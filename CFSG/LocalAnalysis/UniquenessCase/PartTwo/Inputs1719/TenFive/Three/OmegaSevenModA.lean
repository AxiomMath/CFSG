module

public import CFSG.Quasithin.Background.D2Basic
import CFSG.Quasithin.Background.D2Coprime
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Presheaf

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private def omSevenA_normFun (z : MulAut W) (v : W) : W := v * z v * (z ^ 2) v

private def omSevenA_norm (z : MulAut W) : W →* W :=
  MonoidHom.mk' (omSevenA_normFun z) (by
    intro a b
    simp only [omSevenA_normFun, map_mul]
    ac_rfl)

private lemma omSevenA_norm_apply (z : MulAut W) (v : W) :
    omSevenA_norm z v = omSevenA_normFun z v := rfl

private lemma omSevenA_normFun_apply_z (z : MulAut W) (hz : z ^ 3 = 1) (v : W) :
    omSevenA_normFun z (z v) = omSevenA_normFun z v := by
  have h3 : (z ^ 2) (z v) = v := by
    rw [← MulAut.mul_apply, ← pow_succ, hz, MulAut.one_apply]
  have hzz : z (z v) = (z ^ 2) v := by rw [pow_two, MulAut.mul_apply]
  simp only [omSevenA_normFun, h3, hzz]
  ac_rfl

private lemma omSevenA_commute_of_mem_zpowers {t z : MulAut W} (htz : t * z = z * t)
    {x : MulAut W} (hx : x ∈ zpowers t) : x * z = z * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ((commute_iff_eq t z).mpr htz).zpow_left k |>.eq

private lemma omSevenA_conj_mem_zpowers {z g : MulAut W} (hgz : g * z = z * g)
    {x : MulAut W} (hx : x ∈ zpowers z) : g * x * g⁻¹ ∈ zpowers z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow]
  have hconj : g * z * g⁻¹ = z := by rw [hgz, mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩

private lemma omSevenA_apply_mem_commSub_of_commute_of_maps {z g : MulAut W}
    (hgz : g * z = z * g) {W' : Subgroup W} (hW' : ∀ w ∈ W', g w ∈ W') {u : W}
    (hu : u ∈ commSub W' (zpowers z)) : g u ∈ commSub W' (zpowers z) := by
  have hle : commSub W' (zpowers z) ≤ (commSub W' (zpowers z)).comap (g : W →* W) := by
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, hw, rfl⟩
    change g (x w * w⁻¹) ∈ commSub W' (zpowers z)
    have hconj : g * x * g⁻¹ ∈ zpowers z := omSevenA_conj_mem_zpowers hgz hx
    have hgen : g (x w * w⁻¹) = (g * x * g⁻¹) (g w) * (g w)⁻¹ := by
      rw [map_mul, map_inv]
      congr 1
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    rw [hgen]
    exact Subgroup.subset_closure ⟨g * x * g⁻¹, hconj, g w, hW' w hw, rfl⟩
  exact hle hu

private lemma omSevenA_even_of_two_pow_modEq_one {d : ℕ} (h : 2 ^ d ≡ 1 [MOD 3]) :
    Even d := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨j, rfl⟩ := hodd
  have h4 : 4 ^ j ≡ 1 [MOD 3] := by
    simpa using Nat.ModEq.pow j (show 4 ≡ 1 [MOD 3] by decide)
  have h2 : 2 ^ (2 * j + 1) ≡ 2 [MOD 3] := by
    calc 2 ^ (2 * j + 1) = 4 ^ j * 2 := by rw [pow_succ, pow_mul]; norm_num
      _ ≡ 1 * 2 [MOD 3] := h4.mul_right 2
      _ = 2 := one_mul 2
  exact absurd (h2.symm.trans h) (by decide)

theorem norm_apply_eq_one_of_mem_commSub {z : MulAut W} (hz : z ^ 3 = 1) {u : W}
    (hu : u ∈ commSub ⊤ (zpowers z)) : u * z u * (z ^ 2) u = 1 := by
  have hmap : commSub ⊤ (zpowers z) = (⊤ : Subgroup W).map (commHom z) :=
    commSub_zpowers_eq_map (fun _ _ _ _ => Subgroup.mem_top _)
  rw [hmap] at hu
  obtain ⟨w, -, rfl⟩ := hu
  show omSevenA_normFun z (commHom z w) = 1
  rw [← omSevenA_norm_apply z (commHom z w)]
  simp only [commHom_apply, map_mul, map_inv, omSevenA_norm_apply,
    omSevenA_normFun_apply_z z hz w, mul_inv_cancel]

theorem fixV_inf_commSub_zpowers_eq_bot (hW : ∀ w : W, w ^ 2 = 1) {z : MulAut W}
    (hz : z ^ 3 = 1) : fixV (zpowers z) ⊓ commSub ⊤ (zpowers z) = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  rw [Subgroup.mem_inf] at hu
  obtain ⟨hfix, hcomm⟩ := hu
  rw [Subgroup.mem_bot]
  have hzu : z u = u := mem_fixV_zpowers_iff.mp hfix
  have hz2u : (z ^ 2) u = u :=
    hfix _ (Subgroup.pow_mem (zpowers z) (Subgroup.mem_zpowers z) 2)
  have h1 := norm_apply_eq_one_of_mem_commSub hz hcomm
  rw [hzu, hz2u] at h1
  have h2 : u ^ 2 = 1 := hW u
  have h3 : u ^ 3 = 1 := by
    rw [pow_succ, pow_succ, pow_one]
    exact h1
  have h4 : u ^ 3 = u := by rw [pow_succ, h2, one_mul]
  rw [h3] at h4
  exact h4.symm

theorem apply_mem_commSub_of_commute {z g : MulAut W} (hgz : g * z = z * g) {u : W}
    (hu : u ∈ commSub ⊤ (zpowers z)) : g u ∈ commSub ⊤ (zpowers z) :=
  omSevenA_apply_mem_commSub_of_commute_of_maps hgz (fun _ _ => Subgroup.mem_top _) hu

theorem rk_commSub_le_two_mul_rkIdx_of_inverts (hW : ∀ w : W, w ^ 2 = 1) {z t : MulAut W}
    (hz : orderOf z = 3) (ht : t ^ 2 = 1) (htz : t * z * t⁻¹ = z⁻¹) :
    rk ↥(commSub ⊤ (zpowers z)) ≤ 2 * rkIdx (fixV (zpowers t)) := by
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz_inv : z⁻¹ = z ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', hz3]
  set U : Subgroup W := commSub ⊤ (zpowers z) with hU
  set C : Subgroup W := fixV (zpowers t) with hC
  set D : Subgroup W := C ⊓ U with hD
  set zD : Subgroup W := D.map (z : W →* W) with hzD
  have hzD_le_U : zD ≤ U := by
    intro x hx
    rw [hzD] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact apply_mem_commSub_of_commute (show z * z = z * z from rfl) hd.2
  have hinf : D ⊓ zD = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxD, hxzD⟩ := hx
    rw [hzD] at hxzD
    obtain ⟨d, hdD, rfl⟩ := hxzD
    rw [Subgroup.mem_bot]
    have hzd_fix : t (z d) = z d := mem_fixV_zpowers_iff.mp hxD.1
    have htd : t d = d := mem_fixV_zpowers_iff.mp hdD.1
    have htz' : t * z = z⁻¹ * t := by rw [← htz, mul_assoc, inv_mul_cancel, mul_one]
    have htzd : t (z d) = z⁻¹ d := by
      rw [← MulAut.mul_apply, htz', MulAut.mul_apply, htd]
    have h1 : z d = z⁻¹ d := by rw [← htzd, hzd_fix]
    have hz2d : (z ^ 2) d = d := by
      have h := congrArg (fun v : W => z v) h1
      rw [pow_two]
      simp only [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply] at h
      exact h
    have hzd : z d = d := by rw [h1, hz_inv, hz2d]
    have hdU : d ∈ commSub ⊤ (zpowers z) := by rw [← hU]; exact hdD.2
    have hmem : d ∈ fixV (zpowers z) ⊓ commSub ⊤ (zpowers z) :=
      ⟨mem_fixV_zpowers_iff.mpr hzd, hdU⟩
    rw [fixV_inf_commSub_zpowers_eq_bot hW hz3, Subgroup.mem_bot] at hmem
    exact hzd.trans hmem
  have hcard : Nat.card zD = Nat.card D := by
    rw [hzD]
    exact Subgroup.card_map_of_injective (f := (z : W →* W)) z.injective
  have hrkzD : rk zD = rk D := by unfold rk; rw [hcard]
  have hrank := rk_sup_add_rk_inf D zD
  have hsup_le : rk ↥(D ⊔ zD) ≤ rk U := rk_mono (sup_le inf_le_right hzD_le_U)
  rw [hinf, rk_bot] at hrank
  have h2 : 2 * rk D ≤ rk U := by omega
  have hCU' : rk ↥(C ⊔ U) + rk D = rk C + rk U := by
    rw [hD]
    exact rk_sup_add_rk_inf C U
  have hC_idx := rk_add_rkIdx C
  have hCU_le : rk ↥(C ⊔ U) ≤ rk W := by
    have := rk_mono (le_top : C ⊔ U ≤ (⊤ : Subgroup W))
    rwa [rk_top] at this
  have hmain : rk U ≤ rkIdx C + rk D := by omega
  omega

theorem even_rk_commSub_of_commute (hW : ∀ w : W, w ^ 2 = 1) {z t : MulAut W}
    (hz : orderOf z = 3) (htz : t * z = z * t) :
    Even (rk ↥(commSub (commSub ⊤ (zpowers z)) (zpowers t))) := by
  classical
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  set U : Subgroup W := commSub ⊤ (zpowers z) with hU
  set V : Subgroup W := commSub U (zpowers t) with hV
  have hU_inv : ∀ x ∈ zpowers t, ∀ w ∈ U, x w ∈ U := by
    intro x hx w hw
    rw [hU] at hw ⊢
    exact apply_mem_commSub_of_commute (omSevenA_commute_of_mem_zpowers htz hx) hw
  have hVU : V ≤ U := by
    rw [hV]
    exact commSub_le_of_invariant hU_inv
  have hzU : ∀ w ∈ U, z w ∈ U := by
    intro w hw
    rw [hU] at hw ⊢
    exact apply_mem_commSub_of_commute rfl hw
  have hzV : ∀ v ∈ V, z v ∈ V := by
    intro v hv
    rw [hV] at hv ⊢
    exact omSevenA_apply_mem_commSub_of_commute_of_maps htz.symm hzU hv
  have hfixV : fixV (zpowers z) ⊓ V = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    rw [Subgroup.mem_inf] at hv
    rw [Subgroup.mem_bot]
    have hmem : v ∈ fixV (zpowers z) ⊓ U := ⟨hv.1, hVU hv.2⟩
    rw [hU] at hmem
    rw [fixV_inf_commSub_zpowers_eq_bot hW hz3, Subgroup.mem_bot] at hmem
    exact hmem
  haveI : Fintype V := Fintype.ofFinite V
  let f : V → V := fun v => ⟨z v, hzV v v.2⟩
  have hfinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact z.injective (congrArg Subtype.val h)
  let σ : Equiv.Perm V := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj)
  have hσapp : ∀ v : V, ((σ v : V) : W) = z v := fun v => rfl
  have hσn : ∀ n : ℕ, ∀ v : V, (((σ ^ n) v : V) : W) = (z ^ n) v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', Equiv.Perm.mul_apply, hσapp, ih, pow_succ', MulAut.mul_apply]
  have hσ3 : σ ^ 3 = 1 := by
    ext v
    rw [hσn 3 v, hz3]
    rfl
  have hsupp : σ.supportᶜ = {1} := by
    ext v
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro hv
      have hzv : z (v : W) = (v : W) := by
        have h := congrArg (fun w : V => (w : W)) hv
        rwa [hσapp] at h
      have hmem : (v : W) ∈ fixV (zpowers z) ⊓ V :=
        ⟨mem_fixV_zpowers_iff.mpr hzv, v.2⟩
      rw [hfixV, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · rintro rfl
      apply Subtype.ext
      rw [hσapp]
      exact map_one z
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) hσ3
  rw [hsupp, Finset.card_singleton] at hmod
  have hpow : 2 ^ rk V ≡ 1 [MOD 3] := by
    rw [← card_eq_two_pow hW V, Nat.card_eq_fintype_card]
    exact hmod.symm
  exact omSevenA_even_of_two_pow_modEq_one hpow

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
