module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Sec
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136ZCent
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2LinC
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatA
import CFSG.Quasithin.Background.B5Sec
import CFSG.Quasithin.Background.Asc81cTenFourA

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Open.StatedCenterThree

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_three_dvd_lend {L : Subgroup (MulAut W)} (hfield : IsField ↥(LEnd L))
    {φ : ↥(LEnd L)}
    (hφ3 : φ ^ 3 = 1) (hφ1 : φ ≠ 1) {k : ℕ} (hk : Nat.card ↥(LEnd L) = 2 ^ k) :
    3 ∣ 2 ^ k - 1 := by
  letI : Field ↥(LEnd L) := hfield.toField
  have hφ0 : φ ≠ 0 := by
    intro h0
    have h1 : (0 : ↥(LEnd L)) = 1 := by
      have h2 := hφ3
      rw [h0] at h2
      simpa using h2
    exact zero_ne_one h1
  let u := Units.mk0 φ hφ0
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    change ((u : ↥(LEnd L)) ^ 3) = 1
    rw [show (u : ↥(LEnd L)) = φ from Units.val_mk0 hφ0, hφ3]
  have hu1 : u ≠ 1 := by
    intro hh
    apply hφ1
    have h' : (u : ↥(LEnd L)) = (1 : ↥(LEnd L)) := by rw [hh]; rfl
    simpa [u] using h'
  have huord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdiv := orderOf_dvd_natCard u
  rw [huord] at hdiv
  have hcardU := Nat.card_units (↥(LEnd L))
  rw [hcardU, hk] at hdiv
  exact hdiv

private theorem w1369_sigma_eq_one {L : Subgroup (MulAut W)} (hfield : IsField ↥(LEnd L))
    (hcard : Nat.card ↥(LEnd L) = 4) (σ : ↥(LEnd L) ≃+* ↥(LEnd L)) {φ : ↥(LEnd L)}
    (hφ3 : φ ^ 3 = 1) (hφ1 : φ ≠ 1) (hσφ : σ φ = φ) : ∀ ψ, σ ψ = ψ := by
  letI : Field ↥(LEnd L) := hfield.toField
  have hφ0 : φ ≠ 0 := by
    intro h0
    have h1 : (0 : ↥(LEnd L)) = 1 := by
      have h2 := hφ3
      rw [h0] at h2
      simpa using h2
    exact zero_ne_one h1
  let u := Units.mk0 φ hφ0
  have hu1 : u ≠ 1 := by
    intro hh
    apply hφ1
    have h' : (u : ↥(LEnd L)) = (1 : ↥(LEnd L)) := by rw [hh]; rfl
    simpa [u] using h'
  have hunits := Nat.card_units (↥(LEnd L))
  have hgen : Subgroup.zpowers u = ⊤ := by
    refine zpowers_eq_top_of_prime_card (p := 3) ?_ hu1
    rw [hunits, hcard]
  intro ψ
  by_cases hψ0 : ψ = 0
  · rw [hψ0]
    exact σ.map_zero
  · have hmemψ : Units.mk0 ψ (by
        intro h0
        exact hψ0 (by simpa using h0)) ∈ Subgroup.zpowers u := by rw [hgen]; trivial
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmemψ
    have hψ : ψ = φ ^ n := by
      have hh := congrArg (fun v : (↥(LEnd L))ˣ => (v : ↥(LEnd L))) hn
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hh
      exact hh.symm
    rw [hψ, show σ (φ ^ n) = (σ φ) ^ n from map_zpow₀ σ φ n, hσφ]

private theorem w1369_contra
    (hw2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {t z : MulAut W}
    (hirr : IsIrrOn L ⊤ ⊥)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a)
    (htN : ∀ g ∈ L, t * g * t⁻¹ ∈ L)
    (ht2 : orderOf t = 2)
    (hzc : ∀ l ∈ L, l * z = z * l)
    (hz3 : orderOf z = 3)
    (htz : t * z = z * t)
    (hcard : Nat.card W = 2 ^ 6)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) = 3) : False := by
  classical
  obtain ⟨k, hk1, hk⟩ := w135c2_lend_card hw2 hirr
  obtain ⟨d, hd⟩ := w135c2_rk_eq_mul hw2 hirr hk
  have hd2 : 2 ≤ d := w135c2_one_lt_dim hw2 hirr hnab hk hd
  have hrk : rk W = 6 := by
    have h := w135_card_eq_two_pow_rk hw2
    rw [hcard] at h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h.symm
  have hmem : (MulEquiv.toAdditive z).toAddMonoidHom ∈ LEnd L := by
    intro g hg w
    show Additive.ofMul (z (g (Additive.toMul w))) =
      Additive.ofMul (g (z (Additive.toMul w)))
    have h := congrFun (congrArg (fun f : MulAut W => (f : W → W)) (hzc g hg))
      (Additive.toMul w)
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    exact congrArg Additive.ofMul h.symm
  let φ : ↥(LEnd L) := ⟨(MulEquiv.toAdditive z).toAddMonoidHom, hmem⟩
  have hz3' : z ^ 3 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz3] at h
  have hz3app : ∀ y : W, z (z (z y)) = y := by
    intro y
    have h := congrFun (congrArg (fun f : MulAut W => (f : W → W)) hz3') y
    simpa [pow_succ, MulAut.mul_apply] using h
  have hφ3 : φ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subring.coe_pow, Subring.coe_one]
    set f : AddMonoid.End (Additive W) := φ.1
    change f ^ 3 = 1
    have hfapp : ∀ y : Additive W, f y = Additive.ofMul (z (Additive.toMul y)) := fun y => rfl
    apply AddMonoidHom.ext
    intro x
    simp only [pow_succ, pow_zero, AddMonoid.End.coe_mul, AddMonoid.End.coe_one,
      Function.comp_apply, hfapp]
    show Additive.ofMul (z (z (z (Additive.toMul x)))) = Additive.ofMul (Additive.toMul x)
    rw [hz3app]
  have hz1 : z ≠ 1 := by
    intro hz1
    rw [hz1, orderOf_one] at hz3
    exact absurd hz3 (by norm_num)
  have hφ1 : φ ≠ 1 := by
    intro h
    apply hz1
    ext y
    have h2 : ((φ : ↥(LEnd L)) : AddMonoid.End (Additive W)) =
        ((1 : ↥(LEnd L)) : AddMonoid.End (Additive W)) := congrArg Subtype.val h
    have h3 := congrArg (fun f : AddMonoid.End (Additive W) => f (Additive.ofMul y)) h2
    exact Additive.ofMul.injective h3
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hfield : IsField ↥(LEnd L) := w135c2_lend_isField hw2 hirr
  have h3dvd : 3 ∣ 2 ^ k - 1 := w1369_three_dvd_lend hfield hφ3 hφ1 hk
  have hk2 : k = 2 := by
    have hkd : k * d = 6 := by omega
    have hk_le : k ≤ 3 := by
      by_contra h
      have h4 : 4 ≤ k := by omega
      have : 4 * 2 ≤ k * d := Nat.mul_le_mul h4 hd2
      omega
    interval_cases k
    · norm_num at h3dvd
    · rfl
    · norm_num at h3dvd
  have hEcard : Nat.card ↥(LEnd L) = 4 := by rw [hk, hk2]; norm_num
  obtain ⟨σ, hσ2, hσsem⟩ := w135c2_exists_sigma htN ht2
  have htzapp : ∀ y : W, t (z y) = z (t y) := by
    intro y
    have h := congrFun (congrArg (fun f : MulAut W => (f : W → W)) htz) y
    simpa [MulAut.mul_apply] using h
  have hσφ : σ φ = φ := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ : ∃ y : Additive W,
        Additive.ofMul (t (Additive.toMul y)) = x :=
      ⟨Additive.ofMul (t⁻¹ (Additive.toMul x)), by simp⟩
    change (σ φ : AddMonoid.End (Additive W)) (Additive.ofMul (t (Additive.toMul y))) =
      (φ : AddMonoid.End (Additive W)) (Additive.ofMul (t (Additive.toMul y)))
    rw [hσsem φ y]
    have h2 : (φ : AddMonoid.End (Additive W)) y =
        Additive.ofMul (z (Additive.toMul y)) := rfl
    rw [h2]
    have h3 : (φ : AddMonoid.End (Additive W)) (Additive.ofMul (t (Additive.toMul y))) =
        Additive.ofMul (z (t (Additive.toMul y))) := rfl
    rw [h3]
    exact congrArg Additive.ofMul (htzapp (Additive.toMul y))
  have hσ1 : ∀ ψ : ↥(LEnd L), σ ψ = ψ :=
    w1369_sigma_eq_one hfield hEcard σ hφ3 hφ1 hσφ
  obtain ⟨r, hr1, hr⟩ := w135c2_linear hw2 hirr ht2 hk σ hσsem hσ1
  rw [hm, hk2] at hr
  omega

theorem sl34_excluded (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (c : Ctx136 Y t L) (hf : FaithOn L (Wd L) (Cd L))
    (hirr : IsIrrOn L (Wd L) (Cd L)) :
    ¬ (IsSLn ↥L 3 2 ∧ BinaryNaturalSL L (Wd L) (Cd L) 3 2 ∧ tcost t L (Wd L) = 3) := by
  rintro ⟨hSL, hnat, hcost⟩
  classical
  have hfixL : L.map (MulAut.conj t).toMonoidHom = L := c.hfix L c.comp
  have htU : ∀ u ∈ Wd L, t u ∈ Wd L := by
    intro u hu
    have h := Asc81c.commSub_map_conj L t
    rw [hfixL] at h
    change t u ∈ commSub ⊤ L
    rw [h]
    exact Subgroup.mem_map_of_mem t.toMonoidHom hu
  have htZ : ∀ z ∈ Cd L, t z ∈ Cd L := by
    intro z hz
    obtain ⟨hzU, hzF⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨htU z hzU, ?_⟩
    have hfixV : (fixV L).map t.toMonoidHom = fixV L := by
      have h := Asc81c.fixV_map_conj L t
      rw [hfixL] at h
      exact h.symm
    rw [← hfixV]
    exact Subgroup.mem_map_of_mem t.toMonoidHom hzF
  have hstab : StabPair L (Wd L) (Cd L) := fun a ha => ⟨hirr.2.1 a ha, hirr.2.2.1 a ha⟩
  have hZU : Cd L ≤ Wd L := le_of_lt hirr.1
  have hirrM : IsIrrOn (secSub (Wd L) (Cd L) L) ⊤ ⊥ := (secSub_irr hstab hirr.1).mpr hirr
  have hW2 : ∀ w : Sect (Wd L) (Cd L), w ^ 2 = 1 := sect_exp_two hw2 (Wd L) (Cd L)
  have hmt0 : rk ↥(commSub ⊤ (Subgroup.zpowers (secAut (Wd L) (Cd L) t htU htZ))) = 3 := by
    rw [rk_secAut_comm (Z := Cd L) hZU htU htZ]
    simpa only [tcost] using hcost
  have hmt : E3.mQuot ⊤ (fixV (Subgroup.zpowers (secAut (Wd L) (Cd L) t htU htZ))) = 3 := by
    rw [show E3.mQuot ⊤ (fixV (Subgroup.zpowers (secAut (Wd L) (Cd L) t htU htZ))) =
        rkIdx (fixV (Subgroup.zpowers (secAut (Wd L) (Cd L) t htU htZ))) from by
      unfold E3.mQuot rkIdx
      rw [Subgroup.relIndex_top_right]]
    rw [rkIdx_fixV_zpowers, commV_eq_commSub]
    exact hmt0
  have htbar2 : (secAut (Wd L) (Cd L) t htU htZ) ^ 2 = 1 := by
    rw [pow_two]
    ext m
    induction m using QuotientGroup.induction_on with
    | H u =>
      rw [MulAut.mul_apply, MulAut.one_apply, secAut_mk, secAut_mk]
      congr 1
      exact Subtype.ext (by
        have ht2w : t * t = 1 := by
          have h := pow_orderOf_eq_one t
          rw [c.std.t2] at h
          rwa [pow_two] at h
        have h := congrFun (congrArg (fun f : MulAut W => (f : W → W)) ht2w) (u : W)
        simpa [MulAut.mul_apply] using h)
  have htbar1 : secAut (Wd L) (Cd L) t htU htZ ≠ 1 := by
    intro h1
    have h0 : rk ↥(commSub ⊤ (Subgroup.zpowers (secAut (Wd L) (Cd L) t htU htZ))) = 0 := by
      rw [h1]
      have hbot : commSub (⊤ : Subgroup (Sect (Wd L) (Cd L)))
          (Subgroup.zpowers (1 : MulAut (Sect (Wd L) (Cd L)))) = ⊥ := by
        simp [commSub]
      rw [hbot, rk_bot]
    omega
  have ht2bar : orderOf (secAut (Wd L) (Cd L) t htU htZ) = 2 :=
    orderOf_eq_prime htbar2 htbar1
  have htNbar : ∀ g ∈ secSub (Wd L) (Cd L) L,
      secAut (Wd L) (Cd L) t htU htZ * g * (secAut (Wd L) (Cd L) t htU htZ)⁻¹ ∈
        secSub (Wd L) (Cd L) L := by
    intro g hg
    have hmap := secSub_map_conj hstab htU htZ (t := t)
    rw [hfixL] at hmap
    have hmem : (MulAut.conj (secAut (Wd L) (Cd L) t htU htZ)) g ∈
        (secSub (Wd L) (Cd L) L).map
          (MulAut.conj (secAut (Wd L) (Cd L) t htU htZ)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hg
    rw [hmap] at hmem
    simpa [MulAut.conj_apply] using hmem
  obtain ⟨K, hKfield, hKfin, hKcard, hreal⟩ := hnat
  have hrealM : (FFModel.nat (StatedSL 3 K)).Realizes (secSub (Wd L) (Cd L) L) ⊤ ⊥ :=
    (realizes_secSub_iff (FFModel.nat (StatedSL 3 K)) hstab hZU hf).mpr hreal
  obtain ⟨-, hcardM⟩ := w135c2_natural_data (W := Sect (Wd L) (Cd L))
    (L := secSub (Wd L) (Cd L) L) (ι := Fin 3) (K := K) (Γ := StatedSL 3 K) hirrM hrealM
  have hcardM' : Nat.card (Sect (Wd L) (Cd L)) = 2 ^ 6 := by
    rw [hcardM, hKcard, ← pow_mul]
    norm_num
  have hnabL : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcenter : Subgroup.center ↥L = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact Subgroup.mem_center_iff.mpr fun b => Subtype.ext (hcon a a.2 b b.2).symm
    haveI : Subsingleton (↥L ⧸ Subgroup.center ↥L) := by
      rw [hcenter]
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with
      | H x =>
        induction b using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq]
          exact Subgroup.mem_top _
    haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := c.comp.2.2.2
    exact (not_subsingleton_iff_nontrivial.mpr
      (inferInstance : Nontrivial (↥L ⧸ Subgroup.center ↥L))) inferInstance
  obtain ⟨eL⟩ := mulEquiv_secSub hstab hf
  have hLU : L ≤ stabSub (Wd L) := fun a ha =>
    mem_stabSub_of_invariant (hirr.2.1 a ha) (inv_mem_of_forall_mem a (hirr.2.1 a ha))
  have hLZ : L ≤ stabSub (Cd L) := fun a ha =>
    mem_stabSub_of_invariant (hirr.2.2.1 a ha) (inv_mem_of_forall_mem a (hirr.2.2.1 a ha))
  have hfaith0 : L ⊓ centSec (Wd L) (Cd L) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_inf, mem_centSec] at ha
    rw [Subgroup.mem_bot]
    exact hf a ha.1 ha.2.2
  let eL0 : ↥L ≃* ↥(secSub (Wd L) (Cd L) L) :=
    B5.secEquiv L hLU hLZ hfaith0
  have hnabbar : ∃ a ∈ secSub (Wd L) (Cd L) L, ∃ b ∈ secSub (Wd L) (Cd L) L,
      a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnabL
    refine ⟨eL0 ⟨a, ha⟩, (eL0 ⟨a, ha⟩).2, eL0 ⟨b, hb⟩, (eL0 ⟨b, hb⟩).2, ?_⟩
    intro h
    apply hab
    have h1 : eL0 (⟨a, ha⟩ * ⟨b, hb⟩) = eL0 (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h
    have h2 := eL0.injective h1
    simpa using congrArg Subtype.val h2
  obtain ⟨K', hK'field, hK'fin, hK'card, hE⟩ := hSL
  obtain ⟨eSL⟩ := hE
  have h3K' : 3 ∣ Nat.card K' - 1 := by rw [hK'card]; norm_num
  have hZcard : Nat.card (Subgroup.center ↥(StatedSL 3 K')) = 3 :=
    card_center_statedSL_three h3K'
  have hZLcard : Nat.card (Subgroup.center ↥L) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr eSL).toEquiv]
    exact hZcard
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z₀, hz₀ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥L) 3 (by rw [hZLcard])
  let z : MulAut W := ((z₀ : ↥L) : MulAut W)
  have hzL : z ∈ L := (z₀ : ↥L).2
  have hz3 : orderOf z = 3 := by
    change orderOf (((z₀ : ↥L) : MulAut W)) = 3
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz₀ord]
  have hzc : ∀ l ∈ L, l * z = z * l := by
    intro l hl
    have h := Subgroup.mem_center_iff.mp z₀.2 (⟨l, hl⟩ : ↥L)
    have h' := congrArg Subtype.val h
    simpa [z, MulAut.mul_apply] using h'
  have htz : t * z = z * t := center_cent_t c hzL hzc
  have hz3' : z ^ 3 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz3] at h
  let zbar : MulAut (Sect (Wd L) (Cd L)) :=
    secAut (Wd L) (Cd L) z (hirr.2.1 z hzL) (hirr.2.2.1 z hzL)
  have hzbar3 : zbar ^ 3 = 1 := by
    rw [show zbar = secAut (Wd L) (Cd L) z (hirr.2.1 z hzL) (hirr.2.2.1 z hzL) from rfl]
    ext m
    induction m using QuotientGroup.induction_on with
    | H u =>
      simp only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply]
      rw [secAut_mk, secAut_mk, secAut_mk]
      congr 1
      exact Subtype.ext (by
        have h := congrFun (congrArg (fun f : MulAut W => (f : W → W)) hz3') (u : W)
        simpa [pow_succ, MulAut.mul_apply] using h)
  have hzbar1 : zbar ≠ 1 := by
    intro h1
    have hz1 : z = 1 := by
      apply hf z hzL
      intro u hu
      have h2 : secAut (Wd L) (Cd L) z (hirr.2.1 z hzL) (hirr.2.2.1 z hzL)
          (QuotientGroup.mk ⟨u, hu⟩) = QuotientGroup.mk ⟨u, hu⟩ := by
        rw [← show zbar = secAut (Wd L) (Cd L) z (hirr.2.1 z hzL) (hirr.2.2.1 z hzL) from rfl,
          h1]
        rfl
      rw [secAut_mk] at h2
      have h3 : (⟨z u, hirr.2.1 z hzL u hu⟩ : ↥(Wd L))⁻¹ * (⟨u, hu⟩ : ↥(Wd L)) ∈
          (Cd L).subgroupOf (Wd L) := (QuotientGroup.eq).mp h2
      have hzu : (z u)⁻¹ = z u :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hw2 (z u))
      have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hw2 u)
      have h4 := Subgroup.mem_subgroupOf.mp h3
      simpa [hzu, hu, MulAut.mul_apply] using h4
    rw [hz1, orderOf_one] at hz3
    exact absurd hz3 (by norm_num)
  have hzbar_ord : orderOf zbar = 3 := orderOf_eq_prime hzbar3 hzbar1
  have hfaith : L ⊓ centSec (Wd L) (Cd L) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_inf, mem_centSec] at ha
    rw [Subgroup.mem_bot]
    exact hf a ha.1 ha.2.2
  let eL : ↥L ≃* ↥(secSub (Wd L) (Cd L) L) :=
    B5.secEquiv L hLU hLZ hfaith
  have hzbar_eq : zbar = (eL ⟨z, hzL⟩ : ↥(secSub (Wd L) (Cd L) L)) := by
    ext m
    induction m using QuotientGroup.induction_on with
    | H u =>
      rw [show zbar = secAut (Wd L) (Cd L) z (hirr.2.1 z hzL) (hirr.2.2.1 z hzL) from rfl,
        secAut_mk]
      change ((B5.secEquiv L hLU hLZ hfaith ⟨z, hzL⟩ :
        ↥(secSub (Wd L) (Cd L) L)) : MulAut (Sect (Wd L) (Cd L))) (QuotientGroup.mk u) =
        QuotientGroup.mk ⟨z u, hirr.2.1 z hzL u u.2⟩
      rw [B5.secEquiv_apply, B5.secHom_mk]
  have hzcbar : ∀ l ∈ secSub (Wd L) (Cd L) L, l * zbar = zbar * l := by
    intro l hl
    obtain ⟨l₀, hl₀⟩ : ∃ l₀ : ↥L, (eL l₀ : ↥(secSub (Wd L) (Cd L) L)) = ⟨l, hl⟩ :=
      ⟨eL.symm ⟨l, hl⟩, eL.apply_symm_apply ⟨l, hl⟩⟩
    have hl₀' : ((eL l₀ : ↥(secSub (Wd L) (Cd L) L)) : MulAut (Sect (Wd L) (Cd L))) = l :=
      congrArg Subtype.val hl₀
    rw [← hl₀', hzbar_eq]
    have hcomm : l₀ * ⟨z, hzL⟩ = ⟨z, hzL⟩ * l₀ := by
      apply Subtype.ext
      have h := hzc (l₀ : MulAut W) l₀.2
      simpa [z, MulAut.mul_apply] using h
    have h2 := congrArg (fun x : ↥L => (eL x : ↥(secSub (Wd L) (Cd L) L))) hcomm
    simp only [map_mul] at h2
    simpa using congrArg Subtype.val h2
  have htzbar : secAut (Wd L) (Cd L) t htU htZ * zbar =
      zbar * secAut (Wd L) (Cd L) t htU htZ := by
    rw [show zbar = secAut (Wd L) (Cd L) z (hirr.2.1 z hzL) (hirr.2.2.1 z hzL) from rfl]
    ext m
    induction m using QuotientGroup.induction_on with
    | H u =>
      rw [MulAut.mul_apply, MulAut.mul_apply, secAut_mk, secAut_mk, secAut_mk, secAut_mk]
      congr 1
      exact Subtype.ext (by
        have h := congrFun (congrArg (fun f : MulAut W => (f : W → W)) htz) (u : W)
        simpa [MulAut.mul_apply] using h)
  exact w1369_contra (W := Sect (Wd L) (Cd L)) hW2 hirrM hnabbar htNbar ht2bar hzcbar
    hzbar_ord htzbar hcardM' hmt

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
