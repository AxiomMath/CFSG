module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

theorem s16nt_fix_eq_bot_of_central_odd [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hirr : commSub ⊤ L ∈ irrSet L) {z : ↥L}
    (hz : z ∈ Subgroup.center ↥L) (hodd : Odd (orderOf z)) (hz1 : z ≠ 1) :
    commSub ⊤ L ⊓ fixV L = ⊥ := by
  classical
  let U : Subgroup W := commSub ⊤ L
  let Z : Subgroup W := U ⊓ fixV L
  change Z = ⊥
  have hUc : commSub U L = U := hirr.1
  have hIrr : IsIrrOn L U Z := hirr.2
  have hUstab : StableUnder L U := hIrr.2.1
  have hZstab : StableUnder L Z := hIrr.2.2.1
  have hIrrJ : ∀ J : Subgroup W, StableUnder L J → Z ≤ J → J ≤ U → J = Z ∨ J = U :=
    hIrr.2.2.2
  have hzcomm : ∀ g : ↥L, g * z = z * g := Subgroup.mem_center_iff.mp hz
  let ψ : W →* W :=
    { toFun := fun w => (z : MulAut W) w * w⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hψeq : ∀ (l : ↥L) (w : W),
      ψ ((l : MulAut W) w) = (l : MulAut W) (ψ w) := by
    intro l w
    have hcomm : (l : MulAut W) * (z : MulAut W) =
        (z : MulAut W) * (l : MulAut W) := by
      have h := hzcomm l
      simpa using congrArg (Subtype.val) h
    show (z : MulAut W) ((l : MulAut W) w) * ((l : MulAut W) w)⁻¹ =
      (l : MulAut W) ((z : MulAut W) w * w⁻¹)
    have hcommw : (z : MulAut W) ((l : MulAut W) w) =
        (l : MulAut W) ((z : MulAut W) w) := by
      simpa only [MulAut.mul_apply] using (DFunLike.congr_fun hcomm w).symm
    rw [hcommw, map_mul, map_inv]
  let P : Subgroup W := U.map ψ
  let K : Subgroup W := U ⊓ ψ.ker
  have hPU : P ≤ U := by
    rintro p ⟨u, hu, rfl⟩
    exact U.mul_mem (hUstab z z.2 u hu) (U.inv_mem hu)
  have hPstab : StableUnder L P := by
    intro l hl p hp
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hp
    exact Subgroup.mem_map.mpr
      ⟨(l : MulAut W) u, hUstab l hl u hu, hψeq ⟨l, hl⟩ u⟩
  have hZK : Z ≤ K := by
    intro z0 hz0
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz0).1, ?_⟩
    rw [MonoidHom.mem_ker]
    show (z : MulAut W) z0 * z0⁻¹ = 1
    rw [mem_fixV.mp (Subgroup.mem_inf.mp hz0).2 z z.2, mul_inv_cancel]
  have hKU : K ≤ U := inf_le_left
  have hKstab : StableUnder L K := by
    intro l hl k hk
    obtain ⟨hkU, hkker⟩ := Subgroup.mem_inf.mp hk
    refine Subgroup.mem_inf.mpr ⟨hUstab l hl k hkU, ?_⟩
    rw [MonoidHom.mem_ker] at hkker ⊢
    rw [hψeq ⟨l, hl⟩ k, hkker, map_one]
  have hJstab : StableUnder L (P ⊔ Z) := by
    intro l hl x hx
    obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup.mp hx
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hPstab l hl p hp) (hZstab l hl q hq)
  have hKZU : K = Z ∨ K = U := hIrrJ K hKstab hZK hKU
  have hKZ : K = Z := by
    rcases hKZU with h | h
    · exact h
    · exfalso
      have hfixU : ∀ u ∈ U, (z : MulAut W) u = u := by
        intro u hu
        have huk : u ∈ K := by rw [h]; exact hu
        have hker : ψ u = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp huk).2
        show (z : MulAut W) u = u
        rw [show ψ u = (z : MulAut W) u * u⁻¹ from rfl] at hker
        rwa [mul_inv_eq_one] at hker
      have hzw : ∀ w : W, (z : MulAut W) ((z : MulAut W) w) = w := by
        intro w
        have hwU : (z : MulAut W) w * w⁻¹ ∈ U := by
          change (z : MulAut W) w * w⁻¹ ∈ commSub ⊤ L
          exact Subgroup.subset_closure ⟨z, z.2, w, Subgroup.mem_top w, rfl⟩
        have hfix := hfixU _ hwU
        rw [map_mul, map_inv] at hfix
        have h1 : ((z : MulAut W) w)⁻¹ = (z : MulAut W) w :=
          inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using hW2 ((z : MulAut W) w))
        have h2 : w⁻¹ = w :=
          inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using hW2 w)
        rw [h1, h2] at hfix
        rw [mul_comm ((z : MulAut W) w) w] at hfix
        exact mul_right_cancel hfix
      have hz2 : z ^ 2 = 1 := by
        rw [pow_two]
        ext w
        show ((z : MulAut W) * (z : MulAut W)) w = (1 : MulAut W) w
        rw [MulAut.mul_apply, MulAut.one_apply]
        exact hzw w
      have hdvd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
      have hd1 : orderOf z = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact h
        · rw [h] at hodd
          exact absurd hodd (by decide)
      exact hz1 (orderOf_eq_one_iff.mp hd1)
  have hJZU : P ⊔ Z = Z ∨ P ⊔ Z = U :=
    hIrrJ (P ⊔ Z) hJstab le_sup_right (sup_le hPU inf_le_left)
  rcases hJZU with hJZ | hJU
  · have hPleZ : P ≤ Z := by rw [← hJZ]; exact le_sup_left
    have hUK : U ≤ K := by
      rw [← hUc]
      rw [commSub, Subgroup.closure_le]
      rintro c ⟨l, hl, u, hu, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨U.mul_mem (hUstab l hl u hu) (U.inv_mem hu), ?_⟩
      rw [MonoidHom.mem_ker]
      have hψu : ψ u ∈ P := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      have hfixψu : (l : MulAut W) (ψ u) = ψ u :=
        mem_fixV.mp (Subgroup.mem_inf.mp (hPleZ hψu)).2 l hl
      show ψ ((l : MulAut W) u * u⁻¹) = 1
      rw [map_mul, map_inv, hψeq ⟨l, hl⟩ u, hfixψu, mul_inv_cancel]
    have hUZ : U = Z := le_antisymm (hUK.trans (le_of_eq hKZ)) inf_le_left
    have hUleFix : U ≤ fixV L := by rw [hUZ]; exact inf_le_right
    have hbot : U ≤ ⊥ :=
      calc U = commSub U L := hUc.symm
        _ ≤ commSub (fixV L) L := commSub_mono hUleFix le_rfl
        _ = ⊥ := (commSub_eq_bot_iff).mpr le_rfl
    exact le_bot_iff.mp (le_trans inf_le_left hbot)
  · have hcomm_le_P : commSub U L ≤ P := by
      rw [commSub, Subgroup.closure_le]
      rintro c ⟨l, hl, x, hx, rfl⟩
      have hxJ : x ∈ P ⊔ Z := by rw [hJU]; exact hx
      obtain ⟨p, hp, q, hq, hpq⟩ := Subgroup.mem_sup.mp hxJ
      rw [← hpq]
      have hlp : (l : MulAut W) p ∈ P := hPstab l hl p hp
      have hlq : (l : MulAut W) q = q :=
        mem_fixV.mp (Subgroup.mem_inf.mp hq).2 l hl
      have heq : (l : MulAut W) (p * q) * (p * q)⁻¹ =
          (l : MulAut W) p * p⁻¹ := by
        rw [map_mul, hlq]
        group
      rw [heq]
      exact P.mul_mem hlp (P.inv_mem hp)
    have hPUeq : P = U := le_antisymm hPU (by rw [← hUc]; exact hcomm_le_P)
    haveI : Finite ↥U := Subtype.finite
    let ψU : ↥U → ↥U := fun u => ⟨ψ u, hPU (Subgroup.mem_map.mpr ⟨u, u.2, rfl⟩)⟩
    have hsurj : Function.Surjective ψU := by
      intro u
      have hu : (u : W) ∈ U.map ψ := le_of_eq hPUeq.symm u.2
      obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hu
      exact ⟨⟨v, hv⟩, Subtype.ext hvu⟩
    have hinj : Function.Injective ψU := Finite.injective_iff_surjective.mpr hsurj
    rw [eq_bot_iff]
    intro z0 hz0
    have hz0U : z0 ∈ U := (Subgroup.mem_inf.mp hz0).1
    have hz0K : z0 ∈ K := hKZ.symm ▸ hz0
    have hker : ψ z0 = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hz0K).2
    have heq : ψU ⟨z0, hz0U⟩ = ψU ⟨1, U.one_mem⟩ := by
      apply Subtype.ext
      show ψ z0 = ψ 1
      rw [hker, map_one]
    have hz01 : z0 = 1 := congrArg Subtype.val (hinj heq)
    simpa [Subgroup.mem_bot] using hz01

theorem s16nt_row_u43 [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hirr : commSub ⊤ L ∈ irrSet L)
    (h : (∃ S : Type, ∃ _ : Group S, CFSG.Blueprint.LieModel S .PSU 4 3 1 ∧ IsHat ↥L S) ∧
      E3.mQuot (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = 12) :
    3 * rk ↥(commSub ⊤ L ⊓ fixV L) ≤ rk ↥(commSub ⊤ L) := by
  obtain ⟨⟨S, hGrp, hLie, hHat⟩, -⟩ := h
  letI := hGrp
  have hc3 : Nat.card (Subgroup.center ↥L) = 3 := hHat.2.1
  have hne : Subgroup.center ↥L ≠ ⊥ := by
    intro hbot
    rw [hbot] at hc3
    simp at hc3
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let z' : ↥L := z.1
  have hz' : z' ∈ Subgroup.center ↥L := z.2
  have hz'1 : z' ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext h)
  have hdvd : orderOf z' ∣ 3 := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hz'
    rwa [hc3] at h
  have hne1 : orderOf z' ≠ 1 := by
    intro h
    exact hz'1 (orderOf_eq_one_iff.mp h)
  have horder : orderOf z' = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf z') hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hodd3 : Odd (orderOf z') := by rw [horder]; exact ⟨1, by norm_num⟩
  have hZbot : commSub ⊤ L ⊓ fixV L = ⊥ :=
    s16nt_fix_eq_bot_of_central_odd hW2 hirr hz' hodd3 hz'1
  rw [hZbot, rk_bot]
  simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
