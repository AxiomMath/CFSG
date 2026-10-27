module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23L63Perm
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporMathieu

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi23K

open Subgroup CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.Solomon78.F23L63
open CFSG.QuasithinUnique (IsSylowTwoOf)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem le_normalizer_frameE
    {H : Subgroup J} (hEH : frameE ≤ H) (h3 : ¬ 3 ∣ Nat.card ↥H) :
    H ≤ normalizer ((frameE : Subgroup J) : Set J) := by
  let S : Set J := {x : J | x ∈ D23 ∧ x ∈ H}
  let A : Subgroup J := closure S
  have hS : S.Pairwise Commute := by
    intro x hx y hy _
    have hx1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by
      simpa [pow_two, orderOf_of_isConj hx.1] using pow_orderOf_eq_one x)
    have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by
      simpa [pow_two, orderOf_of_isConj hy.1] using pow_orderOf_eq_one y)
    have hxy : orderOf (x * y) ∣ 2 := by
      rcases orderOf_mul_of_isConj hx.1 hy.1 with h | h | h
      · simp [h]
      · simp [h]
      · exact absurd ((show 3 ∣ orderOf (x * y) by rw [h]).trans
          (H.orderOf_dvd_natCard (H.mul_mem hx.2 hy.2))) h3
    have hxy1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (by
      rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.1 hxy)
    show x * y = y * x
    rw [← hxy1, mul_inv_rev, hx1, hy1]
  have hEA : frameE ≤ A := by
    rw [frameE]
    refine CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen.range_le_closure.trans (closure_mono ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨CFSG.EvenSporadicStandard.TwoFi22.FrameJ.fjPt_mem i, hEH (fjPt_mem_frameE i)⟩
  have : IsMulCommutative A := Subgroup.isMulCommutative_closure hS
  have hAE : A = frameE := le_antisymm (fun a ha => centralizer_frameE_le fun x hx =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.le_centralizer A ha) x (hEA hx)).symm) hEA
  have hconj : ∀ h ∈ H, ∀ x ∈ A, h * x * h⁻¹ ∈ A := by
    intro h hh x hx
    induction hx using closure_induction with
    | mem y hy => exact subset_closure ⟨IsConj.trans hy.1 (isConj_iff.2 ⟨h, rfl⟩),
        H.mul_mem (H.mul_mem hh hy.2) (H.inv_mem hh)⟩
    | one => simp
    | mul y z _ _ hy hz => simpa [mul_assoc] using A.mul_mem hy hz
    | inv y _ hy => simpa [mul_assoc] using A.inv_mem hy
  intro h hh
  rw [← hAE, mem_normalizer_iff]
  exact fun n => ⟨hconj h hh n, fun hn => by simpa [mul_assoc] using hconj h⁻¹ (H.inv_mem hh) _ hn⟩

theorem exists_isSylowTwoOf_frameE_le :
    ∃ T : Subgroup J, IsSylowTwoOf T ⊤ ∧ frameE ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 ↥frameE := IsPGroup.of_card (p := 2) (n := 11) frameE_card
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow hE2
  refine ⟨(P : Subgroup J), ⟨le_top, P.isPGroup', ?_⟩, hEP⟩
  change ¬ 2 ∣ (P : Subgroup J).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact Sylow.not_dvd_index P

theorem k105In_normalizer_frameE
    {T : Subgroup J} (hT : IsSylowTwoOf T ⊤) (hET : frameE ≤ T) :
    K105In (normalizer ((frameE : Subgroup J) : Set J)) T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup J := normalizer ((frameE : Subgroup J) : Set J)
  have h3T : ¬ 3 ∣ Nat.card ↥T := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥T)).1 hT.2.1
    intro h3d
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (hk ▸ h3d)) (by norm_num)
  have hTC : T ≤ C := le_normalizer_frameE hET h3T
  obtain ⟨hN, ⟨e⟩⟩ := frame_quotient_m23
  have : (frameE.subgroupOf C).Normal := hN
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M23) :=
    inferInstanceAs (Finite CFSG.Blueprint.NativeSporadic.M23)
  refine k105In_of_quotient (X := J) hT hTC (frameE.subgroupOf C) ?_ e ?_
  · rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left.trans hET
  · intro S H' hS hSH hHs hH3
    exact k105SporAt_M23 (CFSG.Blueprint.NativeSporadic.Carrier .M23)
      ⟨MulEquiv.refl _⟩ S H' hS hSH hHs hH3

theorem k105In_top
    {T : Subgroup J} (hT : IsSylowTwoOf T ⊤) (hET : frameE ≤ T) : K105In ⊤ T := by
  intro Y hTY _ hYs hY3
  exact k105In_normalizer_frameE hT hET Y hTY (le_normalizer_frameE (hET.trans hTY) hY3) hYs hY3

theorem k105SporAt_fi23 :
    K105SporAt .Fi23 := by
  obtain ⟨T, hT, hET⟩ := exists_isSylowTwoOf_frameE_le
  exact k105SporAt_of_k105In hT (k105In_top hT hET) fi23EquivJ

end Fi23K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
