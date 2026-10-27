module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.FixedFree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree (ActsIrr)

theorem fixedFreeFive_of_semidihedral {X : Type*} [Group X] {Q S : Subgroup X} {a b : X}
    (hQ3 : IsPGroup 3 Q) (hQ1 : Q ≠ ⊥) (hQc : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hSN : S ≤ Subgroup.normalizer (Q : Set X)) (haS : a ∈ S) (ha8 : orderOf a = 8)
    (hba : b * a * b⁻¹ = a ^ 3) (hSab : S = Subgroup.closure {a, b})
    (hC : S ⊓ Subgroup.centralizer (Q : Set X) = ⊥) (hirr : ActsIrr S Q) :
    SEFive.FixedFreeFive 3 X := by
  have ha8' : a ^ 8 = 1 := ha8 ▸ pow_orderOf_eq_one a
  have ha12 : a ^ 12 = a ^ 4 := by
    rw [show 12 = 8 + 4 by norm_num, pow_add, ha8', one_mul]
  have hτS : S ≤ Subgroup.centralizer {a ^ 4} := by
    rw [hSab, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Commute.self_pow x 4).eq
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have h : x * a ^ 4 * x⁻¹ = a ^ 4 := by
        rw [← conj_pow, hba, ← pow_mul, ha12]
      exact mul_inv_eq_iff_eq_mul.mp h
  obtain ⟨W, hW⟩ : ∃ W : Subgroup X, W = Q ⊓ Subgroup.centralizer {a ^ 4} := ⟨_, rfl⟩
  have hmemW : ∀ y, y ∈ W ↔ y ∈ Q ∧ y * a ^ 4 = a ^ 4 * y := fun y => by
    rw [hW, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hfwd : ∀ y ∈ S, ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    intro y hy w hw
    obtain ⟨hwQ, hwc⟩ := (hmemW w).1 hw
    have hyc : y * a ^ 4 = a ^ 4 * y := Subgroup.mem_centralizer_singleton_iff.1 (hτS hy)
    refine (hmemW _).2 ⟨(Subgroup.mem_normalizer_iff.1 (hSN hy) w).1 hwQ, ?_⟩
    calc y * w * y⁻¹ * a ^ 4 = y * w * (y⁻¹ * (a ^ 4 * y)) * y⁻¹ := by group
      _ = y * w * (y⁻¹ * (y * a ^ 4)) * y⁻¹ := by rw [hyc]
      _ = y * (w * a ^ 4) * y⁻¹ := by group
      _ = y * (a ^ 4 * w) * y⁻¹ := by rw [hwc]
      _ = (y * a ^ 4) * w * y⁻¹ := by group
      _ = a ^ 4 * y * w * y⁻¹ := by rw [hyc]
      _ = a ^ 4 * (y * w * y⁻¹) := by group
  have hWN : S ≤ Subgroup.normalizer (W : Set X) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hfwd x hx w, fun h => ?_⟩
    have h' := hfwd x⁻¹ (S.inv_mem hx) _ h
    rwa [show x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w by group] at h'
  have hW1 : W = ⊥ := by
    rcases hirr W (hW ▸ inf_le_left) hWN with h | h
    · exact h
    · exfalso
      have hτ : a ^ 4 ∈ S ⊓ Subgroup.centralizer (Q : Set X) := by
        refine ⟨S.pow_mem haS 4, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        exact ((hmemW y).1 (h ▸ hy)).2
      rw [hC, Subgroup.mem_bot] at hτ
      exact pow_ne_one_of_lt_orderOf (x := a) (n := 4) (by norm_num) (by rw [ha8]; norm_num) hτ
  refine ⟨Q, hQ3, hQ1, hQc, a, hSN haS, fun k hk0 hk5 s hs hfix => ?_⟩
  have hks : Commute (a ^ k) s := mul_inv_eq_iff_eq_mul.mp hfix
  have h4 : Commute (a ^ 4) s := by
    interval_cases k
    · simpa using hks.pow_left 4
    · simpa [← pow_mul] using hks.pow_left 2
    · simpa [← pow_mul, ha12] using hks.pow_left 4
    · exact hks
  have hsW : s ∈ W := (hmemW s).2 ⟨hs, h4.eq.symm⟩
  rw [hW1, Subgroup.mem_bot] at hsW
  exact hsW

theorem coverActsTriviallyOnSmall_m11Row {X : Type} [Group X] {K Q S : Subgroup X}
    [IsSimpleGroup ↥K] (hKt : K = ⊤) (hE : CFSG.Open.IsElemAbelian 3 Q) (h9 : Nat.card ↥Q = 9)
    (hSN : S ≤ Subgroup.normalizer (Q : Set X))
    (hab : ∃ a ∈ S, ∃ b ∈ S, orderOf a = 8 ∧ orderOf b = 2 ∧ b * a * b⁻¹ = a ^ 3 ∧
      S = Subgroup.closure {a, b})
    (hC : S ⊓ Subgroup.centralizer (Q : Set X) = ⊥) (hirr : ActsIrr S Q) :
    CoverActsTriviallyOnSmall 3 ↥K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, haS, b, -, ha8, -, hba, hSab⟩ := hab
  have hQ1 : Q ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at h9
    exact absurd h9 (by norm_num)
  have hFF := fixedFreeFive_of_semidihedral (IsPGroup.of_card (n := 2) (by rw [h9]; norm_num))
    hQ1 (fun x hx y hy => by simpa using hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩) hSN haS ha8 hba hSab
    hC hirr
  exact SEFive.coverActsTriviallyOnSmall_of_fixedFreeFive (q := 3) (Or.inr rfl)
    (hFF.of_mulEquiv ((MulEquiv.subgroupCongr hKt).trans Subgroup.topEquiv).symm)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeKIB
