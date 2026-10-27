module

public import CFSG.RankThree.PartOne.KS.Lines

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.Sporadic.SmallOddCore
open scoped Pointwise commutatorElement

theorem core_bot_of_record_pgroup {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R C A B : Subgroup M} {x : M} (hC : C = centralizer ({x} : Set M) ⊓ R) (hAC : A ≤ C)
    (hAn : (A.subgroupOf C).Normal) (hAP : A ≤ P) (hAexp : Monoid.exponent A = p)
    (hAcent : centralizer (A : Set M) ⊓ C ≤ A) (hPB : P ≤ B) (hBR : B ≤ R) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({x} : Set M)) = ⊥ := by
  have hAp : IsPGroup p A := fun g => ⟨1, by
    rw [pow_one, ← hAexp]
    exact Monoid.pow_exponent_eq_one g⟩
  have hCR : R ⊓ centralizer ({x} : Set M) = C := by rw [hC, inf_comm]
  refine line_core_bot_of_normal_pgroup hp (P := P) (R := R) hPB hBR hAP hAp
    (hAC.trans (hC.le.trans inf_le_left)) ?_ ?_
  · rw [hCR]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAC).1 hAn
  · rw [hCR, inf_comm]
    exact hAp.to_le hAcent

theorem core_bot_of_record_derivedP {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P R C B : Subgroup M} {x : M} (hC : C = centralizer ({x} : Set M) ⊓ R)
    (hDs : IsSimpleGroup (⁅C, C⁆ : Subgroup M))
    (hDnab : ∃ g ∈ (⁅C, C⁆ : Subgroup M), ∃ h ∈ (⁅C, C⁆ : Subgroup M), g * h ≠ h * g)
    (hDP : (⁅C, C⁆ : Subgroup M) ≤ P)
    (hcard : Nat.card (centralizer ((⁅C, C⁆ : Subgroup M) : Set M) ⊓ C : Subgroup M) = p)
    (hPB : P ≤ B) (hBR : B ≤ R) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({x} : Set M)) = ⊥ := by
  have hDq : IsQuasisimple (⁅C, C⁆ : Subgroup M) := by
    have := hDs
    obtain ⟨g, hg, h, hh, hne⟩ := hDnab
    exact isQuasisimple_of_isSimpleGroup ⟨⟨g, hg⟩, ⟨h, hh⟩, fun e => hne (congrArg Subtype.val e)⟩
  have hCR : R ⊓ centralizer ({x} : Set M) = C := by rw [hC, inf_comm]
  refine line_core_bot_of_normal_component hp (P := P) (R := R) hPB hBR hDP hDq
    (((commutator_self_le C).trans (hC.le.trans inf_le_left))) ?_ ?_
  · rw [hCR]
    exact le_normalizer_commutator_self C
  · rw [hCR, inf_comm]
    exact IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])

end CFSG.RankThree.PartOne
