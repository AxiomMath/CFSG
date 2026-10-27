module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

namespace TwoTheta

section Norm

@[expose] def threeElements (Λ : Type*) [Group Λ] : Set Λ := {x | ∃ k : ℕ, x ^ 3 ^ k = 1}

variable {Λ : Type} [Group Λ] [Finite Λ] [Group.IsPerfect Λ]

theorem hom_eq_one_of_threeElements
    (e : Λ ⧸ CFSG.pCore 2 Λ ≃* projSL 3 (GaloisField 2 2)) {H : Type} [Group H]
    (ψ : Λ →* H) (h : ∀ x ∈ threeElements Λ, ψ x = 1) : ψ = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 Λ) := inferInstance
  have hPker : (P : Subgroup Λ) ≤ ψ.ker := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    have hk' : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact h x ⟨k, hk'⟩
  have hdvd : ψ.ker.index ∣ (P : Subgroup Λ).index := Subgroup.index_dvd_of_le hPker
  have h3 : ¬ 3 ∣ Nat.card ψ.range := by
    rw [← Subgroup.index_ker]
    exact fun h3 => P.not_dvd_index (h3.trans hdvd)
  haveI : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hH : CFSG.Open.pRank 3 (⊤ : Subgroup ψ.range) ≤ 1 := by
    rw [CFSG.RankThreeEvenClassification.Helpers.pRank_eq_zero_of_not_dvd 3 Nat.prime_three h3]
    exact Nat.zero_le _
  have h1 := Res5.hom_eq_one_of_l34 e hH ψ.rangeRestrict
  ext x
  have h2 := congrArg (fun f : Λ →* ψ.range => (f x : H)) h1
  simpa using h2

theorem eq_top_of_threeElements_subset
    (e : Λ ⧸ CFSG.pCore 2 Λ ≃* projSL 3 (GaloisField 2 2)) {T : Subgroup Λ}
    (hT : threeElements Λ ⊆ (T : Set Λ)) : T = ⊤ := by
  set C := Subgroup.normalClosure (threeElements Λ) with hC
  have hker : ∀ x ∈ threeElements Λ, (QuotientGroup.mk' C) x = 1 := fun x hx =>
    (QuotientGroup.eq_one_iff x).mpr (Subgroup.subset_normalClosure hx)
  have h1 := hom_eq_one_of_threeElements e (QuotientGroup.mk' C) hker
  have hCtop : C = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h2 := congrArg (fun f : Λ →* Λ ⧸ C => f x) h1
    exact (QuotientGroup.eq_one_iff x).mp h2
  have hCT : C ≤ T := by
    show Subgroup.closure (Group.conjugatesOfSet (threeElements Λ)) ≤ T
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨s, hs, hsx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hsx
    obtain ⟨k, hk⟩ := hs
    apply hT
    refine ⟨k, ?_⟩
    rw [conj_pow, hk]
    simp
  rw [eq_top_iff, ← hCtop]
  exact hCT

end Norm

end TwoTheta

end CFSG.RankThree.PartTwo.Sec20
