module

public import CFSG.Timmesfeld.Final.Simple
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Timmesfeld.Final.Orders
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3139
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Open

theorem decl1_of_outcome {G : Type} [Group G] (h : Outcome G) :
    IsSimpleGroup G ∧
      ((Nat.card G ∈ lieOrdersChar 2 ∧
          (∀ n f : ℕ, 2 ≤ n → 1 ≤ f → Nat.card G ≠ ordTwistedA n (2 ^ f)) ∧
          (∀ f : ℕ, 1 ≤ f → Nat.card G ≠ ordBC 2 (2 ^ f))) ∨
        Nonempty (G ≃* PSU3 3 1) ∨
        Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
        Nat.card G = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7) := by
  refine ⟨isSimpleGroup_of_outcome h, ?_⟩
  rcases card_mem_of_outcome h with hm | h | h | h
  · exact .inl (evenOrdersExceptUnitarySp4_spec hm)
  · exact .inr (.inl (nonempty_mulEquiv_PSU3_of_lieModel h))
  · exact .inr (.inr (.inl h))
  · obtain ⟨e⟩ := h
    refine .inr (.inr (.inr ?_))
    rw [Nat.card_congr e.toEquiv]
    exact Sporadic.J2.card_J2

theorem decl2_of_outcome {G : Type} [Group G] (h : Outcome G) :
    (EvenLieType G ∧
      (∀ n f : ℕ, 3 ≤ n → 1 ≤ f → ¬ LieModel G .PSU n 2 f) ∧
      (∀ f : ℕ, 1 ≤ f → ¬ LieModel G .PSp 2 2 f)) ∨
    LieModel G .PSU 3 3 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
      NativeSporadic.IsSporadic G .J2 :=
  (evenLieType_and_card_mem_of_outcome h).imp_left fun ⟨hE, hm⟩ =>
    ⟨hE, fun _ _ hn hf => not_lieModel_PSU_of_card_mem hm hn hf,
      fun _ hf => not_lieModel_PSp_two_of_card_mem hm hf⟩

end CFSG.Timmesfeld
