module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofDefs
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofHJD
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

structure Ctx (A : Subgroup G) (c : G) (L : Subgroup G) (d : G) : Prop where
  conf : Conf1515HJ A c L L
  free : ∀ e ∈ A, e ≠ 1 → IsZCentral L e →
    CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer ({e} : Set G) = ⊥
  mem_d : d ∈ A
  ne_d : d ≠ 1
  zCentral : IsZCentral L d
  odd : Odd (Nat.card ↥(Subgroup.normalizer (L : Set G) ⊓
    pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))))
  off : ∀ F ∈ omegaA A, ¬ F ≤ A ⊓ L

noncomputable abbrev x₀ (L : Subgroup G) (d : G) : Subgroup G :=
  inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem sec13Data (h : Ctx A c L d) : Sec13Data G A c L :=
  h.conf.sec13Data

theorem isE27 (h : Ctx A c L d) : Late.IsE27 A :=
  Late.isE27_of_mem_partTwoE h.sec13Data.mem_partTwoE

theorem mem_L (h : Ctx A c L d) : d ∈ L :=
  Proof15Res4.mem_of_isZCentral h.zCentral

theorem residual_facts
    (h : Ctx A c L d) :
    Group.IsPerfect ↥(x₀ L d) ∧ Sec4.IsTripleCover ↥(x₀ L d) (alternatingGroup (Fin 6)) ∧
      IsQuasisimple ↥(x₀ L d) ∧ Nat.card (Subgroup.center ↥(x₀ L d)) = 3 ∧ d ∈ x₀ L d ∧
      x₀ L d = oPrimeResidualOf 3 (x₀ L d) ∧
      x₀ L d ≤ delta A (lB A) (Subgroup.centralizer ({d} : Set G)) :=
  Proof15Res11.residual_facts h.conf h.free h.mem_d h.ne_d h.zCentral

theorem inf_pPrimeCoreOf_eq_bot
    (h : Ctx A c L d) :
    x₀ L d ⊓ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) = ⊥ := by
  obtain ⟨-, -, hq, hZ3, -, -, -⟩ := h.residual_facts
  exact Proof15Res11.inf_pPrimeCoreOf_eq_bot
    (Item148HJ.residual_le_centralizer_singleton L d) hq hZ3

theorem omega_facts
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h : Ctx A c L d) :
    Subgroup.zpowers d ∉ omegaA A ∧
      ∀ b ∈ Subgroup.zpowers d, Subgroup.zpowers (c * b) ∈ omegaA A :=
  Proof15Res11.omega_facts h134 h48 h.sec13Data h.conf.j2 h.conf.omega_ne h.mem_d h.ne_d
    h.zCentral

end Ctx

theorem step1515HJEndFpfRBoundOff_of_false
    (h : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (d : G),
      Ctx A c L d → False) :
    Step1515HJEndFpfRBoundOff := by
  intro G _ _ A c L hconf hfree d hdA hd1 hdZ hodd hoff
  exact (h G A c L d ⟨hconf, hfree, hdA, hd1, hdZ, hodd, hoff⟩).elim

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
