module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofHJ
public import CFSG.RankThree.PartTwo.Sec14.Concl143HJ
import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofLd
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item14Res7ProofMemFix
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
import CFSG.RankThree.PartTwo.Sec13.Item134Holds
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProof172
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.Sporadic.J2
import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofSec
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec17.Item17TailEnd
import CFSG.RankThree.PartTwo.Sec13.Item136
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofA7
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.PartTwo.Sec13.Item135
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofHJ
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofA7
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofM22
import CFSG.RankThree.PartTwo.Sec17.Item1711Proof
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofKM
import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofKMd
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem lB_closure_eq_ld {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c}) (hcL : c ∉ L)
    {d : G} (hdA : d ∈ A) (hdL : d ∈ L) (hd1 : d ≠ 1)
    (hLD : lB A (Subgroup.closure {c, d}) ≠ ⊥) :
    lB A (Subgroup.closure {c, d}) =
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have hcA : c ∈ A := h.c_mem
  have hc3 : orderOf c = 3 := h.toSec13Data.orderOf_eq
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => h.commute_of_mem hx hy
  have hLc : L ∈ lA A c := h.toSec13Data.mem_lA
  have hinf : L ⊓ Subgroup.zpowers c = ⊥ :=
    Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hc3 hcL
  have hDA : Subgroup.closure ({c, d} : Set G) ≤ A :=
    (Subgroup.closure_le _).mpr (Set.insert_subset_iff.mpr ⟨hcA, Set.singleton_subset_iff.mpr hdA⟩)
  have hdD : d ∈ Subgroup.closure ({c, d} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton d))
  apply le_antisymm
  · exact Proof17Res9.lB_le_ld hΩ hc3 hcL hLc hdL hcA hAcomm hDA hdD
  · obtain ⟨b', e, L', hcfg⟩ := Sec14.exists_isLBConfig_of_lB_ne_bot hLD
    obtain ⟨hDeq, hb'Ω, hLb', hJ2, heL, S, heS, heSc⟩ := hcfg
    have hb'c : Subgroup.zpowers b' = Subgroup.zpowers c := by
      rw [hΩ] at hb'Ω
      exact Set.mem_singleton_iff.mp hb'Ω
    have hLL' : L = L' := by
      have hL : L ∈ lA A b' := by
        rw [CFSG.RankThree.PartTwo.Sec14.lA_eq_of_zpowers_eq hb'c]
        exact hLc
      rw [hLb'] at hL
      exact Set.mem_singleton_iff.mp hL
    subst hLL'
    have hcfg2 : IsLBConfig A (Subgroup.closure ({c, d} : Set G)) b' e L :=
      ⟨hDeq, hb'Ω, hLb', hJ2, heL, S, heS, heSc⟩
    have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
      Subgroup.zpowers_le.mpr (Sec14.centralizer_singleton_le_normalizer_zpowers d
        (Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm c hcA d hdA)))
    have hcd : Subgroup.closure ({c, d} : Set G) = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
      rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
        ← Subgroup.zpowers_eq_closure]
    have heD : e ∈ Subgroup.closure ({c, d} : Set G) := by
      rw [hDeq]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton e))
    have heA : e ∈ A := hDA heD
    have hx' : e ∈ ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := by
      rw [← hcd]
      exact heD
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at hx'
    obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hx'
    have hvL : v ∈ L := (Subgroup.zpowers_le.mpr hdL) hv
    have huL : u ∈ L := by
      have hue : u = e * v⁻¹ := by rw [← huv, mul_inv_cancel_right]
      rw [hue]
      exact mul_mem heL (inv_mem hvL)
    have hu1 : u = 1 := by
      have hmem : u ∈ L ⊓ Subgroup.zpowers c := ⟨huL, hu⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      exact hmem
    have hed : e ∈ Subgroup.zpowers d := by
      rw [← huv, hu1, one_mul]
      exact hv
    have he1 : e ≠ 1 := by
      intro he1
      have hle : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.zpowers c := by
        rw [hDeq]
        refine (Subgroup.closure_le _).mpr ?_
        intro x hx
        rcases Set.mem_insert_iff.mp hx with h1 | h1
        · rw [h1, ← hb'c]
          exact Subgroup.mem_zpowers b'
        · rw [Set.mem_singleton_iff.mp h1, he1]
          exact one_mem _
      have hdc : d ∈ L ⊓ Subgroup.zpowers c := ⟨hdL, hle hdD⟩
      rw [hinf, Subgroup.mem_bot] at hdc
      exact hd1 hdc
    have hode : orderOf e = 3 := orderOf_eq_prime (hA3 e heA) he1
    have hodd : orderOf d = 3 := orderOf_eq_prime (hA3 d hdA) hd1
    have hzd : Subgroup.zpowers e = Subgroup.zpowers d := by
      apply Subgroup.eq_of_le_of_card_ge
      · exact Subgroup.zpowers_le.mpr hed
      · rw [Nat.card_zpowers, Nat.card_zpowers, hode, hodd]
    have hcent : Subgroup.centralizer ({d} : Set G) = Subgroup.centralizer ({e} : Set G) :=
      centralizer_singleton_eq_of_zpowers_eq hzd.symm
    rw [hcent]
    unfold lB
    exact le_iSup_of_le b' (le_iSup_of_le e (le_iSup_of_le L (le_iSup_of_le hcfg2 le_rfl)))

end CFSG.RankThree.PartTwo.Sec17
