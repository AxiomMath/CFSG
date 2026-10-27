module

public import CFSG.Quasithin.Recognition.St84.Sec4QuotA
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize

import CFSG.Quasithin.Recognition.St84.Gen.NatSecPre
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.Quasithin.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement Matrix MatrixGroups

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

theorem natQuot_of_four_le {P L E Z T : Subgroup G}
    [Finite ↥P] (h : A5Pre P L E Z) (hEL : E ≤ L) (hT : IsSylowTwoOf T L)
    (hC : 4 ≤ Z.relIndex (relCent E Z T)) : NatQuot L E Z 2 :=
  natQuot_of_two_pow_le le_rfl
    ⟨h.le, h.norm_L, h.norm_E, h.norm_K, h.sec, h.card, h.core, h.quot, h.nontriv⟩ hEL hT hC

private theorem Setup.a5Pre_Q_of_normal (X : Setup Γ G) (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (h4 : 4 ≤ s) (i : ℤ) (hni : X.n i = 2)
    (hn1 : X.n (i + 1) = 2)
    (hA : X.Gi i ≤ Subgroup.normalizer
      ((X.Q (i - 1) ⊓ X.Q (i + 1) : Subgroup G) : Set G)) :
    A5Pre (X.Gi i) (X.L i) (X.Q i) (X.Q (i - 1) ⊓ X.Q (i + 1)) := by
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  set A : Subgroup G := X.Q (i - 1) ⊓ X.Q (i + 1) with hAdef
  have hQ := X.Q_quot hc hs h4 i
  have hQcomm := X.Q_quot_comm hc hs h4 i
  have hcard : A.relIndex (X.Q i) = 16 := by
    have h := hQ.2.2.2.1
    rw [hn1] at h
    norm_num at h ⊢
    exact h
  have hsec : IsElemSec A (X.Q i) := ⟨hQ.1, hQ.2.2.1, hQ.2.1⟩
  have hcore : ∀ q ∈ CFSG.Open.pCoreOf 2 (X.Gi i), ∀ e ∈ X.Q i, ⁅q, e⁆ ∈ A := by
    intro q hq e he
    exact (Subgroup.commutator_le.mp hQ.2.2.1) q hq e he
  have hquot : IsL2Quot 2 (oTwoQuot ↥(X.L i)) := by
    obtain ⟨e⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert i)).quot
    have e' : oTwoQuot ↥(X.L i) ≃* PSL(2, GaloisField 2 (X.n i)) := e
    rw [hni] at e'
    exact ⟨e'⟩
  have hnontriv : ∃ l ∈ X.L i, ∃ e ∈ X.Q i, ⁅l, e⁆ ∉ A := by
    have hne : ¬ ⁅X.Q i ⊓ X.Q (i - 1), X.Q (i + 1)⁆ ≤ A := hQcomm.1
    have hne' : ¬ ∀ x ∈ X.Q i ⊓ X.Q (i - 1), ∀ y ∈ X.Q (i + 1), ⁅x, y⁆ ∈ A := by
      intro h
      exact hne (Subgroup.commutator_le.mpr h)
    push Not at hne'
    obtain ⟨x, hx, y, hy, hxy⟩ := hne'
    refine ⟨y, ?_, x, hx.1, ?_⟩
    · have hy' := le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi (i + 1)))
        ((X.Q_le_Gi_adj (i + 1)).trans inf_le_left) hy
      simpa using hy'
    · intro hmem
      apply hxy
      simpa [commutatorElement_inv] using A.inv_mem hmem
  exact {
    le := X.L_le_Gi i
    norm_L := (Subgroup.normal_subgroupOf_iff_le_normalizer (X.L_le_Gi i)).mp
      (X.hyp.isLocL2_oTwoPrime (X.vert i)).normal
    norm_E := CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi i)
    norm_K := by simpa [hAdef] using hA
    sec := hsec
    card := hcard
    core := hcore
    quot := hquot
    nontriv := hnontriv }

private theorem Setup.four_le_relIndex_relCent_edgeSylow (X : Setup Γ G)
    (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G s) (h4 : 4 ≤ s) (i : ℤ)
    (hn1 : X.n (i + 1) = 2)
    (hA : X.Gi i ≤ Subgroup.normalizer
      ((X.Q (i - 1) ⊓ X.Q (i + 1) : Subgroup G) : Set G))
    (hquad : ⁅⁅X.Q i, X.edgeSylow i⁆, X.edgeSylow i⁆ ≤ X.Q (i - 1) ⊓ X.Q (i + 1)) :
    4 ≤ (X.Q (i - 1) ⊓ X.Q (i + 1)).relIndex
      (relCent (X.Q i) (X.Q (i - 1) ⊓ X.Q (i + 1)) (X.edgeSylow i)) := by
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  set A : Subgroup G := X.Q (i - 1) ⊓ X.Q (i + 1) with hAdef
  have hQ := X.Q_quot hc hs h4 i
  have hQcomm := X.Q_quot_comm hc hs h4 i
  have hD_le : A ≤ X.Q i ⊓ X.Q (i + 1) := le_inf hQ.1 inf_le_right
  have hDrel : A.relIndex (X.Q i ⊓ X.Q (i + 1)) = 4 := by
    have h := hQ.2.2.2.2.1
    rw [hn1] at h
    norm_num at h ⊢
    exact h
  set C : Subgroup G := ⁅X.Q i ⊓ X.Q (i - 1), X.Q (i + 1)⁆ with hCdef
  have hD : X.Q i ⊓ X.Q (i + 1) = C ⊔ A := hQcomm.2
  have hC_le : C ≤ ⁅X.Q i, X.edgeSylow i⁆ :=
    Subgroup.commutator_mono inf_le_left (X.Q_le_edgeSylow i)
  have hquad' : ⁅⁅X.Q i, X.edgeSylow i⁆, X.edgeSylow i⁆ ≤ A := by
    simpa [hAdef] using hquad
  have h1 : ⁅C, X.edgeSylow i⁆ ≤ A :=
    (Subgroup.commutator_mono hC_le le_rfl).trans hquad'
  have h2 : ⁅A, X.edgeSylow i⁆ ≤ A := by
    refine (Subgroup.le_normalizer_iff_commutator_le_left (H := X.edgeSylow i)
      (K := A)).mp ?_
    exact ((X.edgeSylow_le_L i).trans (X.L_le_Gi i)).trans hA
  have hC_le_Qi : C ≤ X.Q i := by
    rw [hCdef, Subgroup.commutator_le]
    intro x hx y hy
    have hyGi : y ∈ X.Gi i := by
      have hy' := (X.Q_le_Gi_adj (i + 1)).trans inf_le_left hy
      simpa using hy'
    have hyN : y ∈ Subgroup.normalizer (X.Q i : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi i)) hyGi
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (X.Q i).mul_mem hx.1
      ((Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp ((X.Q i).inv_mem hx.1))
  have hCA_norm : C ≤ Subgroup.normalizer (A : Set G) :=
    (hC_le_Qi.trans (X.Q_le_Gi i)).trans hA
  have h3 : ⁅C ⊔ A, X.edgeSylow i⁆ ≤ A :=
    CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize C A
      (X.edgeSylow i) A h1 h2 hCA_norm Subgroup.le_normalizer
  have hQnormA : X.Q i ≤ Subgroup.normalizer (A : Set G) :=
    (X.Q_le_Gi i).trans hA
  have hDS : X.Q i ⊓ X.Q (i + 1) ≤ relCent (X.Q i) A (X.edgeSylow i) := by
    intro e he
    have heD : e ∈ C ⊔ A := by rwa [← hD]
    exact (mem_relCent hQnormA).mpr ⟨he.1, fun s hs =>
      (Subgroup.commutator_le.mp h3) e heD s hs⟩
  haveI hQfin : Finite ↥(X.Q i) :=
    Finite.of_injective (Subgroup.inclusion (X.Q_le_Gi i))
      (Subgroup.inclusion_injective _)
  haveI hrelfin : Finite ↥(relCent (X.Q i) A (X.edgeSylow i)) :=
    Finite.of_injective (Subgroup.inclusion (fun x hx => ((mem_relCent hQnormA).mp hx).1))
      (Subgroup.inclusion_injective _)
  have hxne : (X.Q i ⊓ X.Q (i + 1)).relIndex (relCent (X.Q i) A (X.edgeSylow i)) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hm := Subgroup.relIndex_mul_relIndex (H := A) (K := X.Q i ⊓ X.Q (i + 1))
    (L := relCent (X.Q i) A (X.edgeSylow i)) hD_le hDS
  rw [hDrel] at hm
  have hxpos : 0 < (X.Q i ⊓ X.Q (i + 1)).relIndex
      (relCent (X.Q i) A (X.edgeSylow i)) := Nat.pos_of_ne_zero hxne
  omega

theorem Setup.natQuot_Q_of_normal (X : Setup Γ G)
    (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G s) (h4 : 4 ≤ s) (i : ℤ)
    (hni : X.n i = 2) (hn1 : X.n (i + 1) = 2)
    (hA : X.Gi i ≤ Subgroup.normalizer
      ((X.Q (i - 1) ⊓ X.Q (i + 1) : Subgroup G) : Set G))
    (hquad : ⁅⁅X.Q i, X.edgeSylow i⁆, X.edgeSylow i⁆ ≤ X.Q (i - 1) ⊓ X.Q (i + 1)) :
    NatQuot (X.L i) (X.Q i) (X.Q (i - 1) ⊓ X.Q (i + 1)) 2 := by
  haveI : Finite ↥(X.Gi i) := X.hyp.finite_stab (X.vert i)
  exact natQuot_of_four_le (X.a5Pre_Q_of_normal hc hs h4 i hni hn1 hA)
    (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi i)) (X.Q_le_Gi i))
    (X.isSylowTwoOf_edgeSylow_L i)
    (X.four_le_relIndex_relCent_edgeSylow hc hs h4 i hn1 hA hquad)

end CFSG.Quasithin.St84
