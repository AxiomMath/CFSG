module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofInner
public import CFSG.LieType.SeitzGeneration.OuterNarrowThree
public import CFSG.LieType.SeitzGeneration.OuterLinearCat
public import CFSG.LieType.SeitzGeneration.OuterSUCat
public import CFSG.LieType.SeitzGeneration.OuterHeisCoreProof
public import CFSG.LieType.SeitzGeneration.OuterCoreProof
public import CFSG.LieType.SeitzGeneration.OuterSmallCases
public import CFSG.LieType.SeitzGeneration.SubfieldPairSLLtProof
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUOddProof
import all CFSG.LieType.SeitzGeneration.OuterSUData
import all CFSG.LieType.SeitzGeneration.OuterSUCat

public section

namespace CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof

open CFSG.LieType.SeitzGeneration

section SUPair

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration.SUPair

theorem subfieldPairSUOdd_three_three {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (f₀ : ℕ) (k : Subfield K) (h₀ : UnitaryFieldData ℓ f₀ k)
    (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (hf : f = 3 * f₀)
    (hgq : ¬ (3 ∣ 3 ∧ 3 ∣ ℓ ^ f₀ + 1))
    (A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hne : (suSub h h₀ hbar 3).map (primeFormConjSU h _ A).toMonoidHom ≠ suSub h h₀ hbar 3) :
    Subgroup.closure ((suSub h h₀ hbar 3 : Set (gramSU h
        ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) ∪
      ((suSub h h₀ hbar 3).map (primeFormConjSU h _ A).toMonoidHom : Set (gramSU h
        ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))) = ⊤ := by
  by_cases hq : ℓ ^ f₀ = 2
  · exact absurd ⟨dvd_refl 3, by rw [hq]⟩ hgq
  · exact subfieldPairSUOdd_of_ne_two ℓ f f₀ K h k h₀ hbar 3 Nat.prime_three (by norm_num) hf hq 3
      le_rfl A hne

end SUPair

section Data

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Sec66T (center_eq_bot_of_simple')

variable {n : ℕ}

theorem fieldAutData_primeFormP_of_pair (hn3 : 3 ≤ n)
    {ℓ f p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hpair : ∀ (f₀ : ℕ) (k : Subfield K) (h₀ : UnitaryFieldData ℓ f₀ k)
      (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c), f = p * f₀ → ¬ (p ∣ n ∧ p ∣ ℓ ^ f₀ + 1) →
      ∀ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        (suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom ≠ suSub h h₀ hbar n →
        Subgroup.closure ((suSub h h₀ hbar n : Set (gramSU h
            ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∪
          ((suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom : Set (gramSU h
            ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) = ⊤)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1)) : FieldAutData (primeFormP h (idGram K n)) p :=
  fieldAutData_primeFormP_of_instance hn3 h
    (fun f₀ k h₀ hbar hf hgq _ A hne' => hpair f₀ k h₀ hbar hf hgq A hne') hne hp hp2 hpℓ hg

end Data

section Model

open Matrix CFSG.Open CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.CTP

theorem planeGen_outer_su_model_of_pair {d : TauCeti.ValidLieTypeIndex}
    {n ℓ f p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hpair : ∀ (f₀ : ℕ) (k : Subfield K) (h₀ : UnitaryFieldData ℓ f₀ k)
      (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c), f = p * f₀ → ¬ (p ∣ n ∧ p ∣ ℓ ^ f₀ + 1) →
      ∀ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        (suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom ≠ suSub h h₀ hbar n →
        Subgroup.closure ((suSub h h₀ hbar n : Set (gramSU h
            ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∪
          ((suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom : Set (gramSU h
            ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) = ⊤)
    (e : Cat d ≃* primeFormP h (idGram K n)) (hn3 : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ InnerPlane d p E) : PlaneGen E :=
  planeGen_outer_su_model_of_fieldAutData h e hn3 hne hp
    (fieldAutData_primeFormP_of_pair hn3 h hpair hne hp hp2 hpℓ hg) hE hc hout

theorem planeGen_outer_twistedA_three {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hpq : 3 ≠ q.p) (hlift : ¬ 3 ∣ q.card + 1)
    {E : Subgroup (MulAut (Cat ⟨.twistedA 2 q, hv⟩))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) (hout : ¬ InnerPlane ⟨.twistedA 2 q, hv⟩ 3 E) : PlaneGen E := by
  obtain ⟨hℓ, hf, hn3, hne, F, _, hU, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
        (MulEquiv.refl (Cat ⟨.twistedA 2 q, hv⟩)))
  refine planeGen_outer_su_model_of_pair hU (subfieldPairSUOdd_three_three hU) θ hn3 hne
    Nat.prime_three (by norm_num) hpq ?_ hE hc hout
  intro hd
  apply hlift
  rw [TauCeti.PrimePower.card_def]
  exact hd.trans (Nat.gcd_dvd_right _ _)

end Model

open CFSG.Open CFSG.AGLEmbeddingD2

theorem seitzThreeLThreePiOuterNarrow :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧ p = 3 ∧
      IsLThreePiIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hs, rfl, q, hd | hd⟩
  · subst hd
    by_cases hq : 3 ∣ q.card - 1
    · exact seitzOuter_A2_three outerHeisCore ⟨.A 2 q, hv⟩ 3 hp hp2 hpd hex E hE hc
        ⟨hout, hs, ⟨2, q, rfl⟩, rfl, q, rfl, hq⟩
    · refine seitzOuter_linear subfieldPairSLLt ⟨.A 2 q, hv⟩ 3 hp hp2 hpd hex E hE hc
        ⟨hout, hs, ⟨2, q, rfl⟩, ?_⟩
      rintro ⟨-, q', hq', h⟩
      cases hq'
      exact hq h
  · subst hd
    by_cases hq : 3 ∣ q.card + 1
    · exact seitzOuter_twistedA2_three unitaryHeisCore (unitaryOuterHeisCore_of_finite_cases
        HeisSmall.outerB12AtCard_five HeisSmall.outerB12AtCard_eight HeisSmall.outerB12AtCard_eleven) ⟨.twistedA 2 q, hv⟩ 3
        hp hp2 hpd hex E hE hc ⟨hout, hs, ⟨2, q, rfl⟩, rfl, q, rfl, hq⟩
    · exact planeGen_outer_twistedA_three hv (by simpa using hpd) hq hE hc hout

theorem seitzThreeLThreePi_of_field
    (h : SeitzThreeLThreePiField) :
    SeitzThreeLThreePi := by
  intro d p hp hp2 hpd hex E hE hc ⟨hp3, hd⟩
  by_cases hin : InnerPlane d p E
  · exact seitzThreeLThreePiInner d p hp hp2 hpd hex E hE hc ⟨hin, hp3, hd⟩
  · by_cases hs : NarrowScope p E
    · exact seitzThreeLThreePiOuterNarrow d p hp hp2 hpd hex E hE hc ⟨hin, hs, hp3, hd⟩
    · exact h d p hp hp2 hpd hex E hE hc ⟨hin, hs, hp3, hd⟩

end CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof
