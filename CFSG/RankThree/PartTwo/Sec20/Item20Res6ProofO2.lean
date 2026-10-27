module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofSteps
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec18.Item181b
import CFSG.RankThree.PartTwo.Late.Item2010

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Step202KY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G), Hyp201One G A M L N c →
    ∀ X ∈ scriptM ((A ⊔ kTwenty M c : Subgroup G) : Set G), X ≠ M →
      CFSG.Open.pCoreOf 2 (X ⊓ M) ≠ CFSG.Open.pCoreOf 2 X →
      ∀ Y ∈ oTwoComponentsIn X, ∀ S : Subgroup G,
        CFSG.ABGLocalTools.IsSylowOf 2 S (inSubgroup (CFSG.pPrimeCore 3) (X ⊓ M)) →
        Y ⊔ A ⊔ S ∈ scriptH A M →
        sectionCentralizer A (inSubgroup perfectResidual (Y ⊔ A ⊔ S))
            (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual (Y ⊔ A ⊔ S))) =
          (Subgroup.zpowers c : Set G) →
          Y ≤ Subgroup.normalizer (kTwenty M c : Set G)

theorem Res6.orderOf_c_of_hyp201One (h184 : Sec18.Item184_1) {G : Type} [Group G] [Finite G]
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) : orderOf c = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H, hH18, -, -, -⟩ := exists_sec18H_of_hyp201One h
  obtain ⟨-, c₀, hc₀, hc₀eq⟩ := h184 G A M hH18.toSec18Std H hH18.mem_scriptH
  have hcA : c ∈ A := mem_of_hyp201 h.1
  have hc3 : c ^ 3 = 1 := (isE27_of_mem_partTwoE h.1.mem_partTwoE).1.2 c hcA
  refine orderOf_eq_prime hc3 ?_
  rintro rfl
  have h1 : (c₀ : G) ∈ (Subgroup.zpowers (1 : G) : Set G) := by
    rw [← hH18.centralizer_eq, hc₀eq]
    exact Subgroup.mem_zpowers c₀
  have h2 : c₀ = 1 := by simpa using h1
  rw [h2, orderOf_one] at hc₀
  omega

theorem step202O2_of (h1811 : Sec18.Item181_1) (h184 : Sec18.Item184_1)
    (h1843 : Sec18.Item184_3) (h1810 : Sec18.Item1810Hyp) (hKY : Step202KY) : Step202O2 := by
  intro G _ _ A M L N c h X hX
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup G := h.1.isSimpleGroup
  have h18 : Sec18Std G A M := sec18Std_of_hyp201 h.1
  set K := kTwenty M c with hKdef
  have hAX : A ≤ X := fun a ha => hX.2 (Subgroup.mem_sup_left ha)
  have hAM : A ≤ M := le_of_hyp201 h.1
  have hKM : K ≤ M := kTwenty_le_of_hyp201 h.1
  have hXM : X ≠ M := by
    rintro rfl
    exact hne (by rw [inf_idem])
  have hle := Sec18.pCoreOf_le_pCoreOf_inf h18 hAX
  have hO : inSubgroup (CFSG.pPrimeCore 3) X ≠ inSubgroup (CFSG.pPrimeCore 3) (X ⊓ M) :=
    fun heq => hne (le_antisymm (Late.pCoreOf_inf_le_of_pPrimeCore_eq heq) hle)
  have hXtop : X ≠ ⊤ :=
    Late.ne_top_of_pCoreOf_ne_bot h.1.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal hX.1)
  obtain ⟨Y, hY, S, hS, hI⟩ := h1811 G A M h18 X hAX hXtop hO
  obtain ⟨H, hH18, hH187, -, -⟩ := exists_sec18H_of_hyp201One h
  obtain ⟨w, hw, hcent⟩ := h1843 G A M H c hH18 _ hI
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (Subgroup.normalizer (A : Set G))
  have hconj := h1810 G A M H c hH18 hH187 P hP
  have hA3 : IsPGroup 3 A := (isE27_of_mem_partTwoE h.1.mem_partTwoE).isPGroup
  have hAP : A ≤ P :=
    Res6.le_of_isSylowOf_of_le_normalizer hA3 Subgroup.le_normalizer le_rfl le_rfl hP
  have hcA : c ∈ A := mem_of_hyp201 h.1
  have hcw : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers c := by
    have hmem : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom ∈
        Sec18.conjugatesIn (Subgroup.zpowers c) P := by
      refine ⟨⟨w, rfl⟩, ?_⟩
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact hAP ((Subgroup.mem_normalizer_iff.mp hw c).mp hcA)
    rw [hconj] at hmem
    exact hmem
  rw [hcw] at hcent
  have hYK := hKY G A M L N c h X hX hXM hne Y hY S hS hI hcent
  have hc := Res6.orderOf_c_of_hyp201One h184 h
  have hK2 : ¬ IsPGroup 2 K := fun hK2 =>
    Res6.not_mem_of_isPGroup_two hK2 hc (self_mem_normalClosureIn M c)
  have hNK : Subgroup.normalizer (K : Set G) ≤ M :=
    Res6.normalizer_le_of_le_normalizer h.1.charTwoType h.1.mem_scriptM.1 hKM
      (le_normalizer_normalClosureIn M c) hK2
  have hIM : Y ⊔ A ⊔ S ≤ M :=
    sup_le (sup_le (hYK.trans hNK) hAM)
      (hS.le.trans ((Subgroup.map_subtype_le _).trans inf_le_right))
  exact Sec18.perfectResidual_not_le_of_mem_scriptH h18 hI
    ((Subgroup.map_subtype_le _).trans hIM)

end CFSG.RankThree.PartTwo.Sec20
