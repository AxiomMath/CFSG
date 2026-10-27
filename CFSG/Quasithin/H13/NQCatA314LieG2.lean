module

public import CFSG.Quasithin.H13.NQCatA314LieGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem lieP_perfectCore_G2
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (j : Fin 2) :
    LieP (Nat.card K = 4) (perfectCore ((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf
      (adjointGroup Tag.G2 K))) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hPC : parabolicSubgroup Tag.G2 K {g2Index j} ≤ adjointGroup Tag.G2 K :=
    parabolicSubgroup_le_adjointGroup _ _ _
  have hF : ParabolicFacts (parabolicSubgroup Tag.G2 K {g2Index j})
      (parabolicRadical Tag.G2 K {g2Index j}) := by
    rcases G2.fin_two_cases (g2Index j) with h | h
    · rw [h]
      exact G2.parabolicFacts_zero hK hf
    · rw [h]
      exact G2.parabolicFacts_one hK hf
  have hX : LieP True (perfectCore ((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf
      (adjointGroup Tag.G2 K))) :=
    lieP_perfectCore_subgroupOf_of hPC fun hA => ⟨charTwo_of_parabolicFacts hF hA, trivial⟩
  obtain ⟨g, hg, hker⟩ := exists_levi_hom_adjoint hK hf (g2Index j)
  exact lieP_of_sl2 hK4 g hg hker fun hA h => ⟨(hX hA).1, h⟩

theorem lieP_g2
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 2 ≤ f) (hL : IsG2 2 f ↥L) (hP : IsMaxParabolic2 L P) :
    LieP (f = 2) (perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine lieP_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨-, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU₀ : IsSylowTwoOf ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  refine (lieP_perfectCore_of_equiv e ?_).mono (eq_two_of_card_eq_four hK)
  exact lieP_perfectCore_parabolic hU₀ G2_residualOvergroupsAt
    (fun j => lieP_perfectCore_G2 hK hf j) (isParabolic2_top_map_equiv e hpa)
    (CFSG.QuasithinUnique.A5.G3.map_ne_top_of_equiv e hna)

end CFSG.Quasithin.H13.NQCat.A314D
