module

public import CFSG.LocalAnalysis.StandardType.ExcPay.CoreGen

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F


private theorem excPayC_label_three {G : Type} [Group G] [Finite G] {p f : ℕ} [NeZero f]
    {Bs X : Subgroup G} {ht : GGExcFive .E7} (hp : p.Prime) (hp2 : p ≠ 2)
    (hplus : p ∣ 2 ^ f + 1) (S : ExcPaySquare .E7 ht f p Bs X) {i j : Fin 7}
    (h3 : CoxeterMatrix.E₇ i j = 3) :
    ∃ W : Subgroup G, UnitaryBlockStandardPair (actualQuadraticSubfield f) 2 f W
      (ggRankOneIn X Bs (S.s i)) (ggRankOneIn X Bs (S.s j)) := by
  obtain ⟨θG, -, -, -, -, hpair⟩ :=
    excPaySquare_pair (Or.inr (Or.inl rfl)) hp hp2 hplus S (isA2Pair_simple_E7 h3)
  exact ⟨θG.range, hpair⟩

private theorem excPayC_rankOne_iso {G : Type} [Group G] [Finite G] {p f : ℕ} [NeZero f]
    {Bs X : Subgroup G} {ht : GGExcFive .E7} (hp : p.Prime) (hp2 : p ≠ 2)
    (hplus : p ∣ 2 ^ f + 1) (S : ExcPaySquare .E7 ht f p Bs X) (i : Fin 7) :
    Nonempty (Su (actualQuadraticSubfield f) 2 f 2 ≃* ggRankOneIn X Bs (S.s i)) := by
  obtain ⟨j, hj⟩ := exists_edge_E7 i
  obtain ⟨θG, hθinj, -, hB12, -, -⟩ :=
    excPaySquare_pair (Or.inr (Or.inl rfl)) hp hp2 hplus S (isA2Pair_simple_E7 hj)
  refine ⟨(MonoidHom.ofInjective
    (CFSG.LieType.Steinberg.embSUid_injective
      (CFSG.LieType.BorelTits.unitaryInvolution
        (actualQuadraticSubfield f) 2 f) 2)).trans ?_⟩
  exact (Subgroup.equivMapOfInjective (B12 (actualQuadraticSubfield f) 2 f) θG hθinj).trans
    (MulEquiv.subgroupCongr hB12)

theorem excPhanPayloadOf_E7_of_square {G : Type} [Group G] [Finite G] {p f : ℕ}
    {Bs X : Subgroup G} {ht : GGExcFive .E7} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 2 ≤ f)
    (hplus : p ∣ 2 ^ f + 1)
    (hCQ : IsCentralQuotientOf (lieUniversal .E7 0 2 f Nat.prime_two) ↥X)
    (S : ExcPaySquare .E7 ht f p Bs X) :
    GGExcPhanPayloadOf 7 CoxeterMatrix.E₇ .E7 p Bs X := by
  have hne : NeZero f := ⟨by omega⟩
  have hq : 4 ≤ 2 ^ f := by
    have h : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    simpa using h
  have hcard : Nat.card (actualQuadraticSubfield f) = (2 ^ f) ^ 2 :=
    card_actualQuadraticSubfield (f := f) (by omega)
  refine ⟨f, hq, hCQ, S.s, ?_, actualQuadraticSubfield f, inferInstance, inferInstance,
    inferInstance, hcard, ?_, ?_, ?_⟩
  · intro i
    exact ⟨S.s_mem i, S.s_refl i⟩
  · intro i
    exact excPayC_rankOne_iso hp hp2 hplus S i
  · intro i j hij h2
    exact excPaySquare_comm (Or.inr (Or.inl rfl)) hp hp2 S (orth_simple_E7 hij h2)
  · intro i j h3
    exact excPayC_label_three hp hp2 hplus S h3

end CFSG.StandardType.ExcPay
