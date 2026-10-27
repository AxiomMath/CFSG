module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeSixCube
public import CFSG.LocalAnalysis.StandardType.GGTwE6R5Torus
public import CFSG.RankThree.PartTwo.Sec19.Item1923InnerCore
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.RankThree.PartTwo.Sec18.SylowWStar
public import CFSG.RankThree.PartTwo.Sec19.Item194Five
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec20.Alt20
public import CFSG.RankThree.PartTwo.Sec20.Item203OneProof
public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofNormal
public import CFSG.RankThree.PartTwo.Sec20.OneSteps

public noncomputable section

namespace CFSG.StandardType.QTwoE6

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.TwE6D3
  CFSG.RankThree.PartTwo.Late
  CFSG.ComponentClassification.OuterAutomorphisms

variable {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
  {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
  (hgn : g⁻¹ * CFSG.RankThree.Classical2.twistE6 Ω Fr g =
    CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.n0 Ω)

include hg hgn in
theorem card_langCube_inf_inner :
    Nat.card ↥(TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g ⊓
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* MulAut _).range) =
        3 ^ 5 := by
  let Y := TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g
  let I : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
    (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* MulAut _).range
  have h3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hY := TwE6DD2.isElemAbelian_langCube (n := 1) le_rfl hK σ hσ Fr hFr g
  have hcard : Nat.card ↥Y = 3 ^ 6 :=
    TwE6DD2.card_langCube (n := 1) le_rfl hK σ hσ Fr hFr h3 hg hgn
  letI : Finite ↥Y := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨ρ, h, hρ, hh, _, hinv, hlarge⟩ :=
    TwE6DD2.reflData_langCube (n := 1) le_rfl hK σ hσ h3 Fr hFr hg hgn
  have hhI : ∀ i, h i ∈ I := fun i =>
    mem_inner_of_inverted (hρ i) (hY.2 (h i) (hh i)) (hinv i)
  have hH : Subgroup.closure (Set.range h) ≤ Y ⊓ I := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨hh i, hhI i⟩
  have hlo : 3 ^ 5 ≤ Nat.card ↥(Y ⊓ I) :=
    hlarge.trans (Subgroup.card_le_of_le hH)
  have hnot : ¬ Y ≤ I :=
    TwE6R5.langCube_not_le_inn (n := 1) le_rfl hK σ hσ Fr hFr h3
      (by norm_num) hg hgn
  have hlt : Nat.card ↥(Y ⊓ I) < Nat.card ↥Y := by
    apply Subgroup.card_lt_of_lt
    exact lt_of_le_of_ne inf_le_left (fun heq => hnot (heq.symm ▸ inf_le_right))
  have hYI : IsElemAbelian 3 (Y ⊓ I) := hY.mono inf_le_left
  obtain ⟨k, hk⟩ := hYI.isPGroup.exists_card_eq
  rw [hk] at hlo hlt
  rw [hcard] at hlt
  have hklo : 5 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hlo
  have hkhi : k < 6 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hlt
  have hkeq : k = 5 := by omega
  simpa only [Y, I, hk, hkeq]

include hg hgn in
theorem eq_langCube_inf_inner_of_card {S : Subgroup
    (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hSY : S ≤ TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g)
    (hSI : S ≤ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* MulAut _).range)
    (hS : Nat.card S = 3 ^ 5) :
    S = TwE6DD2.langCube (n := 1) le_rfl hK σ hσ Fr hFr g ⊓
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* MulAut _).range := by
  apply Subgroup.eq_of_le_of_card_ge (le_inf hSY hSI)
  rw [card_langCube_inf_inner hK σ hσ Fr hFr hg hgn, hS]

end CFSG.StandardType.QTwoE6

end
