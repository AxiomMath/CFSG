module

public import CFSG.RankThree.PartTwo.Sec4.RonanK423D4Gen
public import CFSG.RankThree.PartTwo.Sec4.RonanK423D4Two
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFinalInner
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.DataGlue

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423.D4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Res423Two
  CFSG.RankThree.PartTwo.Sec4.RonanK423 CFSG.RankThree.PartTwo.Sec19
  CFSG.AGLEmbeddingD2.Wilson.Census423Three

theorem isoLie_of_trialityD4
    {X M : Type} [Group X] [Group M] (e : X ≃* M) {f : ℕ}
    (hX : Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f) :
    ∃ q : TauCeti.PrimePower, q.p = 2 ∧
      CFSG.RankThree.PartOne.Census3.IsoLie M (.trialityD4 q) := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, σ, hσ, ⟨ι⟩⟩ := hX
  let q : TauCeti.PrimePower := ⟨2, f, hp, by omega⟩
  have hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid := TauCeti.LieTypeIndex.valid_trialityD4 q
  have hK' : Nat.card K = q.card ^ Blueprint.Chevalley.TwistTag.D4.order := by
    rw [hK, TauCeti.PrimePower.card_def]
  have hσ' : ∀ x, σ x = x ^ q.card := fun x => by rw [hσ, TauCeti.PrimePower.card_def]
  obtain ⟨e'⟩ : Nonempty (Blueprint.DerivedCentralQuotient
      (Blueprint.twistedFixedGroup .D4 K σ) ≃*
        TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) :=
    CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv rfl K hK' σ hσ'
  exact ⟨q, rfl, hv, ⟨e.symm.trans (ι.trans e')⟩⟩

theorem hgen_of_inner
    (hT : TrialityThreeInner) {X M : Type} [Group X] [Group M] [Finite M]
    [IsSimpleGroup M] (e : X ≃* M) {f : ℕ}
    (hX : Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f) (hZ : Subgroup.center M = ⊥) :
    ∀ D : Subgroup M, (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) → (∀ x ∈ D, x ^ 3 = 1) →
      Nat.card D = 9 → (⊤ : Subgroup M) ≤
        Subgroup.closure {x : M | ∃ b ∈ D, b ≠ 1 ∧ x * b = b * x} := by
  obtain ⟨q, hq2, hiso⟩ := isoLie_of_trialityD4 e hX
  intro D hDc hDexp hD9
  have hinj := conj_injective_of_center hZ
  have hEel : CFSG.IsElementaryAbelian 3 (D.map (MulAut.conj : M →* MulAut M)) := by
    refine isElementaryAbelian_three_of ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      show MulAut.conj a * MulAut.conj b = MulAut.conj b * MulAut.conj a
      rw [← map_mul, ← map_mul, hDc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      show (MulAut.conj a) ^ 3 = 1
      rw [← map_pow, hDexp a ha, map_one]
  have hcard : Nat.card (D.map (MulAut.conj : M →* MulAut M)) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj, hD9]
    norm_num
  have hinner : ∀ φ ∈ D.map (MulAut.conj : M →* MulAut M), ∃ g : M, φ = MulAut.conj g := by
    rintro _ ⟨d, -, rfl⟩
    exact ⟨d, rfl⟩
  exact closure_centralizers_of_planes (hT q hq2 M hiso _ hEel hcard hinner)

end CFSG.RankThree.PartTwo.Sec4.RonanK423.D4

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423

open CFSG.RankThree.PartTwo.Sec19 CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.AGLEmbeddingD2.Wilson.Census423Three

theorem census423_of_trialityD4_ge4
    {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f) (hq : CFSG.IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) : Census423 X := by
  obtain ⟨K, _, _, _, σ, hK, hσ, hσ3, hf1, hsimple, ⟨e⟩⟩ :=
    Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hX
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv X e.toEquiv
  exact census423_of_equiv_alpha e fun D hDc hDexp hD9 =>
    D4.alphaVanishes_C0_big CFSG.Goldschmidt.topStatement ⟨hf1, hK, hσ⟩ hf hDc hDexp hD9

theorem census423_of_trialityD4
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f) (hq : CFSG.IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) : Census423 X := by
  by_cases hf2 : 2 ≤ f
  · exact census423_of_trialityD4_ge4 hf2 hX hq hZ
  · have hf : f = 1 := by
      have := hX.1.2.1
      omega
    subst hf
    obtain ⟨K, _, _, _, σ, hK, hσ, hσ3, hf1, hsimple, ⟨e⟩⟩ :=
      Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hX
    haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Finite.of_equiv X e.toEquiv
    haveI : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := hsimple
    have P : D4Par 1 K σ := ⟨hf1, hK, hσ⟩
    exact census423_of_equiv_alpha e fun D hDc hDexp hD9 =>
      D4.alphaVanishes_C0_two P
        (D4.hgen_of_inner trialityThreeInner_holds e hX (D4.center_C0_eq_bot P)) hDc hDexp hD9

end CFSG.RankThree.PartTwo.Sec4.RonanK423
