module

public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlatMarking
public import CFSG.LocalAnalysis.StandardType.GGAssemblyNineDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneSix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGAutKCanonIIIFlatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ K : Subgroup G) (m : G), GGAutKConjConfig p B Bs x L D J b L₁ K m →
      ∀ [((ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).Normal],
        GGHypRestIIIFlat p
          (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))
          (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))

@[expose] def GGAutKCanonIVCompInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ K : Subgroup G) (m : G), GGAutKConjConfig p B Bs x L D J b L₁ K m →
      ∀ [((ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).Normal],
        GGHypRestIVComponentwise p
          (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))

@[expose] def GGSixAutKHypRestAtFlatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ b ∈ Bs, b ≠ 1 → ∀ L₁ : Subgroup G,
      IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
      ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
        ¬ K ≤ ggM p B x L D J →
        ∀ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} →
          ∃ (W' : Type) (_ : Group W') (_ : Finite W') (π : ↥(ggAutKW D K m) →* W'),
            Function.Surjective π ∧
            π.ker ≤ (ggAutKH D K (ggM p B x L D J) m ⊓
              Subgroup.centralizer (K : Set G)).subgroupOf (ggAutKW D K m) ∧
            GGHypThreeSixteenRestFlat p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π)

@[expose] def GGStepTwoAutKRestFlatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
      ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
        ¬ K ≤ ggM p B x L D J →
        ∃ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} ∧
          ∃ (W' : Type) (_ : Group W') (_ : Finite W') (π : ↥(ggAutKW D K m) →* W'),
            Function.Surjective π ∧
            π.ker ≤ (ggAutKH D K (ggM p B x L D J) m ⊓
              Subgroup.centralizer (K : Set G)).subgroupOf (ggAutKW D K m) ∧
            GGHypThreeSixteenRestFlat p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π) ∧
            ¬ GGFusionException p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π)

theorem ggStepTwoComponentInput_of_kgroupLayerFlat (h313 : GGLemmaThreeThirteenInput)
    (hKF : GGKGroupFusionLayerInputFlat) (hR : GGStepTwoAutKRestFlatInput) :
    GGStepTwoComponentInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair K hK hLK
  by_contra hKM
  obtain ⟨m, hm, hEC, W', _, _, π, hπ, hker, hrest, hexc⟩ :=
    hR G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair K hK hLK hKM
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, ⟨⟨-, hDel, hDcard, -⟩, -⟩, -⟩ := hctx.2
  obtain ⟨⟨hBBs, -, -⟩, ⟨⟨hDB, -⟩, -⟩, -, -, -, ⟨hBsM, -⟩, -⟩ := hctx.2
  have hfusE : GGControlsStrongFusion (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine s1.2.1.of_map_conj_le ((ggM p B x L D J).inv_mem hm) ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  have hE0el : IsElemAbelian p (D.map (MulAut.conj m⁻¹).toMonoidHom) :=
    isElemAbelian_map_hom hDel _
  have hE0card : Nat.card (D.map (MulAut.conj m⁻¹).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hDcard]
  have hnorm : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    h313 G p hp hp2 (Subgroup.centralizer {b}) (ggM p B x L D J ⊓ Subgroup.centralizer {b}) _
      (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1
        (ggStepTwo_centralizer_ne_top hctx.1.2.1 hpair.2.1))
      hE0el hE0card (hfusE.inf_in hEC) K hK (fun h => hKM (h.trans inf_le_left))
  have hEM : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ ggM p B x L D J := hfusE.1
  have hH₀C : D.map (MulAut.conj m⁻¹).toMonoidHom ⊔ (K ⊓ ggM p B x L D J) ≤
      ggM p B x L D J ⊓ Subgroup.centralizer {b} :=
    sup_le (le_inf hEM hEC) (le_inf inf_le_right (inf_le_left.trans hK.1))
  have hyp := And.intro (ggAutK_hypOne hp hp2 hfusE hE0el hE0card hnorm hKM π hπ hker) hrest
  have hlayer := ggAutK_layer_ne_bot hpair.isComponentOf_inf hLK hpair.le_ggM hH₀C π hker
  have hWle : ggAutKW D K m ≤ Subgroup.centralizer {b} := sup_le hEC hK.1
  have hWne : ggAutKW D K m ≠ ⊤ := fun h =>
    ggStepTwo_centralizer_ne_top hctx.1.2.1 hpair.2.1 (top_le_iff.mp (h ▸ hWle))
  have hKW : CFSG.Open.IsKGroup W' :=
    (CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup hctx.1.2.2.1 _
      hWne).of_surjective π hπ
  rcases hKF W' hKW p _ _ hyp hlayer with htop | hex
  · apply hKM
    have hker' : π.ker ≤ (ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m) :=
      fun w hw => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hker hw))).1
    exact (le_sup_right.trans (ggAutK_le_of_map_eq_top π hker' htop)).trans
      (sup_le hEM inf_le_right)
  · exact hexc hex

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggSixStepTwoV2I1Input_of_schreierLayerFlat (hSch : SchreierFor InCatalog)
    (h613 : GGStepTwoLemmaSixThirteenInput) (hA : GGStepTwoLinearFusionEqInput)
    (hKF : GGKGroupFusionLayerInputFlat) (hR : GGStepTwoAutKRestFlatInput)
    (h615 : GGStepTwoCentralizerInput) : GGSixStepTwoV2I1Input :=
  ggSixStepTwoV2I1Input_of_inputs h613 hA
    (ggStepTwoSubnormalInput_of_split (ggLemmaThreeFourteenInput_of_schreier hSch)
      (ggStepTwoComponentInput_of_kgroupLayerFlat ggLemmaThreeThirteenInput_holds hKF hR)) h615

end Inputs

end CFSG.StandardType
