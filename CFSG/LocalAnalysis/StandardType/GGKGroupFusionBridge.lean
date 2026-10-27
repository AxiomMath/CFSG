module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitz
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoAutK
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteen
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteenP

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Layer

variable {G : Type} [Group G]

theorem ggIsComponentOf_map {G' : Type} [Group G'] (f : G →* G') {L X : Subgroup G}
    (hL : IsComponentOf L X) (hLf : ¬ L ≤ f.ker) : IsComponentOf (L.map f) (X.map f) := by
  obtain ⟨hLX, hs, hq⟩ := hL
  refine ⟨Subgroup.map_mono hLX, ?_, ?_⟩
  · exact (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open _ _).2
      (CFSG.ComponentClassification.Components.chain_map f
        ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open L X).1 hs))
  · rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
    exact CFSG.LocalCores.isQuasisimple_map hq f hLf

theorem ggComponent_not_commute {L H : Subgroup G} (hL : IsComponentOf L H) :
    ¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
  intro hc
  have : Group.IsSolvable L := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (hc a a.2 b b.2)
  exact ggComponent_not_le_of_isSolvable hL this le_rfl

theorem ggAutK_layer_ne_bot [Finite G] {E₀ K M C L₁ : Subgroup G} (hL₁ : IsComponentOf L₁ C)
    (hL₁K : L₁ ≤ K) (hL₁M : L₁ ≤ M) (hH₀C : E₀ ⊔ (K ⊓ M) ≤ C) {W' : Type} [Group W']
    [Finite W'] (π : ↥(E₀ ⊔ K) →* W')
    (hker : π.ker ≤ ((E₀ ⊔ (K ⊓ M)) ⊓ Subgroup.centralizer (K : Set G)).subgroupOf (E₀ ⊔ K)) :
    LargeEvenLayer
      (⊤ : Subgroup (GGHypQuot (((E₀ ⊔ (K ⊓ M)).subgroupOf (E₀ ⊔ K)).map π))) ≠ ⊥ := by
  have hL₁H₀ : L₁ ≤ E₀ ⊔ (K ⊓ M) := (le_inf hL₁K hL₁M).trans le_sup_right
  have hcomp : IsComponentOf L₁ (E₀ ⊔ (K ⊓ M)) :=
    ⟨hL₁H₀, ggIsSubnormal_of_le_of_le hL₁.2.1 hL₁H₀ hH₀C, hL₁.2.2⟩
  have hH₀W₀ : E₀ ⊔ (K ⊓ M) ≤ E₀ ⊔ K := sup_le_sup_left inf_le_left E₀
  have hcomp' := ggIsComponentOf_subgroupOf hcomp hH₀W₀
  have hnotker : ¬ L₁.subgroupOf (E₀ ⊔ K) ≤ π.ker := by
    intro hle
    refine ggComponent_not_commute hL₁ fun x hx y hy => ?_
    have hxW : x ∈ E₀ ⊔ K := (hL₁K.trans le_sup_right) hx
    have hxk := hker (hle (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hxW⟩ : ↥(E₀ ⊔ K)) ∈ _))
    have hxC := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hxk)).2
    exact (Subgroup.mem_centralizer_iff.mp hxC y (hL₁K hy)).symm
  set Hb := ((E₀ ⊔ (K ⊓ M)).subgroupOf (E₀ ⊔ K)).map π
  have hcompW' : IsComponentOf ((L₁.subgroupOf (E₀ ⊔ K)).map π) Hb :=
    ggIsComponentOf_map π hcomp' hnotker
  have hX := ggIsComponentOf_subgroupOf hcompW' (le_refl Hb)
  rw [Subgroup.subgroupOf_self] at hX
  have hnot2 : ¬ ((L₁.subgroupOf (E₀ ⊔ K)).map π).subgroupOf Hb ≤
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Hb)).ker := by
    rw [QuotientGroup.ker_mk']
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥Hb) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
    exact ggComponent_not_le_of_isSolvable hX inferInstance
  have hQ := ggIsComponentOf_map (QuotientGroup.mk' (CFSG.pCore 2 ↥Hb)) hX hnot2
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hQ
  intro hbot
  have hle : (((L₁.subgroupOf (E₀ ⊔ K)).map π).subgroupOf Hb).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Hb)) ≤ LargeEvenLayer (⊤ : Subgroup (GGHypQuot Hb)) :=
    le_sSup hQ
  rw [hbot] at hle
  exact ggComponent_ne_bot hQ (le_bot_iff.mp hle)

end Layer

section Inputs

theorem ggStepTwoComponentInput_of_kgroupLayer (h313 : GGLemmaThreeThirteenInput)
    (hKF : GGKGroupFusionLayerInput) (hR : GGStepTwoAutKRestInput) :
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
  rcases hKF W' p _ _ hyp hlayer with htop | hex
  · apply hKM
    have hker' : π.ker ≤ (ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m) :=
      fun w hw => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hker hw))).1
    exact (le_sup_right.trans (ggAutK_le_of_map_eq_top π hker' htop)).trans
      (sup_le hEM inf_le_right)
  · exact hexc hex

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggSixStepTwoV2Input_of_schreierLayer (hSch : SchreierFor InCatalog)
    (h613 : GGStepTwoLemmaSixThirteenInput) (hA : GGStepTwoLinearFusionInput)
    (hKF : GGKGroupFusionLayerInput) (hR : GGStepTwoAutKRestInput)
    (h615 : GGStepTwoCentralizerInput) : GGSixStepTwoV2Input :=
  ggSixStepTwoV2Input_of_inputs h613 hA
    (ggStepTwoSubnormalInput_of_split (ggLemmaThreeFourteenInput_of_schreier hSch)
      (ggStepTwoComponentInput_of_kgroupLayer ggLemmaThreeThirteenInput_holds hKF hR)) h615

open CFSG.LocalAnalysis.ComponentInitial CFSG.AGLEmbeddingD2 in
theorem ggSixStepTwoV2Input_of_kgroupFamilies (hSch : SchreierFor InCatalog)
    (hS : KFactSeitzRankTwo) (hKA : GGKGroupFusionAt GGKFAlternating)
    (hKD : GGKGroupFusionAt GGKFLieDefining) (hKX : GGKGroupFusionAt GGKFLieSeitzException)
    (hKS : GGKGroupFusionAt GGKFSporadic) (h613 : GGStepTwoLemmaSixThirteenInput)
    (hA : GGStepTwoLinearFusionInput) (hR : GGStepTwoAutKRestInput)
    (h615 : GGStepTwoCentralizerInput) : GGSixStepTwoV2Input :=
  ggSixStepTwoV2Input_of_schreierLayer hSch h613 hA
    (ggKGroupFusionLayerInput_of_families hSch hS hKA hKD hKX hKS) hR h615

end Inputs

end CFSG.StandardType
