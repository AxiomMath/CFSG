module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelH4Pieces
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
import CFSG.LocalAnalysis.StandardType.GGF4H4JBlockAux1
import CFSG.LocalAnalysis.StandardType.GGF4H4JBlockAux2
import CFSG.LocalAnalysis.StandardType.GGF4SmallBook
import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggF4JB_linear_block {G : Type} [Group G] [Finite G] {p f : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hMp : GGInnerDiagMpInput)
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagOn Bs L) (hf : 2 ≤ f)
    (hpf : p ∣ 2 ^ f - 1)
    (hLlab : GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L))
    (y : G) (K : Subgroup G) (hnbr : GGNbr p B x D J y K) :
    ∃ φ₁ : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 f) →* G,
      φ₁.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 f)) ∧
      (φ₁.comp (slLowerBlockHom 3 (GaloisField 2 f))).range = J := by
  have hΛ : LargeEvenInLambda2 (⟨.A, 3, f⟩ : LargeEvenLabel) :=
    ⟨le_trans (by norm_num : 1 ≤ 2) hf, by norm_num, fun h => absurd h (by norm_num)⟩
  have hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f :=
    statedClassicalModel_of_hasLabel_typeA hΛ hLlab
  have hL : GGTypeALocalCfg p B Bs x L D J 3 f y K :=
    ⟨hcfg, hInn, hmodel, hpf, by omega, hnbr⟩
  obtain ⟨φ₁, -, hker, -, hJ⟩ := ggF4JBx_exists_lift_L_lowerBlock hMp hL
  exact ⟨φ₁, hker, hJ⟩

theorem ggF4JB_linear {G : Type} [Group G] [Finite G] {p f : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hMp : GGInnerDiagMpInput)
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagOn Bs L) (hf : 2 ≤ f)
    (hpf : p ∣ 2 ^ f - 1)
    (hLlab : GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L))
    (y : G) (K : Subgroup G) (hnbr : GGNbr p B x D J y K) :
    GGHasLabel ⟨.A, 2, f⟩ (J ⧸ Subgroup.center J) ∧
      Nat.card (Subgroup.center J) = Nat.gcd 3 (2 ^ f - 1) := by
  obtain ⟨φ₁, hker, hJ⟩ :=
    ggF4JB_linear_block hMp hcfg hInn hf hpf hLlab y K hnbr
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hlab : GGHasLabel ⟨.A, 2, f⟩ (J ⧸ Subgroup.center J) :=
    ggF4JBx_hasLabel_J_of_lift hcardF (n := 3) (by omega) (by omega) hker hJ
  refine ⟨hlab, ?_⟩
  have hinj : Function.Injective (φ₁.comp (slLowerBlockHom 3 (GaloisField 2 f))) :=
    injective_comp_slLowerBlockHom (n := 3) (F := GaloisField 2 f) hker
  let eJ : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f) ≃* ↥J :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hJ)
  have hcenterJ : Nat.card (Subgroup.center ↥J) =
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f))) :=
    (Nat.card_congr (Subgroup.centerCongr eJ).toEquiv).symm
  rw [hcenterJ, ggF4JBx_card_center_SL_three f hcardF]

@[expose] def GGF4JBUnitaryHalf
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J ks → 2 ≤ f → p ∣ 2 ^ f + 1 →
    GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L) →
      GGHasLabel ⟨.twA, 2, f⟩ (J ⧸ Subgroup.center J) ∧
        Nat.card (Subgroup.center J) = Nat.gcd 3 (2 ^ f + 1)

theorem ggF4H4JBlock_of_unitary_half
    (hMp : GGInnerDiagMpInput) (hU : GGF4JBUnitaryHalf) :
    GGF4H4JBlock := by
  intro G _ _ p B Bs x L D J ks hres f hf
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hInn : GGInnerDiagOn Bs L := hres.1.1.2.2.1.1
  obtain ⟨ι, M, e, hP, hF⟩ := hres.2.2.1
  have hW4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizerJoin L Bs ks) :=
    ggF4Small_weylOfType_F4 e hP hF
  have hA3 : GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs) := hres.2.2.2.1
  obtain ⟨K, hK⟩ := ggF4Small_ks_nonempty hW4 hA3
  obtain ⟨y, hy⟩ := hres.1.2.2.2.1.2 K hK
  exact ⟨fun hpf hLlab => ggF4JB_linear hMp hcfg hInn hf hpf hLlab y K hy,
    fun hpf hLlab => hU G p f B Bs x L D J ks hres.1 hf hpf hLlab⟩

end CFSG.StandardType

end
