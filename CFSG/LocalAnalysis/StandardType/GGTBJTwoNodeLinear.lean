module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearBlock
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySplitRefl
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftADepHolds
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallALinearBlock
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimLinear
public import CFSG.LocalAnalysis.StandardType.GGResJLineA3
public import CFSG.LocalAnalysis.StandardType.GGResJLinearCubeAutomizer
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.RankPSL
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinearDatum
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTriD4Three
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot

theorem card_eq_of_blockSpecialLinear_label
    (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {F : Type} [Field F] [Finite F] [CharP F 2] {r f a : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    {ψ : SpecialLinearGroup (Fin (r + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (r + 1)) F))
    {S : Finset (Fin (r + 1))} (hS : 2 ≤ S.card)
    (hΛ : LargeEvenInLambda2 ⟨.A, a, f⟩)
    (hLab : GGHasLabel ⟨.A, a, f⟩
      (((blockSpecialLinear S).map ψ) ⧸ Subgroup.center ((blockSpecialLinear S).map ψ))) :
    S.card = a + 1 := by
  have hmod : CFSG.Blueprint.LieModel
      (((blockSpecialLinear S).map ψ) ⧸ Subgroup.center ((blockSpecialLinear S).map ψ))
      .PSL S.card 2 f := by
    rcases (show S.card = 2 ∨ 3 ≤ S.card by omega) with h2 | h3
    · rw [h2]
      exact LinTypeAk.lieModel_map_blockSpecialLinear_of_card_two hF hf hker h2
    · exact LinTorus.lieModel_map_blockSpecialLinear hF (by omega) hker h3
  have hcls := hmod.statedClassicalModel (by decide)
  have hdim : S.card - 1 + 1 = S.card := by omega
  have hcls' : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (((blockSpecialLinear S).map ψ) ⧸ Subgroup.center ((blockSpecialLinear S).map ψ))
      .PSL (S.card - 1 + 1) 2 f := hdim.symm ▸ hcls
  have hiso := hRig _ _ _ hΛ (largeEvenInLambda2_typeA hcls') hLab
    (ggHasLabel_typeA hcls')
  simp only [GGLabelIso, LargeEvenLabel.mk.injEq, reduceCtorEq, false_and, and_false,
    or_false] at hiso
  omega

theorem exists_diagonal_cover_of_large_linear_side_of_marking_of_cfg
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {X : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hside : X = L ∨ ∃ z, GGNbr p B x D J z X)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* X),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t := by
  have hp : p.Prime := Fact.out
  obtain ⟨hXperf, lab, hlab, hraw⟩ := hmark
  have heq : lab = ⟨.A, r, f⟩ := by
    obtain ⟨R, _, I, F, hs, hna, θ, heq, -⟩ := largeEvenRawDatum_exists hraw
    exact heq
  subst lab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, hField, hFinite, hF, hs, hna, θ, -, hN, hI⟩ := hraw
  let : Field F := hField
  let : Finite F := hFinite
  have : CharP F 2 := charP_two_of_card hF
  have hLift : GGTorusLift p (r - 1) (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) F)) := by
    have hrank : r - 1 = r + 1 - 2 := by omega
    rw [hrank]
    exact TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (r + 1) F)
      (TypeA.ggTorusLift_sub_two hp (by simpa only [hF] using hpq) (by omega)
        (slHasSections_of_four_le hp (by simpa only [hF] using hpq) (by omega)))
  have hTB : GGTorusTBGroup p (r - 1)
      (LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) F))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (r + 1)) F)) Set.univ)
      X (ggQuotHom θ) (ggGamma X hN).range := by
    rcases hside with rfl | ⟨z, hz⟩
    · exact ggTorusTBGroup_of_L hcfg hXperf θ hN
        (fun b hb => ggLAut_mem_of_induces X θ hN hI hb) hLift
    · exact ggTorusTBGroup_of_nbr hcfg hz hXperf θ hN
        (fun b hb => ggLAut_mem_of_induces X θ hN hI hb) hLift
  have hTB' := hTB.mulEquiv (TypeA.recipeEquiv (r + 1) F)
    (fun _ h => TypeA.congr_recipeEquiv_mem h)
  obtain ⟨φ, hφs, hker, hdiag⟩ := exists_actsDiag_model_of_tbGroup
    hp (by simpa only [hF] using hpq) (by omega) (by omega) hTB'
  exact ⟨F, hField, hFinite, inferInstance, hN, φ, hF, hφs, hker, hdiag⟩

theorem exists_diagonal_cover_of_large_linear_side_of_marking
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hside : X = L ∨ ∃ z, GGNbr p B x D J z X)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* X),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t :=
  exists_diagonal_cover_of_large_linear_side_of_marking_of_cfg hH.1 hside hr hpq hmark

theorem exists_diagonal_cover_of_large_linear_side_of_cfg
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {X : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hIDA : GGInnerDiagAll p B Bs x L D J)
    (hside : X = L ∨ ∃ z, GGNbr p B x D J z X)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* X),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t := by
  have hInn : GGInnerDiagOn Bs X := by
    rcases hside with rfl | ⟨z, hz⟩
    · exact hIDA.1
    · exact hIDA.2 z X hz
  exact exists_diagonal_cover_of_large_linear_side_of_marking_of_cfg hcfg hside hr hpq
    (ggInnerDiagOn_relabel hRig hInn hΛ hLab)

theorem exists_diagonal_cover_of_large_linear_side
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K X : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hside : X = L ∨ ∃ z, GGNbr p B x D J z X)
    {r f : ℕ} (hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (X ⧸ Subgroup.center X))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* X),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t :=
  exists_diagonal_cover_of_large_linear_side_of_cfg hRig hH.1 hH.2.2.1 hside hr hpq hLab hΛ

theorem exists_block_of_large_linear_L_of_marking
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* L) (S : Finset (Fin (r + 1))),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        (∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t) ∧
        2 ≤ S.card ∧ J = (blockSpecialLinear S).map (L.subtype.comp φ) := by
  have hr : 3 ≤ r := hH.1.three_le_rank_of_typeA_marking hmark hpq
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hφs, hker, hdiag⟩ :=
    exists_diagonal_cover_of_large_linear_side_of_marking hH (Or.inl rfl) hr hpq hmark
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hH.1.2.2.1.2.2.2.2.2.1
  have hDB : D ≤ Bs := hH.1.2.2.1.1.trans hH.1.2.1.1
  have hdiag' : ∀ b : Bs, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag φ (L.normalizerMonoidHom ⟨b, hN b.2⟩) t := by
    intro b
    exact hdiag (ggGamma L hN b) ⟨b, rfl⟩
  obtain ⟨S, hS, hJ⟩ := exists_block_of_isComponentOf_centralizer_SL
    hφs hker hdiag' hDB hJ
  exact ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hS, hJ⟩

theorem exists_block_of_large_linear_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (_hr : 3 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* L) (S : Finset (Fin (r + 1))),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        (∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t) ∧
        2 ≤ S.card ∧ J = (blockSpecialLinear S).map (L.subtype.comp φ) :=
  exists_block_of_large_linear_L_of_marking hH hpq
    (ggInnerDiagOn_relabel hRig hH.2.2.1.1 hΛ hLab)

theorem GGResHyp.fix_mem_centralizer_J_of_typeA_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {r f : ℕ} (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs L) :
    ∀ b : Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hS, hJ⟩ :=
    exists_block_of_large_linear_L_of_marking hH hpq hmark
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  let e : S ≃ Fin S.card := S.equivFin
  let χ : SpecialLinearGroup (Fin S.card) F →* J :=
    TypeANbrDvd.blockSLCover (F := F) S L φ hJ e
  have hχs : Function.Surjective χ :=
    TypeANbrDvd.blockSLCover_surjective (F := F) S L φ hJ e
  have hχker : ∀ g, χ g = 1 → g ∈ scalars S.card F :=
    TypeANbrDvd.blockSLCover_ker_scalar (F := F) S L φ hJ hker e
  have hχdiag : ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
      ∃ t : Fin S.card → F, TypeANbrDvd.ActsDiag χ a t := by
    rintro a ⟨b, rfl⟩
    obtain ⟨t, ht⟩ := hdiag _ ⟨b, rfl⟩
    exact ⟨fun k => t (e.symm k),
      TypeANbrDvd.blockSLCover_actsDiag (F := F) (S := S) (P := L) (φ := φ)
        hJ hN hH.Bs_le_normalizer_J (B := Bs) le_rfl e ht⟩
  exact ResJCubicBlock.ggLinearModel_fix_mem_centralizer hH.Bs_le_normalizer_J
    hH.1.2.1.2.1 hH.1.2.1.2.2.2 hχs hχker hS hχdiag

theorem GGResHyp.fix_mem_centralizer_J_of_typeA_marking_K_exactThree
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs K)
    (hLB : GGLBalanceInput)
    (hD : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    ∀ b : Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  obtain ⟨F, hField, hFinite, hChar, hN, φ, hF, hφs, hker, hdiag⟩ :=
    exists_diagonal_cover_of_large_linear_side_of_marking hH
      (Or.inr ⟨y, hnb⟩) (by omega : 3 ≤ r) hpq hmark
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hpF : p ∣ Nat.card F - 1 := by
    rw [hF]
    exact hpq
  have hdiagK : ∀ b : Bs, ∃ t : Fin (r + 1) → F,
      TypeANbrDvd.ActsDiag φ (K.normalizerMonoidHom ⟨b, hN b.2⟩) t := by
    intro b
    exact hdiag (ggGamma K hN b) ⟨b, rfl⟩
  obtain ⟨V, hVadd, hVmod, ι, ρ, φw, hw, α, hperm, hρ, hφeq, hlin, hrefl, hpair,
    ⟨e, he⟩, hcl⟩ :=
    exists_weyl_datum_of_diagonal_linear_cover (X := K) hp2 hpF (by omega : 3 ≤ r) hBs hSC hN
      hφs hker hdiag
  have hWK : GGWeylTypeData r (Nat.card ↥(ggAutomizer K Bs))
      (Nat.card ↥(Subgroup.center ↥(ggAutomizer K Bs))) := by
    have h0 : GGWeylTypeData r (Nat.card (CoxeterMatrix.A r).Group)
        (Nat.card ↥(Subgroup.center (CoxeterMatrix.A r).Group)) := by
      simpa using (ggWeylTypeData_of_isWeylMatrix (ggHLT_weyl_A (n := r) (by omega)))
    have hc := Nat.card_congr e.toEquiv
    have hz := Nat.card_congr (Subgroup.centerCongr e).toEquiv
    simpa [hc, hz] using h0
  obtain ⟨hpJ, -⟩ :=
    CFSG.StandardType.ggResLeviDatumCard_survivor_dvd_and_ne hD ⟨_, hWK⟩
      (by omega : 3 < r) hH.Bs_le_normalizer_J hp2
      (fun b hb => hBs.2 b hb)
  obtain ⟨hI, -, hDJ⟩ := hH.1
  obtain ⟨-,-,-,-,-,-,hSS,-⟩ := id hI
  obtain ⟨hJK, -⟩ :=
    isComponentOf_comap_ggFix_ggGamma_x_of_dvd hLB hH.1 hpJ hnb hN hxBs
  have hJcompG : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hSS hDJ hnb hJK
  have hJcompZ : IsComponentOf J
      (K ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
    simpa only [CFSG.Walter.centralizer_zpowers_eq'] using hJcompG
  obtain ⟨S, hS, hJ⟩ := exists_block_of_isComponentOf_centralizer_SL
    (L' := K) (E := Bs) (D' := Subgroup.zpowers x) hφs hker hdiagK
    (Subgroup.zpowers_le.mpr hxBs) hJcompZ
  let eS : S ≃ Fin S.card := S.equivFin
  let χ : Matrix.SpecialLinearGroup (Fin S.card) F →* J :=
    TypeANbrDvd.blockSLCover (F := F) S K φ hJ eS
  have hχs : Function.Surjective χ :=
    TypeANbrDvd.blockSLCover_surjective (F := F) S K φ hJ eS
  have hχker : ∀ g, χ g = 1 → g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars S.card F :=
    TypeANbrDvd.blockSLCover_ker_scalar (F := F) S K φ hJ hker eS
  have hχdiag : ∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
      ∃ t : Fin S.card → F, TypeANbrDvd.ActsDiag χ a t := by
    rintro a ⟨b, rfl⟩
    obtain ⟨t, ht⟩ := hdiagK b
    exact ⟨fun k => t (eS.symm k),
      TypeANbrDvd.blockSLCover_actsDiag (F := F) (S := S) (P := K) (φ := φ)
        hJ hN hH.Bs_le_normalizer_J (B := Bs) le_rfl eS ht⟩
  exact ResJCubicBlock.ggLinearModel_fix_mem_centralizer hH.Bs_le_normalizer_J
    hH.1.2.1.2.1 hH.1.2.1.2.2.2 hχs hχker hS hχdiag

theorem exists_corank_two_block_of_large_linear_L
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 4 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.A, r, f⟩ (L ⧸ Subgroup.center L))
    (hΛ : LargeEvenInLambda2 ⟨.A, r, f⟩)
    (hJLab : GGHasLabel ⟨.A, r - 2, f⟩ (J ⧸ Subgroup.center J)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (φ : SpecialLinearGroup (Fin (r + 1)) F →* L) (S : Finset (Fin (r + 1))),
      Nat.card F = 2 ^ f ∧ Function.Surjective φ ∧
        (∀ g, φ g = 1 → g ∈ scalars (r + 1) F) ∧
        (∀ a ∈ (ggGamma L hN).range, ∃ t : Fin (r + 1) → F,
          TypeANbrDvd.ActsDiag φ a t) ∧
        S.card = r - 1 ∧ J = (blockSpecialLinear S).map (L.subtype.comp φ) := by
  obtain ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, hS, hJ⟩ :=
    exists_block_of_large_linear_L hRig hH (by omega : 3 ≤ r) hpq hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hChar
  have hf1 : 1 ≤ f := hΛ.1
  have hf : 2 ≤ f := by
    by_contra hf2
    have hf_eq : f = 1 := by omega
    have hp_one : p ∣ 1 := by simpa only [hf_eq, pow_one] using hpq
    have hp_le : p ≤ 1 := Nat.le_of_dvd (by omega) hp_one
    have hp_gt := (Fact.out : p.Prime).one_lt
    omega
  have hk : (L.subtype.comp φ).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (r + 1)) F) := by
    intro g hg
    have hgφ : φ g = 1 := Subtype.ext (MonoidHom.mem_ker.mp hg)
    exact scalars_le_center (r + 1) F (hker g hgφ)
  have hΛJ : LargeEvenInLambda2 ⟨.A, r - 2, f⟩ := by
    change 1 ≤ f ∧ 1 ≤ r - 2 ∧ (r - 2 = 1 → 2 ≤ f)
    exact ⟨by omega, by omega, fun _ => hf⟩
  have hc := card_eq_of_blockSpecialLinear_label hRig hF hf
    hk hS hΛJ (hJ ▸ hJLab)
  refine ⟨F, hField, hFinite, hChar, hN, φ, S, hF, hφs, hker, hdiag, ?_, hJ⟩
  omega

end CFSG.StandardType

end
