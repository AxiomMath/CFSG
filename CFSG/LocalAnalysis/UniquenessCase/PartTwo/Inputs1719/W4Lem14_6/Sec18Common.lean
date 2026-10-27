module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDelta
public import CFSG.Quasithin.H13.A6S13821zz11
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136FstarComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1OmegaFstar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.ProdFactors
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.T2Abs
public import CFSG.Quasithin.Background.SmithD310UCaseI
public import CFSG.Quasithin.Vol2.Ch12Sec6P31PropACore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem exists_mem_pset_commutator_ne_bot {W : Type} [CommGroup W] [Finite W]
    {Y L X : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hii : commPset Y X = X) :
    ∃ A ∈ Pset Y, ⁅A, L⁆ ≠ ⊥ := by
  classical
  by_contra hcon
  push Not at hcon
  have hzero : commPset Y X = ⊥ := by
    apply le_bot_iff.mp
    unfold commPset
    refine iSup_le fun A => iSup_le fun hA => ?_
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer, hX,
      Subgroup.le_centralizer_iff]
    refine iSup₂_le fun g hg => ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    have hA' : A.map (MulAut.conj g⁻¹).toMonoidHom ∈ Pset Y :=
      isFFStarOffender_map_conj hA (Y.inv_mem hg)
    have h1 : ⁅A.map (MulAut.conj g⁻¹).toMonoidHom, L⁆ = ⊥ := hcon _ hA'
    have hmap := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h1
    rw [Subgroup.map_commutator, Subgroup.map_bot,
      CFSG.Timmesfeld.RankOne.map_conj_map_conj_inv A g] at hmap
    exact hmap
  have hXbot : X = ⊥ := by
    rw [← hii, hzero]
  have hmap1 : L.map (MulAut.conj (1 : MulAut W)).toMonoidHom = L := by
    ext x
    simp [MulAut.conj_apply]
  have hLX : L ≤ X := by
    rw [hX]
    calc L = L.map (MulAut.conj (1 : MulAut W)).toMonoidHom := hmap1.symm
      _ ≤ ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom := le_iSup₂_of_le 1 Y.one_mem le_rfl
  exact B15P4.ne_bot_of_isComponentOf hL (le_bot_iff.mp (hLX.trans (le_of_eq hXbot)))

theorem commSub_commSub_eq_bot_of_isIrrOn {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hirr : IsIrrOn L (commV L) (commV L ⊓ fixV L)) {g : MulAut W} (hg : g ∈ Y)
    (hgN : g ∉ normIn Y L) :
    commSub (commSub (⊤ : Subgroup W) L) (L.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  haveI : CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.ExpTwo W :=
    ⟨fun w => by rw [← pow_two]; exact hW w⟩
  let K : Subgroup (MulAut W) := L.map (MulAut.conj g).toMonoidHom
  have hKcomp : IsComponentOf K Y := CFSG.Quasithin.B113.isComponentOf_conj hL hg
  have hKne : L ≠ K := by
    intro heq
    have hmap : L.map (MulAut.conj g).toMonoidHom = L := heq.symm
    have hgN' : g ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
    exact hgN ⟨hg, hgN'⟩
  have hcomm : ⁅L, K⁆ = ⊥ := by
    rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hL hKcomp.2.1 with hle | hbot
    · exfalso
      have hcard : Nat.card ↥K ≤ Nat.card ↥L := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hKne (Subgroup.eq_of_le_of_card_ge hle hcard)
    · exact hbot
  have hLKcent : L ≤ Subgroup.centralizer (K : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  let ρ : ↥L →* MulAut W := Subgroup.subtype L
  let σ : ↥K →* MulAut W := Subgroup.subtype K
  have hcommA : ∀ (a : ↥L) (b : ↥K) (v : W), ρ a (σ b v) = σ b (ρ a v) := by
    intro a b v
    have hab : (b : MulAut W) * (a : MulAut W) = (a : MulAut W) * (b : MulAut W) :=
      (Subgroup.mem_centralizer_iff.mp (hLKcent a.2)) b b.2
    change (a : MulAut W) ((b : MulAut W) v) = (b : MulAut W) ((a : MulAut W) v)
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, hab]
  have hB : commutator ↥K = ⊤ := hKcomp.2.2.1
  have hperfL : ⁅L, L⁆ = L :=
    Subgroup.isPerfect_iff.mp ((Group.isPerfect_def).2 hL.2.2.1)
  have hcv : CFSG.Quasithin.commV L = CFSG.Quasithin.commSub (⊤ : Subgroup W) L :=
    CFSG.Quasithin.commV_eq_commSub L
  have hcs : CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.commSub ρ =
      CFSG.Quasithin.commSub (⊤ : Subgroup W) L := by
    unfold CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.commSub
      CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.commSubOf
      CFSG.Quasithin.commSub
    congr 1
    ext x
    constructor
    · rintro ⟨a, w, hw, rfl⟩
      exact ⟨a, a.2, w, hw, rfl⟩
    · rintro ⟨x, hx, w, hw, rfl⟩
      exact ⟨⟨x, hx⟩, w, hw, rfl⟩
  have hcs2 : CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.commSubOf ρ
      (CFSG.Quasithin.commSub (⊤ : Subgroup W) L) =
      CFSG.Quasithin.commSub (CFSG.Quasithin.commSub (⊤ : Subgroup W) L) L := by
    unfold CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.commSubOf
      CFSG.Quasithin.commSub
    congr 1
    ext x
    constructor
    · rintro ⟨a, w, hw, rfl⟩
      exact ⟨a, a.2, w, hw, rfl⟩
    · rintro ⟨x, hx, w, hw, rfl⟩
      exact ⟨⟨x, hx⟩, w, hw, rfl⟩
  have hperf : CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.commSub ρ ≤
      CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.commSubOf ρ
        (CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.commSub ρ) := by
    have h := CFSG.Quasithin.SmithD310U.commSub_commSub_eq hperfL (⊤ : Subgroup W)
    rw [hcs, hcs2]
    exact le_of_eq h.symm
  have hfs : CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.fixSubA ρ =
      CFSG.Quasithin.fixV L := by
    ext v
    constructor
    · intro hv x hx
      exact hv ⟨x, hx⟩
    · intro hv a
      exact hv a a.2
  have hirrT2 : CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.IrrQuotGroup ρ := by
    refine ⟨?_, ?_⟩
    · rw [hfs, hcs, ← hcv, inf_comm]
      exact hirr.1
    · intro W' hle hW'le hstab
      rw [hfs] at hle
      rw [hcs] at hle hW'le
      rw [← hcv] at hle hW'le
      rw [inf_comm] at hle
      have h := hirr.2.2.2 W' (fun x hx u hu => hstab ⟨x, hx⟩ u hu) hle hW'le
      rwa [hfs, hcs, ← hcv, inf_comm]
  have key := CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.centralizes_commSub_of_irrQuot
    ρ σ hcommA hB hperf hirrT2
  rw [CFSG.Quasithin.commSub_eq_bot_iff]
  intro u hu
  rw [CFSG.Quasithin.mem_fixV]
  intro x hx
  exact key ⟨x, hx⟩ u (by rw [hcs]; exact hu)

theorem bParam_le_of_normalCase {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hL : IsComponentOf L Y) (hLn : (L.subgroupOf Y).Normal)
    (hfix : fixV L = ⊥) (hZ : Subgroup.center ↥L = ⊥) {B : ℕ}
    (h : ∀ T : Subgroup (MulAut W), L ≤ L ⊔ T → T ≤ L ⊔ T → IsComponentOf L (L ⊔ T) →
      IsSylowIn 2 T (L ⊔ T) → fixV T ≠ fixV (L ⊔ T) →
      Odd (Nat.card (Subgroup.center ↥L)) →
      T ≤ Subgroup.normalizer (L : Set (MulAut W)) → bParam L (L ⊔ T) ≤ B) :
    bParam L Y ≤ B := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hLne : L ≠ ⊥ := B15P4.ne_bot_of_isComponentOf hL
  have hWnt : Nontrivial W := by
    by_contra hnt
    have hsub : Subsingleton W := not_nontrivial_iff_subsingleton.mp hnt
    have : Subsingleton (MulAut W) :=
      ⟨fun a b => MulEquiv.ext fun w => hsub.elim (a w) (b w)⟩
    exact hLne (Subgroup.eq_bot_of_subsingleton L)
  haveI : Nontrivial W := hWnt
  obtain ⟨T, hT⟩ := E1.exists_isSylowIn_two Y
  have hNLY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1).mp hLn
  have hstep : bParam L Y ≤ bParam L (L ⊔ T) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.bParam_le_of_normal hL.1 hNLY hT
  have hLTle : L ⊔ T ≤ Y := sup_le hL.1 hT.le
  have hcompLT : IsComponentOf L (L ⊔ T) :=
    B15P4.isComponentOf_of_le hL le_sup_left hLTle
  have hTsyl : IsSylowIn 2 T (L ⊔ T) :=
    E6.isSylowIn_of_le hT le_sup_right hLTle
  have hfixLT : fixV (L ⊔ T) = ⊥ := by
    rw [CFSG.Quasithin.FixVLat.fixV_sup_eq, hfix, bot_inf_eq]
  have hfixTne : fixV T ≠ ⊥ :=
    CFSG.Quasithin.H13.A6.A6S20.fixV_ne_bot_of_two_group hW hT.isPGroup
  have hfixT : fixV T ≠ fixV (L ⊔ T) := by
    rw [hfixLT]
    exact hfixTne
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rw [hZ, Subgroup.card_bot]
    exact odd_one
  have hTN : T ≤ Subgroup.normalizer (L : Set (MulAut W)) := hT.le.trans hNLY
  exact hstep.trans (h T le_sup_left le_sup_right hcompLT hTsyl hfixT hodd hTN)

private theorem exists_mul_ne_of_isSimpleGroup_of_centralizer_bot {W : Type} [CommGroup W]
    {Y X : Subgroup (MulAut W)} (hXY : X ≤ Y)
    (hC : Y ⊓ Subgroup.centralizer (X : Set (MulAut W)) = ⊥)
    (hs : IsSimpleGroup ↥X) : ∃ a b : ↥X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hXle : X ≤ Subgroup.centralizer (X : Set (MulAut W)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩)).symm
  have hbot : X = ⊥ := by
    have hsub : X ≤ Y ⊓ Subgroup.centralizer (X : Set (MulAut W)) := fun x hx =>
      ⟨hXY hx, hXle hx⟩
    rw [hC] at hsub
    exact le_bot_iff.mp hsub
  haveI : Nontrivial ↥X := hs.toNontrivial
  haveI : Subsingleton ↥X := by
    rw [hbot]
    infer_instance
  exact (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial ↥X›) ‹Subsingleton ↥X›

theorem fstar_eq_of_centralizer {W : Type} [CommGroup W] [Finite W]
    {Y X : Subgroup (MulAut W)} (hXY : X ≤ Y) (hXn : (X.subgroupOf Y).Normal)
    (hs : IsSimpleGroup ↥X) :
    (Y ⊓ Subgroup.centralizer (X : Set (MulAut W)) = ⊥ → Fstar Y = X) ∧
      (IsL2 ↥X 6 → Nat.card ↥(Y ⊓ Subgroup.centralizer (X : Set (MulAut W))) = 3 →
        IsZ3xL2_64 ↥(Fstar Y)) := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  constructor
  · intro hC
    have hnab := exists_mul_ne_of_isSimpleGroup_of_centralizer_bot hXY hC hs
    haveI : IsSimpleGroup ↥X := hs
    have hqo : CFSG.Open.IsQuasisimple ↥X :=
      (CFSG.ComponentClassification.UnbalancingLocal.isQuasisimple_open_iff ↥X).mpr
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
    refine CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_fstar_eq_of_centralizer_le
      (M := MulAut W) (Y := Y) (L := X) hXY hXn hqo ?_
    rw [inf_comm, hC]
    exact bot_le
  · intro hL2 hcard
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : IsSimpleGroup ↥X := hs
    have hq2 : CFSG.Open.IsQuasisimple ↥X := UC22.NatParMax.isQuasisimple_of_isL2 hL2
    have hq2F : CFSG.IsQuasisimple ↥X :=
      (CFSG.ComponentClassification.UnbalancingLocal.isQuasisimple_open_iff ↥X).mp hq2
    have hZXY : Subgroup.center ↥X = ⊥ :=
      CFSG.Quasithin.H13.Ch9.center_eq_bot_of_commutator_eq_top hq2.1
    let NY : Subgroup ↥Y := X.subgroupOf Y
    have hZNY : Subgroup.center ↥NY = ⊥ := by
      have e : ↥NY ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXY
      have h := Subgroup.map_center_eq e
      rw [hZXY] at h
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
    have hqNY : CFSG.IsQuasisimple ↥NY :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXY).symm hq2F
    have hNYcomp : CFSG.IsComponent NY := ⟨hqNY, hXn.isSubnormal⟩
    have hNlayer : NY ≤ CFSG.layer ↥Y := CFSG.LocalCores.component_le_layer hNYcomp
    have hcent_eq : Subgroup.centralizer (NY : Set ↥Y) =
        (Y ⊓ Subgroup.centralizer (X : Set (MulAut W))).subgroupOf Y :=
      (CFSG.centralizer_subgroupOf_eq X Y hXY).trans
        (Subgroup.inf_subgroupOf_left _ _).symm
    have hCardCent : Nat.card ↥(Subgroup.centralizer (NY : Set ↥Y)) = 3 := by
      rw [hcent_eq]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      exact hcard
    have hCnil : Group.IsNilpotent ↥(Subgroup.centralizer (NY : Set ↥Y)) := by
      have hcyc : IsCyclic ↥(Subgroup.centralizer (NY : Set ↥Y)) :=
        isCyclic_of_prime_card hCardCent
      letI : CommGroup ↥(Subgroup.centralizer (NY : Set ↥Y)) := hcyc.commGroup
      infer_instance
    have hFstarGen : CFSG.generalizedFitting ↥Y =
        NY ⊔ Subgroup.centralizer (NY : Set ↥Y) :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16e_omf_generalizedFitting_eq_sup_centralizer
        hNlayer hCnil
    have hNdisj : NY ⊓ Subgroup.centralizer (NY : Set ↥Y) = ⊥ :=
      CFSG.Quasithin.H13.P31A.inf_centralizer_eq_bot_of_center_eq_bot hZNY
    obtain ⟨eProd⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16e_omf_nonempty_mulEquiv_centralizer_prod
        hFstarGen hNdisj
    have hFdef : Fstar Y = (CFSG.generalizedFitting ↥Y).map Y.subtype := by
      unfold Fstar
      rw [CFSG.Adapters.genFittingFStar_eq_foundations]
    let eF : ↥(Fstar Y) ≃* ↥(CFSG.generalizedFitting ↥Y) := by
      rw [hFdef]
      exact (Subgroup.equivMapOfInjective (CFSG.generalizedFitting ↥Y) Y.subtype
        Y.subtype_injective).symm
    let eC : ↥(Subgroup.centralizer (NY : Set ↥Y)) ≃*
        ↥(Y ⊓ Subgroup.centralizer (X : Set (MulAut W))) := by
      rw [hcent_eq]
      exact Subgroup.subgroupOfEquivOfLe inf_le_left
    let eX : ↥NY ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXY
    have hiso : Nonempty (↥(Fstar Y) ≃*
        ↥(Y ⊓ Subgroup.centralizer (X : Set (MulAut W))) × ↥X) :=
      ⟨eF.trans (eProd.trans (MulEquiv.prodCongr eC eX))⟩
    refine ⟨↥(Y ⊓ Subgroup.centralizer (X : Set (MulAut W))), ↥X, inferInstance,
      inferInstance, hiso, ⟨isCyclic_of_prime_card hcard, hcard⟩, hL2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
