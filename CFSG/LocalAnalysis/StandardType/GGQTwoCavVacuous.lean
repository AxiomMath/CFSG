module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCavSetup
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeRank
public import CFSG.LocalAnalysis.StandardType.GGK1ACenterNoglue
public import CFSG.Open.StatedZModTwo
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTriD4Rank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders
public import CFSG.LocalAnalysis.StandardType.GGQTwoUnitaryFullComponent
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1DSmall

public noncomputable section

namespace CFSG.StandardType.QTwoCav

open CFSG.Assembly CFSG.Open.StatedAPI CFSG.Blueprint Matrix Module

theorem card_sq_le_of_elemAbelian_linear_two
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (d : ℕ)
    (E : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ^ 2 ≤ 3 ^ d := by
  letI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (f := 1) (by simpa using hK)
  have hsc : (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSLGroup (Fin d) K) = ⊥ := by
    rw [largeEvenSLGroup_eq_statedSL]
    change (CFSG.Open.StatedScalars (Fin d) K).subgroupOf (CFSG.Open.StatedSL d K) = ⊥
    rw [statedScalars_eq_bot_of_card_two hK, Subgroup.bot_subgroupOf]
  have hSL : LargeEvenSLGroup (Fin d) K = ⊤ := by
    rw [largeEvenSLGroup_eq_statedSL]
    exact statedSL_eq_top_of_card_two hK d
  let e : LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃* GL (Fin d) K :=
    ((QuotientGroup.quotientMulEquivOfEq hsc).trans QuotientGroup.quotientBot).trans
      ((MulEquiv.subgroupCongr hSL).trans Subgroup.topEquiv)
  let f := e.trans (Matrix.GeneralLinearGroup.toLin :
    GL (Fin d) K ≃* (Module.End K (Fin d → K))ˣ)
  let X := E.map f.toMonoidHom
  have hX := hE.map f.toMonoidHom
  have hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hX.1.is_comm.comm (⟨x, hx⟩ : X) ⟨y, hy⟩)
  have hbound := TwoThree.card_sq_le_top hK X hc hX.2
  have hcard : Nat.card X = Nat.card E := Subgroup.card_map_of_injective f.injective
  simpa [hcard] using hbound

theorem not_full_linear_of_marking
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3))
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : False := by
  obtain ⟨hL, lab', hlab', hraw⟩ := hmark
  obtain ⟨R, hGroup, I, F, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hlab : lab' = lab := hP₀.1
  subst lab'
  have hlin : LargeEvenRecipeLinear (lab.rank + 1) (2 ^ lab.n)
      (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : L ⧸ Subgroup.center L ≃* R,
          lab = lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I,
              LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
    rcases htag with hA | ⟨hD, hr⟩
    · simpa only [LargeEvenRawDatumLegacy, LargeEvenRawDatum, hA] using hraw
    · simpa only [LargeEvenRawDatumLegacy, LargeEvenRawDatum, hD, hr, ↓reduceIte,
        Nat.reduceAdd] using hraw
  obtain ⟨K, hField, hFinite, hcard, -, -, θ, hP⟩ := hlin
  letI : Field K := hField
  letI : Finite K := hFinite
  have hn : lab.n = 1 := by
    have := hlab'.1
    change lab.n < 2 at hq2
    omega
  have hK : Nat.card K = 2 := by simpa only [hn, pow_one] using hcard
  have hr : 3 ≤ lab.rank := three_le_exponent_of_beta_index hS Nat.prime_three θ hN hidx
  have hβ := beta_image_of_index hS.1.1.2.1.2.1 hL θ hN hidx
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) K)) = ⊥ :=
    center_largeEvenProj_largeEvenSLGroup_eq_bot (by omega)
  have hconj := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  let E := (ggBeta L θ hN).range.comap (MulAut.conj :
    LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) K) →* MulAut _)
  have hinner : (ggBeta L θ hN).range ≤ (MulAut.conj :
      LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) K) →* MulAut _).range := by
    rintro φ ⟨b, rfl⟩
    obtain ⟨A, hA⟩ := TableB.exists_eq_linConjAut
      (ggLAut_mem_of_induces L θ hN hP.2.2 b.property)
    change ggLAut L θ ⟨b, hN b.property⟩ ∈ _
    rw [hA, TableB.linConjAut_of_mem A (by
      rw [largeEvenSLGroup_eq_statedSL]
      rw [statedSL_eq_top_of_card_two hK]
      exact Subgroup.mem_top _)]
    exact ⟨_, rfl⟩
  have hmap : E.map (MulAut.conj :
      LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) K) →* MulAut _) =
      (ggBeta L θ hN).range := Subgroup.map_comap_eq_self hinner
  let eE : E ≃* (ggBeta L θ hN).range :=
    (Subgroup.equivMapOfInjective E (MulAut.conj :
      LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) K) →* MulAut _) hconj).trans
        (MulEquiv.subgroupCongr hmap)
  have hE : CFSG.Open.IsElemAbelian 3 E :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.of_mulEquiv eE.symm hβ.1.isElementaryAbelian)
  have hcardE : Nat.card E = 3 ^ lab.rank := by
    rw [Nat.card_congr eE.toEquiv]
    exact hβ.2
  have hbound := card_sq_le_of_elemAbelian_linear_two hK (lab.rank + 1) E hE
  rw [hcardE, ← pow_mul] at hbound
  have hle := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hbound
  omega


theorem not_full_triality_of_marking
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (htag : lab.tag = .triD4)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 4)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : False := by
  have hm : LargeEvenMarking L (fun lab' R _ I F θ => lab'.tag = .triD4 ∧
      (lab' = lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)) :=
    largeEvenMarking_mono
      (X := ↥L)
      (P := fun lab' _ _ I _ θ => lab' = lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
      (fun lab' _ _ _ _ _ hP => ⟨hP.1.symm ▸ htag, hP⟩) hmark
  obtain ⟨-, lab', -, hraw⟩ := largeEvenMarking_triD4_innRank hm
  obtain ⟨R, hGroup, I, F, hs, hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  letI : Group R := hGroup
  letI : IsSimpleGroup R := hs
  letI : Finite R := Finite.of_surjective θ θ.surjective
  have hnc : ¬ IsMulCommutative R := by
    intro h
    obtain ⟨a, b, hab⟩ := hna
    exact hab (h.is_comm.comm a b)
  have hZ : Subgroup.center R = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  have hconj := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  have hβ := beta_image_of_index hS.1.1.2.1.2.1 hS.2.1.1 θ hN hidx
  let E := (ggBeta L θ hN).range.comap (MulAut.conj : R →* MulAut R)
  have hinner : (ggBeta L θ hN).range ≤ (MulAut.conj : R →* MulAut R).range := by
    rintro φ ⟨b, rfl⟩
    have hφ := ggLAut_mem_of_induces L θ hN hP.1.2.2 b.property
    rw [hP.2.1] at hφ
    exact hφ
  have hmap : E.map (MulAut.conj : R →* MulAut R) = (ggBeta L θ hN).range :=
    Subgroup.map_comap_eq_self hinner
  let eE : E ≃* (ggBeta L θ hN).range :=
    (Subgroup.equivMapOfInjective E (MulAut.conj : R →* MulAut R) hconj).trans
      (MulEquiv.subgroupCongr hmap)
  have hE : CFSG.Open.IsElemAbelian 3 E :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.of_mulEquiv eE.symm hβ.1.isElementaryAbelian)
  have hcardE : Nat.card E = 3 ^ 4 := by
    rw [Nat.card_congr eE.toEquiv]
    exact hβ.2
  have hupper := hP.2.2 E hE
  rw [hcardE] at hupper
  norm_num at hupper


theorem not_full_tits_of_marking
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (htag : lab.tag = .twF4der)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ 4)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : False := by
  obtain ⟨hL, lab', hlab', hraw⟩ := hmark
  obtain ⟨R₀, hGroup₀, I₀, F₀, -, -, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hlab : lab' = lab := hP₀.1
  subst lab'
  have hn : lab.n = 1 := by
    have hv := hlab'
    simp only [LargeEvenInLambda2, htag] at hv
    exact hv.2.2
  try rw [LargeEvenRawDatumLegacy] at hraw
  try rw [LargeEvenRawDatum] at hraw
  rw [htag, hn] at hraw
  dsimp at hraw
  obtain ⟨K, hField, hFinite, hcard, hs, hna, θ, hP⟩ := hraw
  letI : Field K := hField
  letI : Finite K := hFinite
  have hK : Nat.card K = 2 := by simpa using hcard
  letI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq
    (f := 1) (by simpa using hK)
  let R := LargeEvenCenterQuot (LargeEvenTwF4H 0 K)
  letI : IsSimpleGroup R := hs
  letI : Finite R := Finite.of_surjective θ θ.surjective
  letI : Subsingleton Kˣ :=
    (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hK])).1
  have hnc : ¬ IsMulCommutative R := by
    intro h
    obtain ⟨a, b, hab⟩ := hna
    exact hab (h.is_comm.comm a b)
  have hZ : Subgroup.center R = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  have hconj := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  have hβ := beta_image_of_index hS.1.1.2.1.2.1 hL θ hN hidx
  have hI := chevIDImage_subset_inn_of_subsingleton (A := LargeEvenCartanF4)
    (LargeEvenTwF4H 0 K)
  have hinner : (ggBeta L θ hN).range ≤ (MulAut.conj : R →* MulAut R).range := by
    rintro φ ⟨b, rfl⟩
    exact hI (ggLAut_mem_of_induces L θ hN hP.2.2 b.property)
  let E := (ggBeta L θ hN).range.comap (MulAut.conj : R →* MulAut R)
  have hmap : E.map (MulAut.conj : R →* MulAut R) = (ggBeta L θ hN).range :=
    Subgroup.map_comap_eq_self hinner
  let eE : E ≃* (ggBeta L θ hN).range :=
    (Subgroup.equivMapOfInjective E (MulAut.conj : R →* MulAut R) hconj).trans
      (MulEquiv.subgroupCongr hmap)
  have hcardE : Nat.card E = 3 ^ 4 := by
    rw [Nat.card_congr eE.toEquiv]
    exact hβ.2
  have hm : ReeTitsModel R .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl,
      reeTitsRelationModel_largeEven 0 hcard⟩
  have hdiv := (Subgroup.card_subgroup_dvd_card E).trans
    (CFSG.EvenSmallLie.Child3.card_dvd_of_reeTitsModel_Tits hm)
  rw [hcardE] at hdiv
  norm_num at hdiv


theorem four_dvd_image_of_full_twistedD_three
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .twD) (hr3 : lab.rank = 3)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    4 ∣ Nat.card (ggAutomizer
      ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L)) (ggGamma L hN).range) := by
  let labU : LargeEvenLabel := ⟨.twA, 3, lab.n⟩
  have hD : GGInnerDiagOnLabel
      (fun _ lab' => lab'.tag = .twD ∧ lab'.rank = 3 ∧ lab'.n = lab.n) 3 Bs L :=
    largeEvenMarking_mono (X := ↥L)
      (P := fun lab' _ _ I _ θ => lab' = lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
      (fun lab' _ _ _ _ _ hP =>
        ⟨⟨hP.1.symm ▸ htag, hP.1.symm ▸ hr3, congrArg LargeEvenLabel.n hP.1⟩, hP.2⟩)
      hmark
  have hU := ggInnerDiagOnLabel_twD_to_twA (p := 3) (Bs := Bs) (L := L)
    (S := fun n => n = lab.n) hD
  have hmarkU : GGInnerDiagOnLabel (fun _ lab' => lab' = labU) 3 Bs L :=
    largeEvenMarking_mono (X := ↥L)
      (P := fun lab' _ _ I _ θ =>
        (lab'.tag = .twA ∧ lab'.rank = 3 ∧ lab'.n = lab.n) ∧
          Bs ≤ Subgroup.normalizer (L : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I,
              LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
      (fun lab' _ _ _ _ _ hP => by
        refine ⟨?_, hP.2⟩
        rcases lab' with ⟨t, r, n⟩
        have ht := hP.1.1
        have hr := hP.1.2.1
        have hn := hP.1.2.2
        dsimp only at ht hr hn
        subst t
        subst r
        subst n
        rfl) hU
  exact QTwoUnitaryCav.four_dvd_image_of_full_unitary hS
    (by simpa only [GGLabQTwo, labU] using hq2) rfl hmarkU
    (by simpa only [labU, hr3] using hidx) hN

end CFSG.StandardType.QTwoCav

end
