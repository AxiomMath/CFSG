module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALift
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegKG
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2E7Rank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7Three
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInj
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelRecipeID
public import CFSG.LocalAnalysis.StandardType.GGE6InnerDiagBoundThreeProof3
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace Q2Exceptional

private theorem inducedAut_mem_of_marked_action {G : Type} [Group G]
    {Bs J : Subgroup G} {R : Type} [Group R]
    (θ : J ⧸ Subgroup.center J ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) {I : Set (MulAut R)}
    (hactors : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun j j' : J => (j' : G) = b⁻¹ * j * b) φ)
    (b : Bs) : ggInducedAut θ (ggGamma J hN b) ∈ I := by
  obtain ⟨φ, hφ, hind⟩ := hactors (b : G)⁻¹ (Bs.inv_mem b.2)
  have heq : ggInducedAut θ (ggGamma J hN b) = φ := by
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    induction q using QuotientGroup.induction_on with
    | H j =>
      rw [ggInducedAut_apply]
      exact (hind j (ggGamma J hN b j) (by
        change (ggGamma J hN b j : G) = (b : G)⁻¹⁻¹ * (j : G) * (b : G)⁻¹
        rw [ggGamma_coe, inv_inv])).symm
  rwa [heq]

theorem geomToral_of_faithful_action {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hT : ExcFramesHalf.BigElemAbelianToralBar τ 3)
    {M : Subgroup (ModGL τ K)} {R : Type} [Group R] (f : M →* MulAut R)
    (hf : Function.Injective f) {A : Subgroup (MulAut R)} (hA : IsElemAbelian 3 A)
    (hAf : A ≤ f.range)
    (hM : ∀ x ∈ M, baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
      adjointGroup τ (AlgebraicClosure K))
    (hcard : 3 ^ (τ.rank - 1) ≤ Nat.card A) :
    GGGeomToral τ K ((A.comap f).map M.subtype) := by
  classical
  let W : Subgroup M := A.comap f
  let W₀ : Subgroup (ModGL τ K) := W.map M.subtype
  let Wbar := W₀.map (baseChangeGL (τ := τ) (algebraMap K (AlgebraicClosure K)))
  have hW : IsElemAbelian 3 W := hA.comap hf
  have hW₀ : IsElemAbelian 3 W₀ := hW.map _
  have hWbar : IsElemAbelian 3 Wbar := hW₀.map _
  have hWcard : Nat.card W = Nat.card A := by
    rw [← Subgroup.card_map_of_injective hf, Subgroup.map_comap_eq_self hAf]
  have hWbarcard : Nat.card Wbar = Nat.card A := by
    rw [Subgroup.card_map_of_injective
      (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))),
      Subgroup.card_map_of_injective M.subtype_injective, hWcard]
  have hWbarG : Wbar ≤ adjointGroup τ (AlgebraicClosure K) := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact hM w w.2
  have hK3 : ¬ 3 ∣ Nat.card K := by
    let : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    exact fun h => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      norm_num at this
  exact hT K hK3 Wbar hWbarG
    (fun x hx y hy => TableB.IsElemAbelian.comm hWbar hx hy) hWbar.2
    (by rw [hWbarcard]; exact hcard)

theorem toralActUntw_of_lift {τ : Tag} {K : Type} [Field K] [Finite K]
    {G : Type} [Group G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (θ : J ⧸ Subgroup.center J ≃* adjointGroup τ K)
    (hI : ((ggGamma J hN).range.map (ggInducedAut θ)) ≤
      (RecipeExcLang.inndiagConj τ K).range)
    (hT : GGGeomToral τ K
      ((((ggGamma J hN).range.map (ggInducedAut θ)).comap
        (RecipeExcLang.inndiagConj τ K)).map (RecipeExcLang.inndiagGroup τ K).subtype)) :
    GGExcToralActUntw τ J ((fun b : G => MulAut.conj b) '' (Bs : Set G)) := by
  let A := (ggGamma J hN).range.map (ggInducedAut θ)
  let W := A.comap (RecipeExcLang.inndiagConj τ K)
  refine ⟨K, inferInstance, inferInstance, θ, W, hT, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hbA : ggInducedAut θ (ggGamma J hN ⟨b, hb⟩) ∈ A :=
    Subgroup.mem_map_of_mem _ ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨w, hw⟩ := hI hbA
  refine ⟨w, ?_, fun j => ⟨ggGamma J hN ⟨b, hb⟩ j, rfl, ?_⟩⟩
  · change RecipeExcLang.inndiagConj τ K w ∈ A
    rw [hw]
    exact hbA
  · rw [hw, ggInducedAut_apply]

theorem toralActUntw_of_card {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hTor : ExcFramesHalf.BigElemAbelianToralBar τ 3)
    {G : Type} [Group G] {Bs J : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hJ : commutator J = ⊤)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (θ : J ⧸ Subgroup.center J ≃* adjointGroup τ K)
    (hI : ((ggGamma J hN).range.map (ggInducedAut θ)) ≤
      (RecipeExcLang.inndiagConj τ K).range)
    (hcard : 3 ^ (τ.rank - 1) ≤ Nat.card (ggGamma J hN).range) :
    GGExcToralActUntw τ J ((fun b : G => MulAut.conj b) '' (Bs : Set G)) := by
  have hA : IsElemAbelian 3 ((ggGamma J hN).range.map (ggInducedAut θ)) :=
    (ggBsAut_range_isElemAbelian hBs hN).map _
  have hAc : 3 ^ (τ.rank - 1) ≤
      Nat.card ((ggGamma J hN).range.map (ggInducedAut θ)) := by
    rw [Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hJ θ)]
    exact hcard
  exact toralActUntw_of_lift hN θ hI
    (geomToral_of_faithful_action hTor (RecipeExcLang.inndiagConj τ K)
      (RecipeExcLang.inndiagConj_injective_of_card_eq_two_pow hK) hA hI
      (fun x hx => RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag
        (algebraMap K (AlgebraicClosure K)) hx) hAc)

theorem toralActTw_of_lift {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hσ : orderOf σ = 2)
    {G : Type} [Group G] {Bs J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (θ : J ⧸ Subgroup.center J ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hI : ((ggGamma J hN).range.map (ggInducedAut θ)) ≤
      (RecipeExcLang.twConj K σ).range)
    (hT : GGGeomToral .E6 K
      ((((ggGamma J hN).range.map (ggInducedAut θ)).comap
        (RecipeExcLang.twConj K σ)).map (RecipeExcLang.twInndiagGroup K σ).subtype)) :
    GGExcToralActTw J ((fun b : G => MulAut.conj b) '' (Bs : Set G)) := by
  let A := (ggGamma J hN).range.map (ggInducedAut θ)
  let W := A.comap (RecipeExcLang.twConj K σ)
  refine ⟨K, inferInstance, inferInstance, σ, hσ, θ, W, hT, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hbA : ggInducedAut θ (ggGamma J hN ⟨b, hb⟩) ∈ A :=
    Subgroup.mem_map_of_mem _ ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨w, hw⟩ := hI hbA
  refine ⟨w, ?_, fun j => ⟨ggGamma J hN ⟨b, hb⟩ j, rfl, ?_⟩⟩
  · change RecipeExcLang.twConj K σ w ∈ A
    rw [hw]
    exact hbA
  · rw [hw, ggInducedAut_apply]

theorem toralActTw_of_card {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (hσo : orderOf σ = 2)
    {G : Type} [Group G] {Bs J : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hJ : commutator J = ⊤)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (θ : J ⧸ Subgroup.center J ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hI : ((ggGamma J hN).range.map (ggInducedAut θ)) ≤
      (RecipeExcLang.twConj K σ).range)
    (hcard : 3 ^ 5 ≤ Nat.card (ggGamma J hN).range) :
    GGExcToralActTw J ((fun b : G => MulAut.conj b) '' (Bs : Set G)) := by
  have hA : IsElemAbelian 3 ((ggGamma J hN).range.map (ggInducedAut θ)) :=
    (ggBsAut_range_isElemAbelian hBs hN).map _
  have hAc : 3 ^ (Tag.E6.rank - 1) ≤
      Nat.card ((ggGamma J hN).range.map (ggInducedAut θ)) := by
    rw [Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hJ θ)]
    exact hcard
  have hM : ∀ x ∈ RecipeExcLang.twInndiagGroup K σ,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) x ∈
        adjointGroup .E6 (AlgebraicClosure K) := by
    have hle : RecipeExcLang.twInndiagGroup K σ ≤ RecipeExcLang.inndiagGroup .E6 K := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x (hx | ⟨b, hb, rfl⟩)
      · exact RecipeExcLang.adjointGroup_le_inndiagGroup
          (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hx).1
      · exact RecipeExcLang.rootDiagUnit_mem_inndiagGroup b
    exact fun x hx => RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag
      (algebraMap K (AlgebraicClosure K)) (hle hx)
  exact toralActTw_of_lift σ hσo hN θ hI
    (geomToral_of_faithful_action ExcFramesHalf.bigElemAbelianToralBar_E6_three
      (RecipeExcLang.twConj K σ) (NoOffTwE6Three.twConj_injective hn hK σ hσ)
      hA hI hM hAc)

theorem eight_le_twoLocalRank_of_e8 {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .E8)) :
    8 ≤ LargeEvenTwoLocalRank 3 G := by
  obtain ⟨hL, lab, hΛ, hraw⟩ := hmark
  obtain ⟨R, _, I, F, -, -, θ, ht⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst t
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K, _, _, hK, -, -, θK, -⟩ := hraw
  have : CharP K 2 := charP_two_of_card hK
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  exact succ_le_twoLocalRank_of_torusLift Nat.prime_three hS.2.2.2.1.1
    (hS.1.1.2 x hS.2.1) hS.2.2.1 hL θK TableBExcTwo.ggTorusLift_E8Two

theorem six_pow_le_card_gamma_J_of_e8 {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .E8))
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    3 ^ 6 ≤ Nat.card (ggGamma J hN).range := by
  have hm := eight_le_twoLocalRank_of_e8 hcfg hmark
  exact (Nat.pow_le_pow_right Nat.prime_three.pos (by omega)).trans
    (hcfg.pow_le_card_gamma_J hN)

private theorem orderOf_iterateFrobenius_half {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    orderOf (iterateFrobeniusEquiv K 2 n) = 2 := by
  obtain ⟨f, hf, hof, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * n) (by rw [hK, ← pow_mul, mul_comm])
  have hfeq : f ^ n = iterateFrobeniusEquiv K 2 n := by
    ext c
    rw [RecipeFieldExcInn.pow_apply_of_sq' hf, iterateFrobeniusEquiv_def]
  have hd : n ∣ orderOf f := by rw [hof]; exact ⟨2, by omega⟩
  have ho := orderOf_pow_of_dvd (x := f) (n := n) (by omega) hd
  rw [hof, Nat.mul_div_cancel _ (by omega)] at ho
  rwa [hfeq] at ho

theorem toralAct_of_marking_of_card {G : Type} [Group G]
    {Bs J : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hmark : LargeEvenMarking J (fun lab _ _ I _ θ =>
      (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) ∧
        Bs ≤ Subgroup.normalizer (J : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun j j' : J => (j' : G) = b⁻¹ * j * b) φ))
    (hcard : ∀ hN : Bs ≤ Subgroup.normalizer (J : Set G),
      3 ^ 5 ≤ Nat.card (ggGamma J hN).range)
    (hcardE7 : ∀ lab : LargeEvenLabel, lab.tag = .E7 →
      GGHasLabel lab (J ⧸ Subgroup.center J) →
      ∀ hN : Bs ≤ Subgroup.normalizer (J : Set G),
        3 ^ 6 ≤ Nat.card (ggGamma J hN).range) :
    GGExcToralAct J ((fun b : G => MulAut.conj b) '' (Bs : Set G)) := by
  classical
  obtain ⟨hJ, lab, hΛ, hraw⟩ := hmark
  have hhas : GGHasLabel lab (J ⧸ Subgroup.center J) :=
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw
  obtain ⟨R, _, I, F, -, -, θ, ht, -, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hΛ
  rcases ht with rfl | rfl | rfl
  · dsimp only [LargeEvenRawDatumLegacy] at hraw
    obtain ⟨K, _, _, hK, -, -, θK, -, hN, hactors⟩ := hraw
    have : CharP K 2 := charP_two_of_card hK
    let e := TableBExc.recipeEquiv .E6 K
    let θ₀ := θK.trans e
    have hI : ((ggGamma J hN).range.map (ggInducedAut θ₀)) ≤
        (RecipeExcLang.inndiagConj .E6 K).range := by
      rintro _ ⟨a, ⟨b, rfl⟩, rfl⟩
      have hφ := inducedAut_mem_of_marked_action θK hN hactors b
      obtain ⟨w, hw⟩ := (E6ThreeModel.recipeID_iff_hatAut _).mp hφ
      refine ⟨⟨w, E6IDB.mem_hatGroup_iff_mem_inndiagGroup.mp w.2⟩, ?_⟩
      have htrans : ggInducedAut θ₀ (ggGamma J hN b) =
          MulAut.congr e (ggInducedAut θK (ggGamma J hN b)) :=
        NbrLangTypeA.ggLAut_trans (K := J) θK e ⟨b, hN b.2⟩
      rw [htrans]
      exact (E6IDB.hatAut_eq_inndiagConj w).symm.trans hw
    exact Or.inl (toralActUntw_of_card hK ExcFramesHalf.bigElemAbelianToralBar_E6_three
      hBs hJ hN θ₀ hI (hcard hN))
  · dsimp only [LargeEvenRawDatumLegacy] at hraw
    obtain ⟨K, _, _, hK, -, -, θK, -, hN, hactors⟩ := hraw
    have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
    let σ := iterateFrobeniusEquiv K 2 n
    have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobeniusEquiv_def K 2 n c
    have hσo : orderOf σ = 2 := orderOf_iterateFrobenius_half hΛ.1 hK
    obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hΛ.1 hK σ hσ
    let e := ε.symm
    let θ₀ := θK.trans e
    have hI : ((ggGamma J hN).range.map (ggInducedAut θ₀)) ≤
        (RecipeExcLang.twConj K σ).range := by
      rintro _ ⟨a, ⟨b, rfl⟩, rfl⟩
      have htrans : ggInducedAut θ₀ (ggGamma J hN b) =
          MulAut.congr e (ggInducedAut θK (ggGamma J hN b)) :=
        NbrLangTypeA.ggLAut_trans (K := J) θK e ⟨b, hN b.2⟩
      rw [htrans]
      apply (hε _).mp
      have hφ := inducedAut_mem_of_marked_action θK hN hactors b
      have hcomp : MulAut.congr ε (MulAut.congr e (ggInducedAut θK (ggGamma J hN b))) =
          ggInducedAut θK (ggGamma J hN b) := by
        ext z
        change ε (ε.symm ((ggInducedAut θK (ggGamma J hN b))
          (ε (ε.symm z)))) = (ggInducedAut θK (ggGamma J hN b)) z
        simp only [MulEquiv.apply_symm_apply]
      rwa [hcomp]
    exact Or.inr (Or.inr (toralActTw_of_card hΛ.1 hK σ hσ hσo hBs hJ hN θ₀ hI
      (hcard hN)))
  · dsimp only [LargeEvenRawDatumLegacy] at hraw
    obtain ⟨K, _, _, hK, -, -, θK, -, hN, hactors⟩ := hraw
    have : CharP K 2 := charP_two_of_card hK
    let e := TableBExc.recipeEquiv .E7 K
    let θ₀ := θK.trans e
    have hI : ((ggGamma J hN).range.map (ggInducedAut θ₀)) ≤
        (RecipeExcLang.inndiagConj .E7 K).range := by
      rintro _ ⟨a, ⟨b, rfl⟩, rfl⟩
      have hφ := inducedAut_mem_of_marked_action θK hN hactors b
      obtain ⟨z, hz⟩ := TableBExc.idImage_subset_inn_E7 K hφ
      refine ⟨⟨e z, RecipeExcLang.adjointGroup_le_inndiagGroup (e z).2⟩, ?_⟩
      have htrans : ggInducedAut θ₀ (ggGamma J hN b) =
          MulAut.congr e (ggInducedAut θK (ggGamma J hN b)) :=
        NbrLangTypeA.ggLAut_trans (K := J) θK e ⟨b, hN b.2⟩
      rw [htrans, ← hz, mulAut_congr_conj,
        RecipeExcLang.inndiagConj_of_mem]
    exact Or.inr (Or.inl (toralActUntw_of_card hK ExcFramesHalf.bigElemAbelianToralBar_E7_three
      hBs hJ hN θ₀ hI (hcardE7 ⟨.E7, l, n⟩ rfl hhas hN)))

theorem toralAct_of_marking_of_six_pow_le_card {G : Type} [Group G]
    {Bs J : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hmark : LargeEvenMarking J (fun lab _ _ I _ θ =>
      (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) ∧
        Bs ≤ Subgroup.normalizer (J : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun j j' : J => (j' : G) = b⁻¹ * j * b) φ))
    (hcard : ∀ hN : Bs ≤ Subgroup.normalizer (J : Set G),
      3 ^ 6 ≤ Nat.card (ggGamma J hN).range) :
    GGExcToralAct J ((fun b : G => MulAut.conj b) '' (Bs : Set G)) := by
  exact toralAct_of_marking_of_card hBs hmark
    (fun hN => (Nat.pow_le_pow_right (by norm_num) (by decide)).trans (hcard hN))
    (fun _ _ _ => hcard)

end Q2Exceptional

theorem ggBstarToralJExcInput_e7
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hmark : LargeEvenMarking L (fun lab _ _ I _ θ =>
      lab.tag = .E7 ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ))
    (hIDJ : GGInnerDiagOn Bs J)
    (labJ : LargeEvenLabel) (hΛJ : LargeEvenInLambda2 labJ)
    (htagJ : labJ.tag = .E6 ∨ labJ.tag = .twE6 ∨ labJ.tag = .E7)
    (hlabelJ : GGHasLabel labJ (J ⧸ Subgroup.center J)) :
    GGExcToralAct J ((fun b : G => MulAut.conj b) '' (Bs : Set G)) := by
  have hJM := ggInnerDiagOn_relabel ggLabelRigidInput_holds hIDJ hΛJ hlabelJ
  apply Q2Exceptional.toralAct_of_marking_of_card hcfg.2.1.2.1
  · refine largeEvenMarking_mono ?_ hJM
    intro lab R inst I F θ h
    exact ⟨h.1.symm ▸ htagJ, h.2⟩
  · exact fun hN => pow_five_le_card_range_gamma_J_of_e7Selected hcfg hmark hN
  · exact fun lab ht hh hN => pow_six_le_card_range_gamma_J_of_e7TagJ hcfg hN lab ht hh

theorem ggBstarToralJExcInputOn_e7_holds :
    GGBstarToralJExcInputOn (fun lab => lab.tag = .E7) := by
  intro G _ _ B Bs x L D J hcfg hmark hIDJ labJ hΛJ htagJ hlabelJ
  exact ggBstarToralJExcInput_e7 hcfg hmark hIDJ labJ hΛJ htagJ hlabelJ

theorem ggBstarToralJExcInputOn_e8_holds
    : GGBstarToralJExcInputOn (fun lab => lab.tag = .E8) := by
  intro G _ _ B Bs x L D J hcfg hL hJ labJ hΛJ htJ hlabelJ
  have hM : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .E8) := by
    refine largeEvenMarking_mono ?_ hL
    intro lab R inst I F θ h
    exact h.1
  have hJM := ggInnerDiagOn_relabel ggLabelRigidInput_holds hJ hΛJ hlabelJ
  apply Q2Exceptional.toralAct_of_marking_of_six_pow_le_card hcfg.2.1.2.1
  · refine largeEvenMarking_mono ?_ hJM
    intro lab R inst I F θ h
    exact ⟨h.1.symm ▸ htJ, h.2⟩
  · exact fun hN => Q2Exceptional.six_pow_le_card_gamma_J_of_e8 hcfg hM hN

theorem ggBstarToralJExcInput_of_not_e8
    (hrest : GGBstarToralJExcInputOn (fun lab => lab.tag ≠ .E8)) :
    GGBstarToralJExcInput := by
  intro G _ _ B Bs x L D J hcfg hL hJ labJ hΛJ htJ hlabelJ
  rcases GGInnerDiagOnLabel.elim_or (hL.label (fun _ lab => lab.tag = .E8) 3) with hE | hE
  · exact ggBstarToralJExcInputOn_e8_holds G B Bs x L D J hcfg hE hJ labJ hΛJ htJ hlabelJ
  · exact hrest G B Bs x L D J hcfg hE hJ labJ hΛJ htJ hlabelJ

theorem ggBstarToralJExcInput_of_not_e8_e7
    (hrest : GGBstarToralJExcInputOn (fun lab => lab.tag ≠ .E8 ∧ lab.tag ≠ .E7)) :
    GGBstarToralJExcInput := by
  exact ggBstarToralJExcInput_of_not_e8
    (GGBstarToralJExcInputOn.of_compl hrest ggBstarToralJExcInputOn_e7_holds)

end CFSG.StandardType
