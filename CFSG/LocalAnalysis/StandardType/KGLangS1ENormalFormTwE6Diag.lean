module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTwE6
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.C14Exc CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem kgLangS1ENormalFormTwE6DiagAux_sigma_pow
    {K : Type} [Field K] [Finite K] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = (2 ^ e) ^ 2) (σ : K ≃+* K) (hσ : orderOf σ = 2) :
    ∀ c, σ c = c ^ 2 ^ e := by
  have hK2 : Nat.card K = 2 ^ (2 * e) := by
    rw [hK, ← pow_mul]
    congr 1
    ring
  have hσ2 : σ ^ 2 = 1 := by rw [← pow_orderOf_eq_one σ, hσ]
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    exact absurd hσ (by decide)
  obtain ⟨-, hpow, -⟩ :=
    ringEquiv_sq_eq_one_facts Nat.prime_two (f := 2 * e) (by omega) hK2 hσ2 hσ1
  intro c
  rw [hpow c, show 2 * e / 2 = e by omega]

private theorem kgLangS1ENormalFormTwE6DiagAux_baseChange_mem
    {e : ℕ} (he : 1 ≤ e) {K₀ k : Type} [Field K₀] [Finite K₀] [Field k] [Finite k]
    (hK₀ : Nat.card K₀ = (2 ^ e) ^ 2)
    (σ₀ : K₀ ≃+* K₀) (hσ₀ : ∀ c, σ₀ c = c ^ 2 ^ e) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    (β : K₀ →+* k) {w : ModGL TwistTag.E6.tag K₀}
    (hw : w ∈ RecipeExcLang.twInndiagGroup K₀ σ₀) :
    baseChangeGL (τ := TwistTag.E6.tag) β w ∈ RecipeExcLang.twInndiagGroup k σ := by
  have hmap := CFSG.LieType.Chevalley.map_baseChangeGL_graphFixedRootGroup_eq
    (t := TwistTag.E6) (p := 2) (f := e) (hp := Nat.prime_two) (hf := he)
    (K := K₀) (hK := hK₀) (σ := σ₀.toRingHom) (hσ := hσ₀)
    (ι := β) (Fr := σ.toRingHom) (hFr := hσ) (hFrsurj := σ.surjective)
  have hle : RecipeExcLang.twInndiagGroup K₀ σ₀ ≤
      (RecipeExcLang.twInndiagGroup k σ).comap (baseChangeGL (τ := TwistTag.E6.tag) β) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (hc | ⟨b, hb, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_comap]
      apply RecipeExcLang.graphFixedRootGroup_le_twInndiag σ
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hc
    · rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_rootDiagUnit]
      refine RecipeExcLang.rootDiagUnit_mem_twInndiag fun i => ?_
      apply Units.ext
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
      rw [hb i]
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
      change β (σ₀ (b i : K₀)) = σ (β (b i : K₀))
      rw [hσ₀, hσ, map_pow]
  exact hle hw

private theorem kgLangS1ENormalFormTwE6DiagAux_mem_adjoint
    {k L : Type} [Field k] [Finite k] [Field L] [IsAlgClosed L] (σ : k ≃+* k) (ι : k →+* L)
    {g : ModGL TwistTag.E6.tag k} (hg : g ∈ RecipeExcLang.twInndiagGroup k σ) :
    baseChangeGL (τ := TwistTag.E6.tag) ι g ∈ adjointGroup TwistTag.E6.tag L := by
  have hle : RecipeExcLang.twInndiagGroup k σ ≤
      (adjointGroup TwistTag.E6.tag L).comap (baseChangeGL (τ := TwistTag.E6.tag) ι) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (hc | ⟨b, -, rfl⟩)
    · exact baseChangeGL_mem_adjointGroup (τ := TwistTag.E6.tag) ι
        (graphFixedRootGroup_le TwistTag.E6 k σ.toRingHom hc).1
    · rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_rootDiagUnit]
      exact CFSG.RankThree.Classical2.torusGroup_le_adjointGroup_of_field
        (CFSG.LieType.Chevalley.rootDiagUnit_mem_torusGroup _)
  exact hle hg

private theorem kgLangS1ENormalFormTwE6DiagAux_y_normalForm
    {e : ℕ} (he : 1 ≤ e) {K₀ k : Type} [Field K₀] [Finite K₀] [Field k] [Finite k]
    (hK₀ : Nat.card K₀ = (2 ^ e) ^ 2) (hk : Nat.card k = (2 ^ e) ^ 2)
    (σ₀ : K₀ ≃+* K₀) (hσ₀ : ∀ c, σ₀ c = c ^ 2 ^ e) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    (Ψ : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom))
    {β : K₀ →+* k} {g' : ModGL TwistTag.E6.tag k} (hg' : g' ∈ RecipeExcLang.twInndiagGroup k σ)
    (hnorm : ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
      (Ψ z : ModGL TwistTag.E6.tag k) =
        g' * baseChangeGL (τ := TwistTag.E6.tag) β (z : ModGL TwistTag.E6.tag K₀) * g'⁻¹)
    (W : Subgroup ↥(RecipeExcLang.twInndiagGroup K₀ σ₀))
    {Y : Set (ModGL TwistTag.E6.tag k)}
    (hY : ∀ y ∈ Y, ∃ hy : y ∈ RecipeExcLang.twInndiagGroup k σ, ∃ w ∈ W,
      ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
        Ψ (RecipeExcLang.twConj K₀ σ₀ w z) = RecipeExcLang.twConj k σ ⟨y, hy⟩ (Ψ z))
    {y : ModGL TwistTag.E6.tag k} (hy : y ∈ Y) :
    ∃ w ∈ W, y = g' * baseChangeGL (τ := TwistTag.E6.tag) β
      (w : ModGL TwistTag.E6.tag K₀) * g'⁻¹ := by
  obtain ⟨hyΓ, w, hwW, hconj⟩ := hY y hy
  have hβw : baseChangeGL (τ := TwistTag.E6.tag) β (w : ModGL TwistTag.E6.tag K₀) ∈
      RecipeExcLang.twInndiagGroup k σ :=
    kgLangS1ENormalFormTwE6DiagAux_baseChange_mem he hK₀ σ₀ hσ₀ σ hσ β w.2
  have hw' : g' * baseChangeGL (τ := TwistTag.E6.tag) β (w : ModGL TwistTag.E6.tag K₀) * g'⁻¹ ∈
      RecipeExcLang.twInndiagGroup k σ :=
    mul_mem (mul_mem hg' hβw) (inv_mem hg')
  have heq : RecipeExcLang.twConj k σ ⟨_, hw'⟩ = RecipeExcLang.twConj k σ ⟨y, hyΓ⟩ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    obtain ⟨z, rfl⟩ := Ψ.surjective h
    have h1 := congrArg Subtype.val (hconj z)
    rw [RecipeExcLang.coe_twConj, RecipeExcLang.coe_twConj]
    rw [RecipeExcLang.coe_twConj] at h1
    rw [← h1, hnorm (RecipeExcLang.twConj K₀ σ₀ w z), RecipeExcLang.coe_twConj, hnorm z,
      map_mul, map_mul, map_inv]
    group
  have hinj := NoOffTwE6Three.twConj_injective he hk σ hσ heq
  exact ⟨w, hwW, (congrArg Subtype.val hinj).symm⟩

private theorem kgLangS1ENormalFormTwE6DiagAux_generator_toral
    {K₀ k L : Type} [Field K₀] [Finite K₀] [Field k] [Field L]
    (σ₀ : K₀ ≃+* K₀) (β : K₀ →+* k) (ι : k →+* L) (lamR : AlgebraicClosure K₀ →+* L)
    (hlam : lamR.comp (algebraMap K₀ (AlgebraicClosure K₀)) = ι.comp β)
    (W : Subgroup ↥(RecipeExcLang.twInndiagGroup K₀ σ₀))
    {Y : Set (ModGL TwistTag.E6.tag k)} {g' : ModGL TwistTag.E6.tag k}
    (hYmap : ∀ y ∈ Y, ∃ w ∈ W, y = g' * baseChangeGL (τ := TwistTag.E6.tag) β
      (w : ModGL TwistTag.E6.tag K₀) * g'⁻¹)
    (h₀ : ModGL TwistTag.E6.tag (AlgebraicClosure K₀))
    (hh₀tor : ∀ x ∈ (W.map (RecipeExcLang.twInndiagGroup K₀ σ₀).subtype).map
      (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K₀ (AlgebraicClosure K₀))),
        h₀⁻¹ * x * h₀ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K₀))
    (c : ModGL TwistTag.E6.tag L)
    (hc : c = baseChangeGL (τ := TwistTag.E6.tag) ι g' *
      baseChangeGL (τ := TwistTag.E6.tag) lamR h₀)
    {y : ModGL TwistTag.E6.tag k} (hy : y ∈ Y) :
    (MulAut.conj c⁻¹) (baseChangeGL (τ := TwistTag.E6.tag) ι y) ∈
      torusGroup TwistTag.E6.tag L := by
  obtain ⟨w, hwW, hy_eq⟩ := hYmap y hy
  let xw : ModGL TwistTag.E6.tag (AlgebraicClosure K₀) :=
    baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K₀ (AlgebraicClosure K₀))
      (w : ModGL TwistTag.E6.tag K₀)
  have hxw : xw ∈ (W.map (RecipeExcLang.twInndiagGroup K₀ σ₀).subtype).map
      (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K₀ (AlgebraicClosure K₀))) :=
    ⟨(w : ModGL TwistTag.E6.tag K₀), ⟨w, hwW, rfl⟩, rfl⟩
  have htor : h₀⁻¹ * xw * h₀ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K₀) :=
    hh₀tor xw hxw
  have htorL := CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup (τ := TwistTag.E6.tag)
    lamR htor
  have hmid : baseChangeGL (τ := TwistTag.E6.tag) ι
        (baseChangeGL (τ := TwistTag.E6.tag) β (w : ModGL TwistTag.E6.tag K₀)) =
      baseChangeGL (τ := TwistTag.E6.tag) lamR xw := by
    simp only [xw, CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hlam]
  simp only [MulAut.conj_apply, inv_inv]
  have hyL : baseChangeGL (τ := TwistTag.E6.tag) ι y =
      baseChangeGL (τ := TwistTag.E6.tag) ι g' *
        baseChangeGL (τ := TwistTag.E6.tag) lamR xw *
          (baseChangeGL (τ := TwistTag.E6.tag) ι g')⁻¹ := by
    rw [hy_eq]
    simp only [map_mul, map_inv, hmid]
  rw [hyL, hc]
  have hfinal : (baseChangeGL (τ := TwistTag.E6.tag) ι g' *
        baseChangeGL (τ := TwistTag.E6.tag) lamR h₀)⁻¹ *
        (baseChangeGL (τ := TwistTag.E6.tag) ι g' *
          baseChangeGL (τ := TwistTag.E6.tag) lamR xw *
            (baseChangeGL (τ := TwistTag.E6.tag) ι g')⁻¹) *
        (baseChangeGL (τ := TwistTag.E6.tag) ι g' *
          baseChangeGL (τ := TwistTag.E6.tag) lamR h₀) =
      baseChangeGL (τ := TwistTag.E6.tag) lamR (h₀⁻¹ * xw * h₀) := by
    simp only [map_mul, map_inv]
    group
  rw [hfinal]
  exact htorL

private theorem kgLangS1ENormalFormTwE6DiagAux_toral
    {K₀ k L : Type} [Field K₀] [Finite K₀] [Field k] [Field L] [IsAlgClosed L]
    (σ₀ : K₀ ≃+* K₀) (β : K₀ →+* k) (ι : k →+* L) {g' : ModGL TwistTag.E6.tag k}
    (hg' : baseChangeGL (τ := TwistTag.E6.tag) ι g' ∈ adjointGroup TwistTag.E6.tag L)
    (W : Subgroup ↥(RecipeExcLang.twInndiagGroup K₀ σ₀))
    (hW : GGGeomToral TwistTag.E6.tag K₀
      (W.map (RecipeExcLang.twInndiagGroup K₀ σ₀).subtype))
    {Y : Set (ModGL TwistTag.E6.tag k)}
    (hYmap : ∀ y ∈ Y, ∃ w ∈ W, y = g' * baseChangeGL (τ := TwistTag.E6.tag) β
      (w : ModGL TwistTag.E6.tag K₀) * g'⁻¹) :
    ExcFramesHalf.IsToralSubgroup TwistTag.E6.tag L
      (Subgroup.closure ((baseChangeGL (τ := TwistTag.E6.tag) ι) '' Y)) := by
  let _ : Algebra K₀ L := (ι.comp β).toAlgebra
  obtain ⟨lam⟩ : Nonempty (AlgebraicClosure K₀ →ₐ[K₀] L) := ⟨IsAlgClosed.lift⟩
  let lamR : AlgebraicClosure K₀ →+* L := lam.toRingHom
  have hlam : lamR.comp (algebraMap K₀ (AlgebraicClosure K₀)) = ι.comp β := by
    ext c
    exact lam.commutes c
  obtain ⟨h₀, hh₀G, hh₀tor⟩ := hW
  let c : ModGL TwistTag.E6.tag L := baseChangeGL (τ := TwistTag.E6.tag) ι g' *
    baseChangeGL (τ := TwistTag.E6.tag) lamR h₀
  have hc : c ∈ adjointGroup TwistTag.E6.tag L :=
    mul_mem hg' (baseChangeGL_mem_adjointGroup (τ := TwistTag.E6.tag) lamR hh₀G)
  refine ⟨c, hc, ?_⟩
  intro x hx
  have hgen : ∀ y ∈ (baseChangeGL (τ := TwistTag.E6.tag) ι) '' Y,
      (MulAut.conj c⁻¹) y ∈ torusGroup TwistTag.E6.tag L := by
    rintro _ ⟨y, hyY, rfl⟩
    exact kgLangS1ENormalFormTwE6DiagAux_generator_toral σ₀ β ι lamR hlam W hYmap
      h₀ hh₀tor c rfl hyY
  have hclosure : Subgroup.closure ((baseChangeGL (τ := TwistTag.E6.tag) ι) '' Y) ≤
      Subgroup.comap (MulAut.conj c⁻¹).toMonoidHom (torusGroup TwistTag.E6.tag L) :=
    (Subgroup.closure_le _).2 hgen
  have hx' : (MulAut.conj c⁻¹) x ∈ torusGroup TwistTag.E6.tag L := hclosure hx
  simpa only [MulAut.conj_apply, inv_inv] using hx'

private theorem kgLangS1ENormalFormTwE6DiagAux_normalForm
    {e : ℕ} (he : 1 ≤ e) {K₀ k : Type} [Field K₀] [Finite K₀] [Field k] [Finite k]
    (hK₀ : Nat.card K₀ = (2 ^ e) ^ 2) (hk : Nat.card k = (2 ^ e) ^ 2)
    (σ₀ : K₀ ≃+* K₀) (hσ₀ : ∀ c, σ₀ c = c ^ 2 ^ e)
    (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    (Ψ : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom)) :
    ∃ (β : K₀ →+* k) (g' : ModGL TwistTag.E6.tag k),
      g' ∈ RecipeExcLang.twInndiagGroup k σ ∧
      ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
        (Ψ z : ModGL TwistTag.E6.tag k) =
          g' * baseChangeGL (τ := TwistTag.E6.tag) β
            (z : ModGL TwistTag.E6.tag K₀) * g'⁻¹ := by
  let _ : Fintype K₀ := Fintype.ofFinite K₀
  let _ : Fintype k := Fintype.ofFinite k
  have hcardF : Fintype.card K₀ = Fintype.card k := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀, hk]
  let φ₀ : K₀ ≃+* k := FiniteField.ringEquivOfCardEq hcardF
  have hmap := CFSG.LieType.Chevalley.map_baseChangeGL_graphFixedRootGroup_eq
    (t := TwistTag.E6) (p := 2) (f := e) (hp := Nat.prime_two) (hf := he)
    (K := K₀) (hK := hK₀) (σ := σ₀.toRingHom) (hσ := hσ₀)
    (ι := φ₀.toRingHom) (Fr := σ.toRingHom) (hFr := hσ) (hFrsurj := σ.surjective)
  let eφ : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) :=
    (Subgroup.equivMapOfInjective
      (graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom)
      (baseChangeGL (τ := TwistTag.E6.tag) φ₀.toRingHom)
      (baseChangeGL_injective (τ := TwistTag.E6.tag) φ₀.toRingHom)).trans
      (MulEquiv.subgroupCongr hmap)
  have hcoeφ : ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
      (eφ z : ModGL TwistTag.E6.tag k) =
        baseChangeGL (τ := TwistTag.E6.tag) φ₀.toRingHom z := by
    intro z
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      Subgroup.coe_equivMapOfInjective_apply]
  let α : MulAut ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) := eφ.symm.trans Ψ
  obtain ⟨g, u, δ, hα⟩ :=
    CFSG.LieType.Chevalley.exists_normalForm_E6 (p := 2) (f := e) Nat.prime_two he hk
      σ hσ α
  let dU : ModGL TwistTag.E6.tag k :=
    rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)
  let g' : ModGL TwistTag.E6.tag k := (g : ModGL TwistTag.E6.tag k) * dU
  have hdU : dU ∈ RecipeExcLang.twInndiagGroup k σ :=
    RecipeExcLang.rootDiagUnit_mem_twInndiag (compatDiag_perm u)
  have hg' : g' ∈ RecipeExcLang.twInndiagGroup k σ :=
    mul_mem (RecipeExcLang.graphFixedRootGroup_le_twInndiag σ g.2) hdU
  refine ⟨δ.toRingHom.comp φ₀.toRingHom, g', hg', ?_⟩
  intro z
  have hαz : α (eφ z) = Ψ z := by
    change Ψ (eφ.symm (eφ z)) = Ψ z
    rw [MulEquiv.symm_apply_apply]
  have h := congrArg (fun F : MulAut ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) =>
    F (eφ z)) hα
  have hval : (Ψ z : ModGL TwistTag.E6.tag k) =
      (g : ModGL TwistTag.E6.tag k) *
        (normalActor σ u δ (eφ z) : ModGL TwistTag.E6.tag k) *
          (g : ModGL TwistTag.E6.tag k)⁻¹ := by
    have h1 := congrArg Subtype.val h
    rw [hαz] at h1
    simpa only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      using h1
  have hcoef : (normalActor σ u δ (eφ z) : ModGL TwistTag.E6.tag k) =
      dU * baseChangeGL (τ := TwistTag.E6.tag) (δ.toRingHom.comp φ₀.toRingHom)
        (z : ModGL TwistTag.E6.tag K₀) * dU⁻¹ := by
    rw [CFSG.LieType.Chevalley.normalActor, MulAut.mul_apply,
      CFSG.LieType.Chevalley.coe_compatDiagAutHom,
      CFSG.LieType.Chevalley.coe_fieldActor, hcoeφ z,
      CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL]
  rw [hval, hcoef]
  rw [show g' = (g : ModGL TwistTag.E6.tag k) * dU from rfl]
  group

theorem kgLangS1E_ratPts_frob_twE6_inndiag
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (σ : k ≃+* k) (ι : k →+* L),
      Nat.card k = (2 ^ e) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ e) ∧
      ratPts TwistTag.E6.tag L (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) =
        (RecipeExcLang.twInndiagGroup k σ).map (baseChangeGL ι) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) (GaloisField 2 (2 * e)) := ZMod.algebra _ 2
  let _ : Algebra (ZMod 2) L := ZMod.algebra _ 2
  obtain ⟨φ⟩ : Nonempty (GaloisField 2 (2 * e) →ₐ[ZMod 2] L) := ⟨IsAlgClosed.lift⟩
  let ι : GaloisField 2 (2 * e) →+* L := φ.toRingHom
  let σ : GaloisField 2 (2 * e) ≃+* GaloisField 2 (2 * e) :=
    iterateFrobeniusEquiv (GaloisField 2 (2 * e)) 2 e
  have hcard : Nat.card (GaloisField 2 (2 * e)) = (2 ^ e) ^ 2 := by
    rw [GaloisField.card 2 (2 * e) (by omega), show 2 * e = e * 2 by ring, pow_mul]
  have hσ : ∀ c, σ c = c ^ 2 ^ e := fun c =>
    iterateFrobeniusEquiv_def (GaloisField 2 (2 * e)) 2 e c
  refine ⟨GaloisField 2 (2 * e), inferInstance, inferInstance, σ, ι, hcard, hσ, ?_⟩
  let _ : Algebra (GaloisField 2 (2 * e)) L := ι.toAlgebra
  have hrat : ratPts TwistTag.E6.tag L
      (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) =
      CFSG.Blueprint.twistedFixedGroup TwistTag.E6 L (iterateFrobenius L 2 e) := rfl
  rw [hrat]
  rw [CFSG.HardMathSupport.C14ExcBridgeTwE6.twisted_fixed_eq_map
    (K := GaloisField 2 (2 * e)) (n := e) he hcard σ hσ
    (iterateFrobenius L 2 e) (fun c => iterateFrobenius_def (R := L) 2 e c)]
  rfl

theorem kgLangS1E_normalForm_toral_twE6_inndiag
    {e : ℕ} (he : 1 ≤ e) {K₀ k : Type} [Field K₀] [Finite K₀] [Field k]
    [Finite k] (hK₀ : Nat.card K₀ = (2 ^ e) ^ 2) (hk : Nat.card k = (2 ^ e) ^ 2)
    (σ₀ : K₀ ≃+* K₀) (hσ₀ : orderOf σ₀ = 2) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    (Ψ : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom))
    {L : Type} [Field L] [IsAlgClosed L] (ι : k →+* L)
    (W : Subgroup ↥(RecipeExcLang.twInndiagGroup K₀ σ₀))
    (hW : GGGeomToral TwistTag.E6.tag K₀ (W.map (RecipeExcLang.twInndiagGroup K₀ σ₀).subtype))
    (Y : Set (ModGL TwistTag.E6.tag k))
    (hY : ∀ y ∈ Y, ∃ hy : y ∈ RecipeExcLang.twInndiagGroup k σ, ∃ w ∈ W,
      ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
        Ψ (RecipeExcLang.twConj K₀ σ₀ w z) = RecipeExcLang.twConj k σ ⟨y, hy⟩ (Ψ z)) :
    ExcFramesHalf.IsToralSubgroup TwistTag.E6.tag L
      (Subgroup.closure ((baseChangeGL (τ := TwistTag.E6.tag) ι) '' Y)) := by
  have hσ₀' : ∀ c, σ₀ c = c ^ 2 ^ e :=
    kgLangS1ENormalFormTwE6DiagAux_sigma_pow he hK₀ σ₀ hσ₀
  obtain ⟨β, g', hg', hnorm⟩ :=
    kgLangS1ENormalFormTwE6DiagAux_normalForm he hK₀ hk σ₀ hσ₀' σ hσ Ψ
  have hYmap : ∀ y ∈ Y, ∃ w ∈ W, y = g' * baseChangeGL (τ := TwistTag.E6.tag) β
      (w : ModGL TwistTag.E6.tag K₀) * g'⁻¹ :=
    fun y hy => kgLangS1ENormalFormTwE6DiagAux_y_normalForm he hK₀ hk σ₀ hσ₀' σ hσ Ψ hg'
      hnorm W hY hy
  exact kgLangS1ENormalFormTwE6DiagAux_toral σ₀ β ι
    (kgLangS1ENormalFormTwE6DiagAux_mem_adjoint σ ι hg') W hW hYmap

end CFSG.StandardType

end
