module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs
import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTwE6
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Inn
import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.C14Exc CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem kgLangS1ENormalFormTwE6Aux_not_three_dvd_two_pow_add_one {e : ℕ}
    (heven : Even e) : ¬ 3 ∣ 2 ^ e + 1 := by
  obtain ⟨m, rfl⟩ := heven
  have hpow : (2 : ℕ) ^ (m + m) = 4 ^ m := by
    rw [pow_add, ← mul_pow]
    norm_num
  have h4 : ∀ k : ℕ, 4 ^ k % 3 = 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => simp [pow_succ, Nat.mul_mod, ih]
  intro hdvd
  have hmod : (2 ^ (m + m) + 1) % 3 = 2 := by
    simp [hpow, Nat.add_mod, h4]
  rw [Nat.mod_eq_zero_of_dvd hdvd] at hmod
  exact absurd hmod (by norm_num)

private theorem kgLangS1ENormalFormTwE6Aux_twInndiag_eq_graphFixed
    {K : Type} [Field K] [Finite K] {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q)
    (h3 : ¬ 3 ∣ q + 1) :
    RecipeExcLang.twInndiagGroup K σ = graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  refine le_antisymm ?_ (RecipeExcLang.graphFixedRootGroup_le_twInndiag σ)
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (hc | ⟨b, hb, rfl⟩)
  · exact hc
  · have hb' : b ∈ TableB.TwE6.compat σ.toRingHom := fun i => hb i
    have hbt := TableB.TwE6.compat_le_torus₀ hq hK hσ h3 hb'
    obtain ⟨s, hs, hsb⟩ := Subgroup.mem_map.1 hbt
    rw [← hsb]
    refine TableB.TwE6.rootDiagUnit_cartanChar_mem (t := TwistTag.E6) (K := K)
      (σ := σ.toRingHom) ?_
    exact (TableB.TwE6.mem_compat (σ := σ.toRingHom)).1 hs

private theorem kgLangS1ENormalFormTwE6Aux_sigma_pow
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

private theorem kgLangS1ENormalFormTwE6Aux_eq_of_conj_eq
    {K₀ k : Type} [Field K₀] [Field k]
    (σ₀ : K₀ ≃+* K₀) (σ : k →+* k)
    (Ψ : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 k σ))
    (hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 k σ) = ⊥)
    {u y : ↥(graphFixedRootGroup TwistTag.E6 k σ)}
    (hrel : ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
      u * Ψ z * u⁻¹ = y * Ψ z * y⁻¹) : y = u := by
  have hcent : ∀ v : ↥(graphFixedRootGroup TwistTag.E6 k σ),
      (u⁻¹ * y) * v = v * (u⁻¹ * y) := by
    intro v
    obtain ⟨z, rfl⟩ := Ψ.surjective v
    have h2 : y * Ψ z * y⁻¹ = u * Ψ z * u⁻¹ := (hrel z).symm
    calc (u⁻¹ * y) * Ψ z = u⁻¹ * (y * Ψ z * y⁻¹) * y := by group
      _ = u⁻¹ * (u * Ψ z * u⁻¹) * y := by rw [h2]
      _ = Ψ z * (u⁻¹ * y) := by group
  have hmem : u⁻¹ * y ∈ Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 k σ) := by
    rw [Subgroup.mem_center_iff]
    exact fun v => (hcent v).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  calc y = u * (u⁻¹ * y) := by group
    _ = u := by rw [hmem, mul_one]

private theorem kgLangS1ENormalFormTwE6Aux_y_normalForm
    {K₀ k : Type} [Field K₀] [Finite K₀] [Field k]
    (σ₀ : K₀ ≃+* K₀) (σ : k →+* k)
    (Ψ : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 k σ))
    (hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 k σ) = ⊥)
    (W : Subgroup ↥(RecipeExcLang.twInndiagGroup K₀ σ₀))
    (hle : RecipeExcLang.twInndiagGroup K₀ σ₀ ≤
      graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom)
    {Y : Set (ModGL TwistTag.E6.tag k)} {β : K₀ →+* k} {g' : ModGL TwistTag.E6.tag k}
    (hnorm : ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
      (Ψ z : ModGL TwistTag.E6.tag k) =
        g' * baseChangeGL (τ := TwistTag.E6.tag) β
          (z : ModGL TwistTag.E6.tag K₀) * g'⁻¹)
    (hY : ∀ y ∈ Y, ∃ hy : y ∈ graphFixedRootGroup TwistTag.E6 k σ, ∃ w ∈ W,
      ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
        Ψ (RecipeExcLang.twConj K₀ σ₀ w z) =
          (⟨y, hy⟩ : ↥(graphFixedRootGroup TwistTag.E6 k σ)) * Ψ z *
            (⟨y, hy⟩ : ↥(graphFixedRootGroup TwistTag.E6 k σ))⁻¹)
    {y : ModGL TwistTag.E6.tag k} (hy : y ∈ Y) :
    ∃ w ∈ W, y = g' * baseChangeGL (τ := TwistTag.E6.tag) β
      (w : ModGL TwistTag.E6.tag K₀) * g'⁻¹ := by
  obtain ⟨hyG, w, hwW, hconj⟩ := hY y hy
  let wA : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom) :=
    ⟨(w : ModGL TwistTag.E6.tag K₀), hle w.2⟩
  have hconj_eq : ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
      RecipeExcLang.twConj K₀ σ₀ w z = wA * z * wA⁻¹ := by
    intro z
    apply Subtype.ext
    rw [RecipeExcLang.coe_twConj]
    rfl
  have hrel : ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
      Ψ wA * Ψ z * (Ψ wA)⁻¹ =
        (⟨y, hyG⟩ : ↥(graphFixedRootGroup TwistTag.E6 k σ)) * Ψ z *
          (⟨y, hyG⟩ : ↥(graphFixedRootGroup TwistTag.E6 k σ))⁻¹ := by
    intro z
    have h := hconj z
    rw [hconj_eq z, map_mul, map_mul, map_inv] at h
    exact h
  have hy_eq : (⟨y, hyG⟩ : ↥(graphFixedRootGroup TwistTag.E6 k σ)) = Ψ wA :=
    kgLangS1ENormalFormTwE6Aux_eq_of_conj_eq σ₀ σ Ψ hZ hrel
  refine ⟨w, hwW, ?_⟩
  have hyval : y = (Ψ wA : ModGL TwistTag.E6.tag k) := congrArg Subtype.val hy_eq
  rw [hyval]
  exact hnorm wA

private theorem kgLangS1ENormalFormTwE6Aux_generator_toral
    {K₀ k L : Type} [Field K₀] [Field k] [Field L] [Algebra K₀ L]
    (σ₀ : K₀ ≃+* K₀) (σ : k →+* k)
    (β : K₀ →+* k) (ι : k →+* L) (lamR : AlgebraicClosure K₀ →+* L)
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

private theorem kgLangS1ENormalFormTwE6Aux_toral
    {K₀ k L : Type} [Field K₀] [Field k] [Field L] [IsAlgClosed L]
    (σ₀ : K₀ ≃+* K₀) (σ : k →+* k)
    (β : K₀ →+* k) (ι : k →+* L) {g' : ModGL TwistTag.E6.tag k}
    (hg' : g' ∈ graphFixedRootGroup TwistTag.E6 k σ)
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
    mul_mem (baseChangeGL_mem_adjointGroup (τ := TwistTag.E6.tag) ι
      (graphFixedRootGroup_le TwistTag.E6 k σ hg').1)
      (baseChangeGL_mem_adjointGroup (τ := TwistTag.E6.tag) lamR hh₀G)
  refine ⟨c, hc, ?_⟩
  intro x hx
  have hgen : ∀ y ∈ (baseChangeGL (τ := TwistTag.E6.tag) ι) '' Y,
      (MulAut.conj c⁻¹) y ∈ torusGroup TwistTag.E6.tag L := by
    rintro _ ⟨y, hyY, rfl⟩
    exact kgLangS1ENormalFormTwE6Aux_generator_toral σ₀ σ β ι lamR hlam W hYmap
      h₀ hh₀tor c rfl hyY
  have hclosure : Subgroup.closure ((baseChangeGL (τ := TwistTag.E6.tag) ι) '' Y) ≤
      Subgroup.comap (MulAut.conj c⁻¹).toMonoidHom (torusGroup TwistTag.E6.tag L) :=
    (Subgroup.closure_le _).2 hgen
  have hx' : (MulAut.conj c⁻¹) x ∈ torusGroup TwistTag.E6.tag L := hclosure hx
  simpa only [MulAut.conj_apply, inv_inv] using hx'

private theorem kgLangS1ENormalFormTwE6Aux_normalForm
    {e : ℕ} (he : 1 ≤ e) {K₀ k : Type} [Field K₀] [Finite K₀] [Field k] [Finite k]
    (hK₀ : Nat.card K₀ = (2 ^ e) ^ 2) (hk : Nat.card k = (2 ^ e) ^ 2)
    (σ₀ : K₀ ≃+* K₀) (hσ₀ : ∀ c, σ₀ c = c ^ 2 ^ e)
    (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    (hΓ : RecipeExcLang.twInndiagGroup k σ =
      graphFixedRootGroup TwistTag.E6 k σ.toRingHom)
    (Ψ : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom)) :
    ∃ (β : K₀ →+* k) (g' : ModGL TwistTag.E6.tag k),
      g' ∈ graphFixedRootGroup TwistTag.E6 k σ.toRingHom ∧
      ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
        (Ψ z : ModGL TwistTag.E6.tag k) =
          g' * baseChangeGL (τ := TwistTag.E6.tag) β
            (z : ModGL TwistTag.E6.tag K₀) * g'⁻¹ := by
  letI : Fintype K₀ := Fintype.ofFinite K₀
  letI : Fintype k := Fintype.ofFinite k
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
  have hdU : dU ∈ graphFixedRootGroup TwistTag.E6 k σ.toRingHom := by
    rw [← hΓ]
    exact RecipeExcLang.rootDiagUnit_mem_twInndiag (compatDiag_perm u)
  have hg' : g' ∈ graphFixedRootGroup TwistTag.E6 k σ.toRingHom := mul_mem g.2 hdU
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

theorem kgLangS1E_ratPts_frob_twE6
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 1 ≤ e) (heven : Even e) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (σ : k ≃+* k) (ι : k →+* L),
      Nat.card k = (2 ^ e) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ e) ∧
      ratPts TwistTag.E6.tag L (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) =
        (graphFixedRootGroup TwistTag.E6 k σ.toRingHom).map (baseChangeGL ι) := by
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
  have hq : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have h3 : ¬ 3 ∣ 2 ^ e + 1 :=
    kgLangS1ENormalFormTwE6Aux_not_three_dvd_two_pow_add_one heven
  have hEq := kgLangS1ENormalFormTwE6Aux_twInndiag_eq_graphFixed (q := 2 ^ e) hq hcard σ hσ h3
  have hrat : ratPts TwistTag.E6.tag L
      (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) =
      CFSG.Blueprint.twistedFixedGroup TwistTag.E6 L (iterateFrobenius L 2 e) := rfl
  rw [hrat]
  rw [CFSG.HardMathSupport.C14ExcBridgeTwE6.twisted_fixed_eq_map
    (K := GaloisField 2 (2 * e)) (n := e) he hcard σ hσ
    (iterateFrobenius L 2 e) (fun c => iterateFrobenius_def (R := L) 2 e c)]
  rw [hEq]
  rfl

theorem kgLangS1E_normalForm_toral_twE6
    {e : ℕ} (he : 1 ≤ e) (heven : Even e) {K₀ k : Type} [Field K₀] [Finite K₀] [Field k]
    [Finite k] (hK₀ : Nat.card K₀ = (2 ^ e) ^ 2) (hk : Nat.card k = (2 ^ e) ^ 2)
    (σ₀ : K₀ ≃+* K₀) (hσ₀ : orderOf σ₀ = 2) (σ : k ≃+* k) (hσ : ∀ c, σ c = c ^ 2 ^ e)
    (Ψ : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom))
    {L : Type} [Field L] [IsAlgClosed L] (ι : k →+* L)
    (W : Subgroup ↥(RecipeExcLang.twInndiagGroup K₀ σ₀))
    (hW : GGGeomToral TwistTag.E6.tag K₀ (W.map (RecipeExcLang.twInndiagGroup K₀ σ₀).subtype))
    (Y : Set (ModGL TwistTag.E6.tag k))
    (hY : ∀ y ∈ Y, ∃ hy : y ∈ graphFixedRootGroup TwistTag.E6 k σ.toRingHom, ∃ w ∈ W,
      ∀ z : ↥(graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom),
        Ψ (RecipeExcLang.twConj K₀ σ₀ w z) =
          (⟨y, hy⟩ : ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom)) * Ψ z *
            (⟨y, hy⟩ : ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom))⁻¹) :
    ExcFramesHalf.IsToralSubgroup TwistTag.E6.tag L
      (Subgroup.closure ((baseChangeGL (τ := TwistTag.E6.tag) ι) '' Y)) := by
  have hσ₀' : ∀ c, σ₀ c = c ^ 2 ^ e :=
    kgLangS1ENormalFormTwE6Aux_sigma_pow he hK₀ σ₀ hσ₀
  have hq : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have h3 : ¬ 3 ∣ 2 ^ e + 1 :=
    kgLangS1ENormalFormTwE6Aux_not_three_dvd_two_pow_add_one heven
  have hEqK₀ := kgLangS1ENormalFormTwE6Aux_twInndiag_eq_graphFixed
    (q := 2 ^ e) hq hK₀ σ₀ hσ₀' h3
  have hEqk := kgLangS1ENormalFormTwE6Aux_twInndiag_eq_graphFixed
    (q := 2 ^ e) hq hk σ hσ h3
  obtain ⟨β, g', hg', hnorm⟩ :=
    kgLangS1ENormalFormTwE6Aux_normalForm he hK₀ hk σ₀ hσ₀' σ hσ hEqk Ψ
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 k σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 k σ
  have hle : RecipeExcLang.twInndiagGroup K₀ σ₀ ≤
      graphFixedRootGroup TwistTag.E6 K₀ σ₀.toRingHom := by
    rw [hEqK₀]
  have hYmap : ∀ y ∈ Y, ∃ w ∈ W, y = g' * baseChangeGL (τ := TwistTag.E6.tag) β
      (w : ModGL TwistTag.E6.tag K₀) * g'⁻¹ :=
    fun y hy => kgLangS1ENormalFormTwE6Aux_y_normalForm σ₀ σ.toRingHom Ψ hZ W hle
      hnorm hY hy
  exact kgLangS1ENormalFormTwE6Aux_toral σ₀ σ.toRingHom β ι hg' W hW hYmap

end CFSG.StandardType

end
