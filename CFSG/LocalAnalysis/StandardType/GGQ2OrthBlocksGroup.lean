module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthStatements
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.ClassicalGroups.Orthogonal.MatrixIsometry
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksGroup

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition CFSG.ClassicalGroups.Symplectic Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma liftV_apply_castAdd (t : ℕ) (δ : Fin 2) (u : PlaneRaw.V t) (i : Fin t) :
    liftV t δ u (Fin.castAdd δ.val i) = u i := by
  change Fin.append u (0 : Fin δ.val → ZMod 3) (Fin.castAdd δ.val i) = u i
  rw [Fin.append_left]

lemma liftV_apply_natAdd (t : ℕ) (δ : Fin 2) (u : PlaneRaw.V t) (j : Fin δ.val) :
    liftV t δ u (Fin.natAdd t j) = 0 := by
  change Fin.append u (0 : Fin δ.val → ZMod 3) (Fin.natAdd t j) = 0
  rw [Fin.append_right]
  rfl

theorem liftV_injective (t : ℕ) (δ : Fin 2) : Function.Injective (liftV t δ) := by
  intro u v h
  funext i
  have := congrFun h (Fin.castAdd δ.val i)
  simpa [liftV_apply_castAdd] using this

private lemma natAdd_ne_castAdd {t : ℕ} {δ : Fin 2} (j : Fin δ.val) (i : Fin t) :
    Fin.natAdd t j ≠ Fin.castAdd δ.val i := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

lemma mem_liftSupport_castAdd {t : ℕ} {δ : Fin 2} {S : Finset (Fin t)} {i : Fin t} :
    Fin.castAdd δ.val i ∈ liftSupport t δ S ↔ i ∈ S := by
  rw [liftSupport, Finset.mem_union, Finset.mem_map, Finset.mem_map]
  constructor
  · rintro (⟨j, hj, hji⟩ | ⟨j, -, hji⟩)
    · rw [show j = i from Fin.castAdd_injective t δ.val hji] at hj
      exact hj
    · exact absurd hji (natAdd_ne_castAdd j i)
  · intro hi
    exact Or.inl ⟨i, hi, rfl⟩

private lemma mem_liftSupport_natAdd {t : ℕ} {δ : Fin 2} {S : Finset (Fin t)}
    (j : Fin δ.val) : Fin.natAdd t j ∈ liftSupport t δ S := by
  rw [liftSupport]
  exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)

private lemma forall_map_liftV_castAdd {t : ℕ} {δ : Fin 2}
    (U : Submodule (ZMod 3) (PlaneRaw.V t)) (i : Fin t) :
    (∀ w : ↥(U.map (liftV t δ)), (w : PlaneRaw.V (t + δ.val)) (Fin.castAdd δ.val i) = 0) ↔
      ∀ u : ↥U, (u : PlaneRaw.V t) i = 0 := by
  constructor
  · intro h u
    have := h ⟨liftV t δ (u : PlaneRaw.V t), Submodule.mem_map_of_mem (f := liftV t δ) u.2⟩
    simpa [liftV_apply_castAdd] using this
  · rintro h ⟨w, hw⟩
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    simpa [liftV_apply_castAdd] using h ⟨u, hu⟩

private lemma forall_map_liftV_natAdd {t : ℕ} {δ : Fin 2}
    (U : Submodule (ZMod 3) (PlaneRaw.V t)) (j : Fin δ.val) :
    ∀ w : ↥(U.map (liftV t δ)), (w : PlaneRaw.V (t + δ.val)) (Fin.natAdd t j) = 0 := by
  rintro ⟨w, hw⟩
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
  simp [liftV_apply_natAdd]

private lemma evalRestr_map_liftV_natAdd {t : ℕ} {δ : Fin 2}
    (U : Submodule (ZMod 3) (PlaneRaw.V t)) (j : Fin δ.val) :
    PlaneRaw.evalRestr (U.map (liftV t δ)) (Fin.natAdd t j) = 0 := by
  ext w
  obtain ⟨v, hv⟩ := w
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
  simp [PlaneRaw.evalRestr, liftV_apply_natAdd]

theorem planeQ_add {K : Type} [Field K] [CharP K 2] (t : ℕ) (δ : Fin 2)
    (v w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) :
    planeQ t δ (v + w) = planeQ t δ v + planeQ t δ w +
      v ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ w) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hdot : v ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ w) =
      ∑ i, (v (Sum.inl i) * w (Sum.inr i) + v (Sum.inr i) * w (Sum.inl i)) := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) = spJ (t + δ.val) K from rfl]
    rw [dotProduct, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [spJ_mulVec_inl, spJ_mulVec_inr, mul_neg, CharTwo.neg_eq]
  simp only [planeQ, Pi.add_apply]
  rw [hdot, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < t
  · simp only [h, if_true]
    linear_combination (v (Sum.inl i) * w (Sum.inl i) +
      v (Sum.inr i) * w (Sum.inr i)) * h2
  · simp only [h, if_false]
    ring

theorem largeEvenOrthGroup_planeQ_le_statedSp {K : Type} [Field K] [CharP K 2] (t : ℕ)
    (δ : Fin 2) : LargeEvenOrthGroup (planeQ (K := K) t δ) ≤ StatedSp (t + δ.val) K := by
  intro A hA
  rw [ClassicalGroups.Symplectic.mem_statedSp_iff_forall]
  intro x y
  have hAv : ∀ v : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K,
      planeQ t δ ((A : Matrix _ _ K) *ᵥ v) = planeQ t δ v :=
    CFSG.PGLModel.mem_orthogonalGroup_iff.mp hA
  have hx : planeQ t δ ((A : Matrix _ _ K) *ᵥ x) = planeQ t δ x := hAv x
  have hy : planeQ t δ ((A : Matrix _ _ K) *ᵥ y) = planeQ t δ y := hAv y
  have hxy : planeQ t δ ((A : Matrix _ _ K) *ᵥ (x + y)) = planeQ t δ (x + y) := hAv (x + y)
  have h1 := planeQ_add t δ ((A : Matrix _ _ K) *ᵥ x) ((A : Matrix _ _ K) *ᵥ y)
  have h2 := planeQ_add t δ x y
  have hEq : planeQ t δ x + planeQ t δ y +
      x ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ y) =
      planeQ t δ x + planeQ t δ y +
      ((A : Matrix _ _ K) *ᵥ x) ⬝ᵥ ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *ᵥ ((A : Matrix _ _ K) *ᵥ y)) := by
    rw [← h2, ← hxy, Matrix.mulVec_add, h1, hx, hy]
  rw [ClassicalGroups.Symplectic.spForm_apply, ClassicalGroups.Symplectic.spForm_apply]
  exact add_left_cancel (a := planeQ t δ x + planeQ t δ y) hEq.symm

theorem omegaQ_le_statedSp {K : Type} [Field K] [CharP K 2] (t : ℕ) (δ : Fin 2) :
    omegaQ (K := K) t δ ≤ StatedSp (t + δ.val) K := by
  intro A hA
  change A ∈ LargeEvenOmega (planeQ (K := K) t δ) at hA
  rw [largeEvenOmega_def] at hA
  exact largeEvenOrthGroup_planeQ_le_statedSp t δ
    (Subgroup.commutator_le_of_le le_rfl le_rfl hA)

theorem orthOccursLiftIff_holds :
    ∀ (t : ℕ) (δ : Fin 2) (U : Submodule (ZMod 3) (PlaneRaw.V t)) (c : PlaneRaw.Code t),
      PlaneRaw.occurs U c ↔ PlaneRaw.occurs (U.map (liftV t δ)) (liftCode t δ c) := by
  intro t δ U c
  cases c with
  | zero S =>
    constructor
    · intro hS j
      induction j using Fin.addCases with
      | left i =>
        rw [mem_liftSupport_castAdd, hS i, forall_map_liftV_castAdd]
      | right k =>
        exact iff_of_true (mem_liftSupport_natAdd k) (forall_map_liftV_natAdd U k)
    · intro hS i
      rw [← mem_liftSupport_castAdd (S := S) (i := i), hS (Fin.castAdd δ.val i),
        forall_map_liftV_castAdd]
  | extension e =>
    constructor
    · intro hE
      obtain ⟨he, χ, hχ, hsupp, hzero⟩ := hE
      let φ := Submodule.equivMapOfInjective (liftV t δ) (liftV_injective t δ) U
      let χ' : ↥(U.map (liftV t δ)) →ₗ[ZMod 3] ZMod 3 := χ.comp φ.symm.toLinearMap
      have hφ : ∀ u : ↥U,
          ((φ u : ↥(U.map (liftV t δ))) : PlaneRaw.V (t + δ.val)) = liftV t δ (u : PlaneRaw.V t) :=
        fun u => Submodule.coe_equivMapOfInjective_apply (liftV t δ) (liftV_injective t δ) U u
      have hχ'apply : ∀ u : ↥U, χ' (φ u) = χ u := by
        intro u
        simp [χ']
      have hχ' : χ' ≠ 0 := by
        intro h0
        apply hχ
        ext u
        have := LinearMap.congr_fun h0 (φ u)
        simpa [hχ'apply] using this
      have hne : liftV t δ e ≠ 0 := by
        intro h0
        apply he
        funext i
        have := congrFun h0 (Fin.castAdd δ.val i)
        simpa [liftV_apply_castAdd] using this
      have hsupp' : ∀ j : Fin (t + δ.val), (liftV t δ e) j ≠ 0 →
          PlaneRaw.evalRestr (U.map (liftV t δ)) j = (liftV t δ e) j • χ' := by
        intro j
        induction j using Fin.addCases with
        | left i =>
          intro hj
          have hi : e i ≠ 0 := by
            rwa [liftV_apply_castAdd] at hj
          refine LinearMap.ext fun w => ?_
          obtain ⟨u, rfl⟩ := φ.surjective w
          change ((φ u : ↥(U.map (liftV t δ))) : PlaneRaw.V (t + δ.val))
            (Fin.castAdd δ.val i) = _
          rw [hφ u, liftV_apply_castAdd, liftV_apply_castAdd, LinearMap.smul_apply,
            smul_eq_mul, hχ'apply u]
          have hsu := LinearMap.congr_fun (hsupp i hi) u
          simpa [PlaneRaw.evalRestr, smul_eq_mul] using hsu
        | right k =>
          intro hj
          rw [liftV_apply_natAdd] at hj
          exact absurd rfl hj
      have hzero' : ∀ j : Fin (t + δ.val), (liftV t δ e) j = 0 →
          PlaneRaw.evalRestr (U.map (liftV t δ)) j ≠ χ' ∧
            PlaneRaw.evalRestr (U.map (liftV t δ)) j ≠ -χ' := by
        intro j
        induction j using Fin.addCases with
        | left i =>
          intro hi
          have hi' : e i = 0 := by
            simpa [liftV_apply_castAdd] using hi
          have hz := hzero i hi'
          constructor
          · intro heq
            apply hz.1
            ext u
            have h := LinearMap.congr_fun heq (φ u)
            change ((φ u : ↥(U.map (liftV t δ))) : PlaneRaw.V (t + δ.val))
              (Fin.castAdd δ.val i) = χ' (φ u) at h
            rw [hφ u, liftV_apply_castAdd, hχ'apply u] at h
            exact h
          · intro heq
            apply hz.2
            ext u
            have h := LinearMap.congr_fun heq (φ u)
            change ((φ u : ↥(U.map (liftV t δ))) : PlaneRaw.V (t + δ.val))
              (Fin.castAdd δ.val i) = (-χ') (φ u) at h
            rw [hφ u, liftV_apply_castAdd] at h
            simpa [PlaneRaw.evalRestr, hχ'apply] using h
        | right k =>
          intro _
          rw [evalRestr_map_liftV_natAdd]
          exact ⟨Ne.symm hχ', Ne.symm (neg_ne_zero.mpr hχ')⟩
      exact ⟨hne, χ', hχ', hsupp', hzero'⟩
    · intro hE
      obtain ⟨he', χ', hχ', hsupp', hzero'⟩ := hE
      let φ := Submodule.equivMapOfInjective (liftV t δ) (liftV_injective t δ) U
      let χ : ↥U →ₗ[ZMod 3] ZMod 3 := χ'.comp φ.toLinearMap
      have hφ : ∀ u : ↥U,
          ((φ u : ↥(U.map (liftV t δ))) : PlaneRaw.V (t + δ.val)) = liftV t δ (u : PlaneRaw.V t) :=
        fun u => Submodule.coe_equivMapOfInjective_apply (liftV t δ) (liftV_injective t δ) U u
      have hχapply : ∀ u : ↥U, χ u = χ' (φ u) := by
        intro u
        rfl
      have hne : e ≠ 0 := by
        intro h0
        apply he'
        funext j
        induction j using Fin.addCases with
        | left i =>
          have := congrFun h0 i
          simpa [liftV_apply_castAdd] using this
        | right k =>
          rw [liftV_apply_natAdd]
          rfl
      have hχ : χ ≠ 0 := by
        intro h0
        apply hχ'
        ext w
        obtain ⟨u, rfl⟩ := φ.surjective w
        have := LinearMap.congr_fun h0 u
        simpa [hχapply] using this
      have hsupp : ∀ i : Fin t, e i ≠ 0 → PlaneRaw.evalRestr U i = e i • χ := by
        intro i hi
        have hi' : (liftV t δ e) (Fin.castAdd δ.val i) ≠ 0 := by
          rwa [liftV_apply_castAdd]
        refine LinearMap.ext fun u => ?_
        have hsu := LinearMap.congr_fun (hsupp' (Fin.castAdd δ.val i) hi') (φ u)
        change ((φ u : ↥(U.map (liftV t δ))) : PlaneRaw.V (t + δ.val))
          (Fin.castAdd δ.val i) = ((liftV t δ e) (Fin.castAdd δ.val i) • χ') (φ u) at hsu
        rw [hφ u, liftV_apply_castAdd, liftV_apply_castAdd, LinearMap.smul_apply,
          smul_eq_mul] at hsu
        change (u : PlaneRaw.V t) i = (e i • χ) u
        rw [LinearMap.smul_apply, smul_eq_mul, hχapply u]
        exact hsu
      have hzero : ∀ j : Fin t, e j = 0 → PlaneRaw.evalRestr U j ≠ χ ∧
          PlaneRaw.evalRestr U j ≠ -χ := by
        intro i hi
        have hi' : (liftV t δ e) (Fin.castAdd δ.val i) = 0 := by
          rwa [liftV_apply_castAdd]
        have hz := hzero' (Fin.castAdd δ.val i) hi'
        constructor
        · intro heq
          apply hz.1
          ext w
          obtain ⟨u, rfl⟩ := φ.surjective w
          have h := LinearMap.congr_fun heq u
          change ((φ u : ↥(U.map (liftV t δ))) : PlaneRaw.V (t + δ.val))
            (Fin.castAdd δ.val i) = χ' (φ u)
          rw [hφ u, liftV_apply_castAdd]
          exact h.trans (hχapply u)
        · intro heq
          apply hz.2
          ext w
          obtain ⟨u, rfl⟩ := φ.surjective w
          have h := LinearMap.congr_fun heq u
          change ((φ u : ↥(U.map (liftV t δ))) : PlaneRaw.V (t + δ.val))
            (Fin.castAdd δ.val i) = (-χ') (φ u)
          rw [hφ u, liftV_apply_castAdd]
          simpa [PlaneRaw.evalRestr, hχapply] using h
      exact ⟨hne, χ, hχ, hsupp, hzero⟩

theorem orthExistsLift_holds :
    ∀ (t : ℕ) (δ : Fin 2) (U : Submodule (ZMod 3) (PlaneRaw.V t)) (c : PlaneRaw.Code (t + δ.val)),
      PlaneRaw.occurs (U.map (liftV t δ)) c → ∃ c₀ : PlaneRaw.Code t, c = liftCode t δ c₀ := by
  intro t δ U c hE
  cases c with
  | zero S =>
    let S₀ : Finset (Fin t) := Finset.univ.filter fun i => Fin.castAdd δ.val i ∈ S
    have hmem : ∀ i : Fin t, i ∈ S₀ ↔ Fin.castAdd δ.val i ∈ S := by
      intro i
      simp [S₀]
    have hsupp : liftSupport t δ S₀ = S := by
      ext j
      induction j using Fin.addCases with
      | left i => rw [mem_liftSupport_castAdd, hmem i]
      | right k =>
        have hk : Fin.natAdd t k ∈ S :=
          (hE (Fin.natAdd t k)).2 (forall_map_liftV_natAdd U k)
        exact iff_of_true (mem_liftSupport_natAdd k) hk
    exact ⟨.zero S₀, by rw [liftCode, hsupp]⟩
  | extension e =>
    obtain ⟨he, χ, hχ, hsupp, hzero⟩ := hE
    have hnat : ∀ k : Fin δ.val, e (Fin.natAdd t k) = 0 := by
      intro k
      by_contra hk
      have h := hsupp (Fin.natAdd t k) hk
      rw [evalRestr_map_liftV_natAdd] at h
      exact hk ((smul_eq_zero.mp h.symm).resolve_right hχ)
    let e₀ : PlaneRaw.V t := fun i => e (Fin.castAdd δ.val i)
    have heq : e = liftV t δ e₀ := by
      funext j
      induction j using Fin.addCases with
      | left i => rw [liftV_apply_castAdd]
      | right k => rw [liftV_apply_natAdd, hnat k]
    exact ⟨.extension e₀, by rw [liftCode, heq]⟩

theorem orthGlBlockCentralizerPlaneIdem_holds :
    ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
      (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
      Nat.card K = 2 → Function.Injective ζ →
      ∀ (U : Submodule (ZMod 3) (PlaneRaw.V t)) (c : PlaneRaw.Code t), PlaneRaw.occurs U c →
        (liftCode t δ c).support.Nonempty →
        glBlockCentralizer (omegaQ (K := K) t δ).subtype (oTorusSet ζ t δ U)
            (SpBlocks.planeIdem (t + δ.val) (liftCode t δ c).support) =
          oBlockGroup ζ t δ c := by
  intro K _ _ _ ζ t δ hK hζ U c hc hne
  have hocc : PlaneRaw.occurs (U.map (liftV t δ)) (liftCode t δ c) :=
    (orthOccursLiftIff_holds t δ U c).mp hc
  have hsp := SpBlocks.spGlBlockCentralizerPlaneIdem_holds ζ (t + δ.val) hK hζ
    (U.map (liftV t δ)) (liftCode t δ c) hocc hne
  change (Subgroup.centralizer (SpBlocks.torusSet ζ (t + δ.val) (U.map (liftV t δ))) ⊓
      glFixing (1 - SpBlocks.planeIdem (t + δ.val) (liftCode t δ c).support)).comap
        (omegaQ (K := K) t δ).subtype =
    ((SpBlocks.blockGroup ζ (t + δ.val) (liftCode t δ c)).map
      (StatedSp (t + δ.val) K).subtype).comap (omegaQ (K := K) t δ).subtype
  rw [← hsp]
  rw [show glBlockCentralizer (StatedSp (t + δ.val) K).subtype
      (SpBlocks.torusSet ζ (t + δ.val) (U.map (liftV t δ)))
      (SpBlocks.planeIdem (t + δ.val) (liftCode t δ c).support) =
      (Subgroup.centralizer (SpBlocks.torusSet ζ (t + δ.val) (U.map (liftV t δ))) ⊓
        glFixing (1 - SpBlocks.planeIdem (t + δ.val) (liftCode t δ c).support)).comap
          (StatedSp (t + δ.val) K).subtype from rfl]
  rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
  have htop : (StatedSp (t + δ.val) K).comap (omegaQ (K := K) t δ).subtype = ⊤ := by
    rw [eq_top_iff]
    intro g _
    exact omegaQ_le_statedSp t δ g.2
  conv_rhs => rw [Subgroup.comap_inf, htop, top_inf_eq]

theorem orthYcodeLeCentralizer_holds :
    ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
      (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
      Nat.card K = 2 → Function.Injective ζ →
      ∀ (U : Submodule (ZMod 3) (PlaneRaw.V t)) (c : PlaneRaw.Code t), PlaneRaw.occurs U c →
        (liftCode t δ c).support.Nonempty →
        oYcode ζ t δ c ≤
          (Subgroup.centralizer (oTorusSet ζ t δ U)).comap (omegaQ (K := K) t δ).subtype := by
  intro K _ _ _ ζ t δ hK hζ U c hc hne
  change ⁅oBlockGroup ζ t δ c, oBlockGroup ζ t δ c⁆ ≤ _
  rw [← orthGlBlockCentralizerPlaneIdem_holds ζ t δ hK hζ U c hc hne]
  exact (Subgroup.commutator_le_of_le le_rfl le_rfl).trans (Subgroup.comap_mono inf_le_left)

theorem orthNormalYcode_holds :
    ∀ {K : Type} [Field K] [Finite K] [CharP K 2]
      (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (δ : Fin 2),
      Nat.card K = 2 → Function.Injective ζ →
      ∀ (U : Submodule (ZMod 3) (PlaneRaw.V t)) (c : PlaneRaw.Code t), PlaneRaw.occurs U c →
        (liftCode t δ c).support.Nonempty →
        ((oYcode ζ t δ c).subgroupOf
          ((Subgroup.centralizer (oTorusSet ζ t δ U)).comap (omegaQ (K := K) t δ).subtype)).Normal := by
  intro K _ _ _ ζ t δ hK hζ U c hc hne
  have hle := orthYcodeLeCentralizer_holds ζ t δ hK hζ U c hc hne
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h k hh hk
  have hocc : PlaneRaw.occurs (U.map (liftV t δ)) (liftCode t δ c) :=
    (orthOccursLiftIff_holds t δ U c).mp hc
  have hleSp : omegaQ (K := K) t δ ≤ StatedSp (t + δ.val) K :=
    omegaQ_le_statedSp t δ
  have hkSp : (⟨(k : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K), hleSp k.2⟩ :
      ↥(StatedSp (t + δ.val) K)) ∈
      (Subgroup.centralizer (SpBlocks.torusSet ζ (t + δ.val) (U.map (liftV t δ)))).comap
        (StatedSp (t + δ.val) K).subtype := hk
  have hBsp := SpBlocks.map_conj_blockGroup_le (ζ := ζ) hK hζ (U.map (liftV t δ))
    (c := liftCode t δ c) hocc hne hkSp
  have hB : (oBlockGroup ζ t δ c).map (MulAut.conj k).toMonoidHom ≤ oBlockGroup ζ t δ c := by
    rintro _ ⟨b, hb, rfl⟩
    have hbSp : (⟨(b : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K), hleSp b.2⟩ :
        ↥(StatedSp (t + δ.val) K)) ∈
        SpBlocks.blockGroup ζ (t + δ.val) (liftCode t δ c) := by
      have hbmap : (b : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈
          (SpBlocks.blockGroup ζ (t + δ.val) (liftCode t δ c)).map
            (StatedSp (t + δ.val) K).subtype := hb
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp hbmap
      have hy' : y = (⟨(b : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K), hleSp b.2⟩ :
          ↥(StatedSp (t + δ.val) K)) := Subtype.ext hyb
      rwa [← hy']
    have hconjSp := hBsp ⟨⟨(b : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K), hleSp b.2⟩,
      hbSp, rfl⟩
    have hcoe : (((MulAut.conj (⟨(k : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K), hleSp k.2⟩ :
        ↥(StatedSp (t + δ.val) K))) (⟨(b : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K),
          hleSp b.2⟩ : ↥(StatedSp (t + δ.val) K))) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        (((MulAut.conj k) b : ↥(omegaQ (K := K) t δ)) :
          GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := by
      simp [MulAut.conj_apply, Subgroup.coe_mul]
    rw [oBlockGroup, Subgroup.mem_comap, Subgroup.mem_map]
    exact ⟨_, hconjSp, hcoe⟩
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hh
  rw [oYcode, Subgroup.map_commutator] at hmem
  have hmem' := Subgroup.commutator_mono hB hB hmem
  rw [oYcode]
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem'

end CFSG.StandardType.GGQ2Frame.OrthBlocks
