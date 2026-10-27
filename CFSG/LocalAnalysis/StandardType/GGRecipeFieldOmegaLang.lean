module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaDescent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.GroupTheory.WeirSylow QuadraticMap
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField

namespace RecipeFieldOmega

section Lang

variable {K : Type} [Field K] {d : ℕ}

@[expose] def IsIsoPair (Q : QuadraticForm K (Fin d → K)) (g : coordinateSemilinearGroup d K) :
    Prop :=
  ∀ v, Q (coordinateSemilinearMap g v) = g.right (Q v)

theorem coordinateSemilinearMap_iterate (g : coordinateSemilinearGroup d K) (k : ℕ)
    (v : Fin d → K) : (coordinateSemilinearMap g)^[k] v = coordinateSemilinearMap (g ^ k) v := by
  induction k generalizing v with
  | zero => rw [Function.iterate_zero_apply, pow_zero, coordinateSemilinearMap_one]
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ', coordinateSemilinearMap_mul]

theorem right_pow (g : coordinateSemilinearGroup d K) (k : ℕ) : (g ^ k).right = g.right ^ k :=
  map_pow (SemidirectProduct.rightHom (φ := glFieldAut (Fin d) K)) g k

theorem exists_moved [Finite K] {σ : K ≃+* K} {p : ℕ} (hσ : orderOf σ = p) :
    ∃ θ : K, ∀ i, 0 < i → i < p → (σ ^ i) θ ≠ θ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨g, fun i hi0 hip heq => ?_⟩
  have hfixu : ∀ x : Kˣ, (σ ^ i) (x : K) = x := by
    intro x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, heq]
  have h1 : σ ^ i = 1 := by
    ext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact hfixu (Units.mk0 x hx)
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hσ] at hdvd
  exact absurd (Nat.le_of_dvd hi0 hdvd) (by omega)

theorem exists_fixed_basis_pair [Finite K] {σ : K ≃+* K} {p : ℕ} (hp : p.Prime)
    (hσ : orderOf σ = p) {X : coordinateSemilinearGroup d K} (hXr : X.right = σ)
    (hXp : X ^ p = 1) : ∃ H : GL (Fin d) K, X.left * glFieldAut (Fin d) K σ H = H := by
  let T : (Fin d → K) →+ (Fin d → K) := (coordinateSemilinearMap X).toAddMonoidHom
  have hsmul : ∀ (a : K) (v : Fin d → K), T (a • v) = σ a • T v := fun a v => by
    change coordinateSemilinearMap X (a • v) = σ a • coordinateSemilinearMap X v
    rw [coordinateSemilinearMap_smul, hXr]
  have hTp : ∀ v, T^[p] v = v := fun v => by
    change (coordinateSemilinearMap X)^[p] v = v
    rw [coordinateSemilinearMap_iterate, hXp, coordinateSemilinearMap_one]
  obtain ⟨θ, hθ⟩ := exists_moved hσ
  obtain ⟨H, hH⟩ := RecipeFieldLang.exists_fixed_basis_of_span T
    (RecipeFieldLang.span_fixed_eq_top T hsmul hp.pos hTp hθ)
  refine ⟨H, ?_⟩
  ext r c
  have h := congrFun (hH c) r
  change coordinateSemilinearMap X (fun r => (H : Matrix (Fin d) (Fin d) K) r c) r = _ at h
  rw [coordinateSemilinearMap_apply, hXr] at h
  simp only [Matrix.mulVec, dotProduct] at h
  rw [← h]
  simp [Matrix.mul_apply, glFieldAut_apply_val]

theorem mem_fixed_of_isIsoPair {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K}
    {X : coordinateSemilinearGroup d K} (hX : IsIsoPair Q X) (hXr : X.right = σ)
    {K₀ : Subfield K} (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) {H : GL (Fin d) K}
    (hH : X.left * glFieldAut (Fin d) K σ H = H) (w : Fin d → K₀) :
    Q.comp (Matrix.toLin' H.val) (inclVec K₀ w) ∈ K₀ := by
  rw [hK₀, QuadraticMap.comp_apply, Matrix.toLin'_apply, ← hXr, ← hX, coordinateSemilinearMap_apply]
  congr 1
  have h1 : (fun i => X.right ((H.val.mulVec (inclVec K₀ w)) i)) =
      (glFieldAut (Fin d) K σ H).val.mulVec (inclVec K₀ w) := by
    funext i
    have h2 := RingHom.map_mulVec (σ : K →+* K) H.val (inclVec K₀ w) i
    have h3 : (σ : K →+* K) ∘ inclVec K₀ w = inclVec K₀ w := by
      funext j
      exact (hK₀ _).1 (w j).2
    rw [h3] at h2
    rw [hXr]
    exact h2
  rw [h1, Matrix.mulVec_mulVec, ← Units.val_mul, hH]

theorem nondegenerate_comp_GL {Q : QuadraticForm K (Fin d → K)} (hnd : (polarBilin Q).Nondegenerate)
    (H : GL (Fin d) K) : (polarBilin (Q.comp (Matrix.toLin' H.val))).Nondegenerate := by
  have hHH : ∀ z : Fin d → K, H.val.mulVec ((H⁻¹ : GL (Fin d) K).val.mulVec z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hinj : ∀ x : Fin d → K, H.val.mulVec x = 0 → x = 0 := fun x hx => by
    have := congrArg ((H⁻¹ : GL (Fin d) K).val.mulVec) hx
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
  have key : ∀ x : Fin d → K,
      (∀ y, polar (Q.comp (Matrix.toLin' H.val)) x y = 0) → x = 0 := by
    intro x hx
    refine hinj x (hnd.1 _ fun z => ?_)
    rw [polarBilin_apply_apply, ← hHH z]
    have := hx ((H⁻¹ : GL (Fin d) K).val.mulVec z)
    simpa [polar, Matrix.toLin'_apply, Matrix.mulVec_add] using this
  refine ⟨fun x hx => key x fun y => ?_, fun y hy => key y fun x => ?_⟩
  · rw [← polarBilin_apply_apply]
    exact hx y
  · rw [polar_comm, ← polarBilin_apply_apply]
    exact hy x

theorem exists_isometry_conj_of_isIsoPair [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hnd : (polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {S T : coordinateSemilinearGroup (2 * n) K}
    (hS : IsIsoPair Q S) (hT : IsIsoPair Q T) (hST : T.right = S.right)
    (hσ : orderOf S.right = p) (hSp : S ^ p = 1) (hTp : T ^ p = 1) :
    ∃ h : GL (Fin (2 * n)) K, h ∈ matrixIsometries Q ∧
      h * T.left = S.left * glFieldAut (Fin (2 * n)) K S.right h := by
  set σ := S.right with hσdef
  set K₀ : Subfield K := (σ : K →+* K).eqLocusField (RingHom.id K)
  have hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x := fun x => Iff.rfl
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨HS, hHS⟩ := exists_fixed_basis_pair hp hσ rfl hSp
  obtain ⟨HT, hHT⟩ := exists_fixed_basis_pair hp hσ hST hTp
  have hQS := mem_fixed_of_isIsoPair hS rfl hK₀ hHS
  have hQT := mem_fixed_of_isIsoPair hT hST hK₀ hHT
  have hndS := nondegenerate_comp_GL hnd HS
  have hndT := nondegenerate_comp_GL hnd HT
  have eS : (Q.comp (Matrix.toLin' HS.val)).IsometryEquiv Q := ⟨matrixLinearEquiv HS, fun _ => rfl⟩
  have eT : (Q.comp (Matrix.toLin' HT.val)).IsometryEquiv Q := ⟨matrixLinearEquiv HT, fun _ => rfl⟩
  have hiff : IsPlusType (descForm _ hQT) ↔ IsPlusType (descForm _ hQS) := by
    rw [isPlusType_descForm_iff hpodd hσp hK₀ hn hQT hndT,
      isPlusType_descForm_iff hpodd hσp hK₀ hn hQS hndS, isPlusType_congr eS, isPlusType_congr eT]
  obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff (nondegenerate_descForm hQT hndT)
    (nondegenerate_descForm hQS hndS) (Module.finrank_fin_fun K₀) (Module.finrank_fin_fun K₀) hiff
  set M : GL (Fin (2 * n)) K₀ := matrixLinearIso.symm e.toLinearEquiv
  have hMw : ∀ w, M.val.mulVec w = e w := fun w => by
    change matrixLinearIso M w = e w
    rw [MulEquiv.apply_symm_apply]
    rfl
  set MK : GL (Fin (2 * n)) K := Matrix.GeneralLinearGroup.map K₀.subtype M
  have hMKw : ∀ w, MK.val.mulVec (inclVec K₀ w) = inclVec K₀ (e w) := fun w => by
    funext i
    have h1 := RingHom.map_mulVec K₀.subtype M.val w i
    rw [hMw] at h1
    exact h1.symm
  have hσM : glFieldAut (Fin (2 * n)) K σ MK = MK := by
    ext i j
    exact (hK₀ _).1 (M i j).2
  have hiso : (Q.comp (Matrix.toLin' HS.val)).comp (Matrix.toLin' MK.val) =
      Q.comp (Matrix.toLin' HT.val) := eq_of_forall_inclVec K₀ fun w => by
    rw [QuadraticMap.comp_apply, Matrix.toLin'_apply, hMKw, ← descForm_apply _ hQS, e.map_app,
      descForm_apply]
  refine ⟨HS * MK * HT⁻¹, ?_, ?_⟩
  · rw [mem_matrixIsometries_iff]
    intro v
    have h := congrArg (fun q : QuadraticForm K (Fin (2 * n) → K) =>
      q ((HT⁻¹ : GL (Fin (2 * n)) K).val.mulVec v)) hiso
    simp only [QuadraticMap.comp_apply, Matrix.toLin'_apply] at h
    rw [matrixLinearEquiv_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  · have eTl : T.left = HT * (glFieldAut (Fin (2 * n)) K σ HT)⁻¹ := eq_mul_inv_of_mul_eq hHT
    have eSl : S.left = HS * (glFieldAut (Fin (2 * n)) K σ HS)⁻¹ := eq_mul_inv_of_mul_eq hHS
    rw [eTl, eSl, map_mul, map_mul, map_inv, hσM]
    group

end Lang

end RecipeFieldOmega

end CFSG.StandardType
