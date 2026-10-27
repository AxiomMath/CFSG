module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import CFSG.LocalAnalysis.StandardType.GGFrameCartanData
public import CFSG.LocalAnalysis.StandardType.GGFrameE78Facts
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoin
public import CFSG.LocalAnalysis.StandardType.GGQ2LDatumOfWeyl

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly CFSG.Open

theorem feS_mulVec_apply (n : ℕ) (i : Fin n) (y : FEVec n) (k : Fin n) :
    ((feS n i).mulVec y) k = y k - ((CartanMatrix.E n k i : ℤ) : ZMod 3) * y i := by
  simp [feS, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul]


private theorem exists_frameModelV {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs)
    {n : ℕ} {M : CoxeterMatrix (Fin n)} (hC : GGIntCartan M (CartanMatrix.E n))
    (hent : ∀ i j, i ≠ j → CartanMatrix.E n i j = 0 ∨ CartanMatrix.E n i j = -1 ∨
      CartanMatrix.E n i j = -2)
    (hT : SecFiveRootRefl.CartanTree (CartanMatrix.E n))
    {A : Subgroup (MulAut ↥Bs)} (hA : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs)
    (e : M.Group ≃* ↥A) (he : ∀ i, GGIsReflection 3 ((e (M.simple i) : ↥A) : MulAut ↥Bs))
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ A, φ b = b) → b = 1) (hcard : Nat.card ↥Bs = 3 ^ n) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (ιV : Additive ↥Bs ≃+ V)
      (Ψ : V ≃ₗ[ZMod 3] FEVec n), ∀ (i : Fin n) (b : ↥Bs),
      Ψ (ιV (Additive.ofMul ((e (M.simple i) : MulAut ↥Bs) b))) =
        (feS n i).mulVec (Ψ (ιV (Additive.ofMul b))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, iadd, imod, ⟨ιV⟩⟩ := exists_ggLinData (p := 3) hBs
  letI : AddCommGroup V := iadd
  letI : Module (ZMod 3) V := imod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hVcard : Nat.card V = 3 ^ n := by rw [← card_eq_of_ggLin ιV, hcard]
  have hdim : Module.finrank (ZMod 3) V = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V)
    rw [Nat.card_zmod, hVcard] at h
    exact (Nat.pow_right_injective (Nat.prime_three.two_le) h).symm
  obtain ⟨h, α, hα, hrefl, hpair⟩ :=
    SecFiveRootRefl.exists_cartan_pairing_of_iso (p := 3) (by norm_num) hNT hC hent hT e he hA ιV
  let simple : Fin n → MulAut ↥Bs := fun i => ((e (M.simple i) : ↥A) : MulAut ↥Bs)
  have hsimple_apply : ∀ i w, ggLin (p := 3) ιV (simple i) w = w - α i w • h i :=
    fun i w => by rw [hrefl i]; exact Module.reflection_apply w (hα i)
  have hmap : ((Subgroup.subtype A).comp e.toMonoidHom) '' Set.range M.simple =
      Set.range simple := by
    ext x
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨M.simple i, ⟨i, rfl⟩, rfl⟩
  have hfr : ((Subgroup.subtype A).comp e.toMonoidHom).range = A := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact (e m).2
    · intro hx
      obtain ⟨m, hm⟩ := e.surjective ⟨x, hx⟩
      exact ⟨m, congrArg Subtype.val hm⟩
  have hsimple_eq : (M.toCoxeterSystem).simple = M.simple := by
    funext i
    rw [CoxeterMatrix.toCoxeterSystem_simple]
  have hsimple_range : Set.range M.simple = Set.range (M.toCoxeterSystem).simple := by
    rw [hsimple_eq]
  have hAclos : A = Subgroup.closure (Set.range simple) := by
    have hc : Subgroup.closure (Set.range simple) = A := by
      rw [← hmap, ← MonoidHom.map_closure, hsimple_range,
        (M.toCoxeterSystem).subgroup_closure_range_simple, Subgroup.map_top, hfr]
    exact hc.symm
  have hinj : Function.Injective (LinearMap.pi α) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : ∀ i, α i v = 0 := fun i => congrFun hv i
    have hsfix : ∀ φ ∈ A, ggLin (p := 3) ιV φ v = v := by
      intro φ hφ
      rw [hAclos] at hφ
      induction hφ using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [hsimple_apply, hv' i, zero_smul, sub_zero]
      | one => simp
      | mul x y _ _ hx hy =>
        rw [map_mul]
        change ggLin (p := 3) ιV x (ggLin (p := 3) ιV y v) = v
        rw [hy, hx]
      | inv x _ hx =>
        rw [map_inv]
        exact (LinearEquiv.symm_apply_eq _).2 hx.symm
    set b : ↥Bs := Additive.toMul (ιV.symm v) with hb
    have hvb : v = ιV (Additive.ofMul b) := by simp [hb]
    have hbfix : ∀ φ ∈ A, φ b = b := by
      intro φ hφ
      have h1 := hsfix φ hφ
      rw [hvb, ggLin_apply_ofMul] at h1
      exact Additive.ofMul.injective (ιV.injective h1)
    have hb1 : b = 1 := hfix b hbfix
    rw [hvb, hb1]
    simp
  have hsurj : Function.Surjective (LinearMap.pi α) := by
    have hfd : Module.finrank (ZMod 3) V = Module.finrank (ZMod 3) (Fin n → ZMod 3) := by
      rw [hdim, Module.finrank_fin_fun]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfd).1 hinj
  let Ψ : V ≃ₗ[ZMod 3] (Fin n → ZMod 3) := LinearEquiv.ofBijective (LinearMap.pi α) ⟨hinj, hsurj⟩
  refine ⟨V, iadd, imod, ιV, Ψ, fun i b => ?_⟩
  change Ψ (ιV (Additive.ofMul ((simple i) b))) = (feS n i).mulVec (Ψ (ιV (Additive.ofMul b)))
  rw [← ggLin_apply_ofMul (p := 3) ιV (simple i) b, hsimple_apply]
  funext k
  rw [feS_mulVec_apply]
  change α k (ιV (Additive.ofMul b) - α i (ιV (Additive.ofMul b)) • h i) =
    α k (ιV (Additive.ofMul b)) - ((CartanMatrix.E n k i : ℤ) : ZMod 3) *
      α i (ιV (Additive.ofMul b))
  rw [map_sub, map_smul, hpair k i, smul_eq_mul]
  ring



section Transport

variable {G : Type} [Group G] {Bs : Subgroup G} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (ZMod 3) V]

private noncomputable def frameMat (ιV : Additive ↥Bs ≃+ V) (Ψ : V ≃ₗ[ZMod 3] FEVec n) (φ : MulAut ↥Bs) :
    FEMat n :=
  LinearMap.toMatrix' ((Ψ : V →ₗ[ZMod 3] FEVec n) ∘ₗ
    ((ggLin (p := 3) ιV φ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) ∘ₗ
    (Ψ.symm : FEVec n →ₗ[ZMod 3] V))

private theorem frameMat_mulVec (ιV : Additive ↥Bs ≃+ V) (Ψ : V ≃ₗ[ZMod 3] FEVec n) (φ : MulAut ↥Bs)
    (b : ↥Bs) :
    (frameMat ιV Ψ φ).mulVec (Ψ (ιV (Additive.ofMul b))) = Ψ (ιV (Additive.ofMul (φ b))) := by
  rw [frameMat, LinearMap.toMatrix'_mulVec]
  simp [ggLin_apply_ofMul]

private theorem frameMat_mul (ιV : Additive ↥Bs ≃+ V) (Ψ : V ≃ₗ[ZMod 3] FEVec n) (φ χ : MulAut ↥Bs) :
    frameMat ιV Ψ (φ * χ) = frameMat ιV Ψ φ * frameMat ιV Ψ χ := by
  unfold frameMat
  rw [← LinearMap.toMatrix'_comp]
  congr 1
  apply LinearMap.ext
  intro y
  simp [map_mul]

private theorem frameMat_injective (ιV : Additive ↥Bs ≃+ V) (Ψ : V ≃ₗ[ZMod 3] FEVec n) :
    Function.Injective (frameMat ιV Ψ) := by
  intro φ χ h
  refine MulEquiv.ext fun b => ?_
  have h1 := frameMat_mulVec ιV Ψ φ b
  rw [h, frameMat_mulVec] at h1
  exact Additive.ofMul.injective (ιV.injective (Ψ.injective h1.symm))

private theorem frameMat_one (ιV : Additive ↥Bs ≃+ V) (Ψ : V ≃ₗ[ZMod 3] FEVec n) :
    frameMat ιV Ψ 1 = 1 := by
  unfold frameMat
  simp [map_one]

end Transport


private theorem frame_simple_inv {n : ℕ} (M : CoxeterMatrix (Fin n)) (j : Fin n) :
    (M.simple j)⁻¹ = M.simple j := by
  have hs : (M.toCoxeterSystem).simple = M.simple := by
    funext j
    rw [CoxeterMatrix.toCoxeterSystem_simple]
  have h := (M.toCoxeterSystem).simple_mul_simple_self j
  rw [hs] at h
  exact inv_eq_of_mul_eq_one_right h

private theorem frame_closure_simple {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    Subgroup.closure (Set.range M.simple) = ⊤ := by
  have hs : (M.toCoxeterSystem).simple = M.simple := by
    funext j
    rw [CoxeterMatrix.toCoxeterSystem_simple]
  have h := (M.toCoxeterSystem).subgroup_closure_range_simple
  rwa [hs] at h

theorem exists_frameModel {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs)
    {n : ℕ} {M : CoxeterMatrix (Fin n)} (hC : GGIntCartan M (CartanMatrix.E n))
    (hent : ∀ i j, i ≠ j → CartanMatrix.E n i j = 0 ∨ CartanMatrix.E n i j = -1 ∨
      CartanMatrix.E n i j = -2)
    (hT : SecFiveRootRefl.CartanTree (CartanMatrix.E n))
    {A : Subgroup (MulAut ↥Bs)} (hA : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs)
    (e : M.Group ≃* ↥A) (he : ∀ i, GGIsReflection 3 ((e (M.simple i) : ↥A) : MulAut ↥Bs))
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ A, φ b = b) → b = 1) (hcard : Nat.card ↥Bs = 3 ^ n) :
    ∃ (ψ : Additive ↥Bs ≃+ FEVec n) (ρ : ↥A →* FEMat n), Function.Injective ρ ∧
      (∀ (φ : ↥A) (b : ↥Bs), (ρ φ).mulVec (ψ (Additive.ofMul b)) =
        ψ (Additive.ofMul ((φ : MulAut ↥Bs) b))) ∧
      ∀ i, ρ (e (M.simple i)) = feS n i := by
  classical
  obtain ⟨V, iadd, imod, ιV, Ψ, hΨ⟩ := exists_frameModelV hBs hNT hC hent hT hA e he hfix hcard
  letI : AddCommGroup V := iadd
  letI : Module (ZMod 3) V := imod
  let ρ : ↥A →* FEMat n :=
    { toFun := fun φ => frameMat ιV Ψ (φ : MulAut ↥Bs)
      map_one' := frameMat_one ιV Ψ
      map_mul' := fun φ χ => frameMat_mul ιV Ψ (φ : MulAut ↥Bs) (χ : MulAut ↥Bs) }
  have hρ : ∀ (φ : ↥A) (b : ↥Bs), (ρ φ).mulVec (Ψ (ιV (Additive.ofMul b))) =
      Ψ (ιV (Additive.ofMul ((φ : MulAut ↥Bs) b))) :=
    fun φ b => frameMat_mulVec ιV Ψ (φ : MulAut ↥Bs) b
  refine ⟨ιV.trans Ψ.toAddEquiv, ρ, fun φ χ h => Subtype.ext (frameMat_injective ιV Ψ h), hρ,
    fun i => ?_⟩
  have hsurj : ∀ y : FEVec n, ∃ b : ↥Bs, Ψ (ιV (Additive.ofMul b)) = y := by
    intro y
    obtain ⟨a, ha⟩ := ιV.surjective (Ψ.symm y)
    exact ⟨Additive.toMul a, by rw [ofMul_toMul, ha, LinearEquiv.apply_symm_apply]⟩
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  obtain ⟨b, rfl⟩ := hsurj y
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact (hρ (e (M.simple i)) b).trans (hΨ i b)

theorem exists_frameModel_E7 {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs)
    {A : Subgroup (MulAut ↥Bs)} (hA : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs)
    (e : CoxeterMatrix.E₇.Group ≃* ↥A)
    (he : ∀ i, GGIsReflection 3 ((e (CoxeterMatrix.E₇.simple i) : ↥A) : MulAut ↥Bs))
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ A, φ b = b) → b = 1) (hcard : Nat.card ↥Bs = 3 ^ 7) :
    ∃ (ψ : Additive ↥Bs ≃+ FEVec 7) (ρ : ↥A →* FEMat 7), Function.Injective ρ ∧
      (∀ (φ : ↥A) (b : ↥Bs), (ρ φ).mulVec (ψ (Additive.ofMul b)) =
        ψ (Additive.ofMul ((φ : MulAut ↥Bs) b))) ∧
      ∀ i, ρ (e (CoxeterMatrix.E₇.simple i)) = feS 7 i :=
  exists_frameModel hBs hNT frameCartan_intCartan_E7 frameCartan_entries_E7 frameCartan_tree_E7 hA
    e he hfix hcard

theorem exists_frameModel_E8 {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hNT : GGNoTransvection 3 Bs)
    {A : Subgroup (MulAut ↥Bs)} (hA : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs)
    (e : CoxeterMatrix.E₈.Group ≃* ↥A)
    (he : ∀ i, GGIsReflection 3 ((e (CoxeterMatrix.E₈.simple i) : ↥A) : MulAut ↥Bs))
    (hfix : ∀ b : ↥Bs, (∀ φ ∈ A, φ b = b) → b = 1) (hcard : Nat.card ↥Bs = 3 ^ 8) :
    ∃ (ψ : Additive ↥Bs ≃+ FEVec 8) (ρ : ↥A →* FEMat 8), Function.Injective ρ ∧
      (∀ (φ : ↥A) (b : ↥Bs), (ρ φ).mulVec (ψ (Additive.ofMul b)) =
        ψ (Additive.ofMul ((φ : MulAut ↥Bs) b))) ∧
      ∀ i, ρ (e (CoxeterMatrix.E₈.simple i)) = feS 8 i :=
  exists_frameModel hBs hNT frameCartan_intCartan_E8 frameCartan_entries_E8 frameCartan_tree_E8 hA
    e he hfix hcard

theorem frameModel_coxRefl {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {n : ℕ}
    {M : CoxeterMatrix (Fin n)} {A : Subgroup (MulAut ↥Bs)} (e : M.Group ≃* ↥A)
    {ρ : ↥A →* FEMat n} (hρ : ∀ i, ρ (e (M.simple i)) = feS n i) {φ : ↥A}
    (hφ : (φ : MulAut ↥Bs) ∈ ggCoxRefl M e) : ρ φ ∈ feT n := by
  classical
  obtain ⟨w, i, hwi⟩ := hφ
  obtain rfl : φ = e (w * M.simple i * w⁻¹) := Subtype.ext hwi
  have hw : w ∈ Subgroup.closure (Set.range M.simple) := by
    rw [frame_closure_simple M]
    exact Subgroup.mem_top w
  have key : ∀ i : Fin n, ρ (e (w * M.simple i * w⁻¹)) ∈ feT n := by
    refine Subgroup.closure_induction_left
      (p := fun w _ => ∀ i : Fin n, ρ (e (w * M.simple i * w⁻¹)) ∈ feT n) ?_ ?_ ?_ hw
    · intro i
      rw [one_mul, inv_one, mul_one, hρ i]
      exact FEConjDer.base i
    · rintro x ⟨j, rfl⟩ y _ hy i
      have hy' := hy i
      have h1 : M.simple j * y * M.simple i * (M.simple j * y)⁻¹ =
          M.simple j * (y * M.simple i * y⁻¹) * M.simple j := by
        rw [mul_inv_rev, frame_simple_inv M j]
        group
      rw [h1]
      generalize y * M.simple i * y⁻¹ = u at hy' ⊢
      simp only [map_mul, hρ j]
      exact FEConjDer.conj j hy'
    · rintro x ⟨j, rfl⟩ y _ hy i
      have hy' := hy i
      have h1 : (M.simple j)⁻¹ * y * M.simple i * ((M.simple j)⁻¹ * y)⁻¹ =
          M.simple j * (y * M.simple i * y⁻¹) * M.simple j := by
        rw [frame_simple_inv M j, mul_inv_rev, frame_simple_inv M j]
        group
      rw [h1]
      generalize y * M.simple i * y⁻¹ = u at hy' ⊢
      simp only [map_mul, hρ j]
      exact FEConjDer.conj j hy'
  exact key i

theorem frameModel_feT {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {n : ℕ}
    {M : CoxeterMatrix (Fin n)} {A : Subgroup (MulAut ↥Bs)} (e : M.Group ≃* ↥A)
    {ρ : ↥A →* FEMat n} (hρ : ∀ i, ρ (e (M.simple i)) = feS n i) {t : FEMat n}
    (ht : t ∈ feT n) : ∃ φ : ↥A, (φ : MulAut ↥Bs) ∈ ggCoxRefl M e ∧ ρ φ = t := by
  classical
  induction ht with
  | base i =>
    refine ⟨e (M.simple i), ⟨1, i, ?_⟩, hρ i⟩
    simp
  | conj j _ ih =>
    obtain ⟨φ, ⟨w, i, hwi⟩, hφ⟩ := ih
    obtain rfl : φ = e (w * M.simple i * w⁻¹) := Subtype.ext hwi
    have h1 : M.simple j * w * M.simple i * (M.simple j * w)⁻¹ =
        M.simple j * (w * M.simple i * w⁻¹) * M.simple j := by
      rw [mul_inv_rev, frame_simple_inv M j]
      group
    refine ⟨e (M.simple j * w * M.simple i * (M.simple j * w)⁻¹), ⟨M.simple j * w, i, rfl⟩, ?_⟩
    rw [h1]
    generalize w * M.simple i * w⁻¹ = u at hφ ⊢
    simp only [map_mul, hρ j, hφ]

end CFSG.StandardType.FrameRoute

end
