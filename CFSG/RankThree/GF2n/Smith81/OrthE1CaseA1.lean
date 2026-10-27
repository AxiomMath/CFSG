module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Small
public import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear
public import CFSG.RankThree.GF2n.Smith81.OrthE1Ct
public import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaC

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement Matrix

section Coord

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def coordMat {V : Type} [AddCommGroup V] [Module K V] (c : V ≃ₗ[K] (ι → K))
    (α : V →ₗ[K] V) : Matrix ι ι K :=
  LinearMap.toMatrix' ((c : V →ₗ[K] (ι → K)).comp (α.comp (c.symm : (ι → K) →ₗ[K] V)))

theorem coordMat_mulVec {V : Type} [AddCommGroup V] [Module K V] (c : V ≃ₗ[K] (ι → K))
    (α : V →ₗ[K] V) (v : V) : coordMat c α *ᵥ c v = c (α v) := by
  unfold coordMat
  rw [LinearMap.toMatrix'_mulVec]
  simp

theorem coordMat_comp {V : Type} [AddCommGroup V] [Module K V] (c : V ≃ₗ[K] (ι → K))
    (α β : V →ₗ[K] V) : coordMat c (α.comp β) = coordMat c α * coordMat c β := by
  unfold coordMat
  rw [← LinearMap.toMatrix'_comp]
  congr 1
  apply LinearMap.ext
  intro w
  simp

theorem coordMat_id {V : Type} [AddCommGroup V] [Module K V] (c : V ≃ₗ[K] (ι → K)) :
    coordMat c LinearMap.id = 1 := by
  unfold coordMat
  have : ((c : V →ₗ[K] (ι → K)).comp ((LinearMap.id : V →ₗ[K] V).comp
      (c.symm : (ι → K) →ₗ[K] V))) = LinearMap.id := by
    apply LinearMap.ext
    intro w
    simp
  rw [this, LinearMap.toMatrix'_id]

theorem coordMat_sub {V : Type} [AddCommGroup V] [Module K V] (c : V ≃ₗ[K] (ι → K))
    (α β : V →ₗ[K] V) : coordMat c (α - β) = coordMat c α - coordMat c β := by
  unfold coordMat
  rw [← map_sub]
  congr 1
  apply LinearMap.ext
  intro w
  simp

theorem coordMat_rank {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (c : V ≃ₗ[K] (ι → K)) (α : V →ₗ[K] V) :
    (coordMat c α).rank = Module.finrank K (LinearMap.range α) := by
  unfold Matrix.rank
  have h : (coordMat c α).mulVecLin =
      (c : V →ₗ[K] (ι → K)).comp (α.comp (c.symm : (ι → K) →ₗ[K] V)) := by
    apply LinearMap.ext
    intro w
    rw [Matrix.mulVecLin_apply]
    have := coordMat_mulVec c α (c.symm w)
    rw [c.apply_symm_apply] at this
    simpa using this
  rw [h]
  have hr : LinearMap.range ((c : V →ₗ[K] (ι → K)).comp (α.comp
      (c.symm : (ι → K) →ₗ[K] V))) = (LinearMap.range α).map (c : V →ₗ[K] (ι → K)) := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨α (c.symm w), ⟨c.symm w, rfl⟩, by simp⟩
    · rintro ⟨x, ⟨w, rfl⟩, rfl⟩
      exact ⟨c w, by simp⟩
  rw [hr]
  exact LinearEquiv.finrank_map_eq (c : V ≃ₗ[K] (ι → K)) (LinearMap.range α)

theorem coordMat_eq_of {V : Type} [AddCommGroup V] [Module K V] (c : V ≃ₗ[K] (ι → K))
    (M : Matrix ι ι K) (α : V →ₗ[K] V) (h : ∀ v : V, M *ᵥ c v = c (α v)) :
    M = coordMat c α := by
  ext i j
  have hM := h (c.symm (Pi.single j 1))
  have hC := coordMat_mulVec c α (c.symm (Pi.single j 1))
  rw [c.apply_symm_apply] at hM hC
  have h2 : M *ᵥ Pi.single j 1 = coordMat c α *ᵥ Pi.single j 1 := by rw [hM, hC]
  have h3 := congrFun h2 i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3

@[expose] def coordGL {V : Type} [AddCommGroup V] [Module K V] (c : V ≃ₗ[K] (ι → K))
    (α : V ≃ₗ[K] V) : GL ι K :=
  Units.mk (coordMat c (α : V →ₗ[K] V)) (coordMat c (α.symm : V →ₗ[K] V))
    (by
      rw [← coordMat_comp]
      have h1 : (α : V →ₗ[K] V).comp (α.symm : V →ₗ[K] V) = LinearMap.id := by
        ext w; simp
      rw [h1, coordMat_id])
    (by
      rw [← coordMat_comp]
      have h1 : (α.symm : V →ₗ[K] V).comp (α : V →ₗ[K] V) = LinearMap.id := by
        ext w; simp
      rw [h1, coordMat_id])

end Coord

section Dickson

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem omega_of_even_invol (f : (ι → K) → K)
    (hhom : ∀ (a : K) (v : ι → K), f (a • v) = a ^ 2 * f v)
    (hnz : ∃ v : ι → K, f v ≠ 0) (hN : NormalizerOmegaFor K f) (hD : DicksonNatFor K f)
    (A : GL ι K) (hnorm : ∀ g ∈ StatedOmega f, A * g * A⁻¹ ∈ StatedOmega f)
    (hinv : A * A = 1) (hev : Even ((A : Matrix ι ι K) - 1).rank) : A ∈ StatedOmega f := by
  obtain ⟨c₀, -, hiso⟩ := hN A hnorm
  obtain ⟨v, hv⟩ := hnz
  have hA2 : ∀ w : ι → K, (A : Matrix ι ι K) *ᵥ ((A : Matrix ι ι K) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, hinv, Units.val_one, Matrix.one_mulVec]
  have e : c₀ • (A : Matrix ι ι K) *ᵥ (c₀ • (A : Matrix ι ι K) *ᵥ v) = (c₀ ^ 2) • v := by
    rw [Matrix.mulVec_smul, hA2, smul_smul, sq]
  have h1 := hiso (c₀ • (A : Matrix ι ι K) *ᵥ v)
  rw [e, hhom, hiso v] at h1
  have h4 : (c₀ ^ 4 - 1) * f v = 0 := by
    have : c₀ ^ 4 = (c₀ ^ 2) ^ 2 := by ring
    rw [this]
    linear_combination h1
  have hc4 : c₀ ^ 4 = 1 := by
    rcases mul_eq_zero.mp h4 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv
  have hc1 : c₀ = 1 := by
    have h5 : (c₀ - 1) ^ 4 = c₀ ^ 4 - 1 := by
      have := sub_pow_char_pow (R := K) (p := 2) (n := 2) (x := c₀) (y := 1)
      norm_num at this
      exact this
    rw [hc4, sub_self] at h5
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h5)
  have iso1 : ∀ w : ι → K, f ((A : Matrix ι ι K) *ᵥ w) = f w := by
    intro w
    have := hiso w
    rwa [hc1, one_smul] at this
  exact (hD A iso1 hinv).2 hev

end Dickson

section Transport

variable {K : Type} [Field K] [CharP K 2]

theorem coordGL_inv {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V]
    [Module K V] (c : V ≃ₗ[K] (ι → K)) (α : V ≃ₗ[K] V) :
    (coordGL c α)⁻¹ = coordGL c α.symm := by
  apply Units.ext
  simp [coordGL]

theorem exists_of_involution {ι : Type} [Fintype ι] [DecidableEq ι] (S : QSpace K)
    (V : Submodule K S.E) (Xg : Subgroup (S.E ≃ₗ[K] S.E)) (f : (ι → K) → K)
    (c : ↥V ≃ₗ[K] (ι → K)) (hact : ActsAsNatural S V Xg c f)
    (hhom : ∀ (a : K) (v : ι → K), f (a • v) = a ^ 2 * f v)
    (hnz : ∃ v : ι → K, f v ≠ 0) (hN : NormalizerOmegaFor K f) (hD : DicksonNatFor K f)
    (a : S.E ≃ₗ[K] S.E) (haV : ∀ v ∈ V, a v ∈ V) (hmap : V.map (a : S.E →ₗ[K] S.E) = V)
    (hnorm : ∀ g ∈ Xg, a * g * a⁻¹ ∈ Xg) (ha2 : a * a = 1)
    (hpar : Even (Module.finrank K (LinearMap.range
      (((a : S.E →ₗ[K] S.E).restrict haV : V →ₗ[K] V) - LinearMap.id)))) :
    ∃ g ∈ Xg, ∀ v ∈ V, g v = a v := by
  obtain ⟨hX, h1, h2, h3⟩ := hact
  let α : V ≃ₗ[K] V := LinearEquiv.ofSubmodules a V V hmap
  have hα : ∀ v : V, ((α v : V) : S.E) = a v := fun v => rfl
  have hαs : ∀ v : V, ((α.symm v : V) : S.E) = a.symm v := by
    intro v
    have h := hα (α.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact (a.eq_symm_apply).mpr h.symm
  have hαL : (α : V →ₗ[K] V) = (a : S.E →ₗ[K] S.E).restrict haV := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact hα v
  have hcomp : (α : V →ₗ[K] V).comp (α : V →ₗ[K] V) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show ((α (α v) : V) : S.E) = v
    rw [hα, hα]
    have := congrArg (fun x : S.E ≃ₗ[K] S.E => x (v : S.E)) ha2
    simpa using this
  have hA2 : coordGL c α * coordGL c α = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_one]
    show coordMat c (α : V →ₗ[K] V) * coordMat c (α : V →ₗ[K] V) = 1
    rw [← coordMat_comp, hcomp, coordMat_id]
  have hAmat : ((coordGL c α : GL ι K) : Matrix ι ι K) = coordMat c (α : V →ₗ[K] V) := rfl
  have hAinv : ((coordGL c α)⁻¹ : GL ι K) = coordMat c (α.symm : V →ₗ[K] V) := by
    rw [coordGL_inv]
    rfl
  have hnormΩ : ∀ g ∈ StatedOmega f, coordGL c α * g * (coordGL c α)⁻¹ ∈ StatedOmega f := by
    intro g hg
    obtain ⟨g', hg'X, hg'⟩ := h2 g hg
    have hM : (g : Matrix ι ι K) = coordMat c ((g' : S.E →ₗ[K] S.E).restrict (hX g' hg'X)) := by
      apply coordMat_eq_of c
      intro v
      exact (hg' v.1 v.2).symm
    obtain ⟨A', hA', hA'eq⟩ := h1 (a * g' * a⁻¹) (hnorm g' hg'X)
    have hA'mat : (A' : Matrix ι ι K) = coordMat c
        (((a * g' * a⁻¹ : S.E ≃ₗ[K] S.E) : S.E →ₗ[K] S.E).restrict (hX _ (hnorm g' hg'X))) := by
      apply coordMat_eq_of c
      intro v
      exact (hA'eq v.1 v.2).symm
    have hstep : ((α : V →ₗ[K] V).comp ((g' : S.E →ₗ[K] S.E).restrict (hX g' hg'X))).comp
        (α.symm : V →ₗ[K] V) =
        (((a * g' * a⁻¹ : S.E ≃ₗ[K] S.E) : S.E →ₗ[K] S.E).restrict (hX _ (hnorm g' hg'X))) := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.restrict_apply,
        LinearMap.restrict_apply]
      show ((α (⟨(g' : S.E ≃ₗ[K] S.E) (α.symm v), _⟩ : V)) : S.E) = _
      rw [hα]
      show a ((g' : S.E ≃ₗ[K] S.E) ((α.symm v : V) : S.E)) = _
      rw [hαs]
      rfl
    have hEq : coordGL c α * g * (coordGL c α)⁻¹ = A' := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hAinv, hAmat, hM, hA'mat, ← coordMat_comp,
        ← coordMat_comp, hstep]
    rw [hEq]
    exact hA'
  have hev : Even (((coordGL c α : GL ι K) : Matrix ι ι K) - 1).rank := by
    rw [hAmat, ← coordMat_id (c := c), ← coordMat_sub, coordMat_rank, hαL]
    exact hpar
  have hΩA : coordGL c α ∈ StatedOmega f :=
    omega_of_even_invol f hhom hnz hN hD _ hnormΩ hA2 hev
  obtain ⟨g, hgX, hg⟩ := h2 _ hΩA
  refine ⟨g, hgX, fun v hv => ?_⟩
  have key := hg v hv
  rw [hAmat, coordMat_mulVec] at key
  have h' := congrArg Subtype.val (c.injective key)
  rw [show g v = ((α ⟨v, hv⟩ : V) : S.E) from h', hα]

end Transport

section Forms

theorem statedQuadPlus_hom {K : Type} [Field K] (n : ℕ) (a : K) (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n K (a • v) = a ^ 2 * StatedQuadPlus n K v := by
  simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem statedQuadPlus_nz (K : Type) [Field K] :
    ∃ v : Fin 2 ⊕ Fin 2 → K, StatedQuadPlus 2 K v ≠ 0 := by
  refine ⟨fun j => if j = Sum.inl 0 ∨ j = Sum.inr 0 then 1 else 0, ?_⟩
  simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two]

theorem statedQuadMinus_hom {K : Type} [Field K] (n : ℕ) (b c : K) (a : K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c (a • v) = a ^ 2 * StatedQuadMinus n K b c v := by
  simp only [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  have : ∀ i : Fin (n - 1), a * v (Sum.inl i) * (a * v (Sum.inr (Sum.inl i))) =
      a ^ 2 * (v (Sum.inl i) * v (Sum.inr (Sum.inl i))) := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum]
  ring

theorem statedQuadMinus_nz {K : Type} [Field K] (b c : K) :
    ∃ v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K, StatedQuadMinus 2 K b c v ≠ 0 := by
  refine ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, ?_⟩
  simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.single_apply]

end Forms

section BetaFacts

variable {K : Type} [Field K]

theorem beta_range_eq {S : QSpace K} (V : Submodule K S.E) (β : S.E →ₗ[K] S.E)
    (hβ : BetaProps S V β) (h8 : Module.finrank K S.E = 8) (hV : Module.finrank K V = 4) :
    LinearMap.range β = V := by
  have hker : LinearMap.ker β = V := by
    ext e
    constructor
    · intro he
      exact hβ.ker e (LinearMap.mem_ker.mp he)
    · intro he
      exact LinearMap.mem_ker.mpr (hβ.kills e he)
  have hr := LinearMap.finrank_range_add_finrank_ker β
  rw [hker, h8, hV] at hr
  have hle : LinearMap.range β ≤ V := by
    rintro _ ⟨e, rfl⟩
    exact hβ.range e
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

theorem beta_isTS {S : QSpace K} (V : Submodule K S.E) (β : S.E →ₗ[K] S.E)
    (hβ : BetaProps S V β) (h8 : Module.finrank K S.E = 8) (hV : Module.finrank K V = 4)
    (hiso : ∀ e, S.Qf (e + β e) = S.Qf e) : S.IsTS V := by
  intro v hv
  rw [← beta_range_eq V β hβ h8 hV] at hv
  obtain ⟨e, rfl⟩ := hv
  have h := hiso e
  rw [S.Qf_add, hβ.alt, add_zero] at h
  linear_combination h

theorem comm_beta_of {S : QSpace K} (β : S.E →ₗ[K] S.E) (g k : S.E ≃ₗ[K] S.E) (c : K)
    (hc : c ≠ 0) (hk : ∀ e, k e = e + c • β e) (hgk : g * k = k * g) :
    ∀ e, g (β e) = β (g e) := by
  intro e
  have h1 : g (k e) = k (g e) := by
    have := congrArg (fun x : S.E ≃ₗ[K] S.E => x e) hgk
    simpa [LinearEquiv.mul_apply] using this
  rw [hk, hk, map_add, map_smul] at h1
  have h2 : c • g (β e) = c • β (g e) := by
    have := add_left_cancel h1
    exact this
  exact smul_right_injective S.E hc h2

theorem stab_of_comm {S : QSpace K} (V : Submodule K S.E) (β : S.E →ₗ[K] S.E)
    (hrange : LinearMap.range β = V) (g : S.E ≃ₗ[K] S.E) (hg : ∀ e, g (β e) = β (g e)) :
    ∀ v, v ∈ V ↔ g v ∈ V := by
  have hginv : ∀ e, g.symm (β e) = β (g.symm e) := by
    intro e
    have := hg (g.symm e)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this, LinearEquiv.symm_apply_apply]
  intro v
  constructor
  · intro hv
    rw [← hrange] at hv ⊢
    obtain ⟨e, rfl⟩ := hv
    exact ⟨g e, (hg e).symm⟩
  · intro hv
    rw [← hrange] at hv ⊢
    obtain ⟨e, he⟩ := hv
    refine ⟨g.symm e, ?_⟩
    rw [← hginv, he, LinearEquiv.symm_apply_apply]

end BetaFacts

section Semi

@[expose] def semiConj {K E : Type} [Field K] [AddCommGroup E] [Module K E] (σ : K ≃+* K)
    (T : E ≃+ E) (hT : ∀ (c : K) (e : E), T (c • e) = σ c • T e) (g : E ≃ₗ[K] E) :
    E ≃ₗ[K] E where
  toFun e := T (g (T.symm e))
  invFun e := T (g.symm (T.symm e))
  map_add' x y := by simp
  map_smul' c x := by
    have hTs : T.symm (c • x) = σ.symm c • T.symm x := by
      apply T.injective
      rw [AddEquiv.apply_symm_apply, hT, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    simp only [hTs, map_smul, hT, RingHom.id_apply]
    rw [RingEquiv.apply_symm_apply]
  left_inv e := by simp
  right_inv e := by simp

theorem semiConj_apply {K E : Type} [Field K] [AddCommGroup E] [Module K E] (σ : K ≃+* K)
    (T : E ≃+ E) (hT : ∀ (c : K) (e : E), T (c • e) = σ c • T e) (g : E ≃ₗ[K] E) (e : E) :
    semiConj σ T hT g e = T (g (T.symm e)) := rfl

@[expose] def semiConjHom {K E : Type} [Field K] [AddCommGroup E] [Module K E] (σ : K ≃+* K)
    (T : E ≃+ E) (hT : ∀ (c : K) (e : E), T (c • e) = σ c • T e) :
    (E ≃ₗ[K] E) →* (E ≃ₗ[K] E) where
  toFun := semiConj σ T hT
  map_one' := by
    apply LinearEquiv.ext
    intro e
    simp [semiConj_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro e
    simp [semiConj_apply]

theorem semiConj_mem_O {K E : Type} [Field K] [AddCommGroup E] [Module K E] (σ : K ≃+* K)
    (T : E ≃+ E) (hT : ∀ (c : K) (e : E), T (c • e) = σ c • T e) (Qf : E → K) (a : K)
    (hQ : ∀ e, Qf (T e) = a * σ (Qf e)) (ha : a ≠ 0) (g : E ≃ₗ[K] E)
    (hg : ∀ e, Qf (g e) = Qf e) : ∀ e, Qf (semiConj σ T hT g e) = Qf e := by
  intro e
  rw [semiConj_apply, hQ, hg]
  have h := hQ (T.symm e)
  rw [AddEquiv.apply_symm_apply] at h
  rw [h]

end Semi

section Lgen

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem exists_conj_hom (AM : ActionModel M Q Z)
    (hQn : M ≤ Subgroup.normalizer (Q : Set G)) (m : G) (hm : m ∈ M) :
    ∃ Ψ : (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E) →* (AM.M₀.E ≃ₗ[AM.K] AM.M₀.E),
      (∀ g ∈ AM.S.O, Ψ g ∈ AM.S.O) ∧
      ∀ (y k : G) (hy : y ∈ H0 M Z) (hk : k ∈ H0 M Z), y = m * k * m⁻¹ →
        AM.φ ⟨y, hy⟩ = Ψ (AM.φ ⟨k, hk⟩) := by
  obtain ⟨σ, a, T, hT1, hT2, -, hT4⟩ := AM.glob.act m hm
  have ha : (a : AM.K) ≠ 0 := Units.ne_zero a
  refine ⟨semiConjHom σ T hT1, fun g hg => semiConj_mem_O σ T hT1 AM.M₀.Qf a hT4 ha g hg, ?_⟩
  intro y k hy hk hyk
  subst hyk
  apply LinearEquiv.ext
  intro e
  obtain ⟨x, hxQ, rfl⟩ := AM.M₀.π_surj e
  have hx'Q : m⁻¹ * x * m ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (hQn (inv_mem hm)) x).mp hxQ
    simpa using this
  have hT1' : T.symm (AM.M₀.π x) = AM.M₀.π (m⁻¹ * x * m) := by
    apply T.injective
    rw [AddEquiv.apply_symm_apply, ← hT2 _ hx'Q]
    congr 1
    group
  have hkx : k * (m⁻¹ * x * m) * k⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hQn hk.1) _).mp hx'Q
  rw [← AM.φ_π ⟨m * k * m⁻¹, hy⟩ x hxQ]
  show _ = T ((AM.φ ⟨k, hk⟩) (T.symm (AM.M₀.π x)))
  rw [hT1', ← AM.φ_π ⟨k, hk⟩ _ hx'Q, ← hT2 _ hkx]
  congr 1
  simp only [Subgroup.coe_mk]
  group

theorem map_Omega_le {K : Type} [Field K] (S : QSpace K)
    (Ψ : (S.E ≃ₗ[K] S.E) →* (S.E ≃ₗ[K] S.E)) (hΨ : ∀ g ∈ S.O, Ψ g ∈ S.O) :
    ∀ g ∈ S.Ω, Ψ g ∈ S.Ω := by
  intro g hg
  have hle : Subgroup.map Ψ S.O ≤ S.O := by
    rintro _ ⟨g, hg, rfl⟩
    exact hΨ g hg
  have h2 : Subgroup.map Ψ S.Ω ≤ S.Ω := by
    unfold QSpace.Ω
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h2 ⟨g, hg, rfl⟩

theorem lgen_omega (AM : ActionModel M Q Z) (hQn : M ≤ Subgroup.normalizer (Q : Set G))
    (hLH : LB M Q B ≤ H0 M Z) (hLH0 : Lgen M (LB M Q B) ≤ H0 M Z)
    (hLΩ : ∀ k ∈ LB M Q B, ∀ hk : k ∈ H0 M Z, AM.φ ⟨k, hk⟩ ∈ AM.S.Ω) :
    ∀ x ∈ Lgen M (LB M Q B), ∃ hx : x ∈ H0 M Z, AM.φ ⟨x, hx⟩ ∈ AM.S.Ω := by
  let Ωpre : Subgroup G := (Subgroup.comap (AM.φ) AM.S.Ω).map (H0 M Z).subtype
  have hΩpre : Lgen M (LB M Q B) ≤ Ωpre := by
    unfold Lgen
    apply iSup₂_le
    intro m hm y hy
    have hyL : y ∈ Lgen M (LB M Q B) :=
      Subgroup.mem_iSup_of_mem m (Subgroup.mem_iSup_of_mem hm hy)
    have hyH : y ∈ H0 M Z := hLH0 hyL
    have hkL : m⁻¹ * y * m ∈ LB M Q B := mem_conjSubgroup.mp hy
    have hkH : m⁻¹ * y * m ∈ H0 M Z := hLH hkL
    obtain ⟨Ψ, hΨO, hΨ⟩ := exists_conj_hom AM hQn m hm
    have hyeq := hΨ y (m⁻¹ * y * m) hyH hkH (by group)
    refine Subgroup.mem_map.mpr ⟨⟨y, hyH⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, hyeq]
    exact map_Omega_le AM.S Ψ hΨO _ (hLΩ _ hkL hkH)
  intro x hx
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hΩpre hx)
  rw [Subgroup.mem_comap] at hz
  subst hzx
  exact ⟨z.2, hz⟩

end Lgen

section Heart

open CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {t : G}

theorem xpre_le_Rt (hc : Ctx M Q Z B) (ht : t ∈ LB M Q B) :
    E1Xpre M Q B t ≤ Rt M (LB M Q B) t := by
  unfold E1Xpre
  refine sup_le (Subgroup.commutator_le.mpr fun x hx y hy => ?_) (hc.Q_le_Rt ht)
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem normX_of_ct (hH : E1Hyp M Q Z B t) {c z : G} (hc : c ∈ E1Ct hH.ctx t)
    (hz : z ∈ E1Xpre M Q B t) : c * z * c⁻¹ ∈ E1Xpre M Q B t := by
  have hcinv : c⁻¹ ∈ E1Ct hH.ctx t := inv_mem hc
  have hcinvM : c⁻¹ ∈ M := (mem_CommQ.mp (Subgroup.mem_inf.mp hcinv).1).1
  have hcinvQ : ⁅c⁻¹, t⁆ ∈ Q := (mem_CommQ.mp (Subgroup.mem_inf.mp hcinv).1).2
  have hN := (ctNormalizes_of G M Q Z B t hH c⁻¹ hcinvM hcinvQ).2.2
  have hmem : z ∈ conjSubgroup c⁻¹ (E1Xpre M Q B t) := by rw [hN]; exact hz
  have := mem_conjSubgroup.mp hmem
  simpa [mul_assoc] using this


section LinEquivHelp

variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]

theorem linEquiv_inv_apply (f : E ≃ₗ[K] E) (v : E) : f⁻¹ v = f.symm v := rfl

theorem linEquiv_inv_fix {V : Submodule K E} (f : E ≃ₗ[K] E) (hf : ∀ v ∈ V, f v = v) :
    ∀ v ∈ V, f⁻¹ v = v := by
  intro v hv
  rw [linEquiv_inv_apply, LinearEquiv.symm_apply_eq]
  exact (hf v hv).symm

theorem linEquiv_inv_mem {V : Submodule K E} (f : E ≃ₗ[K] E)
    (hstab : ∀ w, w ∈ V ↔ f w ∈ V) : ∀ v ∈ V, f⁻¹ v ∈ V := by
  intro v hv
  rw [linEquiv_inv_apply]
  exact (hstab _).mpr (by rw [LinearEquiv.apply_symm_apply]; exact hv)

end LinEquivHelp

theorem heart_sub (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z)
    (β : AM.M₀.E →ₗ[AM.K] AM.M₀.E) (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hrange : LinearMap.range β = AM.Vsp hH.ctx t) (hβne : β ≠ 0)
    (hRC : Rt M (LB M Q B) t ≤ E1Ct hH.ctx t)
    (hRβ : ∀ r : ↥(H0 M Z), (r : G) ∈ Rt M (LB M Q B) t → ∀ e, AM.φ r (β e) = β (AM.φ r e))
    (hCβ : ∀ (c : G) (hc : c ∈ H0 M Z), ⁅c, t⁆ ∈ Q → ∀ e,
      AM.φ ⟨c, hc⟩ (β e) = β (AM.φ ⟨c, hc⟩ e))
    (hNx : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t → ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hsurj : ∀ c : AM.K, ∃ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t ∧
      ∀ e, AM.φ x e = e + c • β e)
    (hNsq : ∀ x ∈ Nt M (LB M Q B) t, x ^ 2 ∈ Q)
    (hEven : ∀ g ∈ AM.S.Ω, Even (Module.finrank AM.K ↥(AM.Vsp hH.ctx t ⊓
      (AM.Vsp hH.ctx t).map (g : AM.S.E →ₗ[AM.K] AM.S.E))))
    (hVdim : Module.finrank AM.K ↥(AM.Vsp hH.ctx t) = 4)
    (hcoord : ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (f : (ι → AM.K) → AM.K)
      (c : ↥(AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K)),
      ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) c f ∧
      (∀ (a : AM.K) (v : ι → AM.K), f (a • v) = a ^ 2 * f v) ∧ (∃ v : ι → AM.K, f v ≠ 0) ∧
      NormalizerOmegaFor AM.K f ∧ DicksonNatFor AM.K f)
    (hLC : Nonempty (LCData AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t))))
    (hLgenΩ : ∀ x ∈ Lgen M (LB M Q B), ∃ hx : x ∈ H0 M Z, AM.φ ⟨x, hx⟩ ∈ AM.S.Ω)
    (x : G) (hxL : x ∈ Lgen M (LB M Q B))
    (hcomm : ∀ n ∈ Nt M (LB M Q B) t, ∀ y ∈ conjSubgroup x (Nt M (LB M Q B) t), ⁅n, y⁆ ∈ Q) :
    conjSubgroup x (Nt M (LB M Q B) t) ≤ Rt M (LB M Q B) t := by
  set V := AM.Vsp hH.ctx t with hVdef
  obtain ⟨ι, instF, instD, f, c, hact, hhom, hnz, hN, hD⟩ := hcoord
  obtain ⟨D⟩ := hLC
  obtain ⟨hX, h1, h2, h3⟩ := hact
  have hc : Ctx M Q Z B := hH.ctx
  have htL : t ∈ LB M Q B := hH.mem
  have htQ : t ∉ Q := hH.notQ
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hRH0 : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hNR : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M _ t
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt htL
  have hXR : E1Xpre M Q B t ≤ Rt M (LB M Q B) t := xpre_le_Rt hc htL
  have hNH : Nt M (LB M Q B) t ≤ H0 M Z := hNR.trans hRH0
  have htN : t ∈ Nt M (LB M Q B) t := tMemNt_aux hH
  have hH0M : ∀ c ∈ H0 M Z, c ∈ M := fun c hcH => (Subgroup.mem_inf.mp hcH).1
  have hCmem : ∀ c : G, c ∈ H0 M Z → ⁅c, t⁆ ∈ Q → c ∈ E1Ct hc t := by
    intro c hcH hcQ
    exact Subgroup.mem_inf.mpr ⟨mem_CommQ.mpr ⟨hH0M c hcH, hcQ⟩, hcH⟩
  obtain ⟨hxH, hxΩ⟩ := hLgenΩ x hxL
  have hxM : x ∈ M := hH0M x hxH
  have hxEven := hEven _ hxΩ
  intro n' hn'
  by_contra hnR
  obtain ⟨n, hndef⟩ : ∃ n : G, n = x⁻¹ * n' * x := ⟨_, rfl⟩
  have hn_mem : n ∈ Nt M (LB M Q B) t := by
    rw [hndef]; exact mem_conjSubgroup.mp hn'
  have hn'eq : n' = x * n * x⁻¹ := by rw [hndef]; group
  have hnH : n ∈ H0 M Z := hNH hn_mem
  have hn'H : n' ∈ H0 M Z := by
    rw [hn'eq]; exact mul_mem (mul_mem hxH hnH) (inv_mem hxH)
  have htn : ⁅t, n'⁆ ∈ Q := hcomm t htN n' hn'
  have hn'tQ : ⁅n', t⁆ ∈ Q := by
    have := Q.inv_mem htn
    rwa [commutatorElement_inv] at this
  have hn'C : n' ∈ E1Ct hc t := hCmem n' hn'H hn'tQ
  have hsq : n' ^ 2 ∈ Q := by
    have h1' : n' ^ 2 = x * n ^ 2 * x⁻¹ := by rw [hn'eq]; simp only [sq]; group
    rw [h1']
    exact (Subgroup.mem_normalizer_iff.mp (hQn hxM) (n ^ 2)).mp (hNsq n hn_mem)
  obtain ⟨cn, hcn⟩ := hNx ⟨n, hnH⟩ hn_mem
  have hcn0 : cn ≠ 0 := by
    intro h0
    apply hnR
    have hφn : AM.φ ⟨n, hnH⟩ = 1 := by
      apply LinearEquiv.ext
      intro e
      simp [hcn e, h0]
    have hnQ : n ∈ Q := (AM.φ_ker ⟨n, hnH⟩).mp hφn
    have : n' ∈ Q := by
      rw [hn'eq]
      exact (Subgroup.mem_normalizer_iff.mp (hQn hxM) n).mp hnQ
    exact hQR this
  have key : ∀ w : AM.M₀.E, AM.φ ⟨n', hn'H⟩ (AM.φ ⟨x, hxH⟩ w) =
      AM.φ ⟨x, hxH⟩ (AM.φ ⟨n, hnH⟩ w) := by
    intro w
    have h1' : AM.φ ⟨n', hn'H⟩ * AM.φ ⟨x, hxH⟩ = AM.φ ⟨x, hxH⟩ * AM.φ ⟨n, hnH⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hn'eq]
      group
    have h2' := congrArg (fun f : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E => f w) h1'
    simpa [LinearEquiv.mul_apply] using h2'
  have hφn'eq : ∀ e, AM.φ ⟨n', hn'H⟩ e =
      e + cn • AM.φ ⟨x, hxH⟩ (β ((AM.φ ⟨x, hxH⟩).symm e)) := by
    intro e
    have h2' := key ((AM.φ ⟨x, hxH⟩).symm e)
    rw [LinearEquiv.apply_symm_apply] at h2'
    rw [h2', hcn, map_add, map_smul, LinearEquiv.apply_symm_apply]
  have hinv : AM.φ ⟨n', hn'H⟩ * AM.φ ⟨n', hn'H⟩ = 1 := by
    rw [← map_mul]
    apply (AM.φ_ker _).mpr
    simpa [sq] using hsq
  have hstab := stab_of_comm (S := AM.S) (AM.Vsp hH.ctx t) β hrange (AM.φ ⟨n', hn'H⟩)
    (hCβ n' hn'H hn'tQ)
  have haV : ∀ v ∈ AM.Vsp hH.ctx t, AM.φ ⟨n', hn'H⟩ v ∈ AM.Vsp hH.ctx t :=
    fun v hv => (hstab v).mp hv
  have hmapV : (AM.Vsp hH.ctx t).map (AM.φ ⟨n', hn'H⟩ : AM.S.E →ₗ[AM.K] AM.S.E) =
      AM.Vsp hH.ctx t := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact haV v hv
    · intro v hv
      refine ⟨AM.φ ⟨n', hn'H⟩ v, (hstab v).mp hv, ?_⟩
      have h2' := congrArg (fun f : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E => f v) hinv
      simpa [LinearEquiv.mul_apply] using h2'
  have hkey : ∀ e : AM.M₀.E, AM.φ ⟨n', hn'H⟩ e = e ↔
      (AM.φ ⟨x, hxH⟩).symm e ∈ AM.Vsp hH.ctx t := by
    intro e
    rw [hφn'eq e]
    constructor
    · intro h
      rw [add_eq_left, smul_eq_zero] at h
      rcases h with h | h
      · exact absurd h hcn0
      · have hb : β ((AM.φ ⟨x, hxH⟩).symm e) = 0 := by
          rwa [LinearEquiv.map_eq_zero_iff] at h
        exact hβ.ker _ hb
    · intro h
      rw [show β ((AM.φ ⟨x, hxH⟩).symm e) = 0 from hβ.kills _ h, map_zero, smul_zero, add_zero]
  let Λ : V →ₗ[AM.K] V :=
    ((AM.φ ⟨n', hn'H⟩ : AM.S.E →ₗ[AM.K] AM.S.E).restrict haV) - LinearMap.id
  have hΛ : ∀ v : V, Λ v = 0 ↔ AM.φ ⟨n', hn'H⟩ (v : AM.S.E) = v := by
    intro v
    constructor
    · intro h
      have := congrArg (fun w : V => (w : AM.S.E)) h
      simpa [Λ, sub_eq_zero] using this
    · intro h
      apply Subtype.ext
      simpa [Λ, sub_eq_zero] using h
  have hK0 : (LinearMap.ker Λ).map V.subtype =
      V ⊓ V.map (AM.φ ⟨x, hxH⟩ : AM.S.E →ₗ[AM.K] AM.S.E) := by
    ext e
    rw [Submodule.map_equiv_eq_comap_symm]
    simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.mem_comap]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hfix := (hΛ v).mp (LinearMap.mem_ker.mp hv)
      exact ⟨v.2, (hkey _).mp hfix⟩
    · rintro ⟨he, hφ⟩
      refine ⟨⟨e, he⟩, LinearMap.mem_ker.mpr ((hΛ ⟨e, he⟩).mpr ((hkey e).mpr hφ)), rfl⟩
  have hfin : Module.finrank AM.K (LinearMap.ker Λ) =
      Module.finrank AM.K ↥(V ⊓ V.map (AM.φ ⟨x, hxH⟩ : AM.S.E →ₗ[AM.K] AM.S.E)) := by
    rw [← hK0]
    exact (Submodule.finrank_map_subtype_eq V (LinearMap.ker Λ)).symm
  have hpar : Even (Module.finrank AM.K (LinearMap.range Λ)) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Λ
    rw [hfin, hVdim] at hrn
    obtain ⟨j, hj⟩ := hxEven
    exact ⟨2 - j, by omega⟩
  have hnorm : ∀ g ∈ AM.actImage (E1Xpre M Q B t),
      AM.φ ⟨n', hn'H⟩ * g * (AM.φ ⟨n', hn'H⟩)⁻¹ ∈ AM.actImage (E1Xpre M Q B t) := by
    intro g hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hg
    have hzX : (z : G) ∈ E1Xpre M Q B t := Subgroup.mem_subgroupOf.mp hz
    have hconj : AM.φ ⟨n', hn'H⟩ * AM.φ z * (AM.φ ⟨n', hn'H⟩)⁻¹ =
        AM.φ ⟨n' * (z : G) * n'⁻¹, mul_mem (mul_mem hn'H z.2) (inv_mem hn'H)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [hconj]
    exact Subgroup.mem_map.mpr ⟨⟨n' * (z : G) * n'⁻¹, mul_mem (mul_mem hn'H z.2) (inv_mem hn'H)⟩,
      Subgroup.mem_subgroupOf.mpr (normX_of_ct hH hn'C hzX), rfl⟩
  obtain ⟨g, hgX, hgv⟩ := exists_of_involution AM.S V (AM.actImage (E1Xpre M Q B t)) f c
    ⟨hX, h1, h2, h3⟩ hhom hnz hN hD (AM.φ ⟨n', hn'H⟩) haV hmapV hnorm hinv hpar
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hgX
  have hyX : (y : G) ∈ E1Xpre M Q B t := Subgroup.mem_subgroupOf.mp hy
  have hhH : (y : G) * n' ∈ H0 M Z := mul_mem y.2 hn'H
  have hyR : (y : G) ∈ Rt M (LB M Q B) t := hXR hyX
  have hyC : (y : G) ∈ E1Ct hc t := hRC hyR
  have hhC : (y : G) * n' ∈ E1Ct hc t := mul_mem hyC hn'C
  have hhR : (y : G) * n' ∉ Rt M (LB M Q B) t := by
    intro hR
    apply hnR
    have := (Rt M (LB M Q B) t).mul_mem (inv_mem hyR) hR
    simpa using this
  have hφh_fix : ∀ v ∈ V, AM.φ ⟨(y : G) * n', hhH⟩ v = v := by
    intro v hv
    have hfac : AM.φ ⟨(y : G) * n', hhH⟩ = AM.φ y * AM.φ ⟨n', hn'H⟩ := by
      rw [← map_mul]
      rfl
    have hw : AM.φ y (AM.φ ⟨n', hn'H⟩ v) = AM.φ ⟨n', hn'H⟩ (AM.φ ⟨n', hn'H⟩ v) := by
      rw [hyg]
      exact hgv _ ((hstab v).mp hv)
    rw [hfac, LinearEquiv.mul_apply, hw]
    have h2' := congrArg (fun f : AM.M₀.E ≃ₗ[AM.K] AM.M₀.E => f v) hinv
    simpa [LinearEquiv.mul_apply] using h2'
  set φh : AM.S.E ≃ₗ[AM.K] AM.S.E := AM.φ ⟨(y : G) * n', hhH⟩ with hφhdef
  have hOφh : φh ∈ AM.S.O := fun w => AM.φ_Qf ⟨(y : G) * n', hhH⟩ w
  have hγV : ∀ e : AM.S.E, φh e - e ∈ V := by
    intro e
    apply D.perp
    intro v hv
    have h1' := QSpace.B_isometry AM.S hOφh e v
    rw [hφh_fix v hv] at h1'
    rw [map_sub, LinearMap.sub_apply, h1', sub_self]
  have hγfix : ∀ v ∈ V, (φh : AM.S.E →ₗ[AM.K] AM.S.E) v - v = 0 := fun v hv => by
    rw [LinearEquiv.coe_coe, hφh_fix v hv, sub_self]
  have hφc : ∀ g ∈ AM.actImage (E1Xpre M Q B t), φh * g = g * φh := by
    intro g hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hg
    have hzX : (z : G) ∈ E1Xpre M Q B t := Subgroup.mem_subgroupOf.mp hz
    have hzR : (z : G) ∈ Rt M (LB M Q B) t := hXR hzX
    have hwX : ⁅(y : G) * n', (z : G)⁆ ∈ E1Xpre M Q B t := by
      rw [commutatorElement_def]
      exact mul_mem (normX_of_ct hH hhC hzX) (inv_mem hzX)
    have hwH : ⁅(y : G) * n', (z : G)⁆ ∈ H0 M Z := hRH0 (hXR hwX)
    have hwg : AM.φ ⟨⁅(y : G) * n', (z : G)⁆, hwH⟩ ∈ AM.actImage (E1Xpre M Q B t) :=
      Subgroup.mem_map.mpr ⟨⟨_, hwH⟩, Subgroup.mem_subgroupOf.mpr hwX, rfl⟩
    have hzstab := stab_of_comm (S := AM.S) V β hrange (AM.φ z) (hRβ z hzR)
    have he2 : AM.φ ⟨⁅(y : G) * n', (z : G)⁆, hwH⟩ = ⁅φh, AM.φ z⁆ := by
      rw [← map_commutatorElement]
      congr 1
    have hwfix : ∀ v ∈ V, AM.φ ⟨⁅(y : G) * n', (z : G)⁆, hwH⟩ v = v := by
      intro v hv
      rw [he2, commutatorElement_def, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply]
      have hu : (AM.φ z)⁻¹ v ∈ V := linEquiv_inv_mem (AM.φ z) hzstab v hv
      rw [linEquiv_inv_fix φh hφh_fix ((AM.φ z)⁻¹ v) hu, linEquiv_inv_apply,
        LinearEquiv.apply_symm_apply, hφh_fix v hv]
    have hw1 : AM.φ ⟨⁅(y : G) * n', (z : G)⁆, hwH⟩ = 1 := h3 _ hwg hwfix
    have hcomm1 : ⁅φh, AM.φ z⁆ = 1 := by rw [← he2]; exact hw1
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm1
  have hγcomm : ∀ g : ↥(AM.actImage (E1Xpre M Q B t)), ∀ e : AM.S.E,
      (φh.toLinearMap - LinearMap.id : AM.S.E →ₗ[AM.K] AM.S.E)
          ((g : AM.S.E ≃ₗ[AM.K] AM.S.E) e) =
        (g : AM.S.E ≃ₗ[AM.K] AM.S.E)
          ((φh.toLinearMap - LinearMap.id : AM.S.E →ₗ[AM.K] AM.S.E) e) := by
    intro g e
    have h' : φh ((g : AM.S.E ≃ₗ[AM.K] AM.S.E) e) = (g : AM.S.E ≃ₗ[AM.K] AM.S.E) (φh e) := by
      have hc' := congrArg (fun f : AM.S.E ≃ₗ[AM.K] AM.S.E => f e) (hφc g g.2)
      simpa [LinearEquiv.mul_apply] using hc'
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub, h']
  have hβcomm : ∀ g : ↥(AM.actImage (E1Xpre M Q B t)), ∀ e : AM.S.E,
      β ((g : AM.S.E ≃ₗ[AM.K] AM.S.E) e) = (g : AM.S.E ≃ₗ[AM.K] AM.S.E) (β e) := by
    intro g e
    obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp g.2
    rw [← hzg]
    exact (hRβ z (hXR (Subgroup.mem_subgroupOf.mp hz)) e).symm
  obtain ⟨c₁, hc₁⟩ := D.schur_β (φh.toLinearMap - LinearMap.id) hγcomm (fun e => hγV e)
    (fun v hv => hγfix v hv)
  obtain ⟨c₂, hc₂⟩ := D.schur_β β hβcomm (fun e => hβ.range e) (fun v hv => hβ.kills v hv)
  have hc₂0 : c₂ ≠ 0 := by
    intro h0
    apply hβne
    apply LinearMap.ext
    intro e
    simp [hc₂ e, h0]
  have hDβ : ∀ e, D.β e = c₂⁻¹ • β e := by
    intro e
    rw [hc₂ e, smul_smul, inv_mul_cancel₀ hc₂0, one_smul]
  have hφh_form : ∀ e, φh e = e + (c₁ * c₂⁻¹) • β e := by
    intro e
    have h2' : φh e - e = c₁ • D.β e := by
      have h1' := hc₁ e
      simpa [LinearMap.sub_apply] using h1'
    rw [hDβ e, smul_smul] at h2'
    rw [← h2']
    abel
  obtain ⟨n₁, hn₁N, hn₁⟩ := hsurj (c₁ * c₂⁻¹)
  have hEq : AM.φ n₁ = φh := LinearEquiv.ext fun e => by rw [hn₁ e, hφh_form e]
  have hq1 : AM.φ (n₁⁻¹ * ⟨(y : G) * n', hhH⟩) = 1 := by
    rw [map_mul, map_inv, hEq, inv_mul_cancel]
  have hq : (n₁ : G)⁻¹ * ((y : G) * n') ∈ Q := by
    have := (AM.φ_ker _).mp hq1
    simpa using this
  apply hhR
  have heq : (y : G) * n' = (n₁ : G) * ((n₁ : G)⁻¹ * ((y : G) * n')) := by group
  rw [heq]
  exact mul_mem (hNR hn₁N) (hQR hq)

end Heart


section Final

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {t : G}

theorem L_sylow_props (hH : E1Hyp M Q Z B t) (hSplit : RtSplitStatement) :
    IsPGroup 2 ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)) ∧
      ¬ 2 ∣ ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).index := by
  have hc : Ctx M Q Z B := hH.ctx
  obtain ⟨-, hNX, -, -, -, hLsup, hLX, -, -⟩ := hSplit G M Q Z B t hH
  obtain ⟨-, hNcard, hQuot⟩ := hH.case
  obtain ⟨n, -, hqn, -⟩ := hc.hyp.cp
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [hqn] at hq4
    norm_num at hq4
  have hpos : 0 < Nat.card Z := Nat.card_pos
  have htL : t ∈ LB M Q B := hH.mem
  have hQ2 : IsPGroup 2 Q := isPGroup_Q' hc.hyp
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ2
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt _ htL
  have hNR : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M _ t
  have hRnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Nt M (LB M Q B) t : Set G) :=
    rt_le_normalizer_nt M _ t
  have hQN : Q ≤ Nt M (LB M Q B) t := smith23E1_Q_le_Nt hc htL
  have hNLX : Nt M (LB M Q B) t ⊓ (LB M Q B ⊓ E1Xpre M Q B t) = Q := by
    apply le_antisymm
    · calc Nt M (LB M Q B) t ⊓ (LB M Q B ⊓ E1Xpre M Q B t)
          ≤ Nt M (LB M Q B) t ⊓ E1Xpre M Q B t := inf_le_inf_left _ inf_le_right
        _ = Q := hNX
    · exact le_inf hQN (le_inf le_sup_left le_sup_right)
  have hEN : LB M Q B ⊓ E1Xpre M Q B t ≤ Subgroup.normalizer (Nt M (LB M Q B) t : Set G) :=
    fun x hx => hRnorm (hLR (Subgroup.mem_inf.mp hx).1)
  have hLcard : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z ^ 3 := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer hEN
    rw [← hLsup, hNLX, hNcard, hLX] at h1
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hQpos
    rw [h1]
    ring
  obtain ⟨u, hu, hRN⟩ : ∃ u : ℕ, Odd u ∧
      Nat.card (↥(Rt M (LB M Q B) t) ⧸ (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) =
        Nat.card Z ^ 2 * u := by
    have h2 : 2 ∣ Nat.card Z := by
      rw [hqn]
      exact dvd_pow_self 2 hn0
    have hsq1 : 1 ≤ Nat.card Z ^ 2 := Nat.one_le_pow _ _ hpos
    rcases hQuot with ⟨hnorm, K, hKf, hKfin, hK, ⟨e⟩⟩ | ⟨hnorm, K, hKf, hKfin, hK, b, c, hirr, ⟨e⟩⟩
    · haveI := hnorm
      have _hchar : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (Nat.pos_of_ne_zero hn0) (hK.trans hqn)
      have h := orthE1_card_plus hK hq4 e
      refine ⟨(Nat.card Z ^ 2 - 1) ^ 2,
        Odd.pow (odd_sub_one_of_two_dvd (dvd_pow h2 two_ne_zero) (pow_pos hpos 2)), ?_⟩
      zify [hsq1] at h ⊢
      exact h
    · haveI := hnorm
      have _hchar : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (Nat.pos_of_ne_zero hn0) (hK.trans hqn)
      have h := orthE1_card_minus hK hirr e
      have hsq4 : 1 ≤ Nat.card Z ^ 4 := Nat.one_le_pow _ _ hpos
      refine ⟨Nat.card Z ^ 4 - 1,
        odd_sub_one_of_two_dvd (dvd_pow h2 (by norm_num)) (pow_pos hpos 4), ?_⟩
      zify [hsq1, hsq4] at h ⊢
      exact h
  have hRcard : Nat.card (Rt M (LB M Q B) t) = Nat.card (LB M Q B) * u := by
    rw [← orthE1_card_quot_mul hNR, hRN, hNcard, hLcard]
    ring
  have hLpow : Nat.card (LB M Q B) = 2 ^ (m + 3 * n) := by
    rw [hLcard, hm, hqn]
    ring
  have hpgL : IsPGroup 2 ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)) := by
    apply IsPGroup.of_card (n := m + 3 * n)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLR).toEquiv, hLpow]
  have hidx : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).index = u := by
    have h1 := Subgroup.card_mul_index ((LB M Q B).subgroupOf (Rt M (LB M Q B) t))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLR).toEquiv, hRcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  refine ⟨hpgL, ?_⟩
  rw [hidx]
  intro h
  exact (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)

theorem isPGroup_subgroupOf_of_sq {Q : Subgroup G} (hQ : IsPGroup 2 Q) (T R : Subgroup G)
    (hT : ∀ y ∈ T, y ^ 2 ∈ Q) : IsPGroup 2 (T.subgroupOf R) := by
  intro w
  have hy : ((w : R) : G) ∈ T := Subgroup.mem_subgroupOf.mp w.2
  obtain ⟨j, hj⟩ := hQ ⟨((w : R) : G) ^ 2, hT _ hy⟩
  refine ⟨j + 1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one, OneMemClass.coe_one]
  rw [show 2 ^ (j + 1) = 2 * 2 ^ j by ring, pow_mul]
  have h2 := congrArg Subtype.val hj
  simpa using h2

theorem caseA_forward (hH : E1Hyp M Q Z B t) (hSplit : RtSplitStatement) (hA : E1CaseA M Q B t)
    (x : G) (hx : x ∈ Lgen M (LB M Q B))
    (hNsq : ∀ n ∈ Nt M (LB M Q B) t, n ^ 2 ∈ Q)
    (hheart : conjSubgroup x (Nt M (LB M Q B) t) ≤ Rt M (LB M Q B) t) :
    conjSubgroup x (Nt M (LB M Q B) t) = Nt M (LB M Q B) t := by
  have hc : Ctx M Q Z B := hH.ctx
  have hxM : x ∈ M := (Subgroup.mem_inf.mp (Lgen_le_H0 hc hx)).1
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hNR : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orthE1_Nt_le_Rt M _ t
  have hRnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Nt M (LB M Q B) t : Set G) :=
    rt_le_normalizer_nt M _ t
  have hTsq : ∀ y ∈ conjSubgroup x (Nt M (LB M Q B) t), y ^ 2 ∈ Q := by
    intro y hy
    have hn := mem_conjSubgroup.mp hy
    have h1 : y ^ 2 = x * (x⁻¹ * y * x) ^ 2 * x⁻¹ := by
      simp only [sq]
      group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp (hQn hxM) _).mp (hNsq _ hn)
  have hTpg : IsPGroup 2 ((conjSubgroup x (Nt M (LB M Q B) t)).subgroupOf
      (Rt M (LB M Q B) t)) :=
    isPGroup_subgroupOf_of_sq (isPGroup_Q' hc.hyp) _ _ hTsq
  obtain ⟨P, hPle⟩ := hTpg.exists_le_sylow
  obtain ⟨hLpg, hLidx⟩ := L_sylow_props hH hSplit
  obtain ⟨c, hc'⟩ := exists_conj_of_sylow2 (P : Subgroup (Rt M (LB M Q B) t))
    ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)) P.isPGroup' hLpg (Sylow.not_dvd_index P) hLidx
  have hconjL : ∀ y ∈ conjSubgroup x (Nt M (LB M Q B) t), (c : G) * y * (c : G)⁻¹ ∈ LB M Q B := by
    intro y hy
    have hyR : y ∈ Rt M (LB M Q B) t := hheart hy
    have h1 : (⟨y, hyR⟩ : ↥(Rt M (LB M Q B) t)) ∈
        (conjSubgroup x (Nt M (LB M Q B) t)).subgroupOf (Rt M (LB M Q B) t) :=
      Subgroup.mem_subgroupOf.mpr hy
    have h2 := hc' ⟨y, hyR⟩ (hPle h1)
    have h3 := Subgroup.mem_subgroupOf.mp h2
    simpa using h3
  have hg' : (c : G) * x ∈ Lgen M (LB M Q B) :=
    mul_mem (Rt_le_Lgen M (LB M Q B) t c.2) hx
  have hle : conjSubgroup ((c : G) * x) (Nt M (LB M Q B) t) ≤ LB M Q B := by
    intro w hw
    have h1 := mem_conjSubgroup.mp hw
    have hy : (c : G)⁻¹ * w * (c : G) ∈ conjSubgroup x (Nt M (LB M Q B) t) := by
      apply mem_conjSubgroup.mpr
      have e2 : x⁻¹ * ((c : G)⁻¹ * w * (c : G)) * x = ((c : G) * x)⁻¹ * w * ((c : G) * x) := by
        group
      rw [e2]
      exact h1
    have h2 := hconjL _ hy
    have e : (c : G) * ((c : G)⁻¹ * w * (c : G)) * (c : G)⁻¹ = w := by group
    rwa [e] at h2
  have hA' := hA ((c : G) * x) hg' hle
  have hTN : conjSubgroup x (Nt M (LB M Q B) t) ≤ Nt M (LB M Q B) t := by
    intro y hy
    have h1 : (c : G) * y * (c : G)⁻¹ ∈ conjSubgroup ((c : G) * x) (Nt M (LB M Q B) t) := by
      apply mem_conjSubgroup.mpr
      have e : ((c : G) * x)⁻¹ * ((c : G) * y * (c : G)⁻¹) * ((c : G) * x) = x⁻¹ * y * x := by
        group
      rw [e]
      exact mem_conjSubgroup.mp hy
    rw [hA'] at h1
    have hcinv : (c : G)⁻¹ ∈ Subgroup.normalizer (Nt M (LB M Q B) t : Set G) :=
      hRnorm (inv_mem c.2)
    have h2 := (Subgroup.mem_normalizer_iff.mp hcinv _).mp h1
    have e3 : (c : G)⁻¹ * ((c : G) * y * (c : G)⁻¹) * ((c : G)⁻¹)⁻¹ = y := by group
    rwa [e3] at h2
  exact Subgroup.eq_of_le_of_card_ge hTN (le_of_eq (card_conjSubgroup x _).symm)

end Final

section Core

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} {t : G}

theorem caseA1_core (hH : E1Hyp M Q Z B t) (AM : ActionModel M Q Z) (hA : E1CaseA M Q B t)
    (hSplit : RtSplitStatement) (hRC : Rt M (LB M Q B) t ≤ E1Ct hH.ctx t)
    (β : AM.M₀.E →ₗ[AM.K] AM.M₀.E) (hβ : BetaProps AM.S (AM.Vsp hH.ctx t) β)
    (hRβ : ∀ r : ↥(H0 M Z), (r : G) ∈ Rt M (LB M Q B) t → ∀ e, AM.φ r (β e) = β (AM.φ r e))
    (hNx : ∀ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t → ∃ c : AM.K, ∀ e, AM.φ x e = e + c • β e)
    (hsurj : ∀ c : AM.K, ∃ x : ↥(H0 M Z), (x : G) ∈ Nt M (LB M Q B) t ∧
      ∀ e, AM.φ x e = e + c • β e)
    (hNsq : ∀ x ∈ Nt M (LB M Q B) t, x ^ 2 ∈ Q)
    (hE8 : Module.finrank AM.K AM.M₀.E = 8)
    (hTS : AM.S.IsTS (AM.Vsp hH.ctx t))
    (hdim : Module.finrank AM.K ↥(AM.Vsp hH.ctx t) = 4)
    (hPΩ : AM.S.P (AM.Vsp hH.ctx t) ≤ AM.S.Ω)
    (hEven : ∀ g ∈ AM.S.Ω, Even (Module.finrank AM.K ↥(AM.Vsp hH.ctx t ⊓
      (AM.Vsp hH.ctx t).map (g : AM.S.E →ₗ[AM.K] AM.S.E))))
    (hcoord : ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (f : (ι → AM.K) → AM.K)
      (c : ↥(AM.Vsp hH.ctx t) ≃ₗ[AM.K] (ι → AM.K)),
      ActsAsNatural AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t)) c f ∧
      (∀ (a : AM.K) (v : ι → AM.K), f (a • v) = a ^ 2 * f v) ∧ (∃ v : ι → AM.K, f v ≠ 0) ∧
      NormalizerOmegaFor AM.K f ∧ DicksonNatFor AM.K f)
    (hLC : Nonempty (LCData AM.S (AM.Vsp hH.ctx t) (AM.actImage (E1Xpre M Q B t))))
    (g : G) (hg : g ∈ Lgen M (LB M Q B))
    (hcomm : ∀ n ∈ Nt M (LB M Q B) t, ∀ y ∈ conjSubgroup g (Nt M (LB M Q B) t), ⁅n, y⁆ ∈ Q) :
    conjSubgroup g (Nt M (LB M Q B) t) = Nt M (LB M Q B) t := by
  have hc : Ctx M Q Z B := hH.ctx
  have htL : t ∈ LB M Q B := hH.mem
  have htQ : t ∉ Q := hH.notQ
  have htN : t ∈ Nt M (LB M Q B) t := tMemNt_aux hH
  have htH : t ∈ H0 M Z := ((orthE1_Nt_le_Rt M _ t).trans (hc.Rt_le_H0 t)) htN
  have hrange : LinearMap.range β = AM.Vsp hc t :=
    beta_range_eq (S := AM.S) (AM.Vsp hc t) β hβ hE8 hdim
  obtain ⟨ct, hct⟩ := hNx ⟨t, htH⟩ htN
  have hct0 : ct ≠ 0 := by
    intro h0
    apply htQ
    apply (AM.φ_ker ⟨t, htH⟩).mp
    apply LinearEquiv.ext
    intro e
    simp [hct e, h0]
  have hβne : β ≠ 0 := by
    intro h0
    apply htQ
    apply (AM.φ_ker ⟨t, htH⟩).mp
    apply LinearEquiv.ext
    intro e
    simp [hct e, h0]
  have hCβ : ∀ (c : G) (hcH : c ∈ H0 M Z), ⁅c, t⁆ ∈ Q → ∀ e,
      AM.φ ⟨c, hcH⟩ (β e) = β (AM.φ ⟨c, hcH⟩ e) := by
    intro c hcH hcQ e
    have hcomm1 : AM.φ ⟨c, hcH⟩ * AM.φ ⟨t, htH⟩ = AM.φ ⟨t, htH⟩ * AM.φ ⟨c, hcH⟩ := by
      have h1 : AM.φ (⁅(⟨c, hcH⟩ : ↥(H0 M Z)), ⟨t, htH⟩⁆) = 1 := by
        apply (AM.φ_ker _).mpr
        simpa [commutatorElement_def] using hcQ
      rw [map_commutatorElement] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    exact comm_beta_of (S := AM.S) β (AM.φ ⟨c, hcH⟩) (AM.φ ⟨t, htH⟩) ct hct0 hct hcomm1 e
  have hLΩ : ∀ k ∈ LB M Q B, ∀ hk : k ∈ H0 M Z, AM.φ ⟨k, hk⟩ ∈ AM.S.Ω := by
    intro k hk hkH
    apply hPΩ
    refine ⟨fun e => AM.φ_Qf ⟨k, hkH⟩ e, ?_⟩
    intro v
    exact stab_of_comm (S := AM.S) (AM.Vsp hc t) β hrange _
      (hRβ ⟨k, hkH⟩ (le_Rt _ htL hk)) v
  have hLH : LB M Q B ≤ H0 M Z := (le_Rt _ htL).trans (hc.Rt_le_H0 t)
  have hLH0 : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hLgenΩ := lgen_omega AM hQn hLH hLH0 hLΩ
  exact (caseA_forward hH hSplit hA g hg hNsq
    (heart_sub hH AM β hβ hrange hβne hRC hRβ hCβ hNx hsurj hNsq hEven hdim hcoord hLC
      hLgenΩ g hg hcomm))

end Core

section Main


theorem caseA1_of (hNK : E1NaturalKStatement) (hCt : CtStructureStatement)
    (hSplit : RtSplitStatement) (hLine : NtLineStatement) (hTI : NtTIStatement)
    (hKFd : DicksonNatStatement) (hKFs : DicksonSpaceStatement) : CaseA1Statement := by
  intro G _ _ M Q Z B t hH hA g hg
  constructor
  · intro hcomm
    have hc : Ctx M Q Z B := hH.ctx
    obtain ⟨AM⟩ := ActionModel.nonempty hc.hyp
    have hKZ : Nat.card AM.K = Nat.card Z := AM.glob.card
    have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
    have hK4 : 4 ≤ Nat.card AM.K := by
      rw [hKZ]
      exact hq4
    have hK1 : 1 < Nat.card AM.K := by omega
    have hE8 : Module.finrank AM.K AM.M₀.E = 8 := by
      have h := AM.glob.finrank_E hH.sec.width hK1
      omega
    have hHyp : AM.S.IsHyp := AM.glob.hyperbolic
    obtain ⟨β, hβ, hRβ, hNx, hsurj⟩ := hLine G M Q Z B t hH AM
    have hiso : ∀ e : AM.M₀.E, AM.S.Qf (e + β e) = AM.S.Qf e := by
      intro e
      obtain ⟨x, -, hx⟩ := hsurj 1
      have h1 := AM.φ_Qf x e
      rw [hx e, one_smul] at h1
      exact h1
    have hRC := (hCt G M Q Z B t hH).1
    have hNsq := (ntElemAbelian_of hLine G M Q Z B t hH).2
    rcases hH.case.2.2 with hP | hM
    · have hPl : CaseE1Plus M Q Z B t := ⟨hH.case.1, hH.case.2.1, hP⟩
      obtain ⟨c, hact⟩ := (hNK G M Q Z B t hH AM).1 hPl
      have hdim : Module.finrank AM.K ↥(AM.Vsp hc t) = 4 := by
        rw [LinearEquiv.finrank_eq c, Module.finrank_fintype_fun_eq_card]
        simp
      have hTS : AM.S.IsTS (AM.Vsp hc t) := beta_isTS (S := AM.S) _ β hβ hE8 hdim hiso
      have hXO : AM.actImage (E1Xpre M Q B t) ≤ AM.S.O := by
        intro h hh
        obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hh
        exact fun e => AM.φ_Qf z e
      obtain ⟨hPΩ, hEven⟩ := hKFs AM.K hK4 AM.S hE8 hHyp (AM.Vsp hc t) hTS hdim
      have hLC : Nonempty (LCData AM.S (AM.Vsp hc t) (AM.actImage (E1Xpre M Q B t))) :=
        ((lcData_of parabolic_holds natIrred_holds) AM.K hK4 AM.S hE8 hHyp (AM.Vsp hc t) hTS
          hdim _ hXO).1 c hact
      have hcoord : ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (f : (ι → AM.K) → AM.K)
          (c : ↥(AM.Vsp hc t) ≃ₗ[AM.K] (ι → AM.K)),
          ActsAsNatural AM.S (AM.Vsp hc t) (AM.actImage (E1Xpre M Q B t)) c f ∧
          (∀ (a : AM.K) (v : ι → AM.K), f (a • v) = a ^ 2 * f v) ∧
          (∃ v : ι → AM.K, f v ≠ 0) ∧
          NormalizerOmegaFor AM.K f ∧ DicksonNatFor AM.K f :=
        ⟨Fin 2 ⊕ Fin 2, inferInstance, inferInstance, StatedQuadPlus 2 AM.K, c, hact,
          statedQuadPlus_hom 2, statedQuadPlus_nz AM.K, (normalizerOmega_holds AM.K hK4).1,
          (hKFd AM.K hK4).1⟩
      exact caseA1_core hH AM hA hSplit hRC β hβ hRβ hNx hsurj hNsq hE8 hTS hdim hPΩ hEven
        hcoord hLC g hg hcomm
    · have hPM : CaseE1Minus M Q Z B t := ⟨hH.case.1, hH.case.2.1, hM⟩
      obtain ⟨b, c', hb, c, hact⟩ := (hNK G M Q Z B t hH AM).2 hPM
      have hdim : Module.finrank AM.K ↥(AM.Vsp hc t) = 4 := by
        rw [LinearEquiv.finrank_eq c, Module.finrank_fintype_fun_eq_card]
        simp
      have hTS : AM.S.IsTS (AM.Vsp hc t) := beta_isTS (S := AM.S) _ β hβ hE8 hdim hiso
      have hXO : AM.actImage (E1Xpre M Q B t) ≤ AM.S.O := by
        intro h hh
        obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hh
        exact fun e => AM.φ_Qf z e
      obtain ⟨hPΩ, hEven⟩ := hKFs AM.K hK4 AM.S hE8 hHyp (AM.Vsp hc t) hTS hdim
      have hLC : Nonempty (LCData AM.S (AM.Vsp hc t) (AM.actImage (E1Xpre M Q B t))) :=
        ((lcData_of parabolic_holds natIrred_holds) AM.K hK4 AM.S hE8 hHyp (AM.Vsp hc t) hTS
          hdim _ hXO).2 b c' hb c hact
      have hcoord : ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (f : (ι → AM.K) → AM.K)
          (c : ↥(AM.Vsp hc t) ≃ₗ[AM.K] (ι → AM.K)),
          ActsAsNatural AM.S (AM.Vsp hc t) (AM.actImage (E1Xpre M Q B t)) c f ∧
          (∀ (a : AM.K) (v : ι → AM.K), f (a • v) = a ^ 2 * f v) ∧
          (∃ v : ι → AM.K, f v ≠ 0) ∧
          NormalizerOmegaFor AM.K f ∧ DicksonNatFor AM.K f :=
        ⟨Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2, inferInstance, inferInstance,
          StatedQuadMinus 2 AM.K b c', c, hact, statedQuadMinus_hom 2 b c',
          statedQuadMinus_nz b c', (normalizerOmega_holds AM.K hK4).2 b c' hb,
          (hKFd AM.K hK4).2 b c' hb⟩
      exact caseA1_core hH AM hA hSplit hRC β hβ hRβ hNx hsurj hNsq hE8 hTS hdim hPΩ hEven
        hcoord hLC g hg hcomm
  · intro heq x hx y hy
    rw [heq] at hy
    exact (ntElemAbelian_of hLine G M Q Z B t hH).1 x hx y hy

end Main

end CFSG.RankThree.GF2n.Smith81.Smith23E1
