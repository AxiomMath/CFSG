module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

section ConjP

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem mk_conj_mem_projImage (hπ : π = false → UnitaryFieldData p f K) {h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) {m : ProjGenLinGroup (Fin 3) K}
    (hm : m ∈ projImage (slPi π 3 (p ^ f) K)) :
    (ProjGenLinGroup.mk h)⁻¹ * m * ProjGenLinGroup.mk h ∈ projImage (slPi π 3 (p ^ f) K) := by
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hm
  refine Subgroup.mem_map.mpr ⟨h⁻¹ * s * h, ?_, by rw [map_mul, map_mul, map_inv]⟩
  simpa using conj_mem_slPi hπ (inv_mem hh) hs

@[expose] noncomputable def conjP (hπ : π = false → UnitaryFieldData p f K) {h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) :
    projImage (slPi π 3 (p ^ f) K) ≃* projImage (slPi π 3 (p ^ f) K) where
  toFun m := ⟨(ProjGenLinGroup.mk h)⁻¹ * m * ProjGenLinGroup.mk h,
    mk_conj_mem_projImage hπ hh m.2⟩
  invFun m := ⟨ProjGenLinGroup.mk h * m * (ProjGenLinGroup.mk h)⁻¹, by
    simpa using mk_conj_mem_projImage hπ (inv_mem hh) m.2⟩
  left_inv m := Subtype.ext (by
    change ProjGenLinGroup.mk h * ((ProjGenLinGroup.mk h)⁻¹ * (m : ProjGenLinGroup (Fin 3) K) *
      ProjGenLinGroup.mk h) * (ProjGenLinGroup.mk h)⁻¹ = m
    group)
  right_inv m := Subtype.ext (by
    change (ProjGenLinGroup.mk h)⁻¹ * (ProjGenLinGroup.mk h * (m : ProjGenLinGroup (Fin 3) K) *
      (ProjGenLinGroup.mk h)⁻¹) * ProjGenLinGroup.mk h = m
    group)
  map_mul' m n := Subtype.ext (by
    change (ProjGenLinGroup.mk h)⁻¹ * ((m : ProjGenLinGroup (Fin 3) K) * n) *
      ProjGenLinGroup.mk h = (ProjGenLinGroup.mk h)⁻¹ * m * ProjGenLinGroup.mk h *
        ((ProjGenLinGroup.mk h)⁻¹ * n * ProjGenLinGroup.mk h)
    group)

theorem coe_conjP (hπ : π = false → UnitaryFieldData p f K) {h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) (m : projImage (slPi π 3 (p ^ f) K)) :
    ((conjP hπ hh m : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      (ProjGenLinGroup.mk h)⁻¹ * m * ProjGenLinGroup.mk h :=
  rfl

theorem coe_conjP_symm (hπ : π = false → UnitaryFieldData p f K) {h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) (m : projImage (slPi π 3 (p ^ f) K)) :
    (((conjP hπ hh).symm m : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk h * m * (ProjGenLinGroup.mk h)⁻¹ :=
  rfl

end ConjP

section NormalizedP

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

omit hLn in
theorem slAct_pow_three_of {S : Type*} [Group S] (e : L ≃* S) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (hg3 : g ^ 3 = 1) : slAct e ⟨g, hg⟩ ^ 3 = 1 := by
  rw [← map_pow]
  have : (⟨g, hg⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, hg3, Subgroup.coe_one])
  rw [this, map_one]

theorem slAct_projOf_of_isPGLAtP (hπ : π = false → UnitaryFieldData p f K)
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {a : G} {y : GL (Fin 3) K}
    (hy : IsPGLAtP e a y) {s : GL (Fin 3) K} (hs : s ∈ slPi π 3 (p ^ f) K) :
    slAct e ⟨a, mem_normalizer_of_normal a⟩ (projOf _ ⟨s, hs⟩) =
      projOf _ ⟨y * s * y⁻¹, conj_mem_slPi hπ hy.1 hs⟩ :=
  Subtype.ext (by rw [hy.2, coe_projOf, coe_projOf, map_mul, map_mul, map_inv])

theorem exists_normalized_fieldP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {f₀ : ℕ} (hf : f = 3 * f₀)
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {σ : G}
    (hσ3 : σ ^ 3 = 1) {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hσg : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (g * frobGL ψ s * g⁻¹)) :
    ∃ e' : L ≃* projImage (slPi π 3 (p ^ f) K), ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      ((slAct e' ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (frobGL ψ s) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hΨ3 := frobGL_three' hφ3 hψ
  have hσs : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) =
        projOf _ ⟨g * frobGL ψ s * g⁻¹, conj_mem_slPi hπ hg (frobGL_mem_slPi hK ψ hs)⟩ :=
    fun s hs => Subtype.ext (by rw [hσg, coe_projOf])
  set N := g * frobGL ψ g * frobGL ψ (frobGL ψ g) with hN
  have hW : ∀ A, g * frobGL ψ (g * frobGL ψ (g * frobGL ψ A * g⁻¹) * g⁻¹) * g⁻¹ =
      N * A * N⁻¹ := by
    intro A
    rw [hN]
    simp only [map_mul, map_inv, hΨ3]
    group
  have hmod : ∀ A ∈ slPi π 3 (p ^ f) K, N * A * N⁻¹ * A⁻¹ ∈ StatedScalars (Fin 3) K := by
    intro A hA
    have h1 := congrArg (fun α : MulAut (projImage (slPi π 3 (p ^ f) K)) =>
      ((α (projOf _ ⟨A, hA⟩) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K))
      (slAct_pow_three_of e (mem_normalizer_of_normal σ) hσ3)
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h1
    rw [hσs, hσs, hσs] at h1
    have h2 : ProjGenLinGroup.mk (g * frobGL ψ (g * frobGL ψ (g * frobGL ψ A * g⁻¹) * g⁻¹) *
        g⁻¹) = ProjGenLinGroup.mk A := h1
    rw [hW] at h2
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, h2, mul_inv_cancel]
  have hNc := commute_of_comm_mod_scalars hmod
  have hσ3' : ∀ A ∈ slPi π 3 (p ^ f) K,
      g * frobGL ψ (g * frobGL ψ (g * frobGL ψ A * g⁻¹) * g⁻¹) * g⁻¹ = A := by
    intro A hA
    rw [hW, hNc A hA, mul_inv_cancel_right]
  obtain ⟨h, hh, hconj⟩ := exists_conj_frobGL hK hq hf hφ hφ3 hψ hg hσ3'
  refine ⟨e.trans (conjP hπ hh), fun s hs => ?_⟩
  have hhs : h * s * h⁻¹ ∈ slPi π 3 (p ^ f) K := conj_mem_slPi hπ hh hs
  have h1 : (conjP hπ hh).symm (projOf _ ⟨s, hs⟩) = projOf _ ⟨h * s * h⁻¹, hhs⟩ :=
    Subtype.ext (by rw [coe_conjP_symm, coe_projOf, coe_projOf, map_mul, map_mul, map_inv])
  have h2 : slAct (e.trans (conjP hπ hh)) ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) =
      conjP hπ hh (slAct e ⟨σ, mem_normalizer_of_normal σ⟩
        ((conjP hπ hh).symm (projOf _ ⟨s, hs⟩))) := by
    rw [slAct_apply, slAct_apply]
    rfl
  rw [h2, h1, coe_conjP, hσg, hconj _ hhs]
  have e1 : h⁻¹ * (h * s * h⁻¹) * h = s := by group
  rw [e1, map_mul, map_mul, map_inv]
  group

theorem exists_fixed_liftP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {f₀ : ℕ} (hf : f = 3 * f₀)
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {σ : G}
    (hσψ : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (frobGL ψ s))
    {a : G} (haσ : a * σ = σ * a) {y : GL (Fin 3) K} (hy : IsPGLAtP e a y) :
    ∃ y', IsPGLAtP e a y' ∧ frobGL ψ y' = y' := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hΨ3 : ∀ A : GL (Fin 3) K, frobGL ψ (frobGL ψ (frobGL ψ A)) = A := frobGL_three' hφ3 hψ
  have hσs : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) =
        projOf _ ⟨frobGL ψ s, frobGL_mem_slPi hK ψ hs⟩ :=
    fun s hs => Subtype.ext (by rw [hσψ, coe_projOf])
  have hmod : ∀ t ∈ slPi π 3 (p ^ f) K, (y⁻¹ * frobGL ψ y) * t * (y⁻¹ * frobGL ψ y)⁻¹ * t⁻¹ ∈
      StatedScalars (Fin 3) K := by
    intro t ht
    have hs2 : frobGL ψ (frobGL ψ t) ∈ slPi π 3 (p ^ f) K :=
      frobGL_mem_slPi hK ψ (frobGL_mem_slPi hK ψ ht)
    have hna : (⟨σ * a, mem_normalizer_of_normal _⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨a * σ, mem_normalizer_of_normal _⟩ := Subtype.ext haσ.symm
    have h1 := congrArg (fun x : Subgroup.normalizer (L : Set G) =>
      ((slAct e x (projOf _ ⟨_, hs2⟩) : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K)) hna
    rw [slAct_mul_applyP, slAct_mul_applyP, slAct_projOf_of_isPGLAtP hπ hy, hσs, hσs,
      slAct_projOf_of_isPGLAtP hπ hy] at h1
    have h2 : ProjGenLinGroup.mk (frobGL ψ (y * frobGL ψ (frobGL ψ t) * y⁻¹)) =
        ProjGenLinGroup.mk (y * frobGL ψ (frobGL ψ (frobGL ψ t)) * y⁻¹) := h1
    rw [map_mul (frobGL ψ), map_mul (frobGL ψ), map_inv (frobGL ψ), hΨ3] at h2
    rw [← mk_eq_one_iff_mem_statedScalars]
    calc ProjGenLinGroup.mk ((y⁻¹ * frobGL ψ y) * t * (y⁻¹ * frobGL ψ y)⁻¹ * t⁻¹) =
        (ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk (frobGL ψ y * t * (frobGL ψ y)⁻¹) *
          ProjGenLinGroup.mk y * (ProjGenLinGroup.mk t)⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = (ProjGenLinGroup.mk y)⁻¹ * ProjGenLinGroup.mk (y * t * y⁻¹) *
          ProjGenLinGroup.mk y * (ProjGenLinGroup.mk t)⁻¹ := by rw [h2]
      _ = 1 := by
          simp only [map_mul, map_inv]
          group
  have hcomm := commute_of_comm_mod_scalars hmod
  obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_commute hπ hq' hτ hτ1 hcomm
  have hyψ : frobGL ψ y = y * GeneralLinearGroup.scalar (Fin 3) ℓ := by rw [hℓ]; group
  have hℓT : ℓ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    rw [← scalar_mem_glPi_iff hK, hℓ]
    exact mul_mem (inv_mem hy.1) (frobGL_mem_glPi hK ψ hy.1)
  have s1 : frobGL ψ (frobGL ψ y) = y * GeneralLinearGroup.scalar (Fin 3) ℓ *
      GeneralLinearGroup.scalar (Fin 3) (Units.map (ψ : K →* K) ℓ) := by
    rw [hyψ, map_mul, hyψ, frobGL_scalar]
  have s2 : frobGL ψ (frobGL ψ (frobGL ψ y)) = y * (GeneralLinearGroup.scalar (Fin 3) ℓ *
      GeneralLinearGroup.scalar (Fin 3) (Units.map (ψ : K →* K) ℓ) *
      GeneralLinearGroup.scalar (Fin 3) (Units.map (ψ : K →* K) (Units.map (ψ : K →* K) ℓ))) := by
    rw [s1, map_mul, map_mul, hyψ, frobGL_scalar, frobGL_scalar]
    group
  have hN : (ℓ : K) * ψ ℓ * ψ (ψ ℓ) = 1 := by
    have h1 : GeneralLinearGroup.scalar (Fin 3) ℓ *
        GeneralLinearGroup.scalar (Fin 3) (Units.map (ψ : K →* K) ℓ) *
        GeneralLinearGroup.scalar (Fin 3) (Units.map (ψ : K →* K) (Units.map (ψ : K →* K) ℓ)) =
          1 := by
      have := hΨ3 y
      rw [s2] at this
      exact mul_eq_left.mp this
    have h2 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [Units.val_mul, ← map_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq, Units.coe_map,
      MonoidHom.coe_ofClass] at h2
    exact h2
  obtain ⟨μ, hμT, hμ⟩ := exists_frob_mul_eq hK hq hf hφ hφ3 hψ hℓT hN
  refine ⟨y * GeneralLinearGroup.scalar (Fin 3) μ,
    isPGLAtP_mul_scalar hy ((scalar_mem_glPi_iff hK μ).mpr hμT), ?_⟩
  have hμu : ℓ * Units.map (ψ : K →* K) μ = μ := by
    apply Units.ext
    rw [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, mul_comm]
    exact hμ
  rw [map_mul, hyψ, frobGL_scalar, mul_assoc, ← map_mul, hμu]

theorem mem_sup_centralizer_of_fixedP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {f₀ : ℕ} (hf : f = 3 * f₀)
    {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {a : G}
    {y : GL (Fin 3) K} (hy : IsPGLAtP e a y) (hyψ : frobGL ψ y = y) :
    a ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  obtain ⟨S, -, hScard⟩ := exists_fixedField hK hf hφ3
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  have hS₀ : PiField π p f₀ S := ⟨hK.prime, hf₀, hScard⟩
  have hφ3' : ∀ A ∈ slPi π 3 (p ^ f) K, frobGL φ (frobGL φ (frobGL φ A)) = A :=
    fun A _ => frobGL_three hφ3 A
  have hσ : ∀ A : GL (Fin 3) K, (frobGL φ A : Matrix (Fin 3) (Fin 3) K) =
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (A : Matrix (Fin 3) (Fin 3) K).map (· ^ piCard π (p ^ f₀)) *
        (((1 : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro A
    rw [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, coe_frobGL]
    ext i k
    exact hφ _
  obtain ⟨-, hinner, -⟩ := rank3II_4_10_four hK hq hf (one_mem _) (frobGL φ) hσ hφ3' S hS₀
  have hyφ : frobGL φ y = y := by
    apply Units.ext
    have := congrArg Units.val hyψ
    rw [coe_frobGL] at this ⊢
    ext i k
    have h := congrFun (congrFun this i) k
    simp only [Matrix.map_apply] at h ⊢
    exact (fixed_iff_of_sq hφ3 hψ _).mp h
  obtain ⟨l, hl, hyl⟩ := hinner y ⟨hy.1, hyφ⟩
  obtain ⟨v, hv, -, hav⟩ := exists_inner_mem_of_innerP hK hq hy hl hyl
  have : a = a * v⁻¹ * v := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_right hav) (Subgroup.mem_sup_left hv)

end NormalizedP

section FieldBP

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem fieldB_structureP (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] (hθ : aschbacherSolvableCore 3 L = ⊥)
    {f₀ : ℕ} (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2)
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    {σ : G} (hσA : σ ∈ A) (hσB : σ ∉ L ⊔ Subgroup.centralizer (L : Set G))
    (hσψ : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (frobGL ψ s)) :
    (∀ b ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)),
        ∃ y, IsPGLAtP e b y ∧ frobGL ψ y = y) ∧
      A = A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊔ Subgroup.zpowers σ ∧
      A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊓ Subgroup.zpowers σ = ⊥ ∧
      Nat.card A = Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) * 3 := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hΨ3 := frobGL_three' hφ3 hψ
  have hσs : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) =
        projOf _ ⟨frobGL ψ s, frobGL_mem_slPi hK ψ hs⟩ :=
    fun s hs => Subtype.ext (by rw [hσψ, coe_projOf])
  have hinnerpgl : ∀ b ∈ L ⊔ Subgroup.centralizer (L : Set G), ∃ y, IsPGLAtP e b y := by
    intro b hb
    obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨l, hl⟩).2
    exact ⟨_, isPGLAtP_mul e (isPGLAtP_of_mem e hπ hl hs hse.symm)
      (isPGLAtP_of_mem_centralizer e hu)⟩
  have hfix : ∀ a ∈ A, ∀ y, IsPGLAtP e a y → ∃ y', IsPGLAtP e a y' ∧ frobGL ψ y' = y' :=
    fun a ha y hy => exists_fixed_liftP hK hq hf hφ hφ3 hψ hσψ (hAcomm a ha σ hσA) hy
  have hpglB : ∀ a ∈ A, ∀ y, IsPGLAtP e a y →
      a ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) := by
    intro a ha y hy
    obtain ⟨y', hy', hy'ψ⟩ := hfix a ha y hy
    exact ⟨ha, mem_sup_centralizer_of_fixedP hK hq hf hφ hφ3 hψ hy' hy'ψ⟩
  have hpglOf : ∀ x : G, ∀ g ∈ glPi π 3 (p ^ f) K, (∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      ((slAct e ⟨x, mem_normalizer_of_normal x⟩ (projOf _ ⟨s, hs⟩) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (g * s * g⁻¹)) → IsPGLAtP e x g := by
    intro x g hg hx
    refine ⟨hg, fun m => ?_⟩
    obtain ⟨⟨s, hs⟩, rfl⟩ := projOf_surjective _ m
    rw [hx, coe_projOf, map_mul, map_mul, map_inv]
  have hgen : ∀ a ∈ A, a ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊔
      Subgroup.zpowers σ := by
    intro a ha
    have ha3 : (⟨a, mem_normalizer_of_normal a⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.1.2 a ha)
    rcases pslAct_pgl_or_field hK hq2 hθ e _ ha3 with ⟨y, hy, hys⟩ |
      ⟨-, f₀', hf', ψa, hψa, g, hg, hga⟩
    · exact Subgroup.mem_sup_left (hpglB a ha y ⟨hy, hys⟩)
    · have hf₀' : f₀' = f₀ := by omega
      subst hf₀'
      have hψa' : ψa = φ ∨ ψa = φ ^ 2 := eq_or_eq_sq_of_pow hφ hψa
      have hσσ : σ * σ ∈ Subgroup.zpowers σ := mul_mem (Subgroup.mem_zpowers σ)
        (Subgroup.mem_zpowers σ)
      by_cases hsame : ψa = ψ
      ·
        have hx : IsPGLAtP e (a * σ * σ) g := by
          refine hpglOf _ g hg fun s hs => ?_
          rw [slAct_mul_applyP, slAct_mul_applyP, hσs, hσs, hga, hsame, hΨ3]
        have hxB := hpglB _ (mul_mem (mul_mem ha hσA) hσA) g hx
        have : a = a * σ * σ * (σ * σ)⁻¹ := by group
        rw [this]
        exact mul_mem (Subgroup.mem_sup_left hxB) (Subgroup.mem_sup_right (inv_mem hσσ))
      ·
        have hx : IsPGLAtP e (a * σ) g := by
          refine hpglOf _ g hg fun s hs => ?_
          rw [slAct_mul_applyP, hσs, hga,
            frobGL_comp_eq (ringAut_comp_of_ne hφ3 hψ hψa' hsame)]
        have hxB := hpglB _ (mul_mem ha hσA) g hx
        have : a = a * σ * σ⁻¹ := by group
        rw [this]
        exact mul_mem (Subgroup.mem_sup_left hxB)
          (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers σ)))
  have hAeq : A = A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊔ Subgroup.zpowers σ :=
    le_antisymm (fun a ha => hgen a ha) (sup_le inf_le_left (Subgroup.zpowers_le.mpr hσA))
  have hBσ : A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) ⊓ Subgroup.zpowers σ = ⊥ :=
    inf_zpowers_eq_bot (hA.1.2 σ hσA) (fun h => hσB h.2)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσo : orderOf σ = 3 :=
    orderOf_eq_prime (hA.1.2 σ hσA) (fun h => hσB (h ▸ Subgroup.one_mem _))
  have hcomm : ∀ x ∈ A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)), ∀ y ∈ Subgroup.zpowers σ,
      x * y = y * x := fun x hx y hy =>
    hAcomm x hx.1 y ((Subgroup.zpowers_le.mpr hσA) hy)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [← hAeq, hBσ, Subgroup.card_bot, mul_one, Nat.card_zpowers, hσo] at hcard
  refine ⟨fun b hb => ?_, hAeq, hBσ, hcard⟩
  obtain ⟨y, hy⟩ := hinnerpgl b hb.2
  exact hfix b hb.1 y hy

omit [Finite G] in
theorem card_inf_le_nine (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] (e : L ≃* projImage (slPi π 3 (p ^ f) K))
    {A : Subgroup G} (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) :
    Nat.card (A ⊓ L : Subgroup G) ≤ 9 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  have hLC := inf_centralizer_eq_bot_proj hK hq e
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE : ∀ a ∈ A ⊓ L, ∃ y, IsPGLAtP e a y := by
    intro a ha
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨a, (Subgroup.mem_inf.mp ha).2⟩).2
    exact ⟨s, isPGLAtP_of_mem e hπ _ hs hse.symm⟩
  have hcard := card_eq_card_inf_mul_card_rangeP (hK := hK) (hq := hq) (hA' := hE)
  have hinf : A ⊓ L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hLC]
    exact inf_le_inf_right _ inf_le_right
  rw [hinf, Subgroup.card_bot, one_mul] at hcard
  rw [hcard]
  exact card_le_nine_of_comm h3 hτ hτ1 _
    (range_pglHomP_comm fun a ha b hb => hAcomm a (Subgroup.mem_inf.mp ha).1 b
      (Subgroup.mem_inf.mp hb).1)
    (range_pglHomP_pow fun b hb => hA.1.2 b (Subgroup.mem_inf.mp hb).1)

end FieldBP

end CFSG.RankThree.PartTwo.Sec4
