module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFixed

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

section ConjSL

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] noncomputable def conjSL (hπ : π = false → UnitaryFieldData p f K) {h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) : slPi π 3 (p ^ f) K ≃* slPi π 3 (p ^ f) K where
  toFun s := ⟨h⁻¹ * s * h, by simpa using conj_mem_slPi hπ (inv_mem hh) s.2⟩
  invFun s := ⟨h * s * h⁻¹, conj_mem_slPi hπ hh s.2⟩
  left_inv s := Subtype.ext (show h * (h⁻¹ * (s : GL (Fin 3) K) * h) * h⁻¹ = s by group)
  right_inv s := Subtype.ext (show h⁻¹ * (h * (s : GL (Fin 3) K) * h⁻¹) * h = s by group)
  map_mul' s t := Subtype.ext (show h⁻¹ * ((s : GL (Fin 3) K) * t) * h =
    h⁻¹ * s * h * (h⁻¹ * t * h) by group)

theorem coe_conjSL (hπ : π = false → UnitaryFieldData p f K) {h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) (s : slPi π 3 (p ^ f) K) :
    ((conjSL hπ hh s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = h⁻¹ * s * h :=
  rfl

theorem coe_conjSL_symm (hπ : π = false → UnitaryFieldData p f K) {h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) (s : slPi π 3 (p ^ f) K) :
    (((conjSL hπ hh).symm s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = h * s * h⁻¹ :=
  rfl

end ConjSL

section Lifts

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem isPGLAt_mul_scalar {e : L ≃* slPi π 3 (p ^ f) K} {a : G} {y : GL (Fin 3) K}
    (hy : IsPGLAt e a y) {μ : Kˣ} (hμ : GeneralLinearGroup.scalar (Fin 3) μ ∈ glPi π 3 (p ^ f) K) :
    IsPGLAt e a (y * GeneralLinearGroup.scalar (Fin 3) μ) := by
  refine ⟨mul_mem hy.1 hμ, fun s => ?_⟩
  rw [hy.2 s]
  have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ (s : GL (Fin 3) K)).eq
  calc y * s * y⁻¹ = y * (s * GeneralLinearGroup.scalar (Fin 3) μ) *
      (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ * y⁻¹ := by group
    _ = y * (GeneralLinearGroup.scalar (Fin 3) μ * s) *
      (GeneralLinearGroup.scalar (Fin 3) μ)⁻¹ * y⁻¹ := by rw [hc]
    _ = _ := by group

theorem isPGLAt_inv (hπ : π = false → UnitaryFieldData p f K) {e : L ≃* slPi π 3 (p ^ f) K}
    {a : G} {y : GL (Fin 3) K} (hy : IsPGLAt e a y) : IsPGLAt e a⁻¹ y⁻¹ := by
  refine ⟨inv_mem hy.1, fun s => ?_⟩
  have hmem : y⁻¹ * (s : GL (Fin 3) K) * y ∈ slPi π 3 (p ^ f) K := by
    simpa using conj_mem_slPi hπ (inv_mem hy.1) s.2
  have h1 := hy.2 ⟨_, hmem⟩
  have h2 : slAct e ⟨a, mem_normalizer_of_normal a⟩ ⟨_, hmem⟩ = s :=
    Subtype.ext (by rw [h1]; change y * (y⁻¹ * (s : GL (Fin 3) K) * y) * y⁻¹ = s; group)
  have hinvact : ∀ t, slAct e ⟨a⁻¹, mem_normalizer_of_normal a⁻¹⟩
      (slAct e ⟨a, mem_normalizer_of_normal a⟩ t) = t := by
    intro t
    rw [← slAct_mul_apply]
    have : (⟨a⁻¹ * a, mem_normalizer_of_normal _⟩ : Subgroup.normalizer (L : Set G)) = 1 :=
      Subtype.ext (inv_mul_cancel a)
    rw [this, map_one, MulAut.one_apply]
  have h3 := hinvact ⟨_, hmem⟩
  rw [h2] at h3
  rw [h3, inv_inv]

end Lifts

section Normalized

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_normalized_field (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2)
    (e : L ≃* slPi π 3 (p ^ f) K) {σ : G} (hσ3 : σ ^ 3 = 1) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K)
    (hσg : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        g * frobGL ψ s * g⁻¹) :
    ∃ e' : L ≃* slPi π 3 (p ^ f) K, ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e' ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hσ3' : ∀ A ∈ slPi π 3 (p ^ f) K,
      g * frobGL ψ (g * frobGL ψ (g * frobGL ψ A * g⁻¹) * g⁻¹) * g⁻¹ = A := by
    intro A hA
    have h1 := congrArg (fun α : MulAut (slPi π 3 (p ^ f) K) =>
      ((α ⟨A, hA⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) (slAct_pow_three e hσ3)
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h1
    rw [hσg, hσg, hσg] at h1
    exact h1
  obtain ⟨h, hh, hconj⟩ := exists_conj_frobGL hK hq hf hφ hφ3 hψ hg hσ3'
  refine ⟨e.trans (conjSL hπ hh), fun s => ?_⟩
  have h1 := hσg ((conjSL hπ hh).symm s)
  rw [slAct_apply] at h1 ⊢
  simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply, coe_conjSL]
  rw [h1, coe_conjSL_symm, hconj _ (conj_mem_slPi hπ hh s.2)]
  have e1 : h⁻¹ * (h * (s : GL (Fin 3) K) * h⁻¹) * h = s := by group
  rw [e1]
  group

theorem exists_fixed_lift (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2)
    {e : L ≃* slPi π 3 (p ^ f) K} {σ : G}
    (hσψ : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    {a : G} (haσ : a * σ = σ * a) {y : GL (Fin 3) K} (hy : IsPGLAt e a y) :
    ∃ y', IsPGLAt e a y' ∧ frobGL ψ y' = y' := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hψ3 := ringAut_apply_three' hφ3 hψ
  have hΨ3 : ∀ A : GL (Fin 3) K, frobGL ψ (frobGL ψ (frobGL ψ A)) = A := by
    intro A
    apply Units.ext
    rw [coe_frobGL, coe_frobGL, coe_frobGL]
    ext i k
    simp only [Matrix.map_apply, hψ3]
  have hcomm : ∀ t ∈ slPi π 3 (p ^ f) K, (y⁻¹ * frobGL ψ y) * t = t * (y⁻¹ * frobGL ψ y) := by
    intro t ht
    have hs : frobGL ψ (frobGL ψ t) ∈ slPi π 3 (p ^ f) K :=
      frobGL_mem_slPi hK ψ (frobGL_mem_slPi hK ψ ht)
    have hst : frobGL ψ (frobGL ψ (frobGL ψ t)) = t := hΨ3 t
    have hna : (⟨σ * a, mem_normalizer_of_normal _⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨a * σ, mem_normalizer_of_normal _⟩ := Subtype.ext haσ.symm
    have h1 := congrArg (fun x : Subgroup.normalizer (L : Set G) =>
      ((slAct e x ⟨_, hs⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) hna
    rw [slAct_mul_apply, slAct_mul_apply, hσψ, hy.2, hy.2, hσψ] at h1
    change frobGL ψ (y * frobGL ψ (frobGL ψ t) * y⁻¹) = y * frobGL ψ (frobGL ψ (frobGL ψ t)) *
      y⁻¹ at h1
    rw [map_mul, map_mul, map_inv, hst] at h1
    calc y⁻¹ * frobGL ψ y * t = y⁻¹ * (frobGL ψ y * t * (frobGL ψ y)⁻¹) * frobGL ψ y := by
          group
      _ = y⁻¹ * (y * t * y⁻¹) * frobGL ψ y := by rw [h1]
      _ = t * (y⁻¹ * frobGL ψ y) := by group
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
    isPGLAt_mul_scalar hy ((scalar_mem_glPi_iff hK μ).mpr hμT), ?_⟩
  have hμu : ℓ * Units.map (ψ : K →* K) μ = μ := by
    apply Units.ext
    rw [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, mul_comm]
    exact hμ
  rw [map_mul, hyψ, frobGL_scalar, mul_assoc, ← map_mul, hμu]

theorem mem_sup_centralizer_of_fixed (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2)
    {e : L ≃* slPi π 3 (p ^ f) K} {a : G} {y : GL (Fin 3) K} (hy : IsPGLAt e a y)
    (hyψ : frobGL ψ y = y) : a ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
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
  obtain ⟨v, hv⟩ : ∃ v : L, v = e.symm ⟨l, hl⟩ := ⟨_, rfl⟩
  have hev : ((e v : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = l := by
    rw [hv, MulEquiv.apply_symm_apply]
  have hvinv : IsPGLAt e ((v : G)⁻¹) l⁻¹ := by
    have := isPGLAt_of_mem e hπ (inv_mem v.2)
    have e1 : (⟨(v : G)⁻¹, inv_mem v.2⟩ : L) = v⁻¹ := rfl
    rw [e1, map_inv, Subgroup.coe_inv, hev] at this
    exact this
  have hprod := isPGLAt_mul e hy hvinv
  have hsc : y * l⁻¹ ∈ StatedScalars (Fin 3) K := by
    refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun m hm => ?_
    have hm' : l⁻¹ * m * l ∈ slPi π 3 (p ^ f) K := by
      simpa using conj_mem_slPi hπ (inv_mem (slPi_le_glPi hπ hl)) hm
    have h1 := hyl _ hm'
    calc y * l⁻¹ * m = y * (l⁻¹ * m * l) * y⁻¹ * (y * l⁻¹) := by group
      _ = l * (l⁻¹ * m * l) * l⁻¹ * (y * l⁻¹) := by rw [h1]
      _ = m * (y * l⁻¹) := by group
  have hC := mem_centralizer_of_isPGLAt_scalar hprod hsc
  have : a = a * (v : G)⁻¹ * v := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_right hC) (Subgroup.mem_sup_left v.2)

end Normalized

end CFSG.RankThree.PartTwo.Sec4
