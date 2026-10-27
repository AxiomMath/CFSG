module

public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.KFU

variable {n p : ℕ} {K : Type} [Field K]

@[expose] def NormPerm (p : ℕ) (g : GL (Fin n) K) (τ : Equiv.Perm (Fin n)) : Prop :=
  (∀ x ∈ torusSU p n K, g * x * g⁻¹ ∈ torusSU p n K) ∧
    ∀ x ∈ torusSU p n K, ∀ i, ent (g * x * g⁻¹) (τ i) (τ i) = ent x i i

theorem NormPerm.one : NormPerm (n := n) (K := K) p 1 1 := by
  refine ⟨fun x hx => by simpa using hx, fun x _ i => by simp⟩

theorem NormPerm.mul {g₁ g₂ : GL (Fin n) K} {τ₁ τ₂ : Equiv.Perm (Fin n)} (h₁ : NormPerm p g₁ τ₁)
    (h₂ : NormPerm p g₂ τ₂) : NormPerm p (g₁ * g₂) (τ₁ * τ₂) := by
  refine ⟨fun x hx => ?_, fun x hx i => ?_⟩
  · have := h₁.1 _ (h₂.1 x hx)
    simpa [mul_assoc] using this
  · have h3 := h₁.2 (g₂ * x * g₂⁻¹) (h₂.1 x hx) (τ₂ i)
    rw [h₂.2 x hx i] at h3
    have : g₁ * g₂ * x * (g₁ * g₂)⁻¹ = g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ := by group
    rw [this]
    exact h3

theorem NormPerm.ent_conj {g : GL (Fin n) K} {τ : Equiv.Perm (Fin n)} (hg : NormPerm p g τ)
    {x : GL (Fin n) K} (hx : x ∈ torusSU p n K) (m : Fin n) :
    ent (g * x * g⁻¹) m m = ent x (τ.symm m) (τ.symm m) := by
  have := hg.2 x hx (τ.symm m)
  rwa [Equiv.apply_symm_apply] at this

theorem isDiag_of_mem_torusSU {x : GL (Fin n) K} (hx : x ∈ torusSU p n K) :
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag := by
  obtain ⟨d, -, -, rfl⟩ := mem_torusSU_iff.mp hx
  exact isDiag_diagU d

theorem eq_of_isDiag_of_ent_eq {x y : GL (Fin n) K}
    (hx : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    (hy : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    (h : ∀ m, ent x m m = ent y m m) : x = y := by
  apply Units.ext
  ext k l
  by_cases hkl : k = l
  · subst hkl
    exact h k
  · rw [hx hkl, hy hkl]

theorem NormPerm.conj_eq {g : GL (Fin n) K} {τ : Equiv.Perm (Fin n)} (hg : NormPerm p g τ)
    {x y : GL (Fin n) K} (hx : x ∈ torusSU p n K) (hy : y ∈ torusSU p n K)
    (h : ∀ m, ent y m m = ent x (τ.symm m) (τ.symm m)) : g * x * g⁻¹ = y :=
  eq_of_isDiag_of_ent_eq (isDiag_of_mem_torusSU (hg.1 x hx)) (isDiag_of_mem_torusSU hy)
    fun m => by rw [hg.ent_conj hx m, h m]

theorem torus_char_distinct {u : Kˣ} (hu : u ^ p = 1) (hu2 : u ^ 2 ≠ 1) (i j : Fin n)
    (hij : i ≠ j) : ∃ g ∈ torusSU p n K, ent g i i ≠ ent g j j :=
  torusSU_char_distinct hu hu2 hij

theorem NormPerm.eq_of_conj_eq {g₁ g₂ : GL (Fin n) K} {τ₁ τ₂ : Equiv.Perm (Fin n)}
    (hdist : ∀ i j : Fin n, i ≠ j → ∃ x ∈ torusSU p n K, ent x i i ≠ ent x j j)
    (h₁ : NormPerm p g₁ τ₁) (h₂ : NormPerm p g₂ τ₂)
    (h : ∀ x ∈ torusSU p n K, g₁ * x * g₁⁻¹ = g₂ * x * g₂⁻¹) : τ₁ = τ₂ := by
  refine Equiv.ext fun i => ?_
  by_contra hne
  set m : Fin n := τ₂.symm (τ₁ i) with hm
  have h1 : τ₂ m = τ₁ i := by rw [hm, Equiv.apply_symm_apply]
  have hmi : m ≠ i := by
    intro h'
    rw [h'] at h1
    exact hne h1.symm
  obtain ⟨x, hx, hxne⟩ := hdist m i hmi
  apply hxne
  have e1 := h₁.2 x hx i
  have e2 := h₂.2 x hx m
  rw [h x hx] at e1
  rw [h1] at e2
  exact e2.symm.trans e1

theorem exists_normPerm (hdist : ∀ i j : Fin n, i ≠ j → ∃ x ∈ torusSU p n K, ent x i i ≠ ent x j j)
    {g : GL (Fin n) K} (hg : ∀ x ∈ torusSU p n K, g * x * g⁻¹ ∈ torusSU p n K)
    (hginv : ∀ x ∈ torusSU p n K, g⁻¹ * x * g ∈ torusSU p n K) :
    ∃ τ : Equiv.Perm (Fin n), NormPerm p g τ := by
  obtain ⟨τ, -, -, hτ⟩ := exists_perm_of_normalizes (torusSU p n K)
    (fun x hx => isDiag_of_mem_torusSU hx) hdist hg hginv
  exact ⟨τ, hg, hτ⟩

theorem diagU_inv (d : Fin n → Kˣ) : (diagU d⁻¹ : GL (Fin n) K) = (diagU d)⁻¹ :=
  map_inv diagUHom d

theorem diagU_zpow (d : Fin n → Kˣ) (k : ℤ) : (diagU d : GL (Fin n) K) ^ k = diagU (d ^ k) :=
  (map_zpow diagUHom d k).symm

theorem torusVec_comp (τ : Equiv.Perm (Fin n)) {v : Fin n → Kˣ} (hv : v ∈ torusVec p n K) :
    (v ∘ τ) ∈ torusVec p n K := by
  refine ⟨fun i => hv.1 (τ i), ?_⟩
  have := hv.2
  rw [← Equiv.prod_comp τ] at this
  exact this

theorem NormPerm.conj_diagU {g : GL (Fin n) K} {τ : Equiv.Perm (Fin n)} (hg : NormPerm p g τ)
    {v : Fin n → Kˣ} (hv : v ∈ torusVec p n K) : g * diagU v * g⁻¹ = diagU (v ∘ τ.symm) := by
  have hx : diagU v ∈ torusSU p n K := mem_torusSU_iff.mpr ⟨v, hv.1, hv.2, rfl⟩
  have hy : diagU (v ∘ τ.symm) ∈ torusSU p n K :=
    let hy' := torusVec_comp τ.symm hv
    mem_torusSU_iff.mpr ⟨_, hy'.1, hy'.2, rfl⟩
  refine hg.conj_eq hx hy fun m => ?_
  simp [ent, diagU_val]

end CFSG.RankThree.PartOne.KFU
