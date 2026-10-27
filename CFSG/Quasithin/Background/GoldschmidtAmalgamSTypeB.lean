module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSTypeA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSProd

public section

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv

section Central

variable {E : Type*} [Group E]

set_option synthInstance.maxSize 1000 in
theorem central_inv_Pstd : ∀ i < 4, ∀ j < 2, a₀ ^ i * b₀ ^ j ≠ 1 →
    (a₀ ^ i * b₀ ^ j) * (a₀ ^ i * b₀ ^ j) = 1 →
    (∀ k < 4, ∀ l < 2, (a₀ ^ k * b₀ ^ l) * (a₀ ^ i * b₀ ^ j) =
      (a₀ ^ i * b₀ ^ j) * (a₀ ^ k * b₀ ^ l)) → a₀ ^ i * b₀ ^ j = a₀ ^ 2 := by
  decide

theorem NormA.central_eq {A₁ A₂ : Subgroup E} (N : NormA A₁ A₂) {z : E} (hz : z ∈ A₁ ⊓ A₂)
    (hz1 : z ≠ 1) (hzz : z * z = 1) (hzc : ∀ x ∈ A₁ ⊓ A₂, x * z = z * x) : z = N.a ^ 2 := by
  obtain ⟨i, j, hij⟩ := N.words z hz
  have hmem : ∀ (i j : ℕ), N.a ^ i * N.b ^ j ∈ A₁ := fun i j => (N.words_mem i j).1
  have hs : N.ψ₁ ⟨z, hz.1⟩ = a₀ ^ i * b₀ ^ j := by
    have := N.ψ₁_word i j (hmem i j)
    rw [← this]
    congr 1
    exact Subtype.ext hij
  have hsP : a₀ ^ i * b₀ ^ j ∈ Pstd :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ a₀_mem i) (Subgroup.pow_mem _ b₀_mem j)
  obtain ⟨i', hi', j', hj', hs'⟩ := Pstd_word _ hsP
  rw [hs'] at hs
  have hs1 : a₀ ^ i' * b₀ ^ j' ≠ 1 := by
    rw [← hs]
    intro h1
    apply hz1
    have := N.ψ₁.injective (h1.trans (map_one N.ψ₁).symm)
    exact congrArg Subtype.val this
  have hs2 : (a₀ ^ i' * b₀ ^ j') * (a₀ ^ i' * b₀ ^ j') = 1 := by
    rw [← hs, ← map_mul]
    have : (⟨z, hz.1⟩ : ↥A₁) * ⟨z, hz.1⟩ = 1 := Subtype.ext hzz
    rw [this, map_one]
  have hs3 : ∀ k < 4, ∀ l < 2, (a₀ ^ k * b₀ ^ l) * (a₀ ^ i' * b₀ ^ j') =
      (a₀ ^ i' * b₀ ^ j') * (a₀ ^ k * b₀ ^ l) := by
    intro k _ l _
    rw [← hs, ← N.ψ₁_word k l (hmem k l), ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc _ (N.words_mem k l))
  have h4 := central_inv_Pstd i' hi' j' hj' hs1 hs2 hs3
  have h5 : N.ψ₁ ⟨z, hz.1⟩ = N.ψ₁ ⟨N.a ^ 2, hmem 2 0 |> fun h => by simpa using h⟩ := by
    rw [hs, h4]
    have := N.ψ₁_word 2 0 (hmem 2 0)
    simp only [pow_zero, mul_one] at this
    exact this.symm
  exact congrArg Subtype.val (N.ψ₁.injective h5)

theorem TypeA.exists_iso_central {E' : Type*} [Group E'] {A₁ A₂ : Subgroup E}
    {B₁ B₂ : Subgroup E'} (h : TypeA A₁ A₂) (h' : TypeA B₁ B₂) {z : E} {z' : E'}
    (hz : z ∈ A₁ ⊓ A₂) (hz' : z' ∈ B₁ ⊓ B₂) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hzc : ∀ x ∈ A₁ ⊓ A₂, x * z = z * x) (hz1' : z' ≠ 1) (hzz' : z' * z' = 1)
    (hzc' : ∀ x ∈ B₁ ⊓ B₂, x * z' = z' * x) :
    ∃ (φ₁ : ↥A₁ ≃* ↥B₁) (φ₂ : ↥A₂ ≃* ↥B₂),
      (∀ (x : E) (hx₁ : x ∈ A₁) (hx₂ : x ∈ A₂), (φ₁ ⟨x, hx₁⟩ : E') = φ₂ ⟨x, hx₂⟩) ∧
      (∀ (y : E') (hy₁ : y ∈ B₁) (hy₂ : y ∈ B₂),
        (φ₁.symm ⟨y, hy₁⟩ : E) = φ₂.symm ⟨y, hy₂⟩) ∧
      (φ₁ ⟨z, hz.1⟩ : E') = z' := by
  obtain ⟨N⟩ := h.normA
  obtain ⟨N'⟩ := h'.normA
  have hzN := N.central_eq hz hz1 hzz hzc
  have hzN' := N'.central_eq hz' hz1' hzz' hzc'
  refine ⟨N.ψ₁.trans N'.ψ₁.symm, N.ψ₂.trans N'.ψ₂.symm, ?_, ?_, ?_⟩
  · intro x hx₁ hx₂
    obtain ⟨i, j, rfl⟩ := N.words x (Subgroup.mem_inf.2 ⟨hx₁, hx₂⟩)
    show ((N'.ψ₁.symm (N.ψ₁ ⟨N.a ^ i * N.b ^ j, hx₁⟩) : ↥B₁) : E') =
      ((N'.ψ₂.symm (N.ψ₂ ⟨N.a ^ i * N.b ^ j, hx₂⟩) : ↥B₂) : E')
    rw [N.ψ₁_word, N.ψ₂_word, N'.ψ₁_symm_word, N'.ψ₂_symm_word]
  · intro y hy₁ hy₂
    obtain ⟨i, j, rfl⟩ := N'.words y (Subgroup.mem_inf.2 ⟨hy₁, hy₂⟩)
    show ((N.ψ₁.symm (N'.ψ₁ ⟨N'.a ^ i * N'.b ^ j, hy₁⟩) : ↥A₁) : E) =
      ((N.ψ₂.symm (N'.ψ₂ ⟨N'.a ^ i * N'.b ^ j, hy₂⟩) : ↥A₂) : E)
    rw [N'.ψ₁_word, N'.ψ₂_word, N.ψ₁_symm_word, N.ψ₂_symm_word]
  · have h1 : (⟨z, hz.1⟩ : ↥A₁) = ⟨N.a ^ 2 * N.b ^ 0, (N.words_mem 2 0).1⟩ :=
      Subtype.ext (by show z = N.a ^ 2 * N.b ^ 0; rw [pow_zero, mul_one]; exact hzN)
    show ((N'.ψ₁.symm (N.ψ₁ ⟨z, hz.1⟩) : ↥B₁) : E') = z'
    rw [h1, N.ψ₁_word, N'.ψ₁_symm_word, hzN']
    simp

end Central

section TypeB

variable {E : Type*} [Group E]

structure TypeBData (A₁ A₂ : Subgroup E) where
  K₁ : Subgroup E
  K₂ : Subgroup E
  ε₁ : E
  ε₂ : E
  prod₁ : ProdStr A₁ K₁ ε₁
  prod₂ : ProdStr A₂ K₂ ε₂
  typeA : TypeA K₁ K₂
  ε₁_mem : ε₁ ∈ A₂
  ε₂_mem : ε₂ ∈ A₁
  z_ne : ε₁ * ε₂ ≠ 1
  z_mem : ε₁ * ε₂ ∈ K₁ ⊓ K₂
  inf_split : ∀ t ∈ A₁ ⊓ A₂, t ∈ K₁ ⊓ K₂ ∨ ε₁ * t ∈ K₁ ⊓ K₂

namespace TypeBData

variable {A₁ A₂ : Subgroup E} (D : TypeBData A₁ A₂)

theorem comm : D.ε₂ * D.ε₁ = D.ε₁ * D.ε₂ := D.prod₁.central _ D.ε₂_mem

theorem z_sq : (D.ε₁ * D.ε₂) * (D.ε₁ * D.ε₂) = 1 := by
  calc (D.ε₁ * D.ε₂) * (D.ε₁ * D.ε₂) = D.ε₁ * (D.ε₂ * D.ε₁) * D.ε₂ := by group
    _ = D.ε₁ * (D.ε₁ * D.ε₂) * D.ε₂ := by rw [D.comm]
    _ = (D.ε₁ * D.ε₁) * (D.ε₂ * D.ε₂) := by group
    _ = 1 := by rw [D.prod₁.sq, D.prod₂.sq, one_mul]

theorem z_central : ∀ x ∈ D.K₁ ⊓ D.K₂, x * (D.ε₁ * D.ε₂) = (D.ε₁ * D.ε₂) * x := by
  intro x hx
  have h1 : x * D.ε₁ = D.ε₁ * x := D.prod₁.central x (D.prod₁.le hx.1)
  have h2 : x * D.ε₂ = D.ε₂ * x := D.prod₂.central x (D.prod₂.le hx.2)
  calc x * (D.ε₁ * D.ε₂) = (x * D.ε₁) * D.ε₂ := by group
    _ = D.ε₁ * (x * D.ε₂) := by rw [h1]; group
    _ = D.ε₁ * (D.ε₂ * x) := by rw [h2]
    _ = (D.ε₁ * D.ε₂) * x := by group

include D in
theorem vertexIso₁ : Nonempty (↥A₁ ≃* Multiplicative (ZMod 2) × Perm (Fin 4)) := by
  obtain ⟨Q₁, Q₂, V₁, -⟩ := D.typeA
  obtain ⟨ψ, -⟩ := V₁.exists_iso
  exact ⟨D.prod₁.iota.symm.trans ((MulEquiv.refl _).prodCongr ψ)⟩

include D in
theorem vertexIso₂ : Nonempty (↥A₂ ≃* Multiplicative (ZMod 2) × Perm (Fin 4)) := by
  obtain ⟨Q₁, Q₂, -, V₂, -⟩ := D.typeA
  obtain ⟨ψ, -⟩ := V₂.exists_iso
  exact ⟨D.prod₂.iota.symm.trans ((MulEquiv.refl _).prodCongr ψ)⟩

variable {E' : Type*} [Group E'] {B₁ B₂ : Subgroup E'} (D' : TypeBData B₁ B₂)

theorem agree (φ₁ : ↥D.K₁ ≃* ↥D'.K₁) (φ₂ : ↥D.K₂ ≃* ↥D'.K₂)
    (hag : ∀ (x : E) (h₁ : x ∈ D.K₁) (h₂ : x ∈ D.K₂), (φ₁ ⟨x, h₁⟩ : E') = φ₂ ⟨x, h₂⟩)
    (hz : (φ₁ ⟨D.ε₁ * D.ε₂, D.z_mem.1⟩ : E') = D'.ε₁ * D'.ε₂) :
    ∀ (x : E) (h₁ : x ∈ A₁) (h₂ : x ∈ A₂),
      ((D.prod₁.extIso D'.prod₁ φ₁ ⟨x, h₁⟩ : ↥B₁) : E') =
        ((D.prod₂.extIso D'.prod₂ φ₂ ⟨x, h₂⟩ : ↥B₂) : E') := by
  intro x h₁ h₂
  rcases D.inf_split x ⟨h₁, h₂⟩ with hx | hx
  · have e1 := D.prod₁.extIso_apply_K D'.prod₁ φ₁ hx.1
    have e2 := D.prod₂.extIso_apply_K D'.prod₂ φ₂ hx.2
    exact e1.trans ((hag x hx.1 hx.2).trans e2.symm)
  ·
    have hw1 : D.ε₁ * x ∈ D.K₁ := hx.1
    have hw2 : D.ε₁ * x ∈ D.K₂ := hx.2
    have hx1 : (⟨x, h₁⟩ : ↥A₁) = ⟨D.ε₁, D.prod₁.mem⟩ * ⟨D.ε₁ * x, D.prod₁.le hw1⟩ :=
      Subtype.ext (by
        show x = D.ε₁ * (D.ε₁ * x)
        rw [← mul_assoc, D.prod₁.sq, one_mul])
    have hzz : (D.ε₁ * D.ε₂) * (D.ε₁ * x) ∈ D.K₂ := Subgroup.mul_mem _ D.z_mem.2 hw2
    have hx2 : (⟨x, h₂⟩ : ↥A₂) = ⟨D.ε₂, D.prod₂.mem⟩ *
        ⟨(D.ε₁ * D.ε₂) * (D.ε₁ * x), D.prod₂.le hzz⟩ :=
      Subtype.ext (by
        show x = D.ε₂ * ((D.ε₁ * D.ε₂) * (D.ε₁ * x))
        calc x = D.ε₁ * (D.ε₁ * x) := by rw [← mul_assoc, D.prod₁.sq, one_mul]
          _ = D.ε₁ * (D.ε₂ * D.ε₂) * (D.ε₁ * x) := by rw [D.prod₂.sq, mul_one]
          _ = (D.ε₁ * D.ε₂) * D.ε₂ * (D.ε₁ * x) := by group
          _ = (D.ε₂ * D.ε₁) * D.ε₂ * (D.ε₁ * x) := by rw [D.comm]
          _ = D.ε₂ * ((D.ε₁ * D.ε₂) * (D.ε₁ * x)) := by group)
    have hzφ : (φ₂ ⟨D.ε₁ * D.ε₂, D.z_mem.2⟩ : E') = D'.ε₁ * D'.ε₂ := by
      rw [← hag _ D.z_mem.1 D.z_mem.2]
      exact hz
    have hsplit : (⟨(D.ε₁ * D.ε₂) * (D.ε₁ * x), hzz⟩ : ↥D.K₂) =
        ⟨D.ε₁ * D.ε₂, D.z_mem.2⟩ * ⟨D.ε₁ * x, hw2⟩ := rfl
    have hw : (φ₂ ⟨D.ε₁ * x, hw2⟩ : E') = φ₁ ⟨D.ε₁ * x, hw1⟩ := (hag _ hw1 hw2).symm
    rw [hx1, hx2, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      D.prod₁.extIso_apply_eps D'.prod₁, D.prod₂.extIso_apply_eps D'.prod₂,
      D.prod₁.extIso_apply_K D'.prod₁ φ₁ hw1]
    have e2 := D.prod₂.extIso_apply_K D'.prod₂ φ₂ hzz
    rw [e2, hsplit, map_mul, Subgroup.coe_mul, hzφ, hw]
    have hc' : D'.ε₂ * D'.ε₁ = D'.ε₁ * D'.ε₂ := D'.comm
    calc D'.ε₁ * (φ₁ ⟨D.ε₁ * x, hw1⟩ : E') =
        D'.ε₁ * (D'.ε₂ * D'.ε₂) * (φ₁ ⟨D.ε₁ * x, hw1⟩ : E') := by rw [D'.prod₂.sq, mul_one]
      _ = (D'.ε₁ * D'.ε₂) * D'.ε₂ * (φ₁ ⟨D.ε₁ * x, hw1⟩ : E') := by group
      _ = (D'.ε₂ * D'.ε₁) * D'.ε₂ * (φ₁ ⟨D.ε₁ * x, hw1⟩ : E') := by rw [hc']
      _ = D'.ε₂ * ((D'.ε₁ * D'.ε₂) * (φ₁ ⟨D.ε₁ * x, hw1⟩ : E')) := by group

include D D' in
theorem isAmalgamIso : CFSG.Quasithin.F6.IsAmalgamIso A₁ A₂ B₁ B₂ := by
  obtain ⟨φ₁, φ₂, hag, hag', hz⟩ := TypeA.exists_iso_central D.typeA D'.typeA D.z_mem D'.z_mem
    D.z_ne D.z_sq D.z_central D'.z_ne D'.z_sq D'.z_central
  refine ⟨D.prod₁.extIso D'.prod₁ φ₁, D.prod₂.extIso D'.prod₂ φ₂, ?_, ?_⟩
  · exact D.agree D' φ₁ φ₂ hag hz
  · intro y hy₁ hy₂
    rw [ProdStr.extIso_symm, ProdStr.extIso_symm]
    refine D'.agree D φ₁.symm φ₂.symm hag' ?_ y hy₁ hy₂
    have h1 : φ₁ ⟨D.ε₁ * D.ε₂, D.z_mem.1⟩ = ⟨D'.ε₁ * D'.ε₂, D'.z_mem.1⟩ := Subtype.ext hz
    have h2 := congrArg φ₁.symm h1
    rw [MulEquiv.symm_apply_apply] at h2
    exact (congrArg Subtype.val h2).symm

end TypeBData

end TypeB

end CFSG.Quasithin.F6.GoldAmS
