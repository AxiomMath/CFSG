module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs7

public section

namespace CFSG.Quasithin.H13.Abs523

variable {E : Type} [CommGroup E] [Finite E]

theorem iff_of_inv {𝒦 : Subgroup (MulAut E)} {Y : Subgroup E}
    (hY : ∀ k ∈ 𝒦, ∀ y ∈ Y, k y ∈ Y) (k : MulAut E) (hk : k ∈ 𝒦) (y : E) :
    y ∈ Y ↔ k y ∈ Y := by
  constructor
  · exact hY k hk y
  · intro h
    have := hY k⁻¹ (inv_mem hk) (k y) h
    rw [MulAut.inv_apply, MulEquiv.symm_apply_apply] at this
    exact this

theorem act_trivial_of_small {𝒦 : Subgroup (MulAut E)} [IsSimpleGroup ↥𝒦]
    (hcard : 25 ≤ Nat.card ↥𝒦) (X : Set E) (hX : ∀ k ∈ 𝒦, ∀ x ∈ X, k x ∈ X)
    (hXc : X.ncard ≤ 4) (k : MulAut E) (hk : k ∈ 𝒦) (x : E) (hx : x ∈ X) :
    k x = x := by
  classical
  let ρ : ↥𝒦 →* Equiv.Perm ↥X :=
    { toFun := fun g =>
        { toFun := fun y => ⟨(g : MulAut E) y, hX g g.2 y y.2⟩
          invFun := fun y => ⟨((g⁻¹ : ↥𝒦) : MulAut E) y, hX _ (inv_mem g.2) y y.2⟩
          left_inv := fun y => by
            apply Subtype.ext
            simp
          right_inv := fun y => by
            apply Subtype.ext
            simp }
      map_one' := by
        ext y
        simp
      map_mul' := by
        intro g h
        ext y
        simp [MulAut.mul_apply] }
  have hker : ρ.ker = ⊥ ∨ ρ.ker = ⊤ := IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker
  rcases hker with hbot | htop
  · exfalso
    have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hbot
    have h1 := Nat.card_le_card_of_injective ρ hinj
    rw [Nat.card_perm] at h1
    have hXfin : Nat.card ↥X = X.ncard := by
      exact Nat.card_coe_set_eq X
    rw [hXfin] at h1
    have h2 : (X.ncard).factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hXc
    have h3 : (4 : ℕ).factorial = 24 := by decide
    omega
  · have hmem : (⟨k, hk⟩ : ↥𝒦) ∈ ρ.ker := by
      rw [htop]
      exact Subgroup.mem_top _
    have hfix : ρ ⟨k, hk⟩ = 1 := MonoidHom.mem_ker.mp hmem
    have h3 := congrArg (fun σ : Equiv.Perm ↥X => (σ ⟨x, hx⟩ : ↥X).1) hfix
    simp only [Equiv.Perm.one_apply] at h3
    exact h3

@[expose] def vec (Y₀ : Subgroup E) {Y₁ : Subgroup E} (y : E) (hy : y ∈ Y₁) : Vsec Y₀ Y₁ :=
  ⟨(y : Qt Y₀), mem_Vq.mpr ⟨y, hy, rfl⟩⟩

theorem vec_mul (Y₀ : Subgroup E) {Y₁ : Subgroup E} {y z : E} (hy : y ∈ Y₁) (hz : z ∈ Y₁)
    (hyz : y * z ∈ Y₁) :
    vec Y₀ (y * z) hyz = vec Y₀ y hy * vec Y₀ z hz := by
  apply Subtype.ext
  show ((y * z : E) : Qt Y₀) = (y : Qt Y₀) * (z : Qt Y₀)
  rw [QuotientGroup.mk_mul]

theorem vec_one (Y₀ : Subgroup E) {Y₁ : Subgroup E} : vec Y₀ (1 : E) Y₁.one_mem = 1 := by
  apply Subtype.ext
  show ((1 : E) : Qt Y₀) = 1
  rfl

theorem vec_inv (Y₀ : Subgroup E) {Y₁ : Subgroup E} {y : E} (hy : y ∈ Y₁) (hy' : y⁻¹ ∈ Y₁) :
    vec Y₀ y⁻¹ hy' = (vec Y₀ y hy)⁻¹ := by
  apply Subtype.ext
  show ((y⁻¹ : E) : Qt Y₀) = ((y : Qt Y₀))⁻¹
  rw [QuotientGroup.mk_inv]

theorem vec_eq_one_of_mem (Y₀ : Subgroup E) {Y₁ : Subgroup E} {y : E} (hy : y ∈ Y₁)
    (hy0 : y ∈ Y₀) : vec Y₀ y hy = 1 := by
  apply Subtype.ext
  show ((y : E) : Qt Y₀) = 1
  exact mk_eq_one_of_mem hy0

theorem secHom_vec {Y₀ Y₁ : Subgroup E} (g : stabY Y₀ Y₁) {y : E} (hy : y ∈ Y₁) :
    secHom Y₀ Y₁ g (vec Y₀ y hy) = vec Y₀ (g.1 y) ((g.2.1 y).mp hy) := by
  apply Subtype.ext
  show ((gV g.1 g.2 (vec Y₀ y hy) : Vsec Y₀ Y₁) : Qt Y₀) = ((g.1 y : E) : Qt Y₀)
  rw [gV_coe]
  show gQ g.1 g.2 ((y : E) : Qt Y₀) = _
  rw [gQ_mk]

end CFSG.Quasithin.H13.Abs523
