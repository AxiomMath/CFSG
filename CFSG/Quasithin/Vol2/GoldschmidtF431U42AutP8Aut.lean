module

public import CFSG.LieType.SteinbergBRAutGL32

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.LieType.SteinbergBR.AutGL32 CFSG.QuasithinUnique.Setup.Family

theorem ker_card_eight {X : Type*} [Group X] [Finite X] (Q : Subgroup X) [Q.Normal]
    (e : ↥Q ≃* GL32) (hQ : Nat.card ↥Q = 168) (hQi : Q.index = 8)
    (hexp : ∀ x : X, (∃ k : ℕ, orderOf x = 2 ^ k) → x ^ 4 = 1) :
    Nat.card (MulAut.conjNormal (H := Q) : X →* MulAut ↥Q).ker = 8 := by
  classical
  set φ : X →* MulAut ↥Q := MulAut.conjNormal with hφ
  set K := φ.ker with hK
  have hX : Nat.card X = 1344 := by
    have := Subgroup.card_mul_index Q
    rw [hQ, hQi] at this
    omega
  have hker : ∀ x ∈ K, ∀ q : ↥Q, x * (q : X) * x⁻¹ = q := by
    intro x hx q
    have h1 : φ x = 1 := hx
    have h2 : ((φ x q : ↥Q) : X) = x * (q : X) * x⁻¹ := rfl
    rw [← h2, h1]
    rfl
  have hKQ : ∀ x ∈ K, x ∈ Q → x = 1 := by
    intro x hx hxQ
    have hcen : e ⟨x, hxQ⟩ ∈ Subgroup.center GL32 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have := hker x hx q
      calc (q : X) * x = (x * (q : X) * x⁻¹) * x := by rw [this]
        _ = x * q := by group
    rw [center_GL32, Subgroup.mem_bot] at hcen
    have : (⟨x, hxQ⟩ : ↥Q) = 1 := e.injective (hcen.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hKdvd : Nat.card ↥K ∣ 8 := by
    have hinj : Function.Injective ((QuotientGroup.mk' Q).comp K.subtype) := by
      intro x y hxy
      have h1 : ((x : X)⁻¹ * y) ∈ Q := by
        have := QuotientGroup.eq.1 hxy
        simpa using this
      have h2 : (x : X)⁻¹ * y ∈ K := K.mul_mem (K.inv_mem x.2) y.2
      have h3 : (x : X)⁻¹ * y = 1 := hKQ _ h2 h1
      apply Subtype.ext
      calc (x : X) = (x : X) * 1 := by group
        _ = (x : X) * ((x : X)⁻¹ * y) := by rw [h3]
        _ = y := by group
    have := Subgroup.card_dvd_of_injective _ hinj
    have hq : Nat.card (X ⧸ Q) = 8 := by rw [← Subgroup.index_eq_card, hQi]
    rwa [hq] at this
  have hautcard : Nat.card (MulAut ↥Q) = 336 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact card_mulAut_GL32
  have hKmul : Nat.card ↥K * Nat.card ↥φ.range = 1344 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    have h2 : Nat.card (X ⧸ K) = Nat.card ↥φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [h2, hX] at h1
    rw [mul_comm]
    exact h1.symm
  have hrange_le : Nat.card ↥φ.range ≤ 336 := hautcard ▸ Nat.card_le_card_of_injective _
    Subtype.val_injective
  have hK4 : 4 ≤ Nat.card ↥K := by
    by_contra hlt
    have hpos : 0 < Nat.card ↥K := Nat.card_pos
    have h3 : Nat.card ↥K * Nat.card ↥φ.range ≤ 3 * 336 := Nat.mul_le_mul (by omega) hrange_le
    rw [hKmul] at h3
    omega
  have h48 : Nat.card ↥K = 4 ∨ Nat.card ↥K = 8 := by
    have hle : Nat.card ↥K ≤ 8 := Nat.le_of_dvd (by norm_num) hKdvd
    have hk : Nat.card ↥K = 4 ∨ Nat.card ↥K = 5 ∨ Nat.card ↥K = 6 ∨ Nat.card ↥K = 7 ∨
        Nat.card ↥K = 8 := by omega
    rcases hk with h | h | h | h | h
    · exact Or.inl h
    · rw [h] at hKdvd; omega
    · rw [h] at hKdvd; omega
    · rw [h] at hKdvd; omega
    · exact Or.inr h
  rcases h48 with h4 | h8
  · exfalso
    have hr336 : Nat.card ↥φ.range = 336 := by
      rw [h4] at hKmul
      omega
    have hrtop : φ.range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hr336, hautcard]
    obtain ⟨α, hα⟩ : ∃ α : MulAut ↥Q, orderOf α = 8 := by
      refine ⟨(MulAut.congr e).symm alphaAut, ?_⟩
      rw [MulEquiv.orderOf_eq]
      simpa using orderOf_alphaAut
    obtain ⟨x, hx⟩ : ∃ x : X, φ x = α := by
      have : α ∈ φ.range := by rw [hrtop]; trivial
      exact this
    have h8x : 8 ∣ orderOf x := by
      have := orderOf_map_dvd φ x
      rwa [hx, hα] at this
    have hx0 : orderOf x ≠ 0 := orderOf_pos x |>.ne'
    set y := x ^ (orderOf x / 8) with hy
    have hy8 : orderOf y = 8 := orderOf_pow_orderOf_div hx0 h8x
    have hy4 := hexp y ⟨3, by rw [hy8]; norm_num⟩
    have := orderOf_dvd_of_pow_eq_one hy4
    rw [hy8] at this
    omega
  · exact h8

end CFSG.Quasithin.H13.F431.U42Aut
