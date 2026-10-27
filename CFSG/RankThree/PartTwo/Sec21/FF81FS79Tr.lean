module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Fus

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

def HC (u v : H) : Prop := ∃ g : H, g * u * g⁻¹ = v

theorem HC.symm {u v : H} (h : HC u v) : HC v u := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, by rw [← hg]; group⟩

theorem HC.trans {u v w : H} (h₁ : HC u v) (h₂ : HC v w) : HC u w := by
  obtain ⟨g, rfl⟩ := h₁
  obtain ⟨g', rfl⟩ := h₂
  exact ⟨g' * g, by group⟩

theorem FS79Hyp.t_sq (h : FS79Hyp b t b₁ b₂ J) : t * t = 1 := by
  rw [← pow_two, ← h.ord_t]
  exact pow_orderOf_eq_one t

theorem FS79Hyp.t_ne_one (h : FS79Hyp b t b₁ b₂ J) : t ≠ 1 := by
  intro h1
  have := h.ord_t
  rw [h1, orderOf_one] at this
  omega

theorem FS79Hyp.t_not_mem_J (h : FS79Hyp b t b₁ b₂ J) : t ∉ J := by
  intro htJ
  have hc : t * b = b * t := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b htJ)
  have h2 : b = b⁻¹ := by
    rw [← h.inv_b]
    calc b = (b * t) * t⁻¹ := by group
      _ = t * b * t⁻¹ := by rw [← hc]
  have hb2 : b ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp h2
  have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hb2
  rw [h.ord_b] at hdvd
  norm_num at hdvd

theorem FS79Hyp.mem_zpowers_t (h : FS79Hyp b t b₁ b₂ J) {x : H} (hx : x ∈ Subgroup.zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact h.t_sq
  rw [← zpow_mod_orderOf, h.ord_t]
  have hk : (k % ((2 : ℕ) : ℤ)) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hk with h0 | h0 <;> rw [h0]
  · left
    exact zpow_zero t
  · right
    exact zpow_one t

namespace Std

variable (S : Std b t b₁ b₂ J)

theorem ι_comm_t (σ : J6.S6) : S.ι σ * t = t * S.ι σ :=
  Subgroup.mem_centralizer_singleton_iff.mp (S.hyp.J_le_cen_t (S.ι_mem σ))

theorem ι_comm_b (σ : J6.S6) : S.ι σ * b = b * S.ι σ :=
  Subgroup.mem_centralizer_singleton_iff.mp (S.hyp.J_le_cen_b (S.ι_mem σ))

theorem ι_φ (y : ↥J) : S.ι (S.φ y) = (y : H) := by
  rw [Std.ι_apply]
  simp

theorem mem_B₁_iff (z : H) :
    z ∈ Subgroup.closure ({b₁, b₂} : Set H) ↔ ∃ e ∈ J6.Efin, z = S.ι e := by
  constructor
  · intro hz
    have hzJ := S.hyp.B₁_le_J hz
    have h1 := (S.hyp.mem_B₁_iff_std S.φ S.φ₁ S.φ₂ ⟨z, hzJ⟩).mp hz
    exact ⟨S.φ ⟨z, hzJ⟩, h1, by rw [S.ι_φ]⟩
  · rintro ⟨e, he, rfl⟩
    have := (S.hyp.mem_B₁_iff_std S.φ S.φ₁ S.φ₂ (S.φ.symm e)).mpr (by simpa using he)
    exact this

theorem norm6 {j : H} (hj : j ∈ J)
    (hjB : ∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H),
      j * y * j⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H)) :
    S.φ ⟨j, hj⟩ ∈ J6.N6 := by
  classical
  simp only [J6.N6, Finset.mem_filter, Finset.mem_univ, true_and]
  intro e he
  have hyB : (S.φ.symm e : H) ∈ Subgroup.closure ({b₁, b₂} : Set H) :=
    (S.mem_B₁_iff _).mpr ⟨e, he, by rw [S.ι_apply]⟩
  have h1 := hjB _ hyB
  have hJ1 : j * (S.φ.symm e : H) * j⁻¹ ∈ J :=
    J.mul_mem (J.mul_mem hj (S.φ.symm e).2) (J.inv_mem hj)
  have h2 := (S.hyp.mem_B₁_iff_std S.φ S.φ₁ S.φ₂ ⟨_, hJ1⟩).mp h1
  have e1 : (⟨j * (S.φ.symm e : H) * j⁻¹, hJ1⟩ : ↥J) = ⟨j, hj⟩ * S.φ.symm e * ⟨j, hj⟩⁻¹ := by
    apply Subtype.ext
    simp
  rw [e1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
  exact h2

theorem conj_ι {j : H} (hj : j ∈ J) (e : J6.S6) :
    j * S.ι e * j⁻¹ = S.ι (S.φ ⟨j, hj⟩ * e * (S.φ ⟨j, hj⟩)⁻¹) := by
  rw [map_mul, map_mul, map_inv, S.ι_φ]

theorem ι_conj (γ σ : J6.S6) : S.ι (γ * σ * γ⁻¹) = S.ι γ * S.ι σ * (S.ι γ)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

theorem HC_ι {σ τ : J6.S6} (hστ : ∃ γ : J6.S6, γ * σ * γ⁻¹ = τ) : HC (S.ι σ) (S.ι τ) := by
  obtain ⟨γ, rfl⟩ := hστ
  exact ⟨S.ι γ, (S.ι_conj γ σ).symm⟩

theorem HC_tι {σ τ : J6.S6} (hστ : ∃ γ : J6.S6, γ * σ * γ⁻¹ = τ) :
    HC (t * S.ι σ) (t * S.ι τ) := by
  obtain ⟨γ, rfl⟩ := hστ
  refine ⟨S.ι γ, ?_⟩
  rw [S.ι_conj]
  have h1 : S.ι γ * t = t * S.ι γ := S.ι_comm_t γ
  calc S.ι γ * (t * S.ι σ) * (S.ι γ)⁻¹ = (S.ι γ * t) * S.ι σ * (S.ι γ)⁻¹ := by group
    _ = (t * S.ι γ) * S.ι σ * (S.ι γ)⁻¹ := by rw [h1]
    _ = t * (S.ι γ * S.ι σ * (S.ι γ)⁻¹) := by group

end Std

def E0 (b w₀ : H) : Subgroup H := Subgroup.zpowers b ⊔ Subgroup.zpowers w₀

theorem FS79Hyp.zpowers_le_J (h : FS79Hyp b t b₁ b₂ J) {w₀ : H}
    (hw₀ : w₀ ∈ Subgroup.closure ({b₁, b₂} : Set H)) : Subgroup.zpowers w₀ ≤ J :=
  Subgroup.zpowers_le.mpr (h.B₁_le_J hw₀)

theorem FS79Hyp.E0_le_B (h : FS79Hyp b t b₁ b₂ J) {w₀ : H}
    (hw₀ : w₀ ∈ Subgroup.closure ({b₁, b₂} : Set H)) :
    E0 b w₀ ≤ Subgroup.closure ({b, b₁, b₂} : Set H) :=
  sup_le (FS79Hyp.zpowers_le_B b b₁ b₂)
    (Subgroup.zpowers_le.mpr (FS79Hyp.B₁_le_B b b₁ b₂ hw₀))

theorem FS79Hyp.E0_pgroup (h : FS79Hyp b t b₁ b₂ J) {w₀ : H}
    (hw₀ : w₀ ∈ Subgroup.closure ({b₁, b₂} : Set H)) : IsPGroup 3 (E0 b w₀) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE := h.isElemAb_B
  haveI := hE.1
  exact (IsElementaryAbelian.isPGroup 3 _).to_le (h.E0_le_B hw₀)

theorem FS79Hyp.b_comm_of_mem_J (h : FS79Hyp b t b₁ b₂ J) {w : H} (hw : w ∈ J) :
    w * b = b * w := Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hw)

theorem FS79Hyp.E0_card (h : FS79Hyp b t b₁ b₂ J) {w₀ : H}
    (hw₀ : w₀ ∈ Subgroup.closure ({b₁, b₂} : Set H)) (hw₀1 : w₀ ≠ 1) :
    Nat.card (E0 b w₀) = 9 := by
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ c ∈ Subgroup.zpowers w₀, Commute a c := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact Commute.zpow_zpow (Commute.symm
      (show Commute w₀ b from h.b_comm_of_mem_J (h.B₁_le_J hw₀))) k m
  have hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers w₀ = ⊥ := by
    rw [eq_bot_iff, ← h.zpowers_inf_J]
    exact inf_le_inf_left _ (h.zpowers_le_J hw₀)
  have hw3 : w₀ ^ 3 = 1 := h.B_pow_three (FS79Hyp.B₁_le_B b b₁ b₂ hw₀)
  have hord : orderOf w₀ = 3 := orderOf_eq_prime hw3 hw₀1
  unfold E0
  rw [CFSG.card_sup_eq_mul_of_commute _ _ hcomm hdisj, Nat.card_zpowers, Nat.card_zpowers,
    h.ord_b, hord]

theorem FS79Hyp.E0_inf_B₁ (h : FS79Hyp b t b₁ b₂ J) {w₀ x : H}
    (hw₀ : w₀ ∈ Subgroup.closure ({b₁, b₂} : Set H)) (hx : x ∈ E0 b w₀)
    (hxB : x ∈ Subgroup.closure ({b₁, b₂} : Set H)) : x ∈ Subgroup.zpowers w₀ := by
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ c ∈ Subgroup.zpowers w₀, Commute a c := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact Commute.zpow_zpow (Commute.symm
      (show Commute w₀ b from h.b_comm_of_mem_J (h.B₁_le_J hw₀))) k m
  obtain ⟨a, ha, c, hc, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hx
  have hcB : c ∈ Subgroup.closure ({b₁, b₂} : Set H) :=
    Subgroup.zpowers_le.mpr hw₀ hc
  have haB : a ∈ Subgroup.closure ({b₁, b₂} : Set H) := by
    have := Subgroup.mul_mem _ hxB (Subgroup.inv_mem _ hcB)
    simpa using this
  have haJ : a ∈ J := h.B₁_le_J haB
  have : a ∈ Subgroup.zpowers b ⊓ J := ⟨ha, haJ⟩
  rw [h.zpowers_inf_J, Subgroup.mem_bot] at this
  rw [this, one_mul]
  exact hc

end CFSG.RankThree.PartTwo.Sec21.FF81
