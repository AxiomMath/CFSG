module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationNineK
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTenModel

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

@[expose] def pt (ℓ : Bool) (i : Fin 5) : G := E.ι (ptm ℓ i)

@[expose] def Frame (ℓ : Bool) : Prop := E.zK = E.ι '' ↑(Yset ℓ (!ℓ))

@[expose] def Acts (ℓ : Bool) (k : G) (σ : Equiv.Perm (Fin 5)) : Prop :=
  ∀ i : Fin 5, k * E.pt ℓ i * k⁻¹ = E.pt ℓ (σ i)

@[expose] def e₁ : G := E.ι e1

@[expose] def u₁ : G := E.ι u1

@[expose] def E₀ : Subgroup G := E0h.map E.ι

@[expose] def W (ℓ : Bool) : Subgroup G := (Wm ℓ).map E.ι

theorem pt_mem_B (ℓ : Bool) (i : Fin 5) : E.pt ℓ i ∈ E.B :=
  Subgroup.mem_map_of_mem _ (ptm_mem_A2 ℓ i)

theorem pt_sq (ℓ : Bool) (i : Fin 5) : E.pt ℓ i * E.pt ℓ i = 1 := by
  show E.ι (ptm ℓ i) * E.ι (ptm ℓ i) = 1
  rw [← map_mul, ptm_sq, map_one]

theorem pt_comm (ℓ : Bool) (i j : Fin 5) : E.pt ℓ i * E.pt ℓ j = E.pt ℓ j * E.pt ℓ i := by
  show E.ι (ptm ℓ i) * E.ι (ptm ℓ j) = E.ι (ptm ℓ j) * E.ι (ptm ℓ i)
  rw [← map_mul, ← map_mul, ptm_comm]

theorem pt_inj {ℓ : Bool} {i j : Fin 5} (h : E.pt ℓ i = E.pt ℓ j) : i = j :=
  ptm_inj ℓ i j (E.injective h)

theorem pt_zero (ℓ : Bool) : E.pt ℓ 0 = E.z := by
  show E.ι (ptm ℓ 0) = E.ι z0
  rw [ptm_zero]

theorem pt_one_two (ℓ : Bool) : E.pt ℓ 1 * E.pt ℓ 2 = E.t := by
  show E.ι (ptm ℓ 1) * E.ι (ptm ℓ 2) = E.ι t0
  rw [← map_mul, ptm_one_two]

theorem pt_mul_inj {ℓ : Bool} {i j k l : Fin 5}
    (h : E.pt ℓ i * E.pt ℓ j = E.pt ℓ k * E.pt ℓ l) :
    ptm ℓ i * ptm ℓ j = ptm ℓ k * ptm ℓ l := by
  apply E.injective
  rw [map_mul, map_mul]
  exact h

theorem sq_of_mem_B {b : G} (hb : b ∈ E.B) : b * b = 1 := by
  obtain ⟨w, hw, rfl⟩ := hb
  rw [← map_mul, A2_sq w hw, map_one]

theorem B_cases (ℓ : Bool) {β : G} (hβ : β ∈ E.B) :
    β = 1 ∨ (∃ i : Fin 5, β = E.pt ℓ i) ∨ ∃ i j : Fin 5, i < j ∧ β = E.pt ℓ i * E.pt ℓ j := by
  obtain ⟨w, hw, rfl⟩ := hβ
  rcases A2_cases ℓ w hw with h | ⟨i, h⟩ | ⟨i, j, hij, h⟩
  · left
    rw [h, map_one]
  · right
    left
    exact ⟨i, by rw [h]; rfl⟩
  · right
    right
    exact ⟨i, j, hij, by rw [h, map_mul]; rfl⟩

theorem mem_W_iff {ℓ : Bool} {x : G} : x ∈ E.W ℓ ↔
    x = 1 ∨ x = E.pt ℓ 3 * E.pt ℓ 4 ∨ x = E.pt ℓ 0 * E.pt ℓ 3 ∨ x = E.pt ℓ 0 * E.pt ℓ 4 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases mem_Wm_iff.1 hw with h | h | h | h
    · left
      rw [h, map_one]
    · right
      left
      rw [h, map_mul]
      rfl
    · right
      right
      left
      rw [h, map_mul]
      rfl
    · right
      right
      right
      rw [h, map_mul]
      rfl
  · rintro (h | h | h | h)
    · rw [h]
      exact one_mem _
    · refine ⟨ptm ℓ 3 * ptm ℓ 4, mem_Wm_iff.2 (Or.inr (Or.inl rfl)), ?_⟩
      rw [h, map_mul]
      rfl
    · refine ⟨ptm ℓ 0 * ptm ℓ 3, mem_Wm_iff.2 (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
      rw [h, map_mul]
      rfl
    · refine ⟨ptm ℓ 0 * ptm ℓ 4, mem_Wm_iff.2 (Or.inr (Or.inr (Or.inr rfl))), ?_⟩
      rw [h, map_mul]
      rfl

theorem W_le_B (ℓ : Bool) : E.W ℓ ≤ E.B :=
  Subgroup.map_mono (Wm_le_A2 ℓ)

theorem card_W (ℓ : Bool) : Nat.card (E.W ℓ) = 4 := by
  rw [W, Subgroup.card_map_of_injective E.injective, card_Wm]

theorem mem_E₀_iff {x : G} : x ∈ E.E₀ ↔ x = 1 ∨ x = E.t ∨ x = E.e₁ ∨ x = E.e₁ * E.t := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases E0h_cases w hw with h | h | h | h
    · left
      rw [h, map_one]
    · right
      left
      rw [h]
      rfl
    · right
      right
      left
      rw [h]
      rfl
    · right
      right
      right
      rw [h, map_mul]
      rfl
  · rintro (h | h | h | h)
    · rw [h]
      exact one_mem _
    · exact ⟨t0, t0_mem_E0h, h.symm⟩
    · exact ⟨e1, e1_mem_E0h, h.symm⟩
    · exact ⟨e1 * t0, E0h.mul_mem e1_mem_E0h t0_mem_E0h, by rw [h, map_mul]; rfl⟩

theorem acts_one {ℓ : Bool} : E.Acts ℓ 1 1 := fun i => by simp

theorem acts_mul {ℓ : Bool} {k k' : G} {σ σ' : Equiv.Perm (Fin 5)} (h : E.Acts ℓ k σ)
    (h' : E.Acts ℓ k' σ') : E.Acts ℓ (k * k') (σ * σ') := by
  intro i
  calc k * k' * E.pt ℓ i * (k * k')⁻¹ = k * (k' * E.pt ℓ i * k'⁻¹) * k⁻¹ := by group
    _ = k * E.pt ℓ (σ' i) * k⁻¹ := by rw [h' i]
    _ = E.pt ℓ (σ (σ' i)) := h _

theorem acts_inv {ℓ : Bool} {k : G} {σ : Equiv.Perm (Fin 5)} (h : E.Acts ℓ k σ) :
    E.Acts ℓ k⁻¹ σ⁻¹ := by
  intro i
  have h1 := h (σ⁻¹ i)
  have e1 : σ (σ⁻¹ i) = i := by simp
  rw [e1] at h1
  calc k⁻¹ * E.pt ℓ i * k⁻¹⁻¹ = k⁻¹ * (k * E.pt ℓ (σ⁻¹ i) * k⁻¹) * k⁻¹⁻¹ := by rw [h1]
    _ = E.pt ℓ (σ⁻¹ i) := by group

theorem acts_unique {ℓ : Bool} {k : G} {σ σ' : Equiv.Perm (Fin 5)} (h : E.Acts ℓ k σ)
    (h' : E.Acts ℓ k σ') : σ = σ' := by
  exact Equiv.ext fun i => E.pt_inj (ℓ := ℓ) ((h i).symm.trans (h' i))

theorem acts_conj_pair {ℓ : Bool} {k : G} {σ : Equiv.Perm (Fin 5)} (h : E.Acts ℓ k σ)
    (i j : Fin 5) : k * (E.pt ℓ i * E.pt ℓ j) * k⁻¹ = E.pt ℓ (σ i) * E.pt ℓ (σ j) := by
  calc k * (E.pt ℓ i * E.pt ℓ j) * k⁻¹ = (k * E.pt ℓ i * k⁻¹) * (k * E.pt ℓ j * k⁻¹) := by
        group
    _ = E.pt ℓ (σ i) * E.pt ℓ (σ j) := by rw [h i, h j]

theorem mem_B_of_acts_one (hCB : Subgroup.centralizer (E.B : Set G) = E.B) {ℓ : Bool} {k : G}
    (hk : E.Acts ℓ k 1) : k ∈ E.B := by
  rw [← hCB, Subgroup.mem_centralizer_iff]
  intro β hβ
  have hp : ∀ i, E.pt ℓ i * k = k * E.pt ℓ i := fun i => by
    have h := hk i
    have h2 : k * E.pt ℓ i = E.pt ℓ i * k := mul_inv_eq_iff_eq_mul.1 h
    exact h2.symm
  rcases E.B_cases ℓ hβ with rfl | ⟨i, rfl⟩ | ⟨i, j, -, rfl⟩
  · simp
  · exact hp i
  · calc E.pt ℓ i * E.pt ℓ j * k = E.pt ℓ i * (E.pt ℓ j * k) := by group
      _ = E.pt ℓ i * (k * E.pt ℓ j) := by rw [hp j]
      _ = (E.pt ℓ i * k) * E.pt ℓ j := by group
      _ = k * E.pt ℓ i * E.pt ℓ j := by rw [hp i]
      _ = k * (E.pt ℓ i * E.pt ℓ j) := by group

theorem pt_mem_zK {ℓ : Bool} (hF : E.Frame ℓ) (i : Fin 5) : E.pt ℓ i ∈ E.zK := by
  rw [hF]
  exact ⟨ptm ℓ i, (mem_Yset_iff_pt ℓ _).2 ⟨i, rfl⟩, rfl⟩

theorem mem_zK_iff_pt {ℓ : Bool} (hF : E.Frame ℓ) {y : G} :
    y ∈ E.zK ↔ ∃ i : Fin 5, y = E.pt ℓ i := by
  rw [hF]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, rfl⟩ := (mem_Yset_iff_pt ℓ w).1 hw
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨ptm ℓ i, (mem_Yset_iff_pt ℓ _).2 ⟨i, rfl⟩, rfl⟩

theorem exists_acts {ℓ : Bool} (hF : E.Frame ℓ) {k : G} (hk : k ∈ E.K) :
    ∃ σ : Equiv.Perm (Fin 5), E.Acts ℓ k σ := by
  have key : ∀ i : Fin 5, ∃ j : Fin 5, k * E.pt ℓ i * k⁻¹ = E.pt ℓ j := by
    intro i
    have h1 := E.zK_inv (E.pt_mem_zK hF i) (E.K.inv_mem hk)
    rw [inv_inv] at h1
    obtain ⟨j, hj⟩ := (E.mem_zK_iff_pt hF).1 h1
    exact ⟨j, hj⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 : k * E.pt ℓ i * k⁻¹ = k * E.pt ℓ j * k⁻¹ := by rw [hf i, hf j, hij]
    exact E.pt_inj (mul_left_cancel (mul_right_cancel h1))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun i => hf i⟩

theorem exists_frame
    (h : E.zK = {E.z} ∪ ((E.B : Set G) ∩ E.Δ₃) ∨ E.zK = {E.z} ∪ ((E.B : Set G) ∩ E.Δ₅)) :
    ∃ ℓ : Bool, E.Frame ℓ := by
  rcases h with h | h
  · refine ⟨true, ?_⟩
    rw [Frame, h]
    ext y
    constructor
    · rintro (rfl | ⟨⟨w, hwA, rfl⟩, hy⟩)
      · exact ⟨z0, mem_Yset.2 (Or.inl rfl), rfl⟩
      · exact ⟨w, mem_Yset.2 (Or.inr (Or.inl ⟨rfl, hwA, E.mem_Δ₃_iff.1 hy⟩)), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : w ∈ Yset true (!true) := hw
      rcases mem_Yset.1 hw' with rfl | ⟨-, hwA, hD⟩ | ⟨h, -, -⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨Subgroup.mem_map_of_mem _ hwA, E.mem_Δ₃_iff.2 hD⟩
      · exact absurd h (by decide)
  · refine ⟨false, ?_⟩
    rw [Frame, h]
    ext y
    constructor
    · rintro (rfl | ⟨⟨w, hwA, rfl⟩, hy⟩)
      · exact ⟨z0, mem_Yset.2 (Or.inl rfl), rfl⟩
      · exact ⟨w, mem_Yset.2 (Or.inr (Or.inr ⟨rfl, hwA, E.mem_Δ₅_iff.1 hy⟩)), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : w ∈ Yset false (!false) := hw
      rcases mem_Yset.1 hw' with rfl | ⟨h, -, -⟩ | ⟨-, hwA, hD⟩
      · exact Or.inl rfl
      · exact absurd h (by decide)
      · exact Or.inr ⟨Subgroup.mem_map_of_mem _ hwA, E.mem_Δ₅_iff.2 hD⟩

theorem acts_e₁ (ℓ : Bool) : E.Acts ℓ E.e₁ sw12 := fun i => by
  show E.ι e1 * E.ι (ptm ℓ i) * (E.ι e1)⁻¹ = E.ι (ptm ℓ (sw12 i))
  rw [← map_inv, ← map_mul, ← map_mul, e1_act]

theorem acts_u₁ (ℓ : Bool) : E.Acts ℓ E.u₁ sw34 := fun i => by
  show E.ι u1 * E.ι (ptm ℓ i) * (E.ι u1)⁻¹ = E.ι (ptm ℓ (sw34 i))
  rw [← map_inv, ← map_mul, ← map_mul, u1_act]

theorem e₁_u₁ : E.e₁ * E.u₁ = E.u₁ * E.e₁ := by
  show E.ι e1 * E.ι u1 = E.ι u1 * E.ι e1
  rw [← map_mul, ← map_mul, e1_u1]

theorem e₁_transvection {x : G} (hx : x ∈ E.B) :
    E.e₁ * x * E.e₁⁻¹ * x = 1 ∨ E.e₁ * x * E.e₁⁻¹ * x = E.t := by
  obtain ⟨w, hw, rfl⟩ := hx
  rcases e1_transvection w hw with h | h
  · left
    show E.ι e1 * E.ι w * (E.ι e1)⁻¹ * E.ι w = 1
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, h, map_one]
  · right
    show E.ι e1 * E.ι w * (E.ι e1)⁻¹ * E.ι w = E.ι t0
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, h]

theorem exists_c3 [Finite G] {ℓ : Bool} (hF : E.Frame ℓ)
    (hCB : Subgroup.centralizer (E.B : Set G) = E.B) (hK : Nat.card E.K = 1920)
    (ht10 : E.tK.ncard = 10) :
    ∃ c : G, c ∈ E.K ∧ c * E.t = E.t * c ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ E.Acts ℓ c s3 := by
  have h := ncard_conjClass_mul_card E.K E.t
  have hY : Nat.card ↥(E.K ⊓ Subgroup.centralizer ({E.t} : Set G)) = 192 := by
    have h' : E.tK.ncard * Nat.card ↥(E.K ⊓ Subgroup.centralizer ({E.t} : Set G)) =
        Nat.card E.K := h
    rw [ht10, hK] at h'
    omega
  have h3 : 3 ∣ Nat.card ↥(E.K ⊓ Subgroup.centralizer ({E.t} : Set G)) := by
    rw [hY]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c₀, hc₀⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(E.K ⊓ Subgroup.centralizer ({E.t} : Set G))) 3 h3
  have hc3o : orderOf (c₀ : G) = 3 := by
    rw [← Subgroup.orderOf_coe] at hc₀
    exact hc₀
  have hcK : (c₀ : G) ∈ E.K := c₀.2.1
  have hct : (c₀ : G) * E.t = E.t * c₀ := E.mem_Y.1 c₀.2.2
  generalize (c₀ : G) = c at hc3o hcK hct
  have hc3 : c ^ 3 = 1 := c_pow_three hc3o
  have hc1 : c ≠ 1 := c_ne_one hc3o
  obtain ⟨σ, hσ⟩ := E.exists_acts hF hcK
  have hσ3 : σ ^ 3 = 1 := by
    have h3 : E.Acts ℓ (c * c * c) (σ * σ * σ) := E.acts_mul (E.acts_mul hσ hσ) hσ
    have e3 : c * c * c = 1 := by
      calc c * c * c = c ^ 3 := (pow_three' c).symm
        _ = 1 := hc3
    rw [e3] at h3
    have := E.acts_unique h3 E.acts_one
    calc σ ^ 3 = σ * σ * σ := pow_three' σ
      _ = 1 := this
  have hσ12 : (σ 1 = 1 ∧ σ 2 = 2) ∨ (σ 1 = 2 ∧ σ 2 = 1) := by
    have hct' : c * E.t * c⁻¹ = E.t := by
      calc c * E.t * c⁻¹ = E.t * c * c⁻¹ := by rw [hct]
        _ = E.t := by group
    have h12 := E.acts_conj_pair hσ 1 2
    rw [E.pt_one_two ℓ, hct'] at h12
    have h12' : E.pt ℓ (σ 1) * E.pt ℓ (σ 2) = E.pt ℓ 1 * E.pt ℓ 2 := by
      rw [E.pt_one_two ℓ]
      exact h12.symm
    have hne : σ 1 ≠ σ 2 := fun h => by
      have := σ.injective h
      exact absurd this (by decide)
    rcases pair_inj ℓ (σ 1) (σ 2) 1 2 hne (by decide) (E.pt_mul_inj h12') with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h] at hσ
    have hcB := E.mem_B_of_acts_one hCB hσ
    have hsq := E.sq_of_mem_B hcB
    apply hc1
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hc3, hsq]; group
  rcases perm_classify σ hσ3 hσ12 hσ1 with h | h
  · exact ⟨c, hcK, hct, hc3, hc1, h ▸ hσ⟩
  · refine ⟨c⁻¹, E.K.inv_mem hcK, ?_, ?_, ?_, ?_⟩
    · exact (show Commute c E.t from hct).inv_left
    · calc c⁻¹ ^ 3 = (c ^ 3)⁻¹ := by group
        _ = 1 := by rw [hc3]; simp
    · intro h'
      exact hc1 (inv_eq_one.1 h')
    · have := E.acts_inv hσ
      rw [h, inv_inv] at this
      exact this

end Emb

end CFSG.Quasithin.A10
