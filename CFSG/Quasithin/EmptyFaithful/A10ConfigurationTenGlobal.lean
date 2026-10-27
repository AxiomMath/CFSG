module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTenComm
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTenA4

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem e₁_comm_pt {ℓ : Bool} {i : Fin 5} (hi : sw12 i = i) :
    E.e₁ * E.pt ℓ i = E.pt ℓ i * E.e₁ := by
  have h := E.acts_e₁ ℓ i
  rw [hi] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem e₁_comm_W {ℓ : Bool} {w : G} (hw : w ∈ E.W ℓ) : E.e₁ * w = w * E.e₁ := by
  obtain ⟨h0, h3, h4⟩ := sw12_fix
  have c0 : Commute E.e₁ (E.pt ℓ 0) := E.e₁_comm_pt h0
  have c3 : Commute E.e₁ (E.pt ℓ 3) := E.e₁_comm_pt h3
  have c4 : Commute E.e₁ (E.pt ℓ 4) := E.e₁_comm_pt h4
  rcases E.mem_W_iff.1 hw with rfl | rfl | rfl | rfl
  · exact (Commute.one_right E.e₁).eq
  · exact (c3.mul_right c4).eq
  · exact (c0.mul_right c3).eq
  · exact (c0.mul_right c4).eq

theorem W_conj_c {ℓ : Bool} {c : G} (hcs : E.Acts ℓ c s3) {w : G} (hw : w ∈ E.W ℓ) :
    c * w * c⁻¹ ∈ E.W ℓ := by
  rcases E.mem_W_iff.1 hw with rfl | rfl | rfl | rfl
  · simp
  · rw [E.acts_conj_pair hcs 3 4]
    show E.ι (ptm ℓ (s3 3)) * E.ι (ptm ℓ (s3 4)) ∈ (Wm ℓ).map E.ι
    rw [← map_mul]
    exact Subgroup.mem_map_of_mem _ (Wm_s3 ℓ 3 4 (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  · rw [E.acts_conj_pair hcs 0 3]
    show E.ι (ptm ℓ (s3 0)) * E.ι (ptm ℓ (s3 3)) ∈ (Wm ℓ).map E.ι
    rw [← map_mul]
    exact Subgroup.mem_map_of_mem _ (Wm_s3 ℓ 0 3 (Or.inl ⟨rfl, rfl⟩))
  · rw [E.acts_conj_pair hcs 0 4]
    show E.ι (ptm ℓ (s3 0)) * E.ι (ptm ℓ (s3 4)) ∈ (Wm ℓ).map E.ι
    rw [← map_mul]
    exact Subgroup.mem_map_of_mem _ (Wm_s3 ℓ 0 4 (Or.inr (Or.inl ⟨rfl, rfl⟩)))

theorem W_fixed {ℓ : Bool} {c : G} (hcs : E.Acts ℓ c s3) {w : G} (hw : w ∈ E.W ℓ)
    (h : c * w * c⁻¹ = w) : w = 1 := by
  rcases E.mem_W_iff.1 hw with rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    rw [E.acts_conj_pair hcs 3 4] at h
    exact Wm_fixed ℓ 3 4 (Or.inr (Or.inr ⟨rfl, rfl⟩)) (E.injective (by simp only [map_mul]; exact h))
  · exfalso
    rw [E.acts_conj_pair hcs 0 3] at h
    exact Wm_fixed ℓ 0 3 (Or.inl ⟨rfl, rfl⟩) (E.injective (by simp only [map_mul]; exact h))
  · exfalso
    rw [E.acts_conj_pair hcs 0 4] at h
    exact Wm_fixed ℓ 0 4 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (E.injective (by simp only [map_mul]; exact h))

theorem card_B_inf_Q : Nat.card ↥(E.B ⊓ E.Q) = 8 := by
  have h : E.B ⊓ E.Q = (A2 ⊓ Qh : Subgroup Wc).map E.ι := by
    rw [Subgroup.map_inf _ _ E.ι E.injective]
    rfl
  rw [h, Subgroup.card_map_of_injective E.injective, card_A2_inf_Qh]

theorem false_of_bad [Finite G] {ℓ : Bool} {c : G} (hc3 : c ^ 3 = 1) (hcs : E.Acts ℓ c s3)
    (hbad : E.e₁ * c * E.e₁⁻¹ * c⁻¹ = E.pt ℓ 0 * E.pt ℓ 3)
    (hGz : Nat.card E.Gz = 384) (hBle : E.B ≤ E.Gz) (hQle : E.Q ≤ E.Gz)
    (hQn : ∀ g ∈ E.Gz, ∀ q ∈ E.Q, g * q * g⁻¹ ∈ E.Q)
    (hBn : ∀ g ∈ E.Gz, ∀ b ∈ E.B, g * b * g⁻¹ ∈ E.B) : False := by
  obtain ⟨h0, h3, -⟩ := sw12_fix
  have hP0 : E.pt ℓ 0 * E.pt ℓ 0 = 1 := E.pt_sq ℓ 0
  have hX : E.pt ℓ 0 * E.pt ℓ 3 ∈ E.B := E.B.mul_mem (E.pt_mem_B ℓ 0) (E.pt_mem_B ℓ 3)
  have hXX : (E.pt ℓ 0 * E.pt ℓ 3) * (E.pt ℓ 0 * E.pt ℓ 3) = 1 := E.sq_of_mem_B hX
  have hec : E.e₁ * c * E.e₁⁻¹ = (E.pt ℓ 0 * E.pt ℓ 3) * c := by
    calc E.e₁ * c * E.e₁⁻¹ = (E.e₁ * c * E.e₁⁻¹ * c⁻¹) * c := by group
      _ = (E.pt ℓ 0 * E.pt ℓ 3) * c := by rw [hbad]
  have hcom : Commute E.e₁ (E.pt ℓ 0 * E.pt ℓ 3) :=
    (show Commute E.e₁ (E.pt ℓ 0) from E.e₁_comm_pt h0).mul_right
      (show Commute E.e₁ (E.pt ℓ 3) from E.e₁_comm_pt h3)
  have heX : E.e₁ * (E.pt ℓ 0 * E.pt ℓ 3) * E.e₁⁻¹ = E.pt ℓ 0 * E.pt ℓ 3 := by
    rw [hcom.eq]
    group
  have hzc : E.pt ℓ 0 * c * E.pt ℓ 0 = E.pt ℓ 0 * E.pt ℓ 3 * c := by
    have h := hcs 0
    rw [show s3 0 = 3 from s3_apply.1] at h
    calc E.pt ℓ 0 * c * E.pt ℓ 0 = E.pt ℓ 0 * (c * E.pt ℓ 0 * c⁻¹) * c := by group
      _ = E.pt ℓ 0 * E.pt ℓ 3 * c := by rw [h]
  have hpc : E.pt ℓ 0 * c = (E.pt ℓ 0 * c * E.pt ℓ 0) * E.pt ℓ 0 := by
    calc E.pt ℓ 0 * c = E.pt ℓ 0 * c * 1 := (mul_one _).symm
      _ = E.pt ℓ 0 * c * (E.pt ℓ 0 * E.pt ℓ 0) := by rw [hP0]
      _ = (E.pt ℓ 0 * c * E.pt ℓ 0) * E.pt ℓ 0 := (mul_assoc _ _ _).symm
  have hz'c : (E.e₁ * E.pt ℓ 0) * c = c * (E.e₁ * E.pt ℓ 0) := by
    calc (E.e₁ * E.pt ℓ 0) * c = E.e₁ * (E.pt ℓ 0 * c) := by group
      _ = E.e₁ * ((E.pt ℓ 0 * c * E.pt ℓ 0) * E.pt ℓ 0) := by rw [← hpc]
      _ = E.e₁ * ((E.pt ℓ 0 * E.pt ℓ 3 * c) * E.pt ℓ 0) := by rw [hzc]
      _ = (E.e₁ * (E.pt ℓ 0 * E.pt ℓ 3) * E.e₁⁻¹) * (E.e₁ * c * E.e₁⁻¹) * (E.e₁ * E.pt ℓ 0) := by
          group
      _ = (E.pt ℓ 0 * E.pt ℓ 3) * ((E.pt ℓ 0 * E.pt ℓ 3) * c) * (E.e₁ * E.pt ℓ 0) := by
          rw [heX, hec]
      _ = ((E.pt ℓ 0 * E.pt ℓ 3) * (E.pt ℓ 0 * E.pt ℓ 3)) * c * (E.e₁ * E.pt ℓ 0) := by group
      _ = c * (E.e₁ * E.pt ℓ 0) := by rw [hXX, one_mul]
  have hz'W : ∀ w ∈ E.W ℓ, (E.e₁ * E.pt ℓ 0) * w = w * (E.e₁ * E.pt ℓ 0) := by
    intro w hw
    have h1 := E.B_commute (E.pt ℓ 0) (E.pt_mem_B ℓ 0) w (E.W_le_B ℓ hw)
    have h2 := E.e₁_comm_W hw
    calc (E.e₁ * E.pt ℓ 0) * w = E.e₁ * (E.pt ℓ 0 * w) := by group
      _ = E.e₁ * (w * E.pt ℓ 0) := by rw [h1]
      _ = (E.e₁ * w) * E.pt ℓ 0 := by group
      _ = (w * E.e₁) * E.pt ℓ 0 := by rw [h2]
      _ = w * (E.e₁ * E.pt ℓ 0) := by group
  obtain ⟨m, hm1, hm2⟩ := bad_model ℓ
  have hgz : (E.ι m)⁻¹ * E.z * E.ι m = E.e₁ * E.pt ℓ 0 := by
    rw [E.pt_zero]
    have h := congrArg E.ι hm1
    rw [map_mul, map_mul, map_inv, map_mul] at h
    exact h
  have hz' : E.ι m * (E.e₁ * E.pt ℓ 0) * (E.ι m)⁻¹ = E.z := by
    rw [← hgz]
    group
  have hc₀ : E.ι m * c * (E.ι m)⁻¹ ∈ E.Gz := by
    rw [E.mem_Gz]
    calc E.z * (E.ι m * c * (E.ι m)⁻¹)
        = (E.ι m * (E.e₁ * E.pt ℓ 0) * (E.ι m)⁻¹) * (E.ι m * c * (E.ι m)⁻¹) := by rw [hz']
      _ = E.ι m * ((E.e₁ * E.pt ℓ 0) * c) * (E.ι m)⁻¹ := by group
      _ = E.ι m * (c * (E.e₁ * E.pt ℓ 0)) * (E.ι m)⁻¹ := by rw [hz'c]
      _ = (E.ι m * c * (E.ι m)⁻¹) * (E.ι m * (E.e₁ * E.pt ℓ 0) * (E.ι m)⁻¹) := by group
      _ = (E.ι m * c * (E.ι m)⁻¹) * E.z := by rw [hz']
  let W₀ : Subgroup G := (E.W ℓ).map (MulAut.conj (E.ι m)).toMonoidHom
  have hW₀mem : ∀ x, x ∈ W₀ ↔ ∃ w ∈ E.W ℓ, E.ι m * w * (E.ι m)⁻¹ = x := by
    intro x
    simp [W₀, Subgroup.mem_map, MulAut.conj_apply]
  have hW₀le : W₀ ≤ E.Gz := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := (hW₀mem x).1 hx
    rw [E.mem_Gz]
    calc E.z * (E.ι m * w * (E.ι m)⁻¹)
        = (E.ι m * (E.e₁ * E.pt ℓ 0) * (E.ι m)⁻¹) * (E.ι m * w * (E.ι m)⁻¹) := by rw [hz']
      _ = E.ι m * ((E.e₁ * E.pt ℓ 0) * w) * (E.ι m)⁻¹ := by group
      _ = E.ι m * (w * (E.e₁ * E.pt ℓ 0)) * (E.ι m)⁻¹ := by rw [hz'W w hw]
      _ = (E.ι m * w * (E.ι m)⁻¹) * (E.ι m * (E.e₁ * E.pt ℓ 0) * (E.ι m)⁻¹) := by group
      _ = (E.ι m * w * (E.ι m)⁻¹) * E.z := by rw [hz']
  have hW₀card : Nat.card W₀ = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (E.ι m)).injective, E.card_W]
  have hW₀c : ∀ x ∈ W₀, (E.ι m * c * (E.ι m)⁻¹) * x * (E.ι m * c * (E.ι m)⁻¹)⁻¹ ∈ W₀ := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := (hW₀mem x).1 hx
    rw [hW₀mem]
    refine ⟨c * w * c⁻¹, E.W_conj_c hcs hw, ?_⟩
    group
  have hW₀fix : ∀ x ∈ W₀, (E.ι m * c * (E.ι m)⁻¹) * x * (E.ι m * c * (E.ι m)⁻¹)⁻¹ = x → x = 1 := by
    intro x hx hcx
    obtain ⟨w, hw, rfl⟩ := (hW₀mem x).1 hx
    have hcw : c * w * c⁻¹ = w := by
      have h : E.ι m * (c * w * c⁻¹) * (E.ι m)⁻¹ = E.ι m * w * (E.ι m)⁻¹ := by
        rw [← hcx]
        group
      have h2 := mul_left_cancel (mul_right_cancel h)
      exact h2
    have := E.W_fixed hcs hw hcw
    rw [this]
    group
  have hc3' : c * c * c = 1 := by rw [← pow_three']; exact hc3
  have hc₀3 : (E.ι m * c * (E.ι m)⁻¹) ^ 3 = 1 := by
    rw [pow_three']
    calc (E.ι m * c * (E.ι m)⁻¹) * (E.ι m * c * (E.ι m)⁻¹) * (E.ι m * c * (E.ι m)⁻¹)
        = E.ι m * (c * c * c) * (E.ι m)⁻¹ := by group
      _ = 1 := by rw [hc3']; group
  have hΓ : Nat.card E.Gz = 12 * Nat.card E.Q := by rw [hGz, E.card_Q]
  have hB : Nat.card E.B = 2 * Nat.card ↥(E.B ⊓ E.Q) := by rw [E.card_B, E.card_B_inf_Q]
  have hmain := W_le_Q_of_le (Γ := E.Gz) (Q := E.Q) (B := E.B) (W := W₀) hQle hBle hW₀le hQn hBn
    hΓ hB hc₀ hc₀3 hW₀card hW₀c hW₀fix
  apply hm2
  intro w hw
  have hwW : E.ι w ∈ E.W ℓ := ⟨w, mem_Wm.2 hw, rfl⟩
  have hx : E.ι m * E.ι w * (E.ι m)⁻¹ ∈ W₀ := (hW₀mem _).2 ⟨E.ι w, hwW, rfl⟩
  obtain ⟨q, hq, hqeq⟩ := hmain hx
  have : q = m * w * m⁻¹ := E.injective (by rw [hqeq]; simp only [map_mul, map_inv])
  rw [← this]
  exact hq

@[expose] def Through1310 : Prop :=
  ∃ (ℓ : Bool) (c : G), E.Frame ℓ ∧ c ∈ E.K ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ c * E.t = E.t * c ∧
    E.Acts ℓ c s3 ∧ (∀ x ∈ E.E₀, x * c = c * x) ∧ ∀ x ∈ E.E₀, ∀ w ∈ E.W ℓ, x * w = w * x

theorem lemma_13_9_10 [Finite G] (hG : IsSimpleGroup G) (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) : E.Through1310 := by
  obtain ⟨hlt, hGz, hBP, hQP, hQn, hBn, hLam, hCB, hK, hshape, hz5, htK, ht10, hfus⟩ :=
    E.through_13_9_9 hG hEven hT hM
  obtain ⟨ℓ, hF⟩ := E.exists_frame hshape
  obtain ⟨c, hcK, hct, hc3, hc1, hcs⟩ := E.exists_c3 hF hCB hK ht10
  have hcomm : E.e₁ * c = c * E.e₁ := by
    rcases E.commutator_cases hCB hcK hc3 hcs with h | h
    · calc E.e₁ * c = (E.e₁ * c * E.e₁⁻¹ * c⁻¹) * c * E.e₁ := by group
        _ = c * E.e₁ := by rw [h]; group
    · exact (E.false_of_bad hc3 hcs h hGz (hBP.trans (pCoreOf_le 2 E.Gz))
        (hQP.trans (pCoreOf_le 2 E.Gz)) hQn hBn).elim
  refine ⟨ℓ, c, hF, hcK, hc3, hc1, hct, hcs, ?_, ?_⟩
  · intro x hx
    rcases E.mem_E₀_iff.1 hx with rfl | rfl | rfl | rfl
    · simp
    · exact hct.symm
    · exact hcomm
    · calc E.e₁ * E.t * c = E.e₁ * (E.t * c) := by group
        _ = E.e₁ * (c * E.t) := by rw [hct]
        _ = (E.e₁ * c) * E.t := by group
        _ = c * E.e₁ * E.t := by rw [hcomm]
        _ = c * (E.e₁ * E.t) := by group
  · intro x hx w hw
    rcases E.mem_E₀_iff.1 hx with rfl | rfl | rfl | rfl
    · simp
    · exact E.B_commute _ E.t_mem_B _ (E.W_le_B ℓ hw)
    · exact E.e₁_comm_W hw
    · calc E.e₁ * E.t * w = E.e₁ * (E.t * w) := by group
        _ = E.e₁ * (w * E.t) := by rw [E.B_commute _ E.t_mem_B _ (E.W_le_B ℓ hw)]
        _ = (E.e₁ * w) * E.t := by group
        _ = (w * E.e₁) * E.t := by rw [E.e₁_comm_W hw]
        _ = w * (E.e₁ * E.t) := by group

end Emb

end CFSG.Quasithin.A10
