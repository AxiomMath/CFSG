module

public import CFSG.Sporadic.Recognition.JankoWongInvolutionData

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup

@[expose] def jwPermA1 : Perm (Fin 8) := swap 0 6 * swap 1 2

@[expose] def jwPermB1 : Perm (Fin 8) := swap 0 1 * swap 2 6

@[expose] def jwPermA2 : Perm (Fin 8) := swap 3 7 * swap 4 5

@[expose] def jwPermV : Perm (Fin 8) := swap 1 2 * swap 4 5

@[expose] def jwPermV1 : Perm (Fin 8) := swap 4 5 * swap 6 7

@[expose] def jwPerm367 : Perm (Fin 8) := swap 3 6 * swap 6 7

theorem jwPermA1_conj_u : permT⁻¹ * jwPermA1 * permT = jwPermA2 := by
  unfold permT jwPermA1 jwPermA2; decide

theorem jwPermA1_conj_sigma : permA3⁻¹ * jwPermA1 * permA3 = jwPermB1 := by
  unfold permA3 jwPermA1 jwPermB1; decide

theorem jwPermB1_conj_sigma : permA3⁻¹ * jwPermB1 * permA3 = jwPermA1 * jwPermB1 := by
  unfold permA3 jwPermA1 jwPermB1; decide

theorem jwPermV1_mul_A2 : jwPermV1 * jwPermA2 = jwPerm367 := by
  unfold jwPermV1 jwPermA2 jwPerm367; decide

theorem jwPerm367_cube : jwPerm367 ^ 3 = 1 := by unfold jwPerm367; decide

theorem jwPermV1_mul_T_sq : (jwPermV1 * permT) * (jwPermV1 * permT) = jwPermV := by
  unfold permT jwPermV1 jwPermV; decide

theorem jwPermT_inv_conj_permA3 : permT⁻¹ * permA3 * permT = permB3 := by
  unfold permT permA3 permB3; decide

theorem jwPermV_conj_permB3 : jwPermV⁻¹ * permB3 * jwPermV = permB3⁻¹ := by
  unfold jwPermV permB3; decide

theorem jwPermV_conj_permA3 : jwPermV⁻¹ * permA3 * jwPermV = permA3⁻¹ := by
  unfold jwPermV permA3; decide

theorem jwPermV1_conj_permB3 : jwPermV1⁻¹ * permB3 * jwPermV1 = permB3⁻¹ := by
  unfold jwPermV1 permB3; decide

theorem jwPermV1_conj_permA3 : jwPermV1⁻¹ * permA3 * jwPermV1 = permA3 := by
  unfold jwPermV1 permA3; decide

theorem jwPermA1_comm_permB3 : jwPermA1 * permB3 = permB3 * jwPermA1 := by
  unfold jwPermA1 permB3; decide

theorem jwPermV1_comm_permA3 : jwPermV1 * permA3 = permA3 * jwPermV1 := by
  unfold jwPermV1 permA3; decide

theorem cycleType_jwPermB1 : jwPermB1.cycleType = {2, 2} := by
  unfold jwPermB1; exact cycleType_type22_of_card (by decide) (by decide)

theorem cycleType_jwPermA1 : jwPermA1.cycleType = {2, 2} := by
  unfold jwPermA1; exact cycleType_type22_of_card (by decide) (by decide)

theorem cycleType_jwPermA2 : jwPermA2.cycleType = {2, 2} := by
  unfold jwPermA2; exact cycleType_type22_of_card (by decide) (by decide)

theorem cycleType_jwPermV : jwPermV.cycleType = {2, 2} := by
  unfold jwPermV; exact cycleType_type22_of_card (by decide) (by decide)

theorem cycleType_jwPermV1 : jwPermV1.cycleType = {2, 2} := by
  unfold jwPermV1; exact cycleType_type22_of_card (by decide) (by decide)

theorem cycleType_jwPermA1_mul_A2 : (jwPermA1 * jwPermA2).cycleType = {2, 2, 2, 2} := by
  unfold jwPermA1 jwPermA2; exact cycleType_type2222_of_card (by decide) (by decide)

theorem cycleType_jwPermA1_mul_V : (jwPermA1 * jwPermV).cycleType = {2, 2} := by
  unfold jwPermA1 jwPermV; exact cycleType_type22_of_card (by decide) (by decide)

theorem cycleType_jwPermA2_mul_V : (jwPermA2 * jwPermV).cycleType = {2, 2} := by
  unfold jwPermA2 jwPermV; exact cycleType_type22_of_card (by decide) (by decide)

theorem cycleType_permT_mul_V : (permT * jwPermV).cycleType = {2, 2, 2, 2} := by
  unfold permT jwPermV; exact cycleType_type2222_of_card (by decide) (by decide)

theorem sign_jwPermA1 : sign jwPermA1 = 1 := sign_of_type22 cycleType_jwPermA1

theorem sign_jwPermV1 : sign jwPermV1 = 1 := sign_of_type22 cycleType_jwPermV1

structure Sec4HRel {E : Type*} [Group E] (σ₁ u a₁ v v₁ : E) : Prop where
  sigma1_cube : σ₁ ^ 3 = 1
  u_sq : u ^ 2 = 1
  b1_sq : (σ₁⁻¹ * a₁ * σ₁) ^ 2 = a₁ ^ 2
  a2_sq : (u⁻¹ * a₁ * u) ^ 2 = a₁ ^ 2
  v_sq : v ^ 2 = a₁ ^ 2
  v1_sq : v₁ ^ 2 = a₁ ^ 2
  b1_by_sigma1 : σ₁⁻¹ * (σ₁⁻¹ * a₁ * σ₁) * σ₁ = a₁ * (σ₁⁻¹ * a₁ * σ₁)
  a1_by_v : v⁻¹ * a₁ * v = a₁⁻¹
  a2_by_v : v⁻¹ * (u⁻¹ * a₁ * u) * v = (u⁻¹ * a₁ * u)⁻¹
  sigma2_by_v : v⁻¹ * (u⁻¹ * σ₁ * u) * v = (u⁻¹ * σ₁ * u)⁻¹
  sigma1_by_v : v⁻¹ * σ₁ * v = σ₁⁻¹
  a1_a2_comm : a₁ * (u⁻¹ * a₁ * u) = (u⁻¹ * a₁ * u) * a₁
  a1_sigma2_comm : a₁ * (u⁻¹ * σ₁ * u) = (u⁻¹ * σ₁ * u) * a₁
  sigma1_sigma2_comm : σ₁ * (u⁻¹ * σ₁ * u) = (u⁻¹ * σ₁ * u) * σ₁
  v_by_u : u⁻¹ * v * u = v⁻¹
  v1_a2_cube : (v₁ * (u⁻¹ * a₁ * u)) ^ 3 = 1
  v1_u_sq : (v₁ * u) ^ 2 = v
  sigma1_by_v1 : v₁⁻¹ * σ₁ * v₁ = σ₁
  sigma2_by_v1 : v₁⁻¹ * (u⁻¹ * σ₁ * u) * v₁ = (u⁻¹ * σ₁ * u)⁻¹
  a1_sigma1_cube : (a₁ * σ₁) ^ 3 = 1
  a2_sigma2_cube : ((u⁻¹ * a₁ * u) * (u⁻¹ * σ₁ * u)) ^ 3 = 1

theorem Sec4HRel.map {E F : Type*} [Group E] [Group F] (f : E →* F) {σ₁ u a₁ v v₁ : E}
    (h : Sec4HRel σ₁ u a₁ v v₁) : Sec4HRel (f σ₁) (f u) (f a₁) (f v) (f v₁) where
  sigma1_cube := by simpa [map_mul, map_inv, map_pow] using congrArg f h.sigma1_cube
  u_sq := by simpa [map_mul, map_inv, map_pow] using congrArg f h.u_sq
  b1_sq := by simpa [map_mul, map_inv, map_pow] using congrArg f h.b1_sq
  a2_sq := by simpa [map_mul, map_inv, map_pow] using congrArg f h.a2_sq
  v_sq := by simpa [map_mul, map_inv, map_pow] using congrArg f h.v_sq
  v1_sq := by simpa [map_mul, map_inv, map_pow] using congrArg f h.v1_sq
  b1_by_sigma1 := by simpa [map_mul, map_inv, map_pow] using congrArg f h.b1_by_sigma1
  a1_by_v := by simpa [map_mul, map_inv, map_pow] using congrArg f h.a1_by_v
  a2_by_v := by simpa [map_mul, map_inv, map_pow] using congrArg f h.a2_by_v
  sigma2_by_v := by simpa [map_mul, map_inv, map_pow] using congrArg f h.sigma2_by_v
  sigma1_by_v := by simpa [map_mul, map_inv, map_pow] using congrArg f h.sigma1_by_v
  a1_a2_comm := by simpa [map_mul, map_inv, map_pow] using congrArg f h.a1_a2_comm
  a1_sigma2_comm := by simpa [map_mul, map_inv, map_pow] using congrArg f h.a1_sigma2_comm
  sigma1_sigma2_comm := by simpa [map_mul, map_inv, map_pow] using congrArg f h.sigma1_sigma2_comm
  v_by_u := by simpa [map_mul, map_inv, map_pow] using congrArg f h.v_by_u
  v1_a2_cube := by simpa [map_mul, map_inv, map_pow] using congrArg f h.v1_a2_cube
  v1_u_sq := by simpa [map_mul, map_inv, map_pow] using congrArg f h.v1_u_sq
  sigma1_by_v1 := by simpa [map_mul, map_inv, map_pow] using congrArg f h.sigma1_by_v1
  sigma2_by_v1 := by simpa [map_mul, map_inv, map_pow] using congrArg f h.sigma2_by_v1
  a1_sigma1_cube := by simpa [map_mul, map_inv, map_pow] using congrArg f h.a1_sigma1_cube
  a2_sigma2_cube := by simpa [map_mul, map_inv, map_pow] using congrArg f h.a2_sigma2_cube

namespace IsCover8

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 8)} {z : E}

theorem conj_inv_pow (g x : E) (n : ℕ) : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
  simpa using conj_pow (a := g⁻¹) (b := x) (i := n)

theorem conj_mul_z' (h : IsCover8 ρ z) (g w : E) : g⁻¹ * (w * z) * g = g⁻¹ * w * g * z := by
  calc g⁻¹ * (w * z) * g = g⁻¹ * w * (z * g) := by simp only [mul_assoc]
    _ = g⁻¹ * w * (g * z) := by rw [← h.mul_z_comm g]
    _ = g⁻¹ * w * g * z := by simp only [mul_assoc]

theorem z_mul_mul_z (h : IsCover8 ρ z) (w : E) : z * (w * z) = w := by
  rw [h.mul_z_comm w, ← mul_assoc, h.z_mul_z, one_mul]

theorem inv_conj_of_sq_sq_sq (h : IsCover8 ρ z) {a b : E} (ha : a ^ 2 = z) (hb : b ^ 2 = z)
    (hab : (a * b) ^ 2 = z) : b⁻¹ * a * b = a⁻¹ := by
  have e1 := h.anticomm_of_sq ha hb hab
  calc b⁻¹ * a * b = b⁻¹ * (a * b) := by rw [mul_assoc]
    _ = b⁻¹ * (z * (b * a)) := by rw [e1]
    _ = b⁻¹ * (b * z * a) := by rw [h.mul_z_comm b]; simp only [mul_assoc]
    _ = z * a := by group
    _ = a⁻¹ := (h.inv_eq_mul_z_of_sq ha).symm

theorem commute_of_sq_sq_prod_one (h : IsCover8 ρ z) {a b : E} (ha : a ^ 2 = z) (hb : b ^ 2 = z)
    (hab : (a * b) ^ 2 = 1) : a * b = b * a := by
  have h1 : (a * b) * (a * b) = 1 := by rw [← pow_two]; exact hab
  have h2 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [h2, mul_inv_rev, h.inv_eq_mul_z_of_sq ha, h.inv_eq_mul_z_of_sq hb]
  calc z * b * (z * a) = z * (b * z) * a := by simp only [mul_assoc]
    _ = z * (z * b) * a := by rw [h.mul_z_comm b]
    _ = (z * z) * b * a := by simp only [mul_assoc]
    _ = b * a := by rw [h.z_mul_z, one_mul]

theorem cube_of_normalization (h : IsCover8 ρ z) {a s : E} (hs3 : s ^ 3 = 1) (ha2 : a ^ 2 = z)
    (hR : s⁻¹ * (s⁻¹ * a * s) * s = a * (s⁻¹ * a * s)) : (a * s) ^ 3 = 1 := by
  have hsss : s * s * s = 1 := by rw [← pow_three']; exact hs3
  have haa : a * a = z := by rw [← pow_two]; exact ha2
  have e1 : s⁻¹ * s⁻¹ = s := by
    calc s⁻¹ * s⁻¹ = s⁻¹ * s⁻¹ * (s * s * s) := by rw [hsss, mul_one]
      _ = s := by group
  have e2 : s * s = s⁻¹ := by
    calc s * s = (s * s * s) * s⁻¹ := by group
      _ = s⁻¹ := by rw [hsss, one_mul]
  have e3 : s * a * s⁻¹ = a * (s⁻¹ * a * s) := by
    rw [← hR]
    calc s * a * s⁻¹ = (s⁻¹ * s⁻¹) * a * (s * s) := by rw [e1, e2]
      _ = s⁻¹ * (s⁻¹ * a * s) * s := by group
  calc (a * s) ^ 3 = a * (s * a * s⁻¹) * (s * s * a * s) := by rw [pow_three']; group
    _ = a * (a * (s⁻¹ * a * s)) * (s * s * a * s) := by rw [e3]
    _ = a * a * s⁻¹ * a * (s * s * s) * a * s := by group
    _ = a * a * s⁻¹ * (a * a) * s := by rw [hsss]; simp only [mul_one, mul_assoc]
    _ = z * s⁻¹ * z * s := by rw [haa]
    _ = z * (s⁻¹ * z) * s := by simp only [mul_assoc]
    _ = z * (z * s⁻¹) * s := by rw [h.mul_z_comm s⁻¹]
    _ = 1 := by rw [← mul_assoc, h.z_mul_z, one_mul, inv_mul_cancel]

theorem exists_sec4_a₁ (h : IsCover8 ρ z) {σ₁ : E} (hσ : ρ σ₁ = permA3) :
    ∃ a₁ : E, ρ a₁ = jwPermA1 ∧
      σ₁⁻¹ * (σ₁⁻¹ * a₁ * σ₁) * σ₁ = a₁ * (σ₁⁻¹ * a₁ * σ₁) := by
  obtain ⟨x, hx⟩ := h.exists_lift sign_jwPermA1
  have hρ : ρ (σ₁⁻¹ * (σ₁⁻¹ * x * σ₁) * σ₁) = ρ (x * (σ₁⁻¹ * x * σ₁)) := by
    simp only [map_mul, map_inv, hx, hσ]
    rw [jwPermA1_conj_sigma, jwPermB1_conj_sigma]
  rcases h.eq_or_eq_mul_z hρ.symm with h1 | h1
  · exact ⟨x, hx, h1⟩
  · refine ⟨x * z, by rw [h.rho_mul_z, hx], ?_⟩
    calc σ₁⁻¹ * (σ₁⁻¹ * (x * z) * σ₁) * σ₁
        = σ₁⁻¹ * (σ₁⁻¹ * x * σ₁ * z) * σ₁ := by rw [h.conj_mul_z' σ₁ x]
      _ = σ₁⁻¹ * (σ₁⁻¹ * x * σ₁) * σ₁ * z := h.conj_mul_z' σ₁ _
      _ = x * (σ₁⁻¹ * x * σ₁) * z * z := by rw [h1]
      _ = x * (σ₁⁻¹ * x * σ₁) := by rw [mul_assoc, h.z_mul_z, mul_one]
      _ = x * (z * (σ₁⁻¹ * x * σ₁ * z)) := by rw [h.z_mul_mul_z]
      _ = (x * z) * (σ₁⁻¹ * (x * z) * σ₁) := by
        rw [h.conj_mul_z' σ₁ x]; simp only [mul_assoc]

theorem exists_sec4_v₁ (h : IsCover8 ρ z) {a₂ : E} (ha₂ : ρ a₂ = jwPermA2) :
    ∃ v₁ : E, ρ v₁ = jwPermV1 ∧ (v₁ * a₂) ^ 3 = 1 := by
  obtain ⟨y, hy⟩ := h.exists_lift sign_jwPermV1
  have hρ : ρ ((y * a₂) ^ 3) = 1 := by
    rw [map_pow, map_mul, hy, ha₂, jwPermV1_mul_A2]; exact jwPerm367_cube
  rcases h.mem_ker_iff.mp hρ with h1 | h1
  · exact ⟨y, hy, h1⟩
  · refine ⟨y * z, by rw [h.rho_mul_z, hy], ?_⟩
    have e : y * z * a₂ = (y * a₂) * z := by
      rw [mul_assoc, ← h.mul_z_comm a₂, ← mul_assoc]
    have hz3 : z ^ 3 = z := by rw [pow_succ, h.sq_eq_one, one_mul]
    rw [e, Commute.mul_pow (h.mul_z_comm (y * a₂)) 3, h1, hz3, h.z_mul_z]

theorem exists_sec4_lifts (h : IsCover8 ρ z) {σ₁ u : E} (hσ : ρ σ₁ = permA3) (hσ3 : σ₁ ^ 3 = 1)
    (hu : ρ u = permT) (hu2 : u ^ 2 = 1) :
    ∃ a₁ v v₁ : E, ρ a₁ = jwPermA1 ∧ ρ v = jwPermV ∧ ρ v₁ = jwPermV1 ∧ a₁ ^ 2 = z ∧
      Sec4HRel σ₁ u a₁ v v₁ := by
  obtain ⟨a₁, ha₁, hR4⟩ := h.exists_sec4_a₁ hσ
  have ha₂ : ρ (u⁻¹ * a₁ * u) = jwPermA2 := by
    rw [map_mul, map_mul, map_inv, hu, ha₁]; exact jwPermA1_conj_u
  have hb₁ : ρ (σ₁⁻¹ * a₁ * σ₁) = jwPermB1 := by
    rw [map_mul, map_mul, map_inv, hσ, ha₁]; exact jwPermA1_conj_sigma
  have hσ₂ : ρ (u⁻¹ * σ₁ * u) = permB3 := by
    rw [map_mul, map_mul, map_inv, hu, hσ]; exact jwPermT_inv_conj_permA3
  obtain ⟨v₁, hv₁, hv₁a₂⟩ := h.exists_sec4_v₁ ha₂
  have hρv : ρ ((v₁ * u) ^ 2) = jwPermV := by
    rw [map_pow, map_mul, hv₁, hu, pow_two]; exact jwPermV1_mul_T_sq
  have ha1sq : a₁ ^ 2 = z := h.sq_eq_z_of_type22 (by rw [ha₁]; exact cycleType_jwPermA1)
  have ha2sq : (u⁻¹ * a₁ * u) ^ 2 = z :=
    h.sq_eq_z_of_type22 (by rw [ha₂]; exact cycleType_jwPermA2)
  have hb1sq : (σ₁⁻¹ * a₁ * σ₁) ^ 2 = z :=
    h.sq_eq_z_of_type22 (by rw [hb₁]; exact cycleType_jwPermB1)
  have hvsq : ((v₁ * u) ^ 2) ^ 2 = z :=
    h.sq_eq_z_of_type22 (by rw [hρv]; exact cycleType_jwPermV)
  have hv1sq : v₁ ^ 2 = z := h.sq_eq_z_of_type22 (by rw [hv₁]; exact cycleType_jwPermV1)
  have hσ₂3 : (u⁻¹ * σ₁ * u) ^ 3 = 1 := by rw [conj_inv_pow, hσ3]; group
  have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hu2)
  refine ⟨a₁, (v₁ * u) ^ 2, v₁, ha₁, hρv, hv₁, ha1sq, ?_⟩
  set v := (v₁ * u) ^ 2 with hv
  refine ⟨hσ3, hu2, by rw [hb1sq, ha1sq], by rw [ha2sq, ha1sq], by rw [hvsq, ha1sq],
    by rw [hv1sq, ha1sq], hR4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact h.inv_conj_of_sq_sq_sq ha1sq hvsq (h.sq_eq_z_of_type22 (by
      rw [map_mul, ha₁, hρv]; exact cycleType_jwPermA1_mul_V))
  ·
    exact h.inv_conj_of_sq_sq_sq ha2sq hvsq (h.sq_eq_z_of_type22 (by
      rw [map_mul, ha₂, hρv]; exact cycleType_jwPermA2_mul_V))
  ·
    refine h.eq_of_cube_one ?_ (by rw [inv_pow, hσ₂3, inv_one]) ?_
    · rw [conj_inv_pow, hσ₂3]; group
    · simp only [map_mul, map_inv, hρv, hσ, hu]
      rw [jwPermT_inv_conj_permA3]; exact jwPermV_conj_permB3
  ·
    refine h.eq_of_cube_one ?_ (by rw [inv_pow, hσ3, inv_one]) ?_
    · rw [conj_inv_pow, hσ3]; group
    · simp only [map_mul, map_inv, hρv, hσ]; exact jwPermV_conj_permA3
  ·
    exact h.commute_of_sq_sq_prod_one ha1sq ha2sq
      (h.sq_eq_one_of_type2222_lift (by rw [map_mul, ha₁, ha₂]; exact cycleType_jwPermA1_mul_A2))
  ·
    exact h.commute_of_cube hσ₂3 (by rw [ha₁, hσ₂]; exact jwPermA1_comm_permB3)
  ·
    exact h.commute_of_cube hσ₂3 (by rw [hσ, hσ₂]; exact permA3_comm_permB3)
  ·
    have huv : (u * v) ^ 2 = 1 := h.sq_eq_one_of_type2222_lift (by
      rw [map_mul, hu, hρv]; exact cycleType_permT_mul_V)
    have h1 : u * v * (u * v) = 1 := by rw [← pow_two]; exact huv
    rw [hu_inv]
    calc u * v * u = u * v * (u * v) * v⁻¹ := by group
      _ = v⁻¹ := by rw [h1, one_mul]
  · exact hv₁a₂
  · rfl
  ·
    have hc : v₁ * σ₁ = σ₁ * v₁ :=
      h.commute_of_cube hσ3 (by rw [hv₁, hσ]; exact jwPermV1_comm_permA3)
    calc v₁⁻¹ * σ₁ * v₁ = v₁⁻¹ * (σ₁ * v₁) := by rw [mul_assoc]
      _ = v₁⁻¹ * (v₁ * σ₁) := by rw [hc]
      _ = σ₁ := by group
  ·
    refine h.eq_of_cube_one ?_ (by rw [inv_pow, hσ₂3, inv_one]) ?_
    · rw [conj_inv_pow, hσ₂3]; group
    · simp only [map_mul, map_inv, hv₁, hσ, hu]
      rw [jwPermT_inv_conj_permA3]; exact jwPermV1_conj_permB3
  · exact h.cube_of_normalization hσ3 ha1sq hR4
  · have h1 := h.cube_of_normalization hσ3 ha1sq hR4
    have : (u⁻¹ * a₁ * u) * (u⁻¹ * σ₁ * u) = u⁻¹ * (a₁ * σ₁) * u := by group
    rw [this, conj_inv_pow, h1]; group

end IsCover8

end CFSG.Sporadic.Recognition.JankoWong
