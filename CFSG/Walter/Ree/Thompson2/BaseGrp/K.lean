module

public import CFSG.Walter.Ree.Thompson2.BaseGrp.Bruhat

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

open CFSG.Walter.Ward

theorem mul_inv_pow_three {G : Type*} [Group G] {a t : G} (ha : a * a = 1)
    (h : (a * t) ^ 3 = 1) : (a * t⁻¹) ^ 3 = 1 := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have e : a * t⁻¹ = a * (a * t)⁻¹ * a⁻¹ := by
    calc a * t⁻¹ = a * (a * t)⁻¹ * a := by group
      _ = a * (a * t)⁻¹ * a⁻¹ := by rw [hai]
  rw [e, conj_pow, inv_pow, h, inv_one, mul_one, mul_inv_cancel]

namespace Ctx

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k}
variable (C : Ctx G k σ) [Fintype k]

omit [Fintype k] in
theorem exists_A4 :
    ∃ x τ : G, x ∈ C.L ∧ x * x = 1 ∧ x ≠ 1 ∧ τ ∈ C.L ∧ τ ^ 3 = 1 ∧ τ ≠ 1 ∧
    (x * τ) ^ 3 = 1 := by
  have hp := C.p_odd
  have hf := C.h.f_pos
  have h8 : C.h.p ^ C.h.f % 8 = 3 ∨ C.h.p ^ C.h.f % 8 = 5 := Or.inl C.q_mod_eight
  obtain ⟨P2, hP2L, hP2, h4le, -⟩ := W67.PSL2Sub.exists_sylow C.Liso hp hf
  have h4dvd := W67.PSL2Sub.card_dvd_four C.Liso hp hf h8 hP2L hP2
  have h4 : Nat.card P2 = 4 := le_antisymm (Nat.le_of_dvd (by norm_num) h4dvd) h4le
  have hV := W67.PSL2Sub.isKleinFour_of_card C.Liso hp hf h8 hP2L h4
  have h12 := W67.PSL2Sub.card_inf_normalizer C.Liso hp hf h8 hP2L hV
  have hcent := W67.PSL2Sub.inf_centralizer_eq C.Liso hp hf hP2L hV
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨τ, hτ⟩, hτo⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(C.L ⊓ Subgroup.normalizer (P2 : Set G))) 3 (by rw [h12]; norm_num)
  have hτo' : orderOf τ = 3 := by rwa [Subgroup.orderOf_mk] at hτo
  obtain ⟨hτL, hτN⟩ := Subgroup.mem_inf.mp hτ
  have hτ3 : τ ^ 3 = 1 := by rw [← hτo']; exact pow_orderOf_eq_one τ
  have hnc : τ ∉ Subgroup.centralizer (P2 : Set G) := by
    intro hc
    have hmem : τ ∈ C.L ⊓ Subgroup.centralizer (P2 : Set G) := ⟨hτL, hc⟩
    rw [hcent] at hmem
    have := Subgroup.orderOf_dvd_natCard P2 hmem
    rw [hτo', h4] at this
    norm_num at this
  obtain ⟨v, hv, hvτ⟩ : ∃ v ∈ P2, τ * v * τ⁻¹ ≠ v := by
    by_contra hall
    push Not at hall
    apply hnc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := hall v hv
    calc v * τ = τ * v * τ⁻¹ * τ := by rw [this]
      _ = τ * v := by group
  have hv2 : v * v = 1 := by
    let _ : IsKleinFour P2 := hV
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨v, hv⟩ : P2))
  refine ⟨v, τ, hP2L hv, hv2, ?_, hτL, hτ3, ?_, mul_pow_three_of_kleinFour hV hτ3 hτN hv hvτ⟩
  · rintro rfl
    exact hvτ (by group)
  · rintro rfl
    rw [orderOf_one] at hτo'
    omega

omit [Fintype k] in
theorem not_mem_N_of_inv {x : G} {s : kˣ} (hs : s * s ≠ 1)
    (hx : x * C.tor s * x⁻¹ = (C.tor s)⁻¹) : x ∉ C.N := by
  intro hxN
  obtain ⟨n, rfl⟩ := C.exists_ι hxN
  have h : n * ThompsonN.torus σ s * n⁻¹ = (ThompsonN.torus σ s)⁻¹ :=
    C.ι_injective (by rw [map_mul, map_mul, map_inv, map_inv]; exact hx)
  have hκ := congrArg (ThompsonN.kappaHom σ) h
  simp only [map_mul, map_inv] at hκ
  change n.κ * s * n.κ⁻¹ = s⁻¹ at hκ
  rw [mul_comm n.κ, mul_assoc, mul_inv_cancel, mul_one] at hκ
  apply hs
  calc s * s = s⁻¹ * s := by rw [← hκ]
    _ = 1 := inv_mul_cancel s

omit [CharP k 3] in
theorem orderOf_gen : orderOf (gen k) = Fintype.card k - 1 := by
  classical
  rw [orderOf_eq_card_of_forall_mem_zpowers gen_spec, Nat.card_eq_fintype_card,
    Fintype.card_units]

include C in
theorem gen_pow_ne_one
    {m : ℕ} (hm0 : 0 < m) (hm : m ≤ 4) : gen k ^ m ≠ 1 := by
  intro h1
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_gen] at hdvd
  have hk : Fintype.card k = C.h.q := by rw [Fintype.card_eq_nat_card, C.card_k]
  have hq := C.five_lt_q
  have hq8 := C.q_mod_eight
  have := Nat.le_of_dvd hm0 hdvd
  omega

theorem tor_mem_B_or
    (t : kˣ) : C.tor t ∈ C.B ∨ C.J * C.tor t ∈ C.B := by
  obtain ⟨n, -, hk⟩ := C.card_k_eq
  have hsq : ∀ {u : kˣ}, IsSquare (u : k) → C.tor u ∈ C.B := by
    intro u ⟨s, hs⟩
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs
    have : u = Units.mk0 s hs0 ^ 2 := Units.ext (by rw [hs, Units.val_pow_eq_pow_val,
      Units.val_mk0, sq])
    rw [this]
    exact C.tor_sq_mem_B _
  rcases isSquare_or_isSquare_neg hk (t : k) with h | h
  · exact Or.inl (hsq h)
  · right
    rw [C.J_eq_tor, C.tor_mul]
    apply hsq
    simpa using h

theorem exists_K :
    ∃ K : G, K * K = 1 ∧ K ∉ C.N ∧
    (∀ t : kˣ, K⁻¹ * C.tor t * K = C.tor t⁻¹) ∧ (K * C.T) ^ 3 = 1 := by
  obtain ⟨n, hn, hk⟩ := C.card_k_eq
  obtain ⟨w, hw⟩ := JT.exists_torusData_of_isCyclic C.L C.Liso C.h.p_ne_two C.five_lt_q
    (by have := C.q_mod_eight; change C.h.q % 4 = 3; omega) C.B_le_L C.isCyclic_B C.card_B
  have hwinv : ∀ b ∈ C.B, w * b * w⁻¹ = b⁻¹ := hw.inv
  have hwN : w ∉ C.N := by
    apply C.not_mem_N_of_inv (s := gen k ^ 2)
    · rw [← pow_add]; exact C.gen_pow_ne_one (by norm_num) (by norm_num)
    · exact hwinv _ (C.tor_sq_mem_B _)
  obtain ⟨x₀, τ₀, hx₀L, hx₀2, hx₀1, hτ₀L, hτ₀3, hτ₀1, hx₀τ₀⟩ := C.exists_A4
  obtain ⟨y, hyL, hyU⟩ := C.exists_conj_mem_U hτ₀L hτ₀3
  have hx₁L : y * x₀ * y⁻¹ ∈ C.L := C.L.mul_mem (C.L.mul_mem hyL hx₀L) (C.L.inv_mem hyL)
  have hx₁2 : y * x₀ * y⁻¹ * (y * x₀ * y⁻¹) = 1 := by
    rw [show y * x₀ * y⁻¹ * (y * x₀ * y⁻¹) = y * (x₀ * x₀) * y⁻¹ by group, hx₀2]; group
  have hx₁1 : y * x₀ * y⁻¹ ≠ 1 := by
    intro h1; apply hx₀1
    calc x₀ = y⁻¹ * (y * x₀ * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have hx₁τ₁ : (y * x₀ * y⁻¹ * (y * τ₀ * y⁻¹)) ^ 3 = 1 := by
    rw [show y * x₀ * y⁻¹ * (y * τ₀ * y⁻¹) = y * (x₀ * τ₀) * y⁻¹ by group, conj_pow, hx₀τ₀]
    group
  obtain ⟨p, hp, b, hb, hx₁⟩ := C.bruhat_invol hw.w_mem hwN hw.w_mul_self hwinv hx₁L hx₁2 hx₁1
  set τ₁ := y * τ₀ * y⁻¹ with hτ₁
  have hτ₁1 : τ₁ ≠ 1 := by
    intro h1; apply hτ₀1
    calc τ₀ = y⁻¹ * τ₁ * y := by rw [hτ₁]; group
      _ = 1 := by rw [h1]; group
  set K₀ := w * b with hK₀
  have hpτ : p * τ₁ * p⁻¹ = τ₁ := by rw [C.U_comm hp hyU]; group
  have hK₀τ : (K₀ * τ₁) ^ 3 = 1 := by
    have e : K₀ * τ₁ = p⁻¹ * (y * x₀ * y⁻¹ * τ₁) * p := by
      rw [hx₁]
      calc K₀ * τ₁ = p⁻¹ * (p * K₀ * p⁻¹ * (p * τ₁ * p⁻¹)) * p := by group
        _ = p⁻¹ * (p * K₀ * p⁻¹ * τ₁) * p := by rw [hpτ]
    rw [e, show p⁻¹ * (y * x₀ * y⁻¹ * τ₁) * p = p⁻¹ * (y * x₀ * y⁻¹ * τ₁) * p⁻¹⁻¹ by
      rw [inv_inv], conj_pow, hx₁τ₁]
    group
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw.w_mul_self
  have hK₀2 : K₀ * K₀ = 1 := by
    have := hwinv b hb
    calc K₀ * K₀ = (w * b * w⁻¹) * (w * w) * b := by rw [hK₀]; group
      _ = 1 := by rw [this, hw.w_mul_self]; group
  have hK₀L : K₀ ∈ C.L := C.L.mul_mem hw.w_mem (C.B_le_L hb)
  have hK₀inv : ∀ t : kˣ, K₀ * C.tor t * K₀⁻¹ = (C.tor t)⁻¹ := by
    have hB : ∀ c ∈ C.B, K₀ * c * K₀⁻¹ = c⁻¹ := by
      intro c hc
      calc K₀ * c * K₀⁻¹ = w * (b * c * b⁻¹) * w⁻¹ := by rw [hK₀]; group
        _ = w * c * w⁻¹ := by rw [C.B_comm hb hc, mul_inv_cancel_right]
        _ = c⁻¹ := hwinv c hc
    intro t
    rcases C.tor_mem_B_or t with h | h
    · exact hB _ h
    · have hJK : K₀ * C.J = C.J * K₀ := C.commute_J_of_mem_L hK₀L
      have hJt' : C.J * (C.tor t)⁻¹ = (C.tor t)⁻¹ * C.J := by
        rw [C.tor_inv, C.J_eq_tor, C.tor_comm]
      have := hB _ h
      have e1 : K₀ * (C.J * C.tor t) * K₀⁻¹ = C.J * (K₀ * C.tor t * K₀⁻¹) := by
        calc K₀ * (C.J * C.tor t) * K₀⁻¹ = (K₀ * C.J) * C.tor t * K₀⁻¹ := by group
          _ = (C.J * K₀) * C.tor t * K₀⁻¹ := by rw [hJK]
          _ = C.J * (K₀ * C.tor t * K₀⁻¹) := by group
      calc K₀ * C.tor t * K₀⁻¹ = C.J * (C.J * (K₀ * C.tor t * K₀⁻¹)) := by
            rw [← mul_assoc, C.J_mul_J, one_mul]
        _ = C.J * (C.J * C.tor t)⁻¹ := by rw [← e1, this]
        _ = C.J * (C.tor t)⁻¹ * C.J := by rw [mul_inv_rev, C.J_inv, mul_assoc]
        _ = (C.tor t)⁻¹ := by rw [hJt', mul_assoc, C.J_mul_J, mul_one]
  obtain ⟨β, hβ⟩ := C.mem_U.mp hyU
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hτ₁1 (by rw [hβ, pp_zero, map_one])
  have hconjT : ∀ κ : kˣ, (C.tor κ)⁻¹ * C.T * C.tor κ = C.ι (pp σ 0 ((κ : k) * σ κ) 0) := by
    intro κ
    have := torus_conj_pp (σ := σ) κ 0 1 0
    simp only [zero_mul, one_mul] at this
    rw [tor, T, ← map_inv, ← map_mul, ← map_mul, tT, this]
  have hfinal : ∀ (κ : kˣ) (τ' : G), (C.tor κ)⁻¹ * C.T * C.tor κ = τ' → (K₀ * τ') ^ 3 = 1 →
      ∃ K : G, K * K = 1 ∧ K ∉ C.N ∧ (∀ t : kˣ, K⁻¹ * C.tor t * K = C.tor t⁻¹) ∧
        (K * C.T) ^ 3 = 1 := by
    intro κ τ' hτ' h3
    have hr : ∀ t : kˣ, (C.tor κ)⁻¹ * C.tor t * C.tor κ = C.tor t := by
      intro t; rw [mul_assoc, C.tor_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    have hr' : ∀ t : kˣ, C.tor κ * (C.tor t)⁻¹ * (C.tor κ)⁻¹ = (C.tor t)⁻¹ := by
      intro t
      rw [C.tor_inv t, C.tor_comm κ t⁻¹, mul_inv_cancel_right]
    have hKinv : ∀ t : kˣ, C.tor κ * K₀ * (C.tor κ)⁻¹ * C.tor t * (C.tor κ * K₀ * (C.tor κ)⁻¹)⁻¹
        = (C.tor t)⁻¹ := by
      intro t
      calc C.tor κ * K₀ * (C.tor κ)⁻¹ * C.tor t * (C.tor κ * K₀ * (C.tor κ)⁻¹)⁻¹
          = C.tor κ * (K₀ * ((C.tor κ)⁻¹ * C.tor t * C.tor κ) * K₀⁻¹) * (C.tor κ)⁻¹ := by group
        _ = (C.tor t)⁻¹ := by rw [hr, hK₀inv, hr']
    refine ⟨C.tor κ * K₀ * (C.tor κ)⁻¹, ?_, ?_, ?_, ?_⟩
    · rw [show C.tor κ * K₀ * (C.tor κ)⁻¹ * (C.tor κ * K₀ * (C.tor κ)⁻¹) =
        C.tor κ * (K₀ * K₀) * (C.tor κ)⁻¹ by group, hK₀2]
      group
    · apply C.not_mem_N_of_inv (s := gen k) _ (hKinv _)
      rw [← sq]; exact C.gen_pow_ne_one (by norm_num) (by norm_num)
    · intro t
      have hKi : (C.tor κ * K₀ * (C.tor κ)⁻¹)⁻¹ = C.tor κ * K₀ * (C.tor κ)⁻¹ := by
        rw [show (C.tor κ * K₀ * (C.tor κ)⁻¹)⁻¹ = C.tor κ * K₀⁻¹ * (C.tor κ)⁻¹ by group,
          inv_eq_of_mul_eq_one_right hK₀2]
      have := hKinv t
      rw [hKi] at this
      rw [hKi, this, tor, tor, ← map_inv, ← map_inv]
    · rw [show C.tor κ * K₀ * (C.tor κ)⁻¹ * C.T =
        C.tor κ * (K₀ * ((C.tor κ)⁻¹ * C.T * C.tor κ)) * (C.tor κ)⁻¹ by group, hτ', conj_pow,
        h3]
      group
  have hτ₁inv : C.ι (pp σ 0 (-β) 0) = τ₁⁻¹ := by
    rw [hβ, ← map_inv, pp_inv]
    congr 1
    rw [pp_eq_iff]
    refine ⟨by ring, rfl, by ring⟩
  rcases isSquare_or_isSquare_neg hk β with hsq | hsq
  · obtain ⟨κ₀, hκ₀⟩ := exists_sigma_mul_eq hk hn (σ := σ) hsq
    have hκ₀0 : κ₀ ≠ 0 := by rintro rfl; simp at hκ₀; exact hβ0 hκ₀.symm
    refine hfinal (Units.mk0 κ₀ hκ₀0) τ₁ ?_ hK₀τ
    rw [hconjT, Units.val_mk0, mul_comm, hκ₀]
    exact hβ.symm
  · obtain ⟨κ₀, hκ₀⟩ := exists_sigma_mul_eq hk hn (σ := σ) hsq
    have hκ₀0 : κ₀ ≠ 0 := by rintro rfl; simp at hκ₀; exact hβ0 hκ₀
    refine hfinal (Units.mk0 κ₀ hκ₀0) τ₁⁻¹ ?_ (mul_inv_pow_three hK₀2 hK₀τ)
    rw [hconjT, Units.val_mk0, mul_comm, hκ₀]
    exact hτ₁inv

end Ctx

end CFSG.Walter.Ree.T2.BaseGrp
