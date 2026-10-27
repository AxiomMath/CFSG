module

public import CFSG.Walter.ReeOrder.Ward.PSLWard
public import CFSG.Walter.ReeOrder.Ward.LTable

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG

namespace PSLData

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ} (D : PSLData L q e)

omit [Fintype L] in
theorem exists_conj {x y : L} (h : IsConj y x) : ∃ g : L, g⁻¹ * y * g = x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact ⟨c⁻¹, by rw [inv_inv]; exact hc⟩

theorem val_conj {χ : L → ℂ} (hχ : χ ∈ BlocksIrr L) {x y : L} (h : IsConj y x) : χ y = χ x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc, isClass hχ]

theorem Ro_conj (y : L) (hy : orderOf y ∣ Nat.card D.O) : ∃ g : L, g⁻¹ * y * g ∈ D.O := by
  rcases D.classes y with rfl | ⟨x, hx, hx1, hyx⟩ | ⟨x, hx, hx1, hyx⟩ | ⟨x, hx, hx1, hyx⟩
  · exact ⟨1, by simp only [inv_one, mul_one]; exact D.O.one_mem⟩
  · exfalso
    rw [orderOf_conj hyx, D.U_order x hx hx1] at hy
    exact D.not_p_dvd_O hy
  · obtain ⟨g, hg⟩ := exists_conj hyx
    exact ⟨g, hg ▸ hx⟩
  · exfalso
    rw [orderOf_conj hyx] at hy
    have h2 : orderOf x ∣ Nat.gcd (Nat.card D.O) (Nat.card D.E) :=
      Nat.dvd_gcd hy (D.orderOf_dvd_E hx)
    rw [Nat.Coprime.gcd_eq_one D.coprime_O_E] at h2
    exact hx1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h2))

theorem centralizer_J' (y : L) (hy : y * D.J' = D.J' * y) (hodd : Odd (orderOf y)) :
    y ∈ D.So := by
  set C := Subgroup.centralizer ({D.J'} : Set L) with hCdef
  have hEC : D.E ≤ C := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (D.E_comm hx D.J'_mem)
  have hC : Nat.card C = 2 * Nat.card D.E := D.E_centralizer D.J' D.J'_mem D.orderOf_J'
  have hidx : (D.E.subgroupOf C).index = 2 := by
    have h1 := (D.E.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, hC] at h1
    have hE : 0 < Nat.card D.E := Nat.card_pos
    rw [mul_comm 2] at h1
    exact Nat.eq_of_mul_eq_mul_left hE h1
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hy
  have hsq : (⟨y, hyC⟩ : C) ^ 2 ∈ D.E.subgroupOf C := Subgroup.sq_mem_of_index_two hidx _
  have hy2 : y ^ 2 ∈ D.E := by
    rw [Subgroup.mem_subgroupOf] at hsq
    exact hsq
  obtain ⟨k, hk⟩ := hodd
  have hyE : y ∈ D.E := by
    have : y = (y ^ 2) ^ (k + 1) := by
      calc y = y * y ^ (2 * k + 1) := by rw [← hk, pow_orderOf_eq_one, mul_one]
        _ = (y ^ 2) ^ (k + 1) := by
          rw [← pow_succ', ← pow_mul]
          congr 1
    rw [this]
    exact Subgroup.pow_mem _ hy2 _
  exact D.mem_So_of_odd hyE ⟨k, hk⟩

theorem involution_conj (y : L) (hy : orderOf y = 2) : ∃ g : L, g⁻¹ * y * g = D.J' := by
  rcases D.classes y with rfl | ⟨x, hx, hx1, hyx⟩ | ⟨x, hx, hx1, hyx⟩ | ⟨x, hx, hx1, hyx⟩
  · rw [orderOf_one] at hy
    omega
  · exfalso
    have := D.odd_of_mem_U hx hx1
    rw [← orderOf_conj hyx, hy] at this
    exact absurd this (by decide)
  · exfalso
    have := D.odd_of_mem_O hx
    rw [← orderOf_conj hyx, hy] at this
    exact absurd this (by decide)
  · obtain ⟨g, hg⟩ := exists_conj hyx
    refine ⟨g, ?_⟩
    rw [hg]
    exact D.eq_J'_of_orderOf_two hx (by rw [← orderOf_conj hyx, hy])

theorem even_conj (y : L) (hy : Even (orderOf y)) :
    ∃ g : L, ∃ ρ ∈ D.So, g⁻¹ * y * g = D.J' * ρ := by
  rcases D.classes y with rfl | ⟨x, hx, hx1, hyx⟩ | ⟨x, hx, hx1, hyx⟩ | ⟨x, hx, hx1, hyx⟩
  · rw [orderOf_one] at hy
    exact absurd hy (by decide)
  · exfalso
    rw [orderOf_conj hyx] at hy
    exact (Nat.not_even_iff_odd.mpr (D.odd_of_mem_U hx hx1)) hy
  · exfalso
    rw [orderOf_conj hyx] at hy
    exact (Nat.not_even_iff_odd.mpr (D.odd_of_mem_O hx)) hy
  · obtain ⟨g, hg⟩ := exists_conj hyx
    rcases D.mem_E_cases hx with hxS | ⟨ρ, hρ, hxρ⟩
    · exfalso
      rw [orderOf_conj hyx] at hy
      exact (Nat.not_even_iff_odd.mpr (D.odd_of_mem_So hxS)) hy
    · exact ⟨g, ρ, hρ, by rw [hg, hxρ]⟩

theorem odd_classes (y : L) (hy : Odd (orderOf y)) : y = 1 ∨
    (∃ g : L, g⁻¹ * y * g ∈ D.O ∧ g⁻¹ * y * g ≠ 1) ∨
    (∃ g : L, g⁻¹ * y * g ∈ D.So ∧ g⁻¹ * y * g ≠ 1) ∨
    (D.ηp y + D.ηm y = e ∧ D.St y = 0 ∧ (∀ θ ∈ D.RFam, θ y = -e) ∧
      ∀ θ ∈ D.SFam, θ y = e) := by
  rcases D.classes y with rfl | ⟨x, hx, hx1, hyx⟩ | ⟨x, hx, hx1, hyx⟩ | ⟨x, hx, hx1, hyx⟩
  · exact Or.inl rfl
  · right; right; right
    refine ⟨by rw [val_conj D.ηp_mem hyx, val_conj D.ηm_mem hyx]; exact D.η_U x hx hx1,
      by rw [val_conj D.St_mem hyx]; exact D.St_U x hx hx1, fun θ hθ => ?_, fun θ hθ => ?_⟩
    · rw [val_conj (D.R_mem hθ) hyx]
      obtain ⟨α, -, rfl⟩ := (D.mem_RFam θ).mp hθ
      exact D.XO_U α x hx hx1
    · rw [val_conj (D.S_mem hθ) hyx]
      obtain ⟨β, -, rfl⟩ := (D.mem_SFam θ).mp hθ
      exact D.XE_U β x hx hx1
  · right; left
    obtain ⟨g, hg⟩ := exists_conj hyx
    exact ⟨g, hg ▸ hx, hg ▸ hx1⟩
  · right; right; left
    obtain ⟨g, hg⟩ := exists_conj hyx
    have hxS : x ∈ D.So := D.mem_So_of_odd hx (by rw [← orderOf_conj hyx]; exact hy)
    exact ⟨g, hg ▸ hxS, hg ▸ hx1⟩

theorem χ₀_real (x : D.E) : starRingEnd ℂ (D.χ₀ x : ℂ) = D.χ₀ x := by
  rcases units_sq_eq_one (D.χ₀_sq_apply x) with h | h <;> rw [h] <;> simp

theorem conj_St : starRingEnd ℂ ∘ D.St = D.St := by
  have hc := isClass D.St_mem
  refine D.eq_of_classes (conj_comp_isClass hc) hc ?_ ?_ ?_ ?_
  · simp [D.St_one]
  · intro x hx hx1
    simp [D.St_U x hx hx1]
  · intro x hx hx1
    simp [D.St_O x hx hx1]
  · intro x hx hx1
    simp [D.St_E x hx hx1]

theorem conj_R {θ : L → ℂ} (hθ : θ ∈ D.RFam) : starRingEnd ℂ ∘ θ = θ := by
  have hc := isClass (D.R_mem hθ)
  obtain ⟨α, -, rfl⟩ := (D.mem_RFam θ).mp hθ
  refine D.eq_of_classes (conj_comp_isClass hc) hc ?_ ?_ ?_ ?_
  · simp [D.XO_one α]
  · intro x hx hx1
    simp [D.XO_U α x hx hx1]
  · intro x hx hx1
    rw [Function.comp_apply, D.XO_O α x hx hx1, map_mul, conj_sym]
    simp
  · intro x hx hx1
    simp [D.XO_E α x hx hx1]

theorem conj_S {θ : L → ℂ} (hθ : θ ∈ D.SFam) : starRingEnd ℂ ∘ θ = θ := by
  have hc := isClass (D.S_mem hθ)
  obtain ⟨β, -, rfl⟩ := (D.mem_SFam θ).mp hθ
  refine D.eq_of_classes (conj_comp_isClass hc) hc ?_ ?_ ?_ ?_
  · simp [D.XE_one β]
  · intro x hx hx1
    simp [D.XE_U β x hx hx1]
  · intro x hx hx1
    simp [D.XE_O β x hx hx1]
  · intro x hx hx1
    rw [Function.comp_apply, D.XE_E β x hx hx1, map_mul, conj_sym]
    simp

theorem conj_ηp' : starRingEnd ℂ ∘ D.ηp = if e = -1 then D.ηm else D.ηp := by
  have hp := isClass D.ηp_mem
  have hm := isClass D.ηm_mem
  have hE : ∀ x ∈ D.E, x ≠ 1 → (starRingEnd ℂ ∘ D.ηp) x = D.ηm x := by
    intro x hx hx1
    rw [Function.comp_apply, D.ηp_E x hx hx1, D.ηm_E x hx hx1, map_mul, D.χ₀_real]
    simp
  have hEp : ∀ x ∈ D.E, x ≠ 1 → (starRingEnd ℂ ∘ D.ηp) x = D.ηp x := by
    intro x hx hx1
    rw [Function.comp_apply, D.ηp_E x hx hx1, map_mul, D.χ₀_real]
    simp
  by_cases he : e = -1
  · rw [ite_eq_left he]
    refine D.eq_of_classes (conj_comp_isClass hp) hm ?_ ?_ ?_ hE
    · rw [Function.comp_apply, D.ηp_one, D.ηm_one, map_div₀, map_add, map_natCast,
        map_intCast, map_ofNat]
    · intro x hx hx1
      rw [Function.comp_apply, D.conj_ηp x hx hx1, ite_eq_left he]
    · intro x hx hx1
      simp [D.ηp_O x hx hx1, D.ηm_O x hx hx1]
  · rw [ite_eq_right he]
    refine D.eq_of_classes (conj_comp_isClass hp) hp ?_ ?_ ?_ hEp
    · rw [Function.comp_apply, D.ηp_one, map_div₀, map_add, map_natCast, map_intCast,
        map_ofNat]
    · intro x hx hx1
      rw [Function.comp_apply, D.conj_ηp x hx hx1, ite_eq_right he]
    · intro x hx hx1
      simp [D.ηp_O x hx hx1]

theorem conj_ηm' : starRingEnd ℂ ∘ D.ηm = if e = -1 then D.ηp else D.ηm := by
  have hp := isClass D.ηp_mem
  have hm := isClass D.ηm_mem
  have hE : ∀ x ∈ D.E, x ≠ 1 → (starRingEnd ℂ ∘ D.ηm) x = D.ηp x := by
    intro x hx hx1
    rw [Function.comp_apply, D.ηp_E x hx hx1, D.ηm_E x hx hx1, map_mul, D.χ₀_real]
    simp
  have hEm : ∀ x ∈ D.E, x ≠ 1 → (starRingEnd ℂ ∘ D.ηm) x = D.ηm x := by
    intro x hx hx1
    rw [Function.comp_apply, D.ηm_E x hx hx1, map_mul, D.χ₀_real]
    simp
  by_cases he : e = -1
  · rw [ite_eq_left he]
    refine D.eq_of_classes (conj_comp_isClass hm) hp ?_ ?_ ?_ hE
    · rw [Function.comp_apply, D.ηp_one, D.ηm_one, map_div₀, map_add, map_natCast,
        map_intCast, map_ofNat]
    · intro x hx hx1
      rw [Function.comp_apply, D.conj_ηm x hx hx1, ite_eq_left he]
    · intro x hx hx1
      simp [D.ηp_O x hx hx1, D.ηm_O x hx hx1]
  · rw [ite_eq_right he]
    refine D.eq_of_classes (conj_comp_isClass hm) hm ?_ ?_ ?_ hEm
    · rw [Function.comp_apply, D.ηm_one, map_div₀, map_add, map_natCast, map_intCast,
        map_ofNat]
    · intro x hx hx1
      rw [Function.comp_apply, D.conj_ηm x hx hx1, ite_eq_right he]
    · intro x hx hx1
      simp [D.ηm_O x hx hx1]

theorem galois (N : ℕ) (hN : 0 < N) : ∃ k : ℕ, k.Coprime N ∧ (fun y => D.ηp (y ^ k)) = D.ηm ∧
    (fun y => D.ηm (y ^ k)) = D.ηp ∧ (fun y => D.St (y ^ k)) = D.St := by
  obtain ⟨k, hk, hU⟩ := D.galois_U (N * (2 * Nat.card L))
    (Nat.mul_pos hN (Nat.mul_pos two_pos Nat.card_pos))
  have hkN : k.Coprime N := hk.coprime_dvd_right (dvd_mul_right _ _)
  have hk2 : k.Coprime 2 := hk.coprime_dvd_right
    (Dvd.dvd.mul_left (dvd_mul_right 2 _) _)
  have hkL : k.Coprime (Nat.card L) := hk.coprime_dvd_right
    (Dvd.dvd.mul_left (dvd_mul_left _ 2) _)
  have hodd : Odd k := Nat.coprime_two_right.mp hk2
  have hne : ∀ x : L, x ≠ 1 → x ^ k ≠ 1 := by
    intro x hx h
    have h2 : orderOf x ∣ Nat.gcd k (Nat.card L) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_natCard x)
    rw [Nat.Coprime.gcd_eq_one hkL] at h2
    exact hx (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h2))
  have hχk : ∀ (x : L) (hx : x ∈ D.E),
      ((D.χ₀ ⟨x ^ k, Subgroup.pow_mem _ hx k⟩ : ℂˣ) : ℂ) = D.χ₀ ⟨x, hx⟩ := by
    intro x hx
    have : (⟨x ^ k, Subgroup.pow_mem _ hx k⟩ : D.E) = ⟨x, hx⟩ ^ k := rfl
    rw [this, map_pow]
    obtain ⟨j, hj⟩ := hodd
    rcases units_sq_eq_one (D.χ₀_sq_apply ⟨x, hx⟩) with h | h <;> rw [h]
    · simp
    · rw [hj, pow_succ, pow_mul]
      simp
  have key : ∀ f g : L → ℂ, BlocksIsClassFunction f → BlocksIsClassFunction g → f 1 = g 1 →
      (∀ x ∈ D.U, x ≠ 1 → f (x ^ k) = g x) → (∀ x ∈ D.O, x ≠ 1 → f (x ^ k) = g x) →
      (∀ x ∈ D.E, x ≠ 1 → f (x ^ k) = g x) → (fun y => f (y ^ k)) = g := by
    intro f g hf hg h1 hU' hO' hE'
    refine D.eq_of_classes (f := fun y => f (y ^ k)) (fun a b => ?_) hg (by simp [h1]) hU' hO' hE'
    simp only
    rw [conj_pow, hf]
  have hp := isClass D.ηp_mem
  have hm := isClass D.ηm_mem
  have hS := isClass D.St_mem
  refine ⟨k, hkN, key _ _ hp hm (by rw [D.ηp_one, D.ηm_one]) (fun x hx hx1 => (hU x hx hx1).1)
      (fun x hx hx1 => by
        rw [D.ηp_O _ (Subgroup.pow_mem _ hx k) (hne x hx1), D.ηm_O x hx hx1])
      (fun x hx hx1 => by
        rw [D.ηp_E _ (Subgroup.pow_mem _ hx k) (hne x hx1), D.ηm_E x hx hx1, hχk]),
    key _ _ hm hp (by rw [D.ηp_one, D.ηm_one]) (fun x hx hx1 => (hU x hx hx1).2)
      (fun x hx hx1 => by
        rw [D.ηm_O _ (Subgroup.pow_mem _ hx k) (hne x hx1), D.ηp_O x hx hx1])
      (fun x hx hx1 => by
        rw [D.ηm_E _ (Subgroup.pow_mem _ hx k) (hne x hx1), D.ηp_E x hx hx1, hχk]),
    key _ _ hS hS rfl
      (fun x hx hx1 => by
        rw [D.St_U _ (Subgroup.pow_mem _ hx k) (hne x hx1), D.St_U x hx hx1])
      (fun x hx hx1 => by
        rw [D.St_O _ (Subgroup.pow_mem _ hx k) (hne x hx1), D.St_O x hx hx1])
      (fun x hx hx1 => by
        rw [D.St_E _ (Subgroup.pow_mem _ hx k) (hne x hx1), D.St_E x hx hx1])⟩

@[expose] noncomputable def toWardL : WardL L q e where
  e_eq := D.e_eq
  q_mod := D.q_mod
  q_ge := D.q_ge
  card := D.card
  Ro := D.O
  Ro_cyclic := D.O_cyclic
  Ro_card := D.O_card
  Ro_conj := D.Ro_conj
  Ro_centralizer := D.O_centralizer
  So := D.So
  So_cyclic := by rw [So]; infer_instance
  So_card := by
    rw [D.card_So]
    have h1 := D.E_card
    have h2 := D.card_E_eq
    have h3 : (Nat.card D.E : ℤ) = 2 * D.m := by exact_mod_cast h2
    linarith
  J' := D.J'
  orderOf_J' := D.orderOf_J'
  So_comm := fun ρ hρ => D.E_comm (D.So_le_E hρ) D.J'_mem
  centralizer_J' := D.centralizer_J'
  card_centralizer_J' := by
    rw [D.E_centralizer D.J' D.J'_mem D.orderOf_J']
    have h1 := D.E_card
    push_cast
    linarith
  involution_conj := D.involution_conj
  even_conj := D.even_conj
  θ2 := D.ηp
  θ3 := D.ηm
  θ4 := D.St
  RFam := D.RFam
  SFam := D.SFam
  sbar := D.sbar
  irr := D.irr
  θ2_ne_θ3 := D.ηp_ne_ηm
  deg2 := D.ηp_one
  deg3 := D.ηm_one
  deg4 := D.St_one
  degR := fun θ hθ => by
    obtain ⟨α, -, rfl⟩ := (D.mem_RFam θ).mp hθ
    exact D.XO_one α
  degS := fun θ hθ => by
    obtain ⟨β, -, rfl⟩ := (D.mem_SFam θ).mp hθ
    exact D.XE_one β
  cardR := D.card_RFam
  cardS := D.card_SFam
  sbar_mem := fun θ hθ => D.sbar_mem hθ
  sbar_ne := fun θ hθ => D.sbar_ne hθ
  sbar_sbar := fun θ hθ => D.sbar_sbar hθ
  val_Ro := fun r hr hr1 => ⟨D.ηp_O r hr hr1, D.ηm_O r hr hr1, D.St_O r hr hr1,
    fun θ hθ => by
      obtain ⟨β, -, rfl⟩ := (D.mem_SFam θ).mp hθ
      exact D.XE_O β r hr hr1⟩
  val_So := fun ρ hρ hρ1 => by
    have hE := D.So_le_E hρ
    refine ⟨?_, ?_, D.St_E ρ hE hρ1, fun θ hθ => ?_⟩
    · rw [D.ηp_E ρ hE hρ1, D.χ₀_So hρ]
      simp
    · rw [D.ηm_E ρ hE hρ1, D.χ₀_So hρ]
      simp
    · obtain ⟨α, -, rfl⟩ := (D.mem_RFam θ).mp hθ
      exact D.XO_E α ρ hE hρ1
  val_J'So := fun ρ hρ => by
    have hE : D.J' * ρ ∈ D.E := D.E.mul_mem D.J'_mem (D.So_le_E hρ)
    have h1 := D.J'_mul_ne_one hρ
    have hχ : D.χ₀ ⟨D.J' * ρ, hE⟩ = -1 := by
      have : (⟨D.J' * ρ, hE⟩ : D.E) = D.J'E * ⟨ρ, D.So_le_E hρ⟩ := rfl
      rw [this, map_mul, D.χ₀_J'E, D.χ₀_So hρ, mul_one]
    refine ⟨?_, ?_, D.St_E _ hE h1, fun θ hθ => ?_⟩
    · rw [D.ηp_E _ hE h1, hχ]
      simp
    · rw [D.ηm_E _ hE h1, hχ]
      simp
    · obtain ⟨α, -, rfl⟩ := (D.mem_RFam θ).mp hθ
      exact D.XO_E α _ hE h1
  lam := D.lam
  eps := D.eps
  lam_ne := fun θ hθ => D.lam_ne hθ
  eps_eq := fun θ _ => by
    unfold eps
    split_ifs <;> simp
  lam_sbar := fun θ hθ => D.lam_sbar hθ
  eps_sbar := fun θ hθ => D.eps_sbar hθ
  valS_So := fun θ hθ ρ hρ => D.valS_So hθ ρ hρ
  valS_J'So := fun θ hθ ρ => D.valS_J'So hθ ρ
  lam_surj := D.lam_surj
  lam_inj := fun θ hθ θ' hθ' h => D.lam_inj hθ hθ' h
  odd_classes := D.odd_classes
  unip := D.u
  unip_vals := ⟨D.η_U D.u D.u_mem D.u_ne, D.St_U D.u D.u_mem D.u_ne,
    fun θ hθ => by
      obtain ⟨α, -, rfl⟩ := (D.mem_RFam θ).mp hθ
      exact D.XO_U α D.u D.u_mem D.u_ne,
    fun θ hθ => by
      obtain ⟨β, -, rfl⟩ := (D.mem_SFam θ).mp hθ
      exact D.XE_U β D.u D.u_mem D.u_ne⟩
  unip_not_conj := fun r hr h => by
    by_cases hr1 : r = 1
    · rw [hr1, isConj_one_left] at h
      exact D.u_ne h
    · exact D.U_O D.u D.u_mem D.u_ne r hr hr1 h
  conj_θ2 := D.conj_ηp'
  conj_θ3 := D.conj_ηm'
  conj_θ4 := D.conj_St
  conj_R := fun θ hθ => D.conj_R hθ
  conj_S := fun θ hθ => D.conj_S hθ
  galois := D.galois
  principal := D.principal

end PSLData

end CFSG.Walter.Ward
