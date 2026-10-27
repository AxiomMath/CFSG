module

public import CFSG.Walter.ReeOrder.Ward.Fusion
public import CFSG.Walter.ReeOrder.Ward.Endgame

public section

open scoped MatrixGroups

namespace CFSG.Walter.Ward

@[expose] def WardLTable : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (q : ℕ), Fintype.card F = q →
    ringChar F ≠ 2 → 7 ≤ q → (q % 8 = 3 ∨ q % 8 = 5) →
    Nonempty (WardL PSL(2, F) q (wardSign q))

namespace ReeTypeHyp

variable {G : Type} [Group G] [Finite G] (h : ReeTypeHyp G)

theorem card_F : Fintype.card h.F = h.q := by
  rw [Fintype.card_eq_nat_card, GaloisField.card h.p h.f h.f_pos.ne']
  rfl

theorem exists_W
    (hT : WardLTable) : Nonempty (WardL PSL(2, h.F) h.q h.e) :=
  hT h.F h.q h.card_F h.ringChar_ne_two (by have := h.eleven_le_q; omega) h.mod_eight

variable (W : WardL PSL(2, h.F) h.q h.e)

theorem exists_A_W : ∃ A : G, orderOf A = 3 ∧ A⁻¹ * h.J * A = h.κ W.J' ∧
    A⁻¹ * h.κ W.J' * A = h.J * h.κ W.J' := by
  obtain ⟨A, x, hx, hA, h1, h2⟩ := h.exists_A
  obtain ⟨g, hg⟩ := W.involution_conj x hx
  refine ⟨(h.κ g)⁻¹ * A * h.κ g, ?_, ?_, ?_⟩
  · rw [show (h.κ g)⁻¹ * A * h.κ g = (h.κ g)⁻¹ * A * (h.κ g)⁻¹⁻¹ by rw [inv_inv],
      ← MulAut.conj_apply, MulEquiv.orderOf_eq, hA]
  · have hJg : h.J * h.κ g = h.κ g * h.J := (h.κ_comm g).symm
    calc ((h.κ g)⁻¹ * A * h.κ g)⁻¹ * h.J * ((h.κ g)⁻¹ * A * h.κ g)
        = (h.κ g)⁻¹ * A⁻¹ * (h.κ g * h.J * (h.κ g)⁻¹) * A * h.κ g := by group
      _ = (h.κ g)⁻¹ * (A⁻¹ * h.J * A) * h.κ g := by
          rw [← hJg, mul_inv_cancel_right]; group
      _ = h.κ W.J' := by rw [h1, ← hg]; simp only [map_mul, map_inv]
  · have hJg : h.J * h.κ g = h.κ g * h.J := (h.κ_comm g).symm
    calc ((h.κ g)⁻¹ * A * h.κ g)⁻¹ * h.κ W.J' * ((h.κ g)⁻¹ * A * h.κ g)
        = (h.κ g)⁻¹ * (A⁻¹ * h.κ (g * W.J' * g⁻¹) * A) * h.κ g := by
          simp only [map_mul, map_inv]; group
      _ = (h.κ g)⁻¹ * (A⁻¹ * h.κ x * A) * h.κ g := by rw [← hg]; group
      _ = h.J * h.κ W.J' := by
          rw [h2, ← hg, map_mul, map_mul, map_inv, ← mul_assoc, ← mul_assoc,
            show (h.κ g)⁻¹ * h.J = h.J * (h.κ g)⁻¹ by
              rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hJg, mul_assoc, mul_inv_cancel,
                mul_one]]
          group

include W in
theorem odd_card_So : Odd (Nat.card W.So) := by
  have h1 := W.So_card
  have h2 := W.q_mod
  have he := W.e_eq
  exact Nat.odd_iff.mpr (by omega)

theorem A_So {A : G} (hA1 : A⁻¹ * h.J * A = h.κ W.J')
    (hA2 : A⁻¹ * h.κ W.J' * A = h.J * h.κ W.J') {ρ : PSL(2, h.F)} (hρ : ρ ∈ W.So) :
    ∃ ρ' ∈ W.So, A⁻¹ * h.κ ρ * A = h.κ ρ' := by
  set g := A⁻¹ * h.κ ρ * A with hg
  have hJ'2 : W.J' * W.J' = 1 := by
    have := pow_orderOf_eq_one W.J'
    rw [W.orderOf_J', sq] at this
    exact this
  have hρJ' : h.κ ρ * h.κ W.J' = h.κ W.J' * h.κ ρ := by
    rw [← map_mul, ← map_mul, W.So_comm ρ hρ]
  have hc1 : g * h.κ W.J' = h.κ W.J' * g := by
    rw [hg, ← hA1]
    calc A⁻¹ * h.κ ρ * A * (A⁻¹ * h.J * A) = A⁻¹ * (h.κ ρ * h.J) * A := by group
      _ = A⁻¹ * (h.J * h.κ ρ) * A := by rw [h.κ_comm]
      _ = A⁻¹ * h.J * A * (A⁻¹ * h.κ ρ * A) := by group
  have hc2 : g * (h.J * h.κ W.J') = (h.J * h.κ W.J') * g := by
    rw [hg, ← hA2]
    calc A⁻¹ * h.κ ρ * A * (A⁻¹ * h.κ W.J' * A) = A⁻¹ * (h.κ ρ * h.κ W.J') * A := by group
      _ = A⁻¹ * (h.κ W.J' * h.κ ρ) * A := by rw [hρJ']
      _ = A⁻¹ * h.κ W.J' * A * (A⁻¹ * h.κ ρ * A) := by group
  have hJ : h.J = (h.J * h.κ W.J') * h.κ W.J' := by
    rw [mul_assoc, ← map_mul, hJ'2, map_one, mul_one]
  have hcJ : g * h.J = h.J * g := by
    rw [hJ, ← mul_assoc, hc2, mul_assoc, hc1, ← mul_assoc]
  have hodd : Odd (orderOf g) := by
    rw [hg, show A⁻¹ * h.κ ρ * A = A⁻¹ * h.κ ρ * A⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, orderOf_injective h.κ h.κ_injective]
    have hdvd : orderOf ρ ∣ Nat.card W.So := by
      have := orderOf_dvd_natCard (⟨ρ, hρ⟩ : W.So)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat (h.odd_card_So W) hdvd
  obtain ⟨y, hy | hy⟩ := h.centralizer hcJ
  · have hyJ' : y * W.J' = W.J' * y := by
      apply h.κ_injective
      rw [map_mul, map_mul, ← hy]
      exact hc1
    have hyodd : Odd (orderOf y) := by
      rw [← orderOf_injective h.κ h.κ_injective, ← hy]
      exact hodd
    exact ⟨y, W.centralizer_J' y hyJ' hyodd, hy⟩
  · exfalso
    obtain ⟨k, hk⟩ := hodd
    have hpow : g ^ (2 * k + 1) = 1 := by rw [← hk, pow_orderOf_eq_one]
    have hc : Commute h.J (h.κ y) := (h.κ_comm y).symm
    rw [hy, hc.mul_pow, pow_succ, pow_mul, sq, h.J_mul_J, one_pow, one_mul] at hpow
    apply h.κ_ne_J (y ^ (2 * k + 1))
    rw [map_pow]
    calc h.κ y ^ (2 * k + 1) = h.J * (h.J * h.κ y ^ (2 * k + 1)) := by
          rw [← mul_assoc, h.J_mul_J, one_mul]
      _ = h.J := by rw [hpow, mul_one]

theorem not_comm_gen {A : G} (hA : orderOf A = 3) (hA1 : A⁻¹ * h.J * A = h.κ W.J')
    (hA2 : A⁻¹ * h.κ W.J' * A = h.J * h.κ W.J') (s : W.So)
    (hs : ∀ x : W.So, x ∈ Subgroup.zpowers s) : A * h.κ s ≠ h.κ s * A := by
  have hJ'2 : orderOf (h.κ W.J') = 2 := by
    rw [orderOf_injective h.κ h.κ_injective, W.orderOf_J']
  have hJ'J' : h.κ W.J' * h.κ W.J' = 1 := by
    have := pow_orderOf_eq_one (h.κ W.J')
    rw [hJ'2, sq] at this
    exact this
  have hAN := h.mem_normalizer_closure (h.κ_comm W.J').symm hJ'J' hA1 hA2
  refine h.not_commute (h.κ W.J') (h.κ_mem _) hJ'2 (h.κ s) (h.κ_mem _) ?_ ?_ A hA hAN
  · rw [orderOf_injective h.κ h.κ_injective, Subgroup.orderOf_coe,
      orderOf_eq_card_of_forall_mem_zpowers hs]
    have := W.So_card
    have hq : ((h.p ^ h.f : ℕ) : ℤ) = (h.p : ℤ) ^ h.f := by push_cast; ring
    rw [← hq]
    exact this
  · rw [← map_mul, ← map_mul, W.So_comm s s.2]

theorem eq_one_of_cube {n k : ℕ} (hn : n = 3 ∨ n = 5) (h : k * (k * k) ≡ 1 [MOD n]) :
    k ≡ 1 [MOD n] := by
  have hc := ((Nat.mod_modEq k n).mul ((Nat.mod_modEq k n).mul (Nat.mod_modEq k n))).trans h
  have hlt : k % n < n := Nat.mod_lt _ (by omega)
  refine (Nat.mod_modEq k n).symm.trans ?_
  generalize k % n = r at hc hlt ⊢
  rcases hn with rfl | rfl <;> unfold Nat.ModEq at hc ⊢ <;> interval_cases r <;> omega

include W in
theorem q_ge_27 : 27 ≤ h.q := by
  obtain ⟨A, hA, hA1, hA2⟩ := h.exists_A_W W
  obtain ⟨s, hs⟩ := W.So_cyclic.exists_generator
  have hns := h.not_comm_gen W hA hA1 hA2 s hs
  have hos : orderOf (s : PSL(2, h.F)) = Nat.card W.So := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hs]
  by_contra hlt
  push Not at hlt
  have h11 := h.eleven_le_q
  have h8 := h.mod_eight
  have hcard := W.So_card
  have hecase : (h.q % 8 = 3 ∧ h.e = -1) ∨ (h.q % 8 = 5 ∧ h.e = 1) := by
    unfold ReeTypeHyp.e wardSign
    rcases h8 with h8 | h8
    · exact Or.inl ⟨h8, by rw [ite_eq_left h8]⟩
    · exact Or.inr ⟨h8, by rw [ite_eq_right (by omega)]⟩
  have hn : Nat.card W.So = 3 ∨ Nat.card W.So = 5 := by omega
  obtain ⟨ρ', hρ', hAs⟩ := h.A_So W hA1 hA2 s.2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (s : PSL(2, h.F)) ^ k = ρ' := by
    have h1 : (⟨ρ', hρ'⟩ : W.So) ∈ Subgroup.zpowers s := hs _
    rw [← mem_powers_iff_mem_zpowers] at h1
    obtain ⟨k, hk⟩ := h1
    refine ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  set φ : G →* G := (MulAut.conj A⁻¹).toMonoidHom with hφ
  have hφx : ∀ x, φ x = A⁻¹ * x * A := fun x => by simp [hφ]
  have hφs : φ (h.κ s) = h.κ (s ^ k) := by rw [hφx, hAs, ← hk]
  have hφ3 : ∀ x, φ (φ (φ x)) = x := by
    intro x
    rw [hφx, hφx, hφx]
    have hA3 : A * A * A = 1 := by rw [← pow_three', ← hA, pow_orderOf_eq_one]
    calc A⁻¹ * (A⁻¹ * (A⁻¹ * x * A) * A) * A = (A * A * A)⁻¹ * x * (A * A * A) := by group
      _ = x := by rw [hA3, inv_one, one_mul, mul_one]
  have hφpow : ∀ m : ℕ, φ (h.κ ((s : PSL(2, h.F)) ^ m)) =
      h.κ ((s : PSL(2, h.F)) ^ (k * m)) := by
    intro m
    rw [map_pow h.κ, map_pow φ, hφs, ← map_pow h.κ, ← pow_mul]
  have hss : (s : PSL(2, h.F)) ^ (k * (k * k)) = (s : PSL(2, h.F)) ^ 1 := by
    apply h.κ_injective
    have e := hφ3 (h.κ ((s : PSL(2, h.F)) ^ 1))
    rw [hφpow, hφpow, hφpow] at e
    rw [← e]
    simp only [mul_one]
  have hmod : k * (k * k) ≡ 1 [MOD Nat.card W.So] := by
    rw [← hos]
    exact pow_eq_pow_iff_modEq.mp hss
  have hk1 : k ≡ 1 [MOD Nat.card W.So] := eq_one_of_cube hn hmod
  apply hns
  have hsk : (s : PSL(2, h.F)) ^ k = s := by
    rw [← hos] at hk1
    rw [pow_eq_pow_iff_modEq.mpr hk1, pow_one]
  have : A⁻¹ * h.κ s * A = h.κ s := by rw [hAs, ← hk, hsk]
  calc A * h.κ s = A * (A⁻¹ * h.κ s * A) := by rw [this]
    _ = h.κ s * A := by group

theorem normalizer_W {r : PSL(2, h.F)} (hr : r ∈ W.Ro) (hr1 : r ≠ 1) (b : G)
    (hb : b⁻¹ * h.κ r * b ∈ Subgroup.zpowers (h.κ r)) : b * h.J = h.J * b := by
  obtain ⟨R, hR⟩ := W.Ro_cyclic.exists_generator
  have hoR : orderOf (h.κ R) = Nat.card W.Ro := by
    rw [orderOf_injective h.κ h.κ_injective, Subgroup.orderOf_coe,
      orderOf_eq_card_of_forall_mem_zpowers hR]
  have hrR : h.κ r ∈ Subgroup.zpowers (h.κ R) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hR ⟨r, hr⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow, ← Subgroup.coe_zpow, hk]
  have hκr1 : h.κ r ≠ 1 := fun h0 => hr1 (h.κ_injective (by rw [h0, map_one]))
  have hle := h.normalizer_le (h.κ R) (h.κ_mem _) (by
    rw [hoR]
    have := W.Ro_card
    have hq : ((h.p ^ h.f : ℕ) : ℤ) = (h.p : ℤ) ^ h.f := by push_cast; ring
    rw [← hq]
    exact this) (h.κ r) hrR hκr1
  have hbN : b⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers (h.κ r) : Set G) := by
    refine JT.mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have e : (b⁻¹ * h.κ r * b) ^ k = b⁻¹ * h.κ r ^ k * b := by
      rw [show b⁻¹ * h.κ r * b = b⁻¹ * h.κ r * b⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv]
    rw [inv_inv, ← e]
    exact Subgroup.zpow_mem _ hb k
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle hbN)
  have hb' : b ∈ Subgroup.centralizer ({h.J} : Set G) := by
    rw [← inv_inv b]
    exact Subgroup.inv_mem _ (Subgroup.mem_centralizer_singleton_iff.mpr this)
  exact Subgroup.mem_centralizer_singleton_iff.mp hb'

include W in
theorem exists_setup
    [Fintype G] : Nonempty (WardSetup G PSL(2, h.F) h.q h.e) := by
  obtain ⟨A, hA, hA1, hA2⟩ := h.exists_A_W W
  obtain ⟨s, hs⟩ := W.So_cyclic.exists_generator
  exact ⟨{
    W := W
    q_ge := h.q_ge_27 W
    q_pow := ⟨h.p, h.f, Fact.out, rfl⟩
    J := h.J
    J_mul := h.J_mul_J
    J_ne := h.J_ne_one
    κ := h.κ
    κ_inj := h.κ_injective
    κ_comm := h.κ_comm
    J_not_mem := h.κ_ne_J
    centralizer := fun g hg => h.centralizer hg
    involution_conj := fun x hx => h.isConj_J hx
    normalizer := fun _ r hr hr1 b hb => h.normalizer_W W hr hr1 b hb
    A := A
    orderOf_A := hA
    A_J := hA1
    A_J' := hA2
    A_So := fun ρ hρ => h.A_So W hA1 hA2 hρ
    A_not_comm := ⟨s, s.2, h.not_comm_gen W hA hA1 hA2 s hs⟩ }⟩

end ReeTypeHyp

theorem ward_order_of_table
    (hT : WardLTable) {G : Type} [Group G] [Finite G]
    (h : ReeTypeHyp G) :
    h.e = -1 ∧ (∃ k : ℕ, 1 ≤ k ∧ h.q = 3 ^ (2 * k + 1)) ∧
      Nat.card G = h.q ^ 3 * (h.q ^ 3 + 1) * (h.q - 1) := by
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨W⟩ := h.exists_W hT
  obtain ⟨S⟩ := h.exists_setup W
  exact S.order_of_setup

end CFSG.Walter.Ward
