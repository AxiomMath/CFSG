module

public import CFSG.Quasithin.Background.FLc2Rho
public import CFSG.Quasithin.Background.FLc2Min
public import CFSG.Quasithin.Background.FLcR2A

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open

namespace P0Setup

variable {G : Type} [Group G] {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G}
  (D : P0Setup L S UL n W)

include D

theorem exists_parab_of_minimal [Finite G] {H : Subgroup G} (hSH : S ≤ H) (hHX : H ≤ L ⊔ S)
    (hne : H ≠ S) (hmin : ∀ K : Subgroup G, S ≤ K → K ≤ H → K = S ∨ K = H) :
    ∃ a, IsNode n a ∧ H = parab (L ⊔ S) n W a := by
  have hUJ : Ut n ≤ D.Theta H := D.Ut_le_Theta hSH
  have hJne : D.Theta H ≠ Ut n := by
    intro h
    rw [← D.Theta_S] at h
    exact hne (D.eq_of_Theta_eq hSH le_rfl hHX (le_sup_right) h)
  have hJmin : ∀ K : Subgroup (SLt n), Ut n ≤ K → K ≤ D.Theta H → K = Ut n ∨ K = D.Theta H := by
    intro K hUK hKJ
    obtain ⟨H', hSH', hH'X, hH'⟩ := D.exists_Theta_eq hUK
    have hH'H : H' ≤ H := D.le_of_Theta_le hSH hH'X (by rw [hH']; exact hKJ)
    rcases hmin H' hSH' hH'H with h | h
    · left
      rw [← hH', h, D.Theta_S]
    · right
      rw [← hH', h]
  obtain ⟨a, ha, hJ⟩ := exists_node_of_minimal hUJ hJne hJmin
  refine ⟨a, ha, D.eq_of_Theta_eq hSH (D.S_le_parab a) hHX (parab_le _ _ _ _) ?_⟩
  rw [D.Theta_parab a]
  exact hJ

theorem minimal_parab [Finite G] {a : ℕ} (ha : IsNode n a) :
    parab (L ⊔ S) n W a ≠ S ∧ ∀ K : Subgroup G, S ≤ K → K ≤ parab (L ⊔ S) n W a →
      K = S ∨ K = parab (L ⊔ S) n W a := by
  obtain ⟨hne, hmin⟩ := minimal_of_node ha
  have hTh : D.Theta (parab (L ⊔ S) n W a) = QI n (NodesNe n a) := D.Theta_parab a
  refine ⟨fun h => hne ?_, fun K hSK hKP => ?_⟩
  · rw [← hTh, h, D.Theta_S]
  · have hKX : K ≤ L ⊔ S := hKP.trans (parab_le _ _ _ _)
    have h1 : D.Theta K ≤ QI n (NodesNe n a) := by
      rw [← hTh]
      exact D.Theta_mono hKP
    rcases hmin (D.Theta K) (D.Ut_le_Theta hSK) h1 with h | h
    · left
      exact D.eq_of_Theta_eq hSK le_rfl hKX le_sup_right (by rw [h, D.Theta_S])
    · right
      exact D.eq_of_Theta_eq hSK (D.S_le_parab a) hKX (parab_le _ _ _ _) (by rw [h, hTh])

theorem odd_dvd_three_two [Finite G] (hn : 4 ≤ n) {x : G} (hx : x ∈ parab (L ⊔ S) n W 2)
    (hodd : Odd (orderOf x)) : orderOf x ∣ 3 := by
  have hxX : x ∈ L ⊔ S := parab_le _ _ _ _ hx
  set y : ↥(L ⊔ S) := ⟨x, hxX⟩ with hy
  have h1 : D.rho y ∈ QI n (NodesNe n 2) := by
    have : D.rho y ∈ D.Theta (parab (L ⊔ S) n W 2) := ⟨y, hx, rfl⟩
    rwa [D.Theta_parab 2] at this
  have h6 : (D.rho y) ^ 6 ∈ Ut n := pow_six_mem_Ut hn h1
  have h7 : D.rho (y ^ 6) ∈ D.Theta S := by
    rw [map_pow, D.Theta_S]
    exact h6
  have h8 : ((y ^ 6 : ↥(L ⊔ S)) : G) ∈ S := (D.Theta_mem_iff le_rfl _).1 h7
  have h8' : x ^ 6 ∈ S := h8
  obtain ⟨b, hb⟩ := D.S2 ⟨x ^ 6, h8'⟩
  have hb' : (x ^ 6) ^ 2 ^ b = 1 := by
    have := congrArg Subtype.val hb
    simpa using this
  have hdvd : orderOf x ∣ 3 * 2 ^ (b + 1) := by
    apply orderOf_dvd_of_pow_eq_one
    have e : 3 * 2 ^ (b + 1) = 6 * 2 ^ b := by ring
    rw [e, pow_mul]
    exact hb'
  have hcop : Nat.Coprime (orderOf x) (2 ^ (b + 1)) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    obtain ⟨j, hj⟩ := hodd
    omega
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem rank2_a_node [Finite G] {j : ℕ} (hj3 : 3 ≤ j) (hjn : j < n) :
    pCoreOf 2 (oTwoUpper (parab (L ⊔ S) n W j)) ≤ pCoreOf 2 (parab (L ⊔ S) n W 1) := by
  have hN1 : ∀ x ∈ parab (L ⊔ S) n W j, x ∈ Subgroup.normalizer (W 1 : Set G) := fun x hx =>
    (mem_parab.1 hx).2 1 le_rfl (by omega) (by omega)
  have hN2 : ∀ x ∈ parab (L ⊔ S) n W j, x ∈ Subgroup.normalizer (W 2 : Set G) := fun x hx =>
    (mem_parab.1 hx).2 2 (by omega) (by omega) (by omega)
  have hW1c : Nat.card ↥(W 1) = 2 := by
    rw [D.W_card 1 le_rfl (by omega)]
    norm_num
  have hW2c : Nat.card ↥(W 2) = 4 := by
    rw [D.W_card 2 (by norm_num) (by omega)]
    norm_num
  have hY : oTwoUpper (parab (L ⊔ S) n W j) ≤ Subgroup.centralizer (W 2 : Set G) := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    exact odd_mem_centralizer D.W_one_le_two hW1c hW2c (hN1 x hx.1) (hN2 x hx.1) hx.2
  rw [D.pCoreOf_eq]
  exact pCoreOf_oTwoUpper_le (D.pCoreOf_le_S_node j) hY

end P0Setup

end CFSG.Quasithin.FLc
