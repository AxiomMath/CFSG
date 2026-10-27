module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B : Subgroup G}

private theorem sq_comm_of_inv {n x : G} (h : n * x * n⁻¹ = x⁻¹) : n ^ 2 * x = x * n ^ 2 := by
  have hc : n ^ 2 * x * (n ^ 2)⁻¹ = x := by
    have e : n ^ 2 * x * (n ^ 2)⁻¹ = n * (n * x * n⁻¹) * n⁻¹ := by
      simp only [pow_two, mul_inv_rev, mul_assoc]
    rw [e, h]
    have e2 : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group
    rw [e2, h, inv_inv]
  exact mul_inv_eq_iff_eq_mul.1 hc

private theorem sq_comm_of_fix {n x : G} (h : n * x * n⁻¹ = x) : n ^ 2 * x = x * n ^ 2 := by
  have hc : n ^ 2 * x * (n ^ 2)⁻¹ = x := by
    have e : n ^ 2 * x * (n ^ 2)⁻¹ = n * (n * x * n⁻¹) * n⁻¹ := by
      simp only [pow_two, mul_inv_rev, mul_assoc]
    rw [e, h, h]
  exact mul_inv_eq_iff_eq_mul.1 hc

theorem exists_inverting_involution (hs : FF84Sec3 b L B b₁ b₂) (hCB : CenS B = B) :
    ∃ t : G, orderOf t = 2 ∧ t * b * t⁻¹ = b⁻¹ ∧ t * b₁ * t⁻¹ = b₁ ∧ t * b₂ * t⁻¹ = b₂ ∧
      t ∈ Nor B := by
  obtain ⟨n, hnN, hnb, hnb₁, hnb₂⟩ := hs.mono.2.2.2.1
  haveI : IsElementaryAbelian 3 B := hs.mono.1.1
  have hsqB : n ^ 2 ∈ CenS B := by
    have hc : Subgroup.closure ({b, b₁, b₂} : Set G) ≤ Subgroup.centralizer ({n ^ 2} : Set G) := by
      refine (Subgroup.closure_le _).2 ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rcases hx with rfl | rfl | rfl
      · exact (sq_comm_of_inv hnb).symm
      · exact (sq_comm_of_fix hnb₁).symm
      · exact (sq_comm_of_fix hnb₂).symm
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro h hh
    have hh' : h ∈ Subgroup.closure ({b, b₁, b₂} : Set G) := by
      rw [← hs.mono.2.1]; exact hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hc hh')
  have hsqB' : n ^ 2 ∈ B := hCB ▸ hsqB
  have hcube : (n ^ 2) ^ 3 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (n ^ 2) hsqB'
  have h6 : n ^ 6 = 1 := by
    rw [← pow_mul] at hcube
    simpa using hcube
  have hinv : ∀ x : G, n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := fun x => by group
  have hconj : ∀ x : G, n ^ 3 * x * (n ^ 3)⁻¹ = n * (n * (n * x * n⁻¹) * n⁻¹) * n⁻¹ :=
    fun x => by simp only [pow_three, mul_inv_rev, mul_assoc]
  have ht_b : n ^ 3 * b * (n ^ 3)⁻¹ = b⁻¹ := by
    rw [hconj, hnb, hinv, hnb, inv_inv, hnb]
  have ht_b₁ : n ^ 3 * b₁ * (n ^ 3)⁻¹ = b₁ := by
    rw [hconj, hnb₁, hnb₁, hnb₁]
  have ht_b₂ : n ^ 3 * b₂ * (n ^ 3)⁻¹ = b₂ := by
    rw [hconj, hnb₂, hnb₂, hnb₂]
  have ht2 : (n ^ 3) ^ 2 = 1 := by
    rw [← pow_mul]; simpa using h6
  have ht_ne : n ^ 3 ≠ 1 := by
    intro h1
    rw [h1, inv_one, mul_one, one_mul] at ht_b
    have hsq : b ^ 2 = 1 := by
      have : b * b = 1 := by
        calc b * b = b * b⁻¹ := by rw [← ht_b]
          _ = 1 := mul_inv_cancel b
      simpa [pow_two] using this
    have hdvd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rw [hs.hyp.ord] at hdvd
    norm_num at hdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht_ord : orderOf (n ^ 3) = 2 := orderOf_eq_prime ht2 ht_ne
  have ht_N : n ^ 3 ∈ Nor B := (Nor B).pow_mem hnN 3
  exact ⟨n ^ 3, ht_ord, ht_b, ht_b₁, ht_b₂, ht_N⟩

theorem nor_zpowers_eq (hs : FF84Sec3 b L B b₁ b₂)
    {t : G} (ht : t * b * t⁻¹ = b⁻¹) :
    Nor (Subgroup.zpowers b) = Cen b ⊔ Subgroup.zpowers t := by
  have hbord : orderOf b = 3 := hs.hyp.ord
  have hb3 : b ^ 3 = 1 := by rw [← hbord]; exact pow_orderOf_eq_one b
  have hb_ne : b ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hbord
    norm_num at hbord
  have h1 : t * b⁻¹ * t⁻¹ = b := by
    calc t * b⁻¹ * t⁻¹ = (t * b * t⁻¹)⁻¹ := by group
      _ = b := by rw [ht, inv_inv]
  have ht' : t⁻¹ * b * t = b⁻¹ := by
    calc t⁻¹ * b * t = t⁻¹ * (t * b⁻¹ * t⁻¹) * t := by rw [h1]
      _ = b⁻¹ := by group
  have key : ∀ c : G, c * b * c⁻¹ = b → ∀ h : G, h ∈ Subgroup.zpowers b ↔
      c * h * c⁻¹ ∈ Subgroup.zpowers b := by
    intro c hc h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [← conj_zpow, hc]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      have hc' : c⁻¹ * b * c = b := by
        calc c⁻¹ * b * c = c⁻¹ * (c * b * c⁻¹) * c := by rw [hc]
          _ = b := by group
      have e2 : (c⁻¹ * b * c) ^ k = c⁻¹ * b ^ k * c := by
        have := conj_zpow (a := c⁻¹) (b := b) (i := k)
        rwa [inv_inv] at this
      have hh' : h = b ^ k := by
        calc h = c⁻¹ * (c * h * c⁻¹) * c := by group
          _ = c⁻¹ * b ^ k * c := by rw [hk]
          _ = (c⁻¹ * b * c) ^ k := e2.symm
          _ = b ^ k := by rw [hc']
      rw [hh']
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k
  apply le_antisymm
  ·
    intro g hg
    have hgb : g * b * g⁻¹ ∈ Subgroup.zpowers b :=
      (Subgroup.mem_normalizer_iff.1 hg b).1 (Subgroup.mem_zpowers b)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgb
    have hk3 : b ^ (k % 3) = g * b * g⁻¹ := by
      rw [← hk]
      have := zpow_mod_orderOf b k
      rw [hbord] at this
      exact_mod_cast this
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h0 | h1' | h2
    ·
      rw [h0, zpow_zero] at hk3
      exfalso
      apply hb_ne
      calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [← hk3]
        _ = 1 := by group
    ·
      rw [h1', zpow_one] at hk3
      have hcomm : b * g = g * b := by
        calc b * g = (g * b * g⁻¹) * g := by rw [← hk3]
          _ = g * b := by group
      have hmem : g ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm
      exact (le_sup_left : Cen b ≤ Cen b ⊔ Subgroup.zpowers t) hmem
    ·
      have hb2 : b ^ (2 : ℤ) = b⁻¹ := by
        have hbbb : b * b * b = 1 := by
          simpa [pow_succ, mul_assoc] using hb3
        rw [zpow_two]
        exact eq_inv_of_mul_eq_one_left hbbb
      rw [h2, hb2] at hk3
      have hc : g * t⁻¹ * b * (g * t⁻¹)⁻¹ = b := by
        calc g * t⁻¹ * b * (g * t⁻¹)⁻¹ = g * (t⁻¹ * b * t) * g⁻¹ := by group
          _ = g * b⁻¹ * g⁻¹ := by rw [ht']
          _ = (g * b * g⁻¹)⁻¹ := by group
          _ = b := by rw [← hk3, inv_inv]
      have hcomm : g * t⁻¹ * b = b * (g * t⁻¹) := mul_inv_eq_iff_eq_mul.1 hc
      have hmem : g * t⁻¹ ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2 hcomm
      have key2 : g * t⁻¹ * t ∈ Cen b ⊔ Subgroup.zpowers t :=
        mul_mem ((le_sup_left : Cen b ≤ Cen b ⊔ Subgroup.zpowers t) hmem)
          ((le_sup_right : Subgroup.zpowers t ≤ Cen b ⊔ Subgroup.zpowers t)
            (Subgroup.mem_zpowers t))
      simpa using key2
  ·
    refine sup_le ?_ ?_
    · intro g hg
      have hgb : g * b * g⁻¹ = b := by
        rw [Subgroup.mem_centralizer_singleton_iff.1 hg, mul_inv_cancel_right]
      exact Subgroup.mem_normalizer_iff.2 (key g hgb)
    · refine Subgroup.zpowers_le.2 ?_
      refine Subgroup.mem_normalizer_iff.2 (fun h => ⟨fun hh => ?_, fun hh => ?_⟩)
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
        rw [← hk, ← conj_zpow, ht, inv_zpow]
        exact inv_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k)
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
        have e2 : (t⁻¹ * b * t) ^ k = t⁻¹ * b ^ k * t := by
          have := conj_zpow (a := t⁻¹) (b := b) (i := k)
          rwa [inv_inv] at this
        have hh' : h = (b⁻¹) ^ k := by
          calc h = t⁻¹ * (t * h * t⁻¹) * t := by group
            _ = t⁻¹ * b ^ k * t := by rw [hk]
            _ = (t⁻¹ * b * t) ^ k := e2.symm
            _ = (b⁻¹) ^ k := by rw [ht']
        rw [hh', inv_zpow]
        exact inv_mem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k)

end CFSG.RankThree.PartTwo.Sec21.FF84
