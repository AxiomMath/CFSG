module

public import CFSG.Walter.J1.Nu

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem oddPart_classify_of_centralizer {X : Subgroup G} {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hXp : Nat.card X = p) {x : G} (hx : orderOf x = 2)
    (hXx : X ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ τ : G, ∃ A : Subgroup G, IsFour x τ ∧ (∀ u ∈ X, τ * u * τ⁻¹ = u⁻¹) ∧
      IsMaxInv x τ A ∧ A ≤ Subgroup.centralizer (X : Set G) ∧ X ≤ A ∧
      A ⊓ Subgroup.centralizer ({x} : Set G) = X ∧
      Nat.card A * 2 = Nat.card (Subgroup.centralizer (X : Set G)) ∧
      (∀ y ∈ Subgroup.centralizer (X : Set G), Odd (orderOf y) → y ∈ A) ∧
      (∀ y ∈ A, ∀ z ∈ A, y * z = z * y) ∧
      (Nat.card A = 3 ∨ Nat.card A = 5 ∨ Nat.card A = 15 ∨ Nat.card A = 27 ∨
        Nat.card A = 125) := by
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq hx
  have hXF : X ≤ (h.conj g).F := (h.conj g).le_F_of_odd (by rw [hg]; exact hXx)
    (hXp ▸ odd_of_three_or_five hp)
  obtain ⟨τ, -, A, hT, hτX, hM, h1, h2, h3, h4, h5, h6, h7⟩ :=
    (h.conj g).oddPart_classify hXF hp hXp
  rw [hg] at hT hM h3
  exact ⟨τ, A, hT, hτX, hM, h1, h2, h3, h4, h5, h6, h7⟩

omit [Finite G] in
theorem commute_of_mem_of_conj_mem {a b x : G} (hT : IsFour a b) {A : Subgroup G}
    (hA : IsInv a b A) (hxA : x ∈ A) (hxa : x * a * x⁻¹ = a ∨ x * a * x⁻¹ = b ∨
      x * a * x⁻¹ = a * b) : x * a * x⁻¹ = a := by
  have hcomm : x * a * x⁻¹ * a⁻¹ ∈ A := by
    have : a * x⁻¹ * a⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hA.2.1 _).mp (A.inv_mem hxA)
    rw [show x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) by group]
    exact A.mul_mem hxA this
  have hodd : Odd (orderOf (x * a * x⁻¹ * a⁻¹)) :=
    Odd.of_dvd_nat hA.1 (Subgroup.orderOf_dvd_natCard A hcomm)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hT.mul_self_a
  rcases hxa with h1 | h1 | h1
  · exact h1
  · exfalso
    rw [h1, hainv] at hodd
    rw [show b * a = a * b from hT.2.2.2.symm, hT.orderOf_mul] at hodd
    exact absurd hodd (by decide)
  · exfalso
    rw [h1, hainv, hT.mul_mul_a, hT.2.1] at hodd
    exact absurd hodd (by decide)

include h in
theorem card_oddPart_ne_125 {a b : G} (hT : IsFour a b) {A : Subgroup G} (hM : IsMaxInv a b A)
    (habel : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hA : Nat.card A = 125)
    (ha : Nat.card (A ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = 5) : False := by
  have hpp : (5 : ℕ).Prime := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hpp⟩
  have hcard := h.card_eq_mul hT hM.1
  have hb' := h.card_inf_centralizer hT.2.1 hM.1.1
  have hab' := h.card_inf_centralizer hT.orderOf_mul hM.1.1
  rw [hA, ha] at hcard
  have hb : Nat.card (A ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = 5 := by
    rcases hb' with h1 | h1 | h1 <;> rcases hab' with h2 | h2 | h2 <;> rw [h1, h2] at hcard <;>
      first | rfl | (exfalso; omega) | exact h1
  have hab : Nat.card (A ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) = 5 := by
    rw [hb] at hcard
    omega
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 3) (by rw [hA]; norm_num)
  obtain ⟨ν, hνA, hν3, hcyc⟩ := h.exists_nu hT hM (Or.inr rfl) hAp habel ha hb
  obtain ⟨b', hT', hM', hb'5, hab'5, h1, h2⟩ : ∃ b' : G, IsFour a b' ∧ IsMaxInv a b' A ∧
      Nat.card (A ⊓ Subgroup.centralizer ({b'} : Set G) : Subgroup G) = 5 ∧
      Nat.card (A ⊓ Subgroup.centralizer ({a * b'} : Set G) : Subgroup G) = 5 ∧
      ν * a * ν⁻¹ = b' ∧ ν * b' * ν⁻¹ = a * b' := by
    rcases hcyc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨b, hT, hM, hb, hab, h1, h2⟩
    · refine ⟨a * b, hT.mul_right, hM.mul_right hT, hab, by rw [hT.a_mul_mul]; exact hb, h1, ?_⟩
      rw [hT.a_mul_mul, show ν * (a * b) * ν⁻¹ = (ν * a * ν⁻¹) * (ν * b * ν⁻¹) by group, h1, h2,
        hT.mul_mul_a]
  clear hcyc hb hab hT hM
  obtain ⟨y, hy, hy1⟩ := exists_ne_one_of_card ha hpp.one_lt
  set y₁ := ν * y * ν⁻¹
  set y₂ := ν * y₁ * ν⁻¹
  have hνinv : ∀ z ∈ A, ν * z * ν⁻¹ ∈ A := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp hνA z).mp hz
  have hy₁ : y₁ ∈ A ⊓ Subgroup.centralizer ({b'} : Set G) := by
    refine ⟨hνinv y hy.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    rw [← h1]
    calc ν * y * ν⁻¹ * (ν * a * ν⁻¹) = ν * (y * a) * ν⁻¹ := by group
      _ = ν * (a * y) * ν⁻¹ := by rw [hya]
      _ = ν * a * ν⁻¹ * (ν * y * ν⁻¹) := by group
  have hy₂ : y₂ ∈ A ⊓ Subgroup.centralizer ({a * b'} : Set G) := by
    refine ⟨hνinv y₁ hy₁.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hyb : y₁ * b' = b' * y₁ := Subgroup.mem_centralizer_singleton_iff.mp hy₁.2
    rw [← h2]
    calc ν * y₁ * ν⁻¹ * (ν * b' * ν⁻¹) = ν * (y₁ * b') * ν⁻¹ := by group
      _ = ν * (b' * y₁) * ν⁻¹ := by rw [hyb]
      _ = ν * b' * ν⁻¹ * (ν * y₁ * ν⁻¹) := by group
  have hν3' : ν ^ 3 = 1 := by rw [← hν3, pow_orderOf_eq_one]
  have hy₃ : ν * y₂ * ν⁻¹ = y := by
    calc ν * y₂ * ν⁻¹ = ν ^ 3 * y * (ν ^ 3)⁻¹ := by simp only [y₂, y₁]; rw [pow_three]; group
      _ = y := by rw [hν3']; group
  set w := y * y₁ * y₂
  have hwA : w ∈ A := A.mul_mem (A.mul_mem hy.1 hy₁.1) hy₂.1
  have hwν : w * ν = ν * w := by
    have : ν * w * ν⁻¹ = w := by
      calc ν * w * ν⁻¹ = (ν * y * ν⁻¹) * (ν * y₁ * ν⁻¹) * (ν * y₂ * ν⁻¹) := by
            simp only [w]; group
        _ = y₁ * y₂ * y := by rw [hy₃]
        _ = w := by
          simp only [w]
          rw [habel _ (A.mul_mem hy₁.1 hy₂.1) _ hy.1, ← mul_assoc]
    calc w * ν = (ν * w * ν⁻¹)⁻¹⁻¹ * ν := by rw [this, inv_inv]
      _ = ν * w := by group
  have hw1 : w ≠ 1 := by
    intro hw
    have hfour := h.inf_centralizer_four_eq_bot hT' hM'.1.1
    have hainv : ∀ X : Subgroup G, X ≤ A → X ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ →
        a ∈ Subgroup.normalizer (X : Set G) → ∀ z ∈ X, a * z * a⁻¹ = z⁻¹ :=
      fun X _ hXa haX => inv_of_inf_centralizer_eq_bot hT'.mul_self_a haX hXa
    have hab1 : a * y₁ * a⁻¹ = y₁⁻¹ := by
      refine hainv _ inf_le_left ?_ (mem_normalizer_inf_centralizer hM'.1.2.1 hT'.2.2.2.symm) y₁
        hy₁
      rw [inf_assoc, inf_comm (Subgroup.centralizer _), ← inf_assoc]
      exact hfour
    have hab2 : a * y₂ * a⁻¹ = y₂⁻¹ := by
      refine hainv _ inf_le_left ?_ (mem_normalizer_inf_centralizer hM'.1.2.1 ?_) y₂ hy₂
      · rw [eq_bot_iff]
        intro z hz
        have hza : z * a = a * z := Subgroup.mem_centralizer_singleton_iff.mp hz.2
        have hzab : z * (a * b') = (a * b') * z :=
          Subgroup.mem_centralizer_singleton_iff.mp hz.1.2
        have hzb : z * b' = b' * z := by
          calc z * b' = z * (a * (a * b')) := by rw [hT'.a_mul_mul]
            _ = a * (z * (a * b')) := by rw [← mul_assoc, hza, mul_assoc]
            _ = a * (a * b' * z) := by rw [hzab]
            _ = b' * z := by rw [← mul_assoc, ← mul_assoc, hT'.mul_self_a, one_mul]
        have : z ∈ A ⊓ Subgroup.centralizer ({a} : Set G) ⊓
            Subgroup.centralizer ({b'} : Set G) :=
          ⟨⟨hz.1.1, hz.2⟩, Subgroup.mem_centralizer_singleton_iff.mpr hzb⟩
        rwa [hfour] at this
      · rw [hT'.mul_mul_a, hT'.a_mul_mul]
    have hay : a * y * a⁻¹ = y := by
      rw [← (Subgroup.mem_centralizer_singleton_iff.mp hy.2), mul_inv_cancel_right]
    have hwy : y = (y₁ * y₂)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
      exact hw
    have hy2 : y * y = 1 := by
      have e1 : a * y * a⁻¹ = (a * y₁ * a⁻¹ * (a * y₂ * a⁻¹))⁻¹ := by
        rw [hwy]; group
      rw [hab1, hab2, hay] at e1
      have e2 : (y₁⁻¹ * y₂⁻¹)⁻¹ = y₁ * y₂ := by
        rw [mul_inv_rev, inv_inv, inv_inv, habel _ hy₂.1 _ hy₁.1]
      rw [e2] at e1
      calc y * y = (y₁ * y₂)⁻¹ * (y₁ * y₂) := by rw [← hwy, ← e1]
        _ = 1 := inv_mul_cancel _
    exact hy1 (eq_one_of_mul_self_of_odd (odd_orderOf_of_mem (by rw [ha]; decide) hy) hy2)
  have hνT : ν ∈ Subgroup.normalizer ((GorensteinWalter.kleinFourOfCommutingInvolutions a b'
      hT'.mul_self_a hT'.mul_self_b hT'.2.2.2 : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    have hab3 : ν * (a * b') * ν⁻¹ = a := by
      rw [show ν * (a * b') * ν⁻¹ = (ν * a * ν⁻¹) * (ν * b' * ν⁻¹) by group, h1, h2,
        hT'.b_mul_mul]
    rw [mem_kleinFour_iff hT'.mul_self_a hT'.mul_self_b hT'.2.2.2] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl hab3)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inl h2
    · simp
  obtain ⟨s, hs, -, -, hsν⟩ := h.exists_involution_commute hT' hν3 hνT
  have hνs : Subgroup.zpowers ν ≤ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hsν.symm
  obtain ⟨σ, B, hTB, -, hMB, hBC, hXB, hBs, -, hBodd, hBab, hBcard⟩ :=
    h.oddPart_classify_of_centralizer (Or.inl rfl) (by rw [Nat.card_zpowers, hν3]) hs hνs
  have hwC : w ∈ Subgroup.centralizer ((Subgroup.zpowers ν : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left (hwν.symm) k).eq
  have hwodd : Odd (orderOf w) := odd_orderOf_of_mem (by rw [hA]; decide) hwA
  have hwB : w ∈ B := hBodd w hwC hwodd
  have hνB : ν ∈ B := hXB (Subgroup.mem_zpowers ν)
  have hw5 : orderOf w = 5 := by
    have h1 : orderOf w ∣ 125 := hA ▸ Subgroup.orderOf_dvd_natCard A hwA
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hpp).mp (show orderOf w ∣ 5 ^ 3 by simpa using h1)
    have h2 : orderOf w ∣ Nat.card B := Subgroup.orderOf_dvd_natCard B hwB
    have h3 : 3 ∣ Nat.card B := hν3 ▸ Subgroup.orderOf_dvd_natCard B hνB
    have hwne : orderOf w ≠ 1 := fun h0 => hw1 (orderOf_eq_one_iff.mp h0)
    interval_cases k
    · simp at hk; exact absurd hk hw1
    · simpa using hk
    · rw [hk] at h2
      rcases hBcard with h0 | h0 | h0 | h0 | h0 <;> rw [h0] at h2 h3 <;> omega
    · rw [hk] at h2
      rcases hBcard with h0 | h0 | h0 | h0 | h0 <;> rw [h0] at h2 h3 <;> omega
  have hB15 : Nat.card B = 15 := by
    have h2 : 5 ∣ Nat.card B := hw5 ▸ Subgroup.orderOf_dvd_natCard B hwB
    have h3 : 3 ∣ Nat.card B := hν3 ▸ Subgroup.orderOf_dvd_natCard B hνB
    rcases hBcard with h0 | h0 | h0 | h0 | h0 <;> rw [h0] at h2 h3 ⊢ <;> omega
  set W := Subgroup.zpowers w
  have hW5 : Nat.card W = 5 := by rw [Nat.card_zpowers, hw5]
  have hBcard' := h.card_eq_mul hTB hMB.1
  rw [hBs, Nat.card_zpowers, hν3, hB15] at hBcard'
  have hWx : ∃ x : G, orderOf x = 2 ∧ W ≤ Subgroup.centralizer ({x} : Set G) := by
    have hσ := h.card_inf_centralizer hTB.2.1 hMB.1.1
    have hsσ := h.card_inf_centralizer hTB.orderOf_mul hMB.1.1
    have hgood : ∀ x : G, orderOf x = 2 →
        Nat.card (B ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 5 →
        W ≤ Subgroup.centralizer ({x} : Set G) := by
      intro x _ hx5
      set Bx := B ⊓ Subgroup.centralizer ({x} : Set G)
      have hWN : W ≤ Subgroup.normalizer (Bx : Set G) := by
        rw [Subgroup.zpowers_le]
        refine mem_normalizer_of_conj_mem fun z hz => ?_
        rw [hBab w hwB z hz.1, mul_inv_cancel_right]
        exact hz
      have hWB : W ⊔ Bx ≤ B := sup_le ((Subgroup.zpowers_le).mpr hwB) inf_le_left
      by_cases hdisj : Disjoint Bx W
      · exfalso
        have := Subgroup.card_dvd_of_le hWB
        rw [sup_comm, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Bx W hWN
          hdisj, hx5, hW5, hB15] at this
        norm_num at this
      · rw [Subgroup.disjoint_def] at hdisj
        push Not at hdisj
        obtain ⟨z, hzx, hzW, hz1⟩ := hdisj
        have hWeq := eq_zpowers_of_card_prime hpp hW5 hzW hz1
        rw [hWeq, Subgroup.zpowers_le]
        exact hzx.2
    rcases hσ with h1 | h1 | h1 <;> rcases hsσ with h2 | h2 | h2 <;> rw [h1, h2] at hBcard' <;>
      norm_num at hBcard'
    · exact ⟨_, hTB.orderOf_mul, hgood _ hTB.orderOf_mul h2⟩
    · exact ⟨σ, hTB.2.1, hgood σ hTB.2.1 h1⟩
  obtain ⟨x, hx, hWx⟩ := hWx
  obtain ⟨-, AW, -, -, -, -, hWAW, -, -, hAWodd, -, hAWcard⟩ :=
    h.oddPart_classify_of_centralizer (Or.inr rfl) hW5 hx hWx
  have hAC : A ≤ Subgroup.centralizer (W : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left (habel w hwA z hz) k).eq
  have hAAW : A ≤ AW := fun z hz => hAWodd z (hAC hz) (odd_orderOf_of_mem (by rw [hA]; decide) hz)
  have hAWeq : AW = A := by
    refine (Subgroup.eq_of_le_of_card_ge hAAW ?_).symm
    have := Subgroup.card_dvd_of_le hAAW
    rw [hA] at this ⊢
    rcases hAWcard with h0 | h0 | h0 | h0 | h0 <;> rw [h0] at this ⊢ <;> omega
  have hνC : ν ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left hwν k).eq
  have hνA' : ν ∈ A := hAWeq ▸ hAWodd ν hνC (by rw [hν3]; decide)
  have := commute_of_mem_of_conj_mem hT' hM'.1 hνA' (Or.inr (Or.inl h1))
  exact hT'.2.2.1 (this.symm.trans h1)

end JankoHyp

end CFSG.Walter.J1
