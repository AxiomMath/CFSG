module

public import CFSG.Walter.J1.GoodCount

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

include h in
theorem w_facts {a b : G} (hT : IsFour a b) {A : Subgroup G} (hM : IsMaxInv a b A)
    (habel : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) {ν : G}
    (hνA : ν ∈ Subgroup.normalizer (A : Set G)) (hν3 : ν ^ 3 = 1) (h1 : ν * a * ν⁻¹ = b)
    (h2 : ν * b * ν⁻¹ = a * b) {y : G} (hy : y ∈ A ⊓ Subgroup.centralizer ({a} : Set G))
    (hy1 : y ≠ 1) :
    ν * y * ν⁻¹ ∈ A ⊓ Subgroup.centralizer ({b} : Set G) ∧
      ν * (ν * y * ν⁻¹) * ν⁻¹ ∈ A ⊓ Subgroup.centralizer ({a * b} : Set G) ∧
      ν * (ν * (ν * y * ν⁻¹) * ν⁻¹) * ν⁻¹ = y ∧
      y * (ν * y * ν⁻¹) * (ν * (ν * y * ν⁻¹) * ν⁻¹) ≠ 1 ∧
      y * (ν * y * ν⁻¹) * (ν * (ν * y * ν⁻¹) * ν⁻¹) * ν =
        ν * (y * (ν * y * ν⁻¹) * (ν * (ν * y * ν⁻¹) * ν⁻¹)) := by
  set y₁ := ν * y * ν⁻¹
  set y₂ := ν * y₁ * ν⁻¹
  have hνinv : ∀ z ∈ A, ν * z * ν⁻¹ ∈ A := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp hνA z).mp hz
  have hy₁ : y₁ ∈ A ⊓ Subgroup.centralizer ({b} : Set G) := by
    refine ⟨hνinv y hy.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    rw [← h1]
    calc ν * y * ν⁻¹ * (ν * a * ν⁻¹) = ν * (y * a) * ν⁻¹ := by group
      _ = ν * (a * y) * ν⁻¹ := by rw [hya]
      _ = ν * a * ν⁻¹ * (ν * y * ν⁻¹) := by group
  have hy₂ : y₂ ∈ A ⊓ Subgroup.centralizer ({a * b} : Set G) := by
    refine ⟨hνinv y₁ hy₁.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hyb : y₁ * b = b * y₁ := Subgroup.mem_centralizer_singleton_iff.mp hy₁.2
    rw [← h2]
    calc ν * y₁ * ν⁻¹ * (ν * b * ν⁻¹) = ν * (y₁ * b) * ν⁻¹ := by group
      _ = ν * (b * y₁) * ν⁻¹ := by rw [hyb]
      _ = ν * b * ν⁻¹ * (ν * y₁ * ν⁻¹) := by group
  have hy₃ : ν * y₂ * ν⁻¹ = y := by
    calc ν * y₂ * ν⁻¹ = ν ^ 3 * y * (ν ^ 3)⁻¹ := by simp only [y₂, y₁]; rw [pow_three]; group
      _ = y := by rw [hν3]; group
  refine ⟨hy₁, hy₂, hy₃, ?_, ?_⟩
  · intro hw
    have hfour := h.inf_centralizer_four_eq_bot hT hM.1.1
    have hab1 : a * y₁ * a⁻¹ = y₁⁻¹ := by
      refine inv_of_inf_centralizer_eq_bot hT.mul_self_a
        (mem_normalizer_inf_centralizer hM.1.2.1 hT.2.2.2.symm) ?_ y₁ hy₁
      rw [inf_assoc, inf_comm (Subgroup.centralizer _), ← inf_assoc]
      exact hfour
    have hab2 : a * y₂ * a⁻¹ = y₂⁻¹ := by
      refine inv_of_inf_centralizer_eq_bot hT.mul_self_a
        (mem_normalizer_inf_centralizer hM.1.2.1 (by rw [hT.mul_mul_a, hT.a_mul_mul])) ?_ y₂ hy₂
      rw [eq_bot_iff]
      intro z hz
      have hza : z * a = a * z := Subgroup.mem_centralizer_singleton_iff.mp hz.2
      have hzab : z * (a * b) = (a * b) * z := Subgroup.mem_centralizer_singleton_iff.mp hz.1.2
      have hzb : z * b = b * z := by
        calc z * b = z * (a * (a * b)) := by rw [hT.a_mul_mul]
          _ = a * (z * (a * b)) := by rw [← mul_assoc, hza, mul_assoc]
          _ = a * (a * b * z) := by rw [hzab]
          _ = b * z := by rw [← mul_assoc, ← mul_assoc, hT.mul_self_a, one_mul]
      have : z ∈ A ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :=
        ⟨⟨hz.1.1, hz.2⟩, Subgroup.mem_centralizer_singleton_iff.mpr hzb⟩
      rwa [hfour] at this
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
    exact hy1 (eq_one_of_mul_self_of_odd (odd_orderOf_of_mem hM.1.1 hy.1) hy2)
  · have : ν * (y * y₁ * y₂) * ν⁻¹ = y * y₁ * y₂ := by
      calc ν * (y * y₁ * y₂) * ν⁻¹ = (ν * y * ν⁻¹) * (ν * y₁ * ν⁻¹) * (ν * y₂ * ν⁻¹) := by
            group
        _ = y₁ * y₂ * y := by rw [hy₃]
        _ = y * y₁ * y₂ := by
          rw [habel _ (A.mul_mem hy₁.1 hy₂.1) _ hy.1, ← mul_assoc]
    calc y * y₁ * y₂ * ν = (ν * (y * y₁ * y₂) * ν⁻¹)⁻¹⁻¹ * ν := by rw [this, inv_inv]
      _ = ν * (y * y₁ * y₂) := by group

include h in
theorem exists_nu' {a b : G} (hT : IsFour a b) {A : Subgroup G} (hM : IsMaxInv a b A)
    {p : ℕ} (hp : p = 3 ∨ p = 5) (hAp : IsPGroup p A) (habel : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (ha : Nat.card (A ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = p)
    (hb : Nat.card (A ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = p)
    (hab : Nat.card (A ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) = p) :
    ∃ b' ν : G, IsFour a b' ∧ IsMaxInv a b' A ∧
      Nat.card (A ⊓ Subgroup.centralizer ({b'} : Set G) : Subgroup G) = p ∧
      Nat.card (A ⊓ Subgroup.centralizer ({a * b'} : Set G) : Subgroup G) = p ∧
      ν ∈ Subgroup.normalizer (A : Set G) ∧ orderOf ν = 3 ∧ ν * a * ν⁻¹ = b' ∧
      ν * b' * ν⁻¹ = a * b' := by
  obtain ⟨ν, hνA, hν3, hcyc⟩ := h.exists_nu hT hM hp hAp habel ha hb
  rcases hcyc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨b, ν, hT, hM, hb, hab, hνA, hν3, h1, h2⟩
  · refine ⟨a * b, ν, hT.mul_right, hM.mul_right hT, hab, by rw [hT.a_mul_mul]; exact hb, hνA,
      hν3, h1, ?_⟩
    rw [hT.a_mul_mul, show ν * (a * b) * ν⁻¹ = (ν * a * ν⁻¹) * (ν * b * ν⁻¹) by group, h1, h2,
      hT.mul_mul_a]

theorem nu_mem_normalizer_four {a b ν : G} (hT : IsFour a b) (h1 : ν * a * ν⁻¹ = b)
    (h2 : ν * b * ν⁻¹ = a * b) :
    ν ∈ Subgroup.normalizer ((GorensteinWalter.kleinFourOfCommutingInvolutions a b
      hT.mul_self_a hT.mul_self_b hT.2.2.2 : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem fun z hz => ?_
  have hab3 : ν * (a * b) * ν⁻¹ = a := by
    rw [show ν * (a * b) * ν⁻¹ = (ν * a * ν⁻¹) * (ν * b * ν⁻¹) by group, h1, h2, hT.b_mul_mul]
  rw [mem_kleinFour_iff hT.mul_self_a hT.mul_self_b hT.2.2.2] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl hab3)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inl h2
  · simp

include h in
theorem card_oddPart_ne_27 {a b : G} (hT₀ : IsFour a b) {A : Subgroup G} (hM₀ : IsMaxInv a b A)
    (habel : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y) (hA : Nat.card A = 27)
    (ha : Nat.card (A ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := h.card_eq_mul hT₀ hM₀.1
  have hb' := h.card_inf_centralizer hT₀.2.1 hM₀.1.1
  have hab' := h.card_inf_centralizer hT₀.orderOf_mul hM₀.1.1
  rw [hA, ha] at hcard
  have hb₀ : Nat.card (A ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) = 3 := by
    rcases hb' with h1 | h1 | h1 <;> rcases hab' with h2 | h2 | h2 <;> rw [h1, h2] at hcard <;>
      omega
  have hab₀ : Nat.card (A ⊓ Subgroup.centralizer ({a * b} : Set G) : Subgroup G) = 3 := by
    rw [hb₀] at hcard
    omega
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA]; norm_num)
  obtain ⟨b, ν, hT, hM, hb, hab, hνA, hν3, h1, h2⟩ :=
    h.exists_nu' hT₀ hM₀ (Or.inl rfl) hAp habel ha hb₀ hab₀
  clear hT₀ hM₀ hb₀ hab₀ hcard hb' hab'
  have hν3' : ν ^ 3 = 1 := by rw [← hν3, pow_orderOf_eq_one]
  obtain ⟨y, hy, hy1⟩ := exists_ne_one_of_card ha (by norm_num)
  obtain ⟨hy₁, hy₂, hy₃, hw1, hwν⟩ := h.w_facts hT hM habel hνA hν3' h1 h2 hy hy1
  set y₁ := ν * y * ν⁻¹
  set y₂ := ν * y₁ * ν⁻¹
  set w := y * y₁ * y₂
  have hwA : w ∈ A := A.mul_mem (A.mul_mem hy.1 hy₁.1) hy₂.1
  have hνnA : ν ∉ A := fun hνA' => by
    have := commute_of_mem_of_conj_mem hT hM.1 hνA' (Or.inr (Or.inl h1))
    exact hT.2.2.1 (this.symm.trans h1)
  obtain ⟨s, hs, -, -, hsν⟩ := h.exists_involution_commute hT hν3 (nu_mem_normalizer_four hT h1 h2)
  have hνs : Subgroup.zpowers ν ≤ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hsν.symm
  obtain ⟨σ, B, hTB, -, hMB, -, hXB, hBs, -, hBodd, hBab, hBcard⟩ :=
    h.oddPart_classify_of_centralizer (Or.inl rfl) (by rw [Nat.card_zpowers, hν3]) hs hνs
  have hcomm : ∀ z, z * ν = ν * z → z ∈ Subgroup.centralizer
      ((Subgroup.zpowers ν : Subgroup G) : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left hz.symm k).eq
  have hwB : w ∈ B := hBodd w (hcomm w hwν) (odd_orderOf_of_mem (by rw [hA]; decide) hwA)
  have hνB : ν ∈ B := hXB (Subgroup.mem_zpowers ν)
  have hw3 : w ^ 3 = 1 := by
    have e1 : y ^ 3 = 1 := by rw [← ha]; exact pow_card_eq_one_of_mem hy
    have e2 : y₁ ^ 3 = 1 := by rw [← hb]; exact pow_card_eq_one_of_mem hy₁
    have e3 : y₂ ^ 3 = 1 := by rw [← hab]; exact pow_card_eq_one_of_mem hy₂
    have c1 : Commute y y₁ := habel y hy.1 y₁ hy₁.1
    have c2 : Commute (y * y₁) y₂ := habel _ (A.mul_mem hy.1 hy₁.1) y₂ hy₂.1
    rw [c2.mul_pow, c1.mul_pow, e1, e2, e3, one_mul, one_mul]
  have hwo : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  set Xν := Subgroup.zpowers ν
  set Xw := Subgroup.zpowers w
  have hXwA : Xw ≤ A := (Subgroup.zpowers_le).mpr hwA
  have hdisj : Disjoint Xν Xw := by
    rw [Subgroup.disjoint_def]
    intro z hzν hzw
    by_contra hz1
    have hXνz := eq_zpowers_of_card_prime Nat.prime_three (by rw [Nat.card_zpowers, hν3]) hzν hz1
    have hνz : ν ∈ Subgroup.zpowers z := hXνz ▸ Subgroup.mem_zpowers ν
    exact hνnA ((Subgroup.zpowers_le).mpr (hXwA hzw) hνz)
  have hXwN : Xw ≤ Subgroup.normalizer (Xν : Set G) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    have : w * ν * w⁻¹ = ν := by rw [hwν]; group
    obtain ⟨k, rfl⟩ := hz
    change w * ν ^ k * w⁻¹ ∈ Xν
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, this]
    exact Subgroup.zpow_mem_zpowers ν k
  have hYcard : Nat.card (Xν ⊔ Xw : Subgroup G) = 9 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Xν Xw hXwN hdisj,
      Nat.card_zpowers, Nat.card_zpowers, hν3, hwo]
  have hYB : Xν ⊔ Xw ≤ B := sup_le hXB ((Subgroup.zpowers_le).mpr hwB)
  have hB27 : Nat.card B = 27 := by
    have := Subgroup.card_dvd_of_le hYB
    rw [hYcard] at this
    rcases hBcard with h0 | h0 | h0 | h0 | h0 <;> rw [h0] at this ⊢ <;> omega
  have hBs3 : Nat.card (B ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) = 3 := by
    rw [hBs, Nat.card_zpowers, hν3]
  have hcardB := h.card_eq_mul hTB hMB.1
  have hσ' := h.card_inf_centralizer hTB.2.1 hMB.1.1
  have hsσ' := h.card_inf_centralizer hTB.orderOf_mul hMB.1.1
  rw [hB27, hBs3] at hcardB
  have hBσ : Nat.card (B ⊓ Subgroup.centralizer ({σ} : Set G) : Subgroup G) = 3 := by
    rcases hσ' with h1 | h1 | h1 <;> rcases hsσ' with h2 | h2 | h2 <;> rw [h1, h2] at hcardB <;>
      omega
  have hBsσ : Nat.card (B ⊓ Subgroup.centralizer ({s * σ} : Set G) : Subgroup G) = 3 := by
    rw [hBσ] at hcardB
    omega
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 3) (by rw [hB27]; norm_num)
  obtain ⟨σ', ν', hTB', hMB', hBσ', hBsσ', hν'B, hν'3, h1', h2'⟩ :=
    h.exists_nu' hTB hMB (Or.inl rfl) hBp hBab hBs3 hBσ hBsσ
  have hν'nB : ν' ∉ B := fun hν'B' => by
    have := commute_of_mem_of_conj_mem hTB' hMB'.1 hν'B' (Or.inr (Or.inl h1'))
    exact hTB'.2.2.1 (this.symm.trans h1')
  set c := y₁ * y₂⁻¹
  have hcA : c ∈ A := A.mul_mem hy₁.1 (A.inv_mem hy₂.1)
  have e3 : y₂ ^ 3 = 1 := by rw [← hab]; exact pow_card_eq_one_of_mem hy₂
  have hcν : c * ν * c⁻¹ = w * ν := by
    have hνc : ν * c * ν⁻¹ = y₂ * y⁻¹ := by
      simp only [c]
      rw [show ν * (y₁ * y₂⁻¹) * ν⁻¹ = (ν * y₁ * ν⁻¹) * (ν * y₂ * ν⁻¹)⁻¹ by group, hy₃]
    have hy2y : y₂⁻¹ * y = y * y₂⁻¹ := habel _ (A.inv_mem hy₂.1) y hy.1
    have hy1y : y₁ * y = y * y₁ := habel _ hy₁.1 y hy.1
    have hy2sq : y₂⁻¹ * y₂⁻¹ = y₂ := by
      have h3 : y₂ * y₂ * y₂ = 1 := by rw [← e3, pow_three, mul_assoc]
      have hinv : y₂⁻¹ = y₂ * y₂ := (eq_inv_of_mul_eq_one_left h3).symm
      rw [hinv, show y₂ * y₂ * (y₂ * y₂) = (y₂ * y₂ * y₂) * y₂ by group, h3, one_mul]
    calc c * ν * c⁻¹ = c * (ν * c * ν⁻¹)⁻¹ * ν := by group
      _ = y₁ * y₂⁻¹ * (y * y₂⁻¹) * ν := by rw [hνc, mul_inv_rev, inv_inv]
      _ = y₁ * (y₂⁻¹ * y) * y₂⁻¹ * ν := by group
      _ = y₁ * (y * y₂⁻¹) * y₂⁻¹ * ν := by rw [hy2y]
      _ = (y₁ * y) * (y₂⁻¹ * y₂⁻¹) * ν := by group
      _ = w * ν := by rw [hy1y, hy2sq]
  have hcwν : c * (w * ν) * c⁻¹ = w * w * ν := by
    calc c * (w * ν) * c⁻¹ = (c * w * c⁻¹) * (c * ν * c⁻¹) := by group
      _ = w * (w * ν) := by rw [habel c hcA w hwA, mul_inv_cancel_right, hcν]
      _ = w * w * ν := by group
  set X₁ := Subgroup.zpowers (w * ν)
  set X₂ := Subgroup.zpowers (w * w * ν)
  have hX₁ : Xν.map (MulAut.conj c).toMonoidHom = X₁ := by
    rw [MonoidHom.map_zpowers]; exact congrArg _ hcν
  have hX₂ : X₁.map (MulAut.conj c).toMonoidHom = X₂ := by
    rw [MonoidHom.map_zpowers]; exact congrArg _ hcwν
  have hXν3 : Nat.card Xν = 3 := by rw [Nat.card_zpowers, hν3]
  have hX₁3 : Nat.card X₁ = 3 := by
    rw [← hX₁, Subgroup.card_map_of_injective (MulAut.conj c).injective, hXν3]
  have hX₂3 : Nat.card X₂ = 3 := by
    rw [← hX₂, Subgroup.card_map_of_injective (MulAut.conj c).injective, hX₁3]
  have hgood_conj : ∀ (X : Subgroup G) (x g : G), orderOf x = 2 →
      X ≤ Subgroup.centralizer ({x} : Set G) →
      orderOf (g * x * g⁻¹) = 2 ∧ X.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
    intro X x g hx hXx
    refine ⟨by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx], ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzx : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp (hXx hz)
    change g * z * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * z * g⁻¹)
    calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hzx]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
  obtain ⟨hs₁, hX₁s⟩ := hgood_conj Xν s c hs hνs
  obtain ⟨hs₂, hX₂s⟩ := hgood_conj X₁ _ c hs₁ (hX₁ ▸ hX₁s)
  have hwνB : w * ν ∈ B := B.mul_mem hwB hνB
  have hX₁B : X₁ ≤ B := (Subgroup.zpowers_le).mpr hwνB
  have hX₂B : X₂ ≤ B := (Subgroup.zpowers_le).mpr (B.mul_mem (B.mul_mem hwB hwB) hνB)
  have hgood₀ : Xν ∈ goodSet B := ⟨hXB, hXν3, s, hs, hνs⟩
  have hgood₁ : X₁ ∈ goodSet B := ⟨hX₁B, hX₁3, _, hs₁, hX₁ ▸ hX₁s⟩
  have hgood₂ : X₂ ∈ goodSet B := ⟨hX₂B, hX₂3, _, hs₂, hX₂ ▸ hX₂s⟩
  have hcoord := fun {X : Subgroup G} (hX : X ∈ goodSet B) =>
    h.eq_coord_of_good hTB' hMB' hBab hB27 hBs3 hBσ' hBsσ' hν'B hν'3 hν'nB hX
  have hYle : ∀ {X : Subgroup G}, w ∈ X → ν ∈ X → Nat.card X = 3 → False := by
    intro X hwX hνX hX3
    have := Subgroup.card_le_of_le (sup_le ((Subgroup.zpowers_le).mpr hνX)
      ((Subgroup.zpowers_le).mpr hwX) : Xν ⊔ Xw ≤ X)
    rw [hYcard, hX3] at this
    omega
  have hν_X₁ : ¬ X₁ ≤ Xν := fun hle => by
    have hwν' : w * ν ∈ Xν := hle (Subgroup.mem_zpowers _)
    have : w ∈ Xν := by
      have := Xν.mul_mem hwν' (Xν.inv_mem (Subgroup.mem_zpowers ν))
      simpa using this
    exact hYle this (Subgroup.mem_zpowers ν) hXν3
  have hν_X₂ : ¬ X₂ ≤ Xν := fun hle => by
    have hwν' : w * w * ν ∈ Xν := hle (Subgroup.mem_zpowers _)
    have hww : w * w ∈ Xν := by
      have := Xν.mul_mem hwν' (Xν.inv_mem (Subgroup.mem_zpowers ν))
      simpa using this
    have : w ∈ Xν := by
      have h4 : w = (w * w) * (w * w) := by
        rw [show (w * w) * (w * w) = w ^ 3 * w by rw [pow_three]; group, hw3, one_mul]
      rw [h4]; exact Xν.mul_mem hww hww
    exact hYle this (Subgroup.mem_zpowers ν) hXν3
  have hX₁X₂ : X₁ ≠ X₂ := by
    intro heq
    have h1' : w * w * ν ∈ X₁ := heq ▸ Subgroup.mem_zpowers _
    have hw' : w ∈ X₁ := by
      have := X₁.mul_mem h1' (X₁.inv_mem (Subgroup.mem_zpowers (w * ν)))
      simpa [mul_assoc] using this
    have hν' : ν ∈ X₁ := by
      have := X₁.mul_mem (X₁.inv_mem hw') (Subgroup.mem_zpowers (w * ν))
      simpa using this
    exact hYle hw' hν' hX₁3
  set Bs := B ⊓ Subgroup.centralizer ({s} : Set G)
  set Bσ := B ⊓ Subgroup.centralizer ({σ'} : Set G)
  set Bsσ := B ⊓ Subgroup.centralizer ({s * σ'} : Set G)
  have hBsY : Bs = Xν := hBs
  have hX₁c : X₁ = Bσ ∨ X₁ = Bsσ := by
    rcases hcoord hgood₁ with h0 | h0 | h0
    · exact absurd (h0.trans hBsY).le hν_X₁
    · exact Or.inl h0
    · exact Or.inr h0
  have hX₂c : X₂ = Bσ ∨ X₂ = Bsσ := by
    rcases hcoord hgood₂ with h0 | h0 | h0
    · exact absurd (h0.trans hBsY).le hν_X₂
    · exact Or.inl h0
    · exact Or.inr h0
  have hY : ∀ {X : Subgroup G}, X = Xν ∨ X = X₁ ∨ X = X₂ → X ≤ Xν ⊔ Xw := by
    rintro X (rfl | rfl | rfl)
    · exact le_sup_left
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers ν))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers
        w)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers w)))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers ν))
  have hBσY : Bσ ≤ Xν ⊔ Xw := by
    rcases hX₁c with h0 | h0
    · exact h0 ▸ hY (Or.inr (Or.inl rfl))
    · rcases hX₂c with h0' | h0'
      · exact h0' ▸ hY (Or.inr (Or.inr rfl))
      · exact absurd (h0.trans h0'.symm) hX₁X₂
  have hBsσY : Bsσ ≤ Xν ⊔ Xw := by
    rcases hX₁c with h0 | h0
    · rcases hX₂c with h0' | h0'
      · exact absurd (h0.trans h0'.symm) hX₁X₂
      · exact h0' ▸ hY (Or.inr (Or.inr rfl))
    · exact h0 ▸ hY (Or.inr (Or.inl rfl))
  have hfourB := h.inf_centralizer_four_eq_bot hTB' hMB'.1.1
  set D := Bs ⊔ Bσ
  have hBσN : Bσ ≤ Subgroup.normalizer (Bs : Set G) := by
    intro z hz
    refine mem_normalizer_of_conj_mem fun u hu => ?_
    rw [hBab z hz.1 u hu.1, mul_inv_cancel_right]
    exact hu
  have hdisjB : Disjoint Bs Bσ := by
    rw [disjoint_iff, eq_bot_iff]
    intro z hz
    have : z ∈ B ⊓ Subgroup.centralizer ({s} : Set G) ⊓ Subgroup.centralizer ({σ'} : Set G) :=
      ⟨hz.1, hz.2.2⟩
    rwa [hfourB] at this
  have hDcard : Nat.card D = 9 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Bs Bσ hBσN hdisjB, hBs3,
      hBσ']
  have hDY : D = Xν ⊔ Xw :=
    Subgroup.eq_of_le_of_card_ge (sup_le (hBsY ▸ le_sup_left) hBσY) (by rw [hDcard, hYcard])
  have hBsσD : Bsσ ≤ D := hDY ▸ hBsσY
  have hDinv : IsInv s σ' D := ⟨by rw [hDcard]; decide,
    mem_normalizer_sup (mem_normalizer_inf_centralizer hMB'.1.2.1 rfl)
      (mem_normalizer_inf_centralizer hMB'.1.2.1 hTB'.2.2.2.symm),
    mem_normalizer_sup (mem_normalizer_inf_centralizer hMB'.1.2.2 hTB'.2.2.2)
      (mem_normalizer_inf_centralizer hMB'.1.2.2 rfl)⟩
  have hBW := h.card_eq_mul hTB' hDinv
  have hle1 : 3 ≤ Nat.card (D ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) :=
    hBs3 ▸ Subgroup.card_le_of_le (le_inf le_sup_left inf_le_right)
  have hle2 : 3 ≤ Nat.card (D ⊓ Subgroup.centralizer ({σ'} : Set G) : Subgroup G) :=
    hBσ' ▸ Subgroup.card_le_of_le (le_inf le_sup_right inf_le_right)
  have hle3 : 3 ≤ Nat.card (D ⊓ Subgroup.centralizer ({s * σ'} : Set G) : Subgroup G) :=
    hBsσ' ▸ Subgroup.card_le_of_le (le_inf hBsσD inf_le_right)
  rw [hDcard] at hBW
  have : 3 * 3 * 3 ≤ 9 := by
    rw [hBW]
    exact Nat.mul_le_mul (Nat.mul_le_mul hle1 hle2) hle3
  omega

include h in
theorem bender_4_1 {U : Subgroup G} (hUF : U ≤ h.F) {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hUp : Nat.card U = p) :
    ∃ τ ∈ h.F, ∃ A : Subgroup G, IsFour h.t τ ∧ (∀ u ∈ U, τ * u * τ⁻¹ = u⁻¹) ∧
      IsMaxInv h.t τ A ∧ A ≤ Subgroup.centralizer (U : Set G) ∧ U ≤ A ∧
      A ⊓ Subgroup.centralizer ({h.t} : Set G) = U ∧
      Nat.card A * 2 = Nat.card (Subgroup.centralizer (U : Set G)) ∧
      (∀ x ∈ Subgroup.centralizer (U : Set G), Odd (orderOf x) → x ∈ A) ∧
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ (Nat.card A = p ∨ Nat.card A = 15) := by
  obtain ⟨τ, hτF, A, hT, hτU, hM, hAC, hUA, hCt, hcard, hodd, habel, hAcard⟩ :=
    h.oddPart_classify hUF hp hUp
  refine ⟨τ, hτF, A, hT, hτU, hM, hAC, hUA, hCt, hcard, hodd, habel, ?_⟩
  have hdvd : p ∣ Nat.card A := hUp ▸ Subgroup.card_dvd_of_le hUA
  have hAt : Nat.card (A ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) = p := by
    rw [hCt, hUp]
  rcases hAcard with h0 | h0 | h0 | h0 | h0
  · left; rcases hp with rfl | rfl <;> omega
  · left; rcases hp with rfl | rfl <;> omega
  · right; exact h0
  · exfalso
    rcases hp with rfl | rfl
    · exact h.card_oddPart_ne_27 hT hM habel h0 hAt
    · rw [h0] at hdvd; omega
  · exfalso
    rcases hp with rfl | rfl
    · rw [h0] at hdvd; omega
    · exact h.card_oddPart_ne_125 hT hM habel h0 hAt

include h in
theorem bender_4_1_of_centralizer {X : Subgroup G} {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hXp : Nat.card X = p) {x : G} (hx : orderOf x = 2)
    (hXx : X ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ τ : G, ∃ A : Subgroup G, IsFour x τ ∧ (∀ u ∈ X, τ * u * τ⁻¹ = u⁻¹) ∧
      IsMaxInv x τ A ∧ A ≤ Subgroup.centralizer (X : Set G) ∧ X ≤ A ∧
      A ⊓ Subgroup.centralizer ({x} : Set G) = X ∧
      Nat.card A * 2 = Nat.card (Subgroup.centralizer (X : Set G)) ∧
      (∀ y ∈ Subgroup.centralizer (X : Set G), Odd (orderOf y) → y ∈ A) ∧
      (∀ y ∈ A, ∀ z ∈ A, y * z = z * y) ∧ (Nat.card A = p ∨ Nat.card A = 15) := by
  obtain ⟨g, hg⟩ := h.exists_conj_t_eq hx
  have hXF : X ≤ (h.conj g).F := (h.conj g).le_F_of_odd (by rw [hg]; exact hXx)
    (hXp ▸ odd_of_three_or_five hp)
  obtain ⟨τ, -, A, hT, hτX, hM, h1, h2, h3, h4, h5, h6, h7⟩ := (h.conj g).bender_4_1 hXF hp hXp
  rw [hg] at hT hM h3
  exact ⟨τ, A, hT, hτX, hM, h1, h2, h3, h4, h5, h6, h7⟩

end JankoHyp

end CFSG.Walter.J1
