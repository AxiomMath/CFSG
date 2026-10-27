module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H11

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

theorem seven_translates_gen {G α : Type*} [Group G] [MulAction G α] {g : G}
    (hg : orderOf g = 7) {x : α} (hx : g • x ≠ x) :
    Function.Injective (fun i : Fin 7 => g ^ (i : ℕ) • x) ∧
      ∀ i : Fin 7, g • g ^ (i : ℕ) • x ≠ g ^ (i : ℕ) • x := by
  constructor
  · intro i j hij
    by_contra hne
    simp only at hij
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · have h1 : g ^ ((j : ℕ) - i) • (g ^ (i : ℕ) • x) = g ^ (i : ℕ) • x := by
        rw [← mul_smul, ← pow_add, Nat.sub_add_cancel h.le, hij]
      have h2 := smul_eq_of_pow_smul_eq hg (by omega) (by omega) h1
      rw [← mul_smul, ← pow_succ', pow_succ, mul_smul] at h2
      exact hx (smul_left_cancel _ h2)
    · have h1 : g ^ ((i : ℕ) - j) • (g ^ (j : ℕ) • x) = g ^ (j : ℕ) • x := by
        rw [← mul_smul, ← pow_add, Nat.sub_add_cancel h.le, hij]
      have h2 := smul_eq_of_pow_smul_eq hg (by omega) (by omega) h1
      rw [← mul_smul, ← pow_succ', pow_succ, mul_smul] at h2
      exact hx (smul_left_cancel _ h2)
  · intro i h
    rw [← mul_smul, ← pow_succ', pow_succ, mul_smul] at h
    exact hx (smul_left_cancel _ h)

theorem conj_mem_of_normalizer {N : Subgroup SL4} {g r : SL4}
    (hg : g ∈ Subgroup.normalizer (N : Set SL4)) (hr : r ∈ N) : g * r * g⁻¹ ∈ N :=
  (Subgroup.mem_normalizer_iff.mp hg r).mp hr

theorem eq_stabV_of_le {X S Q : Subgroup SL4} {v : Fin 4 → ZMod 2} (hv : v ≠ 0)
    (hX : X ≤ stabV v) (hS : S ≤ stabV v) (hS64 : Nat.card S = 64)
    (hSX : S ≤ Subgroup.normalizer (X : Set SL4)) (hcard : Nat.card X = Nat.card Q * 168)
    (hQmax : ∀ N : Subgroup SL4, N ≤ X → X ≤ Subgroup.normalizer (N : Set SL4) →
      IsPGroup 2 N → N ≤ Q) : X = stabV v := by
  have hR8 : Nat.card (elV v) = 8 := card_elV_four hv
  have hRS : elV v ≤ stabV v := elV_le_stabV v
  have hXR : X ≤ Subgroup.normalizer (elV v : Set SL4) := hX.trans (stabV_le_normalizer v)
  have hst : Nat.card (stabV v) = 1344 := card_stabV_four hv
  have hRp : IsPGroup 2 (elV v) := IsPGroup.of_card (n := 3) (by rw [hR8]; norm_num)
  obtain ⟨k, hkX, hk⟩ : ∃ k ∈ X, orderOf k = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 7
      (by rw [hcard]; exact Dvd.dvd.mul_left (by norm_num) _)
    exact ⟨k, k.2, by rw [← hk, Subgroup.orderOf_coe]⟩
  have hkv : k • v = v := MulAction.mem_stabilizer_iff.mp (hX hkX)
  have hRXQ : elV v ⊓ X ≤ Q := by
    refine hQmax _ inf_le_right (fun x hx => ?_) (hRp.to_le inf_le_left)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyR, hyX⟩
      exact ⟨conj_mem_of_normalizer (hXR hx) hyR,
        X.mul_mem (X.mul_mem hx hyX) (X.inv_mem hx)⟩
    · rintro ⟨hyR, hyX⟩
      have hx' : x⁻¹ ∈ Subgroup.normalizer (elV v : Set SL4) := Subgroup.inv_mem _ (hXR hx)
      have h1 := conj_mem_of_normalizer hx' hyR
      have h2 : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rw [h2] at h1
      refine ⟨h1, ?_⟩
      have h3 := X.mul_mem (X.mul_mem (X.inv_mem hx) hyX) hx
      rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h3
  have hc1 := card_sup_mul_card_inf' hXR
  have hle1 : Nat.card (elV v ⊔ X : Subgroup SL4) ≤ 1344 :=
    hst ▸ Subgroup.card_le_of_le (sup_le hRS hX)
  have hle2 : Nat.card (elV v ⊓ X : Subgroup SL4) ≤ Nat.card Q := Subgroup.card_le_of_le hRXQ
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  rw [hR8, hcard] at hc1
  have heq2 : Nat.card (elV v ⊓ X : Subgroup SL4) = Nat.card Q := by
    by_contra hne
    have hlt : Nat.card (elV v ⊓ X : Subgroup SL4) < Nat.card Q := lt_of_le_of_ne hle2 hne
    have := Nat.mul_le_mul_right (Nat.card (elV v ⊓ X : Subgroup SL4)) hle1
    nlinarith
  by_cases hQ1 : Nat.card Q = 1
  · exfalso
    have hX168 : Nat.card X = 168 := by rw [hcard, hQ1, one_mul]
    have hRX1 : elV v ⊓ X = ⊥ := Subgroup.eq_bot_of_card_eq _ (heq2.trans hQ1)
    have hc2 := card_sup_mul_card_inf' hSX
    rw [hX168, hS64] at hc2
    have hdvd : Nat.card (X ⊓ S : Subgroup SL4) ∣ 8 := by
      have h1 : Nat.card (X ⊓ S : Subgroup SL4) ∣ 168 := hX168 ▸ Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card (X ⊓ S : Subgroup SL4) ∣ 64 := hS64 ▸ Subgroup.card_dvd_of_le inf_le_right
      have h3 := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 168 64 = 8 by norm_num] at h3
    have hle3 : Nat.card (X ⊓ S : Subgroup SL4) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 1344 ≤ Nat.card (X ⊔ S : Subgroup SL4) := by nlinarith
    have heqXS : X ⊔ S = stabV v :=
      Subgroup.eq_of_le_of_card_ge (sup_le hX hS) (by rw [hst]; exact hge)
    have hRNX : elV v ≤ Subgroup.normalizer (X : Set SL4) :=
      hRS.trans (heqXS ▸ sup_le Subgroup.le_normalizer hSX)
    have hR1 : ∀ r ∈ elV v, r = 1 := fun r hr => by
      refine eq_one_of_comm_elV hk hv hkv hr ?_
      have hcR : k * r * k⁻¹ * r⁻¹ ∈ elV v :=
        (elV v).mul_mem (conj_mem_of_normalizer (hXR hkX) hr) ((elV v).inv_mem hr)
      have hcX : k * r * k⁻¹ * r⁻¹ ∈ X := by
        rw [show k * r * k⁻¹ * r⁻¹ = k * (r * k⁻¹ * r⁻¹) by group]
        exact X.mul_mem hkX (conj_mem_of_normalizer (hRNX hr) (X.inv_mem hkX))
      have h1 : k * r * k⁻¹ * r⁻¹ ∈ elV v ⊓ X := ⟨hcR, hcX⟩
      rw [hRX1, Subgroup.mem_bot] at h1
      calc k * r = k * r * k⁻¹ * r⁻¹ * r * k := by group
        _ = r * k := by rw [h1, one_mul]
    have : elV v = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hR1
    rw [this, Subgroup.card_bot] at hR8
    omega
  ·
    have h2 : 1 < Nat.card (elV v ⊓ X : Subgroup SL4) := by
      rw [heq2]
      omega
    obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.one_lt_card_iff_ne_bot _).mp h2 |>
      (Subgroup.ne_bot_iff_exists_ne_one).mp
    have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
    have hmove : ConjAct.toConjAct k • r ≠ r := by
      rw [ConjAct.toConjAct_smul]
      intro h
      apply hr1'
      refine eq_one_of_comm_elV hk hv hkv hr.1 ?_
      calc k * r = k * r * k⁻¹ * k := by group
        _ = r * k := by rw [h]
    have hk' : orderOf (ConjAct.toConjAct k) = 7 := by
      rw [MulEquiv.orderOf_eq, hk]
    obtain ⟨hinj, -⟩ := seven_translates_gen hk' hmove
    have hmem : ∀ i : ℕ, ConjAct.toConjAct k ^ i • r ∈ elV v ⊓ X := fun i => by
      rw [← map_pow, ConjAct.toConjAct_smul]
      exact ⟨conj_mem_of_normalizer (hXR (X.pow_mem hkX i)) hr.1,
        X.mul_mem (X.mul_mem (X.pow_mem hkX i) hr.2) (X.inv_mem (X.pow_mem hkX i))⟩
    let g : Option (Fin 7) → SL4 := fun o => o.elim 1 fun i => ConjAct.toConjAct k ^ (i : ℕ) • r
    have hgmem : ∀ o, g o ∈ elV v ⊓ X := by
      rintro (_ | i)
      · exact Subgroup.one_mem _
      · exact hmem i
    have hg : Function.Injective g := by
      have hne1 : ∀ i : Fin 7, ConjAct.toConjAct k ^ (i : ℕ) • r ≠ 1 := fun i h' => by
        rw [← map_pow, ConjAct.toConjAct_smul] at h'
        apply hr1'
        calc r = (k ^ (i : ℕ))⁻¹ * (k ^ (i : ℕ) * r * (k ^ (i : ℕ))⁻¹) * k ^ (i : ℕ) := by group
          _ = 1 := by rw [h']; group
      rintro (_ | i) (_ | j) h
      · rfl
      · exact absurd h.symm (hne1 j)
      · exact absurd h (hne1 i)
      · exact congrArg some (hinj h)
    let f : Option (Fin 7) → ↥(elV v ⊓ X : Subgroup SL4) := fun o => ⟨g o, hgmem o⟩
    have hf : Function.Injective f := fun a b h => hg (congrArg Subtype.val h)
    have h8 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card (α := Option (Fin 7)), Fintype.card_option,
      Fintype.card_fin] at h8
    have hRX : elV v ⊓ X = elV v := Subgroup.eq_of_le_of_card_ge inf_le_left (by
      rw [hR8]
      exact h8)
    have hRleX : elV v ≤ X := hRX ▸ inf_le_right
    have hsup : elV v ⊔ X = X := sup_eq_right.mpr hRleX
    have hX1344 : Nat.card X = 1344 := by
      rw [hsup] at hc1
      have h3 : Nat.card (elV v ⊓ X : Subgroup SL4) = 8 := by rw [hRX, hR8]
      rw [h3] at hc1
      rw [heq2] at h3
      rw [hcard, h3]
    exact Subgroup.eq_of_le_of_card_ge hX (by rw [hst, hX1344])

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
