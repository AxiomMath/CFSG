module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23Six5Aut2
public import CFSG.Quasithin.EmptyFaithful.S151bW3Five

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

theorem stab_of_mem_of_fix₁ (hW : ∀ w : W, w ^ 2 = 1) {Mb : Subgroup (MulAut W)}
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) {g : MulAut W}
    (hg : g ∈ Mb) (hz : ∃ z ∈ S.W₁, z ≠ 1 ∧ g z = z) : S.Stab₁ g ∧ S.Stab₂ g := by
  rcases S.stab_or_swap hW (hnorm g hg) with h | h
  · exact h
  · exfalso
    obtain ⟨z, hz1, hz2, hgz⟩ := hz
    have h3 : z ∈ S.W₁ ⊓ S.W₂ := ⟨hz1, by rw [← hgz]; exact h.1 z hz1⟩
    rw [S.winf, Subgroup.mem_bot] at h3
    exact hz2 h3

@[expose] def cenW₂ : Subgroup (MulAut W) where
  carrier := {f | (∀ w ∈ S.W₁, f w = w) ∧ f * S.a₂ = S.a₂ * f ∧ S.Stab₂ f}
  one_mem' := ⟨fun _ _ => rfl, by rw [one_mul, mul_one], fun _ => Iff.rfl⟩
  mul_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨fun w hw => ?_, ?_, fun w => (hg3 w).trans (hf3 (g w))⟩
    · show f (g w) = w
      rw [hg1 w hw, hf1 w hw]
    · calc f * g * S.a₂ = f * (g * S.a₂) := mul_assoc _ _ _
        _ = f * (S.a₂ * g) := by rw [hg2]
        _ = (f * S.a₂) * g := (mul_assoc _ _ _).symm
        _ = (S.a₂ * f) * g := by rw [hf2]
        _ = S.a₂ * (f * g) := mul_assoc _ _ _
  inv_mem' := by
    rintro f ⟨hf1, hf2, hf3⟩
    refine ⟨fun w hw => ?_, ?_, fun w => ?_⟩
    · calc f⁻¹ w = f⁻¹ (f w) := by rw [hf1 w hw]
        _ = w := MulAut.inv_apply_self W f w
    · calc f⁻¹ * S.a₂ = f⁻¹ * (S.a₂ * f) * f⁻¹ := by group
        _ = f⁻¹ * (f * S.a₂) * f⁻¹ := by rw [hf2]
        _ = S.a₂ * f⁻¹ := by group
    · have h := hf3 (f⁻¹ w)
      rw [MulAut.apply_inv_self] at h
      exact h.symm

theorem a₂_mem_cenW₂ : S.a₂ ∈ S.cenW₂ :=
  ⟨fun _ hw => S.a₂_fix_W₁ hw, rfl, (S.stab_of_mem_A₀ (Subgroup.mem_sup_right S.a₂_mem)).2⟩

theorem cenW₂_free (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {f : MulAut W}
    (hf : f ∈ S.cenW₂) {w : W} (hw : w ∈ S.W₂) (hw1 : w ≠ 1) (hfix : f w = w) : f = 1 := by
  have h2 := S.swap.fix_W₁_of_commute hW hcard (g := f) (by rw [swap_a₁]; exact hf.2.1) hw hw1 hfix
  exact S.eq_one_of_fix_W₁_W₂ hf.1 fun v hv => h2 v hv

theorem card_cenW₂_le (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) :
    Nat.card S.cenW₂ ≤ 15 := by
  obtain ⟨w₀, hw₀, hw₀1⟩ : ∃ w ∈ S.W₂, w ≠ 1 := by
    by_contra hcon
    have hbot : S.W₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun x hx =>
      by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    have h1 := Subgroup.card_eq_one.mpr hbot
    have h16 := S.card_W₂ hcard
    omega
  let φ : Option S.cenW₂ → S.W₂ := fun o =>
    o.elim 1 fun f => ⟨f.1 w₀, (f.2.2.2 w₀).mp hw₀⟩
  have hφ : Function.Injective φ := by
    intro o₁ o₂ h
    rcases o₁ with _ | f₁ <;> rcases o₂ with _ | f₂
    · rfl
    · exfalso
      have h1 : f₂.1 w₀ = 1 := (congrArg Subtype.val h).symm
      exact hw₀1 (f₂.1.injective (h1.trans (map_one f₂.1).symm))
    · exfalso
      have h1 : f₁.1 w₀ = 1 := congrArg Subtype.val h
      exact hw₀1 (f₁.1.injective (h1.trans (map_one f₁.1).symm))
    · have h' : f₁.1 w₀ = f₂.1 w₀ := congrArg Subtype.val h
      have hmem : f₂.1⁻¹ * f₁.1 ∈ S.cenW₂ := S.cenW₂.mul_mem (S.cenW₂.inv_mem f₂.2) f₁.2
      have hfix : (f₂.1⁻¹ * f₁.1) w₀ = w₀ := by
        show f₂.1⁻¹ (f₁.1 w₀) = w₀
        rw [h']
        exact MulAut.inv_apply_self W f₂.1 w₀
      have h1 : f₂.1 = f₁.1 := inv_mul_eq_one.mp (S.cenW₂_free hW hcard hmem hw₀ hw₀1 hfix)
      exact congrArg some (Subtype.ext h1.symm)
  have := Nat.card_le_card_of_injective φ hφ
  rw [Finite.card_option, S.card_W₂ hcard] at this
  omega

theorem cenW₂_eq_zpowers (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256) {ε : MulAut W}
    (hε : ε ∈ S.cenW₂) (hε3 : orderOf ε = 3) : S.cenW₂ = Subgroup.zpowers (ε * S.a₂) := by
  have hcomm : Commute ε S.a₂ := hε.2.1
  have hord : orderOf (ε * S.a₂) = 15 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime, hε3, S.orderOf_a₂_five]
    rw [hε3, S.orderOf_a₂_five]
    norm_num
  have hle : Subgroup.zpowers (ε * S.a₂) ≤ S.cenW₂ :=
    Subgroup.zpowers_le.mpr (S.cenW₂.mul_mem hε S.a₂_mem_cenW₂)
  have h15 := S.card_cenW₂_le hW hcard
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord]; exact h15)).symm

theorem mem_zpowers_of_cube_eq_one (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {ε g : MulAut W} (hε : ε ∈ S.cenW₂) (hε3 : orderOf ε = 3) (hg : g ∈ S.cenW₂)
    (hg3 : g ^ 3 = 1) : g ∈ Subgroup.zpowers ε := by
  have hcomm : Commute ε S.a₂ := hε.2.1
  have heq := S.cenW₂_eq_zpowers hW hcard hε hε3
  rw [heq] at hg
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hord : orderOf (ε * S.a₂) = 15 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime, hε3, S.orderOf_a₂_five]
    rw [hε3, S.orderOf_a₂_five]
    norm_num
  have h1 : (ε * S.a₂) ^ (k * 3) = 1 := by
    rw [zpow_mul, hk]
    exact hg3
  have h2 : ((15 : ℕ) : ℤ) ∣ k * 3 := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h1
  obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 5 * m := by
    obtain ⟨j, hj⟩ := h2
    exact ⟨j, by push_cast at hj; omega⟩
  have hε3' : ε ^ 3 = 1 := by
    have := pow_orderOf_eq_one ε
    rwa [hε3] at this
  have hc5 : (ε * S.a₂) ^ (5 : ℤ) = ε ^ (2 : ℤ) := by
    have h5 : S.a₂ ^ 5 = 1 := S.a₂_pow (Or.inr rfl)
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, zpow_natCast, hcomm.mul_pow, h5, mul_one,
      show ε ^ 5 = ε ^ 3 * ε ^ 2 from by rw [← pow_add], hε3', one_mul, zpow_two, pow_two]
  rw [← hk, hm, zpow_mul, hc5, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers ε _

theorem cube_eq_one_of_stabilizes (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {g : MulAut W} (hg : g ∈ S.cenW₂) {L : Subgroup W} (hL2 : L ≤ S.W₂) (hL4 : Nat.card L = 4)
    (hgL : ∀ w ∈ L, g w ∈ L) (hodd : Odd (orderOf g)) : g ^ 3 = 1 := by
  obtain ⟨z, hzL, hz1⟩ : ∃ z ∈ L, z ≠ 1 := by
    by_contra hcon
    have hbot : L = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr fun x hx =>
      by_contra fun hx1 => hcon ⟨x, hx, hx1⟩
    have h1 := Subgroup.card_eq_one.mpr hbot
    omega
  have hpowL : ∀ i : ℕ, (g ^ i) z ∈ L := by
    intro i
    induction i with
    | zero => simpa using hzL
    | succ i ih =>
      rw [pow_succ']
      exact hgL _ ih
  have hpowC : ∀ i : ℕ, g ^ i ∈ S.cenW₂ := fun i => S.cenW₂.pow_mem hg i
  let F : Option (Fin (orderOf g)) → ↥L := fun o =>
    o.elim 1 fun i => ⟨(g ^ (i : ℕ)) z, hpowL i⟩
  have hF : Function.Injective F := by
    rintro (_ | i) (_ | j) hij
    · rfl
    · exfalso
      have h1 : (g ^ (j : ℕ)) z = 1 := (congrArg Subtype.val hij).symm
      exact hz1 ((g ^ (j : ℕ)).injective (h1.trans (map_one _).symm))
    · exfalso
      have h1 : (g ^ (i : ℕ)) z = 1 := congrArg Subtype.val hij
      exact hz1 ((g ^ (i : ℕ)).injective (h1.trans (map_one _).symm))
    · have h1 : (g ^ (i : ℕ)) z = (g ^ (j : ℕ)) z := congrArg Subtype.val hij
      have hmem : (g ^ (j : ℕ))⁻¹ * g ^ (i : ℕ) ∈ S.cenW₂ :=
        S.cenW₂.mul_mem (S.cenW₂.inv_mem (hpowC j)) (hpowC i)
      have hfix : ((g ^ (j : ℕ))⁻¹ * g ^ (i : ℕ)) z = z := by
        show (g ^ (j : ℕ))⁻¹ ((g ^ (i : ℕ)) z) = z
        rw [h1]
        exact MulAut.inv_apply_self W _ z
      have h2 := S.cenW₂_free hW hcard hmem (hL2 hzL) hz1 hfix
      have h3 : g ^ (i : ℕ) = g ^ (j : ℕ) := (inv_mul_eq_one.mp h2).symm
      have h4 := pow_injOn_Iio_orderOf (x := g) i.2 j.2 h3
      exact congrArg some (Fin.ext h4)
  have hle := Nat.card_le_card_of_injective F hF
  rw [Finite.card_option, hL4, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  have hpos : 0 < orderOf g := orderOf_pos g
  have hn : orderOf g ∣ 3 := by
    obtain ⟨m, hm⟩ := hodd
    have : orderOf g = 1 ∨ orderOf g = 3 := by omega
    rcases this with h | h <;> rw [h]
    exact one_dvd 3
  exact orderOf_dvd_iff_pow_eq_one.mp hn

end CFSG.Quasithin.SixData151b
