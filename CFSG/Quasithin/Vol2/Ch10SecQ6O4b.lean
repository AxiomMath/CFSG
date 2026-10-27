module

public import CFSG.Quasithin.Vol2.Ch10SecQ6O4a

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

variable {F : Type} [Field F]

theorem card_fix_units [CharP F 2] [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n) (hn : 1 ≤ n) :
    Nat.card {u : Fˣ // u ^ 2 ^ n = u} = 2 ^ n - 1 := by
  classical
  have := Fintype.ofFinite F
  let e : {u : Fˣ // u ^ 2 ^ n = u} ≃ {x : F // sig n x = x ∧ x ≠ 0} :=
    { toFun := fun u => ⟨u.1, by
        have h1 := congrArg Units.val u.2
        rw [Units.val_pow_eq_pow_val] at h1
        exact h1, u.1.ne_zero⟩
      invFun := fun x => ⟨Units.mk0 x.1 x.2.2, Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0]
        exact x.2.1)⟩
      left_inv := fun u => Subtype.ext (Units.ext rfl)
      right_inv := fun x => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h0 : (0 : F) ∈ Finset.univ.filter fun x : F => sig n x = x := by simp [sig_zero]
  have h1 : (Finset.univ.filter fun x : F => sig n x = x ∧ x ≠ 0) =
      (Finset.univ.filter fun x : F => sig n x = x).erase 0 := by
    ext x
    simp [and_comm]
  have h2 : (Finset.univ.filter fun x : F => sig n x = x).card = 2 ^ n := by
    rw [← card_fixSig hF hn, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    rfl
  rw [h1, Finset.card_erase_of_mem h0, h2]

theorem exists_norm_eq [CharP F 2] [Finite F] {n : ℕ} (hF : Nat.card F = 4 ^ n) (hn : 1 ≤ n)
    {c : F} (hc : sig n c = c) (hc0 : c ≠ 0) : ∃ l : F, l * sig n l = c := by
  classical
  have := Fintype.ofFinite F
  let N : Fˣ →* Fˣ := powMonoidHom (2 ^ n + 1)
  have hunits : Nat.card Fˣ = 4 ^ n - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  have hker : Nat.card N.ker ≤ 2 ^ n + 1 := by
    have h1 := IsCyclic.card_pow_eq_one_le (α := Fˣ) (n := 2 ^ n + 1) (by positivity)
    have h2 : Nat.card N.ker = Nat.card {u : Fˣ // u ^ (2 ^ n + 1) = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun u => MonoidHom.mem_ker)
    rw [h2, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h1
  have hcard : Nat.card Fˣ = Nat.card N.range * Nat.card N.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange N).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup N.ker
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h4 : 4 ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  have hrange : 2 ^ n - 1 ≤ Nat.card N.range := by
    have h5 : 2 ^ n * 2 ^ n = Nat.card N.range * Nat.card N.ker + 1 := by
      rw [← hcard, hunits, ← h4]
      have : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
      omega
    by_contra hlt
    push Not at hlt
    have h6 : Nat.card N.range + 2 ≤ 2 ^ n := by omega
    nlinarith [Nat.zero_le (Nat.card N.range), Nat.zero_le (Nat.card N.ker)]
  have hsub : ∀ u ∈ N.range, u ^ 2 ^ n = u := by
    rintro _ ⟨v, rfl⟩
    have hv : v ^ (4 ^ n - 1) = 1 := by rw [← hunits]; exact pow_card_eq_one'
    change (v ^ (2 ^ n + 1)) ^ 2 ^ n = v ^ (2 ^ n + 1)
    rw [← pow_mul, show (2 ^ n + 1) * 2 ^ n = (4 ^ n - 1) + (2 ^ n + 1) by
      have : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
      rw [h4]
      have : 1 ≤ 2 ^ n * 2 ^ n := by nlinarith
      rw [add_mul, one_mul]
      omega, pow_add, hv, one_mul]
  let R : Finset Fˣ := Finset.univ.filter (· ∈ N.range)
  let T : Finset Fˣ := Finset.univ.filter fun u => u ^ 2 ^ n = u
  have hRT : R ⊆ T := fun u hu => by
    simp only [R, T, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hsub u hu
  have hTcard : T.card = 2 ^ n - 1 := by
    rw [← card_fix_units hF hn, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hRcard : Nat.card N.range = R.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hRT' := Finset.eq_of_subset_of_card_le hRT (by omega)
  have hcT : Units.mk0 c hc0 ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hc)
  rw [← hRT'] at hcT
  simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hcT
  obtain ⟨v, hv⟩ := hcT
  refine ⟨v, ?_⟩
  have h1 := congrArg Units.val hv
  change ((v ^ (2 ^ n + 1) : Fˣ) : F) = c at h1
  rw [Units.val_pow_eq_pow_val, pow_succ, mul_comm] at h1
  exact h1

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
