module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res3

variable {Y : Type*} [Group Y]

theorem isPGroup_zpowers_of_pow_eq_one {p : ℕ} [hp : Fact p.Prime] {σ : MulAut Y}
    (h : σ ^ p = 1) : IsPGroup p (Subgroup.zpowers σ) := by
  have hd : orderOf σ ∣ p := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime hp.out).mp hd with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])

theorem forall_zpowers_fix_iff {σ : MulAut Y} {w : Y} :
    (∀ g : Subgroup.zpowers σ, (g : MulAut Y) w = w) ↔ σ w = w := by
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h g
    have hσ : σ ∈ MulAction.stabilizer (MulAut Y) w := h
    exact (Subgroup.zpowers_le.mpr hσ) g.2

theorem zpowers_commute {σ τ : MulAut Y} (hστ : σ * τ = τ * σ) (g : Subgroup.zpowers σ) :
    (g : MulAut Y) * τ = τ * g := by
  have hσ : σ ∈ Subgroup.centralizer {τ} :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff.mp hx]
      exact hστ.symm
  have := Subgroup.mem_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hσ) g.2) τ rfl
  exact this.symm

@[expose] def fixSub (σ τ : MulAut Y) (hστ : σ * τ = τ * σ) :
    SubMulAction (Subgroup.zpowers σ) Y where
  carrier := {w | τ w = w}
  smul_mem' := fun g w hw => by
    change τ ((g : MulAut Y) w) = (g : MulAut Y) w
    have hw' : τ w = w := hw
    rw [← MulAut.mul_apply, ← zpowers_commute hστ g, MulAut.mul_apply, hw']

@[expose] def fixSubgroup (σ : MulAut Y) : Subgroup Y where
  carrier := {w | σ w = w}
  mul_mem' := fun {a b} ha hb => by
    change σ (a * b) = a * b
    rw [map_mul, show σ a = a from ha, show σ b = b from hb]
  one_mem' := map_one σ
  inv_mem' := fun {a} ha => by
    change σ a⁻¹ = a⁻¹
    rw [map_inv, show σ a = a from ha]

theorem eq_of_two_pow_modEq_twentyOne {a b : ℕ} (ha : a ≤ 6) (hb : 1 ≤ b) (hba : b ≤ a)
    (h : 2 ^ a ≡ 2 ^ b [MOD 21]) : a = b := by
  interval_cases a <;> interval_cases b <;> simp_all [Nat.ModEq]

variable [Finite Y]

theorem eq_one_of_commute_seven_three (hY : IsPGroup 2 Y) (hcard : Nat.card Y ≤ 64)
    {σ τ : MulAut Y} (hσ : σ ^ 7 = 1) (hτ : τ ^ 3 = 1) (hστ : σ * τ = τ * σ)
    (hfix : Nat.card {w : Y // τ w = w} ≤ 4) {w₀ : Y} (hw₀ : w₀ ≠ 1) (hτw₀ : τ w₀ = w₀) :
    σ = 1 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPσ := isPGroup_zpowers_of_pow_eq_one (p := 7) hσ
  have hPτ := isPGroup_zpowers_of_pow_eq_one (p := 3) hτ
  have hτσ : τ * σ = σ * τ := hστ.symm
  set Wc := fixSub σ τ hστ with hWc
  have hWc_card : Nat.card Wc = Nat.card {w : Y // τ w = w} := rfl
  have hmodc := hPσ.card_modEq_card_fixedPoints Wc
  have hcσ : ∀ w : Y, τ w = w → σ w = w := by
    have hsub : MulAction.fixedPoints (Subgroup.zpowers σ) Wc ⊆ Set.univ := Set.subset_univ _
    have heq : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) Wc) = Nat.card Wc := by
      have h1 : Nat.card Wc ≤ 4 := hWc_card ▸ hfix
      have h3 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers σ) Wc) ≤ Nat.card Wc :=
        Finite.card_subtype_le _
      have h2 := hmodc
      unfold Nat.ModEq at h2
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
      exact h2.symm
    have huniv : MulAction.fixedPoints (Subgroup.zpowers σ) Wc = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
      rw [Set.ncard_univ, ← Nat.card_coe_set_eq, heq]
    intro w hw
    have hmem : (⟨w, hw⟩ : Wc) ∈ MulAction.fixedPoints (Subgroup.zpowers σ) Wc :=
      huniv ▸ Set.mem_univ _
    have := hmem ⟨σ, Subgroup.mem_zpowers σ⟩
    exact congrArg Subtype.val this
  set H := fixSubgroup σ with hH
  have hYσ : Nat.card Y ≡ Nat.card H [MOD 7] := by
    have h := hPσ.card_modEq_card_fixedPoints Y
    have he : MulAction.fixedPoints (Subgroup.zpowers σ) Y = (H : Set Y) := by
      ext w
      exact forall_zpowers_fix_iff
    rw [he] at h
    exact h
  have hYτ : Nat.card Y ≡ Nat.card {w : Y // τ w = w} [MOD 3] := by
    have h := hPτ.card_modEq_card_fixedPoints Y
    have he : MulAction.fixedPoints (Subgroup.zpowers τ) Y = {w : Y | τ w = w} := by
      ext w
      exact forall_zpowers_fix_iff
    rw [he] at h
    exact h
  have hHτ : Nat.card H ≡ Nat.card {w : Y // τ w = w} [MOD 3] := by
    set Wσ := fixSub τ σ hτσ with hWσ
    have h := hPτ.card_modEq_card_fixedPoints Wσ
    have hcardW : Nat.card Wσ = Nat.card H := rfl
    have hfixW : Nat.card (MulAction.fixedPoints (Subgroup.zpowers τ) Wσ) =
        Nat.card {w : Y // τ w = w} := by
      refine Nat.card_congr
        { toFun := fun x => ⟨(x : Wσ), (forall_zpowers_fix_iff.mp fun g =>
            congrArg Subtype.val (x.2 g))⟩
          invFun := fun x => ⟨⟨x.1, hcσ x.1 x.2⟩, fun g => Subtype.ext
            (forall_zpowers_fix_iff.mpr x.2 g)⟩
          left_inv := fun x => rfl
          right_inv := fun x => rfl }
    rw [hcardW, hfixW] at h
    exact h
  have h21 : Nat.card Y ≡ Nat.card H [MOD 21] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 7)).mp
      ⟨hYτ.trans hHτ.symm, hYσ⟩
  obtain ⟨a, ha⟩ := hY.exists_card_eq
  have hHdvd : Nat.card H ∣ 2 ^ a := ha ▸ Subgroup.card_subgroup_dvd_card H
  obtain ⟨b, hb, hHb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hHdvd
  have ha6 : a ≤ 6 := by
    by_contra h
    have : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hb1 : 1 ≤ b := by
    by_contra h
    have hb0 : b = 0 := by omega
    have h1 : Nat.card H = 1 := by rw [hHb, hb0, pow_zero]
    have hw₀H : w₀ ∈ H := hcσ w₀ hτw₀
    have hbot := Subgroup.eq_bot_of_card_eq H h1
    rw [hbot] at hw₀H
    exact hw₀ ((Subgroup.mem_bot).mp hw₀H)
  rw [ha, hHb] at h21
  have hab := eq_of_two_pow_modEq_twentyOne ha6 hb1 hb h21
  have htop : H = ⊤ := Subgroup.eq_top_of_card_eq H (by rw [hHb, ha, hab])
  ext w
  have hw : w ∈ H := htop ▸ Subgroup.mem_top w
  exact hw

end CFSG.RankThree.PartTwo.Sec20.Res3
