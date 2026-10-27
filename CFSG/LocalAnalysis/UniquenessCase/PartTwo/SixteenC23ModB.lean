module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ModA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {U : Type*} [CommGroup U] {Y₁ Y₂ : Subgroup U} {A₁ A₂ Mb : Subgroup (MulAut U)}

private lemma c23_eq_of_mem_ncard_two {S : Set U} (hS : S.ncard = 2) (h1 : (1 : U) ∈ S)
    {a b : U} (ha : a ∈ S) (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨c, d, hcd, hS'⟩ := Set.ncard_eq_two.mp hS
  rw [hS'] at h1 ha hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ha hb
  rcases h1 with h1 | h1
  · rcases ha with ha | ha
    · exact absurd (ha.trans h1.symm) ha1
    · rcases hb with hb | hb
      · exact absurd (hb.trans h1.symm) hb1
      · exact ha.trans hb.symm
  · rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact ha.trans hb.symm
      · exact absurd (hb.trans h1.symm) hb1
    · exact absurd (ha.trans h1.symm) ha1

theorem c23_ncard_fixed_eq_two [Finite U] {Y : Subgroup U} (hY : Nat.card Y = 8)
    {R : Subgroup (MulAut U)} (hR : Nat.card R = 3)
    (hinv : ∀ r ∈ R, ∀ y ∈ Y, (r : MulAut U) y ∈ Y)
    (hnt : ∃ r ∈ R, ∃ y ∈ Y, (r : MulAut U) y ≠ y) :
    {y : U | y ∈ Y ∧ ∀ r ∈ R, (r : MulAut U) y = y}.ncard = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : MulAction R U := MulAction.compHom U R.subtype
  let Y' : SubMulAction R U :=
    { carrier := Y, smul_mem' := fun r y hy => hinv r r.2 y hy }
  let Fix : Subgroup U :=
    { carrier := {y : U | y ∈ Y ∧ ∀ r ∈ R, (r : MulAut U) y = y}
      one_mem' := ⟨Y.one_mem, fun r _ => map_one (r : MulAut U)⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨Y.mul_mem ha.1 hb.1, fun r hr => by rw [map_mul, ha.2 r hr, hb.2 r hr]⟩
      inv_mem' := fun {a} ha =>
        ⟨Y.inv_mem ha.1, fun r hr => by rw [map_inv, ha.2 r hr]⟩ }
  change (Fix : Set U).ncard = 2
  have hmod : Nat.card Y' ≡ Nat.card (MulAction.fixedPoints R Y') [MOD 3] :=
    (IsPGroup.of_card (p := 3) (n := 1) (by rw [pow_one]; exact hR)).card_modEq_card_fixedPoints Y'
  have himg : Subtype.val '' (MulAction.fixedPoints R Y') =
      {y : U | y ∈ Y ∧ ∀ r ∈ R, (r : MulAut U) y = y} := by
    ext u
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun r hr => ?_⟩
      have hval : (r : MulAut U) y.1 = y.1 :=
        congrArg Subtype.val (MulAction.mem_fixedPoints.mp hy (⟨r, hr⟩ : R))
      simpa using hval
    · rintro ⟨hy, hfix⟩
      exact ⟨⟨u, hy⟩,
        MulAction.mem_fixedPoints.mpr (fun r => Subtype.ext (hfix (r : MulAut U) r.2)), rfl⟩
  have hfixcard : Nat.card (MulAction.fixedPoints R Y') = Nat.card ↥Fix := by
    rw [Nat.card_coe_set_eq,
      ← Set.ncard_image_of_injective (MulAction.fixedPoints R Y') Subtype.val_injective, himg]
    exact (Nat.card_coe_set_eq (Fix : Set U)).symm
  have hcardY' : Nat.card Y' = 8 := by
    change Nat.card ↥Y = 8
    exact hY
  have hmod2 : 8 ≡ Nat.card ↥Fix [MOD 3] := by
    rw [hcardY'] at hmod
    rwa [hfixcard] at hmod
  have hdiv : Nat.card ↥Fix ∣ 8 := by
    have hle : Fix ≤ Y := fun x hx =>
      (show x ∈ Y ∧ ∀ r ∈ R, (r : MulAut U) x = x from hx).1
    have := Subgroup.card_dvd_of_le hle
    rwa [hY] at this
  have hdiv' : Nat.card ↥Fix ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact hdiv
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv'
  rw [hj] at hmod2
  have hj1 : j = 1 := by
    interval_cases j
    · norm_num [Nat.ModEq] at hmod2
    · rfl
    · norm_num [Nat.ModEq] at hmod2
    · exfalso
      have hcard : Nat.card ↥Y ≤ Nat.card ↥Fix := by rw [hY, hj]; norm_num
      have hFY : Fix = Y :=
        Subgroup.eq_of_le_of_card_ge
          (show Fix ≤ Y from fun x hx =>
            (show x ∈ Y ∧ ∀ r ∈ R, (r : MulAut U) x = x from hx).1) hcard
      obtain ⟨r, hr, y, hy, hry⟩ := hnt
      have hyF : y ∈ Fix := by rw [hFY]; exact hy
      exact hry ((show y ∈ Y ∧ ∀ r ∈ R, (r : MulAut U) y = y from hyF).2 r hr)
  have hFix2 : Nat.card ↥Fix = 2 := by rw [hj, hj1]; norm_num
  exact hFix2

theorem c23_card_inf_eq_three [Finite U] (h : C23Core Y₁ Y₂ A₁ A₂ Mb) {X : Subgroup (MulAut U)}
    (hX : X ≤ A₁ ⊔ A₂) (hcard : Nat.card X = 9) :
    Nat.card ↥(X ⊓ A₁) = 3 ∧ Nat.card ↥(X ⊓ A₂) = 3 := by
  have hA₁norm : A₁ ≤ Subgroup.normalizer (A₂ : Set (MulAut U)) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    rw [c23_core_commute h ha hb, mul_assoc, mul_inv_cancel, mul_one]
    exact hb
  have hXnorm : X ≤ Subgroup.normalizer (A₂ : Set (MulAut U)) :=
    hX.trans (sup_le hA₁norm Subgroup.le_normalizer)
  have hprod : Nat.card ↥(X ⊔ A₂) * Nat.card ↥(X ⊓ A₂) = 9 * 168 := by
    rw [s16c7_card_sup_mul_card_inf hXnorm, hcard, h.card_A₂]
  have hdvd : Nat.card ↥(X ⊔ A₂) ∣ 168 * 168 := by
    have hle : X ⊔ A₂ ≤ A₁ ⊔ A₂ := sup_le hX le_sup_right
    have := Subgroup.card_dvd_of_le hle
    rwa [c23_core_card_sup h] at this
  set k₂ : ℕ := Nat.card ↥(X ⊓ A₂)
  set k₁ : ℕ := Nat.card ↥(X ⊓ A₁)
  have hk₂dvd : k₂ ∣ 9 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : X ⊓ A₂ ≤ X)
    rwa [hcard] at this
  have hk₂ne : k₂ ≠ 1 := by
    rintro hk
    rw [hk, mul_one] at hprod
    rw [hprod] at hdvd
    norm_num at hdvd
  have hk₂ : k₂ = 3 ∨ k₂ = 9 := by
    have h9 : k₂ ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
      exact hk₂dvd
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9
    interval_cases j
    · exact absurd (by simpa using hj) hk₂ne
    · exact Or.inl (by simpa using hj)
    · exact Or.inr (by simpa using hj)
  have hk₁dvd : k₁ ∣ 9 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : X ⊓ A₁ ≤ X)
    rwa [hcard] at this
  have hk₁ne : k₁ ≠ 1 := by
    have hA₂norm : A₂ ≤ Subgroup.normalizer (A₁ : Set (MulAut U)) := by
      rw [Subgroup.le_normalizer_iff]
      intro a ha b hb
      rw [← c23_core_commute h hb ha, mul_assoc, mul_inv_cancel, mul_one]
      exact hb
    have hXnorm₁ : X ≤ Subgroup.normalizer (A₁ : Set (MulAut U)) :=
      hX.trans (sup_le Subgroup.le_normalizer hA₂norm)
    have hprod₁ : Nat.card ↥(X ⊔ A₁) * k₁ = 9 * 168 := by
      change Nat.card ↥(X ⊔ A₁) * Nat.card ↥(X ⊓ A₁) = 9 * 168
      rw [s16c7_card_sup_mul_card_inf hXnorm₁, hcard, h.card_A₁]
    have hdvd₁ : Nat.card ↥(X ⊔ A₁) ∣ 168 * 168 := by
      have hle : X ⊔ A₁ ≤ A₁ ⊔ A₂ := sup_le hX le_sup_left
      have := Subgroup.card_dvd_of_le hle
      rwa [c23_core_card_sup h] at this
    rintro hk
    rw [hk, mul_one] at hprod₁
    rw [hprod₁] at hdvd₁
    norm_num at hdvd₁
  have hk₁ : k₁ = 3 ∨ k₁ = 9 := by
    have h9 : k₁ ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
      exact hk₁dvd
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9
    interval_cases j
    · exact absurd (by simpa using hj) hk₁ne
    · exact Or.inl (by simpa using hj)
    · exact Or.inr (by simpa using hj)
  have hcomm : ∀ x ∈ X ⊓ A₁, ∀ y ∈ X ⊓ A₂, x * y = y * x :=
    fun x hx y hy => c23_core_commute h hx.2 hy.2
  have hinf : (X ⊓ A₁) ⊓ (X ⊓ A₂) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hxA : x ∈ A₁ ⊓ A₂ := ⟨hx.1.2, hx.2.2⟩
    rw [c23_core_inf_A_eq_bot h] at hxA
    exact hxA
  have hsup_le : (X ⊓ A₁) ⊔ (X ⊓ A₂) ≤ X := sup_le inf_le_left inf_le_left
  have hprod2 : Nat.card ↥((X ⊓ A₁) ⊔ (X ⊓ A₂)) = k₁ * k₂ := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (X ⊓ A₁) (X ⊓ A₂) hcomm).1
    rw [hinf, Subgroup.card_bot, mul_one] at h
    exact h
  have hle9 : k₁ * k₂ ≤ 9 := by
    have hle : Nat.card ↥((X ⊓ A₁) ⊔ (X ⊓ A₂)) ≤ 9 := by
      have := Subgroup.card_le_of_le hsup_le
      rwa [hcard] at this
    rwa [hprod2] at hle
  have hk₁3 : k₁ = 3 := by
    rcases hk₁ with hk | hk
    · exact hk
    · rcases hk₂ with hk₂ | hk₂
      · rw [hk, hk₂] at hle9; norm_num at hle9
      · rw [hk, hk₂] at hle9; norm_num at hle9
  have hk₂3 : k₂ = 3 := by
    rcases hk₂ with hk | hk
    · exact hk
    · rcases hk₁ with hk₁ | hk₁
      · rw [hk₁, hk] at hle9; norm_num at hle9
      · rw [hk₁, hk] at hle9; norm_num at hle9
  exact ⟨hk₁3, hk₂3⟩

theorem c23_unique_fixed [Finite U] (h : C23Core Y₁ Y₂ A₁ A₂ Mb) {X : Subgroup (MulAut U)}
    (hX : X ≤ A₁ ⊔ A₂) (hcard : Nat.card X = 9) {u u' : U} (hu : u ∈ c23Omega Y₁ Y₂)
    (hu' : u' ∈ c23Omega Y₁ Y₂) (hfu : ∀ x ∈ X, (x : MulAut U) u = u)
    (hfu' : ∀ x ∈ X, (x : MulAut U) u' = u') : u = u' := by
  have hR₁ : Nat.card ↥(X ⊓ A₁) = 3 := (c23_card_inf_eq_three h hX hcard).1
  have hR₂ : Nat.card ↥(X ⊓ A₂) = 3 := (c23_card_inf_eq_three h hX hcard).2
  simp only [c23Omega, Set.mem_setOf_eq] at hu hu'
  obtain ⟨hu₁, hu₂⟩ := hu
  obtain ⟨hu₁', hu₂'⟩ := hu'
  obtain ⟨y₁, hy₁, y₂, hy₂, hy₁y₂⟩ :=
    Subgroup.mem_sup.mp (by rw [h.sup_eq]; exact Subgroup.mem_top u)
  obtain ⟨y₁', hy₁', y₂', hy₂', hy₁'y₂'⟩ :=
    Subgroup.mem_sup.mp (by rw [h.sup_eq]; exact Subgroup.mem_top u')
  have hy₁ne : y₁ ≠ 1 := by
    rintro rfl
    rw [one_mul] at hy₁y₂
    exact hu₂ (hy₁y₂ ▸ hy₂)
  have hy₁'ne : y₁' ≠ 1 := by
    rintro rfl
    rw [one_mul] at hy₁'y₂'
    exact hu₂' (hy₁'y₂' ▸ hy₂')
  have hy₂ne : y₂ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hy₁y₂
    exact hu₁ (hy₁y₂ ▸ hy₁)
  have hy₂'ne : y₂' ≠ 1 := by
    rintro rfl
    rw [mul_one] at hy₁'y₂'
    exact hu₁' (hy₁'y₂' ▸ hy₁')
  have hinv₁ : ∀ r ∈ X ⊓ A₁, ∀ y ∈ Y₁, (r : MulAut U) y ∈ Y₁ := by
    intro r hr y hy
    have hmap := c23_core_map_eq₁ h hr.2
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (r : MulAut U).toMonoidHom hy
  have hnt₁ : ∃ r ∈ X ⊓ A₁, ∃ y ∈ Y₁, (r : MulAut U) y ≠ y := by
    haveI : Nontrivial ↥(X ⊓ A₁) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hR₁]
      norm_num
    obtain ⟨r, hrne⟩ := exists_ne (1 : ↥(X ⊓ A₁))
    have hrne' : (r : MulAut U) ≠ 1 := fun hc => hrne (Subtype.ext (by simpa using hc))
    have hex : ∃ u₀ : U, (r : MulAut U) u₀ ≠ u₀ := by
      by_contra hcon
      rw [not_exists] at hcon
      apply hrne'
      ext u₀
      simpa using not_not.mp (hcon u₀)
    obtain ⟨u₀, hu₀⟩ := hex
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subgroup.mem_sup.mp (by rw [h.sup_eq]; exact Subgroup.mem_top u₀)
    refine ⟨(r : MulAut U), r.2, a, ha, ?_⟩
    intro hra
    apply hu₀
    calc (r : MulAut U) u₀ = (r : MulAut U) (a * b) := by rw [hab]
      _ = (r : MulAut U) a * (r : MulAut U) b := map_mul _ _ _
      _ = a * b := by rw [hra, h.triv₁ (r : MulAut U) r.2.2 b hb]
      _ = u₀ := hab
  have hfix₁ : ({y : U | y ∈ Y₁ ∧ ∀ r ∈ X ⊓ A₁, (r : MulAut U) y = y} : Set U).ncard = 2 :=
    c23_ncard_fixed_eq_two (Y := Y₁) (R := X ⊓ A₁) h.card₁ hR₁ hinv₁ hnt₁
  have hy₁fix : y₁ ∈ ({y : U | y ∈ Y₁ ∧ ∀ r ∈ X ⊓ A₁, (r : MulAut U) y = y} : Set U) := by
    refine ⟨hy₁, fun r hr => ?_⟩
    have h1 : (r : MulAut U) u = u := hfu r hr.1
    have h2 : (r : MulAut U) (y₁ * y₂) = y₁ * y₂ := by rw [hy₁y₂]; exact h1
    rw [map_mul, h.triv₁ r hr.2 y₂ hy₂] at h2
    exact mul_right_cancel h2
  have hy₁'fix : y₁' ∈ ({y : U | y ∈ Y₁ ∧ ∀ r ∈ X ⊓ A₁, (r : MulAut U) y = y} : Set U) := by
    refine ⟨hy₁', fun r hr => ?_⟩
    have h1 : (r : MulAut U) u' = u' := hfu' r hr.1
    have h2 : (r : MulAut U) (y₁' * y₂') = y₁' * y₂' := by rw [hy₁'y₂']; exact h1
    rw [map_mul, h.triv₁ r hr.2 y₂' hy₂'] at h2
    exact mul_right_cancel h2
  have h1mem₁ : (1 : U) ∈ ({y : U | y ∈ Y₁ ∧ ∀ r ∈ X ⊓ A₁, (r : MulAut U) y = y} : Set U) :=
    ⟨Y₁.one_mem, fun r _ => map_one (r : MulAut U)⟩
  have hy₁_eq : y₁ = y₁' :=
    c23_eq_of_mem_ncard_two hfix₁ h1mem₁ hy₁fix hy₁'fix hy₁ne hy₁'ne
  have hinv₂ : ∀ r ∈ X ⊓ A₂, ∀ y ∈ Y₂, (r : MulAut U) y ∈ Y₂ := by
    intro r hr y hy
    have hmap := c23_core_map_eq₂ h hr.2
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (r : MulAut U).toMonoidHom hy
  have hnt₂ : ∃ r ∈ X ⊓ A₂, ∃ y ∈ Y₂, (r : MulAut U) y ≠ y := by
    haveI : Nontrivial ↥(X ⊓ A₂) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hR₂]
      norm_num
    obtain ⟨r, hrne⟩ := exists_ne (1 : ↥(X ⊓ A₂))
    have hrne' : (r : MulAut U) ≠ 1 := fun hc => hrne (Subtype.ext (by simpa using hc))
    have hex : ∃ u₀ : U, (r : MulAut U) u₀ ≠ u₀ := by
      by_contra hcon
      rw [not_exists] at hcon
      apply hrne'
      ext u₀
      simpa using not_not.mp (hcon u₀)
    obtain ⟨u₀, hu₀⟩ := hex
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subgroup.mem_sup.mp (by rw [h.sup_eq]; exact Subgroup.mem_top u₀)
    refine ⟨(r : MulAut U), r.2, b, hb, ?_⟩
    intro hrb
    apply hu₀
    calc (r : MulAut U) u₀ = (r : MulAut U) (a * b) := by rw [hab]
      _ = (r : MulAut U) a * (r : MulAut U) b := map_mul _ _ _
      _ = a * b := by rw [h.triv₂ (r : MulAut U) r.2.2 a ha, hrb]
      _ = u₀ := hab
  have hfix₂ : ({y : U | y ∈ Y₂ ∧ ∀ r ∈ X ⊓ A₂, (r : MulAut U) y = y} : Set U).ncard = 2 :=
    c23_ncard_fixed_eq_two (Y := Y₂) (R := X ⊓ A₂) h.card₂ hR₂ hinv₂ hnt₂
  have hy₂fix : y₂ ∈ ({y : U | y ∈ Y₂ ∧ ∀ r ∈ X ⊓ A₂, (r : MulAut U) y = y} : Set U) := by
    refine ⟨hy₂, fun r hr => ?_⟩
    have h1 : (r : MulAut U) u = u := hfu r hr.1
    have h2 : (r : MulAut U) (y₁ * y₂) = y₁ * y₂ := by rw [hy₁y₂]; exact h1
    rw [map_mul, h.triv₂ r hr.2 y₁ hy₁] at h2
    exact mul_left_cancel h2
  have hy₂'fix : y₂' ∈ ({y : U | y ∈ Y₂ ∧ ∀ r ∈ X ⊓ A₂, (r : MulAut U) y = y} : Set U) := by
    refine ⟨hy₂', fun r hr => ?_⟩
    have h1 : (r : MulAut U) u' = u' := hfu' r hr.1
    have h2 : (r : MulAut U) (y₁' * y₂') = y₁' * y₂' := by rw [hy₁'y₂']; exact h1
    rw [map_mul, h.triv₂ r hr.2 y₁' hy₁'] at h2
    exact mul_left_cancel h2
  have h1mem₂ : (1 : U) ∈ ({y : U | y ∈ Y₂ ∧ ∀ r ∈ X ⊓ A₂, (r : MulAut U) y = y} : Set U) :=
    ⟨Y₂.one_mem, fun r _ => map_one (r : MulAut U)⟩
  have hy₂_eq : y₂ = y₂' :=
    c23_eq_of_mem_ncard_two hfix₂ h1mem₂ hy₂fix hy₂'fix hy₂ne hy₂'ne
  rw [← hy₁y₂, ← hy₁'y₂', hy₁_eq, hy₂_eq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
