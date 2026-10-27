module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Stab
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Gen

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open scoped Pointwise commutatorElement
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem leviSU_mem_u5LnStab (A : SpecialLinearGroup (Fin 2) K) :
    leviSU h 1 A ∈ u5LnStab h := by
  rw [mem_u5LnStab_iff, mat_leviSU]
  intro a b hb ha
  rcases hb with rfl | rfl <;> rcases ha with rfl | rfl | rfl <;> simp [ιe₁, ιe₂, ιz, ιf₁, ιf₂]

theorem N₁sub_le_u5LnStab : N₁sub h ≤ u5LnStab h := by
  rintro _ ⟨A, rfl⟩
  exact leviSU_mem_u5LnStab A

theorem N₁sub_le_perfectCore_u5LnStab : N₁sub h ≤ perfectCore (u5LnStab h) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h)
  exact range_le_perfectCore this (leviSU h 1) N₁sub_le_u5LnStab

theorem exists_torus_line (hf : 2 ≤ f) :
    ∃ t ∈ Isub h, t ∈ N₁sub h ∧ ∀ a b : HypIndex 2 1, a ≠ b → mat t a a ≠ mat t b b := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  obtain ⟨⟨htI, htN⟩, e1, e2⟩ := leviSU_diagSL (h := h) ω
  set t := leviSU h 1 (diagSL ω) with ht
  have e3 : mat t ιz ιz = 1 := by
    rw [ht, mat_leviSU]
    simp [ιz]
  have b1 := torus_bar_mul htI ιe₁
  have b2 := torus_bar_mul htI ιe₂
  simp only [hypPartner_inl] at b1 b2
  have E1 : mat t ιe₁ ιe₁ = ((ω ^ (1 : ℤ) : Kˣ) : K) := by rw [e1]; simp
  have E2 : mat t ιe₂ ιe₂ = ((ω ^ (-1 : ℤ) : Kˣ) : K) := by rw [e2]; simp
  have E3 : mat t ιz ιz = ((ω ^ (0 : ℤ) : Kˣ) : K) := by rw [e3]; simp
  have E4 : mat t ιf₁ ιf₁ = ((ω ^ (-(((2 ^ f : ℕ) : ℤ) * 1)) : Kˣ) : K) := by
    rw [eq_inv_of_mul_eq_one_right b1, E1, bar_zpow, ← Units.val_inv_eq_inv_val, ← _root_.zpow_neg]
  have E5 : mat t ιf₂ ιf₂ = ((ω ^ (-(((2 ^ f : ℕ) : ℤ) * -1)) : Kˣ) : K) := by
    rw [eq_inv_of_mul_eq_one_right b2, E2, bar_zpow, ← Units.val_inv_eq_inv_val, ← _root_.zpow_neg]
  refine ⟨t, htI, htN, fun a b hab => ?_⟩
  have key : ∀ {m n : ℤ}, m ≠ n → m - n ≤ 2 * ((2 ^ f : ℕ) : ℤ) →
      n - m ≤ 2 * ((2 ^ f : ℕ) : ℤ) → ((ω ^ m : Kˣ) : K) ≠ ((ω ^ n : Kˣ) : K) :=
    fun h0 h1 h2 => zpow_val_ne_of_le hω hf h0 h1 h2
  have hq := four_le_q hf
  have hcases : ∀ a : HypIndex 2 1, a = ιe₁ ∨ a = ιe₂ ∨ a = ιz ∨ a = ιf₂ ∨ a = ιf₁ := by decide
  rcases hcases a with rfl | rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | (simp only [E1, E2, E3, E4, E5]; exact key (by omega) (by omega) (by omega))

theorem U_le_perfectCore_u5LnStab (hf : 2 ≤ f) :
    hypUnitriangular h 2 1 ≤ perfectCore (u5LnStab h) := by
  have : Finite (hypSU h 2 1) := by have := h.finite; infer_instance
  obtain ⟨t, htI, htN, hne⟩ := exists_torus_line (h := h) hf
  have htP : t ∈ perfectCore (u5LnStab h) := N₁sub_le_perfectCore_u5LnStab htN
  have hUP : hypUnitriangular h 2 1 ≤ u5LnStab h :=
    (hypUnitriangular_le_hypBorel h).trans (hypBorel_le_isoStabilizer h (by norm_num) le_rfl)
  have hfix : ∀ v ∈ hypUnitriangular h 2 1, ∀ z ∈ (⊥ : Subgroup (hypSU h 2 1)),
      t * v * t⁻¹ = v * z → v ∈ (⊥ : Subgroup (hypSU h 2 1)) := by
    intro v hv z hz e
    rw [Subgroup.mem_bot] at hz
    subst hz
    rw [mul_one] at e
    refine Subgroup.mem_bot.2 (eq_of_U_entries hv (one_mem _) fun a b hab => ?_)
    have e1 : mat (t * v * t⁻¹) a b = mat v a b := by rw [e]
    rw [torus_conj_apply htI] at e1
    have hb := torus_ne_zero htI b
    have hab' : a ≠ b := fun e => (lt_irrefl _) (e ▸ hab)
    have : mat v a b * (mat t a a - mat t b b) = 0 := by
      field_simp at e1
      linear_combination e1
    rw [mat_one, one_apply_ne hab']
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 (hne a b hab'))
  have key := exists_commutator_mul (U := hypUnitriangular h 2 1) (Z := ⊥)
    (fun z hz u hu => by rw [Subgroup.mem_bot.mp hz]; simp) (t := t)
    (fun u hu => torus_conj_mem_U htI hu) (fun z hz => by rw [Subgroup.mem_bot.mp hz]; simp) hfix
  intro g hg
  obtain ⟨u, hu, z, hz, rfl⟩ := key g hg
  rw [Subgroup.mem_bot.mp hz, mul_one]
  have := normalizer_le_normalizer_perfectCore (u5LnStab h) (Subgroup.le_normalizer (hUP hu))
  exact mul_mem ((Subgroup.mem_normalizer_iff.mp this t).mp htP) (inv_mem htP)

theorem mat_Vsub_apply {v : hypSU h 2 1} (hv : v ∈ Vsub h) (c d : HypIndex 2 1)
    (hcd : ¬((c = ιe₁ ∨ c = ιe₂) ∧ (d = ιf₁ ∨ d = ιf₂))) :
    mat v c d = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) c d := by
  obtain ⟨hvU, a1, a2, a3, a4, a5, a6⟩ := mem_Vsub'.1 hv
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩⟩ := U_entries hvU
  rcases hypIndex_cases c with rfl | rfl | rfl | rfl | rfl <;>
    rcases hypIndex_cases d with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [ιe₁, ιe₂, ιz, ιf₁, ιf₂]

theorem conj_mem_Vsub_of_mem_u5LnStab {g v : hypSU h 2 1} (hg : g ∈ u5LnStab h)
    (hv : v ∈ Vsub h) : g * v * g⁻¹ ∈ Vsub h := by
  have hG := (mem_u5LnStab_iff g).1 hg
  have hGi : ∀ d b : HypIndex 2 1, (d = ιf₁ ∨ d = ιf₂) → (b = ιe₁ ∨ b = ιe₂ ∨ b = ιz) →
      mat g⁻¹ d b = 0 := by
    intro d b hd hb
    rw [mat_inv_apply]
    have : mat g (hypPartner b) (hypPartner d) = 0 := by
      apply hG
      · rcases hd with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rcases hb with rfl | rfl | rfl
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
    rw [this, map_zero]
  set E := mat v - 1 with hE
  have hEv : mat v = 1 + E := by rw [hE]; abel
  have hconj : mat (g * v * g⁻¹) = 1 + mat g * E * mat g⁻¹ := by
    rw [mat_mul, mat_mul, hEv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← mat_mul,
      mul_inv_cancel, mat_one]
  have hEz : ∀ c d : HypIndex 2 1, ¬((c = ιe₁ ∨ c = ιe₂) ∧ (d = ιf₁ ∨ d = ιf₂)) → E c d = 0 := by
    intro c d hcd
    rw [hE, Matrix.sub_apply, mat_Vsub_apply hv c d hcd, sub_self]
  have hent : ∀ a b : HypIndex 2 1, ¬((a = ιe₁ ∨ a = ιe₂) ∧ (b = ιf₁ ∨ b = ιf₂)) →
      mat (g * v * g⁻¹) a b = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) a b := by
    intro a b hab
    rw [hconj, Matrix.add_apply]
    suffices (mat g * E * mat g⁻¹) a b = 0 by rw [this, add_zero]
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hcd : (c = ιe₁ ∨ c = ιe₂) ∧ (d = ιf₁ ∨ d = ιf₂)
    · by_cases ha : a = ιe₁ ∨ a = ιe₂
      · have hb : b = ιe₁ ∨ b = ιe₂ ∨ b = ιz := by
          rcases hypIndex_cases b with h1 | h1 | h1 | h1 | h1
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr h1)
          · exact absurd ⟨ha, Or.inr h1⟩ hab
          · exact absurd ⟨ha, Or.inl h1⟩ hab
        rw [hGi d b hcd.2 hb, mul_zero]
      · have ha' : a = ιz ∨ a = ιf₂ ∨ a = ιf₁ := by
          rcases hypIndex_cases a with h1 | h1 | h1 | h1 | h1
          · exact absurd (Or.inl h1) ha
          · exact absurd (Or.inr h1) ha
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr h1)
        rw [hG a c hcd.1 ha', zero_mul, zero_mul]
    · rw [hEz c d hcd]
      simp
  have hne : ∀ a b : HypIndex 2 1, fullPos a < fullPos b → a ≠ b := fun a b hab e =>
    (lt_irrefl _) (e ▸ hab)
  have hU : g * v * g⁻¹ ∈ hypUnitriangular h 2 1 := by
    rw [mem_hypUnitriangular]
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · have hna : ¬((a = ιe₁ ∨ a = ιe₂) ∧ (b = ιf₁ ∨ b = ιf₂)) := by
        rintro ⟨ha, hb⟩
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact absurd hab (by decide)
      change mat (g * v * g⁻¹) a b = 0
      rw [hent a b hna, one_apply_ne (hne b a hab).symm]
    · have hna : ¬((a = ιe₁ ∨ a = ιe₂) ∧ (a = ιf₁ ∨ a = ιf₂)) := by
        rintro ⟨ha, hb⟩
        rcases ha with rfl | rfl <;> rcases hb with h1 | h1 <;> exact absurd h1 (by decide)
      change mat (g * v * g⁻¹) a a = 1
      rw [hent a a hna, one_apply_eq]
  refine mem_Vsub'.2 ⟨hU, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hent _ _ (by decide), one_apply_ne (by decide)]

end CFSG.Quasithin.H13.Sec53F.Unit
