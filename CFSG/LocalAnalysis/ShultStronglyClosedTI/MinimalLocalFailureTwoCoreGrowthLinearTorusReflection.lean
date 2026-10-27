module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u

variable {G : Type u} [Group G]

theorem reflection_join_normal_form (T : Subgroup G) (w : G)
    (hw : w ∈ Subgroup.normalizer (T : Set G)) (hwsq : w * w = 1)
    (g : G) (hg : g ∈ T ⊔ Subgroup.zpowers w) :
    ∃ a ∈ T, g = a ∨ g = a * w := by
  have hwi : w⁻¹ = w := by
    have h := congrArg (fun y : G => w⁻¹ * y) hwsq
    simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using h.symm
  let R : Subgroup G :=
    { carrier := {g | ∃ a ∈ T, g = a ∨ g = a * w}
      one_mem' := ⟨1, T.one_mem, Or.inl rfl⟩
      mul_mem' := by
        rintro g h ⟨a, ha, hga | hga⟩ ⟨b, hb, hhb | hhb⟩
        · exact ⟨a * b, T.mul_mem ha hb, Or.inl (by rw [hga, hhb])⟩
        · exact ⟨a * b, T.mul_mem ha hb, Or.inr (by rw [hga, hhb]; group)⟩
        · refine ⟨a * (w * b * w⁻¹), T.mul_mem ha
            ((Subgroup.mem_normalizer_iff.mp hw b).mp hb), Or.inr ?_⟩
          rw [hga, hhb]
          group
        · refine ⟨a * (w * b * w⁻¹), T.mul_mem ha
            ((Subgroup.mem_normalizer_iff.mp hw b).mp hb), Or.inl ?_⟩
          calc
            g * h = (a * (w * b * w⁻¹)) * (w * w) := by rw [hga, hhb]; group
            _ = a * (w * b * w⁻¹) := by rw [hwsq, mul_one]
      inv_mem' := by
        rintro g ⟨a, ha, hga | hga⟩
        · exact ⟨a⁻¹, T.inv_mem ha, Or.inl (congrArg Inv.inv hga)⟩
        · refine ⟨w * a⁻¹ * w⁻¹,
            (Subgroup.mem_normalizer_iff.mp hw a⁻¹).mp (T.inv_mem ha), Or.inr ?_⟩
          calc
            g⁻¹ = w * a⁻¹ := by rw [hga, mul_inv_rev, hwi]
            _ = (w * a⁻¹ * w⁻¹) * w := by group }
  have hTR : T ≤ R := fun a ha => ⟨a, ha, Or.inl rfl⟩
  have hwR : w ∈ R := ⟨1, T.one_mem, Or.inr (one_mul w).symm⟩
  exact (sup_le hTR (Subgroup.zpowers_le_of_mem hwR)) hg

theorem reflection_join_action (T : Subgroup G) [IsCyclic T] (w : G)
    (hw : w ∈ Subgroup.normalizer (T : Set G)) (hwsq : w * w = 1)
    (hinv : ∀ x : G, x ∈ T → w * x * w⁻¹ = x⁻¹)
    (g : G) (hg : g ∈ T ⊔ Subgroup.zpowers w) :
    (∀ x : G, x ∈ T → g * x * g⁻¹ = x) ∨
      (∀ x : G, x ∈ T → g * x * g⁻¹ = x⁻¹) := by
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val
      ((@IsMulCommutative.is_comm T _ IsCyclic.isMulCommutative).comm
        (⟨a, ha⟩ : T) (⟨b, hb⟩ : T))
  obtain ⟨a, ha, hga | hga⟩ := reflection_join_normal_form T w hw hwsq g hg
  · left
    intro x hx
    rw [hga, hcomm a ha x hx]
    group
  · right
    intro x hx
    calc
      g * x * g⁻¹ = a * (w * x * w⁻¹) * a⁻¹ := by rw [hga]; group
      _ = a * x⁻¹ * a⁻¹ := by rw [hinv x hx]
      _ = x⁻¹ := by rw [hcomm a ha x⁻¹ (T.inv_mem hx)]; group

theorem odd_nonidentity_ne_inverse (x : G) (hx : x ≠ 1)
    (hxodd : Odd (orderOf x)) : x ≠ x⁻¹ := by
  intro heq
  have hsq : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x⁻¹ * x := congrArg (fun y : G => y * x) heq
      _ = 1 := inv_mul_cancel x
  have hdiv : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
  have hone : orderOf x = 1 := hxodd.coprime_two_right.eq_one_of_dvd hdiv
  exact hx (orderOf_eq_one_iff.mp hone)

theorem odd_element_centralizer_eq_reflection_torus
    (T : Subgroup G) [IsCyclic T] (w x : G)
    (hw : w ∈ Subgroup.normalizer (T : Set G)) (hwsq : w * w = 1)
    (hinv : ∀ y : G, y ∈ T → w * y * w⁻¹ = y⁻¹)
    (hxT : x ∈ T) (hx : x ≠ 1) (hxodd : Odd (orderOf x))
    (hnormalizer : Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      T ⊔ Subgroup.zpowers w) :
    Subgroup.centralizer ({x} : Set G) = T ∧
      ∀ u : G, u * x * u⁻¹ = x⁻¹ →
        ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
          u * y * u⁻¹ = y⁻¹ := by
  have hneinv := odd_nonidentity_ne_inverse x hx hxodd
  have hTC : T ≤ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val
      ((@IsMulCommutative.is_comm T _ IsCyclic.isMulCommutative).comm
        (⟨a, ha⟩ : T) (⟨x, hxT⟩ : T))
  have hcentralizer : Subgroup.centralizer ({x} : Set G) = T := by
    apply le_antisymm _ hTC
    intro g hg
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hfix : g * x * g⁻¹ = x := by rw [hcomm]; group
    have hgN : g ∈ Subgroup.normalizer
        ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (g * x * g⁻¹) = Subgroup.zpowers x
      rw [hfix]
    rw [hnormalizer] at hgN
    obtain ⟨a, ha, hga | hga⟩ := reflection_join_normal_form T w hw hwsq g hgN
    · simpa only [hga] using ha
    · have hinverted : g * x * g⁻¹ = x⁻¹ := by
        calc
          g * x * g⁻¹ = a * (w * x * w⁻¹) * a⁻¹ := by rw [hga]; group
          _ = a * x⁻¹ * a⁻¹ := by rw [hinv x hxT]
          _ = x⁻¹ := by
            have hacomm := Subgroup.mem_centralizer_singleton_iff.mp (hTC ha)
            have hacomminv : a * x⁻¹ = x⁻¹ * a := (Commute.symm
              (show Commute a x from hacomm)).inv_left.eq.symm
            rw [hacomminv]
            group
      exact False.elim (hneinv (hfix.symm.trans hinverted))
  refine ⟨hcentralizer, ?_⟩
  intro u hux y hy
  have huN : u ∈ Subgroup.normalizer
      ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (u * x * u⁻¹) = Subgroup.zpowers x
    rw [hux, Subgroup.zpowers_inv]
  rw [hnormalizer] at huN
  rcases reflection_join_action T w hw hwsq hinv u huN with hidentity | hinversion
  · exact False.elim (hneinv ((hidentity x hxT).symm.trans hux))
  · exact hinversion y (hcentralizer ▸ hy)

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
