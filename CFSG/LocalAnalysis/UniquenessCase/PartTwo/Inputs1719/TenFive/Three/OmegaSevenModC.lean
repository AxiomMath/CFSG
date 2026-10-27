module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private lemma omSevenC_inv_mapsTo {U : Subgroup W} {t : MulAut W}
    (ht : ∀ u ∈ U, t u ∈ U) : ∀ u ∈ U, t⁻¹ u ∈ U := by
  have hle : U.map (t : W →* W) ≤ U := by
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    exact ht u hu
  have hcard : Nat.card ↥(U.map (t : W →* W)) = Nat.card ↥U :=
    Subgroup.card_map_of_injective t.injective
  have heq : U.map (t : W →* W) = U := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard]
  intro u hu
  have hu' : u ∈ U.map (t : W →* W) := by rw [heq]; exact hu
  obtain ⟨v, hv, hv_eq⟩ := hu'
  have hvu : (t⁻¹ : MulAut W) u = v := by
    rw [MulAut.inv_apply, ← hv_eq]
    exact MulEquiv.symm_apply_apply t v
  rwa [hvu]

private lemma omSevenC_zpow_mapsTo {U : Subgroup W} {t : MulAut W}
    (ht : ∀ u ∈ U, t u ∈ U) (k : ℤ) : ∀ u ∈ U, (t ^ k) u ∈ U := by
  induction k using Int.induction_on with
  | zero =>
      intro u hu
      simpa using hu
  | succ i ih =>
      intro u hu
      have hz : (t : MulAut W) ^ ((i : ℤ) + 1) = t * t ^ (i : ℤ) := by
        rw [Int.add_comm, zpow_one_add]
      rw [hz, MulAut.mul_apply]
      exact ht _ (ih u hu)
  | pred i ih =>
      intro u hu
      have hz : (t : MulAut W) ^ (-(i : ℤ) - 1) = t ^ (-(i : ℤ)) * t⁻¹ := by
        rw [zpow_sub_one]
      rw [hz, MulAut.mul_apply]
      exact ih _ (omSevenC_inv_mapsTo ht u hu)

private lemma omSevenC_mul_mem_sup {U : Subgroup W} {t t' : MulAut W}
    (ht : ∀ u ∈ U, t u ∈ U) (ht' : ∀ u ∈ U, t' u ∈ U) {u : W} (hu : u ∈ U) :
    (t * t') u * u⁻¹ ∈ commSub U (zpowers t) ⊔ commSub U (zpowers t') := by
  have h1 : t (t' u) * (t' u)⁻¹ ∈ commSub U (zpowers t) :=
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, t' u, ht' u hu, rfl⟩
  have h2 : t' u * u⁻¹ ∈ commSub U (zpowers t') :=
    Subgroup.subset_closure ⟨t', Subgroup.mem_zpowers t', u, hu, rfl⟩
  have hkey : (t * t') u * u⁻¹ = (t (t' u) * (t' u)⁻¹) * (t' u * u⁻¹) := by
    rw [MulAut.mul_apply]
    group
  rw [hkey]
  exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)

theorem commSub_zpowers_mul_le {U : Subgroup W} {t t' : MulAut W} (ht : ∀ u ∈ U, t u ∈ U)
    (ht' : ∀ u ∈ U, t' u ∈ U) :
    commSub U (zpowers (t * t')) ≤ commSub U (zpowers t) ⊔ commSub U (zpowers t') := by
  rw [commSub, Subgroup.closure_le]
  rintro c ⟨x, hx, w, hw, rfl⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  clear hx
  have hstab : ∀ u ∈ U, (t * t') u ∈ U := fun u hu => ht _ (ht' u hu)
  induction k using Int.induction_on with
  | zero => simpa using Subgroup.one_mem _
  | succ i ih =>
      have hw1 : ((t * t') ^ (i : ℤ)) w ∈ U := omSevenC_zpow_mapsTo hstab (i : ℤ) w hw
      have hz : (t * t') ^ ((i : ℤ) + 1) = (t * t') * (t * t') ^ (i : ℤ) := by
        rw [Int.add_comm, zpow_one_add]
      rw [hz, MulAut.mul_apply]
      set w₁ : W := ((t * t') ^ (i : ℤ)) w with hw₁
      have hw1U : w₁ ∈ U := by rw [hw₁]; exact hw1
      have hkey : (t * t') w₁ * w⁻¹ = ((t * t') w₁ * w₁⁻¹) * (w₁ * w⁻¹) := by
        group
      rw [hkey]
      exact mul_mem (omSevenC_mul_mem_sup ht ht' hw1U) ih
  | pred i ih =>
      have hw2 : ((t * t') ^ (-(i : ℤ) - 1)) w ∈ U :=
        omSevenC_zpow_mapsTo hstab _ w hw
      set w₂ : W := ((t * t') ^ (-(i : ℤ) - 1)) w with hw₂
      have hw2U : w₂ ∈ U := by rw [hw₂]; exact hw2
      have hz : (t * t') ^ (-(i : ℤ) - 1) = (t * t') ^ (-(i : ℤ)) * (t * t')⁻¹ := by
        rw [zpow_sub_one]
      have hgw2 : (t * t') w₂ = ((t * t') ^ (-(i : ℤ))) w := by
        rw [hw₂]
        have hmul : (t * t') * (t * t') ^ (-(i : ℤ) - 1) = (t * t') ^ (-(i : ℤ)) := by
          rw [← zpow_one_add, show (1 : ℤ) + (-(i : ℤ) - 1) = -(i : ℤ) by ring]
        rw [← MulAut.mul_apply, hmul]
      have hkey : w₂ * w⁻¹ = ((t * t') w₂ * w₂⁻¹)⁻¹ * ((t * t') w₂ * w⁻¹) := by
        group
      rw [hkey]
      exact mul_mem (inv_mem (omSevenC_mul_mem_sup ht ht' hw2U)) (by rw [hgw2]; exact ih)

theorem rk_commSub_zpowers_conj_of_stable {U : Subgroup W} {g t : MulAut W}
    (hg : ∀ u ∈ U, g u ∈ U) (hg' : ∀ u ∈ U, g⁻¹ u ∈ U) :
    rk ↥(commSub U (zpowers (g * t * g⁻¹))) = rk ↥(commSub U (zpowers t)) := by
  have heq :
      commSub U (zpowers (g * t * g⁻¹)) = (commSub U (zpowers t)).map (g : W →* W) := by
    apply le_antisymm
    · rw [commSub, Subgroup.closure_le]
      rintro c ⟨x, hx, w, hw, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      refine Subgroup.mem_map.mpr ⟨(t ^ k) (g⁻¹ w) * (g⁻¹ w)⁻¹, ?_, ?_⟩
      · exact Subgroup.subset_closure
          ⟨t ^ k, Subgroup.zpow_mem_zpowers t k, g⁻¹ w, hg' w hw, rfl⟩
      · rw [conj_zpow, map_mul, map_inv]
        simp [MulAut.mul_apply]
    · rw [commSub, MonoidHom.map_closure (g : W →* W), Subgroup.closure_le]
      rintro _ ⟨c, hc, rfl⟩
      obtain ⟨x, hx, u, hu, rfl⟩ := hc
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hgen : g ((t ^ k) u * u⁻¹) = ((g * t * g⁻¹) ^ k) (g u) * (g u)⁻¹ := by
        rw [conj_zpow, map_mul, map_inv]
        simp [MulAut.mul_apply]
      change g ((t ^ k) u * u⁻¹) ∈ commSub U (zpowers (g * t * g⁻¹))
      rw [hgen]
      exact Subgroup.subset_closure
        ⟨(g * t * g⁻¹) ^ k, Subgroup.zpow_mem_zpowers _ k, g u, hg u hu, rfl⟩
  have hcard : Nat.card ↥((commSub U (zpowers t)).map (g : W →* W)) =
      Nat.card ↥(commSub U (zpowers t)) :=
    Subgroup.card_map_of_injective (f := (g : W →* W)) g.injective
  rw [heq]
  unfold rk
  rw [hcard]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
