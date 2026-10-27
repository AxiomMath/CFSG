module

public import CFSG.Quasithin.Background.D36GluedNDBase
public import CFSG.Quasithin.EmptyFaithful.S151bRank

public section

namespace CFSG.Quasithin

namespace A5Lift

section Lift

variable {Y : Type} [CommGroup Y]

theorem lift_fixed (hY : ∀ y : Y, y ^ 2 = 1) {Z : Subgroup Y} {e₁ e₂ c : MulAut Y}
    (h₁Z : ∀ z ∈ Z, e₁ z = z) (h₂Z : ∀ z ∈ Z, e₂ z = z) (hcZ : ∀ z ∈ Z, c z = z)
    (hce₁ : c * e₁ * c⁻¹ = e₂) (hce₂ : c * e₂ * c⁻¹ = e₁ * e₂) {u : Y}
    (hu₁ : e₁ u * u⁻¹ ∈ Z) (huc : c u * u⁻¹ ∈ Z) : e₁ u = u ∧ e₂ u = u := by
  have hsq : ∀ z : Y, z * z = 1 := fun z => by rw [← pow_two]; exact hY z
  have hcinvZ : ∀ z ∈ Z, c⁻¹ z = z := fun z hz => by
    calc c⁻¹ z = c⁻¹ (c z) := by rw [hcZ z hz]
      _ = z := MulAut.inv_apply_self _ _ _
  obtain ⟨a, ha⟩ : ∃ a : Y, a = e₁ u * u⁻¹ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Y, d = c u * u⁻¹ := ⟨_, rfl⟩
  rw [← ha] at hu₁
  rw [← hd] at huc
  have hea : e₁ u = a * u := by rw [ha, inv_mul_cancel_right]
  have hcd : c u = d * u := by rw [hd, inv_mul_cancel_right]
  have hcinv : c⁻¹ u = d * u := by
    have h1 : c⁻¹ (c u) = c⁻¹ (d * u) := by rw [hcd]
    rw [map_mul, hcinvZ d huc] at h1
    simp only [MulAut.inv_apply_self] at h1
    calc c⁻¹ u = d⁻¹ * (d * c⁻¹ u) := by group
      _ = d⁻¹ * u := by rw [← h1]
      _ = d * u := by rw [inv_eq_of_mul_eq_one_right (hsq d)]
  have hb : e₂ u = a * u := by
    calc e₂ u = (c * e₁ * c⁻¹) u := by rw [hce₁]
      _ = c (e₁ (c⁻¹ u)) := by simp only [MulAut.mul_apply]
      _ = c (e₁ (d * u)) := by rw [hcinv]
      _ = c (d * (a * u)) := by rw [map_mul, h₁Z d huc, hea]
      _ = d * (a * (d * u)) := by rw [map_mul, map_mul, hcZ d huc, hcZ a hu₁, hcd]
      _ = (d * d) * (a * u) := by ac_rfl
      _ = a * u := by rw [hsq d, one_mul]
  have hl : (e₁ * e₂) u = u := by
    calc (e₁ * e₂) u = e₁ (a * u) := by rw [MulAut.mul_apply, hb]
      _ = a * (a * u) := by rw [map_mul, h₁Z a hu₁, hea]
      _ = (a * a) * u := by rw [mul_assoc]
      _ = u := by rw [hsq a, one_mul]
  have hlhs : (c * e₂ * c⁻¹) u = u := by rw [hce₂]; exact hl
  have hrhs : (c * e₂ * c⁻¹) u = a * u := by
    calc (c * e₂ * c⁻¹) u = c (e₂ (c⁻¹ u)) := by simp only [MulAut.mul_apply]
      _ = c (e₂ (d * u)) := by rw [hcinv]
      _ = c (d * (a * u)) := by rw [map_mul, h₂Z d huc, hb]
      _ = d * (a * (d * u)) := by rw [map_mul, map_mul, hcZ d huc, hcZ a hu₁, hcd]
      _ = (d * d) * (a * u) := by ac_rfl
      _ = a * u := by rw [hsq d, one_mul]
  have hau : a * u = u := hrhs.symm.trans hlhs
  have ha1 : a = 1 := by simpa using hau
  exact ⟨by rw [hea, ha1, one_mul], by rw [hb, ha1, one_mul]⟩

end Lift

section Klein

variable {Y : Type} [CommGroup Y]

theorem klein_ids {e₁ e₂ : MulAut Y} (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1)
    (hc : e₁ * e₂ = e₂ * e₁) : e₁ * (e₁ * e₂) = e₂ ∧ e₁ * e₂ * e₁ = e₂ ∧ e₂ * (e₁ * e₂) = e₁ ∧
      e₁ * e₂ * e₂ = e₁ ∧ e₁ * e₂ * (e₁ * e₂) = 1 ∧ e₂ * e₁ = e₁ * e₂ := by
  have i1 : e₁ * (e₁ * e₂) = e₂ := by rw [← mul_assoc, h₁, one_mul]
  have i3 : e₂ * (e₁ * e₂) = e₁ := by rw [hc, ← mul_assoc, h₂, one_mul]
  exact ⟨i1, by rw [mul_assoc, ← hc, i1], i3, by rw [mul_assoc, h₂, mul_one],
    by rw [mul_assoc, i3, h₁], hc.symm⟩

@[expose] def kleinSub (e₁ e₂ : MulAut Y) (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1)
    (hc : e₁ * e₂ = e₂ * e₁) : Subgroup (MulAut Y) where
  carrier := {x | x = 1 ∨ x = e₁ ∨ x = e₂ ∨ x = e₁ * e₂}
  one_mem' := Or.inl rfl
  mul_mem' := by
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := klein_ids h₁ h₂ hc
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp [i1, i2, i3, i4, i5, i6, h₁, h₂]
  inv_mem' := by
    obtain ⟨-, -, -, -, -, i6⟩ := klein_ids h₁ h₂ hc
    rintro x (rfl | rfl | rfl | rfl)
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right h₁))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right h₂)))
    · right; right; right
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h₁, inv_eq_of_mul_eq_one_right h₂, i6]

theorem kleinSub_isElemAbelian2 {e₁ e₂ : MulAut Y} (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1)
    (hc : e₁ * e₂ = e₂ * e₁) : IsElemAbelian2 (kleinSub e₁ e₂ h₁ h₂ hc) := by
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := klein_ids h₁ h₂ hc
  refine ⟨?_, ?_⟩
  · rintro a (rfl | rfl | rfl | rfl) b (rfl | rfl | rfl | rfl) <;>
      simp [i1, i2, i3, i4, i5, i6, h₁, h₂]
  · rintro a (rfl | rfl | rfl | rfl) <;> simp [pow_two, i5, h₁, h₂]

theorem kleinSub_subset {e₁ e₂ : MulAut Y} (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1)
    (hc : e₁ * e₂ = e₂ * e₁) [DecidableEq (MulAut Y)] :
    ((kleinSub e₁ e₂ h₁ h₂ hc : Subgroup (MulAut Y)) : Set (MulAut Y)) ⊆
      (({1, e₁, e₂, e₁ * e₂} : Finset (MulAut Y)) : Set (MulAut Y)) := by
  intro x hx
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  exact hx

theorem card_kleinSub_le_four {e₁ e₂ : MulAut Y} (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1)
    (hc : e₁ * e₂ = e₂ * e₁) : Nat.card ↥(kleinSub e₁ e₂ h₁ h₂ hc) ≤ 4 := by
  classical
  have hcard : Nat.card ↥(kleinSub e₁ e₂ h₁ h₂ hc) =
      (kleinSub e₁ e₂ h₁ h₂ hc : Set (MulAut Y)).ncard := Nat.card_coe_set_eq _
  rw [hcard]
  calc (kleinSub e₁ e₂ h₁ h₂ hc : Set (MulAut Y)).ncard
      ≤ (({1, e₁, e₂, e₁ * e₂} : Finset (MulAut Y)) : Set (MulAut Y)).ncard :=
        Set.ncard_le_ncard (kleinSub_subset h₁ h₂ hc) (Finset.finite_toSet _)
    _ = ({1, e₁, e₂, e₁ * e₂} : Finset (MulAut Y)).card := Set.ncard_coe_finset _
    _ ≤ 4 := Finset.card_le_four

theorem three_le_card_kleinSub {e₁ e₂ : MulAut Y} (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1)
    (hc : e₁ * e₂ = e₂ * e₁) (hne1 : e₁ ≠ 1) (hne2 : e₂ ≠ 1) (hne : e₁ ≠ e₂) :
    3 ≤ Nat.card ↥(kleinSub e₁ e₂ h₁ h₂ hc) := by
  classical
  have hsub : (({1, e₁, e₂} : Finset (MulAut Y)) : Set (MulAut Y)) ⊆
      ((kleinSub e₁ e₂ h₁ h₂ hc : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  have h3 : ({1, e₁, e₂} : Finset (MulAut Y)).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, e₁, e₂, hne1.symm, hne2.symm, hne, rfl⟩
  have hcard : Nat.card ↥(kleinSub e₁ e₂ h₁ h₂ hc) =
      (kleinSub e₁ e₂ h₁ h₂ hc : Set (MulAut Y)).ncard := Nat.card_coe_set_eq _
  have hfin : (kleinSub e₁ e₂ h₁ h₂ hc : Set (MulAut Y)).Finite :=
    Set.Finite.subset (Finset.finite_toSet ({1, e₁, e₂, e₁ * e₂} : Finset (MulAut Y)))
      (kleinSub_subset h₁ h₂ hc)
  rw [hcard]
  calc 3 = (({1, e₁, e₂} : Finset (MulAut Y)) : Set (MulAut Y)).ncard := by
        rw [Set.ncard_coe_finset, h3]
    _ ≤ (kleinSub e₁ e₂ h₁ h₂ hc : Set (MulAut Y)).ncard := Set.ncard_le_ncard hsub hfin

theorem kleinSub_cubic [Finite Y] (hY : ∀ y : Y, y ^ 2 = 1) {e₁ e₂ : MulAut Y}
    (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1) (hc : e₁ * e₂ = e₂ * e₁) :
    commSeries (kleinSub e₁ e₂ h₁ h₂ hc) 3 = ⊥ :=
  commSeries_three_eq_bot_of_card_le_four151b hY (kleinSub_isElemAbelian2 h₁ h₂ hc)
    (card_kleinSub_le_four h₁ h₂ hc)

end Klein

end A5Lift

open A5Lift

section Glued

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace NDSetup

variable (S : NDSetup X A L₀ U U')

include S

theorem false_of_klein {e₁ e₂ c : MulAut Y} (he₁ : e₁ ∈ L₀) (he₂ : e₂ ∈ L₀) (hc : c ∈ L₀)
    (h₁ : e₁ * e₁ = 1) (h₂ : e₂ * e₂ = 1) (hcomm : e₁ * e₂ = e₂ * e₁) (hne1 : e₁ ≠ 1)
    (hne2 : e₂ ≠ 1) (hne : e₁ ≠ e₂) (hce₁ : c * e₁ * c⁻¹ = e₂)
    (hce₂ : c * e₂ * c⁻¹ = e₁ * e₂) {u : Y} (huU : u ∈ U) (huZ : u ∉ U ⊓ fixV L₀)
    (hu₁ : e₁ u * u⁻¹ ∈ U ⊓ fixV L₀) (huc : c u * u⁻¹ ∈ U ⊓ fixV L₀)
    (hk : rk ↥(A ⊓ stabSub U) = 2) (hr : rk ↥U - rk ↥(U ⊓ fixV L₀) ≤ 4)
    (hsu : 5 ≤ (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) +
      (rk ↥U - rk ↥(U ⊓ U'))) : False := by
  obtain ⟨hu1, hu2⟩ := lift_fixed S.exp (Z := U ⊓ fixV L₀) (fun z hz => hz.2 e₁ he₁)
    (fun z hz => hz.2 e₂ he₂) (fun z hz => hz.2 c hc) hce₁ hce₂ hu₁ huc
  set E := kleinSub e₁ e₂ h₁ h₂ hcomm with hE
  have hEL : E ≤ L₀ := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact he₁
    · exact he₂
    · exact mul_mem he₁ he₂
  have hEel : IsElemAbelian2 E := kleinSub_isElemAbelian2 h₁ h₂ hcomm
  have hEne : E ≠ ⊥ := by
    intro hbot
    have : e₁ ∈ E := Or.inr (Or.inl rfl)
    rw [hbot, Subgroup.mem_bot] at this
    exact hne1 this
  have hE2 : IsA2 X E := ⟨hEL.trans S.le_X, hEne, hEel⟩
  have hE3 : commSeries E 3 = ⊥ := kleinSub_cubic S.exp h₁ h₂ hcomm
  have hcmp := S.swap.compare_cubic hE2 hE3 (fun e he u' hu' => S.cent e (hEL he) u' hu')
  have hE3c : 3 ≤ Nat.card E := three_le_card_kleinSub h₁ h₂ hcomm hne1 hne2 hne
  have hEcard : Nat.card E = 2 ^ rk E := B1.card_elemAbelian hEel
  have hrkE : 2 ≤ rk ↥E := by
    by_contra hcon
    have : 2 ^ rk ↥E ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have huE : u ∈ fixV E := by
    rintro x (rfl | rfl | rfl | rfl)
    · rfl
    · exact hu1
    · exact hu2
    · show (e₁ * e₂) u = u
      rw [MulAut.mul_apply, hu2, hu1]
  have hZE : U ⊓ fixV L₀ ≤ U ⊓ fixV E := inf_le_inf_left U (fun z hz x hx => hz x (hEL hx))
  have hlt : rk ↥(U ⊓ fixV L₀) < rk ↥(U ⊓ fixV E) := by
    by_contra hcon
    push Not at hcon
    have heq := eq_of_le_of_rk_le S.exp hZE hcon
    exact huZ (heq ▸ ⟨huU, huE⟩)
  have hUE : rk ↥(U ⊓ fixV E) ≤ rk ↥U := rk_mono inf_le_left
  rw [hk] at hcmp
  generalize (rk ↥U - rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U'))) +
    (rk ↥U - rk ↥(U ⊓ U')) = w at hcmp hsu
  generalize rk ↥E = q at hcmp hrkE
  have h1 : rk ↥U - rk ↥(U ⊓ fixV E) ≤ 3 := by omega
  have h2 : 5 * 2 ≤ w * q := Nat.mul_le_mul hsu hrkE
  have h3 : (2 + 1) * (rk ↥U - rk ↥(U ⊓ fixV E)) ≤ (2 + 1) * 3 := Nat.mul_le_mul_left _ h1
  omega

end NDSetup

end Glued

end CFSG.Quasithin
