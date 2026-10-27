module

public import CFSG.Quasithin.MS93.M16Basic

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin MulAction

theorem eq_of_card_fixedBy {A X : Type*} [Group A] [MulAction A X] [Finite A] [Finite X]
    (x₀ : X) (hx₀ : ∀ a : A, a • x₀ = x₀) (hcard : Nat.card X ≤ Nat.card A)
    (hc : ∀ a b : A, a ≠ 1 → b ≠ 1 →
      Nat.card (fixedBy X a) = Nat.card (fixedBy X b)) :
    ∀ (a : A) (x : X), a • x = x := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have : Fintype X := Fintype.ofFinite X
  have : Fintype (Quotient (orbitRel A X)) := Fintype.ofFinite _
  by_cases hA : ∀ a : A, a = 1
  · intro a x; rw [hA a, one_smul]
  push Not at hA
  obtain ⟨a₀, ha₀⟩ := hA
  set c := Nat.card (fixedBy X a₀) with hcdef
  have hB := sum_card_fixedBy_eq_card_orbits_mul_card_group A X
  have hsum : ∑ a : A, Fintype.card (fixedBy X a) =
      Fintype.card X + (Fintype.card A - 1) * c := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : A))]
    have h1 : Fintype.card (fixedBy X (1 : A)) = Fintype.card X := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      simp
    rw [h1]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => c), Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, smul_eq_mul]
    intro a ha
    rw [← Nat.card_eq_fintype_card]
    exact hc a a₀ (Finset.ne_of_mem_erase ha) ha₀
  have hc1 : 1 ≤ c := by
    rw [hcdef]
    have : Nonempty (fixedBy X a₀) := ⟨⟨x₀, hx₀ a₀⟩⟩
    exact Nat.card_pos
  have hcX : c ≤ Fintype.card X := by
    rw [hcdef, ← Nat.card_eq_fintype_card]
    exact Nat.card_mono (Set.toFinite _) (Set.subset_univ _) |>.trans (by simp)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcard
  have hA1 : 1 ≤ Fintype.card A := Fintype.card_pos
  have key : (Fintype.card X : ℤ) - c =
      ((Fintype.card (Quotient (orbitRel A X)) : ℤ) - c) * Fintype.card A := by
    have h := hsum.symm.trans hB
    zify [hA1] at h
    linarith
  have hk : (Fintype.card (Quotient (orbitRel A X)) : ℤ) - c = 0 := by
    have ha : (0 : ℤ) < Fintype.card A := by exact_mod_cast hA1
    have h1 : 0 ≤ ((Fintype.card (Quotient (orbitRel A X)) : ℤ) - c) * Fintype.card A := by
      rw [← key]; linarith
    have h2 : ((Fintype.card (Quotient (orbitRel A X)) : ℤ) - c) * Fintype.card A <
        Fintype.card A := by
      rw [← key]; linarith
    have h3 := nonneg_of_mul_nonneg_left h1 ha
    have h4 : (Fintype.card (Quotient (orbitRel A X)) : ℤ) - c < 1 := by
      by_contra h5
      push Not at h5
      nlinarith
    omega
  have hcx : c = Fintype.card X := by
    rw [hk, zero_mul] at key
    omega
  intro a x
  by_cases ha : a = 1
  · rw [ha, one_smul]
  have hca : Nat.card (fixedBy X a) = Nat.card X := by
    rw [hc a a₀ ha ha₀, ← hcdef, hcx, Nat.card_eq_fintype_card]
  have hall : fixedBy X a = Set.univ := (Set.eq_univ_iff_ncard _).mpr hca
  have hx : x ∈ fixedBy X a := hall ▸ Set.mem_univ x
  exact hx

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

theorem rootElt_apply_eq_of_card_le [Finite F] [Finite V] (ρ : SL3 F →* MulAut V)
    (R : Subgroup V) {i j : Fin 3} (hR : Nat.card R ≤ Nat.card F)
    (hX : ∀ c : F, ∀ r ∈ R, ρ (rootElt i j c) r ∈ R)
    (hH : ∀ c c' : F, c ≠ 0 → c' ≠ 0 → ∃ h : SL3 F, h * rootElt i j c * h⁻¹ = rootElt i j c' ∧
      ∀ r ∈ R, ρ h r ∈ R)
    (c : F) {r : V} (hr : r ∈ R) : ρ (rootElt i j c) r = r := by
  let act : MulAction (Multiplicative F) ↥R :=
    { smul := fun a r => ⟨ρ (rootElt i j (Multiplicative.toAdd a)) r, hX _ r r.2⟩
      one_smul := fun r => Subtype.ext (by
        change ρ (rootElt i j (Multiplicative.toAdd 1)) r = r
        simp)
      mul_smul := fun a b r => Subtype.ext (by
        change ρ (rootElt i j (Multiplicative.toAdd (a * b))) r =
          ρ (rootElt i j (Multiplicative.toAdd a)) (ρ (rootElt i j (Multiplicative.toAdd b)) r)
        rw [toAdd_mul, rootElt_add, rho_mul]) }
  have hsmul : ∀ (a : Multiplicative F) (r : ↥R),
      ((a • r : ↥R) : V) = ρ (rootElt i j (Multiplicative.toAdd a)) r := fun _ _ => rfl
  have hle : ∀ a b : Multiplicative F, a ≠ 1 → b ≠ 1 →
      Nat.card (fixedBy ↥R a) ≤ Nat.card (fixedBy ↥R b) := by
    intro a b ha hb
    obtain ⟨h, hconj, hhR⟩ := hH (Multiplicative.toAdd a) (Multiplicative.toAdd b)
      (by simpa using ha) (by simpa using hb)
    let f : fixedBy ↥R a → fixedBy ↥R b := fun x =>
      ⟨⟨ρ h x.1, hhR _ x.1.2⟩, by
        have hx := x.2
        rw [mem_fixedBy] at hx ⊢
        apply Subtype.ext
        rw [hsmul]
        change ρ (rootElt i j (Multiplicative.toAdd b)) (ρ h x.1) = ρ h x.1
        rw [← hconj, rho_mul, rho_mul, rho_inv_rho, ← hsmul, hx]⟩
    refine Nat.card_le_card_of_injective f fun x y hxy => ?_
    have h1 := congrArg (fun z : fixedBy ↥R b => ((z.1 : ↥R) : V)) hxy
    simp only [f] at h1
    have h2 : ρ h⁻¹ (ρ h x.1) = ρ h⁻¹ (ρ h y.1) := by rw [h1]
    rw [rho_inv_rho, rho_inv_rho] at h2
    exact Subtype.ext (Subtype.ext h2)
  have htriv := eq_of_card_fixedBy (A := Multiplicative F) (X := ↥R) 1
    (fun a => Subtype.ext (by rw [hsmul]; exact map_one _))
    ((Nat.card_congr Multiplicative.toAdd).trans_le hR)
    (fun a b ha hb => le_antisymm (hle a b ha hb) (hle b a hb ha))
  have := congrArg Subtype.val (htriv (Multiplicative.ofAdd c) ⟨r, hr⟩)
  rwa [hsmul] at this

end CFSG.Quasithin.MS93.M16
