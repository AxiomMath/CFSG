module

public import CFSG.CharacterTheory.Semidihedral.ParameterFiveGeneration

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.BenderSuzuki PFAppendixIII PFchapter1section1
open CFSG.Semidihedral.ParameterFive

variable {G : Type} [Group G]

theorem solvable_of_conj
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {t : G} (ht : orderOf t = 2) {M : Subgroup G} (hCM : Subgroup.centralizer {t} ≤ M)
    (hconj : ∀ x ∈ M, orderOf x = 2 → ∃ m ∈ M, m * t * m⁻¹ = x)
    (hrank : ∃ E : Subgroup G, Nat.card E = 4 ∧ ∀ x ∈ E, x ^ 2 = 1)
    (hMtop : M ≠ ⊤) : Group.IsSolvable M := by
  have hM := isStronglyEmbedded_of_conj ht hMtop hCM hconj
  have hL : involutionCore G = ⊤ := hM.involutionCore_eq_top_of_isSimple inferInstance
  rcases theorem_SE M hM with hlow | hB
  · exfalso
    apply hlow
    obtain ⟨E, hE4, hE2⟩ := hrank
    refine ⟨E.subgroupOf (involutionCore G), ?_, ?_⟩
    · have hEL : E ≤ involutionCore G := hL ▸ le_top
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE4]
    · rintro ⟨⟨x, hxL⟩, hxE⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hE2 x hxE
  · obtain ⟨-, -, hsolv, -⟩ := hB
    replace hsolv : Group.IsSolvable _ := hsolv
    set L := involutionCore G with hLdef
    let eL : L ≃* G := (MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv
    have hmemL : ∀ x : G, x ∈ L := fun x => by rw [hL]; exact Subgroup.mem_top x
    have hsimpleL : IsSimpleGroup L := eL.isSimpleGroup_congr.mpr inferInstance
    have hcore : twoPrimeCore L = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (twoPrimeCore L) with h | h
      · exact h
      · exfalso
        have htL : t ∈ L := hmemL t
        have hodd : Odd (Nat.card (twoPrimeCore L)) :=
          Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := L))
        have htcore : (⟨t, htL⟩ : L) ∈ twoPrimeCore L := h ▸ Subgroup.mem_top _
        have h2 : orderOf (⟨⟨t, htL⟩, htcore⟩ : twoPrimeCore L) = 2 := by
          rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
          exact ht
        have := orderOf_dvd_natCard (⟨⟨t, htL⟩, htcore⟩ : twoPrimeCore L)
        rw [h2] at this
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    set B := (((M ⊓ L).subgroupOf L).map (QuotientGroup.mk' (twoPrimeCore L))) with hBdef
    let φ : M →* B :=
      { toFun := fun c => ⟨QuotientGroup.mk' (twoPrimeCore L) ⟨c, hmemL c⟩,
          ⟨⟨c, hmemL c⟩, ⟨c.2, hmemL c⟩, rfl⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := by
      intro a b hab
      have h := congrArg Subtype.val hab
      change QuotientGroup.mk' (twoPrimeCore L) _ = QuotientGroup.mk' (twoPrimeCore L) _ at h
      rw [QuotientGroup.mk'_eq_mk', hcore] at h
      obtain ⟨z, hz, hzeq⟩ := h
      rw [Subgroup.mem_bot] at hz
      rw [hz, mul_one] at hzeq
      exact Subtype.ext (congrArg (fun x : L => (x : G)) hzeq)
    exact Group.isSolvable_of_isSolvable_injective hφ

end CFSG.Quasithin.H13.F431.L3
