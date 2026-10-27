module

public import CFSG.Quasithin.Vol2.Ch7NotFF
public import CFSG.Quasithin.Background.HSL3Two

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem not_concl701FF_SL3Pair_one (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711SL3Pair T L I 1 → ¬ Concl701FF T L I := by
  intro _ hrow hFF
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨φ, hφN, hinf, hsup, hniso⟩ := exists_twist hV hN hNM htw
  have hFF' : IsFFModule (V := IntMod (fsuV T I) hV)
      (Subgroup.normalizer (autI hV (fsuL0 T L) : Set (MulAut (IntMod (fsuV T I) hV)))) :=
    isFFModule_of_concl701FF hFF
  have hL : BinaryNaturalSL (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥
      3 1 := hnat
  exact SL3Pair.H4_SL3Two hL hφN hinf hsup hniso le_rfl hFF'

theorem not_concl701FF_SL3Pair_all (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) (n : ℕ) :
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711SL3Pair T L I n → ¬ Concl701FF T L I := by
  intro hc hrow
  rcases Nat.lt_or_ge n 2 with h | h
  · rcases Nat.lt_or_ge n 1 with h0 | h1
    · exfalso
      obtain ⟨-, K, _, _, hK, -⟩ := hrow
      have : Nontrivial K := inferInstance
      have h1 := Finite.one_lt_card (α := K)
      rw [hK, show n = 0 by omega, pow_zero] at h1
      exact lt_irrefl 1 h1
    · obtain rfl : n = 1 := by omega
      exact not_concl701FF_SL3Pair_one hV hN hNM hc hrow
  · exact not_concl701FF_SL3Pair hV hN hNM h hc hrow

end CFSG.Quasithin.H13
