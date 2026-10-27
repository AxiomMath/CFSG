module

public import CFSG.Quasithin.Vol2.Ch7NotFFTwo
public import CFSG.Quasithin.Background.HA7Alpha
public import Certificates.Certificate7022
public import Certificates.Certificate7067

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem not_concl701FF_S7Pair (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711S7Pair T L I → ¬ Concl701FF T L I := by
  intro _ hrow hFF
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨φ, hφN, hinf, hsup, hniso⟩ := exists_twist hV hN hNM htw
  have hFF' : IsFFModule (V := IntMod (fsuV T I) hV)
      (Subgroup.normalizer (autI hV (fsuL0 T L) : Set (MulAut (IntMod (fsuV T I) hV)))) :=
    isFFModule_of_concl701FF hFF
  have hL : A7Four (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥ := hnat
  exact (A7.H8_A7Pair_alpha hL hφN hinf hsup hniso le_rfl).2.2 hFF'

theorem not_concl701FF_twistedPair
    (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    ∀ _ : IsMulCommutative ↥(fsuV T I),
      ((∃ n : ℕ, Row711SL3Pair T L I n) ∨ Row711Sp4Pair T L I ∨ Row711S7Pair T L I) →
        ¬ Concl701FF T L I := by
  intro hc h
  rcases h with ⟨n, hn⟩ | h | h
  · exact not_concl701FF_SL3Pair_all hV hN hNM n hc hn
  · exact not_concl701FF_Sp4Pair hV hN hNM hc h
  · exact not_concl701FF_S7Pair hV hN hNM hc h

end CFSG.Quasithin.H13
