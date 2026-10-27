module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineGap
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineT
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

theorem noSocle185Factor_perm (hO : LieOrderFormulasInput) (n : ℕ) :
    NoSocle185Factor (Equiv.Perm (Fin n)) := by
  by_cases hn : n ≤ 6
  · refine NoSocle185Factor.of_not_dvd fun T _ hT hd => ?_
    have h720 : Nat.card (Equiv.Perm (Fin n)) ∣ 720 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact (Nat.factorial_dvd_factorial hn : Nat.factorial n ∣ Nat.factorial 6)
    exact (hT.card_facts hO).2.1 (hd.trans h720)
  · have h7 : 7 ≤ n := by omega
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    refine NoSocle185Factor.of_index_two (alternatingGroup (Fin n))
      alternatingGroup.index_eq_two ?_
    haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    refine NoSocle185Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
    obtain ⟨t, m, p, f, hp, hp2, hadm, hY⟩ := hT.oddLieType
    have hodd : CFSG.Blueprint.OddLieType (alternatingGroup (Fin n)) :=
      ⟨t, m, p, f, hp, hp2, hadm, hY.of_mulEquiv e.symm⟩
    rcases (by omega : n = 7 ∨ n = 8 ∨ 9 ≤ n) with rfl | rfl | h9
    · exact CFSG.ComponentClassification.CatFC.not_oddLieType_alt7 hO hodd
    · have : Nat.card T = 20160 := by
        rw [← Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      exact (hT.card_facts hO).2.2.1 this
    · exact CFSG.OddStandard.AltStdSec.not_oddLieType_alt hO h9 hodd

theorem noSocle185Factor_of_isSymGp (hO : LieOrderFormulasInput) {Y : Type} [Group Y] {m : ℕ}
    (h : IsSymGp Y m) : NoSocle185Factor Y := by
  obtain ⟨e⟩ := h
  exact (noSocle185Factor_perm hO m).of_mulEquiv e.symm

end CFSG.LocalAnalysis.WeakClosure81

end
