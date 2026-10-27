module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec19.SimsC198AutCrit
import CFSG.RankThree.PartTwo.Sec19.SimsC198Crit
import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.Sporadic.Bridge.M11
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.J1
import CFSG.Sporadic.Bridge.J2
import CFSG.Sporadic.Bridge.M23Surj
import CFSG.Sporadic.Bridge.J3Surj
import CFSG.Sporadic.Presentation.McLExact
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.M24
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.HS
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.He
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Ru
import CFSG.RankThree.PartTwo.Census.Sporadic.J4Bridge
import CFSG.RankThree.Asc83Table.M23
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
import CFSG.RankThree.PartTwo.KFacts.K426J3
import CFSG.RankThree.PartTwo.KFacts.K426RestMcL
import CFSG.RankThree.PartTwo.KFacts.K426RestON
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.PairJ3CertBase
import CFSG.RankThree.PartTwo.Sec19.SimsC198Iso

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem noAutDatum_of_mulEquiv_card {S T : Type} [Group S] [Finite S] [IsSimpleGroup S]
    [Group T] (e : S ≃* T) (hout : ¬ 3 ∣ Nat.card (Outer T)) (h81 : ¬ 81 ∣ Nat.card T) :
    NoAutDatum S :=
  noAutDatum_of_out_card
    (by rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]; exact hout)
    (by rw [Nat.card_congr e.toEquiv]; exact h81)

private theorem noAutDatum_M11
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* Sec4.Spor .M11) :
    NoAutDatum S := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have e' : S ≃* NativeSporadic.M11 := e.trans b.symm
  haveI : Finite NativeSporadic.M11 := Finite.of_equiv S e'.toEquiv
  refine noAutDatum_of_mulEquiv_card (T := NativeSporadic.M11) e'
    (Sec4.not_three_dvd_card_outer_of_le_two CFSG.Sporadic.Schreier.at_m11_schreier.1) ?_
  rw [CFSG.Sporadic.Mathieu.card_M11]
  norm_num

private theorem noAutDatum_M12
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* Sec4.Spor .M12) :
    NoAutDatum S := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have e' : S ≃* NativeSporadic.M12 := e.trans b.symm
  haveI : Finite NativeSporadic.M12 := Finite.of_equiv S e'.toEquiv
  refine noAutDatum_of_mulEquiv_card (T := NativeSporadic.M12) e'
    (Sec4.not_three_dvd_card_outer_of_le_two
      (CFSG.ComponentClassification.M12Cover.card_outer).le) ?_
  rw [CFSG.Sporadic.Mathieu.card_M12]
  norm_num

private theorem noAutDatum_M22
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* Sec4.Spor .M22) :
    NoAutDatum S := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have e' : S ≃* NativeSporadic.M22 := e.trans b.symm
  haveI : Finite NativeSporadic.M22 := Finite.of_equiv S e'.toEquiv
  refine noAutDatum_of_mulEquiv_card (T := NativeSporadic.M22) e'
    (Sec4.not_three_dvd_card_outer_of_le_two
      (Sec4.card_outer_le_two_of_card_mulAut_le CFSG.Sporadic.Schreier.m22_center_eq_bot'
        CFSG.Sporadic.Schreier.m22_mulAut_card)) ?_
  rw [CFSG.Sporadic.Mathieu.card_M22]
  norm_num

private theorem noAutDatum_M23
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* Sec4.Spor .M23) :
    NoAutDatum S := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have e' : S ≃* NativeSporadic.M23 := e.trans b.symm
  haveI : Finite NativeSporadic.M23 := Finite.of_equiv S e'.toEquiv
  refine noAutDatum_of_mulEquiv_card (T := NativeSporadic.M23) e'
    (Sec4.not_three_dvd_card_outer_of_le_two CFSG.Sporadic.Schreier.at_m23_schreier.1) ?_
  rw [CFSG.RankThree.Asc83Table.M23.card_M23]
  norm_num

private theorem noAutDatum_M24
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* Sec4.Spor .M24) :
    NoAutDatum S := by
  haveI : IsSimpleGroup TauCeti.SporadicName.M24.Group := e.symm.isSimpleGroup
  obtain ⟨b⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_M24
  have e' : S ≃* NativeSporadic.M24 := e.trans b
  haveI : Finite NativeSporadic.M24 := Finite.of_equiv S e'.toEquiv
  refine noAutDatum_of_mulEquiv_card (T := NativeSporadic.M24) e'
    (Sec4.not_three_dvd_card_outer_of_le_two
      (Sec4.card_outer_le_two_of_card_mulAut_le CFSG.Sporadic.Schreier.m24_center_eq_bot'
        (CFSG.Sporadic.Schreier.m24_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num)))))
    ?_
  rw [CFSG.Sporadic.Mathieu.card_M24]
  norm_num

private theorem noAutDatum_J1
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* Sec4.Spor .J1) :
    NoAutDatum S := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  have e' : S ≃* NativeSporadic.J1 := e.trans b.symm
  haveI : Finite NativeSporadic.J1 := Finite.of_equiv S e'.toEquiv
  refine noAutDatum_of_mulEquiv_card (T := NativeSporadic.J1) e'
    (Sec4.not_three_dvd_card_outer_of_le_two
      (CFSG.Sporadic.Schreier.at_j1_schreier.1.le.trans (by norm_num))) ?_
  rw [CFSG.Sporadic.J1.card_J1]
  norm_num

private theorem noAutDatum_J2
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* Sec4.Spor .J2) :
    NoAutDatum S := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have e' : S ≃* NativeSporadic.J2 := e.trans b.symm
  haveI : Finite NativeSporadic.J2 := Finite.of_equiv S e'.toEquiv
  refine noAutDatum_of_mulEquiv_card (T := NativeSporadic.J2) e'
    (Sec4.not_three_dvd_card_outer_of_le_two Sec4.card_outer_J2) ?_
  rw [CFSG.Sporadic.J2.card_J2]
  norm_num

private theorem noAutDatum_HS
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* Sec4.Spor .HS) :
    NoAutDatum S := by
  haveI : IsSimpleGroup TauCeti.SporadicName.HS.Group := e.symm.isSimpleGroup
  obtain ⟨b⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_HS
  have e' : S ≃* NativeSporadic.HS := e.trans b
  haveI : Finite NativeSporadic.HS := Finite.of_equiv S e'.toEquiv
  refine noAutDatum_of_mulEquiv_card (T := NativeSporadic.HS) e'
    (Sec4.not_three_dvd_card_outer_of_le_two Sec4.card_outer_HS) ?_
  rw [CFSG.Sporadic.HS.card_HS]
  norm_num

private theorem noAutDatum_Ru
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* Sec4.Spor .Ru) :
    NoAutDatum S := by
  haveI : IsSimpleGroup TauCeti.SporadicName.Ru.Group := e.symm.isSimpleGroup
  obtain ⟨b⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Ru
  have e' : S ≃* NativeSporadic.Ru := e.trans b
  haveI : Finite NativeSporadic.Ru := Finite.of_equiv S e'.toEquiv
  refine noAutDatum_of_mulEquiv_card (T := NativeSporadic.Ru) e'
    (Sec4.not_three_dvd_card_outer_of_le_two Sec4.card_outer_Ru) ?_
  rw [CFSG.Sporadic.Ru.card_Ru]
  norm_num

private theorem noAutDatum_He
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* Sec4.Spor .He) :
    NoAutDatum S := by
  haveI : IsSimpleGroup TauCeti.SporadicName.He.Group := e.symm.isSimpleGroup
  obtain ⟨b⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_He
  have e' : S ≃* NativeSporadic.He := e.trans b
  haveI : Finite NativeSporadic.He := Finite.of_equiv S e'.toEquiv
  refine noAutDatum_of_mulEquiv_card (T := NativeSporadic.He) e'
    (Sec4.not_three_dvd_card_outer_of_le_two CFSG.Sporadic.Schreier.AT_He_Schreier.1) ?_
  rw [CFSG.Sporadic.He.card_He]
  norm_num

private theorem noAutDatum_J4
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* Sec4.Spor .J4) :
    NoAutDatum S := by
  haveI : IsSimpleGroup TauCeti.SporadicName.J4.Group := e.symm.isSimpleGroup
  obtain ⟨b⟩ := CFSG.RankThree.PartTwo.Census.nonempty_mulEquiv_carrier_J4
  have e' : S ≃* NativeSporadic.J4 := e.trans b
  haveI : Finite NativeSporadic.J4 := Finite.of_equiv S e'.toEquiv
  refine noAutDatum_of_mulEquiv_card (T := NativeSporadic.J4) e'
    (Sec4.not_three_dvd_card_outer_of_le_two
      (CFSG.AGLEmbedding.card_outer_J4.le.trans (by norm_num))) ?_
  rw [CFSG.Sporadic.J4.card_J4]
  norm_num

theorem noAutDatum_spor_small
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .HS ∨
      s = .Ru ∨ s = .He ∨ s = .J4)
    (e : S ≃* CFSG.RankThree.PartTwo.Sec4.Spor s) : NoAutDatum S := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact noAutDatum_M11 e
  · exact noAutDatum_M12 e
  · exact noAutDatum_M22 e
  · exact noAutDatum_M23 e
  · exact noAutDatum_M24 e
  · exact noAutDatum_J1 e
  · exact noAutDatum_J2 e
  · exact noAutDatum_HS e
  · exact noAutDatum_Ru e
  · exact noAutDatum_He e
  · exact noAutDatum_J4 e

private theorem prime_le_five_of_dvd {a b c r : ℕ} (hr : r.Prime) (hd : r ∣ 2 ^ a * 3 ^ b * 5 ^ c) :
    r ≤ 5 := by
  rcases (Nat.Prime.dvd_mul hr).1 hd with h | h
  · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact (Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h)).trans (by norm_num)
    · exact (Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h)).trans (by norm_num)
  · exact Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h)

private theorem not_dvd_of_smooth {a b c n N : ℕ} (hn : n = 2 ^ a * 3 ^ b * 5 ^ c)
    (hN : IsType198Card N) : ¬ N ∣ n := by
  intro hd
  obtain ⟨r, hr, hr7, hrN⟩ := IsType198Card.exists_prime N hN
  have := prime_le_five_of_dvd hr (hn ▸ hrN.trans hd)
  omega

private theorem card_centralizer_j3P
    (c : CFSG.Sporadic.Schreier.j3P) (hc : orderOf c = 3) :
    Nat.card (Subgroup.centralizer ({c} : Set CFSG.Sporadic.Schreier.j3P)) = 1080 ∨
      Nat.card (Subgroup.centralizer ({c} : Set CFSG.Sporadic.Schreier.j3P)) = 243 := by
  have hxo : orderOf (c : Equiv.Perm (Fin 6156)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hc
  have hcard : Nat.card (Subgroup.centralizer ({c} : Set CFSG.Sporadic.Schreier.j3P)) =
      Nat.card (Subgroup.centralizer ({(c : Equiv.Perm (Fin 6156))} : Set (Equiv.Perm (Fin 6156))) ⊓
        CFSG.Sporadic.Schreier.j3P : Subgroup (Equiv.Perm (Fin 6156))) :=
    CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv (MulEquiv.refl _) c
  rw [hcard]
  obtain ⟨k, hk, d, hd, e, he, hkc⟩ := CFSG.RankThree.PartTwo.KFacts.K426.j3t_fusion c.2 hxo
  rw [hkc]
  rcases hd with rfl | rfl
  · have hcube : CFSG.RankThree.PartTwo.KFacts.K426.j3tXA ^ 3 = 1 :=
      (CFSG.RankThree.PartTwo.KFacts.K426.j3tReps_spec (c := 0) (by norm_num)).2
    rw [CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk hcube he]
    left
    rw [← CFSG.RankThree.PartTwo.KFacts.K426.j3t_caseA.1]
    exact CFSG.RankThree.PartTwo.KFacts.K426.j3t_caseA.2
  · have hcube : CFSG.RankThree.PartTwo.KFacts.K426.j3tXB ^ 3 = 1 :=
      (CFSG.RankThree.PartTwo.KFacts.K426.j3tReps_spec (c := 1) (by norm_num)).2
    rw [CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk hcube he]
    right
    rw [← CFSG.RankThree.PartTwo.KFacts.K426.j3t_caseB.1]
    exact CFSG.RankThree.PartTwo.KFacts.K426.j3t_caseB.2

private theorem noLocalDatum_J3
    {S : Type} [Group S] [Finite S] (e : S ≃* Sec4.Spor .J3) : NoLocalDatum S := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have e' : S ≃* CFSG.Sporadic.Schreier.j3P :=
    e.trans (b.symm.trans CFSG.Sporadic.Schreier.j3PermEquiv)
  refine NoLocalDatum.of_mulEquiv (S' := CFSG.Sporadic.Schreier.j3P) e'
    (noLocalDatum_of_centralizer fun c hc N hN => ?_)
  rcases card_centralizer_j3P c hc with h | h <;> rw [h]
  · exact not_dvd_of_smooth (a := 3) (b := 3) (c := 1) (by norm_num) hN
  · exact not_dvd_of_smooth (a := 0) (b := 5) (c := 0) (by norm_num) hN

private theorem noLocalDatum_McL
    {S : Type} [Group S] [Finite S] (e : S ≃* Sec4.Spor .McL) : NoLocalDatum S := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have e' : S ≃* NativeSporadic.McL := e.trans b.symm
  haveI : Finite NativeSporadic.McL := Finite.of_equiv S e'.toEquiv
  refine NoLocalDatum.of_mulEquiv (S' := NativeSporadic.McL) e'
    (noLocalDatum_of_centralizer fun c hc N hN => ?_)
  rcases CFSG.RankThree.PartTwo.KFacts.K426Rest.mclThreeCentralizerCard c hc with h | h <;> rw [h]
  · exact not_dvd_of_smooth (a := 3) (b := 6) (c := 1) (by norm_num) hN
  · exact not_dvd_of_smooth (a := 2) (b := 5) (c := 0) (by norm_num) hN

private theorem noLocalDatum_ON
    {S : Type} [Group S] [Finite S] (e : S ≃* Sec4.Spor .ONan) : NoLocalDatum S := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have e' : S ≃* NativeSporadic.ON := e.trans b.symm
  haveI : Finite NativeSporadic.ON := Finite.of_equiv S e'.toEquiv
  refine NoLocalDatum.of_mulEquiv (S' := NativeSporadic.ON) e'
    (noLocalDatum_of_centralizer fun c hc N hN => ?_)
  rw [CFSG.RankThree.PartTwo.KFacts.K426Rest.onThreeCentralizer c hc]
  exact not_dvd_of_smooth (a := 3) (b := 4) (c := 1) (by norm_num) hN

theorem noLocalDatum_spor_cent
    {S : Type} [Group S] [Finite S] {s : TauCeti.SporadicName}
    (hs : s = .J3 ∨ s = .McL ∨ s = .ONan)
    (e : S ≃* CFSG.RankThree.PartTwo.Sec4.Spor s) : NoLocalDatum S := by
  rcases hs with rfl | rfl | rfl
  · exact noLocalDatum_J3 e
  · exact noLocalDatum_McL e
  · exact noLocalDatum_ON e

end CFSG.RankThree.PartTwo.Sec19.SimsC198
