module

public import CFSG.Quasithin.H13.KG14726L115CDefs
public import CFSG.Quasithin.H13.KGFactAutCover
public import CFSG.Quasithin.H13.KGFactX27Over
public import CFSG.Sporadic.Schreier.PairJ2Pairs

public section

namespace CFSG.Quasithin.H13.KGSpor726

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms CFSG.Quasithin.H13.KGX27
  CFSG.Quasithin.H13.KGAutCover

@[expose] def SporData (S : Type) [Group S] : Prop :=
  IsSimpleGroup S ∧ Nat.card (Outer S) ≤ 2 ∧
    NoIndexOvergroup 27 fun (Y : Type) [Group Y] => Nonempty (Y ≃* S)

theorem false_of_sporData {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    {S : Type} [Group S] (hS : SporData S) (e : X ⧸ CFSG.pCore 2 X ≃* S)
    {A B : Subgroup (MulAut X)} (hA : (MulAut.conj : X →* MulAut X).range ≤ A) (hBA : B ≤ A)
    (hodd : ¬ 2 ∣ (B.subgroupOf A).index) {a : ℕ} (hB : Nat.card B = 2 ^ a * 27) : False := by
  obtain ⟨hsimp, hout, hno⟩ := hS
  have : Group.IsPerfect X := hq.1
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  have hS' : IsSimpleGroup (X ⧸ CFSG.pCore 2 X) := e.isSimpleGroup
  have eZ : X ⧸ Subgroup.center X ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq (center_eq_pCore hq hS')).trans e
  have hout' : Nat.card (Outer (X ⧸ Subgroup.center X)) ≤ 2 := by
    rw [Nat.card_congr (equivalence eZ).toEquiv]
    exact hout
  obtain ⟨H, P, hP2, hPi, hPH, hHc⟩ := exists_overgroup_of_odd_index hout' hA hBA hodd hB
  exact hno _ ⟨(innerEquiv X).symm.trans eZ⟩ H P hP2 hPi hPH hHc

theorem card_outer_le_two_of_card_mulAut_le {Y : Type} [Group Y] [Finite Y]
    (hc : Subgroup.center Y = ⊥) (h : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) :
    Nat.card (Outer Y) ≤ 2 := by
  have hI := CFSG.Sporadic.Schreier.card_inner_of_center_eq_bot hc
  have h1 := Subgroup.card_mul_index (inner Y)
  rw [hI, Subgroup.index_eq_card] at h1
  have hpos : 0 < Nat.card Y := Nat.card_pos
  have h2 : Nat.card Y * Nat.card (Outer Y) ≤ Nat.card Y * 2 := by
    rw [h1, mul_comm]
    exact h
  exact Nat.le_of_mul_le_mul_left h2 hpos

theorem noIndexOvergroup_of_card {S : Type} [Group S] {N : ℕ} (hS : Nat.card S = N)
    (hN : ¬ 27 ∣ N) : NoIndexOvergroup 27 fun (Y : Type) [Group Y] => Nonempty (Y ≃* S) :=
  noIndexOvergroup_of_not_dvd fun Y _ _ ⟨e⟩ => by
    rw [Nat.card_congr e.toEquiv, hS]
    exact hN

theorem sporData_m11 :
    SporData (NativeSporadic.Carrier .M11) :=
  ⟨CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2,
    CFSG.Sporadic.Schreier.at_m11_schreier.1,
    noIndexOvergroup_of_card CFSG.Sporadic.Mathieu.card_M11 (by norm_num)⟩

theorem sporData_m12 :
    SporData (NativeSporadic.Carrier .M12) :=
  ⟨CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2,
    CFSG.ComponentClassification.M12Cover.card_outer.le,
    noIndexOvergroup_m12 (Or.inr rfl)⟩

theorem sporData_m22 :
    SporData (NativeSporadic.Carrier .M22) :=
  ⟨CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2,
    card_outer_le_two_of_card_mulAut_le (Y := ↥NativeSporadic.M22)
      CFSG.Sporadic.Schreier.m22_center_eq_bot'
      CFSG.Sporadic.Schreier.m22_mulAut_card,
    noIndexOvergroup_of_card CFSG.Sporadic.Mathieu.card_M22 (by norm_num)⟩

theorem sporData_m23 :
    SporData (NativeSporadic.Carrier .M23) :=
  ⟨CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2,
    CFSG.Sporadic.Schreier.at_m23_schreier.1,
    noIndexOvergroup_of_card CFSG.Sporadic.Schreier.m23_card (by norm_num)⟩

theorem sporData_m24 :
    SporData (NativeSporadic.Carrier .M24) :=
  ⟨CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2,
    card_outer_le_two_of_card_mulAut_le (Y := ↥NativeSporadic.M24)
      CFSG.Sporadic.Schreier.m24_center_eq_bot'
      (CFSG.Sporadic.Schreier.m24_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))),
    noIndexOvergroup_m24⟩

theorem sporData_he :
    SporData (NativeSporadic.Carrier .He) :=
  ⟨CFSG.Sporadic.He.isSimpleGroup_He,
    CFSG.Sporadic.Schreier.AT_He_Schreier.1,
    noIndexOvergroup_he⟩

theorem sporData_hs :
    SporData (NativeSporadic.Carrier .HS) :=
  ⟨CFSG.Sporadic.HS.isSimpleGroup_HS,
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.hs_outer_card_le
      CFSG.Sporadic.Schreier.hsPermEquiv,
    noIndexOvergroup_of_card CFSG.Sporadic.HS.card_HS (by norm_num)⟩

theorem sporData_j2 :
    SporData (NativeSporadic.Carrier .J2) :=
  ⟨CFSG.Sporadic.J2.isSimpleGroup_J2,
    CFSG.Sporadic.Schreier.AT_J2_Schreier.1,
    noIndexOvergroup_j2⟩

theorem sporData_ru :
    SporData (NativeSporadic.Carrier .Ru) :=
  ⟨CFSG.Sporadic.Ru.isSimpleGroup_Ru,
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv
      (by rw [CFSG.Sporadic.RuSchreier.card_outer_ruP]; norm_num) CFSG.Sporadic.RuSchreier.ruEquivP,
    noIndexOvergroup_ru (Or.inr rfl)⟩

theorem kg14726L115Spor_holds :
    KG14726L115Spor := by
  intro X _ _ s hs hq ⟨e⟩ A hA B hBA hodd ⟨a, hB⟩
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact false_of_sporData hq sporData_m11 e hA hBA hodd hB
  · exact false_of_sporData hq sporData_m12 e hA hBA hodd hB
  · exact false_of_sporData hq sporData_m22 e hA hBA hodd hB
  · exact false_of_sporData hq sporData_m23 e hA hBA hodd hB
  · exact false_of_sporData hq sporData_m24 e hA hBA hodd hB
  · exact false_of_sporData hq sporData_he e hA hBA hodd hB
  · exact false_of_sporData hq sporData_hs e hA hBA hodd hB
  · exact false_of_sporData hq sporData_j2 e hA hBA hodd hB
  · exact false_of_sporData hq sporData_ru e hA hBA hodd hB

end CFSG.Quasithin.H13.KGSpor726
