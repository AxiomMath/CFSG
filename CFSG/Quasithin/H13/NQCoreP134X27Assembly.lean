module

public import CFSG.Quasithin.H13.NQCoreP134X27Small
public import CFSG.Quasithin.H13.NQCoreP134X27L3
public import CFSG.Quasithin.H13.NQCoreP134X27U3
public import CFSG.Quasithin.H13.NQCoreP134X27Sp4
public import CFSG.Quasithin.H13.NQCoreP134X27G2
public import CFSG.Quasithin.H13.NQCoreP134X27D4
public import CFSG.Quasithin.H13.NQCoreP134X27F4
public import CFSG.Quasithin.H13.NQCoreP134X27Tits
public import CFSG.Quasithin.H13.KGFactX27Spor
public import CFSG.Quasithin.H13.NQCoreP134OutThreeHolds
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddAbel
public import CFSG.Quasithin.Background.F6CatInstances
public import CFSG.Quasithin.Vol2.F134Cyclic

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def X27Psl3Three : Prop :=
  NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 3 1

@[expose] def X27Psl3Plus : Prop :=
  ∀ r : ℕ, r.Prime → r % 3 = 1 →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 r 1

@[expose] def X27Psu3Minus : Prop :=
  ∀ r : ℕ, r.Prime → r ≠ 2 → r % 3 = 2 →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 r 1

theorem facts134X27_psl3Odd_of (hL33 : X27Psl3Three) (hplus : X27Psl3Plus) :
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 r 1 := by
  intro r hr hr2
  have h3 : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases h3 with h0 | h1 | h2
  · obtain rfl : r = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 (Nat.dvd_of_mod_eq_zero h0)).symm
    exact hL33
  · exact hplus r hr h1
  · exact noX27ConfigQ_of_noE9Cfg (isoInvariant_stated _ _ _ _)
      (noX27Simple_of_noElemNine fun _ _ h => F134.noElemNine_of_statedPSL_three h2 h)
      (noE9Cfg_of_noElemNine fun _ _ h => F134.noElemNine_of_statedPSL_three h2 h)

theorem facts134X27_psu3Odd_of
    (hminus : X27Psu3Minus) :
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 r 1 := by
  intro r hr hr2
  have h3 : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases h3 with h0 | h1 | h2
  · obtain rfl : r = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 (Nat.dvd_of_mod_eq_zero h0)).symm
    exact KGX27.noX27ConfigQ_psu3_three
  · exact noX27ConfigQ_of_noE9Cfg (isoInvariant_stated _ _ _ _)
      (noX27Simple_of_noElemNine fun _ _ h => F134.noElemNine_of_statedPSU_three h1 h)
      (noE9Cfg_of_noElemNine fun _ _ h => F134.noElemNine_of_statedPSU_three h1 h)
  · exact hminus r hr hr2 h2

theorem facts134X27_of
    (hL33 : X27Psl3Three) (hplus : X27Psl3Plus)
    (hminus : X27Psu3Minus) : Facts134X27 where
  alt := facts134X27_alt KGX27.noX27ConfigQ_alt6
  psl2Odd := facts134X27_psl2Odd KGX27.noX27ConfigQ_alt6
  psl3Odd := facts134X27_psl3Odd_of hL33 hplus
  psu3Odd := facts134X27_psu3Odd_of hminus
  psl2Even := facts134X27_psl2Even
  psl3Even := X27L3.facts134X27_psl3Even
  psu3Even := X27U3.facts134X27_psu3Even
  psp4Even := facts134X27_psp4Even
  g2Even := X27G2.facts134X27_g2Even
  d4Even := X27D4.facts134X27_d4Even
  f4Even := X27F4.facts134X27_f4Even
  sz := facts134X27_sz
  tits := X27Tits.facts134X27_tits
  psl45 := facts134X27_psl45
  m11 := KGX27.noX27ConfigQ_m11
  m12 := KGX27.noX27ConfigQ_m12
  m22 := KGX27.noX27ConfigQ_m22
  m23 := KGX27.noX27ConfigQ_m23
  m24 := KGX27.noX27ConfigQ_m24
  j1 := KGX27.noX27ConfigQ_j1
  j2 := KGX27.noX27ConfigQ_j2
  j4 := KGX27.noX27ConfigQ_j4
  hs := KGX27.noX27ConfigQ_hs
  he := KGX27.noX27ConfigQ_he
  ru := KGX27.noX27ConfigQ_ru

theorem prop134ThreeExtraspecial_of_three
    (hL33 : X27Psl3Three) (hplus : X27Psl3Plus) (hminus : X27Psu3Minus) :
    Prop134ThreeExtraspecial :=
  prop134ThreeExtraspecial_of_facts Vol2Native.a36CoreForSQTKCat_proved
    Vol2Native.a37ForSQTKCat_proved Vol2.Ch10.SecA.a38ForSQTKCat_proved outThreeFact_holds
    facts134Odd_outAbelian F6.nativeTheoremCSection (facts134X27_of hL33 hplus hminus)

end CFSG.Quasithin.H13.NQCore
