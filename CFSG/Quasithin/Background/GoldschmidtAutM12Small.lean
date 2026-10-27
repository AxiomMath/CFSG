module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Fam
public import CFSG.Quasithin.Background.GoldschmidtAutM12DataM22
public import CFSG.Quasithin.Background.GoldschmidtAutM12DataM23
public import CFSG.Quasithin.Background.GoldschmidtAutM12DataJ2
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.GH74.KGroups.Sz8

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

namespace AutM12Recog

theorem excl_m11
    {S : Type} [Group S] [Finite S]
    (e : S ≃* ↥NativeSporadic.M11) : Excl S := by
  have : Finite ↥NativeSporadic.M11 := Finite.of_equiv S e.toEquiv
  refine Excl.of_mulEquiv e ?_
  refine excl_of_outer_le (a := 4) (c := 2)
    ⟨495, by decide, by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num⟩ (by norm_num)
    (by norm_num) ?_
  exact CFSG.Sporadic.Schreier.at_m11_schreier.1

theorem excl_j1
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.J1) : Excl S := by
  have : Finite NativeSporadic.J1 := Finite.of_equiv S e.toEquiv
  refine Excl.of_mulEquiv e ?_
  refine excl_of_outer_le (a := 3) (c := 1)
    ⟨21945, by decide, by rw [CFSG.Sporadic.J1.card_J1]; norm_num⟩ (by norm_num) (by norm_num) ?_
  exact CFSG.Sporadic.Schreier.at_j1_schreier.1.le

theorem excl_suzuki_eight
    {S : Type} [Group S] [Finite S] (h : SuzukiModel S 2 3) : Excl S := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.Sz8.equiv_of_lieModel (K := S)
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))
  have hcard : Nat.card S = 2 ^ 6 * 455 := by
    rw [Nat.card_congr e.toEquiv, CFSG.GH74.KGroups.card_group CFSG.GH74.KGroups.Sz8.QP
      CFSG.GH74.KGroups.Sz8.QP_ok, (CFSG.GH74.KGroups.Sz8.QP_valid).2]
    norm_num
  have haut : Nat.card (MulAut S) = 87360 := CFSG.GH74.KGroups.Sz8.card_mulAut e
  refine excl_of_aut_le (a := 6) (c := 1) ⟨455, by decide, hcard⟩ (by norm_num) (by norm_num) ?_
  intro n hn
  rw [haut, hcard] at hn
  have h3 : 2 ^ n ∣ 3 := by
    have : 2 ^ 6 * 455 * 2 ^ n ∣ 2 ^ 6 * 455 * 3 := by simpa using hn
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hle : 2 ^ n ≤ 3 := Nat.le_of_dvd (by norm_num) h3
  have hn1 : n ≤ 1 := by
    by_contra hlt
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · norm_num
  · norm_num at h3

theorem excl_m22 {S : Type} [Group S] [Finite S] (e : S ≃* ↥NativeSporadic.M22) : Excl S :=
  excl_of_hasTwoE16 fun Q => Tab.hasTwoE16_of_mulEquiv Tab.M22Cert.hasTwoE16_m22 Q e

theorem excl_m23 {S : Type} [Group S] [Finite S] (e : S ≃* ↥NativeSporadic.M23) : Excl S :=
  excl_of_hasTwoE16 fun Q => Tab.hasTwoE16_of_mulEquiv Tab.M23Cert.hasTwoE16_m23 Q e

theorem excl_j2 {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.J2) : Excl S :=
  excl_of_hasTwoE16 fun Q => Tab.hasTwoE16_of_mulEquiv Tab.J2Cert.hasTwoE16_j2 Q e

end AutM12Recog

end CFSG.Quasithin.F6
