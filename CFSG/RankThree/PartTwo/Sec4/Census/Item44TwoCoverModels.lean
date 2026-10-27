module

public import CFSG.GH74.Generic.GKFTables
import CFSG.Models.Transport
import CFSG.Models.PGL
import CFSG.Models.Blueprint
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Assembly.LowTwoRank CFSG.Models Matrix Subgroup
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp projOmegaPlus projOmegaMinus)
open CFSG.Adapters.RankTwoModelTransports (statedProjEquivMapMk)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.GH74.Generic (NoTwoCover card_center_dvd_hopfMultiplier card_hopfMultiplier_of_griess)

export CFSG.Adapters.RankTwoModelTransports (statedProjEquivProjImage)

theorem lieModel_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {t : StatedLieTag}
    {n p f : ℕ} (h : LieModel Y t n p f) : LieModel X t n p f :=
  CFSG.Models.LieModel.of_mulEquiv e.symm h

theorem lieModel_projSL {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSL n p e) :
    LieModel (projSL n (GaloisField p e)) .PSL n p e :=
  CFSG.PGLModel.lieModel_projSL h

theorem lieModel_projSU {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSU n p e) :
    LieModel (projSU n p e) .PSU n p e :=
  CFSG.PGLModel.lieModel_projSU h

theorem lieModel_projSp {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSp n p e) :
    LieModel (projSp n (GaloisField p e)) .PSp n p e :=
  CFSG.PGLModel.lieModel_projSp h

theorem lieModel_projOmegaPlus {n p e : ℕ} [Fact p.Prime]
    (h : StatedLieAdmissible .POmegaPlus n p e) :
    LieModel (projOmegaPlus n (GaloisField p e)) .POmegaPlus n p e :=
  CFSG.PGLModel.lieModel_projOmegaPlus h

theorem lieModel_projOmegaMinus {n p e : ℕ} [Fact p.Prime]
    (h : StatedLieAdmissible .POmegaMinus n p e) {b c : GaloisField p e}
    (hbc : ∀ s : GaloisField p e, s ^ 2 + b * s + c ≠ 0) :
    LieModel (projOmegaMinus (n - 1) (GaloisField p e) b c) .POmegaMinus n p e :=
  CFSG.PGLModel.lieModel_projOmegaMinus h hbc

theorem lieModel_lie {t : StatedLieTag} {p f : ℕ} (h : StatedLieAdmissible t 0 p f)
    (d : TauCeti.ValidLieTypeIndex) (hd : NamesTag d.1 t p f) :
    LieModel (TauCeti.CFSGIndex.lie d).Group t 0 p f :=
  ⟨h, Or.inr ⟨rfl, d, hd, ⟨MulEquiv.refl _⟩⟩⟩

theorem blueprint_lieModel_of_classical {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ CFSG.Blueprint.classicalTags) (h : LieModel X t n p f) :
    CFSG.Blueprint.LieModel X t n p f :=
  CFSG.Models.LieModel.toBlueprint ht h

@[expose] def IsTwoCover (J : Type) [Group J] [Finite J] (S : Type) [Group S] : Prop :=
  IsQuasisimple J ∧ IsPGroup 2 (center J) ∧ Nontrivial (center J) ∧
    Nonempty (J ⧸ center J ≃* S)

theorem two_dvd_card_center {J : Type} [Group J] [Finite J] (hZ2 : IsPGroup 2 (center J))
    (hZnt : Nontrivial (center J)) : 2 ∣ Nat.card (center J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact absurd hk (Finite.one_lt_card).ne'
  · rw [hk, pow_succ]
    exact dvd_mul_left 2 _

theorem card_center_eq_two_of_dvd {J : Type} [Group J] [Finite J]
    (hZnt : Nontrivial (center J)) (h : Nat.card (center J) ∣ 2) : Nat.card (center J) = 2 :=
  ((Nat.dvd_prime Nat.prime_two).mp h).resolve_left (Finite.one_lt_card).ne'

theorem not_isTwoCover_of_noTwoCover {J X : Type} [Group J] [Finite J] [Group X]
    (hX : NoTwoCover X) : ¬ IsTwoCover J X := by
  rintro ⟨hq, hZ2, hZnt, he⟩
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hZnt (hX J hq hZ2 he)

@[expose] def tableOrder (t : StatedLieTag) (n p f : ℕ) : ℕ :=
  (genericOrders t n p f).1 * (genericOrders t n p f).2 *
    ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2)

theorem card_center_dvd_tableOrder (hGA : GriessMultipliersAllModels) {J X : Type} [Group J]
    [Finite J] [Group X] (hq : IsQuasisimple J) (e : J ⧸ center J ≃* X) {t : StatedLieTag}
    {n p f : ℕ} (hm : LieModel X t n p f) : Nat.card (center J) ∣ tableOrder t n p f := by
  rw [tableOrder, ← card_hopfMultiplier_of_griess hGA hm]
  exact card_center_dvd_hopfMultiplier hq e

theorem not_isTwoCover_of_odd_tableOrder (hGA : GriessMultipliersAllModels) {J X : Type}
    [Group J] [Finite J] [Group X] {t : StatedLieTag} {n p f : ℕ} (hm : LieModel X t n p f)
    (hodd : Odd (tableOrder t n p f)) : ¬ IsTwoCover J X := by
  rintro ⟨hq, hZ2, hZnt, ⟨e⟩⟩
  exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat (card_center_dvd_tableOrder hGA hq e hm)))
    (even_iff_two_dvd.mpr (two_dvd_card_center hZ2 hZnt))

theorem card_center_eq_two_of_tableOrder (hGA : GriessMultipliersAllModels) {J X : Type}
    [Group J] [Finite J] [Group X] (hq : IsQuasisimple J) (hZnt : Nontrivial (center J))
    (e : J ⧸ center J ≃* X) {t : StatedLieTag} {n p f : ℕ} (hm : LieModel X t n p f)
    (h2 : tableOrder t n p f = 2) : Nat.card (center J) = 2 :=
  card_center_eq_two_of_dvd hZnt (h2 ▸ card_center_dvd_tableOrder hGA hq e hm)

theorem odd_tableOrder {t : StatedLieTag} {n p f : ℕ} (h1 : Odd (genericOrders t n p f).1)
    (h2 : Odd (genericOrders t n p f).2) (he : exceptionalOrders t n p f = (1, 1)) :
    Odd (tableOrder t n p f) := by
  rw [tableOrder, he]
  exact (h1.mul h2).mul (odd_one.mul odd_one)

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨2 ^ k - 1, ?_⟩
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [pow_succ]
  omega

theorem odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) :=
  (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one

theorem odd_gcd_of_odd_right {m k : ℕ} (hk : Odd k) : Odd (Nat.gcd m k) :=
  hk.of_dvd_nat (Nat.gcd_dvd_right m k)

end CFSG.RankThree.PartTwo.Sec4.Census
