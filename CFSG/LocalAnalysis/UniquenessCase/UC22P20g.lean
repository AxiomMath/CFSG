module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Timmesfeld.Orders.Distinct
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.Adapters.LieModelOrders
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Blueprint.LieModelAPI
import CFSG.Assembly.Subnormal
import CFSG.Quasithin.Background.A3ComponentsQuotient
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LieType.Simplicity.Exceptional
import CFSG.LieType.Simplicity.TrialityD4
import CFSG.LieType.Simplicity.ReeLargeModel
import CFSG.RankThree.PartOne.S12K.Rigidity
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LocalAnalysis.UniquenessCase.UC22S22b
import CFSG.LocalAnalysis.UniquenessCase.UC6R2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.EvenSmallLie.CatalogOrders (lieOrd)

@[expose] def UC22P20gSmallOrder (m : ℕ) : Prop :=
  m = 60 ∨ m = 168 ∨ m = 20160 ∨ m = 62400 ∨ m = 979200

theorem uc22p20g_three_dvd_of_smallOrder {m : ℕ} (h : UC22P20gSmallOrder m) : 3 ∣ m := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem uc22p20g_two_part {m N : ℕ} {Z : ℕ → Prop} (hP : CFSG.Timmesfeld.Orders.Profile m N Z)
    (hm : UC22P20gSmallOrder m) : N = 2 ∨ N = 3 ∨ N = 6 ∨ N = 8 := by
  obtain ⟨r, hr, hmr⟩ := hP.two
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr (by decide : Odd 15)
      (hmr.symm.trans (by norm_num)))
  · exact Or.inr (Or.inl (CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr (by decide : Odd 21)
      (hmr.symm.trans (by norm_num))))
  · exact Or.inr (Or.inr (Or.inl (CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr
      (by decide : Odd 315) (hmr.symm.trans (by norm_num)))))
  · exact Or.inr (Or.inr (Or.inl (CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr
      (by decide : Odd 975) (hmr.symm.trans (by norm_num)))))
  · exact Or.inr (Or.inr (Or.inr (CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr
      (by decide : Odd 3825) (hmr.symm.trans (by norm_num)))))

theorem uc22p20g_big_not_small {m N : ℕ} {Z : ℕ → Prop}
    (hP : CFSG.Timmesfeld.Orders.Profile m N Z) (hN : 9 ≤ N) (hm : UC22P20gSmallOrder m) :
    False := by
  rcases uc22p20g_two_part hP hm with h | h | h | h <;> omega

theorem uc22p20g_ordA_one_not_small {n : ℕ} (hn : 3 ≤ n)
    (hm : UC22P20gSmallOrder (ordA 1 (2 ^ n))) : False := by
  have hP := CFSG.Timmesfeld.Orders.profile_ordA (n := 1) (f := n) le_rfl (by omega)
  have hN : n * (1 * (1 + 1) / 2) = n := by norm_num
  rw [hN] at hP
  rcases uc22p20g_two_part hP hm with h | h | h | h
  · omega
  · subst h; revert hm; unfold UC22P20gSmallOrder; decide
  · subst h; revert hm; unfold UC22P20gSmallOrder; decide
  · subst h; revert hm; unfold UC22P20gSmallOrder; decide

section Helpers

variable {X : Type} [Group X]

theorem uc22p20g_nonab_of_quasisimple (hq : CFSG.Open.IsQuasisimple X) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, y, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem uc22p20g_center_bot_of_simple (hq : CFSG.Open.IsQuasisimple X) (hs : IsSimpleGroup X) :
    Subgroup.center X = ⊥ := by
  haveI := hs
  exact uc22p22a_center_eq_bot (uc22p20g_nonab_of_quasisimple hq)

theorem uc22p20g_card_quot_center_of_eq_bot (h : Subgroup.center X = ⊥) :
    Nat.card (X ⧸ Subgroup.center X) = Nat.card X :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).toEquiv

theorem uc22p20g_normal_of_commuting {N₁ N₂ : Subgroup X} (hsup : N₁ ⊔ N₂ = ⊤)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) : N₁.Normal := by
  have h3 : N₁ ⊔ N₂ ≤ Subgroup.normalizer (N₁ : Set X) := by
    refine sup_le Subgroup.le_normalizer (Subgroup.le_normalizer_iff.2 fun b hb k hk => ?_)
    have : b * k * b⁻¹ = k := by rw [← hcomm k hk b hb]; group
    rw [this]
    exact hk
  rw [hsup] at h3
  exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 h3)

theorem uc22p20g_qs_simple (hnab : ∃ a b : X, a * b ≠ b * a) (hs : IsSimpleGroup X) {c N : ℕ}
    {Z : ℕ → Prop} (hc : Nat.card X = c) (hP : CFSG.Timmesfeld.Orders.Profile c N Z) (hN : 9 ≤ N) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) := by
  haveI := hs
  refine ⟨uc22p22a_isQuasisimple_of_simple hnab, fun hm => ?_⟩
  rw [uc22p20g_card_quot_center_of_eq_bot (uc22p22a_center_eq_bot hnab), hc] at hm
  exact uc22p20g_big_not_small hP hN hm

theorem uc22p20g_qs_classical (hnab : ∃ a b : X, a * b ≠ b * a) {t : StatedLieTag} {m n : ℕ}
    (ht : t ∈ CFSG.Blueprint.classicalTags) (hm0 : m ≠ 0) (h : LieModel X t m 2 n) {c N : ℕ}
    {Z : ℕ → Prop} (hc : lieOrd t m (2 ^ n) = c)
    (hP : CFSG.Timmesfeld.Orders.Profile c N Z) (hN : 9 ≤ N) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_simple hnab (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags ht h)
    ((h.card_eq_lieOrd hm0).trans hc) hP hN

theorem uc22p20g_qs_cover (hq : CFSG.Open.IsQuasisimple X) {t : StatedLieTag} {m n : ℕ} (hm0 : m ≠ 0)
    (h : LieModel (X ⧸ Subgroup.center X) t m 2 n) {c N : ℕ} {Z : ℕ → Prop}
    (hc : lieOrd t m (2 ^ n) = c) (hP : CFSG.Timmesfeld.Orders.Profile c N Z) (hN : 9 ≤ N) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) := by
  refine ⟨hq, fun hm => ?_⟩
  rw [(h.card_eq_lieOrd hm0).trans hc] at hm
  exact uc22p20g_big_not_small hP hN hm

end Helpers

@[expose] def UC22P20gShape (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 2 < n ∧ (IsSz X n ∨ IsL2 X n ∨ IsL3 X n ∨ IsU3 X n ∨
      LieModel X .PSL 4 2 n ∨ IsU4 X n ∨ IsG2 X n ∨ Is3D4 X n ∨
      LieModel X .twistedF4 0 2 n ∨ IsSp4 X n ∨ IsSL3 X n ∨
      IsSU3 X n ∨ LieModel X .PSp 3 2 n ∨ IsOmega8m X n)) ∨
    IsU4 X 2 ∨ IsU5 X 2 ∨ IsOmega8m X 2 ∨ Is3D4 X 2 ∨
    Is3D4 X 1 ∨
    (∃ n : ℕ, 2 < n ∧ IsSzL2Product X n) ∨
    IsSU3CentralSquare X

@[expose] def UC22P20gExcG2 : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), IsG2 X n → IsSimpleGroup X ∧ Nat.card X = ordG2 (2 ^ n)

@[expose] def UC22P20gExc3D4 : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), Is3D4 X n →
    IsSimpleGroup X ∧ Nat.card X = ordTrialityD4 (2 ^ n)

@[expose] def UC22P20gExc2F4 : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), LieModel X .twistedF4 0 2 n →
    IsSimpleGroup X ∧ Nat.card X = ordTwistedF4 (2 ^ n)

@[expose] def UC22P20gExcFacts : Prop :=
  UC22P20gExcG2 ∧ UC22P20gExc3D4 ∧ UC22P20gExc2F4

section ShapeCases

variable {X : Type} [Group X]

theorem uc22p20g_qs_Sz (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (h : IsSz X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) := by
  have hs := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h
  haveI := hs
  refine ⟨uc22p22a_isQuasisimple_of_simple hnab, fun hm => ?_⟩
  exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 h
    ((uc22p20g_three_dvd_of_smallOrder hm).trans (Subgroup.card_quotient_dvd_card _))

theorem uc22p20g_qs_L2 (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 2 < n) (h : IsL2 X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) := by
  have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) h
  haveI := hs
  refine ⟨uc22p22a_isQuasisimple_of_simple hnab, fun hm => ?_⟩
  rw [uc22p20g_card_quot_center_of_eq_bot (uc22p22a_center_eq_bot hnab),
    h.card_eq_lieOrd (by norm_num)] at hm
  exact uc22p20g_ordA_one_not_small hn hm

theorem uc22p20g_qs_L3 (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 2 < n) (h : IsL3 X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_classical hnab (t := .PSL) (by decide) (by norm_num) h (c := ordA 2 (2 ^ n)) rfl
    (CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (f := n) (by norm_num) (by omega))
    (by norm_num <;> omega)

theorem uc22p20g_qs_U3 (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 2 < n) (h : IsU3 X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_classical hnab (t := .PSU) (by decide) (by norm_num) h
    (c := ordTwistedA 2 (2 ^ n)) rfl
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := n) (by norm_num) (by omega))
    (by norm_num <;> omega)

theorem uc22p20g_qs_L4 (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 2 < n)
    (h : LieModel X .PSL 4 2 n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_classical hnab (t := .PSL) (by decide) (by norm_num) h (c := ordA 3 (2 ^ n)) rfl
    (CFSG.Timmesfeld.Orders.profile_ordA (n := 3) (f := n) (by norm_num) (by omega))
    (by norm_num <;> omega)

theorem uc22p20g_qs_U4 (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 2 ≤ n) (h : IsU4 X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_classical hnab (t := .PSU) (by decide) (by norm_num) h
    (c := ordTwistedA 3 (2 ^ n)) rfl
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 3) (g := n) (by norm_num) (by omega))
    (by norm_num <;> omega)

theorem uc22p20g_qs_U5 (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 2 ≤ n) (h : IsU5 X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_classical hnab (t := .PSU) (by decide) (by norm_num) h
    (c := ordTwistedA 4 (2 ^ n)) rfl
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 4) (g := n) (by norm_num) (by omega))
    (by norm_num <;> omega)

theorem uc22p20g_qs_Sp4 (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 2 < n) (h : IsSp4 X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_classical hnab (t := .PSp) (by decide) (by norm_num) h (c := ordBC 2 (2 ^ n)) rfl
    (CFSG.Timmesfeld.Orders.profile_ordBC (n := 2) (f := n) (by omega))
    (by norm_num <;> omega)

theorem uc22p20g_qs_Sp6 (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 2 < n)
    (h : LieModel X .PSp 3 2 n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_classical hnab (t := .PSp) (by decide) (by norm_num) h (c := ordBC 3 (2 ^ n)) rfl
    (CFSG.Timmesfeld.Orders.profile_ordBC (n := 3) (f := n) (by omega))
    (by norm_num <;> omega)

theorem uc22p20g_qs_Om8m (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 1 ≤ n)
    (h : IsOmega8m X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_classical hnab (t := .POmegaMinus) (by decide) (by norm_num) h
    (c := ordTwistedD 4 (2 ^ n)) rfl
    (CFSG.Timmesfeld.Orders.profile_ordTwistedD (n := 4) (f := n) (by norm_num) (by omega))
    (by norm_num <;> omega)

theorem uc22p20g_qs_SL3 {n : ℕ} (hn : 2 < n) (h : IsSL3 X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_cover h.1 (t := .PSL) (m := 3) (by norm_num) h.2 (c := ordA 2 (2 ^ n)) rfl
    (CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (f := n) (by norm_num) (by omega))
    (by norm_num <;> omega)

theorem uc22p20g_qs_SU3 {n : ℕ} (hn : 2 < n) (h : IsSU3 X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_cover h.1 (t := .PSU) (m := 3) (by norm_num) h.2 (c := ordTwistedA 2 (2 ^ n)) rfl
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) (g := n) (by norm_num) (by omega))
    (by norm_num <;> omega)

theorem uc22p20g_qs_G2 (hE : UC22P20gExcFacts) (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ}
    (hn : 2 ≤ n) (h : IsG2 X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_simple hnab (hE.1 X n h).1 (hE.1 X n h).2
    (CFSG.Timmesfeld.Orders.profile_ordG2 (f := n) (by omega)) (by omega)

theorem uc22p20g_qs_3D4 (hE : UC22P20gExcFacts) (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ}
    (hn : 1 ≤ n) (h : Is3D4 X n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_simple hnab (hE.2.1 X n h).1 (hE.2.1 X n h).2
    (CFSG.Timmesfeld.Orders.profile_ordTrialityD4 (f := n) (by omega)) (by omega)

theorem uc22p20g_qs_2F4 (hE : UC22P20gExcFacts) (hnab : ∃ a b : X, a * b ≠ b * a) {n : ℕ}
    (hn : 1 ≤ n) (h : LieModel X .twistedF4 0 2 n) :
    CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) :=
  uc22p20g_qs_simple hnab (hE.2.2 X n h).1 (hE.2.2 X n h).2
    (CFSG.Timmesfeld.Orders.profile_ordTwistedF4 (f := n) (by omega)) (by omega)

theorem uc22p20g_simple_nonab_SzL2 {A : Type} [Group A] {n : ℕ} (hn : 2 < n)
    (hA : IsSz A n ∨ IsL2 A n) : IsSimpleGroup A ∧ ∃ a b : A, a * b ≠ b * a := by
  rcases hA with hA | hA
  · exact ⟨CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hA,
      CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hA⟩
  · have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL)
      (by decide) hA
    refine ⟨hs, ?_⟩
    by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative A := ⟨⟨fun a b => hcon a b⟩⟩
    have hprime := (Group.is_simple_iff_prime_card (α := A)).1 hs
    have hP := CFSG.Timmesfeld.Orders.profile_ordA (n := 1) (f := n) le_rfl (by omega)
    have hN : n * (1 * (1 + 1) / 2) = n := by norm_num
    rw [hN] at hP
    obtain ⟨r, -, hr⟩ := hP.two
    have hcard : Nat.card A = ordA 1 (2 ^ n) := hA.card_eq_lieOrd (by norm_num)
    have h8 : 2 ^ 3 ∣ Nat.card A := by
      rw [hcard, hr]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) r
    have h2 : 2 ∣ Nat.card A := dvd_trans (by norm_num) h8
    have h2' : Nat.card A = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hprime).1 h2).symm
    rw [h2'] at h8
    exact absurd h8 (by decide)

theorem uc22p20g_card_ne_sixty {A : Type} [Group A] {n : ℕ} (hn : 2 < n)
    (hA : IsSz A n ∨ IsL2 A n) : Nat.card A ≠ 60 := by
  intro h60
  rcases hA with hA | hA
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hA
      (h60 ▸ (by decide : 3 ∣ 60))
  · have h' : ordA 1 (2 ^ n) = 60 := (hA.card_eq_lieOrd (by norm_num)).symm.trans h60
    exact uc22p20g_ordA_one_not_small (by omega) (Or.inl h')

end ShapeCases

@[expose] def UC22P20gProd (X : Type) [Group X] : Prop :=
  ∃ N₁ N₂ : Subgroup X, N₁ ⊔ N₂ = ⊤ ∧ (∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) ∧
    CFSG.Open.IsQuasisimple ↥N₁ ∧ CFSG.Open.IsQuasisimple ↥N₂ ∧
    Nat.card ↥N₁ ≠ 60 ∧ Nat.card ↥N₂ ≠ 60

section ProdShapes

variable {X : Type} [Group X]

theorem uc22p20g_prod_of_szL2Product {n : ℕ} (hn : 2 < n) (h : IsSzL2Product X n) :
    UC22P20gProd X := by
  obtain ⟨A, B, _, _, ⟨e⟩, hA, hB⟩ := h
  have hAs := uc22p20g_simple_nonab_SzL2 hn hA
  have hBs := uc22p20g_simple_nonab_SzL2 hn hB
  haveI := hAs.1
  haveI := hBs.1
  have hAq : CFSG.Open.IsQuasisimple A := uc22p22a_isQuasisimple_of_simple hAs.2
  have hBq : CFSG.Open.IsQuasisimple B := uc22p22a_isQuasisimple_of_simple hBs.2
  let f₁ : A →* X := e.symm.toMonoidHom.comp (MonoidHom.inl A B)
  let f₂ : B →* X := e.symm.toMonoidHom.comp (MonoidHom.inr A B)
  have hf₁ : Function.Injective f₁ :=
    e.symm.injective.comp (fun a a' h => by simpa using congrArg Prod.fst h)
  have hf₂ : Function.Injective f₂ :=
    e.symm.injective.comp (fun b b' h => by simpa using congrArg Prod.snd h)
  have hx : ∀ x : X, x = f₁ (e x).1 * f₂ (e x).2 := by
    intro x
    simp only [f₁, f₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
      MulEquiv.coe_toMonoidHom]
    rw [← map_mul]
    simp
  refine ⟨f₁.range, f₂.range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    rw [hx x]
    exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [f₁, f₂, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
      MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul]
    simp
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hf₁).symm hAq
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hf₂).symm hBq
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf₁).toEquiv]
    exact uc22p20g_card_ne_sixty hn hA
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf₂).toEquiv]
    exact uc22p20g_card_ne_sixty hn hB

theorem uc22p20g_prod_of_square (h : IsSU3CentralSquare X) : UC22P20gProd X := by
  obtain ⟨K₁, K₂, hsup, hcomm, hK₁, hK₂, -⟩ := h
  have hcard : ∀ K : Subgroup X, IsSU3 ↥K 3 → Nat.card ↥K ≠ 60 := by
    intro K hK h60
    have h5 : Nat.card (↥K ⧸ Subgroup.center ↥K) = lieOrd .PSU 3 (2 ^ 3) :=
      hK.2.card_eq_lieOrd (by norm_num)
    have hd := Subgroup.card_quotient_dvd_card (Subgroup.center ↥K)
    rw [h5, h60] at hd
    revert hd
    decide
  exact ⟨K₁, K₂, hsup, hcomm, hK₁.1, hK₂.1, hcard K₁ hK₁, hcard K₂ hK₂⟩

theorem uc22p20g_shape_cases (hE : UC22P20gExcFacts) (hs : UC22P20gShape X)
    (hnab : ∃ a b : X, a * b ≠ b * a) :
    (CFSG.Open.IsQuasisimple X ∧ ¬ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X))) ∨
      UC22P20gProd X := by
  rcases hs with ⟨n, hn, h | h | h | h | h | h | h | h | h | h | h | h | h | h⟩ | h | h | h | h | h |
      ⟨n, hn, h⟩ | h
  · exact Or.inl (uc22p20g_qs_Sz hnab h)
  · exact Or.inl (uc22p20g_qs_L2 hnab hn h)
  · exact Or.inl (uc22p20g_qs_L3 hnab hn h)
  · exact Or.inl (uc22p20g_qs_U3 hnab hn h)
  · exact Or.inl (uc22p20g_qs_L4 hnab hn h)
  · exact Or.inl (uc22p20g_qs_U4 hnab (by omega) h)
  · exact Or.inl (uc22p20g_qs_G2 hE hnab (by omega) h)
  · exact Or.inl (uc22p20g_qs_3D4 hE hnab (by omega) h)
  · exact Or.inl (uc22p20g_qs_2F4 hE hnab (by omega) h)
  · exact Or.inl (uc22p20g_qs_Sp4 hnab hn h)
  · exact Or.inl (uc22p20g_qs_SL3 hn h)
  · exact Or.inl (uc22p20g_qs_SU3 hn h)
  · exact Or.inl (uc22p20g_qs_Sp6 hnab hn h)
  · exact Or.inl (uc22p20g_qs_Om8m hnab (by omega) h)
  · exact Or.inl (uc22p20g_qs_U4 hnab le_rfl h)
  · exact Or.inl (uc22p20g_qs_U5 hnab le_rfl h)
  · exact Or.inl (uc22p20g_qs_Om8m hnab (by norm_num) h)
  · exact Or.inl (uc22p20g_qs_3D4 hE hnab (by norm_num) h)
  · exact Or.inl (uc22p20g_qs_3D4 hE hnab (by norm_num) h)
  · exact Or.inr (uc22p20g_prod_of_szL2Product hn h)
  · exact Or.inr (uc22p20g_prod_of_square h)

theorem uc22p20g_nonab_of_simple_card [IsSimpleGroup X] (h : ¬ (Nat.card X).Prime) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative X := ⟨⟨fun a b => hcon a b⟩⟩
  exact h ((Group.is_simple_iff_prime_card (α := X)).1 inferInstance)

theorem uc22p20g_not_quasisimple_of_commuting (hq : CFSG.Open.IsQuasisimple X)
    {N₁ N₂ : Subgroup X} (hsup : N₁ ⊔ N₂ = ⊤) (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (h₁ : ∃ a ∈ N₁, ∃ b ∈ N₁, a * b ≠ b * a) (h₂ : ∃ a ∈ N₂, ∃ b ∈ N₂, a * b ≠ b * a) :
    False := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
  have hN₁ : N₁.Normal := uc22p20g_normal_of_commuting hsup hcomm
  rcases (hN₁.map (QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _)).eq_bot_or_eq_top with hbot | htop
  · obtain ⟨a, ha, b, hb, hab⟩ := h₁
    have hmem : QuotientGroup.mk' (Subgroup.center X) a ∈
        N₁.map (QuotientGroup.mk' (Subgroup.center X)) := ⟨a, ha, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply] at hmem
    have hac : a ∈ Subgroup.center X := (QuotientGroup.eq_one_iff a).1 hmem
    exact hab (Subgroup.mem_center_iff.1 hac b).symm
  · obtain ⟨c, hc, d, hd, hcd⟩ := h₂
    have hmem : QuotientGroup.mk' (Subgroup.center X) c ∈
        N₁.map (QuotientGroup.mk' (Subgroup.center X)) := by rw [htop]; trivial
    obtain ⟨a, ha, hac⟩ := hmem
    have hz : a⁻¹ * c ∈ Subgroup.center X := QuotientGroup.eq.1 hac
    have hcz : c = a * (a⁻¹ * c) := by group
    apply hcd
    have h1 := hcomm a ha d hd
    have h2 : (a⁻¹ * c) * d = d * (a⁻¹ * c) := (Subgroup.mem_center_iff.1 hz d).symm
    rw [hcz]
    calc a * (a⁻¹ * c) * d = a * ((a⁻¹ * c) * d) := mul_assoc _ _ _
      _ = a * (d * (a⁻¹ * c)) := by rw [h2]
      _ = (a * d) * (a⁻¹ * c) := (mul_assoc _ _ _).symm
      _ = (d * a) * (a⁻¹ * c) := by rw [h1]
      _ = d * (a * (a⁻¹ * c)) := mul_assoc _ _ _

end ProdShapes

@[expose] def UC22P20gSmall (X : Type) [Group X] : Prop :=
  IsL2 X 2 ∨ IsSU3 X 2 ∨ IsSL3 X 1 ∨ IsSL3 X 2 ∨ IsSp4 X 2

section Small

variable {X : Type} [Group X]

theorem uc22p20g_small_facts (h : UC22P20gSmall X) :
    CFSG.Open.IsQuasisimple X ∧ UC22P20gSmallOrder (Nat.card (X ⧸ Subgroup.center X)) := by
  rcases h with h | h | h | h | h
  · have hs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL)
      (by decide) h
    haveI := hs
    have hcard : Nat.card X = 60 := (h.card_eq_lieOrd (by norm_num)).trans (by decide)
    have hnab := uc22p20g_nonab_of_simple_card (X := X) (by rw [hcard]; norm_num)
    refine ⟨uc22p22a_isQuasisimple_of_simple hnab, ?_⟩
    rw [uc22p20g_card_quot_center_of_eq_bot (uc22p22a_center_eq_bot hnab), hcard]
    exact Or.inl rfl
  · refine ⟨h.1, ?_⟩
    rw [h.2.card_eq_lieOrd (by norm_num)]
    unfold UC22P20gSmallOrder
    decide
  · refine ⟨h.1, ?_⟩
    rw [h.2.card_eq_lieOrd (by norm_num)]
    unfold UC22P20gSmallOrder
    decide
  · refine ⟨h.1, ?_⟩
    rw [h.2.card_eq_lieOrd (by norm_num)]
    unfold UC22P20gSmallOrder
    decide
  · obtain ⟨hs, hnab⟩ := uc22p22a_sp4_simple X 2 h
    haveI := hs
    refine ⟨uc22p22a_isQuasisimple_of_simple hnab, ?_⟩
    rw [uc22p20g_card_quot_center_of_eq_bot (uc22p22a_center_eq_bot hnab),
      h.card_eq_lieOrd (by norm_num)]
    unfold UC22P20gSmallOrder
    decide

theorem uc22p20g_small_not_shape (hE : UC22P20gExcFacts) (hsm : UC22P20gSmall X)
    (hs : UC22P20gShape X) : False := by
  obtain ⟨hq, hm⟩ := uc22p20g_small_facts hsm
  rcases uc22p20g_shape_cases hE hs (uc22p20g_nonab_of_quasisimple hq) with ⟨-, hns⟩ |
      ⟨N₁, N₂, hsup, hcomm, h₁, h₂, -, -⟩
  · exact hns hm
  · obtain ⟨a, b, hab⟩ := uc22p20g_nonab_of_quasisimple h₁
    obtain ⟨c, d, hcd⟩ := uc22p20g_nonab_of_quasisimple h₂
    exact uc22p20g_not_quasisimple_of_commuting hq hsup hcomm
      ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
      ⟨c, c.2, d, d.2, fun h => hcd (Subtype.ext h)⟩

end Small

section Components

variable {X : Type} [Group X]

theorem uc22p20g_eq_of_components [Finite X] {P N₁ N₂ : Subgroup X} (hsup : N₁ ⊔ N₂ = ⊤)
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (h₁ : CFSG.Open.IsQuasisimple ↥N₁)
    (h₂ : CFSG.Open.IsQuasisimple ↥N₂) (hP : CFSG.Open.IsQuasisimple ↥P)
    (hsn : CFSG.Open.IsSubnormal P ⊤) : P = N₁ ∨ P = N₂ := by
  have hN₁ : N₁.Normal := uc22p20g_normal_of_commuting hsup hcomm
  have hN₂ : N₂.Normal := uc22p20g_normal_of_commuting (by rw [sup_comm]; exact hsup)
    fun a ha b hb => (hcomm b hb a ha).symm
  have cP : CFSG.IsComponent P := ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hP,
    CFSG.Open.IsSubnormal.top_iff.mp hsn⟩
  have c₁ : CFSG.IsComponent N₁ :=
    ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr h₁, hN₁.isSubnormal⟩
  have c₂ : CFSG.IsComponent N₂ :=
    ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr h₂, hN₂.isSubnormal⟩
  by_contra hne
  push Not at hne
  rcases CFSG.LocalCores.distinct_components_commute cP c₁ with h | h
  · exact hne.1 h
  rcases CFSG.LocalCores.distinct_components_commute cP c₂ with h' | h'
  · exact hne.2 h'
  have hP1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have hP2 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h'
  have hPc : ∀ p ∈ P, p ∈ Subgroup.center X := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({p} : Set X) := by
      have h4 : N₁ ⊔ N₂ ≤ Subgroup.centralizer ({p} : Set X) := by
        refine sup_le (fun n hn => ?_) (fun n hn => ?_)
        · refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact (Subgroup.mem_centralizer_iff.1 (hP1 hp) n hn).symm
        · refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact (Subgroup.mem_centralizer_iff.1 (hP2 hp) n hn).symm
      rw [hsup] at h4
      exact h4 (Subgroup.mem_top g)
    exact (Subgroup.mem_centralizer_iff.1 hg p rfl).symm
  obtain ⟨a, b, hab⟩ := uc22p20g_nonab_of_quasisimple hP
  exact hab (Subtype.ext (Subgroup.mem_center_iff.1 (hPc _ b.2) a))

theorem uc22p20g_a5_not_shape (hE : UC22P20gExcFacts) [Finite X] (hs : UC22P20gShape X)
    {P : Subgroup X} (hsn : CFSG.Open.IsSubnormal P ⊤) (hPs : IsSimpleGroup ↥P)
    (hPc : Nat.card ↥P = 60) : False := by
  haveI := hPs
  have hPnab : ∃ a b : ↥P, a * b ≠ b * a :=
    uc22p20g_nonab_of_simple_card (by rw [hPc]; norm_num)
  have hPq : CFSG.Open.IsQuasisimple ↥P := uc22p22a_isQuasisimple_of_simple hPnab
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hPnab
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  rcases uc22p20g_shape_cases hE hs hnab with ⟨hq, hns⟩ | ⟨N₁, N₂, hsup, hcomm, h₁, h₂, hn₁, hn₂⟩
  · rcases CFSG.Quasithin.A3.eq_top_or_le_center_of_subnormal
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)
      (CFSG.Open.IsSubnormal.top_iff.mp hsn) with htop | hle
    · subst htop
      have hXs : IsSimpleGroup X := Subgroup.topEquiv.symm.isSimpleGroup
      have hX60 : Nat.card X = 60 := by rw [← Subgroup.card_top]; exact hPc
      refine hns ?_
      rw [uc22p20g_card_quot_center_of_eq_bot (uc22p20g_center_bot_of_simple hq hXs), hX60]
      exact Or.inl rfl
    · obtain ⟨a, b, hab⟩ := hPnab
      exact hab (Subtype.ext (Subgroup.mem_center_iff.1 (hle b.2) a))
  · rcases uc22p20g_eq_of_components hsup hcomm h₁ h₂ hPq hsn with rfl | rfl
    · exact hn₁ hPc
    · exact hn₂ hPc

end Components

section Main

theorem uc22p20g_two_le_of_isL2 {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) : 2 ≤ n := by
  obtain ⟨-, h1, -, h22, -⟩ := h.admissible
  by_contra hlt
  have hn1 : n = 1 := by omega
  subst hn1
  exact h22 rfl

theorem uc22p20g_one_le_of_isSL3 {X : Type} [Group X] {n : ℕ} (h : IsSL3 X n) : 1 ≤ n := by
  obtain ⟨-, h1, -⟩ := h.2.admissible
  exact h1

variable {G : Type} [Group G] [Finite G]

theorem uc22p20g_three_le_of_nparam_calL (hE : UC22P20gExcFacts) {D : Data G} (h20_7 : S20_7 D)
    (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M) {n : ℕ} (hn : NParam L n) :
    3 ≤ n := by
  have hshape : UC22P20gShape (Bar2 L) := h20_7 h1930 L hL
  by_contra hlt
  push Not at hlt
  rcases hn with hsingle | ⟨L₁, L₂, hL₁, hL₂, hsup, hne, hall⟩
  · rcases hsingle with hSz | hL2 | hSU3 | hSL3 | hSp4
    · have := CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hSz
      omega
    · have h2 := uc22p20g_two_le_of_isL2 hL2
      obtain rfl : n = 2 := by omega
      exact uc22p20g_small_not_shape hE (Or.inl hL2) hshape
    · have h2 := uc22p22a_two_le_of_isU3 hSU3.2
      obtain rfl : n = 2 := by omega
      exact uc22p20g_small_not_shape hE (Or.inr (Or.inl hSU3)) hshape
    · have h1 := uc22p20g_one_le_of_isSL3 hSL3
      rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl
      · exact uc22p20g_small_not_shape hE (Or.inr (Or.inr (Or.inl hSL3))) hshape
      · exact uc22p20g_small_not_shape hE (Or.inr (Or.inr (Or.inr (Or.inl hSL3)))) hshape
    · have h2 := uc22p22a_two_le_of_isSp4 hSp4
      obtain rfl : n = 2 := by omega
      exact uc22p20g_small_not_shape hE (Or.inr (Or.inr (Or.inr (Or.inr hSp4)))) hshape
  · rcases hall L₁ (by simp) with hSz | hL2 | ⟨h3, -⟩
    · have := CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hSz
      omega
    · have h2 := uc22p20g_two_le_of_isL2 hL2
      obtain rfl : n = 2 := by omega
      have hsubn : CFSG.Open.IsSubnormal L₁ L := hL₁.1
      have hle : L₁ ≤ L := uc22p22a_le_of_isSubnormal hsubn
      obtain ⟨e, -⟩ := uc22p20d_bar2Equiv hle hsubn
      have hPL2 := CFSG.Blueprint.LieModel.of_mulEquiv e hL2
      have hPs := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL)
        (by decide) hPL2
      have hPc : Nat.card ↥((L₁.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) = 60 :=
        (hPL2.card_eq_lieOrd (by norm_num)).trans (by decide)
      have hsn : CFSG.Open.IsSubnormal
          ((L₁.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ⊤ :=
        CFSG.Quasithin.A3.subnormal_top_map (QuotientGroup.mk'_surjective _)
          (CFSG.Open.IsSubnormal.top_iff.mpr hsubn.subgroupOf)
      exact uc22p20g_a5_not_shape hE hshape hsn hPs hPc
    · omega

theorem uc22p20g_three_le_of_nparam (hE : UC22P20gExcFacts) {D : Data G} (h20_7 : S20_7 D)
    (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calLLow D.T D.M) {n : ℕ} (hn : NParam L n) :
    3 ≤ n :=
  uc22p20g_three_le_of_nparam_calL hE h20_7 h1930 hL.1 hn

theorem uc22p20g_hn3_of (hE : UC22P20gExcFacts) (D : Data G) (Ch : Choice2011 G)
    (h20_7 : S20_7 D) : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n :=
  fun h1930 c => uc22p20g_three_le_of_nparam hE h20_7 h1930 c.hL0 c.hn

theorem uc22p20g_hn3_ctx22b_of (hE : UC22P20gExcFacts) (D : Data G) (Ch : Choice2011 G)
    (h20_7 : S20_7 D) : H1930 D → ∀ c : Ctx22b D Ch, 3 ≤ c.n :=
  fun h1930 c => uc22p20g_hn3_of hE D Ch h20_7 h1930 c.toCtx22.toCtx21

end Main

section Exceptional

open CFSG.Blueprint CFSG.EvenSmallLie.CatalogOrders

section G2

theorem uc22p20g_excG2 : UC22P20gExcG2 := by
  intro X _ n h
  have hce : ChevalleyExceptionalModel X .G2 2 n := h.chevalleyExceptionalModel (by decide)
  exact ⟨(CFSG.LieType.Simplicity.fam_g2_simplicity X 2 n hce).2,
    card_eq_lieOrd_of_exceptional hce⟩

end G2

section D4

theorem uc22p20g_exc3D4 : UC22P20gExc3D4 := by
  intro X _ n h
  have hce : ChevalleyExceptionalModel X .trialityD4 2 n := h.chevalleyExceptionalModel (by decide)
  exact ⟨(CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 n hce).2,
    card_eq_lieOrd_of_exceptional hce⟩

end D4

section F4

theorem uc22p20g_exc2F4 : UC22P20gExc2F4 := by
  intro X _ n h
  have hre : ReeTitsModel X .twistedF4 2 n := (h.reeTitsModel (by decide)).2
  exact ⟨(CFSG.LieType.Simplicity.fam_2f4_simplicity X 2 n hre).2,
    CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hre⟩

end F4

end Exceptional

section Certified

theorem uc22p20g_excFacts : UC22P20gExcFacts :=
  ⟨uc22p20g_excG2, uc22p20g_exc3D4, uc22p20g_exc2F4⟩

variable {G : Type} [Group G] [Finite G]

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UC22
