module

public import CFSG.RankThree.PartOne.FOCD.LyBound
import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.RankThree.Native.DerivedGenerators
public import CFSG.RankThree.PartOne.FOC.InnerCase
public import CFSG.RankThree.PartOne.FOC.Transfer
public import CFSG.RankThree.PartOne.SPOR.OuterLy

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

open CFSG.RankThree.PartOne.S12K (charTwoOrder card_of_lieModel_two)

open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo innerAut fixSub mem_fixSub)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Open

section TwoPart


private theorem two_pow_dvd_of_profile {ord N m : ℕ} {Z : ℕ → Prop}
    (hP : Profile ord N Z) (hN : m ≤ N) : 2 ^ m ∣ ord := by
  obtain ⟨r, -, h⟩ := hP.two
  rw [h]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 hN) r

theorem two_pow_dvd_card_lieModel_two {X : Type} [Group X] {t : StatedLieTag} {n m : ℕ}
    (hX : LieModel X t n 2 m) (hm : 1 ≤ m) : 2 ^ m ∣ Nat.card X := by
  obtain ⟨hadm, hcard⟩ := card_of_lieModel_two hX
  rw [hcard]
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -⟩ := hadm
    refine two_pow_dvd_of_profile (profile_ordA (n := n - 1) (f := m) (by omega) hm) ?_
    have h1 : 1 ≤ (n - 1) * (n - 1 + 1) / 2 := by
      apply Nat.div_pos _ (by norm_num)
      have : 1 ≤ n - 1 := by omega
      nlinarith
    exact Nat.le_mul_of_pos_right m h1
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    refine two_pow_dvd_of_profile (profile_ordTwistedA (n := n - 1) (g := m) (by omega) hm) ?_
    have h1 : 1 ≤ (n - 1) * (n - 1 + 1) / 2 := by
      apply Nat.div_pos _ (by norm_num)
      have : 2 ≤ n - 1 := by omega
      nlinarith
    exact Nat.le_mul_of_pos_right m h1
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    refine two_pow_dvd_of_profile (profile_ordBC (n := n) hm) ?_
    have h1 : 1 ≤ n * n := by nlinarith
    exact Nat.le_mul_of_pos_right m h1
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    refine two_pow_dvd_of_profile (profile_ordD (n := n) (by omega) hm) ?_
    have h1 : 1 ≤ n * (n - 1) := by
      have : 1 ≤ n - 1 := by omega
      nlinarith
    exact Nat.le_mul_of_pos_right m h1
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    refine two_pow_dvd_of_profile (profile_ordTwistedD (n := n) (by omega) hm) ?_
    have h1 : 1 ≤ n * (n - 1) := by
      have : 1 ≤ n - 1 := by omega
      nlinarith
    exact Nat.le_mul_of_pos_right m h1
  case G2 => exact two_pow_dvd_of_profile (profile_ordG2 (f := m) hm) (by omega)
  case F4 => exact two_pow_dvd_of_profile (profile_ordF4 (f := m) hm) (by omega)
  case E6 => exact two_pow_dvd_of_profile (profile_ordE6 (f := m) hm) (by omega)
  case E7 => exact two_pow_dvd_of_profile (profile_ordE7 (f := m) hm) (by omega)
  case E8 => exact two_pow_dvd_of_profile (profile_ordE8 (f := m) hm) (by omega)
  case twistedE6 => exact two_pow_dvd_of_profile (profile_ordTwistedE6 (f := m) hm) (by omega)
  case trialityD4 => exact two_pow_dvd_of_profile (profile_ordTrialityD4 (f := m) hm) (by omega)
  case twistedB2 => exact two_pow_dvd_of_profile (profile_ordSuzuki (f := m) hm) (by omega)
  case twistedG2 =>
    obtain ⟨-, -, -, hp3, -⟩ := hadm
    omega
  case twistedF4 => exact two_pow_dvd_of_profile (profile_ordTwistedF4 (f := m) hm) (by omega)
  case Tits =>
    obtain ⟨-, -, -, -, hm1⟩ := hadm
    have : m = 1 := hm1
    subst this
    show 2 ^ 1 ∣ ordTits
    unfold ordTits
    norm_num

end TwoPart

theorem mem_innerAut_of_not_dvd_card_outer {T : Type} [Group T] {p : ℕ} (hp : p.Prime)
    (hnd : ¬ p ∣ Nat.card (Outer T)) {β : MulAut T} (hβ : β ^ p = 1) : β ∈ innerAut T := by
  have h1 : (QuotientGroup.mk β : Outer T) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hβ, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk β : Outer T) ∣ p := orderOf_dvd_of_pow_eq_one h1
  rcases (Nat.dvd_prime hp).mp h2 with h | h
  · have h3 : β ∈ inner T := (QuotientGroup.eq_one_iff β).mp (orderOf_eq_one_iff.mp h)
    exact h3
  · exact absurd (h ▸ orderOf_dvd_natCard _) hnd

section Ly


theorem fieldInnerT_Ly_five {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hT : Nonempty (T ≃* NativeSporadic.Ly)) :
    FieldInnerT 5 T := by
  intro _ x β E hxp hβp hβx _ hE hxN hxnot ⟨t, n, f, hf, hLie⟩
  have h5 : Nat.Prime 5 := by norm_num
  have hZ : Subgroup.center T = ⊥ := center_eq_bot_of_nonab ‹IsSimpleGroup T› hnab
  obtain ⟨hout2, -⟩ := SPOR.outer_order_divides_two' hT
  have hnd : ¬ 5 ∣ Nat.card (Outer T) := fun h =>
    absurd (Nat.le_of_dvd (by norm_num) (h.trans hout2)) (by norm_num)
  obtain ⟨b, hb⟩ := mem_innerAut_of_not_dvd_card_outer h5 hnd hβp
  have hbfix : ∀ y : T, y ∈ fixSub β ↔ b * y * b⁻¹ = y := by
    intro y
    rw [mem_fixSub, ← hb, MulAut.conj_apply]
  by_cases hb1 : b = 1
  ·
    have hβ1 : fixSub β = ⊤ := by
      ext y
      simp [hbfix, hb1]
    rw [hβ1] at hE
    have hs : IsSimpleGroup ↥(⊤ : Subgroup T) := Subgroup.topEquiv.isSimpleGroup
    have hEtop : E = ⊤ := @eq_of_isComponentOf_simple T _ ⊤ E hs hE
    exact hxnot (hEtop ▸ Subgroup.mem_sup_left (Subgroup.mem_top x))
  ·
    have hbp : b ^ 5 = 1 := by
      have h1 : MulAut.conj (b ^ 5) = (1 : MulAut T) := by
        rw [map_pow, hb]; exact hβp
      have h2 : b ^ 5 ∈ Subgroup.center T := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut T => φ g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * b ^ 5 = (b ^ 5 * g * (b ^ 5)⁻¹) * b ^ 5 := by rw [this]
          _ = b ^ 5 * g := by group
      rw [hZ, Subgroup.mem_bot] at h2
      exact h2
    have hbord : orderOf b = 5 := orderOf_eq_prime hbp hb1
    have hX := two_pow_dvd_card_lieModel_two hLie (by nlinarith : 1 ≤ 5 * f)
    have hXE : Nat.card (↥E ⧸ Subgroup.center ↥E) ∣ Nat.card E := by
      rw [← Subgroup.index_eq_card]
      exact Subgroup.index_dvd_card _
    have h2E : 2 ^ (5 * f) ∣ Nat.card E := hX.trans hXE
    obtain ⟨S⟩ : Nonempty (Sylow 2 ↥E) := inferInstance
    have hcardS : Nat.card S = 2 ^ (Nat.card E).factorization 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact Sylow.card_eq_multiplicity S
    have hfac : 5 * f ≤ (Nat.card E).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h2E
    have hS32 : 32 ≤ Nat.card (S : Subgroup ↥E) := by
      rw [hcardS]
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (5 * f) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
        _ ≤ 2 ^ (Nat.card E).factorization 2 := Nat.pow_le_pow_right (by norm_num) hfac
    set R : Subgroup T := (S : Subgroup ↥E).map E.subtype with hR
    have hcardR : Nat.card R = Nat.card (S : Subgroup ↥E) :=
      Subgroup.card_map_of_injective E.subtype_injective
    have hR2 : IsPGroup 2 R := (S.isPGroup').map E.subtype
    have hbR : ∀ u ∈ R, b * u * b⁻¹ = u := by
      rintro _ ⟨s, hs, rfl⟩
      exact (hbfix _).1 (hE.1 s.2)
    have := ly_two_subgroup_commuting_five_le_sixteen hT hbord R hR2 hbR
    omega

end Ly

end CFSG.RankThree.PartOne.FOCD
