module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.RankThree.PartTwo.Sec4.Census (tableOrder)

@[expose] def KShapeList (X : Type) [Group X] : Prop :=
  IsL2 X 2 ∨ IsU3 X 2 ∨ IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2 ∨
  (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 9 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e X) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((p % 4 = 3 ∧ LieModel X .PSL 3 p 1) ∨ (p % 4 = 1 ∧ LieModel X .PSU 3 p 1))) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel X .PSp 2 p 1)

private lemma w183K3Shape_isQuasisimple_of_open {J : Type} [Group J]
    (hq : CFSG.Open.IsQuasisimple J) : CFSG.IsQuasisimple J := by
  haveI : Group.IsPerfect J := ⟨hq.1⟩
  exact CFSG.RankThree.PartTwo.Sec4.Census.isQuasisimple_of_isPerfect hq.2

private lemma w183K3Shape_models_of_blueprint {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (h : CFSG.Blueprint.LieModel X t n p f)
    (ht : t ∈ CFSG.Blueprint.classicalTags) : CFSG.Models.LieModel X t n p f := by
  have hc : StatedClassicalModel X t n p f := CFSG.Blueprint.LieModel.statedClassicalModel h ht
  exact ⟨hc.1, Or.inl hc⟩

private lemma w183K3Shape_false_of_dvd_two {J : Type} [Group J] [Finite J]
    (hodd : Odd (Nat.card ↥(Subgroup.center J))) (hZ : Nontrivial ↥(Subgroup.center J))
    (hdiv : Nat.card ↥(Subgroup.center J) ∣ 2) : False := by
  haveI : Nontrivial ↥(Subgroup.center J) := hZ
  have h1 : Nat.card ↥(Subgroup.center J) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
    · exact h1
    · rw [h2] at hodd
      exact absurd hodd (by decide)
  exact (Finite.one_lt_card (α := ↥(Subgroup.center J))).ne' h1

private lemma w183K3Shape_false_of_models {J X : Type} [Group J] [Finite J] [Group X]
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hq : CFSG.Open.IsQuasisimple J) (hodd : Odd (Nat.card ↥(Subgroup.center J)))
    (hZ : Nontrivial ↥(Subgroup.center J)) (e : J ⧸ Subgroup.center J ≃* X)
    {t : StatedLieTag} {n p f : ℕ} (hm : CFSG.Models.LieModel X t n p f)
    (htab : tableOrder t n p f ∣ 2) : False := by
  have hq' : CFSG.IsQuasisimple J := w183K3Shape_isQuasisimple_of_open hq
  have hdiv := CFSG.RankThree.PartTwo.Sec4.Census.card_center_dvd_tableOrder hGA hq' e hm
  exact w183K3Shape_false_of_dvd_two hodd hZ (hdiv.trans htab)

private lemma w183K3Shape_exc_psl2 {s f : ℕ} (hs2 : s ≠ 2) (h92 : ¬ (s = 3 ∧ f = 2)) :
    exceptionalOrders .PSL 2 s f = (1, 1) := by
  unfold exceptionalOrders
  split <;> first | rfl | omega | (simp_all)

private lemma w183K3Shape_exc_psl3 {s f : ℕ} (hs2 : s ≠ 2) :
    exceptionalOrders .PSL 3 s f = (1, 1) := by
  unfold exceptionalOrders
  split <;> first | rfl | omega | (simp_all)

private lemma w183K3Shape_exc_psu3 {s f : ℕ} :
    exceptionalOrders .PSU 3 s f = (1, 1) := by
  unfold exceptionalOrders
  split <;> first | rfl | omega | (simp_all)

private lemma w183K3Shape_exc_psp2 {s f : ℕ} :
    exceptionalOrders .PSp 2 s f = (1, 1) := rfl

theorem kstar_residual_shape (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {J X : Type} [Group J] [Finite J] [Group X] (hq : CFSG.Open.IsQuasisimple J)
    (hodd : Odd (Nat.card ↥(Subgroup.center J))) (hZ : Nontrivial ↥(Subgroup.center J))
    (e : J ⧸ Subgroup.center J ≃* X) (hX : KShapeList X) :
    IsAlt X 6 ∨ IsL3 X 2 ∨ (∃ p : ℕ, p.Prime ∧ p % 12 = 7 ∧ LieModel X .PSL 3 p 1) ∨
    (∃ p : ℕ, p.Prime ∧ p % 12 = 5 ∧ LieModel X .PSU 3 p 1) := by
  have hZ' : Nat.card ↥(Subgroup.center J) ≠ 1 := by
    haveI : Nontrivial ↥(Subgroup.center J) := hZ
    exact (Finite.one_lt_card (α := ↥(Subgroup.center J))).ne'
  rcases hX with hL2 | hU3 | hAlt | hL31 | hL32 | hSp4 |
    ⟨p, e', hp, hne, hgt, hF⟩ | ⟨p, hp, hne, hInner⟩ | ⟨p, hp, hne, hSp⟩
  · exact (w183K3Shape_false_of_models hGA hq hodd hZ e
      (w183K3Shape_models_of_blueprint hL2 (by decide)) (by decide)).elim
  · exact (w183K3Shape_false_of_models hGA hq hodd hZ e
      (w183K3Shape_models_of_blueprint hU3 (by decide)) (by decide)).elim
  · exact Or.inl hAlt
  · exact (w183K3Shape_false_of_models hGA hq hodd hZ e
      (w183K3Shape_models_of_blueprint hL31 (by decide)) (by decide)).elim
  · exact Or.inr (Or.inl hL32)
  · exact (w183K3Shape_false_of_models hGA hq hodd hZ e
      (w183K3Shape_models_of_blueprint hSp4 (by decide)) (by decide)).elim
  ·
    exfalso
    have h92 : ¬ (p = 3 ∧ e' = 2) := by
      rintro ⟨rfl, rfl⟩
      norm_num at hgt
    have hgcd : Nat.gcd 2 (p ^ e' - 1) = 2 := by
      obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hne).pow
      exact Nat.gcd_eq_left ⟨k, by rw [hk]; omega⟩
    have htab : tableOrder .PSL 2 p e' = 2 := by
      simp only [tableOrder, genericOrders, w183K3Shape_exc_psl2 hne h92, hgcd]
    exact w183K3Shape_false_of_models hGA hq hodd hZ e
      (show CFSG.Models.LieModel X .PSL 2 p e' from ⟨hF.1, Or.inl hF⟩) (by rw [htab])
  · rcases hInner with ⟨h4, hL3⟩ | ⟨h4, hU3p⟩
    ·
      have hq' : CFSG.IsQuasisimple J := w183K3Shape_isQuasisimple_of_open hq
      have hm : CFSG.Models.LieModel X .PSL 3 p 1 :=
        w183K3Shape_models_of_blueprint hL3 (by decide)
      have hdiv := CFSG.RankThree.PartTwo.Sec4.Census.card_center_dvd_tableOrder hGA hq' e hm
      have htab : tableOrder .PSL 3 p 1 = Nat.gcd 3 (p - 1) := by
        simp only [tableOrder, genericOrders, w183K3Shape_exc_psl3 hne]
        norm_num
      rw [htab] at hdiv
      have hcard3 : Nat.card ↥(Subgroup.center J) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp
          (hdiv.trans (Nat.gcd_dvd_left 3 (p - 1))) with h1 | h3
        · exact absurd h1 hZ'
        · exact h3
      have h3dvd : 3 ∣ p - 1 := by
        have h' : 3 ∣ Nat.gcd 3 (p - 1) := by rwa [hcard3] at hdiv
        exact (Nat.dvd_gcd_iff.mp h').2
      have hpge : 3 ≤ p := by
        have h2 := hp.two_le
        omega
      have hp3 : p % 3 = 1 := by
        obtain ⟨k, hk⟩ := h3dvd
        omega
      exact Or.inr (Or.inr (Or.inl ⟨p, hp, by omega, hL3⟩))
    ·
      have hq' : CFSG.IsQuasisimple J := w183K3Shape_isQuasisimple_of_open hq
      have hm : CFSG.Models.LieModel X .PSU 3 p 1 :=
        w183K3Shape_models_of_blueprint hU3p (by decide)
      have hdiv := CFSG.RankThree.PartTwo.Sec4.Census.card_center_dvd_tableOrder hGA hq' e hm
      have htab : tableOrder .PSU 3 p 1 = Nat.gcd 3 (p + 1) := by
        simp only [tableOrder, genericOrders, w183K3Shape_exc_psu3]
        norm_num
      rw [htab] at hdiv
      have hcard3 : Nat.card ↥(Subgroup.center J) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp
          (hdiv.trans (Nat.gcd_dvd_left 3 (p + 1))) with h1 | h3
        · exact absurd h1 hZ'
        · exact h3
      have h3dvd : 3 ∣ p + 1 := by
        have h' : 3 ∣ Nat.gcd 3 (p + 1) := by rwa [hcard3] at hdiv
        exact (Nat.dvd_gcd_iff.mp h').2
      have hp3 : p % 3 = 2 := by
        obtain ⟨k, hk⟩ := h3dvd
        omega
      exact Or.inr (Or.inr (Or.inr ⟨p, hp, by omega, hU3p⟩))
  ·
    exfalso
    have h2dvd : 2 ∣ p - 1 := by
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hne
      exact ⟨k, by omega⟩
    have hgcd : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
      simpa using Nat.gcd_eq_left h2dvd
    have htab : tableOrder .PSp 2 p 1 = 2 := by
      simp only [tableOrder, genericOrders, w183K3Shape_exc_psp2, hgcd]
    exact w183K3Shape_false_of_models hGA hq hodd hZ e
      (w183K3Shape_models_of_blueprint hSp (by decide)) (by rw [htab])

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
