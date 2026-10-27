module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
public import CFSG.Sporadic.SmallOddCore.J3Aut
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5Small

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)
open CFSG.ComponentClassification.OuterAutomorphisms


section CertificateFree


theorem le_innAut_of_card_outer_le_two {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (h : Nat.card (Outer (Y ⧸ center Y)) ≤ 2) {R : Subgroup (MulAut Y)} (hR : IsPGroup 3 R) :
    R ≤ innAut Y := by
  intro φ hφ
  obtain ⟨k, hk⟩ := hR ⟨φ, hφ⟩
  have hφk : φ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set ψ : Outer (Y ⧸ center Y) :=
    centerQuotientOuterHom Y (QuotientGroup.mk' (inner Y) φ) with hψ
  have h3 : orderOf ψ ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [hψ, ← map_pow, ← map_pow, hφk, map_one, map_one])
  have h2 : orderOf ψ ∣ 2 := by
    have hpos : 0 < Nat.card (Outer (Y ⧸ center Y)) := Nat.card_pos
    have hd := orderOf_dvd_natCard ψ
    have hc : Nat.card (Outer (Y ⧸ center Y)) = 1 ∨ Nat.card (Outer (Y ⧸ center Y)) = 2 := by
      omega
    rcases hc with hc | hc <;> rw [hc] at hd
    · exact hd.trans (one_dvd 2)
    · exact hd
  have h1 : orderOf ψ = 1 :=
    Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 3 2).pow_left k) h3 h2
  have hmk : QuotientGroup.mk' (inner Y) φ = 1 :=
    (map_eq_one_iff _ (centerQuotient_outer_injective Y)).mp (orderOf_eq_one_iff.mp h1)
  exact (QuotientGroup.eq_one_iff (N := inner Y) φ).mp hmk

theorem card_outer_alternatingGroup_le_two {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (Outer (alternatingGroup (Fin n))) ≤ 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  have hle : (alternatingGroup (Fin n)).map
      (MulAut.conjNormal (H := alternatingGroup (Fin n))) ≤ innAut (alternatingGroup (Fin n)) := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, by ext x; simp [MulAut.conj_apply]⟩
  have hidx := Subgroup.index_map_of_bijective hbij (alternatingGroup (Fin n))
  rw [alternatingGroup.index_eq_two] at hidx
  have hdvd := hidx ▸ Subgroup.index_dvd_of_le hle
  rw [← Subgroup.index_eq_card]
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem card_outer_psp43_le_two :
    Nat.card (Outer CFSG.GH74.Exceptional.PSp43) ≤ 2 := by
  have hle : Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) ≤ 51840 :=
    CFSG.Quasithin.SimsF5.card_mulAut_of_mulEquiv_PSp43 (MulEquiv.refl _)
  have hconj : Function.Injective (MulAut.conj : CFSG.GH74.Exceptional.PSp43 →*
      MulAut CFSG.GH74.Exceptional.PSp43) :=
    CFSG.HardMathSupport.Timmesfeld.DefChar.conj_injective_of_center_eq_bot center_PSp43_eq_bot
  have hinner : Nat.card (innAut CFSG.GH74.Exceptional.PSp43) = 25920 := by
    rw [← card_PSp43]
    exact (Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv).symm
  have hcard : Nat.card (MulAut CFSG.GH74.Exceptional.PSp43) =
      Nat.card (Outer CFSG.GH74.Exceptional.PSp43) * 25920 := by
    rw [← hinner]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  omega

theorem card_outer_le_two_of_isAlt {S : Type} [Group S] {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (h : IsAlt S n) : Nat.card (Outer S) ≤ 2 := by
  obtain ⟨e⟩ := h
  exact CFSG.Sporadic.Schreier.outer_card_le_of_equiv (card_outer_alternatingGroup_le_two hn hn6) e

theorem card_outer_le_two_of_psp43 {S : Type} [Group S] (h : LieModel S .PSp 2 3 1) :
    Nat.card (Outer S) ≤ 2 := by
  obtain ⟨e⟩ := psp43_equiv_of_lieModel h
  exact CFSG.Sporadic.Schreier.outer_card_le_of_equiv card_outer_psp43_le_two e

@[expose] def K2Lie : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (fam : LieFam811) (r f : ℕ), IsLie811 Y fam r f →
    pRank 3 (⊤ : Subgroup Y) = 3 →
    ∀ R : Subgroup (MulAut Y), IsPGroup 3 R →
      CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ innAut Y) (innAut Y) → ¬ R ≤ innAut Y →
      4 ≤ pRank 3 R

theorem exists_isLie811_of_clause4 {Y : Type} [Group Y] (hq : IsQuasisimple Y)
    (hZ : Odd (Nat.card (center Y)))
    (h : ((∃ p f : ℕ, p ≠ 3 ∧ LieModel (Y ⧸ center Y) .PSp 3 p f) ∨
      (∃ p f : ℕ, p ≠ 3 ∧ LieModel (Y ⧸ center Y) .POmegaMinus 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (Y ⧸ center Y) .PSL 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ p ^ f ≠ 2 ∧ LieModel (Y ⧸ center Y) .PSU 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel (Y ⧸ center Y) .PSL 6 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (Y ⧸ center Y) .PSU 6 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel (Y ⧸ center Y) .PSL 7 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (Y ⧸ center Y) .PSU 7 p f) ∨
      (∃ p f : ℕ, p ≠ 3 ∧ LieModel (Y ⧸ center Y) .POmegaOdd 3 p f))) :
    ∃ (fam : LieFam811) (r f : ℕ), IsLie811 Y fam r f := by
  rcases h with ⟨p, f, h3, hm⟩ | ⟨p, f, h3, hm⟩ | ⟨p, f, h1, hm⟩ | ⟨p, f, h1, h2, hm⟩ |
    ⟨p, f, h1, hm⟩ | ⟨p, f, h1, hm⟩ | ⟨p, f, h1, hm⟩ | ⟨p, f, h1, hm⟩ | ⟨p, f, h3, hm⟩
  · exact ⟨.psp6, p, f, hq, hZ, (CFSG.Blueprint.LieModel.admissible hm).1, h3, hm⟩
  · exact ⟨.pomega8m, p, f, hq, hZ, (CFSG.Blueprint.LieModel.admissible hm).1, h3, hm⟩
  · have hp := (CFSG.Blueprint.LieModel.admissible hm).1
    exact ⟨.l4, p, f, hq, hZ, hp, by omega, Or.inl ⟨h1, hm⟩⟩
  · exact ⟨.l4, p, f, hq, hZ, (CFSG.Blueprint.LieModel.admissible hm).1, h2, Or.inr ⟨h1, hm⟩⟩
  · have hp := (CFSG.Blueprint.LieModel.admissible hm).1
    exact ⟨.l6, p, f, hq, hZ, hp, Or.inl ⟨h1, hm⟩⟩
  · have hp := (CFSG.Blueprint.LieModel.admissible hm).1
    exact ⟨.l6, p, f, hq, hZ, hp, Or.inr ⟨h1, hm⟩⟩
  · have hp := (CFSG.Blueprint.LieModel.admissible hm).1
    exact ⟨.l7, p, f, hq, hZ, hp, Or.inl ⟨h1, hm⟩⟩
  · have hp := (CFSG.Blueprint.LieModel.admissible hm).1
    exact ⟨.l7, p, f, hq, hZ, hp, Or.inr ⟨h1, hm⟩⟩
  · have hadm := CFSG.Blueprint.LieModel.admissible hm
    exact ⟨.omega7, p, f, hq, hZ, hadm.1, hadm.2.2.2, h3, hm⟩

end CertificateFree

theorem card_outer_le_two_of_isJ3 {S : Type} [Group S] (h : IsSpor S .J3) :
    Nat.card (Outer S) ≤ 2 := by
  obtain ⟨e⟩ := h
  have hJ : Nat.card (Outer CFSG.Blueprint.NativeSporadic.J3) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.j3_outer_card_le
      CFSG.Sporadic.Schreier.j3PermEquiv
  exact CFSG.Sporadic.Schreier.outer_card_le_of_equiv hJ e

theorem k2_of_k1 (h1 : K1) (hLie : K2Lie) : K2 := by
  intro Y _ _ hq hcat hZ hr3 hnO hnL R hR hSyl hnin
  haveI : Group.IsPerfect Y := hq.1
  have hqo : CFSG.Open.IsQuasisimple Y := ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  have hr3o : CFSG.Open.pRank 3 (⊤ : Subgroup Y) = 3 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hr3
  have hsmall : Nat.card (Outer (Y ⧸ center Y)) ≤ 2 → False := fun h =>
    hnin (le_innAut_of_card_outer_le_two h hR)
  rcases h1 Y hqo hcat hZ hr3o with hO | ⟨-, hAlt | hL | hLieAlt | hJ⟩
  · exact absurd hO hnO
  · rcases hAlt with h | h | h <;>
      exact (hsmall (card_outer_le_two_of_isAlt (by norm_num) (by norm_num) h)).elim
  · rcases hL with h | h
    · exact absurd h hnL
    · exact (hsmall (card_outer_le_two_of_psp43 h)).elim
  · obtain ⟨fam, r, f, hY⟩ := exists_isLie811_of_clause4 hq hZ hLieAlt
    exact hLie Y fam r f hY hr3 R hR hSyl hnin
  · exact (hsmall (card_outer_le_two_of_isJ3 hJ)).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
