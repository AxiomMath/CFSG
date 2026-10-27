module

public import CFSG.Timmesfeld.Bridge.Asc72Triangle
import CFSG.Timmesfeld.Bridge.Asc72Theorem
import CFSG.Timmesfeld.Special.TwoCore
import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBSolvable
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.BaerCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import Certificates.Certificate43
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur
import CFSG.Timmesfeld.Bridge.Asc72Lift

public section

namespace CFSG.OddTranspositions.PartThree.EightSix

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

theorem orderOf_image_mul_dvd_four {X Y : Type} [Group X] [Group Y] {u w v : X}
    (h4 : orderOf (u * v * w) = 4) (φ : X →* Y) :
    orderOf (φ u * φ v * φ w) ∣ 4 := by
  have h := orderOf_map_dvd φ (u * v * w)
  rw [h4] at h
  simpa only [map_mul] using h

theorem orderOf_image_mul_eq_four {Y : Type} [Group Y] [Finite Y] {E : Set Y}
    (hE : IsOddTransp E) (hN : IsNormalSet E) {a b c : Y} (ht : IsTriangle E a b c)
    (hdvd : orderOf (a * c * b) ∣ 4) : orderOf (a * c * b) = 4 := by
  rcases ht.orderOf_cases hE hN with h1 | h4 | h3
  · exfalso
    obtain ⟨hodd, hgt⟩ := h1
    have hfour : orderOf (a * c * b) ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact hdvd
    have hq1 := CFSG.Timmesfeld.Special.eq_one_of_odd_of_dvd_two_pow hodd hfour
    omega
  · exact h4
  · exfalso
    obtain ⟨n, hnodd, hn1, hord⟩ := h3
    have h2n : 2 * n ∣ 4 := hord ▸ hdvd
    have hn4 : n ∣ 4 := (Nat.dvd_mul_left n 2).trans h2n
    have hfour : n ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact hn4
    have hn1' := CFSG.Timmesfeld.Special.eq_one_of_odd_of_dvd_two_pow hnodd hfour
    omega

theorem isSolvable_of_closure_triple_eq_top_of_eq {Y : Type} [Group Y] {a b c : Y}
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (h : a = b ∨ a = c ∨ b = c)
    (hgen : Subgroup.closure ({a, b, c} : Set Y) = ⊤) : Group.IsSolvable Y := by
  rcases h with h | h | h
  · have htop : Subgroup.closure ({a, c} : Set Y) = ⊤ := by
      rw [← hgen]
      congr 1
      ext x
      simp [h]
    exact isSolvable_of_two_involutions a c ha hc htop
  · have htop : Subgroup.closure ({a, b} : Set Y) = ⊤ := by
      rw [← hgen]
      congr 1
      ext x
      simp [h, or_comm]
    exact isSolvable_of_two_involutions a b ha hb htop
  · have htop : Subgroup.closure ({a, b} : Set Y) = ⊤ := by
      rw [← hgen]
      congr 1
      ext x
      simp [h]
    exact isSolvable_of_two_involutions a b ha hb htop

theorem isSolvable_quotient_of_disjoint {X : Type} [Group X] [Finite X] {D : Set X}
    (hS : Setup X D) {u w v : X} (htri : IsTriangle D u w v)
    (h4 : orderOf (u * v * w) = 4) (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤)
    {N : Subgroup X} [N.Normal] (hND : ∀ d ∈ D, d ∉ N) (hN1 : N ≠ ⊥)
    (hind : ∀ (Y : Type) [Group Y] [Finite Y] (E : Set Y), Nat.card Y < Nat.card X →
      Setup Y E → ∀ a b c : Y, IsTriangle E a b c → orderOf (a * c * b) = 4 →
      Subgroup.closure ({a, b, c} : Set Y) = ⊤ → Group.IsSolvable Y) :
    Group.IsSolvable (X ⧸ N) := by
  classical
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  have hπne : ∀ d ∈ D, π d ≠ 1 := fun d hd h1 =>
    hND d hd ((QuotientGroup.eq_one_iff d).mp h1)
  have hS' : Setup (X ⧸ N) (π '' D) :=
    hS.map π (QuotientGroup.mk'_surjective N) hπne
  have hgen' : Subgroup.closure ({π u, π w, π v} : Set (X ⧸ N)) = ⊤ := by
    have h := MonoidHom.map_closure π (s := ({u, w, v} : Set X))
    rw [hgen, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N)] at h
    simpa only [Set.image_insert_eq, Set.image_singleton] using h.symm
  have hpu2 : π u * π u = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one htri.1, map_one]
  have hpw2 : π w * π w = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one htri.2.2.1, map_one]
  have hpv2 : π v * π v = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one htri.2.1, map_one]
  have huE : π u ∈ π '' D := ⟨u, htri.1, rfl⟩
  have hvE : π v ∈ π '' D := ⟨v, htri.2.1, rfl⟩
  have hwE : π w ∈ π '' D := ⟨w, htri.2.2.1, rfl⟩
  have hcuv : Commute (π u) (π v) := htri.2.2.2.2.1.map π
  have hcard : Nat.card (X ⧸ N) < Nat.card X := CFSG.card_quotient_lt_of_ne_bot N hN1
  by_cases huv : π u = π v
  · exact isSolvable_of_closure_triple_eq_top_of_eq hpu2 hpw2 hpv2
      (Or.inr (Or.inl huv)) hgen'
  · by_cases hcuw : Commute (π u) (π w)
    · have huw : π u = π w :=
        eq_of_commute_of_odd hS.oddT htri.1 htri.2.2.1 hcuw
          (hS.oddT.odd_of_not_commute htri.1 htri.2.2.1 htri.2.2.2.2.2.1)
      exact isSolvable_of_closure_triple_eq_top_of_eq hpu2 hpw2 hpv2
        (Or.inl huw) hgen'
    · by_cases hcvw : Commute (π v) (π w)
      · have hvw : π v = π w :=
          eq_of_commute_of_odd hS.oddT htri.2.1 htri.2.2.1 hcvw
            (hS.oddT.odd_of_not_commute htri.2.1 htri.2.2.1 htri.2.2.2.2.2.2)
        exact isSolvable_of_closure_triple_eq_top_of_eq hpu2 hpw2 hpv2
          (Or.inr (Or.inr hvw.symm)) hgen'
      ·
        have htri' : IsTriangle (π '' D) (π u) (π w) (π v) :=
          ⟨huE, hvE, hwE, huv, hcuv, hcuw, hcvw⟩
        have hq4 : orderOf (π u * π v * π w) = 4 :=
          orderOf_image_mul_eq_four hS'.oddT hS'.normal htri'
            (orderOf_image_mul_dvd_four h4 π)
        exact hind (X ⧸ N) (π '' D) hcard hS' (π u) (π w) (π v) htri' hq4 hgen'

theorem isSolvable_of_quotient_secondKind {X : Type} [Group X] [Finite X] {D : Set X}
    (hS : Setup X D) {u w v : X} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hgen : Subgroup.closure ({u, w, v} : Set X) = ⊤) {N : Subgroup X} [N.Normal]
    (hN : Group.IsSolvable N) (hN1 : N ≠ ⊥)
    (hind : ∀ (Y : Type) [Group Y] [Finite Y] (E : Set Y), Nat.card Y < Nat.card X →
      Setup Y E → ∀ a b c : Y, IsTriangle E a b c → orderOf (a * c * b) = 4 →
      Subgroup.closure ({a, b, c} : Set Y) = ⊤ → Group.IsSolvable Y) :
    Group.IsSolvable X := by
  classical
  rcases hS.subset_or_disjoint N with hDN | hND
  ·
    have hNtop : N = ⊤ := hS.eq_top_of_subset N hDN
    have hsolTop : Group.IsSolvable (⊤ : Subgroup X) := hNtop ▸ hN
    exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := X)).toMonoidHom)
      (Subgroup.topEquiv (G := X)).surjective
  · have hQ : Group.IsSolvable (X ⧸ N) :=
      isSolvable_quotient_of_disjoint hS htri h4 hgen hND hN1 hind
    have hsolN : Group.IsSolvable N := hN
    have hsolQ : Group.IsSolvable (X ⧸ N) := hQ
    exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end CFSG.OddTranspositions.PartThree.EightSix
