module

public import CFSG.RankThree.GF2n.Smith81.Bridge
public import CFSG.RankThree.GF2n.Smith81.Sec2Defs
public import CFSG.RankThree.GF2n.Smith81.TiFusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Local

variable [Finite G] {M Q Z : Subgroup G}

theorem local_of_global_M (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (h213 : Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G))) {v u s : G}
    (hv : IsConj z v) (hu : IsConj z u) (hs : IsConj z s) (huv : Commute u v)
    (hsv : Commute s v) :
    (orderOf (u * s) = 2 ∨ orderOf (u * s) = 4 ∨ Odd (orderOf (u * s))) ∧
      (orderOf (u * s) = 4 → IsConj z ((u * s) ^ 2)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hv
  have hcomm : ∀ t : G, Commute t v → Commute (c⁻¹ * t * c) z := by
    intro t ht
    show c⁻¹ * t * c * z = z * (c⁻¹ * t * c)
    have h1 := ht.eq
    rw [← hc] at h1
    calc c⁻¹ * t * c * z = c⁻¹ * (t * (c * z * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * z * c⁻¹) * t) * c := by rw [h1]
      _ = z * (c⁻¹ * t * c) := by group
  have hu' : IsConj z (c⁻¹ * u * c) := IsConj.trans hu (isConj_iff.mpr ⟨c⁻¹, by simp⟩)
  have hs' : IsConj z (c⁻¹ * s * c) := IsConj.trans hs (isConj_iff.mpr ⟨c⁻¹, by simp⟩)
  have huM : c⁻¹ * u * c ∈ M := mem_M_of_commute_Z H hz hz1 (hcomm u huv).eq
  have hsM : c⁻¹ * s * c ∈ M := mem_M_of_commute_Z H hz hz1 (hcomm s hsv).eq
  have hord : orderOf (c⁻¹ * u * c * (c⁻¹ * s * c)) = orderOf (u * s) := by
    have e : c⁻¹ * u * c * (c⁻¹ * s * c) = c⁻¹ * (u * s) * c⁻¹⁻¹ := by group
    rw [e, CFSG.Timmesfeld.CorB.orderOf_conj]
  refine ⟨?_, fun h4 => ?_⟩
  · have := h213.2.1 _ ⟨hu', huM⟩ _ ⟨hs', hsM⟩
    rwa [hord] at this
  · have h4' : orderOf (c⁻¹ * u * c * (c⁻¹ * s * c)) = 4 := by rw [hord]; exact h4
    have hsq := h213.2.2 _ ⟨hu', huM⟩ _ ⟨hs', hsM⟩ h4'
    have e : (u * s) ^ 2 = c * ((c⁻¹ * u * c * (c⁻¹ * s * c)) ^ 2) * c⁻¹ := by
      simp only [pow_two]; group
    rw [e]
    exact conjClassSet_conj hsq.1 c

end Local

section Graph

theorem diam_two_of_pathReduction {D : Set G}
    (hred : ∀ x ∈ D, ∀ z ∈ D, ∀ w ∈ D, ∀ y ∈ D, Commute x z → Commute z w → Commute w y →
      ∃ v ∈ D, Commute x v ∧ Commute v y)
    {x y : G} (hx : x ∈ D) (h : Relation.ReflTransGen (CommOn D) x y) :
    y ∈ D ∧ ∃ v ∈ D, Commute x v ∧ Commute v y := by
  induction h with
  | refl => exact ⟨hx, x, hx, Commute.refl x, Commute.refl x⟩
  | tail _ hbc ih =>
    obtain ⟨hb, v, hv, hxv, hvb⟩ := ih
    obtain ⟨-, hc, hbc'⟩ := hbc
    obtain ⟨u, hu, hxu, huc⟩ := hred x hx v hv _ hb _ hc hxv hvb hbc'
    exact ⟨hc, u, hu, hxu, huc⟩

theorem diam_two_of_connected {D : Set G}
    (hred : ∀ x ∈ D, ∀ z ∈ D, ∀ w ∈ D, ∀ y ∈ D, Commute x z → Commute z w → Commute w y →
      ∃ v ∈ D, Commute x v ∧ Commute v y)
    (hconn : ∀ x ∈ D, ∀ y ∈ D, Relation.ReflTransGen (CommOn D) x y) :
    ∀ x ∈ D, ∀ y ∈ D, ∃ v ∈ D, Commute x v ∧ Commute v y :=
  fun x hx y hy => (diam_two_of_pathReduction hred hx (hconn x hx y hy)).2

variable [Finite G] {M Q Z : Subgroup G}

theorem isRootInvolutionSet_conjClassSet (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) (h213 : Timmesfeld.IsRootInvolutionSet (conjClassSet z ∩ (M : Set G)))
    (hdiam : ∀ x ∈ conjClassSet z, ∀ y ∈ conjClassSet z,
      ∃ v ∈ conjClassSet z, Commute x v ∧ Commute v y) :
    Timmesfeld.IsRootInvolutionSet (conjClassSet z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isRootInvolutionSet_of_local (fun d hd => ?_) ?_ (fun x hx y hy => ?_)
  · exact orderOf_eq_prime (by rw [pow_two]; exact mul_self_eq_one_of_isConj_Z H hz hd)
      (ne_one_of_isConj_Z hz1 hd)
  · intro v hv x hx y hy hxv hyv
    exact local_of_global_M H hz hz1 h213 hv hx hy hxv hyv
  · obtain ⟨v, hv, h1, h2⟩ := hdiam x hx y hy
    exact ⟨v, hv, h1, h2.symm⟩

end Graph

end CFSG.RankThree.GF2n.Smith81
