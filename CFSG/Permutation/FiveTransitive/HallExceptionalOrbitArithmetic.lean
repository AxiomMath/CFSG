module

public import CFSG.Permutation.FiveTransitive.HallExceptionalCalculation
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.Research.HallExceptionalOrbitArithmetic

open MulAction

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

private theorem orbit_ncard_dvd_set_ncard
    (P : Subgroup G) (t : ℕ) (S : Set X)
    (horbitSub : ∀ x ∈ S, MulAction.orbit P x ⊆ S)
    (horbitCard : ∀ x ∈ S, (MulAction.orbit P x).ncard = t) :
    t ∣ S.ncard := by
  classical
  induction hcard : S.ncard using Nat.strong_induction_on generalizing S with
  | h n ih =>
      by_cases hS : S = ∅
      · rw [hS] at hcard
        have hn : n = 0 := by
          simpa only [Set.ncard_empty] using hcard.symm
        subst n
        simpa only [Set.ncard_empty] using dvd_zero t
      · obtain ⟨x, hx⟩ : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
        let O : Set X := MulAction.orbit P x
        let R : Set X := S \ O
        have hOS : O ⊆ S := horbitSub x hx
        have hxO : x ∈ O := MulAction.mem_orbit_self x
        have hOnonempty : O.Nonempty := ⟨x, hxO⟩
        have hOpos : 0 < O.ncard := hOnonempty.ncard_pos
        have hOle : O.ncard ≤ S.ncard := Set.ncard_le_ncard hOS
        have hRcard : R.ncard = S.ncard - O.ncard := by
          exact Set.ncard_diff hOS
        have hRlt : R.ncard < S.ncard := by omega
        have hRltN : R.ncard < n := by omega
        have hRorbitSub :
            ∀ y ∈ R, MulAction.orbit P y ⊆ R := by
          intro y hy z hz
          refine ⟨horbitSub y hy.1 hz, ?_⟩
          intro hzO
          obtain ⟨g, hgy⟩ := MulAction.mem_orbit_iff.mp hz
          obtain ⟨k, hkx⟩ := MulAction.mem_orbit_iff.mp hzO
          apply hy.2
          rw [← hgy] at hkx
          apply MulAction.mem_orbit_iff.mpr
          refine ⟨g⁻¹ * k, ?_⟩
          rw [mul_smul, hkx, inv_smul_smul]
        have hRorbitCard :
            ∀ y ∈ R, (MulAction.orbit P y).ncard = t := by
          intro y hy
          exact horbitCard y hy.1
        have hRdvd : t ∣ R.ncard := by
          exact ih R.ncard hRltN R hRorbitSub hRorbitCard rfl
        have hsum : R.ncard + O.ncard = S.ncard :=
          Set.ncard_diff_add_ncard_of_subset hOS
        have hOcard : O.ncard = t := horbitCard x hx
        obtain ⟨k, hk⟩ := hRdvd
        refine ⟨k + 1, ?_⟩
        calc
          n = S.ncard := hcard.symm
          _ = R.ncard + O.ncard := hsum.symm
          _ = t * k + t := by rw [hk, hOcard]
          _ = t * (k + 1) := by rw [Nat.mul_add, Nat.mul_one]

theorem pgroup_orbit_eq_triple
    (A P : Subgroup G) (hA : IsPGroup 3 A) (hPA : P ≤ A)
    (B T E : Set X) (hfixed : MulAction.fixedPoints A X = B)
    (hE : E = B ∪ T) (hBT : Disjoint B T)
    (hTcard : T.ncard = 3)
    (p : X) (hpT : p ∈ T)
    (hPfix : E ⊆ MulAction.fixedPoints P X)
    (t w : ℕ) (ht : t = 3 ^ w) (hw : 2 ≤ w)
    (horbitCard : ∀ x : X, x ∉ E →
      (MulAction.orbit P x).ncard = t) :
    MulAction.orbit A p = T := by
  classical
  let O : Set X := MulAction.orbit A p
  let I : Set X := O ∩ E
  let S : Set X := O \ E
  have hpB : p ∉ B := by
    intro hpB
    exact Set.disjoint_left.mp hBT hpB hpT
  have hpNotFixed : p ∉ MulAction.fixedPoints A X := by
    rw [hfixed]
    exact hpB
  obtain ⟨n, hn⟩ := hA.card_orbit p
  have hOcard : O.ncard = 3 ^ n := by
    simpa only [O, Nat.card_coe_set_eq] using hn
  have hnpos : 0 < n := by
    by_contra hnpos
    have hnzero : n = 0 := by omega
    have hcardOne : Fintype.card O = 1 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        hOcard, hnzero, pow_zero]
    exact hpNotFixed
      ((MulAction.mem_fixedPoints_iff_card_orbit_eq_one).mpr hcardOne)
  have hOBempty : O ∩ B = ∅ := by
    ext x
    constructor
    · rintro ⟨hxO, hxB⟩
      obtain ⟨g, hgp⟩ := MulAction.mem_orbit_iff.mp hxO
      have hxFixed : x ∈ MulAction.fixedPoints A X := by
        rw [hfixed]
        exact hxB
      have hginv := MulAction.mem_fixedPoints.mp hxFixed g⁻¹
      have hpx : p = x := by
        calc
          p = g⁻¹ • (g • p) := by rw [inv_smul_smul]
          _ = g⁻¹ • x := congrArg (fun z : X ↦ g⁻¹ • z) hgp
          _ = x := hginv
      exact (hpB (hpx ▸ hxB)).elim
    · intro hx
      exact hx.elim
  have hIT : I ⊆ T := by
    intro x hx
    have hxE : x ∈ B ∪ T := by
      rw [← hE]
      exact hx.2
    rcases hxE with hxB | hxT
    · have : x ∈ O ∩ B := ⟨hx.1, hxB⟩
      rw [hOBempty] at this
      exact this.elim
    · exact hxT
  have hpI : p ∈ I := by
    refine ⟨MulAction.mem_orbit_self p, ?_⟩
    rw [hE]
    exact Or.inr hpT
  have hInonempty : I.Nonempty := ⟨p, hpI⟩
  have hIpos : 0 < I.ncard := hInonempty.ncard_pos
  have hIle : I.ncard ≤ 3 := by
    rw [← hTcard]
    exact Set.ncard_le_ncard hIT
  have hSorbitSub :
      ∀ x ∈ S, MulAction.orbit P x ⊆ S := by
    intro x hx z hz
    obtain ⟨g, hgx⟩ := MulAction.mem_orbit_iff.mp hz
    have hzO : z ∈ O := by
      obtain ⟨a, hap⟩ := MulAction.mem_orbit_iff.mp hx.1
      apply MulAction.mem_orbit_iff.mpr
      let gA : A := ⟨(g : G), hPA g.prop⟩
      refine ⟨gA * a, ?_⟩
      change (a : G) • p = x at hap
      change (g : G) • x = z at hgx
      change ((g : G) * (a : G)) • p = z
      rw [mul_smul, hap, hgx]
    refine ⟨hzO, ?_⟩
    intro hzE
    have hzFixed := MulAction.mem_fixedPoints.mp (hPfix hzE) g⁻¹
    apply hx.2
    have hxz : x = z := by
      calc
        x = g⁻¹ • (g • x) := by rw [inv_smul_smul]
        _ = g⁻¹ • z := congrArg (fun y : X ↦ g⁻¹ • y) hgx
        _ = z := hzFixed
    rwa [hxz]
  have hSorbitCard :
      ∀ x ∈ S, (MulAction.orbit P x).ncard = t := by
    intro x hx
    exact horbitCard x hx.2
  have htS : t ∣ S.ncard :=
    orbit_ncard_dvd_set_ncard P t S hSorbitSub hSorbitCard
  have hthreeT : 3 ∣ t := by
    rw [ht]
    exact dvd_pow_self 3 (by omega)
  have hthreeS : 3 ∣ S.ncard := hthreeT.trans htS
  have hsum : I.ncard + S.ncard = O.ncard := by
    simpa only [I, S] using Set.ncard_inter_add_ncard_diff_eq_ncard O E
  have hthreeO : 3 ∣ O.ncard := by
    rw [hOcard]
    exact dvd_pow_self 3 (by omega)
  have hthreeI : 3 ∣ I.ncard := by
    apply (Nat.dvd_add_iff_left hthreeS).mpr
    rwa [hsum]
  have hIcard : I.ncard = 3 := by
    have := Nat.le_of_dvd hIpos hthreeI
    omega
  have hITeq : I = T :=
    Set.eq_of_subset_of_ncard_le hIT (by rw [hIcard, hTcard])
  have hnEq : n = 1 := by
    by_contra hnOne
    have hnTwo : 2 ≤ n := by omega
    have hnineO : 9 ∣ O.ncard := by
      rw [hOcard]
      have hpow : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 hnTwo
      norm_num at hpow ⊢
      exact hpow
    have hnineT : 9 ∣ t := by
      rw [ht]
      have hpow : 3 ^ 2 ∣ 3 ^ w := pow_dvd_pow 3 hw
      norm_num at hpow ⊢
      exact hpow
    have hnineS : 9 ∣ S.ncard := hnineT.trans htS
    have hnineI : 9 ∣ I.ncard := by
      apply (Nat.dvd_add_iff_left hnineS).mpr
      rwa [hsum]
    rw [hIcard] at hnineI
    norm_num at hnineI
  have hOthree : O.ncard = 3 := by
    rw [hOcard, hnEq]
    norm_num
  have hSzero : S.ncard = 0 := by omega
  have hSempty : S = ∅ :=
    (Set.ncard_eq_zero (s := S) (Set.toFinite S)).mp hSzero
  have hOE : O ⊆ E := by
    intro x hxO
    by_contra hxNotE
    have hxS : x ∈ S := ⟨hxO, hxNotE⟩
    rw [hSempty] at hxS
    exact hxS.elim
  calc
    O = I := by
      ext x
      constructor
      · intro hx
        exact ⟨hx, hOE hx⟩
      · exact fun hx ↦ hx.1
    _ = T := hITeq

end FiveTransitive.Research.HallExceptionalOrbitArithmetic

end CFSG
