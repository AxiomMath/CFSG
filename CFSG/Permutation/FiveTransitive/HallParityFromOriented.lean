module

public import CFSG.Permutation.FiveTransitive.HallLargeDegreeReduced
public import CFSG.Permutation.FiveTransitive.HallReflectionData

public section

namespace CFSG

namespace FiveTransitive.Research.HallParityFromOriented

open MulAction Subgroup
open Research.HallLargeDegreeReduced
open Research.HallOrbitTransitivity
open Research.HallReflectionData
open Research.HallSylowNormalizer
open scoped Pointwise

private theorem sign_eq_neg_one_of_four_cycle
    {Y : Type} [Fintype Y] [DecidableEq Y]
    (sigma : Equiv.Perm Y) (a b c d : Y)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hsa : sigma a = b) (hsb : sigma b = c)
    (hsc : sigma c = d) (hsd : sigma d = a)
    (hfix : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d →
      sigma x = x) :
    Equiv.Perm.sign sigma = -1 := by
  classical
  let tau : Equiv.Perm Y :=
    Equiv.swap a d * Equiv.swap a c * Equiv.swap a b
  have htauA : tau a = b := by
    simp [tau, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      hab, hab.symm, hac, hac.symm, had, had.symm,
      hbc, hbc.symm, hbd, hbd.symm, hcd, hcd.symm]
  have htauB : tau b = c := by
    simp [tau, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      hab, hab.symm, hac, hac.symm, had, had.symm,
      hbc, hbc.symm, hbd, hbd.symm, hcd, hcd.symm]
  have htauC : tau c = d := by
    simp [tau, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      hab, hab.symm, hac, hac.symm, had, had.symm,
      hbc, hbc.symm, hbd, hbd.symm, hcd, hcd.symm]
  have htauD : tau d = a := by
    simp [tau, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      hab, hab.symm, hac, hac.symm, had, had.symm,
      hbc, hbc.symm, hbd, hbd.symm, hcd, hcd.symm]
  have hsigma : sigma = tau := by
    ext x
    by_cases hxa : x = a
    · subst x
      exact hsa.trans htauA.symm
    by_cases hxb : x = b
    · subst x
      exact hsb.trans htauB.symm
    by_cases hxc : x = c
    · subst x
      exact hsc.trans htauC.symm
    by_cases hxd : x = d
    · subst x
      exact hsd.trans htauD.symm
    rw [hfix x hxa hxb hxc hxd]
    simp [tau, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      hxa, hxb, hxc, hxd]
  rw [hsigma]
  simp only [tau, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap had, Equiv.Perm.sign_swap hac,
    Equiv.Perm.sign_swap hab]
  norm_num

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem false_of_six_fixedSet_and_oriented_quarterTurn
    {ell : ℕ} [Fact ell.Prime]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q : X) (hq : q = a • p) (hpq : p ≠ q)
    (hFa : MulAction.fixedBy X a = {e 0, e 1})
    (hFb : MulAction.fixedBy X b = {p, q})
    (hFc : MulAction.fixedBy X (a * b) = {e 2, e 3})
    (hEcard : (exceptionalSet (X := X) a b).ncard = 6)
    (Q : Sylow ell (MulAction.stabilizer G e))
    (hfixed : MulAction.fixedPoints (ambientSylow e Q) X =
      exceptionalSet (X := X) a b)
    (u : G)
    (hu0 : u • e 0 = e 0) (hu1 : u • e 1 = e 1)
    (hu2 : u • e 2 = q) (huq : u • q = e 3)
    (hu3 : u • e 3 = p) (hup : u • p = e 2) : False := by
  classical
  let A : Subgroup G := ambientSylow e Q
  let F := MulAction.fixedPoints A X
  letI : Fintype F := Fintype.ofFinite F
  have hbp : b • p = p := by
    change p ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  have hbq : b • q = q := by
    change q ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  have hsix : Function.Injective (exceptionalSixMap e p q) :=
    exceptionalSixMap_injective e a b haTwo haBase hbBase p q
      hq.symm hpq hbp hbq
  have he2q : e 2 ≠ q := by
    simpa [exceptionalSixMap] using
      hsix.ne (show (4 : Fin 6) ≠ 1 by decide)
  have he2e3 : e 2 ≠ e 3 := e.injective.ne (by decide)
  have he2p : e 2 ≠ p := by
    simpa [exceptionalSixMap] using
      hsix.ne (show (4 : Fin 6) ≠ 0 by decide)
  have hqe3 : q ≠ e 3 := by
    simpa [exceptionalSixMap] using
      hsix.ne (show (1 : Fin 6) ≠ 5 by decide)
  have hqp : q ≠ p := hpq.symm
  have he3p : e 3 ≠ p := by
    simpa [exceptionalSixMap] using
      hsix.ne (show (5 : Fin 6) ≠ 0 by decide)
  have he2F : e 2 ∈ F := by
    change e 2 ∈ MulAction.fixedPoints (ambientSylow e Q) X
    rw [hfixed]
    right
    rw [hFc]
    simp
  have hqF : q ∈ F := by
    change q ∈ MulAction.fixedPoints (ambientSylow e Q) X
    rw [hfixed]
    left; right
    rw [hFb]
    simp
  have he3F : e 3 ∈ F := by
    change e 3 ∈ MulAction.fixedPoints (ambientSylow e Q) X
    rw [hfixed]
    right
    rw [hFc]
    simp
  have hpF : p ∈ F := by
    change p ∈ MulAction.fixedPoints (ambientSylow e Q) X
    rw [hfixed]
    left; right
    rw [hFb]
    simp
  let x2 : F := ⟨e 2, he2F⟩
  let xq : F := ⟨q, hqF⟩
  let x3 : F := ⟨e 3, he3F⟩
  let xp : F := ⟨p, hpF⟩
  have hx2q : x2 ≠ xq := fun h => he2q (congrArg Subtype.val h)
  have hx2x3 : x2 ≠ x3 := fun h => he2e3 (congrArg Subtype.val h)
  have hx2p : x2 ≠ xp := fun h => he2p (congrArg Subtype.val h)
  have hxqx3 : xq ≠ x3 := fun h => hqe3 (congrArg Subtype.val h)
  have hxqp : xq ≠ xp := fun h => hqp (congrArg Subtype.val h)
  have hx3p : x3 ≠ xp := fun h => he3p (congrArg Subtype.val h)
  let K := MulAction.stabilizer G (F : Set X)
  have huSet : u ∈ K := by
    rw [MulAction.mem_stabilizer_set' (Set.toFinite F)]
    intro x hx
    have hxE : x ∈ exceptionalSet (X := X) a b := by
      rw [← hfixed]
      exact hx
    rcases hxE with (hxa | hxb) | hxc
    · rw [hFa] at hxa
      rcases hxa with rfl | rfl
      · simpa only [hu0] using hx
      · simpa only [hu1] using hx
    · rw [hFb] at hxb
      rcases hxb with rfl | rfl
      · rw [hup]
        exact he2F
      · rw [huq]
        exact he3F
    · rw [hFc] at hxc
      rcases hxc with rfl | rfl
      · rw [hu2]
        exact hqF
      · rw [hu3]
        exact hpF
  let uK : K := ⟨u, huSet⟩
  let sigma : Equiv.Perm F := MulAction.toPermHom K F uK
  have hsigma2 : sigma x2 = xq := by
    apply Subtype.ext
    exact hu2
  have hsigmaq : sigma xq = x3 := by
    apply Subtype.ext
    exact huq
  have hsigma3 : sigma x3 = xp := by
    apply Subtype.ext
    exact hu3
  have hsigmap : sigma xp = x2 := by
    apply Subtype.ext
    exact hup
  have hsigmaFix : ∀ y : F,
      y ≠ x2 → y ≠ xq → y ≠ x3 → y ≠ xp →
      sigma y = y := by
    intro y hy2 hyq hy3 hyp
    apply Subtype.ext
    change u • (y : X) = (y : X)
    have hyE : (y : X) ∈ exceptionalSet (X := X) a b := by
      rw [← hfixed]
      exact y.prop
    rcases hyE with (hya | hyb) | hyc
    · rw [hFa] at hya
      rcases hya with h0 | h1
      · rw [h0, hu0]
      · rw [h1, hu1]
    · rw [hFb] at hyb
      rcases hyb with hp | hq'
      · exact (hyp (Subtype.ext hp)).elim
      · exact (hyq (Subtype.ext hq')).elim
    · rw [hFc] at hyc
      rcases hyc with h2 | h3
      · exact (hy2 (Subtype.ext h2)).elim
      · exact (hy3 (Subtype.ext h3)).elim
  have hsign : Equiv.Perm.sign sigma = -1 :=
    sign_eq_neg_one_of_four_cycle sigma x2 xq x3 xp
      hx2q hx2x3 hx2p hxqx3 hxqp hx3p
      hsigma2 hsigmaq hsigma3 hsigmap hsigmaFix
  have hFcard : Nat.card F = 6 := by
    rw [Nat.card_coe_set_eq]
    change (MulAction.fixedPoints (ambientSylow e Q) X).ncard = 6
    rw [hfixed]
    exact hEcard
  have hpqF : xp ≠ xq := by
    exact fun h => hpq (congrArg Subtype.val h)
  have hpBase : ∀ i, e i ≠ (xp : X) := by
    intro i
    fin_cases i
    · simpa [exceptionalSixMap] using
        hsix.ne (show (2 : Fin 6) ≠ 0 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (3 : Fin 6) ≠ 0 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (4 : Fin 6) ≠ 0 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (5 : Fin 6) ≠ 0 by decide)
  have hqBase : ∀ i, e i ≠ (xq : X) := by
    intro i
    fin_cases i
    · simpa [exceptionalSixMap] using
        hsix.ne (show (2 : Fin 6) ≠ 1 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (3 : Fin 6) ≠ 1 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (4 : Fin 6) ≠ 1 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (5 : Fin 6) ≠ 1 by decide)
  exact false_of_ambientSylow_fixed_card_six_and_odd_setwise_lift
    h4 e Q hodd hFcard uK hsign xp xq hpqF hpBase hqBase

theorem false_of_seven_fixedSet_and_oriented_quarterTurn
    {ell : ℕ} [Fact ell.Prime]
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q r : X) (hq : q = a • p) (hpq : p ≠ q)
    (hFa : MulAction.fixedBy X a = {e 0, e 1, r})
    (hFb : MulAction.fixedBy X b = {p, q, r})
    (hFc : MulAction.fixedBy X (a * b) = {e 2, e 3, r})
    (_hD : MulAction.fixedBy X a ∩ MulAction.fixedBy X b = {r})
    (hEcard : (exceptionalSet (X := X) a b).ncard = 7)
    (Q : Sylow ell (MulAction.stabilizer G e))
    (hfixed : MulAction.fixedPoints (ambientSylow e Q) X =
      exceptionalSet (X := X) a b)
    (u : G)
    (hu0 : u • e 0 = e 0) (hu1 : u • e 1 = e 1)
    (hur : u • r = r)
    (hu2 : u • e 2 = q) (huq : u • q = e 3)
    (hu3 : u • e 3 = p) (hup : u • p = e 2) : False := by
  classical
  let A : Subgroup G := ambientSylow e Q
  let F := MulAction.fixedPoints A X
  letI : Fintype F := Fintype.ofFinite F
  have hbp : b • p = p := by
    change p ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  have hbq : b • q = q := by
    change q ∈ MulAction.fixedBy X b
    rw [hFb]
    simp
  have hsix : Function.Injective (exceptionalSixMap e p q) :=
    exceptionalSixMap_injective e a b haTwo haBase hbBase p q
      hq.symm hpq hbp hbq
  have he2q : e 2 ≠ q := by
    simpa [exceptionalSixMap] using
      hsix.ne (show (4 : Fin 6) ≠ 1 by decide)
  have he2e3 : e 2 ≠ e 3 := e.injective.ne (by decide)
  have he2p : e 2 ≠ p := by
    simpa [exceptionalSixMap] using
      hsix.ne (show (4 : Fin 6) ≠ 0 by decide)
  have hqe3 : q ≠ e 3 := by
    simpa [exceptionalSixMap] using
      hsix.ne (show (1 : Fin 6) ≠ 5 by decide)
  have hqp : q ≠ p := hpq.symm
  have he3p : e 3 ≠ p := by
    simpa [exceptionalSixMap] using
      hsix.ne (show (5 : Fin 6) ≠ 0 by decide)
  have he2F : e 2 ∈ F := by
    change e 2 ∈ MulAction.fixedPoints (ambientSylow e Q) X
    rw [hfixed]
    right
    rw [hFc]
    simp
  have hqF : q ∈ F := by
    change q ∈ MulAction.fixedPoints (ambientSylow e Q) X
    rw [hfixed]
    left; right
    rw [hFb]
    simp
  have he3F : e 3 ∈ F := by
    change e 3 ∈ MulAction.fixedPoints (ambientSylow e Q) X
    rw [hfixed]
    right
    rw [hFc]
    simp
  have hpF : p ∈ F := by
    change p ∈ MulAction.fixedPoints (ambientSylow e Q) X
    rw [hfixed]
    left; right
    rw [hFb]
    simp
  let x2 : F := ⟨e 2, he2F⟩
  let xq : F := ⟨q, hqF⟩
  let x3 : F := ⟨e 3, he3F⟩
  let xp : F := ⟨p, hpF⟩
  have hx2q : x2 ≠ xq := fun h => he2q (congrArg Subtype.val h)
  have hx2x3 : x2 ≠ x3 := fun h => he2e3 (congrArg Subtype.val h)
  have hx2p : x2 ≠ xp := fun h => he2p (congrArg Subtype.val h)
  have hxqx3 : xq ≠ x3 := fun h => hqe3 (congrArg Subtype.val h)
  have hxqp : xq ≠ xp := fun h => hqp (congrArg Subtype.val h)
  have hx3p : x3 ≠ xp := fun h => he3p (congrArg Subtype.val h)
  let K := MulAction.stabilizer G (F : Set X)
  have huSet : u ∈ K := by
    rw [MulAction.mem_stabilizer_set' (Set.toFinite F)]
    intro x hx
    have hxE : x ∈ exceptionalSet (X := X) a b := by
      rw [← hfixed]
      exact hx
    rcases hxE with (hxa | hxb) | hxc
    · rw [hFa] at hxa
      rcases hxa with rfl | rfl | rfl
      · simpa only [hu0] using hx
      · simpa only [hu1] using hx
      · simpa only [hur] using hx
    · rw [hFb] at hxb
      rcases hxb with rfl | rfl | rfl
      · rw [hup]
        exact he2F
      · rw [huq]
        exact he3F
      · simpa only [hur] using hx
    · rw [hFc] at hxc
      rcases hxc with rfl | rfl | rfl
      · rw [hu2]
        exact hqF
      · rw [hu3]
        exact hpF
      · simpa only [hur] using hx
  let uK : K := ⟨u, huSet⟩
  let sigma : Equiv.Perm F := MulAction.toPermHom K F uK
  have hsigma2 : sigma x2 = xq := by
    apply Subtype.ext
    exact hu2
  have hsigmaq : sigma xq = x3 := by
    apply Subtype.ext
    exact huq
  have hsigma3 : sigma x3 = xp := by
    apply Subtype.ext
    exact hu3
  have hsigmap : sigma xp = x2 := by
    apply Subtype.ext
    exact hup
  have hsigmaFix : ∀ y : F,
      y ≠ x2 → y ≠ xq → y ≠ x3 → y ≠ xp →
      sigma y = y := by
    intro y hy2 hyq hy3 hyp
    apply Subtype.ext
    change u • (y : X) = (y : X)
    have hyE : (y : X) ∈ exceptionalSet (X := X) a b := by
      rw [← hfixed]
      exact y.prop
    rcases hyE with (hya | hyb) | hyc
    · rw [hFa] at hya
      rcases hya with h0 | h1 | hr
      · rw [h0, hu0]
      · rw [h1, hu1]
      · rw [hr, hur]
    · rw [hFb] at hyb
      rcases hyb with hp | hq' | hr
      · exact (hyp (Subtype.ext hp)).elim
      · exact (hyq (Subtype.ext hq')).elim
      · rw [hr, hur]
    · rw [hFc] at hyc
      rcases hyc with h2 | h3 | hr
      · exact (hy2 (Subtype.ext h2)).elim
      · exact (hy3 (Subtype.ext h3)).elim
      · rw [hr, hur]
  have hsign : Equiv.Perm.sign sigma = -1 :=
    sign_eq_neg_one_of_four_cycle sigma x2 xq x3 xp
      hx2q hx2x3 hx2p hxqx3 hxqp hx3p
      hsigma2 hsigmaq hsigma3 hsigmap hsigmaFix
  have hFcard : Nat.card F = 7 := by
    rw [Nat.card_coe_set_eq]
    change (MulAction.fixedPoints (ambientSylow e Q) X).ncard = 7
    rw [hfixed]
    exact hEcard
  have hpqF : xp ≠ xq := by
    exact fun h => hpq (congrArg Subtype.val h)
  have hpBase : ∀ i, e i ≠ (xp : X) := by
    intro i
    fin_cases i
    · simpa [exceptionalSixMap] using
        hsix.ne (show (2 : Fin 6) ≠ 0 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (3 : Fin 6) ≠ 0 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (4 : Fin 6) ≠ 0 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (5 : Fin 6) ≠ 0 by decide)
  have hqBase : ∀ i, e i ≠ (xq : X) := by
    intro i
    fin_cases i
    · simpa [exceptionalSixMap] using
        hsix.ne (show (2 : Fin 6) ≠ 1 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (3 : Fin 6) ≠ 1 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (4 : Fin 6) ≠ 1 by decide)
    · simpa [exceptionalSixMap] using
        hsix.ne (show (5 : Fin 6) ≠ 1 by decide)
  exact false_of_ambientSylow_fixed_card_seven_and_odd_setwise_lift
    h4 e Q hodd hFcard uK hsign xp xq hpqF hpBase hqBase

end FiveTransitive.Research.HallParityFromOriented

end CFSG
