module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeCardSubgroupIntersection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: subgroups of order `p²` in a group of order `p³`

This module lands the equation-(8) cubic counting core used by the linear
branch (`refs/bender-dihedral-sylow.tex`, lines 708--735): in a finite
group `Q` of order `p³` whose centre has order `p` and whose exponent is
`p`, the number of subgroups of order `p²` is exactly `p + 1`.

The proof reduces the count to the quotient `Q / Z(Q)`, which has order
`p²` and exponent `p`, where the number of subgroups of order `p` is
`p + 1` (`order_p_subgroups_card_of_order_p_sq_exponent_p` from
`SecondCaseLinearEquationEightDefs`); the correspondence is via
`comap`/`map` by the canonical quotient, using the fact that every
order-`p²` subgroup contains the centre.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- In a finite group of order `p^3` with center of order `p` and exponent
`p`, the number of subgroups of order `p^2` is `p + 1`. -/
public theorem order_p_sq_subgroups_card_of_order_p_cube
    {Q : Type u} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card Q = p ^ 3) (hZcard : Nat.card (Subgroup.center Q) = p)
    (hexp : Monoid.exponent Q = p) :
    Nat.card {X : Subgroup Q // Nat.card X = p ^ 2} = p + 1 := by
  classical
  let Z : Subgroup Q := Subgroup.center Q
  let q : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  have hZle : ∀ X : Subgroup Q, Nat.card X = p ^ 2 → Z ≤ X := by
    intro X hX
    by_contra hZX
    rcases Set.not_subset.mp hZX with ⟨z, hzZ, hzX⟩
    let Zp : Subgroup Q := Subgroup.zpowers z
    have hzpow : z ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [hexp]) z
    have hzord : orderOf z = p := orderOf_eq_prime (x := z) (p := p) hzpow (by
      intro hz1
      exact hzX (by simpa [hz1] using X.one_mem))
    have hZpcard : Nat.card Zp = p := by
      dsimp [Zp]
      rw [Nat.card_zpowers]
      exact hzord
    have hnotZp : ¬ Zp ≤ X := by
      intro hle
      exact hzX (hle (Subgroup.mem_zpowers z))
    have hpZp : (Nat.card Zp).Prime := by
      rw [hZpcard]
      exact (Fact.out : p.Prime)
    have hcap : X ⊓ Zp = ⊥ :=
      inf_eq_bot_of_not_le_of_prime_card X Zp hpZp hnotZp
    have hzcent : z ∈ Subgroup.centralizer (X : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_center_iff.mp hzZ x
    have hnorm : Zp ≤ Subgroup.normalizer (X : Set Q) := by
      apply Subgroup.zpowers_le.mpr
      exact (Subgroup.centralizer_le_normalizer (X : Set Q)) hzcent
    have hsupcard : Nat.card (X ⊔ Zp : Subgroup Q) = p ^ 3 := by
      rw [card_sup_eq_mul_of_disjoint_of_le_normalizer X Zp hnorm
        (disjoint_iff.mpr hcap), hX, hZpcard]
      simp [pow_succ, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have hsuptop : X ⊔ Zp = (⊤ : Subgroup Q) := by
      have hcard_le : Nat.card (⊤ : Subgroup Q) ≤
          Nat.card (X ⊔ Zp : Subgroup Q) := by
        rw [Subgroup.card_top, hcard]
        exact le_of_eq hsupcard.symm
      exact Subgroup.eq_of_le_of_card_ge le_top hcard_le
    have hZpcenter : Zp ≤ Subgroup.center Q := by
      apply Subgroup.zpowers_le.mpr
      exact hzZ
    have hXab : IsMulCommutative (↥X) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hX
    have hXcomm : ∀ x y : Q, x ∈ X → y ∈ X → x * y = y * x := by
      intro x y hx hy
      exact congrArg Subtype.val (hXab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hcommQ : ∀ x y : Q, x * y = y * x := by
      intro a b
      have haSup : a ∈ (X ⊔ Zp : Subgroup Q) := by
        rw [hsuptop]
        trivial
      have hbSup : b ∈ (X ⊔ Zp : Subgroup Q) := by
        rw [hsuptop]
        trivial
      have hset : ((X ⊔ Zp : Subgroup Q) : Set Q) = (X : Set Q) * (Zp : Set Q) :=
        Subgroup.coe_mul_of_right_le_normalizer_left X Zp hnorm
      change a ∈ ((X ⊔ Zp : Subgroup Q) : Set Q) at haSup
      change b ∈ ((X ⊔ Zp : Subgroup Q) : Set Q) at hbSup
      rw [hset] at haSup hbSup
      rcases Set.mem_mul.mp haSup with ⟨x, hx, z1, hz1, hxa⟩
      rcases Set.mem_mul.mp hbSup with ⟨y, hy, z2, hz2, hxb⟩
      have hz1y : z1 * y = y * z1 :=
        (Subgroup.mem_center_iff.mp (hZpcenter hz1) y).symm
      have hz2x : z2 * x = x * z2 :=
        (Subgroup.mem_center_iff.mp (hZpcenter hz2) x).symm
      have hz1z2 : z1 * z2 = z2 * z1 :=
        (Subgroup.mem_center_iff.mp (hZpcenter hz1) z2).symm
      rw [← hxa, ← hxb]
      calc
        (x * z1) * (y * z2) = x * (z1 * y) * z2 := by group
        _ = x * (y * z1) * z2 := by rw [hz1y]
        _ = x * y * z1 * z2 := by group
        _ = y * x * z1 * z2 := by rw [hXcomm x y hx hy]
        _ = y * x * (z1 * z2) := by group
        _ = y * x * (z2 * z1) := by rw [hz1z2]
        _ = y * (x * z2) * z1 := by group
        _ = y * (z2 * x) * z1 := by rw [hz2x]
        _ = (y * z2) * (x * z1) := by group
    have hcomm : IsMulCommutative Q := ⟨⟨hcommQ⟩⟩
    have hZtop : Z = (⊤ : Subgroup Q) := by
      dsimp [Z]
      exact Subgroup.center_eq_top_iff.mpr hcomm
    have hZcard' : Nat.card Z = p := by simpa [Z] using hZcard
    rw [hZtop, Subgroup.card_top, hcard] at hZcard'
    have hpbase : 1 < p := (Fact.out : p.Prime).one_lt
    have hp3 : p < p ^ 3 := by
      simpa using (Nat.pow_lt_pow_right hpbase (by norm_num : 1 < 3))
    omega
  have hquotcard : Nat.card (Q ⧸ Z) = p ^ 2 := by
    have hfac := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have hZcard' : Nat.card Z = p := by simpa [Z] using hZcard
    rw [hcard, hZcard'] at hfac
    have hfac' : p * p ^ 2 = p * Nat.card (Q ⧸ Z) := by
      simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hfac
    exact (Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos hfac').symm
  have hquotexp : Monoid.exponent (Q ⧸ Z) = p := by
    have hquotnontriv : Nontrivial (Q ⧸ Z) := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      have hpbase : 1 < p := (Fact.out : p.Prime).one_lt
      have hp2 : 1 < p ^ 2 := one_lt_pow₀ hpbase (by norm_num : 2 ≠ 0)
      simpa only [hquotcard] using hp2
    letI : Nontrivial (Q ⧸ Z) := hquotnontriv
    have hdiv : Monoid.exponent (Q ⧸ Z) ∣ p := by
      simpa only [hexp] using (Group.exponent_quotient_dvd Z)
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with h1 | hp
    · exfalso
      exact (not_subsingleton (Q ⧸ Z)) (Monoid.exp_eq_one_iff.mp h1)
    · exact hp
  let S2 : Type u := {X : Subgroup Q // Nat.card X = p ^ 2}
  let S1 : Type u := {Y : Subgroup (Q ⧸ Z) // Nat.card Y = p}
  let f : S2 → S1 := fun X => by
    let Y : Subgroup (Q ⧸ Z) := X.1.map q
    have hker : q.ker = Z := by simpa [q] using QuotientGroup.ker_mk' Z
    have hmapcard := card_map_eq_card_mul_card_ker q X.1
    have hcapZ : X.1 ⊓ q.ker = Z := by
      rw [hker]
      exact le_antisymm inf_le_right (le_inf (hZle X.1 X.2) le_rfl)
    have hYcard : Nat.card Y = p := by
      have hZcard' : Nat.card Z = p := by simpa [Z] using hZcard
      have hcardXY : Nat.card X.1 = Nat.card Y * Nat.card Z := by
        simpa [Y, hcapZ] using hmapcard
      have hcardXY' : p ^ 2 = Nat.card Y * p := by
        simpa [X.2, hZcard'] using hcardXY
      have hcancel : Nat.card Y * p = p * p := by
        simpa [pow_two, Nat.mul_comm] using hcardXY'.symm
      exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos hcancel
    exact ⟨Y, hYcard⟩
  let g : S1 → S2 := fun Y => by
    let X : Subgroup Q := Y.1.comap q
    have hker : q.ker = Z := by simpa [q] using QuotientGroup.ker_mk' Z
    have hmap : X.map q = Y.1 := by
      dsimp [X]
      exact Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective Z) Y.1
    have hcap : X ⊓ q.ker = Z := by
      rw [hker]
      exact le_antisymm inf_le_right
        (le_inf (QuotientGroup.le_comap_mk' Z Y.1) le_rfl)
    have hmapcard := card_map_eq_card_mul_card_ker q X
    have hXcard : Nat.card X = p ^ 2 := by
      rw [hmap, hcap] at hmapcard
      have hZcard' : Nat.card Z = p := by simpa [Z] using hZcard
      have hcardX' : Nat.card X = Nat.card Y.1 * p := by
        simpa [hZcard'] using hmapcard
      have hcancel : Nat.card X = p * p := by
        simpa [Y.2, pow_two, Nat.mul_comm] using hcardX'
      exact hcancel.trans (by rw [pow_two])
    exact ⟨X, hXcard⟩
  have hfg : Function.LeftInverse g f := by
    intro X
    apply Subtype.ext
    dsimp [g, f]
    have hker : q.ker = Z := by simpa [q] using QuotientGroup.ker_mk' Z
    rw [Subgroup.comap_map_eq, hker]
    exact sup_eq_left.mpr (hZle X.1 X.2)
  have hgf : Function.RightInverse g f := by
    intro Y
    apply Subtype.ext
    dsimp [g, f]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective Z) Y.1
  have hS2S1 : Nat.card S2 = Nat.card S1 :=
    Nat.card_congr (Equiv.ofBijective f ⟨hfg.injective, hgf.surjective⟩)
  have hS1card : Nat.card S1 = p + 1 := by
    dsimp [S1]
    exact order_p_subgroups_card_of_order_p_sq_exponent_p hquotcard hquotexp
  change Nat.card S2 = p + 1
  rw [hS2S1, hS1card]

end CFSG.GorensteinWalter
