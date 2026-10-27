module

public import CFSG.Permutation.FiveTransitive.SmallTwoGroupFiveElementaryAction
public import Mathlib.GroupTheory.GroupAction.Blocks

public section

namespace CFSG

namespace FiveTransitive.Degree28SmallTwoFiveOrbit

open MulAction

theorem exterior_fixed_subsingleton
    {A Q X : Type*} [Group A] [Group Q] [Finite Q] [Finite X]
    [MulDistribMulAction A Q] [MulAction A X] [MulAction Q X]
    (hA : IsPGroup 5 A) (hQ : IsPGroup 2 Q) (hcard : Nat.card Q ≤ 16)
    (hmove : ∃ a : A, ∃ q : Q, a • q ≠ q)
    (hcompat : ∀ (a : A) (q : Q) (x : X), a • (q • x) = (a • q) • (a • x))
    (hX : Nat.card X < 32) :
    (fixedPoints A X \ fixedPoints Q X).Subsingleton := by
  classical
  have h16 := TwoGroupFiveAutomorphism.card_eq_sixteen_of_nontrivial_action
    A Q hA hQ hcard hmove
  have hfree (x : X) (hxA : x ∈ fixedPoints A X) (hxQ : x ∉ fixedPoints Q X)
      (q : Q) (hqx : q • x = x) : q = 1 := by
    have hbot : stabilizer Q x = ⊥ := by
      by_contra hn
      have htop := SmallTwoGroupFiveElementaryAction.invariant_eq_top hA hQ hcard hmove
        (stabilizer Q x) hn (by
          intro a r hr
          change (a • r) • x = x
          change r • x = x at hr
          have hh := hcompat a r x
          rw [hxA a,hr,hxA a] at hh
          exact hh.symm)
      apply hxQ
      intro r
      exact (show r ∈ stabilizer Q x from htop ▸ Subgroup.mem_top r)
    have hmem : q ∈ stabilizer Q x := hqx
    rwa [hbot,Subgroup.mem_bot] at hmem
  have horbit (x : X) (hxA : x ∈ fixedPoints A X) (hxQ : x ∉ fixedPoints Q X) :
      (orbit Q x).ncard = 16 := by
    let f : Q → orbit Q x := fun q => ⟨q • x,mem_orbit_iff.mpr ⟨q,rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro q r h
        have hh : q • x = r • x := congrArg Subtype.val h
        have he : (r⁻¹ * q) • x = x := by rw [mul_smul,hh,inv_smul_smul]
        exact (inv_mul_eq_one.mp (hfree x hxA hxQ _ he)).symm
      · rintro ⟨y,hy⟩
        obtain ⟨q,hq⟩ := mem_orbit_iff.mp hy
        exact ⟨q,Subtype.ext hq⟩
    rw [← Nat.card_coe_set_eq,← Nat.card_congr (Equiv.ofBijective f hf),h16]
  intro x hx y hy
  by_contra hxy
  have hdis : Disjoint (orbit Q x) (orbit Q y) := by
    rcases orbit.eq_or_disjoint (G := Q) x y with he | hd
    · exfalso
      have hym : y ∈ orbit Q x := he.symm ▸ mem_orbit_self y
      obtain ⟨q,hq⟩ := mem_orbit_iff.mp hym
      have hqfixed : ∀ a : A, a • q = q := by
        intro a
        have hh : (a • q) • x = q • x := by
          calc
            (a • q) • x = (a • q) • (a • x) := by rw [hx.1 a]
            _ = a • (q • x) := (hcompat a q x).symm
            _ = q • x := by rw [hq,hy.1 a]
        have hi : (q⁻¹ * (a • q)) • x = x := by rw [mul_smul,hh,inv_smul_smul]
        exact (inv_mul_eq_one.mp (hfree x hx.1 hx.2 _ hi)).symm
      have hqone := SmallTwoGroupFiveElementaryAction.fixed_eq_one hA hQ hcard hmove q hqfixed
      apply hxy
      simpa only [hqone,one_smul] using hq
    · exact hd
  have hle := Set.ncard_le_ncard (Set.subset_univ (orbit Q x ∪ orbit Q y))
  rw [Set.ncard_union_eq hdis,horbit x hx.1 hx.2,horbit y hy.1 hy.2,Set.ncard_univ] at hle
  omega

end FiveTransitive.Degree28SmallTwoFiveOrbit

end CFSG
