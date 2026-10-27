module

public import CFSG.Permutation.FiveTransitive.OddIndexTwoConjugacy

public section

namespace CFSG

namespace FiveTransitive.OddKernelEqualImageConjugacy

theorem exists_ker_conjugator
    {G A : Type*} [Group G] [Finite G] [Group A]
    (f : G →* A) (hodd : Odd (Nat.card f.ker))
    (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : f a = f b) (hfb : f b ≠ 1) :
    ∃ k : G, k ∈ f.ker ∧ k * a * k⁻¹ = b := by
  let Z := Subgroup.zpowers (f b)
  let L := Z.comap f
  let phi : L →* Z :=
    { toFun := fun x => ⟨f x, x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun _ _ => Subtype.ext (map_mul f _ _) }
  have hsur : Function.Surjective phi := by
    intro z
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp z.property
    have hm : b ^ n ∈ L := by
      change f (b ^ n) ∈ Z
      rw [map_zpow, hn]
      exact z.property
    exact ⟨⟨b ^ n, hm⟩, Subtype.ext (by change f (b ^ n) = z.val; rw [map_zpow, hn])⟩
  have hkcard : Nat.card phi.ker = Nat.card f.ker := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
        invFun := fun x => ⟨⟨x.val, by
          change f x.val ∈ Z
          rw [show f x.val = 1 from x.property]
          exact Z.one_mem⟩, Subtype.ext x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hZ : Nat.card Z = 2 := by
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime _ hfb
    rw [← map_pow, hb, map_one]
  let aL : L := ⟨a, by change f a ∈ Z; rw [hab]; exact Subgroup.mem_zpowers _⟩
  let bL : L := ⟨b, Subgroup.mem_zpowers _⟩
  obtain ⟨k, hk, heq⟩ := Research.OddIndexTwoConjugacy.exists_ker_conjugator_of_odd_kernel_card_two
    phi hsur (hkcard.symm ▸ hodd) hZ
    (u := aL) (v := bL) (Subtype.ext ha) (Subtype.ext hb)
    (by intro h; apply hfb; rw [← hab, show a = 1 from congrArg Subtype.val h, map_one])
    (by intro h; apply hfb; rw [show b = 1 from congrArg Subtype.val h, map_one])
    (by intro h; exact hfb (congrArg Subtype.val h))
  exact ⟨k.val, congrArg Subtype.val hk, congrArg Subtype.val heq⟩

end FiveTransitive.OddKernelEqualImageConjugacy

end CFSG
