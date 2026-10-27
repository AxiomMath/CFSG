module

public import CFSG.Permutation.FiveTransitive.TwoFixedCentralizer
public import CFSG.Permutation.FiveTransitive.NormalizerEvenCoset

public section

namespace CFSG

namespace FiveTransitive.NormalizerEvenCentralizerTwo

open MulAction NormalizerFixedComplement

theorem actual_coset
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hfree : ∀ (r : Q) (z : X), z ∉ fixedPoints Q X → r • z = z → r = 1)
    (x : Normalizer Q)
    (hlocal : (fixedBy X (x : G) ∩ fixedPoints Q X).ncard = 5)
    (q : Inside Q) (hqx : orderOf ((q : Normalizer Q) * x) = 2) :
    let n := (q : Normalizer Q) * x
    Nat.card ((Subgroup.centralizer ({(n : G)} : Set G)).subgroupOf Q) = 2 ∧
      Nat.card (fixedBy (Domain (X := X) Q) n) = 2 ∧
      ∀ z : Domain (X := X) Q, n • z = z →
        Nat.card {w : Domain (X := X) Q // w ∈ orbit (Inside Q) z ∧ n • w = w} = 2 ∧
        ∀ w : Domain (X := X) Q, n • w = w → w ∈ orbit (Inside Q) z := by
  let n := (q : Normalizer Q) * x
  let _ : (Inside Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  let _ : Nontrivial Q := Q.nontrivial_iff_ne_bot.mpr hne
  let eQ : Inside Q ≃* Q := Subgroup.subgroupOfEquivOfLe Q.le_normalizer
  let _ : Nontrivial (Inside Q) := eQ.toEquiv.nontrivial
  let action : MulAction (Inside Q) (Domain (X := X) Q) :=
    MulAction.compHom (Domain (X := X) Q) (Inside Q).subtype
  let f : MulAut (Inside Q) := MulAut.conjNormal n
  have hn2 : n ^ 2 = 1 := hqx ▸ pow_orderOf_eq_one n
  have hf2 : f ^ 2 = 1 := by
    change (MulAut.conjNormal n) ^ 2 = 1
    rw [←map_pow, hn2, map_one]
  have hf : Function.Involutive f := by
    intro r
    exact congrArg (fun u : MulAut (Inside Q) => u r) hf2
  have hcompat : ∀ r : Inside Q, ∀ y : Domain (X := X) Q,
      n • (r • y) = f r • (n • y) := by
    intro r y
    change n • ((r : Normalizer Q) • y) = ((f r : Inside Q) : Normalizer Q) • (n • y)
    rw [MulAut.conjNormal_apply]
    simp only [mul_smul, inv_smul_smul]
  have htwo := NormalizerEvenCoset.fixed_card_eq_two heven hdegree hmax Q x hlocal q hqx
  obtain ⟨hcard, horbits⟩ := @TwoFixedCentralizer.fixed_card_two
    (Inside Q) (Domain (X := X) Q) _ _ _ _ action hQ.comap_subtype f hf (fun z => n • z) hcompat
    (NormalizerFixedComplement.free_inside Q hfree) htwo
  have hfixed (r : Inside Q) : f r = r ↔
      r.val.val ∈ Subgroup.centralizer ({(n : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hr
      have hh := congrArg (fun u : Inside Q => u.val.val) hr
      change (n : G) * r.val.val * (n : G)⁻¹ = r.val.val at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hr
      apply Subtype.ext
      apply Subtype.ext
      change (n : G) * r.val.val * (n : G)⁻¹ = r.val.val
      rw [←hr, mul_assoc, mul_inv_cancel, mul_one]
  let E : {r : Inside Q // f r = r} ≃
      (Subgroup.centralizer ({(n : G)} : Set G)).subgroupOf Q :=
    { toFun := fun r => ⟨⟨r.val.val.val, r.val.property⟩, (hfixed r.val).mp r.property⟩
      invFun := fun r => ⟨eQ.symm r.val, (hfixed (eQ.symm r.val)).mpr r.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨(Nat.card_congr E).symm.trans hcard, htwo, horbits⟩

end FiveTransitive.NormalizerEvenCentralizerTwo

end CFSG
