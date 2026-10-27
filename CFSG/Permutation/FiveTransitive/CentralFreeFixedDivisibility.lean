module

public import CFSG.Permutation.FiveTransitive.NormalizerFixedComplement

public section

namespace CFSG

namespace FiveTransitive.CentralFreeFixedDivisibility

open MulAction

theorem fixed_dvd
    {G Y : Type*} [Group G] [Finite G] [Finite Y] [MulAction G Y]
    (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1)
    (f : Y → Y) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y) :
    Nat.card G ∣ Nat.card (Function.fixedPoints f) := by
  let F : SubMulAction G Y :=
    { carrier := Function.fixedPoints f
      smul_mem' g y hy := by change f (g • y) = g • y; rw [heq, hy] }
  have hfreeF : ∀ (g : G) (y : F), g • y = y → g = 1 := by
    intro g y hg
    exact hfree g y.val (congrArg Subtype.val hg)
  change Nat.card G ∣ Nat.card F
  rw [FreeComplementOrbitCount.card_eq_mul_orbits hfreeF]
  exact dvd_mul_right _ _

theorem complementary_fixed_dvd
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (n : NormalizerFixedComplement.Normalizer Q)
    (hcomm : ∀ q : Q, Commute q.val n.val) :
    Nat.card Q ∣ (fixedBy X n.val \ fixedPoints Q X).ncard := by
  let I := NormalizerFixedComplement.Inside Q
  let D := NormalizerFixedComplement.Domain (X := X) Q
  have h := fixed_dvd (NormalizerFixedComplement.free_inside Q hfree)
    (fun z : D => n • z) (by
      intro q z
      apply Subtype.ext
      change n.val • (q.val.val • z.val) = q.val.val • (n.val • z.val)
      rw [← mul_smul, ← (hcomm ⟨q.val.val, q.property⟩).eq, mul_smul])
  have hcard : Nat.card I = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv
  change Nat.card I ∣ Nat.card (fixedBy D n) at h
  rw [hcard, NormalizerFixedComplement.fixed_card] at h
  exact h

end FiveTransitive.CentralFreeFixedDivisibility

end CFSG
