module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

private lemma w135c2_lend_injective_of_ne_zero (hirr : IsIrrOn L ⊤ ⊥)
    {a : ↥(LEnd L)} (ha : a ≠ 0) : Function.Injective a.1 := by
  classical
  let K : Subgroup W :=
    { carrier := {w : W | a.1 (Additive.ofMul w) = 0}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [ofMul_mul, map_add, hx, hy, add_zero]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [ofMul_inv, map_neg, hx, neg_zero] }
  have hstable : StableUnder L K := by
    intro g hg w hw
    have hw' : a.1 (Additive.ofMul w) = 0 := hw
    change a.1 (Additive.ofMul (g (Additive.toMul (Additive.ofMul w)))) = 0
    rw [a.2 g hg (Additive.ofMul w), hw']
    simp
  rcases hirr.2.2.2 K hstable bot_le le_top with hK | hK
  · intro x y hxy
    have hz : a.1 (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hmem : (x - y).toMul ∈ K := hz
    rw [hK, Subgroup.mem_bot] at hmem
    have h0 : x - y = 0 := by
      rw [← ofMul_toMul (x - y), hmem, ofMul_one]
    exact sub_eq_zero.mp h0
  · exfalso
    apply ha
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    have hmem : x.toMul ∈ K := by rw [hK]; exact Subgroup.mem_top _
    have hx0 : a.1 (Additive.ofMul x.toMul) = 0 := hmem
    change a.1 x = 0
    simpa using hx0

theorem w135c2_lend_isField (hW : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn L ⊤ ⊥) :
    IsField ↥(LEnd L) := by
  classical
  haveI hnt : Nontrivial ↥(LEnd L) := by
    refine ⟨1, 0, ?_⟩
    intro h
    have h1 : ((1 : ↥(LEnd L)) : AddMonoid.End (Additive W)) =
        ((0 : ↥(LEnd L)) : AddMonoid.End (Additive W)) := congrArg Subtype.val h
    have htop : (⊤ : Subgroup W) = ⊥ := by
      rw [eq_bot_iff]
      intro w _
      have hw : (Additive.ofMul w : Additive W) = 0 := by
        have := congrArg (fun f : AddMonoid.End (Additive W) => f (Additive.ofMul w)) h1
        simpa using this
      exact ofMul_eq_zero.mp hw
    exact absurd htop (ne_of_gt hirr.1)
  haveI hnoz : NoZeroDivisors ↥(LEnd L) :=
    ⟨fun {a b} hab => by
      by_cases ha : a = 0
      · exact Or.inl ha
      · refine Or.inr (Subtype.ext ?_)
        have hinj := w135c2_lend_injective_of_ne_zero hirr ha
        have hab' : a.1 * b.1 = 0 := by
          have h := congrArg Subtype.val hab
          simpa using h
        apply AddMonoidHom.ext
        intro x
        change b.1 x = 0
        exact hinj (by
          have h := congrArg (fun φ : AddMonoid.End (Additive W) => φ x) hab'
          simpa using h)⟩
  haveI : IsDomain ↥(LEnd L) := NoZeroDivisors.to_isDomain _
  haveI : Finite ↥(LEnd L) := by
    haveI : Finite (AddMonoid.End (Additive W)) := DFunLike.finite _
    infer_instance
  exact Finite.isDomain_to_isField ↥(LEnd L)

end CFSG.LocalAnalysis.WeakClosure81
