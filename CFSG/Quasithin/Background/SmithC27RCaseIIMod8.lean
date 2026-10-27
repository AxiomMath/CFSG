module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimPerm
public import CFSG.Quasithin.Background.B5FinS8Schur
public import CFSG.Quasithin.Background.C124YZModel

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.QuasithinUnique Equiv Equiv.Perm

private theorem v8g1_mem_V8 : Claim2526.v8g1 ∈ Claim2526.V8 :=
  Subgroup.subset_closure (List.mem_cons_self ..)

private theorem zmod2_eq_of_add_eq_zero : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide

private theorem zmod2_add_self_ne_one : ∀ a : ZMod 2, a + a ≠ 1 := by decide

private theorem permAct_swap01_of_eq {x : G6.PermMod 8}
    (h : Multiplicative.toAdd x 0 = Multiplicative.toAdd x 1) :
    G6.permAct 8 (swap 0 1) x = x := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply, swap_inv]
  rcases eq_or_ne i 0 with rfl | h0
  · rw [swap_apply_left]
    exact h.symm
  rcases eq_or_ne i 1 with rfl | h1
  · rw [swap_apply_right]
    exact h
  rw [swap_apply_of_ne_of_ne h0 h1]

private theorem toAdd_eq_of_v8g1 {x : G6.PermMod 8} (h : G6.permAct 8 Claim2526.v8g1 x = x) :
    Multiplicative.toAdd x 0 = Multiplicative.toAdd x 1 := by
  have h1 := congrFun (congrArg Multiplicative.toAdd h) 1
  rw [G6.permAct_apply, show Claim2526.v8g1⁻¹ 1 = 0 by decide] at h1
  exact h1

theorem coreAct_swap01_of_fix_V8 (x : ↥(G6.coreMod 8))
    (hx : ∀ g ∈ Claim2526.V8, G6.coreAct 8 g x = x) : G6.coreAct 8 (swap 0 1) x = x :=
  Subtype.ext (permAct_swap01_of_eq (toAdd_eq_of_v8g1 (congrArg Subtype.val
    (hx _ v8g1_mem_V8))))

theorem dAct_swap01_of_fix_V8 (x : C124.YZ.DM 8)
    (hx : ∀ g ∈ Claim2526.V8, C124.YZ.dAct 8 g x = x) : C124.YZ.dAct 8 (swap 0 1) x = x := by
  obtain ⟨m, rfl⟩ : ∃ m : ↥(G6.coreMod 8), (QuotientGroup.mk m : B5FinS8.Mod8) = x :=
    QuotientGroup.mk_surjective x
  have h : (QuotientGroup.mk (G6.coreAct 8 Claim2526.v8g1 m) : B5FinS8.Mod8) =
      QuotientGroup.mk m := hx _ v8g1_mem_V8
  have h0 : Multiplicative.toAdd (m : G6.PermMod 8) 0 =
      Multiplicative.toAdd (m : G6.PermMod 8) 1 := by
    rcases (B5FinS8.mk_eq_mk_iff _ _).1 h with h1 | h1
    · have h2 := congrFun h1 0
      rw [Pi.add_apply, Pi.zero_apply, G6.coreAct_coe, G6.permAct_apply,
        show Claim2526.v8g1⁻¹ 0 = 1 by decide] at h2
      exact (zmod2_eq_of_add_eq_zero _ _ h2).symm
    · have h2 := congrFun h1 4
      rw [Pi.add_apply, G6.coreAct_coe, G6.permAct_apply,
        show Claim2526.v8g1⁻¹ 4 = 4 by decide] at h2
      exact absurd h2 (zmod2_add_self_ne_one _)
  change (QuotientGroup.mk (G6.coreAct 8 (swap 0 1) m) : B5FinS8.Mod8) = QuotientGroup.mk m
  rw [show G6.coreAct 8 (swap 0 1) m = m from Subtype.ext (permAct_swap01_of_eq h0)]

end CFSG.Quasithin.SmithC27
