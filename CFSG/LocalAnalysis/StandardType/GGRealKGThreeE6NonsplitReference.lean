module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6NonsplitFrame
public import CFSG.LocalAnalysis.StandardType.GGKGForkTransfer
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcWeyl

public section

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K]

theorem natCard_frame_range (D : E6QPlusThreeFrame K) :
    Nat.card D.frame.range = 3 ^ 4 := by
  classical
  let e : Multiplicative (Fin Tag.F4.rank → ZMod 3) ≃ D.frame.range :=
    (MonoidHom.ofInjective D.frame_injective).toEquiv
  rw [← Nat.card_congr e]
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (Multiplicative (Fin Tag.F4.rank → ZMod 3)) = 3 ^ 4
  rw [Fintype.card_congr Multiplicative.toAdd]
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hrank : Tag.F4.rank = 4 := by decide
  rw [hrank]

theorem mem_N_of_GGKGIsReflAt (D : E6QPlusThreeFrame K)
    {x : adjointGroup .E6 K} (hx : GGKGIsReflAt 3 D.frame.range x) :
    x ∈ D.N := by
  refine D.mem_N_of_conj x fun s => ?_
  exact (Subgroup.mem_normalizer_iff.mp hx.1 (D.frame (Multiplicative.ofAdd s))).mp
    ⟨Multiplicative.ofAdd s, rfl⟩

theorem exists_weyl_of_GGKGIsReflAt (D : E6QPlusThreeFrame K)
    {x : adjointGroup .E6 K} (hx : GGKGIsReflAt 3 D.frame.range x) :
    ∃ w : WeylGroup .F4,
      w * w = 1 ∧
      Nat.card {s : Fin Tag.F4.rank → ZMod 3 //
        TableBExc.torusAct .F4 3 w s = s} = 3 ^ 3 ∧
      ∀ s : Fin Tag.F4.rank → ZMod 3,
        x * D.frame (Multiplicative.ofAdd s) * x⁻¹ =
          D.frame (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 w s)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxN : x ∈ D.N := mem_N_of_GGKGIsReflAt D hx
  let a : D.N := ⟨x, hxN⟩
  let w : WeylGroup .F4 := D.weyl a
  have hw_sq : w * w = 1 := by
    have hperm : TableBExc.torusPerm .F4 3 (w * w) = TableBExc.torusPerm .F4 3 1 := by
      ext s x
      rw [TableBExc.torusPerm_apply, TableBExc.torusAct_mul]
      simp only [map_one, Equiv.Perm.coe_one, id_eq]
      have hvec : TableBExc.torusAct .F4 3 w
          (TableBExc.torusAct .F4 3 w s) = s := by
        change Multiplicative.ofAdd
            (TableBExc.torusAct .F4 3 w (TableBExc.torusAct .F4 3 w s)) =
          Multiplicative.ofAdd s
        apply D.frame_injective
        rw [← D.conj_frame a (TableBExc.torusAct .F4 3 w s), ← D.conj_frame a s]
        exact hx.2.1 (D.frame (Multiplicative.ofAdd s)) ⟨Multiplicative.ofAdd s, rfl⟩
      exact congrFun hvec x
    exact NoOffExc.torusPerm_injective (τ := .F4) (p := 3)
      (by norm_num : (3 : ℕ) ≠ 2) (by simpa using hperm)
  have hcard_range : Nat.card D.frame.range = 3 ^ 4 := natCard_frame_range D
  have hfix_range : Nat.card
      {e : D.frame.range // x * (e : adjointGroup .E6 K) * x⁻¹ = e} = 3 ^ 3 := by
    have h := hx.2.2
    rw [hcard_range] at h
    norm_num at h ⊢
    omega
  let eRange : (Fin Tag.F4.rank → ZMod 3) ≃ D.frame.range :=
    (Multiplicative.toAdd.symm).trans
      (MonoidHom.ofInjective D.frame_injective).toEquiv
  have hfix_add : Nat.card {s : Fin Tag.F4.rank → ZMod 3 //
      TableBExc.torusAct .F4 3 w s = s} = 3 ^ 3 := by
    have hfix : Nat.card {s : Fin Tag.F4.rank → ZMod 3 //
        TableBExc.torusAct .F4 3 w s = s} =
        Nat.card {e : D.frame.range // x * (e : adjointGroup .E6 K) * x⁻¹ = e} := by
      refine Nat.card_congr (Equiv.subtypeEquiv eRange ?_)
      intro s
      constructor
      · intro hs
        change x * D.frame (Multiplicative.ofAdd s) * x⁻¹ =
          D.frame (Multiplicative.ofAdd s)
        rw [D.conj_frame a s]
        exact congrArg D.frame (congrArg Multiplicative.ofAdd hs)
      · intro hs
        change x * (eRange s : adjointGroup .E6 K) * x⁻¹ =
          (eRange s : adjointGroup .E6 K) at hs
        change x * D.frame (Multiplicative.ofAdd s) * x⁻¹ =
          D.frame (Multiplicative.ofAdd s) at hs
        change Multiplicative.ofAdd (TableBExc.torusAct .F4 3 w s) =
          Multiplicative.ofAdd s
        apply D.frame_injective
        rw [← D.conj_frame a s]
        exact hs
    rw [hfix, hfix_range]
  refine ⟨w, hw_sq, hfix_add, ?_⟩
  intro s
  simpa only [a, w] using D.conj_frame a s

end CFSG.StandardType.ExcFrames.E6QPlusThree

end
