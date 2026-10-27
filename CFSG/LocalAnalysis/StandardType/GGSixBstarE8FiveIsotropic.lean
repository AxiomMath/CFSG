module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProof

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open Module

namespace NoOffE8Five

local instance noOffE8FiveFactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance noOffE8FiveNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section Isotropic


theorem mem_eigE8_iff {lam : ZMod 5} {x : Fin Tag.E8.rank → ZMod 5} :
    x ∈ NoOffRest.eigE8 5 lam ↔
      NoOffRest.torusLin .E8 5 NoOffRest.weylE8W x = lam • x :=
  @NoOffRest.mem_eigSp (ZMod 5) (Fin Tag.E8.rank → ZMod 5) (inferInstance) (inferInstance)
    (Pi.module _ _ _) (NoOffRest.torusLin .E8 5 NoOffRest.weylE8W) lam x

theorem finrank_eigE8_five {lam : ZMod 5} (hlam : lam * lam = -1) :
    finrank (ZMod 5) (NoOffRest.eigE8 5 lam) = 4 :=
  @NoOffRest.finrank_eigE8 5 _ (by norm_num) lam hlam

theorem bform_eq_zero_of_mem_eigE8 {lam : ZMod 5} (hlam : lam * lam = -1)
    {x y : Fin Tag.E8.rank → ZMod 5} (hx : x ∈ NoOffRest.eigE8 5 lam)
    (hy : y ∈ NoOffRest.eigE8 5 lam) : NoOffRest.bform .E8 5 x y = 0 := by
  have hx' : NoOffRest.torusLin .E8 5 NoOffRest.weylE8W x = lam • x :=
    (mem_eigE8_iff (x := x)).mp hx
  have hy' : NoOffRest.torusLin .E8 5 NoOffRest.weylE8W y = lam • y :=
    (mem_eigE8_iff (x := y)).mp hy
  have hb : NoOffRest.bform .E8 5 (NoOffRest.torusLin .E8 5 NoOffRest.weylE8W x)
      (NoOffRest.torusLin .E8 5 NoOffRest.weylE8W y) = NoOffRest.bform .E8 5 x y := by
    rw [NoOffRest.torusLin_apply, NoOffRest.torusLin_apply]
    exact NoOffRest.bform_torusAct NoOffRest.weylE8W x y
  have h : NoOffRest.bform .E8 5 x y = lam * lam * NoOffRest.bform .E8 5 x y := by
    calc NoOffRest.bform .E8 5 x y
        = NoOffRest.bform .E8 5 (NoOffRest.torusLin .E8 5 NoOffRest.weylE8W x)
            (NoOffRest.torusLin .E8 5 NoOffRest.weylE8W y) := hb.symm
      _ = NoOffRest.bform .E8 5 (lam • x) (lam • y) := by rw [hx', hy']
      _ = lam * lam * NoOffRest.bform .E8 5 x y := by
            rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
            ring
  have hneg : NoOffRest.bform .E8 5 x y = -NoOffRest.bform .E8 5 x y := by
    rw [hlam] at h
    exact h.trans (neg_one_mul _)
  have hzero : NoOffRest.bform .E8 5 x y + NoOffRest.bform .E8 5 x y = 0 :=
    eq_neg_iff_add_eq_zero.mp hneg
  have h2 : (2 : ZMod 5) * NoOffRest.bform .E8 5 x y = 0 := by
    rw [two_mul]
    exact hzero
  exact (mul_eq_zero.mp h2).resolve_left (NoOffRest.two_ne_zero_zmod (by norm_num))

theorem mem_eigE8_of_forall_bform_eq_zero {lam : ZMod 5} (hlam : lam * lam = -1)
    {z : Fin Tag.E8.rank → ZMod 5}
    (hz : ∀ y ∈ NoOffRest.eigE8 5 lam, NoOffRest.bform .E8 5 y z = 0) :
    z ∈ NoOffRest.eigE8 5 lam := by
  let E := NoOffRest.eigSp (NoOffRest.torusLin .E8 5 NoOffRest.weylE8W) lam
  let N := (NoOffRest.bform .E8 5).orthogonal E
  have hle : E ≤ N := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact bform_eq_zero_of_mem_eigE8 hlam hy hx
  have hdimE : finrank (ZMod 5) E = 4 := finrank_eigE8_five hlam
  have hdimN : finrank (ZMod 5) N = 4 := by
    dsimp only [N]
    rw [LinearMap.BilinForm.finrank_orthogonal
        (NoOffRest.bform_nondegenerate_E8 (p := 5)) E,
      hdimE, Module.finrank_fin_fun]
    change 8 - 4 = 4
    norm_num
  have hEq : E = N :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hdimE, hdimN])
  have hzN : z ∈ N := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hz y hy
  change z ∈ E
  rw [hEq]
  exact hzN

theorem exists_mem_eigE8_bform_redMod_ne_zero {lam : ZMod 5} (hlam : lam * lam = -1)
    {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) :
    ∃ y ∈ NoOffRest.eigE8 5 lam,
      NoOffRest.bform .E8 5 y (TableBExc.redMod .E8 5 α) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hmem : TableBExc.redMod .E8 5 α ∈ NoOffRest.eigE8 5 lam :=
    mem_eigE8_of_forall_bform_eq_zero hlam hcon
  have h0 := bform_eq_zero_of_mem_eigE8 hlam hmem hmem
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  have h1 : Tag.E8.symmetrizer j j = 1 := by
    change (1 : Matrix (Fin 8) (Fin 8) ℤ) j j = 1
    exact Matrix.one_apply_eq j
  rw [NoOffRest.bform_redMod, hj, h1] at h0
  have h2 : (2 : ZMod 5) = 0 := by
    have h3 := h0
    push_cast at h3
    simpa using h3
  exact NoOffRest.two_ne_zero_zmod (p := 5) (by norm_num) h2

end Isotropic

end NoOffE8Five

end CFSG.StandardType
