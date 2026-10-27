
module

public import CFSG.Monster.B.TwoA.Base.SevenPairCBase
public import CFSG.Monster.B.TwoA.Base.Space34ABase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

open scoped Pointwise

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem mem_wSetStab_span
    {n : ℕ} {g : Fin n → Wv v0} {k : Kstab v0}
    (h : ∀ i, wAct v0 k (g i) ∈ Submodule.span (ZMod 2) (Set.range g)) :
    k ∈ wSetStab (Submodule.span (ZMod 2) (Set.range g)) := by
  intro x hx
  have hle : Submodule.span (ZMod 2) (Set.range g) ≤
      (Submodule.span (ZMod 2) (Set.range g)).comap (wAct v0 k) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  exact hle hx

@[expose] def wordP3 : Fin 7 → Equiv.Perm (Fin 24) :=
  ![1, wit2, wit1 * wit2, wit5 * wit2, wit3 * wit5 * wit2, wit4 * wit5 * wit2,
    wit3 * wit4 * wit5 * wit2]

theorem wordP3_pair : ∀ i : Fin 7, (wordP3 i 2 = pa7 i ∧ wordP3 i 3 = pb7 i) ∨
    (wordP3 i 2 = pb7 i ∧ wordP3 i 3 = pa7 i) := by
  decide

@[expose] def wordF3 (i : Fin 7) : FA3 :=
  ![1, witF3 4, witF3 2 * witF3 4, witF3 3 * witF3 4, witF3 0 * witF3 3 * witF3 4,
    witF3 1 * witF3 3 * witF3 4, witF3 0 * witF3 1 * witF3 3 * witF3 4] i

theorem coe_wordF3 (i : Fin 7) :
    (((wordF3 i : FA3) : AutPerm) : Equiv.Perm (Fin 24)) = wordP3 i := by
  fin_cases i <;> rfl

theorem wordF3_pair (i : Fin 7) :
    ((((wordF3 i : FA3) : AutPerm) : Equiv.Perm (Fin 24)) 2 = pa7 i ∧
      (((wordF3 i : FA3) : AutPerm) : Equiv.Perm (Fin 24)) 3 = pb7 i) ∨
    ((((wordF3 i : FA3) : AutPerm) : Equiv.Perm (Fin 24)) 2 = pb7 i ∧
      (((wordF3 i : FA3) : AutPerm) : Equiv.Perm (Fin 24)) 3 = pa7 i) := by
  rw [coe_wordF3]
  exact wordP3_pair i

@[expose] def wordP2 : Fin 3 → Equiv.Perm (Fin 24) := ![1, wit2, wit1 * wit2]

theorem wordP2_pair : ∀ i : Fin 3,
    (wordP2 i 2 = pa7 ⟨i, by omega⟩ ∧ wordP2 i 3 = pb7 ⟨i, by omega⟩) ∨
    (wordP2 i 2 = pb7 ⟨i, by omega⟩ ∧ wordP2 i 3 = pa7 ⟨i, by omega⟩) := by
  decide

@[expose] def wordF2 (i : Fin 3) : FA2 := ![1, witF2 1, witF2 0 * witF2 1] i

theorem coe_wordF2 (i : Fin 3) :
    (((wordF2 i : FA2) : AutPerm) : Equiv.Perm (Fin 24)) = wordP2 i := by
  fin_cases i <;> rfl

theorem wordF2_pair (i : Fin 3) :
    ((((wordF2 i : FA2) : AutPerm) : Equiv.Perm (Fin 24)) 2 = pa7 ⟨i, by omega⟩ ∧
      (((wordF2 i : FA2) : AutPerm) : Equiv.Perm (Fin 24)) 3 = pb7 ⟨i, by omega⟩) ∨
    ((((wordF2 i : FA2) : AutPerm) : Equiv.Perm (Fin 24)) 2 = pb7 ⟨i, by omega⟩ ∧
      (((wordF2 i : FA2) : AutPerm) : Equiv.Perm (Fin 24)) 3 = pa7 ⟨i, by omega⟩) := by
  rw [coe_wordF2]
  exact wordP2_pair i

@[expose] def signW (b : ZMod 2) : C :=
  if b = 0 then ⟨evW 0, (mem_Ceq.1 (evW_mem 0)).1⟩ else 0

theorem signW_mem (b : ZMod 2) : ((signW b : C) : Fin 24 → ZMod 2) ∈ Ceq := by
  rw [signW]
  split_ifs
  · exact evW_mem 0
  · exact Ceq.zero_mem

theorem signW_23 (b : ZMod 2) :
    1 + ((signW b : C) : Fin 24 → ZMod 2) 2 + ((signW b : C) : Fin 24 → ZMod 2) 3 = b := by
  rcases zmod2_cases b with rfl | rfl
  · rw [signW, ite_eq_left rfl]
    decide +kernel
  · rw [signW, ite_eq_right (by decide)]
    rfl

theorem monomial_move
    {p : AutPerm} (hp : p ∈ Ppair) {x y : Fin 24} (h : OffPair x y)
    (hxy : ((p : Equiv.Perm (Fin 24)) 2 = x ∧ (p : Equiv.Perm (Fin 24)) 3 = y) ∨
      ((p : Equiv.Perm (Fin 24)) 2 = y ∧ (p : Equiv.Perm (Fin 24)) 3 = x)) (b : ZMod 2) :
    ∃ hk : (QuotientGroup.mk (gO (signW b) * PO p) : OLq) ∈ Kstab v0,
      wAct v0 ⟨_, hk⟩ (wFr + sW) = pairW x y h b := by
  have hk := (mk_mem_Kstab_iff_monomial (signW b) p).2 ⟨hp, signW_mem b⟩
  refine ⟨hk, ?_⟩
  rw [wFr_add_sW, wAct_monomial_pairW hk offPair23 1, signW_23, pairW_eq_iff]
  exact ⟨hxy, rfl⟩

abbrev Usharp (U : Submodule (ZMod 2) (Wv v0)) : Type := {x : Wv v0 // x ∈ U ∧ x ≠ 0}

@[expose, instance_reducible] def usharpAction
    (U : Submodule (ZMod 2) (Wv v0)) :
    MulAction (wSetStab U) (Usharp U) where
  smul k x := ⟨wAct v0 ((k : Kstab v0)⁻¹) x, ((wSetStab U).inv_mem k.2) x x.2.1, fun h =>
    x.2.2 (by
      rw [← wAct_apply_inv (k : Kstab v0) x, h, map_zero])⟩
  one_smul x := Subtype.ext (by
    change wAct v0 ((1 : wSetStab U) : Kstab v0)⁻¹ x = x
    rw [OneMemClass.coe_one, inv_one, wAct_one, Module.End.one_apply])
  mul_smul k k' x := Subtype.ext (by
    change wAct v0 ((k * k' : wSetStab U) : Kstab v0)⁻¹ x =
      wAct v0 ((k : Kstab v0)⁻¹) (wAct v0 ((k' : Kstab v0)⁻¹) x)
    rw [Subgroup.coe_mul, mul_inv_rev, wAct_mul, Module.End.mul_apply])

attribute [local instance] usharpAction

theorem natCard_Usharp
    (U : Submodule (ZMod 2) (Wv v0)) :
    Nat.card (Usharp U) = Nat.card U - 1 := by
  classical
  have e : Usharp U ≃ {x : U // x ≠ 0} :=
    { toFun := fun v => ⟨⟨v.1, v.2.1⟩, fun h => v.2.2 (congrArg Subtype.val h)⟩
      invFun := fun x => ⟨x.1, x.1.2, fun h => x.2 (Subtype.ext h)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Fintype U := Fintype.ofFinite U
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card]

theorem index_wSetStab_inf_Mfr
    {U : Submodule (ZMod 2) (Wv v0)} (hw : wFr ∈ U)
    (htr : ∀ y ∈ U, y ≠ 0 → ∃ k ∈ wSetStab U, wAct v0 k wFr = y) :
    ((wSetStab U ⊓ Mfr).subgroupOf (wSetStab U)).index = Nat.card U - 1 := by
  set w0 : Usharp U := ⟨wFr, hw, wFr_ne_zero⟩
  have hstab : MulAction.stabilizer (wSetStab U) w0 =
      (wSetStab U ⊓ Mfr).subgroupOf (wSetStab U) := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, ← Subtype.coe_inj]
    change wAct v0 ((k : Kstab v0)⁻¹) wFr = wFr ↔ _
    rw [fix_inv_iff]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  have horb : MulAction.orbit (wSetStab U) w0 = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro v
    obtain ⟨k, hk, hkw⟩ := htr v v.2.1 v.2.2
    refine ⟨⟨k, hk⟩⁻¹, Subtype.ext ?_⟩
    change wAct v0 ((((⟨k, hk⟩ : wSetStab U)⁻¹ : wSetStab U) : Kstab v0)⁻¹) wFr = v
    rw [InvMemClass.coe_inv, inv_inv]
    exact hkw
  rw [← hstab, MulAction.index_stabilizer, horb, Set.ncard_univ, natCard_Usharp]

instance wFix_U4_normal :
    ((wFix (U4 : Set (Wv v0))).subgroupOf (wSetStab U4)).Normal :=
  ker_resHomU ▸ (resHomU U4).normal_ker

instance wFix_U3_normal :
    ((wFix (U3 : Set (Wv v0))).subgroupOf (wSetStab U3)).Normal :=
  ker_resHomU ▸ (resHomU U3).normal_ker

end CFSG.Monster.B.TwoA
