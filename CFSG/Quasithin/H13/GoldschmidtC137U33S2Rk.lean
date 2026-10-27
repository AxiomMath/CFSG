module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Hyp
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Br
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Cases

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat
open scoped commutatorElement

theorem comm_bgen (i j : ℕ) : ⁅bgen i, bgen j⁆ = wd [i, j, i, j] := by
  rw [commutatorElement_def, bgen_inv, bgen_inv]
  simp [wd_cons, wd_nil, mul_assoc]

theorem wd_mem_derived (i j : ℕ) : wd [i, j, i, j] ∈ g2Derived (ZMod 2) := by
  rw [← comm_bgen]
  exact commutator_mem_g2Derived _ _

theorem common_fix : ∀ c ∈ o0Codes, mact (wcode [0, 1, 0, 1]) c = c →
    mact (wcode [3, 2, 3, 2]) c = c → c = 0 ∨ c = 129 := by
  decide +kernel

theorem common_fix_Q : ∀ c ∈ o0Codes,
    (mact (wcode [0, 1, 0, 1]) c = c ∨ mact (wcode [0, 1, 0, 1]) c = c ^^^ 129) →
    (mact (wcode [3, 2, 3, 2]) c = c ∨ mact (wcode [3, 2, 3, 2]) c = c ^^^ 129) →
      c = 0 ∨ c = 129 := by
  decide +kernel

theorem act_fix_129 (g : Gam) : act g 129 = 129 :=
  congrArg Subtype.val (o0Act_one g (by decide))

end CFSG.Quasithin.H13.U3.GC137.S2

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.U3.GC137.S2

theorem fixV_derived_Q :
    fixV ((g2Derived (ZMod 2)).map (g2QAct (ZMod 2))) = ⊥ := by
  refine le_antisymm (fun v hv => ?_) bot_le
  obtain ⟨c, rfl⟩ := codeQ_surjective v
  have h1 := hv (g2QAct (ZMod 2) (wd [0, 1, 0, 1])) ⟨_, wd_mem_derived 0 1, rfl⟩
  have h2 := hv (g2QAct (ZMod 2) (wd [3, 2, 3, 2])) ⟨_, wd_mem_derived 3 2, rfl⟩
  rw [g2QAct_codeQ] at h1 h2
  have e1 := (codeQ_eq_iff c _).1 h1.symm
  have e2 := (codeQ_eq_iff c _).1 h2.symm
  have hw1 : (o0Act (wd [0, 1, 0, 1]) c).1 = mact (wcode [0, 1, 0, 1]) c.1 := by
    change mact (matCode (wd [0, 1, 0, 1]).1) c.1 = _
    rw [matCode_wd (by decide)]
  have hw2 : (o0Act (wd [3, 2, 3, 2]) c).1 = mact (wcode [3, 2, 3, 2]) c.1 := by
    change mact (matCode (wd [3, 2, 3, 2]).1) c.1 = _
    rw [matCode_wd (by decide)]
  rw [hw1] at e1
  rw [hw2] at e2
  rcases common_fix_Q c.1 c.2 e1 e2 with h | h
  · have : c = o0Zero := Subtype.ext h
    rw [this, codeQ_zero]
    exact Subgroup.one_mem _
  · have : codeQ c = codeQ o0Zero := (codeQ_eq_iff c o0Zero).2 (Or.inr (by simp [h, o0Zero]))
    rw [this, codeQ_zero]
    exact Subgroup.one_mem _

theorem rk_L_Q : rkIdx (fixV ((g2Derived (ZMod 2)).map (g2QAct (ZMod 2)))) = 6 := by
  have h := rkIdx_of_cards (fixV ((g2Derived (ZMod 2)).map (g2QAct (ZMod 2)))) (a := 0) (b := 6)
    (by rw [card_ModQ]; norm_num) (by rw [fixV_derived_Q]; simp)
  exact h

@[expose] def zO : ModO := codeO ⟨129, by decide⟩

theorem zO_sq : zO ^ 2 = 1 := by
  rw [pow_two, zO, ← codeO_xor]
  have : o0Xor (⟨129, by decide⟩ : O0C) ⟨129, by decide⟩ = o0Zero := o0Xor_self _
  rw [this, codeO_zero]

theorem zO_ne_one : zO ≠ 1 := by
  intro h
  rw [zO, ← codeO_zero] at h
  have := congrArg Subtype.val (codeO_injective h)
  simp [o0Zero] at this

theorem card_zpowers_zO : Nat.card (Subgroup.zpowers zO) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime zO_sq zO_ne_one

theorem fixV_derived_O :
    fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) = Subgroup.zpowers zO := by
  refine le_antisymm (fun v hv => ?_) ?_
  · obtain ⟨c, rfl⟩ := codeO_surjective v
    have h1 := hv (g2OAct (ZMod 2) (wd [0, 1, 0, 1])) ⟨_, wd_mem_derived 0 1, rfl⟩
    have h2 := hv (g2OAct (ZMod 2) (wd [3, 2, 3, 2])) ⟨_, wd_mem_derived 3 2, rfl⟩
    rw [g2OAct_codeO] at h1 h2
    have e1 := congrArg Subtype.val (codeO_injective h1)
    have e2 := congrArg Subtype.val (codeO_injective h2)
    have hw1 : (o0Act (wd [0, 1, 0, 1]) c).1 = mact (wcode [0, 1, 0, 1]) c.1 := by
      change mact (matCode (wd [0, 1, 0, 1]).1) c.1 = _
      rw [matCode_wd (by decide)]
    have hw2 : (o0Act (wd [3, 2, 3, 2]) c).1 = mact (wcode [3, 2, 3, 2]) c.1 := by
      change mact (matCode (wd [3, 2, 3, 2]).1) c.1 = _
      rw [matCode_wd (by decide)]
    rw [hw1] at e1
    rw [hw2] at e2
    rcases common_fix c.1 c.2 e1 e2 with h | h
    · have : c = o0Zero := Subtype.ext h
      rw [this, codeO_zero]
      exact Subgroup.one_mem _
    · have : c = ⟨129, by decide⟩ := Subtype.ext h
      rw [this]
      exact Subgroup.mem_zpowers zO
  · rw [Subgroup.zpowers_le]
    intro x hx
    obtain ⟨g, -, rfl⟩ := hx
    rw [zO, g2OAct_codeO]
    exact congrArg codeO (o0Act_one g (by decide))

theorem rk_L_O : rkIdx (fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2)))) = 6 := by
  have h := rkIdx_of_cards (fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2)))) (a := 1) (b := 7)
    (by rw [card_ModO]; norm_num) (by rw [fixV_derived_O, card_zpowers_zO]; simp)
  exact h

end CFSG.Quasithin.H13.U3.GC137
