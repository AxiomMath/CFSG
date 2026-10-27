
module

public import CFSG.Monster.B.TwoA.Base.GeomResBase
public import CFSG.Monster.B.TwoA.Base.PetersenB

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

open CFSG.Monster.B.Co2 (v0)

attribute [local instance] parAction

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

@[expose] def natStd :
    ℕ → Submodule (ZMod 2) (Wv v0)
  | 2 => Submodule.span (ZMod 2) {wFr}
  | 3 => Uplane
  | 4 => U3
  | 5 => U4
  | _ => ⊥

theorem Vhat_eq_EU :
    Vhat = EU (Submodule.span (ZMod 2) {wFr}) := by
  have hw : wFr ∈ Submodule.span (ZMod 2) {wFr} := Submodule.mem_span_singleton_self _
  have h0 : (0 : Wv v0) ∈ Submodule.span (ZMod 2) {wFr} := Submodule.zero_mem _
  have hle : Vhat ≤ EU (Submodule.span (ZMod 2) {wFr}) := by
    intro d hd
    rcases (mem_Vhat_iff d).1 hd with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact xhat_mem_EU
    · exact Subgroup.mul_mem _ xhat_mem_EU (mem_EU_of (e := yhatE) (by rw [psiW_yhat]; exact hw))
    · exact mem_EU_of (e := yhatE) (by rw [psiW_yhat]; exact hw)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [natCard_EU, natCard_submodule, finrank_span_singleton wFr_ne_zero,
    isKleinFour_Vhat.card_four]
  norm_num

@[expose] def psiSubImage (A : Subgroup Dfull) : Submodule (ZMod 2) (Wv v0) where
  carrier := {w | ∃ e : Ehat, (e : Dfull) ∈ A ∧ psiW e = w}
  add_mem' {a b} ha hb := by
    obtain ⟨e, he, rfl⟩ := ha
    obtain ⟨e', he', rfl⟩ := hb
    exact ⟨e * e', A.mul_mem he he', psiW_mul e e'⟩
  zero_mem' := ⟨1, A.one_mem, psiW_one⟩
  smul_mem' t {a} ha := by
    obtain ⟨e, he, rfl⟩ := ha
    rcases zmod2_cases t with rfl | rfl
    · exact ⟨1, A.one_mem, by rw [psiW_one, zero_smul]⟩
    · exact ⟨e, he, by rw [one_smul]⟩

theorem psiSubImage_EU
    (U : Submodule (ZMod 2) (Wv v0)) : psiSubImage (EU U) = U := by
  ext w
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (mem_EU.1 he).2
  · intro hw
    obtain ⟨e, he, heU⟩ := exists_EU_of_mem hw
    exact ⟨e, heU, he⟩

theorem conjSub_EU {h : Dfull} (hh : h ∈ Jhat) (U : Submodule (ZMod 2) (Wv v0)) :
    conjSub h (EU U) = EU (U.map (wAct v0 (jhatToKv0 ⟨h, hh⟩)⁻¹)) := by
  have h1 := conjSub_inv_EU (Jhat.inv_mem hh) U
  rw [inv_inv] at h1
  rw [h1, show (⟨h⁻¹, Jhat.inv_mem hh⟩ : Jhat) = ⟨h, hh⟩⁻¹ from rfl, map_inv]

abbrev Res1 : Set ParGeom := parRes {stdObj 1 le_rfl (by norm_num)}

@[expose] def NatObj :
    Set (ℕ × Submodule (ZMod 2) (Wv v0)) :=
  {x | 2 ≤ x.1 ∧ x.1 ≤ 5 ∧ ∃ k : Kstab v0, x.2 = (natStd x.1).map (wAct v0 k)}

@[expose] def resNat (x : ParGeom) : ℕ × Submodule (ZMod 2) (Wv v0) :=
  (parType x, psiSubImage x.1.2)

theorem jhatToKv0_quot :
    Function.Surjective jhatToKv0 ∧ jhatToKv0.ker = Ehat.subgroupOf Jhat :=
  ⟨jhatToKv0_surjective, ker_jhatToKv0⟩

end CFSG.Monster.B.TwoA
