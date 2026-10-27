module

public import CFSG.LargeExtraspecial.SL4ModClassSpec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module Native CFSG.Sporadic.SmallF2.Native Matrix

theorem false_of_validClass_small {d : ℕ} {refs : Array (Array (Array ℕ))}
    {taus : Array (Array ℕ)} {X : Submodule (ZMod 2) (Fin 105 → ZMod 2)}
    (hX : IsIrredTau taus X d) {m : ℕ} (hm : vec m ∈ X) {c : ClassCert}
    (hc : validClass d refs taus m c = true) (hk : c.kind = 1) : False := by
  rw [validClass, Bool.and_eq_true] at hc
  obtain ⟨hd, hc⟩ := hc
  have hL := mem_of_derivOK hX.1 hm hd
  have hk0 : ¬((c.kind == 0) = true) := by rw [hk]; decide
  have hk1 : (c.kind == 1) = true := by rw [hk]; rfl
  rw [ite_eq_right hk0, ite_eq_left hk1] at hc
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hnz, hB⟩, hmB⟩, hcl⟩ := hc
  have hB' : c.B.size < d := decide_eq_true_eq.mp hB
  have hmB' : xorSel c.mB c.B = xorSel c.sel c.L := beq_iff_eq.mp hmB
  have hm'X : vec (xorSel c.sel c.L) ∈ X := xorSel_mem c.sel hL
  have hm'0 : vec (xorSel c.sel c.L) ≠ 0 := vec_ne_zero_of_nz hnz
  have hm'Y : vec (xorSel c.sel c.L) ∈ spanB c.B := by
    rw [← hmB']
    exact xorSel_mem c.mB fun i hi => Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have hY : IsTauInv taus (spanB c.B) :=
    isTauInv_spanB_of_forall fun t ht s hs =>
      ⟨c.coef[6 * t + s]!, forall_of_closedC hcl t ht s hs⟩
  have hinv : IsTauInv taus (X ⊓ spanB c.B) := fun s hs F hF =>
    ⟨hX.1 s hs F hF.1, hY s hs F hF.2⟩
  have hne : X ⊓ spanB c.B ≠ ⊥ := by
    intro h0
    apply hm'0
    have : vec (xorSel c.sel c.L) ∈ X ⊓ spanB c.B := ⟨hm'X, hm'Y⟩
    rw [h0, Submodule.mem_bot] at this
    exact this
  have hle := hX.2.2 _ hinv inf_le_left hne
  have h1 : finrank (ZMod 2) X ≤ finrank (ZMod 2) (spanB c.B) :=
    Submodule.finrank_mono (le_trans hle inf_le_right)
  have h2 := finrank_spanB_le c.B
  have hdim : finrank (ZMod 2) X = d := hX.2.1
  omega

end CFSG.LargeExtraspecial.SL4Mod
