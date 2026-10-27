module

public import CFSG.LocalAnalysis.StandardType.GGNineDepRowSym
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymPerm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggNineDepRowSymSuccTwo_holds : GGNineDepRowSymSuccTwoInput := by
  classical
  intro V _ _ h α r T s x X hdisj
  rcases hdisj with ⟨hdvd, e, _⟩
  let d := Module.finrank (ZMod 3) ↥(ggFixLineT r s)
  have hdvd' : 3 ∣ d + 2 := hdvd
  have hd_ge : 7 ≤ d := X.d_ge
  have hd_le : d ≤ 9 := X.d_le
  have hd : d = 7 := by omega
  let P : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range r)
  let A : Subgroup (V ≃ₗ[ZMod 3] V) := ggLargeGrp r s
  let Q : Subgroup (↥(ggFixLineT r s) ≃ₗ[ZMod 3] ↥(ggFixLineT r s)) := ggNineQ X
  have hPA : P ≤ A := Subgroup.closure_mono (Set.subset_union_left)
  have hcardP : Nat.card ↥P = Nat.factorial 9 := by
    have h := l04fD5_P_card (p := 3) (m := 9 - 1) (by norm_num) (by norm_num)
      (V := V) (h := h) (α := α) (r := r) X.case.lin.pair X.case.lin.refl_form
    simpa using h
  have hcardA : Nat.card ↥A = Nat.card ↥Q := by
    change Nat.card ↥A = Nat.card ↥(Set.range (⇑(ggLargeRho r s X.hA)))
    exact Nat.card_congr (Equiv.ofInjective (⇑(ggLargeRho r s X.hA)) X.restr.1)
  have hcardQ : Nat.card ↥Q = Nat.factorial 9 := by
    calc Nat.card ↥Q = Nat.card (Equiv.Perm (Fin (d + 2))) := Nat.card_congr e.toEquiv
      _ = (d + 2).factorial := by rw [Nat.card_perm, Nat.card_fin]
      _ = Nat.factorial 9 := by rw [hd]
  have hcardA' : Nat.card ↥A = Nat.factorial 9 := hcardA.trans hcardQ
  have hfinA : Finite ↥A :=
    Nat.finite_of_card_ne_zero (by rw [hcardA']; exact Nat.factorial_ne_zero 9)
  have hPAeq : P = A := Subgroup.eq_of_le_of_card_ge hPA (by rw [hcardA', hcardP])
  have hFle : ggLinFix (Set.range r) ≤ Submodule.span (ZMod 3) ({x} : Set V) := by
    intro v hv
    rw [← X.case.lin.fix_s]
    intro a ha
    obtain ⟨k, rfl⟩ := ha
    have hskA : s k ∈ A := Subgroup.subset_closure (Or.inr ⟨k, rfl⟩)
    have hskP : s k ∈ P := by rw [hPAeq]; exact hskA
    have hfixP : ∀ g ∈ P, g v = v := by
      intro g hg
      change g ∈ Subgroup.closure (Set.range r) at hg
      refine Subgroup.closure_induction (p := fun g _ => g v = v) ?_ ?_ ?_ ?_ hg
      · rintro g ⟨i, rfl⟩
        exact hv (r i) ⟨i, rfl⟩
      · simp
      · intro a b ha hb iha ihb
        rw [LinearEquiv.mul_apply, ihb, iha]
      · intro a ha iha
        apply a.injective
        exact (LinearEquiv.apply_symm_apply a v).trans iha.symm
    exact hfixP (s k) hskP
  have hFle1 : Module.finrank (ZMod 3) ↥(ggLinFix (Set.range r)) ≤ 1 := by
    have h1 := Submodule.finrank_mono hFle
    have h2 : Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3) ({x} : Set V)) = 1 := by
      simpa using finrank_span_singleton (K := ZMod 3) X.case.lin.x_ne
    omega
  exact absurd hFle1 (not_le.mpr (lt_of_lt_of_le (by norm_num : 1 < 2) X.case.two))

end CFSG.StandardType

end
