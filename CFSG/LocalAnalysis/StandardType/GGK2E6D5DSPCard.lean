module

public import CFSG.LocalAnalysis.StandardType.GGK2E6D5DSPSubgroupCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import Mathlib.GroupTheory.Perm.Fin

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.HdRo7D

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_dspSubgroup_le {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin 6) (ZMod 3) V) :
    Nat.card (DSPSubgroup 3 b) ≤ 1920 := by
  classical
  let P : Subgroup (V ≃ₗ[ZMod 3] V) := DSPSubgroup 3 b
  have hdata : ∀ a : P, ∃ σc : Equiv.Perm (Fin 6) × (Fin 6 → ZMod 3),
      σc.1 0 = 0 ∧ σc.2 0 = 1 ∧
      (∀ i, σc.2 i = 1 ∨ σc.2 i = -1) ∧
      (∏ i, σc.2 i = 1) ∧
      ∀ i, (a : V ≃ₗ[ZMod 3] V) (b i) = σc.2 i • b (σc.1 i) := by
    intro a
    have ha : DSP 3 b (a : V ≃ₗ[ZMod 3] V) := a.2
    obtain ⟨σ, c, hσ, hc0, hc, hprod, hact⟩ := ha
    exact ⟨(σ, c), hσ, hc0, hc, hprod, hact⟩
  choose d hd using hdata
  have hm1 : (-1 : ZMod 3) ≠ 1 := by decide
  have hfst : ∀ σ : Equiv.Perm (Fin 6), (Equiv.Perm.decomposeFin σ).1 = σ 0 := by
    intro σ
    have h := Equiv.Perm.decomposeFin_symm_apply_zero (Equiv.Perm.decomposeFin σ).1
      (Equiv.Perm.decomposeFin σ).2
    rw [Prod.mk.eta, Equiv.symm_apply_apply] at h
    exact h.symm
  let F : P → Equiv.Perm (Fin 5) × (Fin 4 → Bool) := fun a =>
    ((Equiv.Perm.decomposeFin (d a).1).2,
      fun i => decide ((d a).2 ((Fin.succ i).castSucc) = 1))
  have hF : Function.Injective F := by
    intro a a' haa'
    simp only [F, Prod.mk.injEq] at haa'
    obtain ⟨hperm, hsigns⟩ := haa'
    have hsign : ∀ j : Fin 4,
        (d a).2 ((Fin.succ j).castSucc) = (d a').2 ((Fin.succ j).castSucc) := by
      intro j
      have hj := congrFun hsigns j
      simp only [decide_eq_decide] at hj
      rcases (hd a).2.2.1 ((Fin.succ j).castSucc) with h | h <;>
        rcases (hd a').2.2.1 ((Fin.succ j).castSucc) with h' | h'
      · rw [h, h']
      · exact absurd (hj.mp h) (by rw [h']; exact hm1)
      · exact absurd (hj.mpr h') (by rw [h]; exact hm1)
      · rw [h, h']
    have hσ : (d a).1 = (d a').1 := by
      apply Equiv.Perm.decomposeFin.injective
      refine Prod.ext ?_ hperm
      rw [hfst, hfst, (hd a).1, (hd a').1]
    have hprefix : (∏ i : Fin 5, (d a).2 (Fin.castSucc i)) =
        (∏ i : Fin 5, (d a').2 (Fin.castSucc i)) := by
      apply Finset.prod_congr rfl
      intro i _
      fin_cases i
      · simpa using (hd a).2.1.trans (hd a').2.1.symm
      · simpa using hsign 0
      · simpa using hsign 1
      · simpa using hsign 2
      · simpa using hsign 3
    have hprefixne : (∏ i : Fin 5, (d a).2 (Fin.castSucc i)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      rcases (hd a).2.2.1 (Fin.castSucc i) with h | h <;> simp [h]
    have hpa : (∏ i : Fin 5, (d a).2 (Fin.castSucc i)) *
        (d a).2 (Fin.last 5) = 1 := by
      simpa [Fin.prod_univ_castSucc] using (hd a).2.2.2.1
    have hpa' : (∏ i : Fin 5, (d a').2 (Fin.castSucc i)) *
        (d a').2 (Fin.last 5) = 1 := by
      simpa [Fin.prod_univ_castSucc] using (hd a').2.2.2.1
    rw [← hprefix] at hpa'
    have hlast : (d a).2 (Fin.last 5) = (d a').2 (Fin.last 5) :=
      mul_left_cancel₀ hprefixne (hpa.trans hpa'.symm)
    have hc : (d a).2 = (d a').2 := by
      funext i
      fin_cases i
      · simpa using (hd a).2.1.trans (hd a').2.1.symm
      · simpa using hsign 0
      · simpa using hsign 1
      · simpa using hsign 2
      · simpa using hsign 3
      · simpa using hlast
    apply Subtype.ext
    apply b.ext'
    intro i
    rw [(hd a).2.2.2.2 i, (hd a').2.2.2.2 i, hσ, hc]
  calc Nat.card P ≤ Nat.card (Equiv.Perm (Fin 5) × (Fin 4 → Bool)) :=
        Nat.card_le_card_of_injective F hF
    _ = 1920 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm,
        Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      norm_num

end CFSG.StandardType

end
