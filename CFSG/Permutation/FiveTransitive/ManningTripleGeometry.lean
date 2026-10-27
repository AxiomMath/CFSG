module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import CFSG.Permutation.FiveTransitive.ManningEdgeGeometry

public section

namespace CFSG

namespace FiveTransitive.ManningTripleGeometry

open Equiv MulAction

private theorem pow_ne_of_prime
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : Perm X) (hp : (orderOf g).Prime) {a : X} (ha : g a ≠ a)
    {k : ℕ} (hk : 0 < k) (hklt : k < orderOf g) : (g ^ k) a ≠ a := by
  have hco : k.Coprime (orderOf g) := (hp.coprime_iff_not_dvd.mpr
    (fun h => (Nat.le_of_dvd hk h).not_gt hklt)).symm
  have hs := Perm.support_pow_coprime (σ := g) hco
  exact Perm.mem_support.mp (hs ▸ Perm.mem_support.mpr ha)

theorem independent_triple
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : Perm X) (hp : (orderOf g).Prime) (hp5 : 5 ≤ orderOf g)
    (hm : 6 ≤ g.support.card) :
    ∃ a c f : X, c = g (g a) ∧ a ≠ c ∧ a ≠ f ∧ c ≠ f ∧
      ({a,c,f} : Finset X) ⊆ g.support ∧
      ∀ x ∈ ({a,c,f} : Finset X), g x ∉ ({a,c,f} : Finset X) := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < g.support.card)
  have hga : g a ≠ a := Perm.mem_support.mp ha
  have hg2 : g (g a) ≠ a := by
    simpa [pow_succ, Perm.mul_apply] using pow_ne_of_prime g hp hga (k := 2) (by omega) (by omega)
  have hg3 : g (g (g a)) ≠ a := by
    simpa [pow_succ, Perm.mul_apply] using pow_ne_of_prime g hp hga (k := 3) (by omega) (by omega)
  let c := g (g a)
  let E : Finset X := {g.symm a, a, g a, c, g c}
  have hE : E.card ≤ 5 := by
    have h1 := Finset.card_insert_le (g.symm a) ({a,g a,c,g c} : Finset X)
    have h2 := Finset.card_insert_le a ({g a,c,g c} : Finset X)
    have h3 := Finset.card_insert_le (g a) ({c,g c} : Finset X)
    have h4 := Finset.card_insert_le c ({g c} : Finset X)
    have h5 : ({g c} : Finset X).card = 1 := Finset.card_singleton _
    dsimp [E]
    omega
  obtain ⟨f, hf, hfE⟩ := Finset.exists_mem_notMem_of_card_lt_card (show E.card < g.support.card by omega)
  have hfa : f ≠ a := by intro he; exact hfE (by simp [E, he])
  have hfc : f ≠ c := by intro he; exact hfE (by simp [E, he])
  have hfg : f ≠ g a := by intro he; exact hfE (by simp [E, he])
  have hfgc : f ≠ g c := by intro he; exact hfE (by simp [E, he])
  have hgf : g f ≠ a := by
    intro he
    exact hfE (by simp [E, show f = g.symm a from (g.symm_apply_apply f).symm.trans (congrArg g.symm he)])
  have hgfc : g f ≠ c := by
    intro he
    exact hfg (g.injective he)
  have hc : c ∈ g.support := Perm.apply_mem_support.mpr (Perm.apply_mem_support.mpr ha)
  refine ⟨a,c,f,rfl,hg2.symm,hfa.symm,hfc.symm,?_,?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hga, fun he => hga (g.injective he).symm, hfg.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hg3, Perm.mem_support.mp hc, hfgc.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hgf, hgfc, Perm.mem_support.mp hf⟩

theorem exists_conjugate_fix_two_move
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (h3 : MulAction.IsMultiplyPretransitive P X 3)
    (g : Perm X) (hg : g ∈ P) (hm : 0 < g.support.card)
    (hfixed : g.support.card + 2 ≤ Fintype.card X)
    {a c f : X} (hac : a ≠ c) (haf : a ≠ f) (hcf : c ≠ f) :
    ∃ u : Perm X, u ∈ P ∧ u.support.card = g.support.card ∧ orderOf u = orderOf g ∧
      u a = a ∧ u f = f ∧ u c ≠ c := by
  classical
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hm
  have hcompl : 1 < g.supportᶜ.card := by rw [Finset.card_compl]; omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcompl
  have hxfix : g x = x := by simpa using hx
  have hyfix : g y = y := by simpa using hy
  have hxz : x ≠ z := fun he => (Perm.mem_support.mp hz) (he ▸ hxfix)
  have hyz : y ≠ z := fun he => (Perm.mem_support.mp hz) (he ▸ hyfix)
  let v : Fin 3 → X := ![x,z,y]
  let w : Fin 3 → X := ![a,c,f]
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢
    all_goals aesop
  have hw : Function.Injective w := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [w] at hij ⊢
    all_goals aesop
  obtain ⟨h, hh⟩ := MulAction.isMultiplyPretransitive_iff.mp h3
    (⟨v,hv⟩ : Fin 3 ↪ X) (⟨w,hw⟩ : Fin 3 ↪ X)
  have hhx : (h : Perm X) x = a := by
    change h • x = a
    simpa [v,w] using DFunLike.congr_fun hh 0
  have hhz : (h : Perm X) z = c := by
    change h • z = c
    simpa [v,w] using DFunLike.congr_fun hh 1
  have hhy : (h : Perm X) y = f := by
    change h • y = f
    simpa [v,w] using DFunLike.congr_fun hh 2
  let u : Perm X := (h : Perm X) * g * (h : Perm X)⁻¹
  have hi (b d : X) (he : (h : Perm X) b = d) : (h : Perm X)⁻¹ d = b := by
    rw [← he]; exact (h : Perm X).symm_apply_apply b
  refine ⟨u, P.mul_mem (P.mul_mem h.property hg) (P.inv_mem h.property),
    Perm.card_support_conj, ?_, ?_, ?_, ?_⟩
  · exact (SemiconjBy.orderOf_eq (h : Perm X) (x := g) (y := u) (by
      change (h : Perm X) * g = ((h : Perm X) * g * (h : Perm X)⁻¹) * (h : Perm X)
      group)).symm
  · change (h : Perm X) (g ((h : Perm X)⁻¹ a)) = a
    rw [hi x a hhx, hxfix, hhx]
  · change (h : Perm X) (g ((h : Perm X)⁻¹ f)) = f
    rw [hi y f hhy, hyfix, hhy]
  · intro he
    change (h : Perm X) (g ((h : Perm X)⁻¹ c)) = c at he
    rw [hi z c hhz] at he
    exact (Perm.mem_support.mp hz) ((h : Perm X).injective (he.trans hhz.symm))

theorem three_cycle_triple
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : Perm X) (horder : orderOf g = 3) (hm : 4 ≤ g.support.card) :
    ∃ a b c d : X, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      g a=b ∧ g b=c ∧ g c=a ∧
      ({a,b,d} : Finset X).card=3 ∧ ({a,b,d} : Finset X) ⊆ g.support ∧
      c ∉ ({a,b,d} : Finset X) ∧
      (({a,b,d} : Finset X).filter (fun x => g x ∈ ({a,b,d} : Finset X))) = {a} := by
  classical
  have hp : (orderOf g).Prime := by rw [horder]; exact Nat.prime_three
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<g.support.card by omega)
  have hga := Perm.mem_support.mp ha
  have h2 : g (g a) ≠ a := by
    simpa [pow_succ,Perm.mul_apply] using pow_ne_of_prime g hp hga (k:=2) (by omega) (by omega)
  have h3 (x:X) : g (g (g x))=x := by
    have h := congrArg (fun p : Perm X => p x) (pow_orderOf_eq_one g)
    simpa [horder,pow_succ,Perm.mul_apply] using h
  let b := g a
  let c := g b
  have hab : a≠b := hga.symm
  have hac : a≠c := h2.symm
  have hbc : b≠c := fun he => hga (g.injective he).symm
  have hE : ({a,b,c} : Finset X).card=3 := by simp [hab,hac,hbc]
  obtain ⟨d,hd,hdE⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({a,b,c} : Finset X).card<g.support.card by omega)
  have hda : d≠a := by intro he; exact hdE (by simp [he])
  have hdb : d≠b := by intro he; exact hdE (by simp [he])
  have hdc : d≠c := by intro he; exact hdE (by simp [he])
  have hcS : c∉({a,b,d} : Finset X) := by simp [hac.symm,hbc.symm,hdc.symm]
  have hgda : g d≠a := by
    intro he
    exact hdc (g.injective (he.trans (h3 a).symm))
  have hgdb : g d≠b := fun he => hda (g.injective he)
  have hgdS : g d∉({a,b,d} : Finset X) := by
    simp [hgda,hgdb,Perm.mem_support.mp hd]
  refine ⟨a,b,c,d,hab,hac,hbc,rfl,rfl,h3 a,?_,?_,hcS,?_⟩
  · simp [hab,hda.symm,hdb.symm]
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact Perm.apply_mem_support.mpr ha
    · exact hd
  · ext x
    simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl,hx⟩
      · rfl
      · exact (hcS (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hx)).elim
      · exact (hgdS (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hx)).elim
    · rintro rfl
      exact ⟨Or.inl rfl,Or.inr (Or.inl rfl)⟩

theorem large_cycle_edge_cards
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : Perm X) (S : Finset X) (hS : S⊆g.support) (hcard : S.card=3)
    (hn : ∀x∈S,g x∉S) {c:X} (hc:c∈S) :
    (g.support.filter (fun x=>x∉S ∧ g x∉S)).card=g.support.card-6 ∧
      (g.support.filter (fun x=>(x=c ∧ g x∉S) ∨ (x∉S ∧ g x=c))).card=2 := by
  constructor
  · simpa [hcard] using ManningEdgeGeometry.outer_edges_card_of_no_internal g S hS hn
  · apply ManningEdgeGeometry.distinguished_edges_card_two g S hc (hS hc) (hn c hc)
    intro hp
    have h := hn (g.symm c) hp
    exact h (by simpa using hc)

theorem three_cycle_edge_cards
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : Perm X) (S : Finset X) (hS : S⊆g.support) (hcard : S.card=3)
    {a c:X} (ha:a∈S) (hga:g a∈S) (hgc:g c=a) (hc:c∉S)
    (hinternal : S.filter (fun x=>g x∈S)={a}) :
    (g.support.filter (fun x=>x∉S ∧ g x∉S)).card=g.support.card-5 ∧
      (g.support.filter (fun x=>(x=a ∧ g x∉S) ∨ (x∉S ∧ g x=a))).card=1 := by
  constructor
  · have h := ManningEdgeGeometry.outer_edges_card_identity g S hS
    rw [hcard,hinternal,Finset.card_singleton] at h
    omega
  · apply ManningEdgeGeometry.distinguished_edges_card_one g S (hS ha) hga
    have he : g.symm a=c := g.injective ((g.apply_symm_apply a).trans hgc.symm)
    simpa [he] using hc

end FiveTransitive.ManningTripleGeometry

end CFSG
