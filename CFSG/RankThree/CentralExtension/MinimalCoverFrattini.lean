module

public import CFSG.RankThree.CentralExtension.CenterFixingAutSplit
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.CentralExtension

open Subgroup

theorem conjNormal_eq_of_isPerfect_of_isCyclic {Y : Type*} [Group Y] [Group.IsPerfect Y]
    {Z : Subgroup Y} [Z.Normal] [IsCyclic Z] (y : Y) (z : Z) : MulAut.conjNormal y z = z := by
  let f : Y →* (ZMod (Nat.card Z))ˣ :=
    (IsCyclic.mulAutMulEquiv (G := Z)).toMonoidHom.comp MulAut.conjNormal
  have hy : y ∈ f.ker := by
    have h := Abelianization.commutator_subset_ker f
    rw [Group.IsPerfect.commutator_eq_top] at h
    exact h (mem_top y)
  have h1 : MulAut.conjNormal y = (1 : MulAut Z) := by
    have h2 : (IsCyclic.mulAutMulEquiv (G := Z)) (MulAut.conjNormal y) = 1 := hy
    rwa [MulEquiv.map_eq_one_iff] at h2
  rw [h1]
  rfl

theorem perfect_minimal_cover_excludes_extraspecial_frattini_subgroup {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (P : Subgroup Y) [P.Normal]
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤) :
    ¬ ∃ D : Subgroup Y, D.Normal ∧ D ≤ P ∧ (∀ d ∈ D, d ^ p = 1) ∧
      center D = commutator D ∧ Nat.card (center D) = p := by
  rintro ⟨D, hDn, hDP, hDexp, hDZ, hDcard⟩
  have hexp : ∀ d : D, d ^ p = 1 := fun d => Subtype.ext (by simpa using hDexp d d.2)
  obtain ⟨ε⟩ := CFSG.OddSolvableUnitary.nonempty_center_mulEquiv hDcard
  have _ : Module (ZMod p) (Additive (Abelianization D)) :=
    AddCommGroup.zmodModule (CFSG.OddSolvableUnitary.nsmul_abelianization_eq_zero hexp)
  set Z : Subgroup Y := (center D).map D.subtype with hZdef
  have : IsCyclic Z := by
    refine isCyclic_of_prime_card (p := p) ?_
    rw [hZdef, card_map_of_injective D.subtype_injective, hDcard]
  have hfix : ∀ y : Y, ∀ z ∈ center D, MulAut.conjNormal y z = z := by
    intro y z hz
    have h1 := congrArg Subtype.val
      (conjNormal_eq_of_isPerfect_of_isCyclic y (⟨z, z, hz, rfl⟩ : Z))
    rw [MulAut.conjNormal_apply] at h1
    exact Subtype.ext (by rw [MulAut.conjNormal_apply]; exact h1)
  let c : Y →* centerFixingAut D :=
    (MulAut.conjNormal : Y →* MulAut D).codRestrict (centerFixingAut D) hfix
  have hc : ∀ y, (c y : MulAut D) = MulAut.conjNormal y := fun _ => rfl
  obtain ⟨-, -, hker, ⟨s, hs⟩, -⟩ :=
    odd_exponent_extraspecial_center_fixing_automorphism_split hp2 hexp hDZ ε
  set lam := centerFixingAutSp hDZ ε with hlam
  have hsec : ∀ t, lam (s t) = t := fun t => DFunLike.congr_fun hs t
  have hcD : ∀ d : D, c d ∈ lam.ker := by
    intro d
    rw [hker, mem_subgroupOf, hc, MulAut.conjNormal_val]
    exact ⟨d, rfl⟩
  set M : Subgroup Y := s.range.comap c with hMdef
  have hsup : D ⊔ M = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : c y * (s (lam (c y)))⁻¹ ∈ lam.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsec, mul_inv_cancel]
    rw [hker, mem_subgroupOf] at h1
    obtain ⟨d, hd⟩ := h1
    have hdy : (d : Y)⁻¹ * y ∈ M := by
      rw [hMdef, mem_comap]
      refine ⟨lam (c y), ?_⟩
      apply Subtype.ext
      rw [map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv, hc d, MulAut.conjNormal_val,
        hd]
      simp
    have h2 := mul_mem_sup d.2 hdy
    rwa [mul_inv_cancel_left] at h2
  have hMtop : M.map (QuotientGroup.mk' P) = ⊤ := by
    refine eq_top_iff.2 fun q _ => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P q
    have hy : y ∈ D ⊔ M := by rw [hsup]; exact mem_top y
    obtain ⟨d, hd, m, hm, rfl⟩ := mem_sup_of_normal_left.1 hy
    refine ⟨m, hm, ?_⟩
    rw [map_mul, show (QuotientGroup.mk' P) d = 1 from (QuotientGroup.eq_one_iff d).2 (hDP hd),
      one_mul]
  have hM := hmin M hMtop
  have hDc : ∀ d : D, d ∈ center D := by
    intro d
    have hdM : (d : Y) ∈ M := hM ▸ mem_top (d : Y)
    obtain ⟨t, ht⟩ := hdM
    have h1 := hcD d
    rw [MonoidHom.mem_ker, ← ht, hsec] at h1
    rw [h1, map_one] at ht
    have h2 : MulAut.conj d = 1 := by
      rw [← MulAut.conjNormal_val, ← hc]
      exact congrArg Subtype.val ht.symm
    refine mem_center_iff.2 fun g => ?_
    have h3 := congrArg (fun φ : MulAut D => φ g) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    calc g * d = d * g * d⁻¹ * d := by rw [h3]
      _ = d * g := by group
  have hcomm : commutator D = ⊥ := by
    rw [eq_bot_iff, _root_.commutator_def, commutator_le]
    intro a _ b _
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.1 (hDc b) a)
  rw [← hDZ] at hcomm
  rw [hcomm, card_bot] at hDcard
  exact hp.out.one_lt.ne hDcard

end CFSG.RankThree.CentralExtension
