module

public import CFSG.Quasithin.H13.A7HyperplaneBasic
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm CFSG.Quasithin.SteinbergCB

@[expose] def pairE (i j : Fin 7) : Fin 7 → ZMod 2 := Pi.single i 1 + Pi.single j 1

@[expose] def cyc234 : Perm (Fin 7) := swap 2 4 * swap 2 3

@[expose] def cyc456 : Perm (Fin 7) := swap 4 6 * swap 4 5

@[expose] def inv0123 : Perm (Fin 7) := swap 0 1 * swap 2 3

@[expose] def moveOne (j : Fin 7) : Perm (Fin 7) := swap 1 (if j = 2 then 3 else 2) * swap 1 j

theorem cyc234_mem : cyc234 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide +kernel

theorem cyc456_mem : cyc456 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide +kernel

theorem inv0123_mem : inv0123 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide +kernel

theorem moveOne_mem : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 → moveOne j ∈ alternatingGroup (Fin 7) := by
  intro j
  rw [mem_alternatingGroup]
  revert j
  decide +kernel

theorem permAct7_moveOne : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 →
    permAct7 (moveOne j) (pairE 0 1) = pairE 0 j := by
  decide +kernel

theorem pairE01_fixed : permAct7 cyc234 (pairE 0 1) = pairE 0 1 ∧
    permAct7 cyc456 (pairE 0 1) = pairE 0 1 ∧ permAct7 inv0123 (pairE 0 1) = pairE 0 1 := by
  decide +kernel

theorem fixed_pairE01 : ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 → permAct7 cyc234 v = v →
    permAct7 cyc456 v = v → permAct7 inv0123 v = v → v = 0 ∨ v = pairE 0 1 := by
  decide +kernel

theorem eq_sum_pairE : ∀ v : Fin 7 → ZMod 2, ∑ i, v i = 0 →
    v = (if v 1 = 1 then pairE 0 1 else 0) + (if v 2 = 1 then pairE 0 2 else 0) +
      (if v 3 = 1 then pairE 0 3 else 0) + (if v 4 = 1 then pairE 0 4 else 0) +
      (if v 5 = 1 then pairE 0 5 else 0) + (if v 6 = 1 then pairE 0 6 else 0) := by
  decide +kernel

theorem pairE01_ne_zero : pairE 0 1 ≠ 0 := by
  decide +kernel

theorem pairE_mem (i j : Fin 7) : pairE i j ∈ evenWeight 7 :=
  pair_mem_evenWeight i j

theorem eq_self_of_commute_alternating {g : (Fin 7 → ZMod 2) → Fin 7 → ZMod 2}
    (hgE : ∀ e ∈ evenWeight 7, g e ∈ evenWeight 7)
    (hgadd : ∀ e ∈ evenWeight 7, ∀ e' ∈ evenWeight 7, g (e + e') = g e + g e')
    (hginj : ∀ e ∈ evenWeight 7, g e = 0 → e = 0)
    (hgc : ∀ σ ∈ alternatingGroup (Fin 7), ∀ e ∈ evenWeight 7,
      g (permAct7 σ e) = permAct7 σ (g e)) :
    ∀ e ∈ evenWeight 7, g e = e := by
  have h0E : (0 : Fin 7 → ZMod 2) ∈ evenWeight 7 := Submodule.zero_mem _
  have hg0 : g 0 = 0 := by
    have h := hgadd 0 h0E 0 h0E
    rw [add_zero] at h
    exact left_eq_add.1 h
  have h01 : g (pairE 0 1) = pairE 0 1 := by
    obtain ⟨h1, h2, h3⟩ := pairE01_fixed
    have hw := hgE _ (pairE_mem 0 1)
    have hfix : ∀ σ ∈ alternatingGroup (Fin 7), permAct7 σ (pairE 0 1) = pairE 0 1 →
        permAct7 σ (g (pairE 0 1)) = g (pairE 0 1) := by
      intro σ hσ hf
      rw [← hgc σ hσ _ (pairE_mem 0 1), hf]
    rcases fixed_pairE01 _ hw (hfix _ cyc234_mem h1) (hfix _ cyc456_mem h2)
        (hfix _ inv0123_mem h3) with h | h
    · exact absurd (hginj _ (pairE_mem 0 1) h) pairE01_ne_zero
    · exact h
  have hpair : ∀ j : Fin 7, j ≠ 0 → g (pairE 0 j) = pairE 0 j := by
    intro j hj0
    by_cases hj1 : j = 1
    · subst hj1
      exact h01
    rw [← permAct7_moveOne j hj0 hj1, hgc _ (moveOne_mem j hj0 hj1) _ (pairE_mem 0 1), h01]
  have hterm : ∀ (j : Fin 7) (c : ZMod 2), j ≠ 0 →
      g (if c = 1 then pairE 0 j else 0) = if c = 1 then pairE 0 j else 0 := by
    intro j c hj
    split_ifs
    · exact hpair j hj
    · exact hg0
  have htermE : ∀ (j : Fin 7) (c : ZMod 2),
      (if c = 1 then pairE 0 j else 0) ∈ evenWeight 7 := by
    intro j c
    split_ifs
    · exact pairE_mem 0 j
    · exact h0E
  intro e he
  rw [eq_sum_pairE e he]
  set t1 := (if e 1 = 1 then pairE 0 1 else 0) with ht1
  set t2 := (if e 2 = 1 then pairE 0 2 else 0) with ht2
  set t3 := (if e 3 = 1 then pairE 0 3 else 0) with ht3
  set t4 := (if e 4 = 1 then pairE 0 4 else 0) with ht4
  set t5 := (if e 5 = 1 then pairE 0 5 else 0) with ht5
  set t6 := (if e 6 = 1 then pairE 0 6 else 0) with ht6
  have m1 := htermE 1 (e 1)
  have m2 := htermE 2 (e 2)
  have m3 := htermE 3 (e 3)
  have m4 := htermE 4 (e 4)
  have m5 := htermE 5 (e 5)
  have m6 := htermE 6 (e 6)
  have m12 := Submodule.add_mem _ m1 m2
  have m123 := Submodule.add_mem _ m12 m3
  have m1234 := Submodule.add_mem _ m123 m4
  have m12345 := Submodule.add_mem _ m1234 m5
  rw [hgadd _ m12345 _ m6, hgadd _ m1234 _ m5, hgadd _ m123 _ m4, hgadd _ m12 _ m3,
    hgadd _ m1 _ m2, hterm 1 _ (by decide), hterm 2 _ (by decide), hterm 3 _ (by decide),
    hterm 4 _ (by decide), hterm 5 _ (by decide), hterm 6 _ (by decide)]

theorem eq_of_permAct7_eq {σ ρ : Perm (Fin 7)}
    (h : ∀ e ∈ evenWeight 7, permAct7 σ e = permAct7 ρ e) : σ = ρ := by
  have h1 : ρ⁻¹ * σ = 1 := by
    apply eq_one_of_permAct7_fix
    intro e he
    rw [permAct7_mul, h e he, ← permAct7_mul, inv_mul_cancel, permAct7_one]
  rw [← inv_mul_eq_one.1 h1]

theorem exists_perm_of_normalizes_alternating {f : (Fin 7 → ZMod 2) → Fin 7 → ZMod 2}
    (hfE : ∀ e ∈ evenWeight 7, f e ∈ evenWeight 7)
    (hfadd : ∀ e ∈ evenWeight 7, ∀ e' ∈ evenWeight 7, f (e + e') = f e + f e')
    (hfinj : ∀ e ∈ evenWeight 7, f e = 0 → e = 0)
    (hfsurj : ∀ e ∈ evenWeight 7, ∃ e' ∈ evenWeight 7, f e' = e)
    (hfn : ∀ σ ∈ alternatingGroup (Fin 7), ∃ σ' ∈ alternatingGroup (Fin 7),
      ∀ e ∈ evenWeight 7, f (permAct7 σ e) = permAct7 σ' (f e)) :
    ∃ τ : Perm (Fin 7), ∀ e ∈ evenWeight 7, f e = permAct7 τ e := by
  classical
  have huniq : ∀ a b : Perm (Fin 7), (∀ e ∈ evenWeight 7, permAct7 a (f e) = permAct7 b (f e)) →
      a = b := by
    intro a b h
    apply eq_of_permAct7_eq
    intro e he
    obtain ⟨e', he', rfl⟩ := hfsurj e he
    exact h e' he'
  let α : alternatingGroup (Fin 7) → alternatingGroup (Fin 7) := fun σ =>
    ⟨Classical.choose (hfn σ σ.2), (Classical.choose_spec (hfn σ σ.2)).1⟩
  have hα : ∀ σ : alternatingGroup (Fin 7), ∀ e ∈ evenWeight 7,
      f (permAct7 σ e) = permAct7 (α σ) (f e) := fun σ =>
    (Classical.choose_spec (hfn σ σ.2)).2
  have hαmul : ∀ σ ρ : alternatingGroup (Fin 7), α (σ * ρ) = α σ * α ρ := by
    intro σ ρ
    apply Subtype.ext
    apply huniq
    intro e he
    rw [← hα (σ * ρ) e he, Subgroup.coe_mul, Subgroup.coe_mul, permAct7_mul, permAct7_mul,
      hα σ _ (permAct7_mem_evenWeight _ he), hα ρ e he]
  let αh : alternatingGroup (Fin 7) →* alternatingGroup (Fin 7) :=
    { toFun := α
      map_one' := by
        apply Subtype.ext
        apply huniq
        intro e he
        rw [← hα 1 e he]
        simp [permAct7_one]
      map_mul' := hαmul }
  have hαinj : Function.Injective αh := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply eq_one_of_permAct7_fix
    intro e he
    have h1 : f (permAct7 σ e) = f e := by
      rw [hα σ e he]
      have : α σ = 1 := hσ
      rw [this]
      exact permAct7_one _
    have h2 : f (permAct7 σ e + e) = 0 := by
      rw [hfadd _ (permAct7_mem_evenWeight _ he) _ he, h1]
      exact fun_add_self_eq_zero _
    have h3 := hfinj _ (Submodule.add_mem _ (permAct7_mem_evenWeight _ he) he) h2
    calc permAct7 (σ : Perm (Fin 7)) e = permAct7 (σ : Perm (Fin 7)) e + e + e := by
          rw [add_assoc, fun_add_self_eq_zero, add_zero]
      _ = e := by rw [h3, zero_add]
  let αe : MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective αh hαinj.bijective_of_finite
  obtain ⟨τ, hτ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)).2 αe
  have hατ : ∀ σ : alternatingGroup (Fin 7), ((α σ : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      τ * σ * τ⁻¹ := by
    intro σ
    have h1 : αe σ = MulAut.conjNormal τ σ := by rw [hτ]
    have h2 : ((αe σ : alternatingGroup (Fin 7)) : Perm (Fin 7)) = τ * σ * τ⁻¹ := by
      rw [h1, MulAut.conjNormal_apply]
    exact h2
  refine ⟨τ, fun e he => ?_⟩
  have hS := eq_self_of_commute_alternating (g := fun e => permAct7 τ⁻¹ (f e))
    (fun e he => permAct7_mem_evenWeight _ (hfE e he))
    (fun e he e' he' => by simp only [hfadd e he e' he', map_add])
    (fun e he h => by
      apply hfinj e he
      have h' := congrArg (permAct7 τ) h
      rwa [← permAct7_mul, mul_inv_cancel, permAct7_one, map_zero] at h')
    (fun σ hσ e he => by
      show permAct7 τ⁻¹ (f (permAct7 σ e)) = permAct7 σ (permAct7 τ⁻¹ (f e))
      rw [hα ⟨σ, hσ⟩ e he, hατ ⟨σ, hσ⟩, ← permAct7_mul, ← permAct7_mul]
      congr 1
      group)
    e he
  have h' := congrArg (permAct7 τ) hS
  rwa [← permAct7_mul, mul_inv_cancel, permAct7_one] at h'

end CFSG.Quasithin.H13.A7
