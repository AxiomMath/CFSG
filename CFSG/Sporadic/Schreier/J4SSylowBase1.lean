
module

public import CFSG.Sporadic.Schreier.J4SSylowBase

import Mathlib.Tactic.IrreducibleDef
public import CFSG.Sporadic.Schreier.J4SSylowCheck
public import CFSG.Sporadic.Schreier.J4SLocalNodesBase1
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem actsBy_one : ActsBy 1 (idRows 11) := fun a => by
  rw [η_congr (toVecD_app11_idRows a)]
  group

theorem actsBy_mul
    {g h : J} {C D : Array ℕ} (hg : ActsBy g C) (hh : ActsBy h D) :
    ActsBy (g * h) (comp11 C D) := fun a => by
  rw [η_congr (toVecD_app11_comp11 C D a), ← hg, ← hh]
  group

theorem cols_eq_of_actsBy
    {g : J} {C D : Array ℕ} (hC : ActsBy g C) (hD : ActsBy g D)
    (hCs : C.size = 11) (hDs : D.size = 11) (hCl : ∀ j < 11, C[j]! < 2048)
    (hDl : ∀ j < 11, D[j]! < 2048) : C = D := by
  have hCb : ∀ j < 11, C[j]?.getD 0 < 2 ^ 11 := fun j hj => by
    rw [← getElem!_eq_getD']; exact hCl j hj
  have hDb : ∀ j < 11, D[j]?.getD 0 < 2 ^ 11 := fun j hj => by
    rw [← getElem!_eq_getD']; exact hDl j hj
  refine Array.ext (by rw [hCs, hDs]) fun j h1 h2 => ?_
  have hj : j < 11 := hCs ▸ h1
  have e : app11 C (2 ^ j) = app11 D (2 ^ j) :=
    η_injOn (vecMulN_lt hCb _) (vecMulN_lt hDb _) ((hC (2 ^ j)).symm.trans (hD (2 ^ j)))
  rw [app11_two_pow hCb hj, app11_two_pow hDb hj, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2] at e
  exact e

theorem kgen_acts
    {i : ℕ} (hi : i < 4) : ActsBy (kgen i) generatorColumns[i]! := fun a => by
  rw [kgen_def, ← genCols_all i hi]
  exact word_conj_η_cols (fiveGenWords[i]!) a

theorem exists_uElt :
    ∀ e < 1024, ∃ g ∈ U, ActsBy g elementColumns[e]! := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exact ⟨1, U.one_mem, elem_zero ▸ actsBy_one⟩
    · obtain ⟨-, -, hpar, -⟩ := elem_all e he
      obtain ⟨hp, hg, heq⟩ := hpar hpos
      obtain ⟨g, hgU, hgA⟩ := ih _ hp (by omega)
      refine ⟨g * kgen (discoveryParents[e]!)[1]!, U.mul_mem hgU (kgen_mem_U ⟨_, hg⟩), ?_⟩
      rw [heq]
      exact actsBy_mul hgA (kgen_acts hg)

@[expose] def uElt
    (e : ℕ) : J := if h : e < 1024 then Classical.choose (exists_uElt e h) else 1

theorem uElt_spec
    {e : ℕ} (he : e < 1024) : uElt e ∈ U ∧ ActsBy (uElt e) elementColumns[e]! := by
  rw [uElt, dite_eq_left he]
  exact Classical.choose_spec (exists_uElt e he)

theorem uElt_mem_U
    (e : ℕ) : uElt e ∈ U := by
  by_cases he : e < 1024
  · exact (uElt_spec he).1
  · rw [uElt, dite_eq_right he]
    exact U.one_mem

theorem uElt_acts
    {e : ℕ} (he : e < 1024) : ActsBy (uElt e) elementColumns[e]! := (uElt_spec he).2

theorem uElt_injOn
    {e e' : ℕ} (he : e < 1024) (he' : e' < 1024) (h : uElt e = uElt e') :
    e = e' := by
  obtain ⟨hs, hl, -⟩ := elem_all e he
  obtain ⟨hs', hl', -⟩ := elem_all e' he'
  have hcols : elementColumns[e]! = elementColumns[e']! :=
    cols_eq_of_actsBy (uElt_acts he) (h ▸ uElt_acts he') hs hs' hl hl'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact elem_distinct e' he' e hlt hcols
  · exact elem_distinct e he e' hlt hcols.symm

theorem conj_vS
    {e : ℕ} (he : e < 1024) :
    uElt e * vS * (uElt e)⁻¹ = η (app11 elementColumns[e]! 4) :=
  uElt_acts he 4

theorem conjGen_le_N : conjGen ≤ N := by
  rw [conjGen, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact conj_mem_N_of_mem_K (U_le_K hg) (η_mem_N 4)

theorem conjGen_eq_N :
    conjGen = N := by
  refine Subgroup.eq_of_le_of_card_ge conjGen_le_N ?_
  have hB : ∀ j < 11, η normalOrbitSpanBasis.toArray[j]! ∈ conjGen := by
    intro j hj
    obtain ⟨hlt, heq⟩ := span_all j hj
    rw [← heq, ← conj_vS hlt]
    exact Subgroup.subset_closure ⟨_, uElt_mem_U _, rfl⟩
  have hmem : ∀ c, η (app11 normalOrbitSpanBasis.toArray c) ∈ conjGen := by
    intro c
    rw [← prod_bits_eq η η_xor]
    refine conjGen.list_prod_mem fun m hm => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
    split_ifs
    · exact hB j j.isLt
    · exact conjGen.one_mem
  have hlt : ∀ c, app11 normalOrbitSpanBasis.toArray c < 2 ^ 11 := fun c =>
    vecMulN_lt (fun j hj => by rw [← getElem!_eq_getD']; exact span_size.2 j hj) c
  have hf : Function.Injective fun c : Fin 2048 =>
      (⟨η (app11 normalOrbitSpanBasis.toArray c), hmem c⟩ : conjGen) := by
    intro c c' h
    have h' := Subtype.ext_iff.1 h
    dsimp only at h'
    have := η_injOn (hlt _) (hlt _) h'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (fun e => hne (Fin.ext e)) with h1 | h1
    · exact span_distinct c' c'.isLt c h1 this
    · exact span_distinct c c.isLt c' h1 this.symm
  have := Nat.card_le_card_of_injective _ hf
  rw [Nat.card_fin] at this
  rw [card_N]
  exact this

theorem N_le_S0 : N ≤ S0 := by
  rw [← conjGen_eq_N, conjGen, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact S0.mul_mem (S0.mul_mem (U_le_S0 hg) vS_mem_S0) (S0.inv_mem (U_le_S0 hg))

@[expose] def NU : Subgroup J where
  carrier := {s | ∃ n ∈ N, ∃ u ∈ U, s = n * u}
  mul_mem' := by
    rintro _ _ ⟨n, hn, u, hu, rfl⟩ ⟨n', hn', u', hu', rfl⟩
    refine ⟨n * (u * n' * u⁻¹), N.mul_mem hn (conj_mem_N_of_mem_K (U_le_K hu) hn'), u * u',
      U.mul_mem hu hu', by group⟩
  one_mem' := ⟨1, N.one_mem, 1, U.one_mem, (one_mul 1).symm⟩
  inv_mem' := by
    rintro _ ⟨n, hn, u, hu, rfl⟩
    have h := conj_mem_N_of_mem_K (U_le_K (U.inv_mem hu)) (N.inv_mem hn)
    rw [inv_inv] at h
    exact ⟨u⁻¹ * n⁻¹ * u, h, u⁻¹, U.inv_mem hu, by group⟩

theorem S0_eq_NU : S0 = NU := by
  refine le_antisymm ?_ ?_
  · rw [S0, Subgroup.closure_le]
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact ⟨vS, η_mem_N 4, 1, U.one_mem, (mul_one vS).symm⟩
    · exact ⟨1, N.one_mem, kgen i, kgen_mem_U i, (one_mul _).symm⟩
  · rintro _ ⟨n, hn, u, hu, rfl⟩
    exact S0.mul_mem (N_le_S0 hn) (U_le_S0 hu)

theorem N_inf_U : N ⊓ U = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have h : g ∈ K ⊓ N := ⟨U_le_K hg.2, hg.1⟩
  rwa [K_inf_N] at h

theorem exists_mul_of_mem_S0
    {s : J} (hs : s ∈ S0) : ∃ n ∈ N, ∃ u ∈ U, s = n * u := by
  rw [S0_eq_NU] at hs
  exact hs

theorem mul_unique
    {n n' u u' : J} (hn : n ∈ N) (hn' : n' ∈ N) (hu : u ∈ U) (hu' : u' ∈ U)
    (h : n * u = n' * u') : n = n' ∧ u = u' := by
  have h1 : n'⁻¹ * n = u' * u⁻¹ := by
    rw [show n'⁻¹ * n = n'⁻¹ * (n * u) * u⁻¹ by group, h]
    group
  have h3 : n'⁻¹ * n ∈ U := by rw [h1]; exact U.mul_mem hu' (U.inv_mem hu)
  have h2 : n'⁻¹ * n ∈ N ⊓ U := ⟨N.mul_mem (N.inv_mem hn') hn, h3⟩
  rw [N_inf_U, Subgroup.mem_bot] at h2
  have e1 : n = n' := by rw [← mul_inv_cancel_left n' n, h2, mul_one]
  refine ⟨e1, ?_⟩
  rw [e1] at h
  exact (mul_left_cancel h)

theorem N_normal_in_S0 :
    (N.subgroupOf S0).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer N_le_S0).2 ?_
  rw [S0, Subgroup.closure_le]
  rintro _ (rfl | ⟨i, rfl⟩)
  · exact Subgroup.le_normalizer (η_mem_N 4)
  · exact K_le_normalizer (kgen_mem_K i)

theorem N_sup_U : N ⊔ U = S0 := by
  refine le_antisymm (sup_le N_le_S0 U_le_S0) fun s hs => ?_
  obtain ⟨n, hn, u, hu, rfl⟩ := exists_mul_of_mem_S0 hs
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hu)

end CFSG.Sporadic.J4Schreier
