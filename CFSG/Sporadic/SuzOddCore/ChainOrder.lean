module

public import CFSG.Certificates.SchreierChainOrderMembership
public import Mathlib.Algebra.BigOperators.Fin

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.RawSchreierDatum

variable {n : ℕ} {Q : RawSchreierDatum n}

structure ChainEqns (Q : RawSchreierDatum n) : Prop where
  init : ∀ j : Fin Q.originalCount,
    Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j
  words : ∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
    Q.strong.get j = Q.derivationValue j hj
  terminal : ∀ s ∈ Q.levelGenerators Q.baseCount, s = 1

namespace ChainEqns

theorem strong_mem (h : ChainEqns Q) (j : Fin Q.strongCount) :
    Q.strong.get j ∈ Q.originalSubgroup := by
  have all : ∀ a : ℕ, ∀ j : Fin Q.strongCount,
      j.val = a → Q.strong.get j ∈ Q.originalSubgroup := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja
      by_cases hj : j.val < Q.originalCount
      · let l : Fin Q.originalCount := ⟨j.val, hj⟩
        have hcast : Fin.castLE Q.originalCount_le l = j := Fin.ext rfl
        rw [← hcast, h.init l]
        exact Subgroup.subset_closure (schreier_vector_get_mem_toList Q.original l)
      · rw [h.words j (Nat.le_of_not_gt hj)]
        apply schreierWordValue_mem_subgroup Q.strong.get
          (Nat.le_of_lt j.isLt) (Q.derivation j (Nat.le_of_not_gt hj)) Q.originalSubgroup
        intro l
        exact ih l.val (by omega) ⟨l.val, l.isLt.trans j.isLt⟩ rfl
  exact all j.val j rfl

theorem levelSubgroup_zero (h : ChainEqns Q) : Q.levelSubgroup 0 = Q.originalSubgroup := by
  rw [RawSchreierDatum.levelSubgroup, Q.levelGenerators_zero]
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro g hg
    obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get Q.strong g).1 hg
    exact h.strong_mem j
  · apply (Subgroup.closure_le _).2
    intro g hg
    obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get Q.original g).1 hg
    rw [← h.init j]
    exact Subgroup.subset_closure
      (schreier_vector_get_mem_toList Q.strong (Fin.castLE Q.originalCount_le j))

theorem levelSubgroup_terminal (h : ChainEqns Q) : Q.levelSubgroup Q.baseCount = ⊥ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro s hs
    exact Subgroup.mem_bot.2 (h.terminal s hs)
  · exact bot_le

end ChainEqns

@[expose] def orbProd (Q : RawSchreierDatum n) (i : ℕ) : ℕ :=
  (((List.finRange Q.baseCount).drop i).map fun j => Nat.card (Q.orbitPoints j)).prod

theorem orbProd_terminal (Q : RawSchreierDatum n) : orbProd Q Q.baseCount = 1 := by
  have hdrop : (List.finRange Q.baseCount).drop Q.baseCount = [] :=
    List.drop_eq_nil_iff.2 (by simp)
  simp only [orbProd, hdrop, List.map_nil, List.prod_nil]

theorem orbProd_succ (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    orbProd Q i.val = Nat.card (Q.orbitPoints i) * orbProd Q (i.val + 1) := by
  have hlen : i.val < (List.finRange Q.baseCount).length := by simp
  have hentry : (List.finRange Q.baseCount)[i.val] = i := by
    apply Fin.ext
    simp only [List.getElem_finRange, Fin.val_cast]
  rw [orbProd, List.drop_eq_getElem_cons hlen, hentry, List.map_cons, List.prod_cons]
  rfl

theorem orbProd_zero (Q : RawSchreierDatum n) :
    orbProd Q 0 = ∏ i : Fin Q.baseCount, Nat.card (Q.orbitPoints i) := by
  rw [orbProd, List.drop_zero, Fin.prod_univ_def]

@[expose] def levelStab (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Q.levelSubgroup i.val ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i)

theorem card_levelSubgroup_eq (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Nat.card (Q.levelSubgroup i.val) = Nat.card (Q.orbitPoints i) * Nat.card (levelStab Q i) := by
  have hcard := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (Q.levelSubgroup i.val) (Q.base.get i))
  rw [Nat.card_prod, ← Q.orbitPoints_eq_orbit i] at hcard
  rw [← hcard]
  congr 1
  refine Nat.card_congr ?_
  exact
    { toFun := fun g => ⟨g.val.val, g.val.property, MulAction.mem_stabilizer_iff.2 g.property⟩
      invFun := fun g => ⟨⟨g.val, g.property.1⟩, MulAction.mem_stabilizer_iff.2 g.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_succ_le_levelStab (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    Nat.card (Q.levelSubgroup (i.val + 1)) ≤ Nat.card (levelStab Q i) :=
  Subgroup.card_le_of_le (Q.levelSubgroup_succ_le_stabilizer i)

theorem card_orbitPoints_pos (Q : RawSchreierDatum n) (i : Fin Q.baseCount) :
    0 < Nat.card (Q.orbitPoints i) := by
  rw [Q.orbitPoints_eq_orbit i]
  have : Nonempty (MulAction.orbit (Q.levelSubgroup i.val) (Q.base.get i)) :=
    ⟨⟨_, MulAction.mem_orbit_self _⟩⟩
  exact Nat.card_pos

namespace ChainEqns

theorem card_ge (h : ChainEqns Q) :
    ∀ d i, i + d = Q.baseCount → orbProd Q i ≤ Nat.card (Q.levelSubgroup i) ∧
      (Nat.card (Q.levelSubgroup i) = orbProd Q i → ∀ j : Fin Q.baseCount, i ≤ j.val →
        Nat.card (levelStab Q j) = Nat.card (Q.levelSubgroup (j.val + 1))) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hi' : i = Q.baseCount := by omega
    subst hi'
    refine ⟨?_, fun _ j hj => absurd j.isLt (by omega)⟩
    rw [h.levelSubgroup_terminal, Subgroup.card_bot, orbProd_terminal]
  | succ d ih =>
    intro i hi
    let j0 : Fin Q.baseCount := ⟨i, by omega⟩
    obtain ⟨hge, heq⟩ := ih (i + 1) (by omega)
    have hcard := card_levelSubgroup_eq Q j0
    have hle := card_succ_le_levelStab Q j0
    have hpos := card_orbitPoints_pos Q j0
    have hprod := orbProd_succ Q j0
    change Nat.card (Q.levelSubgroup i) = _ at hcard
    change Nat.card (Q.levelSubgroup (i + 1)) ≤ _ at hle
    change orbProd Q i = _ at hprod
    refine ⟨?_, fun hE j hj => ?_⟩
    · rw [hprod, hcard]
      exact Nat.mul_le_mul_left _ (hge.trans hle)
    · rw [hprod, hcard] at hE
      have hs : Nat.card (levelStab Q j0) = orbProd Q (i + 1) :=
        Nat.eq_of_mul_eq_mul_left hpos hE
      have hsucc : Nat.card (Q.levelSubgroup (i + 1)) = orbProd Q (i + 1) :=
        le_antisymm (hle.trans hs.le) hge
      rcases Nat.lt_or_ge i j.val with hlt | hle'
      · exact heq hsucc j hlt
      · have hj' : j = j0 := Fin.ext (by simp [j0]; omega)
        subst hj'
        exact hs.trans hsucc.symm

theorem stab_eq (h : ChainEqns Q)
    (hcard : Nat.card Q.originalSubgroup ≤ ∏ i : Fin Q.baseCount, Nat.card (Q.orbitPoints i))
    (i : Fin Q.baseCount) : Q.levelSubgroup (i.val + 1) = levelStab Q i := by
  obtain ⟨hge, heq⟩ := h.card_ge Q.baseCount 0 (by omega)
  rw [h.levelSubgroup_zero] at hge heq
  rw [orbProd_zero] at hge heq
  have hc := heq (le_antisymm hcard hge) i (Nat.zero_le _)
  exact Subgroup.eq_of_le_of_card_ge (Q.levelSubgroup_succ_le_stabilizer i) hc.le

theorem strip_mem_next (h : ChainEqns Q)
    (hcard : Nat.card Q.originalSubgroup ≤ ∏ i : Fin Q.baseCount, Nat.card (Q.orbitPoints i))
    (i : Fin Q.baseCount) (g : Equiv.Perm (Fin n)) (hg : g ∈ Q.levelSubgroup i.val) :
    ∃ t, Q.transversal? i (g (Q.base.get i)) = some t ∧
      t⁻¹ * g ∈ Q.levelSubgroup (i.val + 1) := by
  have hx : g (Q.base.get i) ∈ Q.orbitPoints i := by
    rw [Q.orbitPoints_eq_orbit i]
    exact MulAction.mem_orbit_iff.2 ⟨⟨g, hg⟩, rfl⟩
  obtain ⟨t, ht, htH, _, htb⟩ := Q.orbitPoint_transversal i (g (Q.base.get i)) hx
  refine ⟨t, ht, ?_⟩
  rw [h.stab_eq hcard i]
  refine ⟨(Q.levelSubgroup i.val).mul_mem ((Q.levelSubgroup i.val).inv_mem htH) hg, ?_⟩
  apply MulAction.mem_stabilizer_iff.2
  change t⁻¹ (g (Q.base.get i)) = Q.base.get i
  rw [← htb]
  simp

theorem siftResidual_eq_one (h : ChainEqns Q)
    (hcard : Nat.card Q.originalSubgroup ≤ ∏ i : Fin Q.baseCount, Nat.card (Q.orbitPoints i))
    (i : ℕ) (hi : i ≤ Q.baseCount) (g : Equiv.Perm (Fin n)) (hg : g ∈ Q.levelSubgroup i) :
    schreierSiftResidual (Q.siftLevels Q.orbitTables i) g = some 1 := by
  have go : ∀ d i, i + d = Q.baseCount → ∀ g : Equiv.Perm (Fin n),
      g ∈ Q.levelSubgroup i →
      schreierSiftResidual (Q.siftLevels Q.orbitTables i) g = some 1 := by
    intro d
    induction d with
    | zero =>
      intro i hi g hg
      have hi' : i = Q.baseCount := by omega
      subst i
      rw [h.levelSubgroup_terminal] at hg
      have hg' : g = 1 := Subgroup.mem_bot.1 hg
      subst g
      have hdrop : (List.finRange Q.baseCount).drop Q.baseCount = [] :=
        List.drop_eq_nil_iff.2 (by simp)
      simp only [siftLevels, hdrop, List.map_nil, schreierSiftResidual]
    | succ d ih =>
      intro i hi g hg
      let j : Fin Q.baseCount := ⟨i, by omega⟩
      obtain ⟨t, ht, hnext⟩ := h.strip_mem_next hcard j g hg
      rw [Q.siftResidual_strip j g t ht]
      exact ih (i + 1) (by omega) (t⁻¹ * g) hnext
  exact go (Q.baseCount - i) i (by omega) g hg

theorem validSchreier (h : ChainEqns Q)
    (hcard : Nat.card Q.originalSubgroup ≤ ∏ i : Fin Q.baseCount, Nat.card (Q.orbitPoints i)) :
    ValidSchreier Q := by
  refine (validSchreier_iff Q).2 ⟨h.init, h.words, h.terminal, ?_⟩
  intro i x tx htx s hs
  have hsH : s ∈ Q.levelSubgroup i.val :=
    SchreierOrbitState.signed_steps_mem_closure (Q.levelGenerators i.val) s hs
  have htx' : Q.transversal? i x = some tx := htx
  obtain ⟨htxH, -, htxb⟩ := Q.transversal_sound i x tx htx'
  have hsx : s x ∈ Q.orbitPoints i := by
    rw [Q.orbitPoints_eq_orbit i]
    refine MulAction.mem_orbit_iff.2 ⟨⟨s * tx, (Q.levelSubgroup i.val).mul_mem hsH htxH⟩, ?_⟩
    change (s * tx) (Q.base.get i) = s x
    rw [Equiv.Perm.mul_apply, htxb]
  obtain ⟨ty, hty, htyH, -, htyb⟩ := Q.orbitPoint_transversal i (s x) hsx
  refine ⟨ty, hty, ?_⟩
  have hmem : ty⁻¹ * s * tx ∈ Q.levelSubgroup (i.val + 1) := by
    rw [h.stab_eq hcard i]
    refine ⟨(Q.levelSubgroup i.val).mul_mem ((Q.levelSubgroup i.val).mul_mem
      ((Q.levelSubgroup i.val).inv_mem htyH) hsH) htxH, ?_⟩
    apply MulAction.mem_stabilizer_iff.2
    change (ty⁻¹ * s * tx) (Q.base.get i) = Q.base.get i
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, htxb, ← htyb]
    exact Equiv.symm_apply_apply ty (Q.base.get i)
  exact (schreierSiftSucceeds_eq_true_iff _ _).2
    (h.siftResidual_eq_one hcard (i.val + 1) (by omega) _ hmem)

end ChainEqns

end CFSG.Sporadic.SuzOddCore
