module

public import CFSG.Sporadic.Co2Smith.GlNJKPerm

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native

@[expose] def njChBase : List (Fin 77) := [21, 1, 2, 3, 39, 25, 5]

theorem njChBase_eq : (njChBase.map Fin.val).toArray = Native.glNJChBase.toArray := rfl

section Groups


@[expose] noncomputable def qN (k : ℕ) : normalizer (Jc : Set K) :=
  if hk : k < 3 then ⟨qK k, qK_mem_N hk⟩ else 1

theorem qN_val {k : ℕ} (hk : k < 3) : (qN k : K) = qK k := by
  simp [qN, hk]

theorem rep_piK_qN {k : ℕ} (hk : k < 3) : Rep 77 Native.glNJPerm[k]! (piK (qN k)) := by
  intro x
  have e := piK_spec (qN k) x
  rw [qN_val hk, qK_conj_omK hk] at e
  exact (congrArg Fin.val (omK_injective e)).symm

theorem piK_Jc {g : normalizer (Jc : Set K)} (hg : (g : K) ∈ Jc) : piK g = 1 := by
  refine (chom_eq_one_iff omK_injective _ stable_normalizer g).2 fun k => ?_
  exact Jc_comm hg (omK_mem_Jc k)

@[expose] noncomputable def PQ : Subgroup (Equiv.Perm (Fin 77)) :=
  closure {piK (qN 0), piK (qN 1)}

theorem glNJChain_parts :
    2 ≤ Native.glNJChS.size ∧ Native.glNJChS[0]! = Native.glNJPerm[0]! ∧
      Native.glNJChS[1]! = Native.glNJPerm[1]! ∧
      rawChainOK 77 (Native.glNJChS.extract 0 2) Native.glNJChS
        (njChBase.map Fin.val).toArray Native.glNJChW 4 = true ∧
      (rawOrbitSizes 77 Native.glNJChS (njChBase.map Fin.val).toArray).prod = 11520 := by
  have h := glNJChain_check
  simp only [Native.glNJChainOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rw [njChBase_eq]
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

@[expose] noncomputable def njChain : RawSchreierDatum 77 :=
  RawSchreierDatum.ofArrays 77 (by norm_num) Native.glNJChS 2 glNJChain_parts.1 njChBase
    (by decide) Native.glNJChW


theorem card_njChain : Nat.card njChain.originalSubgroup = 11520 := by
  have h := glNJChain_parts.2.2.2.1
  rw [njChain, card_originalSubgroup_of_chainOK
    (chainArrays_ofArrays (chainCheckFacts h).strong_inv) (by norm_num) h,
    glNJChain_parts.2.2.2.2]

theorem njChain_eq : njChain.originalSubgroup = PQ := by
  rw [RawSchreierDatum.originalSubgroup, PQ]
  congr 1
  ext g
  simp only [njChain, Set.mem_ofPred_eq, RawSchreierDatum.mem_ofArrays_original,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  have hc := chainCheckFacts glNJChain_parts.2.2.2.1
  have h0 := (rep_permOfArr (hc.strong_inv 0 (by have := glNJChain_parts.1; omega))).1
  have h1 := (rep_permOfArr (hc.strong_inv 1 (by have := glNJChain_parts.1; omega))).1
  have r0 : Rep 77 Native.glNJChS[0]! (piK (qN 0)) := by
    rw [glNJChain_parts.2.1]
    exact rep_piK_qN (by norm_num)
  have r1 : Rep 77 Native.glNJChS[1]! (piK (qN 1)) := by
    rw [glNJChain_parts.2.2.1]
    exact rep_piK_qN (by norm_num)
  have e0 : permOfArr 77 Native.glNJChS[0]! = piK (qN 0) := h0.unique r0
  have e1 : permOfArr 77 Native.glNJChS[1]! = piK (qN 1) := h1.unique r1
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · exact Or.inl e0
    · exact Or.inr e1
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, e0⟩
    · exact ⟨1, by norm_num, e1⟩

theorem card_PQ : Nat.card PQ = 11520 := by
  rw [← njChain_eq, card_njChain]

theorem piK_qN_zero {k : ℕ} (hk : k < 2) : piK (qN k) 0 = 0 := by
  apply omK_injective
  rw [piK_spec, qN_val (by omega), omK_zero, qK_comm_z0 hk, mul_inv_cancel_right]


theorem PQ_le_njAut0 : PQ ≤ njAut0 := by
  rw [PQ, closure_le]
  rintro _ (rfl | rfl)
  · exact ⟨piK_mem_njAut _, piK_qN_zero (by norm_num)⟩
  · exact ⟨piK_mem_njAut _, piK_qN_zero (by norm_num)⟩

theorem PQ_eq_njAut0 : PQ = njAut0 :=
  Subgroup.eq_of_le_of_card_ge PQ_le_njAut0 (by rw [card_PQ]; exact card_njAut0_le)

@[expose] noncomputable def wordN (w : List ℕ) : normalizer (Jc : Set K) := (w.map qN).prod

theorem wordN_val {w : List ℕ} (hw : ∀ i ∈ w, i < 3) : (wordN w : K) = wordK w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have e : wordK (i :: w) = qK i * wordK w := by
      rw [wordK, List.map_cons, List.prod_cons]
      rfl
    rw [wordN, List.map_cons, List.prod_cons, Subgroup.coe_mul, ← wordN,
      ih fun j hj => hw j (List.mem_cons_of_mem _ hj), qN_val (hw i List.mem_cons_self), e]

theorem eq_njAut_of_gens {X : Subgroup (Equiv.Perm (Fin 77))} (hX : X ≤ njAut)
    (hq : ∀ i < 3, piK (qN i) ∈ X) : X = njAut := by
  have hw : ∀ w : List ℕ, (∀ i ∈ w, i < 3) → piK (wordN w) ∈ X := by
    intro w hw
    induction w with
    | nil => rw [wordN, List.map_nil, List.prod_nil, map_one]; exact X.one_mem
    | cons i w ih =>
      rw [wordN, List.map_cons, List.prod_cons, map_mul, ← wordN]
      exact X.mul_mem (hq i (hw i List.mem_cons_self))
        (ih fun j hj => hw j (List.mem_cons_of_mem _ hj))
  refine eq_of_transitive_of_le 0 hX (fun k => ⟨_, hw _ (glNJOm_spec.2.2.2.2.2.2.1 k k.2).1, ?_⟩)
    fun σ hσ hσ0 => ?_
  · apply omK_injective
    rw [piK_spec, wordN_val (glNJOm_spec.2.2.2.2.2.2.1 k k.2).1, omK_zero, omK_conj_z0]
  · have hPQ : PQ ≤ X := by
      rw [PQ, closure_le]
      rintro _ (rfl | rfl)
      · exact hq 0 (by norm_num)
      · exact hq 1 (by norm_num)
    exact hPQ (PQ_eq_njAut0 ▸ ⟨hσ, hσ0⟩)

end Groups

end CFSG.Sporadic.Co2Smith
