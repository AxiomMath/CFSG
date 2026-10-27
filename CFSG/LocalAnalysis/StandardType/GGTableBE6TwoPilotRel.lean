module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotGens

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint TableBExc.E6Three E6TwoMat CFSG.SeitzReduction

namespace E6TwoPilot

local instance e6TwoPilotRelNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Words

variable {K : Type} [Field K]

theorem wordElt_wpow (n : ℕ) (w : List ℕ) : wordElt K (wpow n w) = wordElt K w ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wpow, wordElt_append, ih, pow_succ']

theorem wordElt_mem_adjointGroup (w : List ℕ) : wordElt K w ∈ adjointGroup .E6 K :=
  list_prod_mem fun _ hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_adjointGroup _ _

theorem coe_uE6Two_eq_wordElt (i : Fin 4) :
    ((uE6Two (K := K) i : adjointGroup .E6 K) : ModGL .E6 K) = wordElt K (uWord i) := by
  obtain ⟨hw, h0, h1⟩ := rootOf_uWord i
  rw [hw, wordElt_cons, wordElt_cons, wordElt_nil, mul_one, h0, h1]
  rfl

end Words

section Elts

variable {K : Type} [Field K]

theorem coe_torusE6Two_eq_wordElt (h2 : (2 : K) = 0) (v : Fin 4 → ZMod 3) :
    ((torusE6Two (K := K) h2 (.ofAdd v) : adjointGroup .E6 K) : ModGL .E6 K) =
      wordElt K (eWord v) := by
  have e : (Multiplicative.ofAdd v : Multiplicative (Fin 4 → ZMod 3)) =
      .ofAdd (Pi.single 0 (v 0)) * .ofAdd (Pi.single 1 (v 1)) * .ofAdd (Pi.single 2 (v 2)) *
        .ofAdd (Pi.single 3 (v 3)) := by
    apply Multiplicative.toAdd.injective
    funext j
    fin_cases j <;> simp
  rw [e, map_mul, map_mul, map_mul, torusE6Two_single, torusE6Two_single, torusE6Two_single,
    torusE6Two_single, RankThree.CentralCover.zmodPowHom_apply,
    RankThree.CentralCover.zmodPowHom_apply, RankThree.CentralCover.zmodPowHom_apply,
    RankThree.CentralCover.zmodPowHom_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, coe_uE6Two_eq_wordElt]
  rw [eWord, wordElt_append, wordElt_append, wordElt_append, wordElt_wpow, wordElt_wpow,
    wordElt_wpow, wordElt_wpow]

variable (K) in
@[expose] noncomputable def sE6Two : adjointGroup .E6 K :=
  ⟨wordElt K sWord, wordElt_mem_adjointGroup sWord⟩

variable [CharP K 2]

theorem sE6Two_pow_three : sE6Two K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  change wordElt K sWord ^ 3 = 1
  rw [pow_succ, pow_two, ← wordElt_append, ← wordElt_append]
  exact wordElt_eq_of_wordsAgree wordsAgree_s_cube

theorem sE6Two_mul_uE6Two (h2 : (2 : K) = 0) (i : Fin 4) :
    sE6Two K * uE6Two i = torusE6Two h2 (.ofAdd (msCol i)) * sE6Two K := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_torusE6Two_eq_wordElt, coe_uE6Two_eq_wordElt]
  change wordElt K sWord * wordElt K (uWord i) = wordElt K (eWord (msCol i)) * wordElt K sWord
  rw [← wordElt_append, ← wordElt_append]
  fin_cases i
  · exact wordElt_eq_of_wordsAgree wordsAgree_s_u0
  · exact wordElt_eq_of_wordsAgree wordsAgree_s_u1
  · exact wordElt_eq_of_wordsAgree wordsAgree_s_u2
  · exact wordElt_eq_of_wordsAgree wordsAgree_s_u3

end Elts

@[expose] def tWord : List (Fin Tag.E6.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]

@[expose] noncomputable def tWeyl : WeylGroup .E6 :=
  (coxeterSystem .E6).wordProd tWord

section Triality


theorem tWeyl_smul_bE6 : ∀ i : Fin 4, tWeyl • bE6 i = bE6 (tPerm i) := by
  intro i
  rw [tWeyl, wordProd_smul]
  revert i
  decide +kernel

theorem tWeyl_cube : tWeyl * tWeyl * tWeyl = 1 := by
  refine ext_single fun j => ?_
  rw [mul_smul, mul_smul, one_smul, tWeyl, wordProd_smul, wordProd_smul, wordProd_smul]
  revert j
  decide +kernel

theorem tWeyl_smul_sWord :
    (sWord.map rootOf).map (tWeyl • ·) = sWordT.map rootOf := by
  rw [tWeyl, List.map_map]
  simp only [Function.comp_def, wordProd_smul]
  decide +kernel

variable (K : Type) [Field K] in
@[expose] noncomputable def tE6Two : adjointGroup .E6 K :=
  ⟨canonicalRep (coxeterSystem .E6) K tWeyl, canonicalRep_mem_adjointGroup _ K _⟩

variable {K : Type} [Field K] [CharP K 2]

theorem tE6Two_conj_uE6Two (i : Fin 4) :
    tE6Two K * uE6Two i * (tE6Two K)⁻¹ = uE6Two (tPerm i) := by
  have h1 := E6Pilot.canonicalRep_mul_pinnedX_mul_inv_of_charTwo tWeyl (isRoot_bE6 i) (1 : K)
  have h2 := E6Pilot.canonicalRep_mul_pinnedX_mul_inv_of_charTwo tWeyl (isRoot_neg_bE6 i)
    (1 : K)
  rw [tWeyl_smul_bE6] at h1
  rw [smul_neg, tWeyl_smul_bE6] at h2
  apply Subtype.ext
  change canonicalRep (coxeterSystem .E6) K tWeyl *
      (pinnedX .E6 K (bE6 i) 1 * pinnedX .E6 K (-bE6 i) 1) *
        (canonicalRep (coxeterSystem .E6) K tWeyl)⁻¹ =
      pinnedX .E6 K (bE6 (tPerm i)) 1 * pinnedX .E6 K (-bE6 (tPerm i)) 1
  rw [← h1, ← h2]
  group

theorem tE6Two_pow_three : tE6Two K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  change canonicalRep (coxeterSystem .E6) K tWeyl ^ 3 = 1
  rw [pow_succ, pow_two, ← RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
    ← RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo, tWeyl_cube, canonicalRep_one]


theorem tE6Two_mul_sE6Two : tE6Two K * sE6Two K = sE6Two K * tE6Two K := by
  have hF : ∀ α ∈ sWord.map rootOf, IsRoot .E6 α := by
    intro α hα
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hα
    have h : 6 ≤ a ∧ a < 78 := by
      simp only [sWord, List.mem_cons, List.not_mem_nil, or_false] at ha
      omega
    exact isRoot_rootOf ⟨a, h.2⟩ h.1
  have h := E6Pilot.canonicalRep_mul_list_prod_mul_inv_of_charTwo (K := K) tWeyl hF
    (fun _ => 1)
  have e1 : ((sWord.map rootOf).map fun α => pinnedX .E6 K α ((fun _ => (1 : K)) α)).prod =
      wordElt K sWord := by
    rw [List.map_map]
    rfl
  have e2 :
      ((sWord.map rootOf).map fun α => pinnedX .E6 K (tWeyl • α) ((fun _ => (1 : K)) α)).prod =
        wordElt K sWordT := by
    have h3 := tWeyl_smul_sWord
    rw [List.map_map] at h3 ⊢
    rw [wordElt]
    have h4 : (sWordT.map fun a => pinnedX .E6 K (rootOf a) 1) =
        ((sWordT.map rootOf).map fun α => pinnedX .E6 K α 1) := by
      rw [List.map_map]
      rfl
    rw [h4, ← h3, List.map_map]
    rfl
  rw [e1, e2, wordElt_eq_of_wordsAgree wordsAgree_sT] at h
  have h' : tE6Two K * sE6Two K * (tE6Two K)⁻¹ = sE6Two K := Subtype.ext h
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'

end Triality

end E6TwoPilot

end CFSG.StandardType
