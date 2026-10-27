
module

public import CFSG.Sporadic.HNOddCore.SylBBase

public import CFSG.Sporadic.HNOddCore.SylA
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.PCheckInputs
public meta import CFSG.Sporadic.HNOddCore.QCheck
public meta import Std.Data.HashMap
public import CFSG.Sporadic.HNOddCore.QCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData
public import CFSG.Sporadic.HNSchreier.SylowCheck

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem cls_parts : pReps.size = 29 ∧ csArr.size = 29 ∧
    (∀ c < 29, peq 800 (pcomp 800 pE[pReps[c]!]! pE[pReps[c]!]!) (pid 800) = true ∧
      classOK idxMap pE InvData.pgenPerms (pinvs 800 InvData.pgenPerms) pReps[c]!
        csArr[c]!.1 csArr[c]!.2.1 csArr[c]!.2.2 = true) ∧
    (∀ c < 29, ∀ c' < 29, c ≠ c' → (csArr[c']!.1.contains pReps[c]!) = false) ∧
    (∀ k < 16384, peq 800 (pcomp 800 pE[k]! pE[k]!) (pid 800) = true →
      mkArr[k]! < 29 ∧ (csArr[mkArr[k]!]!.1.contains k) = true) := by
  have h := CFSG.Sporadic.HNOddCore.Native.sylow_cert
  unfold CFSG.Sporadic.HNOddCore.Native.sylowChecks sylowChecksE at h
  dsimp only at h
  rw [← csArr_eq, ← mkArr_eq] at h
  unfold sylowChecksH at h
  dsimp only at h
  rw [← idxMap_eq] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, h13⟩, h14⟩, -⟩, h16⟩,
    h17⟩, h18⟩ := h
  refine ⟨h13, h14, fun c hc => ?_, fun c hc c' hc' hne => ?_, fun k hk hsq => ?_⟩
  · have := allBelowN_spec h16 hc
    simp only [Bool.and_eq_true] at this
    exact this
  · have := allBelowN_spec (allBelowN_spec h17 hc) hc'
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
    rcases this with h | h
    · exact absurd h hne
    · exact h
  · have := allBelowN_spec h18 hk
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with h | h
    · rw [hsq] at h
      exact absurd h (by decide)
    · exact h

theorem prep_pgi
    {g : ℕ} (hg : g < 14) :
    PRep 800 (pinvs 800 InvData.pgenPerms)[g]! (pbarPerm g)⁻¹ :=
  prep_inv_of_pisInv (prep_pbarPerm hg) (p_parts.2.2.2.1 g hg).2.2

theorem prep_pconj
    {g : ℕ} (hg : g < 14) {x : Array ℕ} {σ : Perm (Fin 800)}
    (hx : PRep 800 x σ) :
    PRep 800 (pconj InvData.pgenPerms[g]! (pinvs 800 InvData.pgenPerms)[g]! x)
      (pbarPerm g * σ * (pbarPerm g)⁻¹) := by
  rw [mul_assoc]
  exact prep_pcomp (prep_pbarPerm hg) (prep_pcomp hx (prep_pgi hg))

theorem classOK_spec {c : ℕ} (hc : c < 29) :
    0 < (clsL c).size ∧ (clsL c)[0]! = pReps[c]! ∧ (∀ j < (clsL c).size, (clsL c)[j]! < 16384) ∧
    (∀ j < (clsL c).size, 0 < j → (csArr[c]!.2.1)[j]! < j ∧ (csArr[c]!.2.2)[j]! < 14 ∧
      peq 800 pE[(clsL c)[j]!]! (pconj InvData.pgenPerms[(csArr[c]!.2.2)[j]!]!
        (pinvs 800 InvData.pgenPerms)[(csArr[c]!.2.2)[j]!]! pE[(clsL c)[(csArr[c]!.2.1)[j]!]!]!) =
          true) ∧
    (∀ j < (clsL c).size, ∀ g < 14, ∃ m < 16384, peq 800 pE[m]!
      (pconj InvData.pgenPerms[g]! (pinvs 800 InvData.pgenPerms)[g]! pE[(clsL c)[j]!]!) = true ∧
        (clsL c).contains m = true) := by
  have h := (cls_parts.2.2.1 c hc).2
  unfold classOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hpos⟩, h0⟩, -⟩, -⟩, htree⟩, hcl⟩ := h
  refine ⟨hpos, h0, fun j hj => ?_, fun j hj hj0 => ?_, fun j hj g hg => ?_⟩
  · have := allBelowN_spec htree hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · have := allBelowN_spec htree hj
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at this
    rcases this.2 with h' | h'
    · omega
    · exact ⟨h'.1.1, h'.1.2, h'.2⟩
  · have := allBelowN_spec (allBelowN_spec hcl hj) hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨_, this.1.1, this.1.2, this.2⟩

theorem classSet_tree
    {c : ℕ} (hc : c < 29) :
    ∀ j < (clsL c).size, ∃ y ∈ Pbar, y * repPerm c * y⁻¹ = ePerm (clsL c)[j]! := by
  obtain ⟨-, h0, hlt, htree, -⟩ := classOK_spec hc
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hj0 : j = 0
    · subst hj0
      exact ⟨1, Pbar.one_mem, by rw [one_mul, inv_one, mul_one, repPerm, h0]⟩
    · obtain ⟨hp, hg, he⟩ := htree j hj (Nat.pos_of_ne_zero hj0)
      obtain ⟨y, hy, hye⟩ := ih _ hp (lt_trans hp hj)
      refine ⟨pbarPerm _ * y, Pbar.mul_mem (pbarPerm_mem hg) hy, ?_⟩
      have e := eq_of_peq (prep_ePerm (hlt j hj))
        (prep_pconj hg (prep_ePerm (hlt _ (lt_trans hp hj)))) he
      rw [e, ← hye, mul_inv_rev]
      group

theorem classSet_mem_Pbar
    {c : ℕ} (hc : c < 29) {x : Perm (Fin 800)} (hx : x ∈ classSet c) :
    x ∈ Pbar := by
  obtain ⟨j, hj, rfl⟩ := hx
  exact ePerm_mem _ ((classOK_spec hc).2.2.1 j hj)

theorem classSet_conj
    {c : ℕ} (hc : c < 29) :
    ∀ y ∈ Pbar, ∀ x ∈ classSet c, y * x * y⁻¹ ∈ classSet c := by
  obtain ⟨-, -, hlt, -, hcl⟩ := classOK_spec hc
  apply conj_mem_of_closure
  rintro _ ⟨g, rfl⟩ _ ⟨j, hj, rfl⟩
  obtain ⟨m, hm, he, hcont⟩ := hcl j hj g g.2
  rw [Array.contains_iff_mem, Array.mem_iff_getElem] at hcont
  obtain ⟨j', hj', hj'e⟩ := hcont
  refine ⟨j', hj', ?_⟩
  rw [getElem!_pos _ j' hj', hj'e]
  exact (eq_of_peq (prep_ePerm hm) (prep_pconj g.2 (prep_ePerm (hlt j hj))) he)

theorem rep_mem_classSet
    {c : ℕ} (hc : c < 29) : repPerm c ∈ classSet c := by
  obtain ⟨hpos, h0, -, -, -⟩ := classOK_spec hc
  exact ⟨0, hpos, by rw [h0]; rfl⟩

theorem rep_lt {c : ℕ} (hc : c < 29) : pReps[c]! < 16384 := by
  obtain ⟨hpos, h0, hlt, -, -⟩ := classOK_spec hc
  rw [← h0]
  exact hlt 0 hpos

theorem pE_sq_iff
    {k : ℕ} (hk : k < 16384) :
    peq 800 (pcomp 800 pE[k]! pE[k]!) (pid 800) = true ↔ ePerm k ^ 2 = 1 := by
  rw [peq_iff (prep_pcomp (prep_ePerm hk) (prep_ePerm hk)) prep_pid, pow_two]

theorem repPerm_sq
    {c : ℕ} (hc : c < 29) : repPerm c ^ 2 = 1 :=
  (pE_sq_iff (rep_lt hc)).1 (cls_parts.2.2.1 c hc).1

theorem repPerm_mem
    {c : ℕ} (hc : c < 29) : repPerm c ∈ Pbar := ePerm_mem _ (rep_lt hc)

theorem classes_Pbar :
    ∀ x ∈ Pbar, x ^ 2 = 1 → ∃! c : Fin 29, ∃ y ∈ Pbar, y * repPerm c * y⁻¹ = x := by
  intro x hx hsq
  obtain ⟨k, hkx⟩ := Pbar_subset hx
  simp only at hkx
  subst hkx
  have hk := k.2
  have hE := (pE_sq_iff hk).2 hsq
  obtain ⟨hmk, hcont⟩ := cls_parts.2.2.2.2 k hk hE
  rw [Array.contains_iff_mem, Array.mem_iff_getElem] at hcont
  obtain ⟨j, hj, hje⟩ := hcont
  have hxS : ePerm k ∈ classSet mkArr[(k : ℕ)]! := ⟨j, hj, by rw [getElem!_pos _ j hj, hje]⟩
  refine ⟨⟨_, hmk⟩, ?_, ?_⟩
  · obtain ⟨y, hy, hye⟩ := classSet_tree hmk j hj
    exact ⟨y, hy, by rw [hye, getElem!_pos _ j hj, hje]⟩
  · rintro c' ⟨y, hy, hye⟩
    apply Fin.ext
    by_contra hne
    have h1 := classSet_conj hmk y⁻¹ (Pbar.inv_mem hy) _ hxS
    rw [← hye, inv_inv, show y⁻¹ * (y * repPerm c' * y⁻¹) * y = repPerm c' by group] at h1
    obtain ⟨j', hj', hj'e⟩ := h1
    have hlt := (classOK_spec hmk).2.2.1 j' hj'
    have heq := ePerm_injective hlt (rep_lt c'.2) hj'e
    have hdis := cls_parts.2.2.2.1 c' c'.2 _ hmk hne
    rw [← heq] at hdis
    have : (clsL mkArr[(k : ℕ)]!).contains (clsL mkArr[(k : ℕ)]!)[j']! = true := by
      rw [Array.contains_iff_mem, getElem!_pos _ j' hj']
      exact Array.getElem_mem hj'
    rw [this] at hdis
    exact Bool.noConfusion hdis

theorem card_inv_Pbar :
    Nat.card {x : Pbar // x ^ 2 = 1} = 880 := by
  have e : {k : Fin 16384 // ePerm k ^ 2 = 1} ≃ {x : Pbar // x ^ 2 = 1} :=
    Equiv.subtypeEquiv (Equiv.ofBijective eMap eMap_bijective) fun k => by
      show ePerm k ^ 2 = 1 ↔ eMap k ^ 2 = 1
      rw [Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one]
      rfl
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 : (Finset.univ.filter fun k : Fin 16384 => ePerm k ^ 2 = 1) =
      Finset.univ.filter fun k : Fin 16384 =>
        peq 800 (pcomp 800 pE[(k : ℕ)]! pE[(k : ℕ)]!) (pid 800) = true := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (pE_sq_iff k.2).symm
  rw [h2]
  exact (card_eq_countP_fin (p := fun k => peq 800 (pcomp 800 pE[k]! pE[k]!) (pid 800))).trans
    p_parts.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.HNOddCore
