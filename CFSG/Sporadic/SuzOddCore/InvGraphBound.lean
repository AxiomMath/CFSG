module

public import CFSG.Sporadic.SuzOddCore.InvGraph

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Inv

variable {tt : Array ℕ} {t σ : Equiv.Perm (Fin 1782)} (ht : Rep 1782 tt t)
  (hσ : NbrInv invNbr σ) (hcomm : ∀ x, σ (t x) = t (σ x))
include ht hσ hcomm

theorem initColour_inv (rule : String) : ColInv 1782 (initColour rule tt) σ := by
  intro v
  rw [initColour, getElem!_ofFn_nat _ (σ v).2, getElem!_ofFn_nat _ v.2]
  simp only
  rw [ht (σ v), ht v, ← hcomm v]
  have hfix : (((σ (t v) : Fin 1782) : ℕ) == ((σ v : Fin 1782) : ℕ)) =
      (((t v : Fin 1782) : ℕ) == (v : ℕ)) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    constructor
    · intro h
      exact congrArg Fin.val (σ.injective (Fin.ext h))
    · intro h
      rw [show t v = v from Fin.ext h]
  have hadj : (invNbr[((σ v : Fin 1782) : ℕ)]!).contains ((σ (t v) : Fin 1782) : ℕ) =
      (invNbr[(v : ℕ)]!).contains ((t v : Fin 1782) : ℕ) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
    exact (hσ v (t v)).symm
  rw [hfix, hadj]

theorem refineStepT_inv {col : Array ℕ} (hc : ColInv 1782 col σ) :
    ColInv 1782 (refineStepT tt col) σ := by
  intro v
  rw [refineStepT, getElem!_ofFn_nat _ (σ v).2, getElem!_ofFn_nat _ v.2]
  simp only
  rw [hc v, ht (σ v), ht v, ← hcomm v, hc (t v),
    nbrColours_inv (fun x => invNbr_facts.point x) hσ hc v]

theorem refineIterT_inv {col : Array ℕ} (hc : ColInv 1782 col σ) :
    ∀ k, ColInv 1782 (refineIterT tt col k) σ
  | 0 => hc
  | k + 1 => refineStepT_inv ht hσ hcomm (refineIterT_inv hc k)

end Inv

theorem getElem!_set!_eq {col : Array ℕ} {p x : ℕ} (hp : p < col.size) :
    (col.set! p x)[p]! = x := by
  rw [getElem!_pos _ p (by simpa using hp)]
  simp [Array.set!]

theorem getElem!_set!_ne {col : Array ℕ} {p q x : ℕ} (hq : q < col.size) (hpq : p ≠ q) :
    (col.set! p x)[q]! = col[q]! := by
  rw [getElem!_pos _ q (by simpa using hq), getElem!_pos col q hq]
  exact Array.getElem_setIfInBounds_ne hq hpq

theorem indivPoint_inv {col : Array ℕ} (hsz : col.size = 1782) {p j : ℕ} (hp : p < 1782)
    {σ : Equiv.Perm (Fin 1782)} (hσp : σ ⟨p, hp⟩ = ⟨p, hp⟩) (hc : ColInv 1782 col σ) :
    ColInv 1782 (indivPoint col p j) σ := by
  intro v
  rw [indivPoint]
  by_cases hv : (v : ℕ) = p
  · have hv' : v = ⟨p, hp⟩ := Fin.ext hv
    rw [hv', hσp]
  · have hσv : ((σ v : Fin 1782) : ℕ) ≠ p := by
      intro h
      apply hv
      have : σ v = ⟨p, hp⟩ := Fin.ext h
      rw [← hσp] at this
      exact congrArg Fin.val (σ.injective this)
    rw [getElem!_set!_ne (by rw [hsz]; exact (σ v).2) (Ne.symm hσv),
      getElem!_set!_ne (by rw [hsz]; exact v.2) (Ne.symm hv), hc v]

theorem refineIterT_size (tt col : Array ℕ) : ∀ k, (refineIterT tt col k).size = col.size ∨
    (refineIterT tt col k).size = 1782
  | 0 => Or.inl rfl
  | k + 1 => Or.inr (by simp [refineIterT, refineStepT])

theorem stageColour_size {i : ℕ} : ∀ s, (stageColour i s).size = 1782
  | 0 => by
    rw [stageColour]
    rcases refineIterT_size (tArr i) (initColour (invColorRules.getD i "") (tArr i))
      (invInitRefinements.getD i []).length with h | h
    · rw [h]; simp [initColour]
    · exact h
  | s + 1 => by
    rw [stageColour]
    rcases refineIterT_size (tArr i) (indivPoint (stageColour i s) ((stepPoints i).getD s 0) s)
      (((invSteps.getD i []).getD s []).getD 2 0) with h | h
    · rw [h, indivPoint, Array.size_set!, stageColour_size s]
    · exact h

@[expose] def invBasePt (i s : ℕ) : Fin 1782 := pt 1782 ((stepPoints i).getD s 0)

theorem stepPoints_lt
    {i s : ℕ} (hi : i < 4) (hs : s < (stepPoints i).length) :
    (stepPoints i).getD s 0 < 1782 := by
  rw [List.getD_eq_getElem _ _ hs]
  exact invGraph_check.2.2.2.2.2.2 i hi _ (List.getElem_mem hs)

theorem stepPoints_length (i : ℕ) : (stepPoints i).length = (invSteps.getD i []).length := by
  simp [stepPoints]

theorem invBasePt_val
    {i s : ℕ} (hi : i < 4) (hs : s < (stepPoints i).length) :
    ((invBasePt i s : Fin 1782) : ℕ) = (stepPoints i).getD s 0 :=
  pt_val (stepPoints_lt hi hs)

theorem stageColour_inv
    {i : ℕ} (hi : i < 4) {σ : Equiv.Perm (Fin 1782)} (hσ : NbrInv invNbr σ)
    (hcomm : ∀ x, σ (suzInv i x) = suzInv i (σ x)) :
    ∀ s ≤ (stepPoints i).length, (∀ r < s, σ (invBasePt i r) = invBasePt i r) →
      ColInv 1782 (stageColour i s) σ
  | 0, _, _ => by
    rw [stageColour]
    exact refineIterT_inv (rep_suzInv hi) hσ hcomm (initColour_inv (rep_suzInv hi) hσ hcomm _) _
  | s + 1, hs, hfix => by
    rw [stageColour]
    refine refineIterT_inv (rep_suzInv hi) hσ hcomm ?_ _
    have hp := stepPoints_lt hi (show s < (stepPoints i).length by omega)
    refine indivPoint_inv (stageColour_size s) hp ?_
      (stageColour_inv hi hσ hcomm s (by omega) fun r hr => hfix r (by omega))
    have := hfix s (by omega)
    have e : invBasePt i s = ⟨(stepPoints i).getD s 0, hp⟩ := Fin.ext (invBasePt_val hi (by omega))
    rwa [e] at this

@[expose] def autPerm : (invGraph ≃g invGraph) →* Equiv.Perm (Fin 1782) where
  toFun σ := σ.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem autPerm_apply (σ : invGraph ≃g invGraph) (x : Fin 1782) : autPerm σ x = σ x := rfl

@[expose] def autCent (t : Equiv.Perm (Fin 1782)) : Subgroup (invGraph ≃g invGraph) :=
  (Subgroup.centralizer {t}).comap autPerm

@[expose] def invCent (i : ℕ) : Subgroup (invGraph ≃g invGraph) := autCent (suzInv i)

theorem mem_autCent {t : Equiv.Perm (Fin 1782)} {σ : invGraph ≃g invGraph} :
    σ ∈ autCent t ↔ ∀ x, σ (t x) = t (σ x) := by
  rw [autCent, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h x
    have := congrArg (fun g : Equiv.Perm (Fin 1782) => g x) h
    simp only [Equiv.Perm.mul_apply, autPerm_apply] at this
    exact this
  · intro h
    ext x
    simp only [Equiv.Perm.mul_apply, autPerm_apply]
    exact congrArg Fin.val (h x)

theorem nbrInv_of_aut
    (σ : invGraph ≃g invGraph) : NbrInv invNbr σ.toEquiv := by
  intro x y
  rw [invNbr_adj, invNbr_adj]
  exact σ.map_rel_iff.symm

instance : Finite (invGraph ≃g invGraph) :=
  Finite.of_injective (fun σ : invGraph ≃g invGraph => σ.toEquiv) fun _ _ h =>
    RelIso.ext fun x => congrArg (fun e : Equiv.Perm (Fin 1782) => e x) h

@[expose] def invCentStab (i s : ℕ) : Subgroup (invCent i) := stabChain (invBasePt i) s

theorem mem_invCentStab {i s : ℕ} {σ : invCent i} :
    σ ∈ invCentStab i s ↔ ∀ j < s, (σ : invGraph ≃g invGraph) (invBasePt i j) = invBasePt i j := by
  rw [invCentStab, mem_stabChain]
  rfl

theorem colInv_of_stab
    {i s : ℕ} (hi : i < 4) (hs : s ≤ (stepPoints i).length) {σ : invCent i}
    (hσ : σ ∈ invCentStab i s) : ColInv 1782 (stageColour i s) (σ : invGraph ≃g invGraph).toEquiv :=
  stageColour_inv hi (nbrInv_of_aut _) (mem_autCent.1 σ.2) s hs (mem_invCentStab.1 hσ)

theorem invCentStab_orbit
    {i s : ℕ} (hi : i < 4) (hs : s < (stepPoints i).length) :
    (MulAction.orbit (invCentStab i s) (invBasePt i s)).ncard ≤
      ((invSteps.getD i []).getD s []).getD 1 0 := by
  have hs' : s < (invSteps.getD i []).length := by rw [← stepPoints_length]; exact hs
  refine le_trans ?_ (invGraph_check.2.2.2.2.1 i hi s hs')
  rw [classCount, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨⟨σ, hσ⟩, rfl⟩
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  rw [← invBasePt_val hi hs]
  exact colInv_of_stab hi hs.le hσ (invBasePt i s)

theorem invCentStab_last
    {i : ℕ} (hi : i < 4) :
    invCentStab i (stepPoints i).length = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have hc := colInv_of_stab hi le_rfl hσ
  obtain ⟨hnd, hsize⟩ := invGraph_check.2.2.2.2.2.1 i hi
  rw [← stepPoints_length] at hnd hsize
  apply Subtype.ext
  refine RelIso.ext fun v => Fin.ext ?_
  have h := hc v
  rw [List.take_of_length_le (by simp [hsize])] at hnd
  rw [getElem!_pos _ _ (by rw [hsize]; exact ((σ : invGraph ≃g invGraph) v).2),
    getElem!_pos _ _ (by rw [hsize]; exact v.2), ← Array.getElem_toList,
    ← Array.getElem_toList] at h
  exact (hnd.getElem_inj_iff).1 h

theorem card_invCent_le_prod
    {i : ℕ} (hi : i < 4) :
    Nat.card (invCent i) ≤
      ∏ s ∈ Finset.range (stepPoints i).length, ((invSteps.getD i []).getD s []).getD 1 0 :=
  card_le_prod_of_stabChain (G := invCent i) (invBasePt i)
    (fun s => ((invSteps.getD i []).getD s []).getD 1 0) _
    (fun _ hs => invCentStab_orbit hi hs) (invCentStab_last hi)

theorem card_invCent_le
    {i : ℕ} (hi : i < 4) :
    Nat.card (invCent i) ≤ invGraphBounds.getD i 0 := by
  refine (card_invCent_le_prod hi).trans (le_of_eq ?_)
  interval_cases i <;> decide

@[expose] def toAut
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ suzT) : invGraph ≃g invGraph where
  toEquiv := g
  map_rel_iff' := suzT_adj hg _ _

theorem toAut_apply
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ suzT) (x : Fin 1782) :
    toAut hg x = g x := rfl

theorem card_centralizer_le
    {i : ℕ} (hi : i < 4) :
    Nat.card (Subgroup.centralizer {suzInv i} ⊓ suzT : Subgroup (Equiv.Perm (Fin 1782))) ≤
      invGraphBounds.getD i 0 := by
  refine le_trans ?_ (card_invCent_le hi)
  refine Nat.card_le_card_of_injective
    (fun g => ⟨toAut g.2.2, mem_autCent.2 fun x => ?_⟩) ?_
  · have := congrArg (fun h : Equiv.Perm (Fin 1782) => h x)
      (Subgroup.mem_centralizer_singleton_iff.1 g.2.1)
    simp only [Equiv.Perm.mul_apply] at this
    rw [toAut_apply, toAut_apply]
    exact this
  · intro g h hgh
    apply Subtype.ext
    have := congrArg (fun σ : invCent i => (σ : invGraph ≃g invGraph).toEquiv) hgh
    exact this

end CFSG.Sporadic.SuzOddCore
