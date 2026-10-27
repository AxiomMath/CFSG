module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTBridge

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Certificates.Data.E6TableT

private lemma rank_e6 : Tag.E6.rank = 6 := rfl

private lemma length_basisVec (i : Nat) : (basisVec i).length = 6 := by
  simp [basisVec]

private lemma ofFn_pi_single (i : Fin Tag.E6.rank) :
    List.ofFn (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) = basisVec i.val := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_ofFn, basisVec, List.getElem?_map]
  by_cases hk : k < Tag.E6.rank
  · have hk6 : k < 6 := hk
    rw [dif_pos hk, List.getElem?_range hk6]
    simp only [Option.map_some, Option.some.injEq]
    by_cases hik : i.val = k
    · have hfin : (⟨k, hk⟩ : Fin Tag.E6.rank) = i := Fin.ext hik.symm
      rw [hfin, Pi.single_eq_same, if_pos hik]
    · have hne : (⟨k, hk⟩ : Fin Tag.E6.rank) ≠ i := fun heq => hik (Fin.ext_iff.mp heq).symm
      rw [Pi.single_eq_of_ne hne, if_neg hik]
  · have hk6 : 6 ≤ k := Nat.le_of_not_lt (show ¬ k < 6 from hk)
    rw [dif_neg hk, List.getElem?_eq_none (by simpa using hk6)]
    rfl

private lemma length_row (i : Fin Tag.E6.rank) : (cartan.getD i.val []).length = 6 := by
  fin_cases i <;> decide +kernel

private lemma length_scalarMul (a : Int) (v : Vec) : (scalarMul a v).length = v.length := by
  simp [scalarMul]

private lemma scalarMul_eq_map (a : Int) (v : Vec) :
    scalarMul a v = v.map (fun x => a * x) := rfl

private lemma cartan_eq_row (i j : Fin Tag.E6.rank) :
    Tag.E6.cartan i j = (cartan.getD i.val []).getD j.val 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private lemma pi_single_apply (i k : Fin Tag.E6.rank) :
    (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) k = if i.val = k.val then 1 else 0 := by
  by_cases h : i = k
  · subst h; simp [Pi.single_eq_same]
  · have hki : k ≠ i := fun hki => h hki.symm
    have hval : ¬ i.val = k.val := fun hv => h (Fin.ext hv)
    rw [Pi.single_eq_of_ne hki, if_neg hval]

private lemma basisVec_getElem (i : Fin Tag.E6.rank) {k : Nat} (hk : k < 6) :
    (basisVec i.val)[k]'(by rw [length_basisVec]; exact hk) =
      if i.val = k then 1 else 0 := by
  simp [basisVec, List.getElem_map, List.getElem_range]

private lemma zipWith_mul_ofFn (i : Fin Tag.E6.rank) (γ : Fin Tag.E6.rank → ℤ) :
    List.zipWith (· * ·) (cartan.getD i.val []) (List.ofFn γ) =
      List.ofFn (fun j : Fin Tag.E6.rank => (cartan.getD i.val []).getD j.val 0 * γ j) := by
  apply List.ext_getElem
  · rw [List.length_zipWith, List.length_ofFn, List.length_ofFn, length_row i, rank_e6]
    rfl
  · intro k _ h2
    have hk6 : k < 6 := by simpa [List.length_ofFn, rank_e6] using h2
    rw [List.getElem_zipWith, List.getElem_ofFn, List.getElem_ofFn]
    dsimp only
    rw [List.getD_eq_getElem (cartan.getD i.val []) 0 (by rw [length_row i]; exact hk6)]

private lemma dot_row_ofFn (i : Fin Tag.E6.rank) (γ : Fin Tag.E6.rank → ℤ) :
    dot (cartan.getD i.val []) (List.ofFn γ) = ∑ j, Tag.E6.cartan i j * γ j := by
  rw [dot, zipWith_mul_ofFn i γ, List.sum_ofFn]
  exact Finset.sum_congr rfl fun j _ => by rw [cartan_eq_row i j]

private lemma reflect_apply (i : Fin Tag.E6.rank) (γ : Fin Tag.E6.rank → ℤ)
    (k : Fin Tag.E6.rank) :
    CFSG.Blueprint.Chevalley.reflect Tag.E6 i γ k =
      γ k - dot (cartan.getD i.val []) (List.ofFn γ) *
        (if i.val = k.val then 1 else 0) := by
  show (γ - (∑ j, Tag.E6.cartan i j * γ j) • Pi.single i 1 : Fin Tag.E6.rank → ℤ) k = _
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← dot_row_ofFn i γ, pi_single_apply i k]

private lemma getElem?_sub_of_lt {a b : List Int} {k : Nat}
    (ha : k < a.length) (hb : k < b.length) :
    (a - b)[k]? = some (a[k] - b[k]) := by
  rw [Lean.Omega.IntList.sub_def, List.getElem?_zipWithAll,
    List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]
  rfl

private lemma getElem?_sub_eq_none {a b : List Int} {k : Nat}
    (ha : a.length ≤ k) (hb : b.length ≤ k) : (a - b)[k]? = none := by
  rw [Lean.Omega.IntList.sub_def, List.getElem?_zipWithAll,
    List.getElem?_eq_none ha, List.getElem?_eq_none hb]

private lemma ofFn_reflect (i : Fin Tag.E6.rank) (γ : Fin Tag.E6.rank → ℤ) :
    List.ofFn (CFSG.Blueprint.Chevalley.reflect Tag.E6 i γ) =
      Certificates.Data.E6TableT.reflect i.val (List.ofFn γ) := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_ofFn, Certificates.Data.E6TableT.reflect]
  by_cases hk : k < Tag.E6.rank
  · have hk6 : k < 6 := hk
    rw [dif_pos hk]
    rw [getElem?_sub_of_lt (a := List.ofFn γ)
      (b := scalarMul (dot (cartan.getD i.val []) (List.ofFn γ)) (basisVec i.val))
      (by rw [List.length_ofFn]; exact hk)
      (by rw [length_scalarMul, length_basisVec]; exact hk6)]
    rw [Option.some.injEq, reflect_apply i γ ⟨k, hk⟩, List.getElem_ofFn]
    simp only [scalarMul_eq_map, List.getElem_map, basisVec_getElem i hk6]
  · have hk6 : 6 ≤ k := Nat.le_of_not_lt (show ¬ k < 6 from hk)
    rw [dif_neg hk]
    rw [getElem?_sub_eq_none
      (by rw [List.length_ofFn]; exact Nat.le_of_not_lt hk)
      (by rw [length_scalarMul, length_basisVec]; exact hk6)]

private lemma closedOK_holds : closedOK () = true := by decide +kernel

private lemma basisVec_mem_roots {i : Nat} (hi : i < 6) : basisVec i ∈ roots () := by
  have h := closedOK_holds
  simp only [closedOK, Bool.and_eq_true, beq_iff_eq] at h
  have hb : ((List.range 6).all fun i => (roots ()).contains (basisVec i)) = true := h.1.2
  exact List.contains_iff_mem.mp ((List.all_eq_true.mp hb) i (List.mem_range.mpr hi))

private lemma reflect_mem_roots {v : Vec} (hv : v ∈ roots ()) {i : Nat} (hi : i < 6) :
    Certificates.Data.E6TableT.reflect i v ∈ roots () := by
  have h := closedOK_holds
  simp only [closedOK, Bool.and_eq_true, beq_iff_eq] at h
  have hall : ((roots ()).all fun v => ((List.range 6).all fun i =>
      (roots ()).contains (Certificates.Data.E6TableT.reflect i v))) = true := h.2
  have hinner : ((List.range 6).all fun i =>
      (roots ()).contains (Certificates.Data.E6TableT.reflect i v)) = true :=
    (List.all_eq_true.mp hall) v hv
  exact List.contains_iff_mem.mp ((List.all_eq_true.mp hinner) i (List.mem_range.mpr hi))

private def RootList (l : Vec) : Prop :=
  ∃ γ : Fin Tag.E6.rank → ℤ, l = List.ofFn γ ∧ IsRoot Tag.E6 γ

private lemma RootList.basis (i : Fin Tag.E6.rank) : RootList (basisVec i.val) :=
  ⟨Pi.single i 1, (ofFn_pi_single i).symm, IsRoot.basis i⟩

private lemma RootList.reflect {l : Vec} (hl : RootList l) (i : Fin Tag.E6.rank) :
    RootList (Certificates.Data.E6TableT.reflect i.val l) := by
  rcases hl with ⟨γ, rfl, hγ⟩
  exact ⟨CFSG.Blueprint.Chevalley.reflect Tag.E6 i γ, (ofFn_reflect i γ).symm,
    IsRoot.reflect i hγ⟩

private lemma RootList.reflect_nat {l : Vec} (hl : RootList l) {i : Nat} (hi : i < 6) :
    RootList (Certificates.Data.E6TableT.reflect i l) :=
  RootList.reflect hl ⟨i, hi⟩

private lemma foldl_snd_of_mem {α : Type*} (f : List Vec × List Vec → α → List Vec × List Vec)
    (l : List α) (P : List Vec → Prop)
    (h : ∀ p a, a ∈ l → P p.2 → P (f p a).2) :
    ∀ p, P p.2 → P (l.foldl f p).2 := by
  induction l with
  | nil => intro p hp; exact hp
  | cons a l ih =>
      intro p hp
      rw [List.foldl_cons]
      exact ih (fun p' b hb hp' => h p' b (List.mem_cons_of_mem a hb) hp')
        (f p a) (h p a List.mem_cons_self hp)

private lemma closureStep_sound {acc frontier : List Vec}
    (hf : ∀ v ∈ frontier, RootList v) :
    ∀ w ∈ closureStep acc frontier, RootList w := by
  unfold closureStep
  refine foldl_snd_of_mem _ frontier (fun l => ∀ w ∈ l, RootList w) ?_ (acc, []) ?_
  · intro p v hv hp
    refine foldl_snd_of_mem _ (List.range 6) (fun l => ∀ w ∈ l, RootList w) ?_ p hp
    intro p' i hi hp'
    have hi6 : i < 6 := List.mem_range.mp hi
    dsimp only
    by_cases hc : acc.contains (Certificates.Data.E6TableT.reflect i v) ||
        p'.2.contains (Certificates.Data.E6TableT.reflect i v)
    · rw [if_pos hc]; exact hp'
    · rw [if_neg hc]
      intro w hw
      rw [List.mem_append] at hw
      rcases hw with hw | hw
      · exact hp' w hw
      · rw [List.mem_singleton] at hw
        subst hw
        exact RootList.reflect_nat (hf v hv) hi6
  · intro w hw
    simp at hw

private lemma closure_sound {fuel : Nat} {acc frontier : List Vec}
    (ha : ∀ x ∈ acc, RootList x) (hf : ∀ x ∈ frontier, RootList x) :
    ∀ x ∈ Certificates.Data.E6TableT.closure fuel acc frontier, RootList x := by
  induction fuel generalizing acc frontier with
  | zero => exact ha
  | succ fuel ih =>
      rw [Certificates.Data.E6TableT.closure]
      split
      · assumption
      · rename_i hne
        apply ih
        · intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · exact ha x hx
          · exact closureStep_sound hf x hx
        · exact closureStep_sound hf

private lemma RootList.of_mem_roots {x : Vec} (hx : x ∈ roots ()) : RootList x := by
  have h : roots () = Certificates.Data.E6TableT.closure 30
      ((List.range 6).map basisVec) ((List.range 6).map basisVec) := rfl
  rw [h] at hx
  refine closure_sound ?_ ?_ x hx
  · intro y hy
    rw [List.mem_map] at hy
    rcases hy with ⟨i, hi, rfl⟩
    exact RootList.basis ⟨i, List.mem_range.mp hi⟩
  · intro y hy
    rw [List.mem_map] at hy
    rcases hy with ⟨i, hi, rfl⟩
    exact RootList.basis ⟨i, List.mem_range.mp hi⟩

theorem isRoot_iff_mem_roots (γ : Fin Tag.E6.rank → ℤ) : IsRoot Tag.E6 γ ↔ List.ofFn γ ∈ roots () := by
  constructor
  · intro h
    induction h with
    | basis j =>
        rw [ofFn_pi_single j]
        exact basisVec_mem_roots j.isLt
    | reflect i hv ih =>
        rw [ofFn_reflect i _]
        exact reflect_mem_roots ih i.isLt
  · intro h
    rcases RootList.of_mem_roots h with ⟨δ, hδ, hroot⟩
    have hγδ : γ = δ := List.ofFn_injective hδ
    rw [← hγδ] at hroot
    exact hroot

end CFSG.StandardType.TablePThreeKG

end
