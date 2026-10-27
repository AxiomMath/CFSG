module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE8Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GS03E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open scoped commutatorElement

variable (K : Type) [Field K] in
@[expose] noncomputable def e8FrameProd (L : List ℕ) : ModGL .E8 K :=
  (L.map fun k => pinnedX .E8 K (Tag.E8.rootCertificate.root k) 1).prod

@[expose] def commB (a c : ℕ) : Bool :=
  decide (a < Tag.E8.rootCertificate.roots.length) &&
    decide (c < Tag.E8.rootCertificate.roots.length) &&
    !oddDerivVecEq (Tag.E8.rootCertificate.root a + Tag.E8.rootCertificate.root c) 0 &&
    oddDerivNotRootB .E8 (Tag.E8.rootCertificate.root a + Tag.E8.rootCertificate.root c)

@[expose] def sumB (a b p : ℕ) : Bool :=
  decide (a < Tag.E8.rootCertificate.roots.length) &&
    decide (b < Tag.E8.rootCertificate.roots.length) &&
    decide (p < Tag.E8.rootCertificate.roots.length) &&
    oddDerivVecEq (Tag.E8.rootCertificate.root p)
      (Tag.E8.rootCertificate.root a + Tag.E8.rootCertificate.root b) &&
    !oddDerivVecEq (Tag.E8.rootCertificate.root p) 0 &&
    !oddDerivVecEq (Tag.E8.rootCertificate.root a) (Tag.E8.rootCertificate.root b)

@[expose] def pairwiseCommB : List ℕ → Bool
  | [] => true
  | a :: L => L.all (commB a) && pairwiseCommB L

inductive FrameStep where
  | comm (i j p : ℕ)
  | strip (i j : ℕ)
  | square (i j p : ℕ)
  | perm (i : ℕ) (L : List ℕ)

@[expose] def FrameStep.apply (F : List (List ℕ)) : FrameStep → Option (List ℕ)
  | .comm i j p =>
    match F[i]?, F[j]? with
    | some [a], some (b :: L) => if sumB a b p && L.all (commB a) then some [p] else none
    | _, _ => none
  | .strip i j =>
    match F[i]?, F[j]? with
    | some [a], some (a' :: L) => if a == a' then some L else none
    | _, _ => none
  | .square i j p =>
    match F[i]?, F[j]? with
    | some (a :: L), some (b :: L') => if L == L' && sumB a b p then some [p] else none
    | _, _ => none
  | .perm i L =>
    match F[i]? with
    | some L₀ => if pairwiseCommB L₀ && L₀.isPerm L then some L else none
    | none => none

@[expose] def runSteps (F : List (List ℕ)) : List FrameStep → List (List ℕ)
  | [] => F
  | s :: ss => runSteps ((s.apply F).elim F fun L => F ++ [L]) ss

@[expose] def hasRootB (F : List (List ℕ)) (v : Fin Tag.E8.rank → ℤ) : Bool :=
  F.any fun L =>
    match L with
    | [p] => oddDerivVecEq (Tag.E8.rootCertificate.root p) v
    | _ => false

@[expose] def simpleRootsB (F : List (List ℕ)) : Bool :=
  (List.finRange Tag.E8.rank).all fun j =>
    hasRootB F (Pi.single j 1) && hasRootB F (-Pi.single j 1)

section Gen

variable {K : Type} [Field K]

private lemma commB_spec {a c : ℕ} (h : commB a c = true) :
    a < Tag.E8.rootCertificate.roots.length ∧
      c < Tag.E8.rootCertificate.roots.length ∧
      Tag.E8.rootCertificate.root a + Tag.E8.rootCertificate.root c ≠ 0 ∧
      ¬ IsRoot .E8 (Tag.E8.rootCertificate.root a + Tag.E8.rootCertificate.root c) := by
  simp only [commB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨ha, hc⟩, hne⟩, hnr⟩ := h
  refine ⟨ha, hc, ?_, not_isRoot_of_oddDerivNotRootB hnr⟩
  intro h0
  rw [h0, oddDerivVecEq_self] at hne
  exact Bool.noConfusion hne

private lemma sumB_spec {a b p : ℕ} (h : sumB a b p = true) :
    a < Tag.E8.rootCertificate.roots.length ∧
      b < Tag.E8.rootCertificate.roots.length ∧
      p < Tag.E8.rootCertificate.roots.length ∧
      Tag.E8.rootCertificate.root p =
        Tag.E8.rootCertificate.root a + Tag.E8.rootCertificate.root b ∧
      Tag.E8.rootCertificate.root p ≠ 0 ∧
      Tag.E8.rootCertificate.root a ≠ Tag.E8.rootCertificate.root b := by
  simp only [sumB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨ha, hb⟩, hp⟩, he⟩, hp0⟩, hne⟩ := h
  refine ⟨ha, hb, hp, eq_of_oddDerivVecEq he, ?_, ?_⟩
  · intro h0
    rw [h0, oddDerivVecEq_self] at hp0
    exact Bool.noConfusion hp0
  · intro h0
    rw [h0, oddDerivVecEq_self] at hne
    exact Bool.noConfusion hne

theorem commute_pinnedX_of_commB {a c : ℕ} (h : commB a c = true) (d d' : K) :
    Commute (pinnedX .E8 K (Tag.E8.rootCertificate.root a) d)
      (pinnedX .E8 K (Tag.E8.rootCertificate.root c) d') := by
  obtain ⟨ha, hc, hne, hnr⟩ := commB_spec h
  have hroot_a := RootCertificate.isRoot_root Tag.E8.rootCertificate_check a ha
  have hroot_c := RootCertificate.isRoot_root Tag.E8.rootCertificate_check c hc
  by_cases heq : Tag.E8.rootCertificate.root a = Tag.E8.rootCertificate.root c
  · rw [heq]
    exact (pinnedX_add .E8 K (Tag.E8.rootCertificate.root c) d d').symm.trans
      ((by rw [add_comm] :
          pinnedX .E8 K (Tag.E8.rootCertificate.root c) (d + d') =
            pinnedX .E8 K (Tag.E8.rootCertificate.root c) (d' + d)).trans
        (pinnedX_add .E8 K (Tag.E8.rootCertificate.root c) d' d))
  · have hne' : Tag.E8.rootCertificate.root a ≠ -Tag.E8.rootCertificate.root c := by
      intro hneg
      exact hne (by rw [hneg, neg_add_cancel])
    have hcomm := (simply_laced_root_commutator_unit .E8 (Or.inr (Or.inr (Or.inr rfl)))
      hroot_a hroot_c heq hne').2 hnr
    exact hcomm K (pinnedX .E8 K (Tag.E8.rootCertificate.root a) d)
      (Subgroup.subset_closure ⟨d, rfl⟩)
      (pinnedX .E8 K (Tag.E8.rootCertificate.root c) d')
      (Subgroup.subset_closure ⟨d', rfl⟩)

theorem commutatorElement_pinnedX_of_sumB [CharP K 2] {a b p : ℕ} (h : sumB a b p = true)
    (c d : K) :
    ⁅pinnedX .E8 K (Tag.E8.rootCertificate.root a) c,
        pinnedX .E8 K (Tag.E8.rootCertificate.root b) d⁆ =
      pinnedX .E8 K (Tag.E8.rootCertificate.root p) (c * d) := by
  obtain ⟨ha, hb, hp, he, hp0, hne⟩ := sumB_spec h
  have hroot_a := RootCertificate.isRoot_root Tag.E8.rootCertificate_check a ha
  have hroot_b := RootCertificate.isRoot_root Tag.E8.rootCertificate_check b hb
  have hroot_ab : IsRoot .E8 (Tag.E8.rootCertificate.root a +
      Tag.E8.rootCertificate.root b) := by
    rw [← he]
    exact RootCertificate.isRoot_root Tag.E8.rootCertificate_check p hp
  have hne' : Tag.E8.rootCertificate.root a ≠ -Tag.E8.rootCertificate.root b := by
    intro hneg
    exact hp0 (by rw [he, hneg, neg_add_cancel])
  obtain ⟨hε, hform⟩ :=
    (simply_laced_root_commutator_unit .E8 (Or.inr (Or.inr (Or.inr rfl)))
      hroot_a hroot_b hne hne').1 hroot_ab
  have hsign : ((commConst .E8 (Tag.E8.rootCertificate.root a)
      (Tag.E8.rootCertificate.root b) (1, 1) : ℤ) : K) = 1 := by
    rcases hε with h1 | h1
    · rw [h1]
      norm_num
    · rw [h1]
      rw [show ((-1 : ℤ) : K) = -(1 : K) by norm_num, CharTwo.neg_eq]
  rw [hform K c d, hsign, one_mul, ← he]

private lemma pairwiseCommB_map_commute {L : List ℕ} (h : pairwiseCommB L = true) :
    (L.map fun k => pinnedX .E8 K (Tag.E8.rootCertificate.root k) 1).Pairwise Commute := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [pairwiseCommB, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨ha, hL⟩ := h
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨?_, ih hL⟩
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact commute_pinnedX_of_commB (ha k hk) 1 1

theorem e8FrameProd_perm {L₀ L : List ℕ} (h : pairwiseCommB L₀ = true) (hp : L₀.Perm L) :
    e8FrameProd K L₀ = e8FrameProd K L := by
  rw [e8FrameProd]
  exact List.Perm.prod_eq' (hp.map _) (pairwiseCommB_map_commute h)

private lemma hasRootB_spec {F : List (List ℕ)} {v : Fin Tag.E8.rank → ℤ}
    (h : hasRootB F v = true) :
    ∃ p, [p] ∈ F ∧ Tag.E8.rootCertificate.root p = v := by
  rw [hasRootB] at h
  obtain ⟨L, hL, hLv⟩ := List.any_eq_true.1 h
  cases L with
  | nil => simp at hLv
  | cons p L' =>
    cases L' with
    | nil =>
      simp only at hLv
      exact ⟨p, by simpa using hL, eq_of_oddDerivVecEq hLv⟩
    | cons q L'' => simp at hLv

private lemma pinnedX_mem_of_basis [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    (hn : ∀ i, weylElt .E8 K i (1 : Kˣ) ∈ H) {c : K}
    (hb : ∀ j, pinnedX .E8 K (Pi.single j 1) c ∈ H) :
    ∀ α, IsRoot .E8 α → pinnedX .E8 K α c ∈ H := by
  intro α hα
  refine IsRoot.rec (motive := fun v _ => pinnedX .E8 K v c ∈ H) ?_ ?_ hα
  · intro j
    exact hb j
  · intro i v hv ih
    have hconj := classListE8_weylElt_conj_pinnedX (τ := .E8) (K := K) i hv c
    rw [← hconj]
    exact mul_mem (mul_mem (hn i) ih) (inv_mem (hn i))

private lemma weylElt_one_mem [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    (hpos : ∀ j, pinnedX .E8 K (Pi.single j 1) 1 ∈ H)
    (hneg : ∀ j, pinnedX .E8 K (-Pi.single j 1) 1 ∈ H) :
    ∀ i, weylElt .E8 K i (1 : Kˣ) ∈ H := by
  intro i
  have hx : pinnedX .E8 K (Pi.single i 1) 1 ∈ H := hpos i
  have hy : pinnedX .E8 K (-Pi.single i 1) (-1) ∈ H := by
    simpa [CharTwo.neg_eq] using hneg i
  have hweyl : weylElt .E8 K i (1 : Kˣ) =
      xUnit .E8 K i 1 * yUnit .E8 K i (-1) * xUnit .E8 K i 1 := by
    ext
    simp [weylElt, xUnit, yUnit]
  rw [hweyl]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · simpa [pinnedX_single] using hx
  · simpa [pinnedX_neg_single] using hy
  · simpa [pinnedX_single] using hx

private lemma commute_pinnedX_frameProd [CharP K 2] {a : ℕ} {L0 : List ℕ}
    (hca : ∀ k ∈ L0, commB a k = true) (c : K) :
    Commute (pinnedX .E8 K (Tag.E8.rootCertificate.root a) c) (e8FrameProd K L0) := by
  rw [e8FrameProd]
  refine Commute.list_prod_right _ _ ?_
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  exact commute_pinnedX_of_commB (hca k hk) c 1

private lemma pinnedX_commutator_eq_frame [CharP K 2] {a b p : ℕ} (hs : sumB a b p = true) :
    ⁅pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1,
        pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1⁆ = e8FrameProd K [p] := by
  have h := commutatorElement_pinnedX_of_sumB (K := K) hs 1 1
  rw [mul_one] at h
  rw [show e8FrameProd K [p] =
      pinnedX .E8 K (Tag.E8.rootCertificate.root p) 1 by simp [e8FrameProd]]
  exact h

private lemma commutator_mul_right_of_commute {a b : ℕ} {L0 : List ℕ}
    (hG : Commute (pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1)
      (e8FrameProd K L0)) :
    ⁅pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1,
        pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L0⁆ =
      ⁅pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1,
        pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, Commute.commutator_eq hG]
  simp

private lemma commutator_mem_of_mem {G : Type} [Group G] {H : Subgroup G} {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  have h1 : a * b ∈ H := mul_mem ha hb
  have h2 : a⁻¹ ∈ H := inv_mem ha
  have h3 : b⁻¹ ∈ H := inv_mem hb
  exact mul_mem (mul_mem h1 h2) h3

private lemma e8FrameProd_comm_main [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    {a b p : ℕ} {L0 : List ℕ} (hs : sumB a b p = true)
    (hca : ∀ k ∈ L0, commB a k = true)
    (hXa : pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1 ∈ H)
    (hXbG : pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L0 ∈ H) :
    e8FrameProd K [p] ∈ H := by
  have hG : Commute (pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1)
      (e8FrameProd K L0) := commute_pinnedX_frameProd hca 1
  have hmul_eq := commutator_mul_right_of_commute (b := b) hG
  have hcomm_eq : ⁅pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1,
        pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1⁆ = e8FrameProd K [p] :=
    pinnedX_commutator_eq_frame (K := K) hs
  have hmem : ⁅pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1,
        pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L0⁆ ∈ H :=
    commutator_mem_of_mem hXa hXbG
  rw [hmul_eq, hcomm_eq] at hmem
  exact hmem

private lemma e8FrameProd_of_apply_comm [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    {F : List (List ℕ)} (hF : ∀ L ∈ F, e8FrameProd K L ∈ H) {i j p : ℕ} {L : List ℕ}
    (h : (FrameStep.comm i j p).apply F = some L) : e8FrameProd K L ∈ H := by
  simp only [FrameStep.apply] at h
  cases hFi : F[i]? with
  | none => simp [hFi] at h
  | some Li =>
    cases Li with
    | nil => simp [hFi] at h
    | cons a Li' =>
      cases Li' with
      | cons b L0 => simp [hFi] at h
      | nil =>
        cases hFj : F[j]? with
        | none => simp [hFi, hFj] at h
        | some Lj =>
          cases Lj with
          | nil => simp [hFi, hFj] at h
          | cons b L0 =>
            simp only [hFi, hFj] at h
            split at h
            · rename_i hcond
              simp only [Option.some.injEq] at h
              rw [← h]
              simp only [Bool.and_eq_true, List.all_eq_true] at hcond
              obtain ⟨hs, hca⟩ := hcond
              exact e8FrameProd_comm_main hs hca
                (by
                  have := hF [a] (List.mem_of_getElem? hFi)
                  simpa [e8FrameProd] using this)
                (by
                  have := hF (b :: L0) (List.mem_of_getElem? hFj)
                  simpa [e8FrameProd, List.map_cons, List.prod_cons] using this)
            · simp at h

private lemma e8FrameProd_strip_main {H : Subgroup (ModGL .E8 K)} {a a' : ℕ} {L0 : List ℕ}
    (hae : a = a') (hXa : pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1 ∈ H)
    (hXaL : pinnedX .E8 K (Tag.E8.rootCertificate.root a') 1 * e8FrameProd K L0 ∈ H) :
    e8FrameProd K L0 ∈ H := by
  rw [← hae] at hXaL
  have h := mul_mem (inv_mem hXa) hXaL
  simpa using h

private lemma e8FrameProd_of_apply_strip {H : Subgroup (ModGL .E8 K)}
    {F : List (List ℕ)} (hF : ∀ L ∈ F, e8FrameProd K L ∈ H) {i j : ℕ} {L : List ℕ}
    (h : (FrameStep.strip i j).apply F = some L) : e8FrameProd K L ∈ H := by
  simp only [FrameStep.apply] at h
  cases hFi : F[i]? with
  | none => simp [hFi] at h
  | some Li =>
    cases Li with
    | nil => simp [hFi] at h
    | cons a Li' =>
      cases Li' with
      | cons a' L0 => simp [hFi] at h
      | nil =>
        cases hFj : F[j]? with
        | none => simp [hFi, hFj] at h
        | some Lj =>
          cases Lj with
          | nil => simp [hFi, hFj] at h
          | cons a' L0 =>
            simp only [hFi, hFj] at h
            split at h
            · rename_i hcond
              simp only [Option.some.injEq] at h
              rw [← h]
              have hae : a = a' := beq_iff_eq.1 hcond
              exact e8FrameProd_strip_main hae
                (by
                  have := hF [a] (List.mem_of_getElem? hFi)
                  simpa [e8FrameProd] using this)
                (by
                  have := hF (a' :: L0) (List.mem_of_getElem? hFj)
                  simpa [e8FrameProd, List.map_cons, List.prod_cons] using this)
            · simp at h

private lemma e8FrameProd_square_main [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    {a b p : ℕ} {L0 : List ℕ} (hs : sumB a b p = true)
    (hU : pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1 * e8FrameProd K L0 ∈ H)
    (hV : pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L0 ∈ H) :
    e8FrameProd K [p] ∈ H := by
  have hXa_inv : (pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1)⁻¹ =
      pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1 := by
    rw [pinnedX_neg, CharTwo.neg_eq]
  have hXb_inv : (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1)⁻¹ =
      pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 := by
    rw [pinnedX_neg, CharTwo.neg_eq]
  have hUV : (pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1 * e8FrameProd K L0) *
        (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L0)⁻¹ =
      pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1 *
        pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 := by
    rw [mul_inv_rev, hXb_inv]
    group
  have hsq : ((pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1 * e8FrameProd K L0) *
        (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L0)⁻¹) ^ 2 =
      e8FrameProd K [p] := by
    have hcomm_eq := pinnedX_commutator_eq_frame (K := K) hs
    rw [hUV, pow_two, ← hcomm_eq, commutatorElement_def, hXa_inv, hXb_inv]
    group
  have hmem : ((pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1 * e8FrameProd K L0) *
        (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L0)⁻¹) ^ 2 ∈ H := by
    rw [pow_two]
    have hu : (pinnedX .E8 K (Tag.E8.rootCertificate.root a) 1 * e8FrameProd K L0) *
        (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L0)⁻¹ ∈ H :=
      mul_mem hU (inv_mem hV)
    exact mul_mem hu hu
  rw [← hsq]
  exact hmem

private lemma e8FrameProd_of_apply_square [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    {F : List (List ℕ)} (hF : ∀ L ∈ F, e8FrameProd K L ∈ H) {i j p : ℕ} {L : List ℕ}
    (h : (FrameStep.square i j p).apply F = some L) : e8FrameProd K L ∈ H := by
  simp only [FrameStep.apply] at h
  cases hFi : F[i]? with
  | none => simp [hFi] at h
  | some Li =>
    cases Li with
    | nil => simp [hFi] at h
    | cons a L0 =>
      cases hFj : F[j]? with
      | none => simp [hFi, hFj] at h
      | some Lj =>
        cases Lj with
        | nil => simp [hFi, hFj] at h
        | cons b L1 =>
          simp only [hFi, hFj] at h
          split at h
          · rename_i hcond
            simp only [Option.some.injEq] at h
            rw [← h]
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨hLL, hs⟩ := hcond
            rw [← hLL] at hFj
            exact e8FrameProd_square_main hs
              (by
                have := hF (a :: L0) (List.mem_of_getElem? hFi)
                simpa [e8FrameProd, List.map_cons, List.prod_cons] using this)
              (by
                have := hF (b :: L0) (List.mem_of_getElem? hFj)
                simpa [e8FrameProd, List.map_cons, List.prod_cons] using this)
          · simp at h

private lemma e8FrameProd_of_apply_perm {H : Subgroup (ModGL .E8 K)}
    {F : List (List ℕ)} (hF : ∀ L ∈ F, e8FrameProd K L ∈ H) {i : ℕ} {L M : List ℕ}
    (h : (FrameStep.perm i L).apply F = some M) : e8FrameProd K M ∈ H := by
  simp only [FrameStep.apply] at h
  cases hFi : F[i]? with
  | none => simp [hFi] at h
  | some L0 =>
    simp only [hFi] at h
    split at h
    · rename_i hcond
      simp only [Option.some.injEq] at h
      rw [← h]
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨hpair, hperm⟩ := hcond
      have hp : L0.Perm L := List.isPerm_iff.1 hperm
      exact (e8FrameProd_perm (K := K) hpair hp) ▸ hF L0 (List.mem_of_getElem? hFi)
    · simp at h

private lemma e8FrameProd_of_apply [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    {F : List (List ℕ)} (hF : ∀ L ∈ F, e8FrameProd K L ∈ H) (s : FrameStep) {L : List ℕ}
    (h : s.apply F = some L) : e8FrameProd K L ∈ H := by
  cases s with
  | comm i j p => exact e8FrameProd_of_apply_comm hF h
  | strip i j => exact e8FrameProd_of_apply_strip hF h
  | square i j p => exact e8FrameProd_of_apply_square hF h
  | perm i L0 => exact e8FrameProd_of_apply_perm hF h

theorem e8FrameProd_mem_of_mem_runSteps [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    {F : List (List ℕ)} (hF : ∀ L ∈ F, e8FrameProd K L ∈ H) (ss : List FrameStep) :
    ∀ L ∈ runSteps F ss, e8FrameProd K L ∈ H := by
  induction ss generalizing F with
  | nil => simpa [runSteps] using hF
  | cons s ss ih =>
    change ∀ L ∈ runSteps ((s.apply F).elim F fun L => F ++ [L]) ss, e8FrameProd K L ∈ H
    refine ih (F := (s.apply F).elim F fun L => F ++ [L]) ?_
    intro L hL
    cases hs : s.apply F with
    | none =>
      have hL' : L ∈ F := by simpa [hs] using hL
      exact hF L hL' 
    | some L0 =>
      have hL' : L ∈ F ++ [L0] := by simpa [hs] using hL
      rcases List.mem_append.1 hL' with hL | hL
      · exact hF L hL
      · rw [List.mem_singleton.1 hL]
        exact e8FrameProd_of_apply (s := s) hF hs

private lemma pinnedX_word_mem [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    (hn : ∀ i, weylElt .E8 K i (1 : Kˣ) ∈ H) (ω : List ℕ) {k : ℕ}
    (hk : k < Tag.E8.rootCertificate.roots.length) {c : K}
    (hc : pinnedX .E8 K (Tag.E8.rootCertificate.root k) c ∈ H) :
    pinnedX .E8 K (Tag.E8.rootCertificate.root (wordPos Tag.E8.rootCertificate ω k)) c ∈ H := by
  have hword : classListE8WordElt .E8 K ω ∈ H := by
    induction ω with
    | nil => simp [classListE8WordElt]
    | cons i ω ih =>
      rw [classListE8WordElt]
      exact mul_mem ih (hn (Tag.E8.idx i))
  have hconj := classListE8_wordElt_conj_pinnedX (τ := .E8) (K := K) ω hk c
  rw [← hconj]
  exact mul_mem (mul_mem hword hc) (inv_mem hword)

theorem pinnedX_one_mem_of_simpleRootsB [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    {F : List (List ℕ)} (hF : ∀ L ∈ F, e8FrameProd K L ∈ H) (h : simpleRootsB F = true) :
    ∀ α, IsRoot .E8 α → pinnedX .E8 K α 1 ∈ H := by
  have hsimple : ∀ j : Fin Tag.E8.rank,
      hasRootB F (Pi.single j 1) = true ∧ hasRootB F (-Pi.single j 1) = true := by
    intro j
    have h' := h
    simp only [simpleRootsB, List.all_eq_true, List.mem_finRange] at h'
    simpa [Bool.and_eq_true] using h' j
  have hpos : ∀ j, pinnedX .E8 K (Pi.single j 1) 1 ∈ H := by
    intro j
    obtain ⟨p, hpF, hpv⟩ := hasRootB_spec (hsimple j).1
    have := hF [p] hpF
    simpa [e8FrameProd, hpv] using this
  have hneg : ∀ j, pinnedX .E8 K (-Pi.single j 1) 1 ∈ H := by
    intro j
    obtain ⟨p, hpF, hpv⟩ := hasRootB_spec (hsimple j).2
    have := hF [p] hpF
    simpa [e8FrameProd, hpv] using this
  exact pinnedX_mem_of_basis (weylElt_one_mem hpos hneg) hpos

theorem pinnedX_mem_of_conj_e8FrameProd [CharP K 2] {H : Subgroup (ModGL .E8 K)} {g b p : ℕ}
    {L : List ℕ} (hs : sumB g b p = true) (hc : L.all (commB g) = true) (μ : K)
    (h1 : e8FrameProd K (b :: L) ∈ H)
    (h2 : pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ * e8FrameProd K (b :: L) *
      (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹ ∈ H) :
    pinnedX .E8 K (Tag.E8.rootCertificate.root p) μ ∈ H := by
  have hGL : e8FrameProd K (b :: L) =
      pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L := by
    simp [e8FrameProd, List.map_cons, List.prod_cons]
  rw [hGL] at h1 h2
  have hcomm : Commute (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)
      (e8FrameProd K L) := by
    rw [e8FrameProd]
    refine Commute.list_prod_right _ _ ?_
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact commute_pinnedX_of_commB (List.all_eq_true.1 hc k hk) μ 1
  have hGXg : e8FrameProd K L * (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹ =
      (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹ * e8FrameProd K L :=
    (hcomm.symm.inv_right).eq
  have hcalc : (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
        (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L) *
          (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹) *
        (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L)⁻¹ =
      ⁅pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ,
        pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1⁆ := by
    rw [commutatorElement_def]
    calc (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
          (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L) *
            (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹) *
          (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 * e8FrameProd K L)⁻¹
        = pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
            pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 *
            (e8FrameProd K L * (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹) *
            ((e8FrameProd K L)⁻¹ * (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1)⁻¹) := by
          rw [mul_inv_rev]
          group
      _ = pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
            pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 *
            ((pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹ * e8FrameProd K L) *
            ((e8FrameProd K L)⁻¹ * (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1)⁻¹) := by
          rw [hGXg]
      _ = pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
            pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1 *
            (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹ *
            (pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1)⁻¹ := by
          group
  have hX : ⁅pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ,
        pinnedX .E8 K (Tag.E8.rootCertificate.root b) 1⁆ =
      pinnedX .E8 K (Tag.E8.rootCertificate.root p) μ := by
    simpa using commutatorElement_pinnedX_of_sumB (K := K) hs μ 1
  rw [← hX, ← hcalc]
  exact mul_mem h2 (inv_mem h1)

private lemma exists_basis_of_pinnedX_mem [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    (hn : ∀ i, weylElt .E8 K i (1 : Kˣ) ∈ H) {v : Fin Tag.E8.rank → ℤ} (hv : IsRoot .E8 v)
    {c : K} (hc : pinnedX .E8 K v c ∈ H) :
    ∃ i, pinnedX .E8 K (Pi.single i 1) c ∈ H := by
  refine (IsRoot.rec (motive := fun v _ => pinnedX .E8 K v c ∈ H →
    ∃ i, pinnedX .E8 K (Pi.single i 1) c ∈ H) ?_ ?_ hv) hc
  · intro j hc
    exact ⟨j, hc⟩
  · intro i v hv ih hc
    have hconj := classListE8_weylElt_conj_pinnedX (τ := .E8) (K := K) i hv c
    have hXv : pinnedX .E8 K v c ∈ H := by
      rw [show pinnedX .E8 K v c =
          (weylElt .E8 K i 1)⁻¹ * pinnedX .E8 K (reflect .E8 i v) c * weylElt .E8 K i 1 by
        rw [← hconj]
        group]
      exact mul_mem (mul_mem (inv_mem (hn i)) hc) (hn i)
    exact ih hXv

private lemma commutator_pinnedX_single_add [CharP K 2] {j m : Fin Tag.E8.rank} {c d : K}
    (hroot : IsRoot .E8 (Pi.single j 1 + Pi.single m 1))
    (hne1 : (Pi.single j 1 : Fin Tag.E8.rank → ℤ) + Pi.single m 1 ≠ -Pi.single m 1)
    (hne2 : (Pi.single j 1 : Fin Tag.E8.rank → ℤ) + Pi.single m 1 ≠ -(-Pi.single m 1)) :
    ⁅pinnedX .E8 K (Pi.single j 1 + Pi.single m 1) c,
        pinnedX .E8 K (-Pi.single m 1) d⁆ =
      pinnedX .E8 K (Pi.single j 1) (c * d) := by
  have hβ : IsRoot .E8 (-Pi.single m 1) := isRoot_neg_single .E8 m
  have hroot_sum : IsRoot .E8 ((Pi.single j 1 + Pi.single m 1) + -Pi.single m 1) := by
    have h := isRoot_single .E8 j
    convert h using 1
    abel
  obtain ⟨hε, hform⟩ :=
    (simply_laced_root_commutator_unit .E8 (Or.inr (Or.inr (Or.inr rfl))) hroot hβ hne1
      hne2).1 hroot_sum
  have hsign : ((commConst .E8 (Pi.single j 1 + Pi.single m 1) (-Pi.single m 1) (1, 1) : ℤ) :
      K) = 1 := by
    rcases hε with h1 | h1
    · rw [h1]
      norm_num
    · rw [h1]
      rw [show ((-1 : ℤ) : K) = -(1 : K) by norm_num, CharTwo.neg_eq]
  rw [hform K c d, hsign, one_mul]
  rw [show (Pi.single j 1 + Pi.single m 1) + -Pi.single m 1 = Pi.single j 1 by abel]

private lemma pinnedX_single_mul_mem [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    {j m : Fin Tag.E8.rank} {c d : K}
    (hroot : IsRoot .E8 (Pi.single j 1 + Pi.single m 1))
    (hne1 : (Pi.single j 1 : Fin Tag.E8.rank → ℤ) + Pi.single m 1 ≠ -Pi.single m 1)
    (hne2 : (Pi.single j 1 : Fin Tag.E8.rank → ℤ) + Pi.single m 1 ≠ -(-Pi.single m 1))
    (hc : pinnedX .E8 K (Pi.single j 1 + Pi.single m 1) c ∈ H)
    (hd : pinnedX .E8 K (-Pi.single m 1) d ∈ H) :
    pinnedX .E8 K (Pi.single j 1) (c * d) ∈ H := by
  have hmem : ⁅pinnedX .E8 K (Pi.single j 1 + Pi.single m 1) c,
        pinnedX .E8 K (-Pi.single m 1) d⁆ ∈ H := commutator_mem_of_mem hc hd
  rwa [commutator_pinnedX_single_add hroot hne1 hne2] at hmem

theorem adjointGroup_le_of_pinnedX_generator [CharP K 2] {H : Subgroup (ModGL .E8 K)}
    (h1 : ∀ α, IsRoot .E8 α → pinnedX .E8 K α 1 ∈ H) {μ : K}
    (hμ : ∀ c : K, c ≠ 0 → ∃ k : ℕ, μ ^ k = c) {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot .E8 γ)
    (hμH : pinnedX .E8 K γ μ ∈ H) : adjointGroup .E8 K ≤ H := by
  have hpos : ∀ j : Fin Tag.E8.rank, pinnedX .E8 K (Pi.single j 1) 1 ∈ H :=
    fun j => h1 _ (.basis j)
  have hneg : ∀ j : Fin Tag.E8.rank, pinnedX .E8 K (-Pi.single j 1) 1 ∈ H :=
    fun j => h1 _ (isRoot_neg_single .E8 j)
  have hn : ∀ i, weylElt .E8 K i (1 : Kˣ) ∈ H := weylElt_one_mem hpos hneg
  obtain ⟨i0, hi0⟩ := exists_basis_of_pinnedX_mem hn hγ hμH
  have hi0' : pinnedX .E8 K (Tag.E8.rootCertificate.root (i0 : ℕ)) μ ∈ H := by
    simpa [(CFSG.LieType.Chevalley.RootWalk.rootCertificate_basis_table (τ := .E8)).2.1 i0]
      using hi0
  have hz : pinnedX .E8 K (Tag.E8.rootCertificate.root 0) μ ∈ H := by
    fin_cases i0
    · simpa using hi0'
    · have h := pinnedX_word_mem hn [3, 2, 1, 3, 0, 2] (k := 1) (by decide +kernel) hi0'
      rw [show wordPos Tag.E8.rootCertificate [3, 2, 1, 3, 0, 2] 1 = 0 by decide +kernel] at h
      exact h
    · have h := pinnedX_word_mem hn [0, 2] (k := 2) (by decide +kernel) hi0'
      rw [show wordPos Tag.E8.rootCertificate [0, 2] 2 = 0 by decide +kernel] at h
      exact h
    · have h := pinnedX_word_mem hn [2, 3, 0, 2] (k := 3) (by decide +kernel) hi0'
      rw [show wordPos Tag.E8.rootCertificate [2, 3, 0, 2] 3 = 0 by decide +kernel] at h
      exact h
    · have h := pinnedX_word_mem hn [3, 4, 2, 3, 0, 2] (k := 4) (by decide +kernel) hi0'
      rw [show wordPos Tag.E8.rootCertificate [3, 4, 2, 3, 0, 2] 4 = 0 by decide +kernel] at h
      exact h
    · have h := pinnedX_word_mem hn [4, 5, 3, 4, 2, 3, 0, 2] (k := 5) (by decide +kernel) hi0'
      rw [show wordPos Tag.E8.rootCertificate [4, 5, 3, 4, 2, 3, 0, 2] 5 = 0 by
        decide +kernel] at h
      exact h
    · have h := pinnedX_word_mem hn [5, 6, 4, 5, 3, 4, 2, 3, 0, 2] (k := 6)
        (by decide +kernel) hi0'
      rw [show wordPos Tag.E8.rootCertificate [5, 6, 4, 5, 3, 4, 2, 3, 0, 2] 6 = 0 by
        decide +kernel] at h
      exact h
    · have h := pinnedX_word_mem hn [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2] (k := 7)
        (by decide +kernel) hi0'
      rw [show wordPos Tag.E8.rootCertificate [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2] 7 = 0 by
        decide +kernel] at h
      exact h
  have hk1 : pinnedX .E8 K (Tag.E8.rootCertificate.root 1) μ ∈ H := by
    have h := pinnedX_word_mem hn [2, 0, 3, 1, 2, 3] (k := 0) (by decide +kernel) hz
    rwa [show wordPos Tag.E8.rootCertificate [2, 0, 3, 1, 2, 3] 0 = 1 by decide +kernel] at h
  have hk2 : pinnedX .E8 K (Tag.E8.rootCertificate.root 2) μ ∈ H := by
    have h := pinnedX_word_mem hn [2, 0] (k := 0) (by decide +kernel) hz
    rwa [show wordPos Tag.E8.rootCertificate [2, 0] 0 = 2 by decide +kernel] at h
  have hk3 : pinnedX .E8 K (Tag.E8.rootCertificate.root 3) μ ∈ H := by
    have h := pinnedX_word_mem hn [2, 0, 3, 2] (k := 0) (by decide +kernel) hz
    rwa [show wordPos Tag.E8.rootCertificate [2, 0, 3, 2] 0 = 3 by decide +kernel] at h
  have hk4 : pinnedX .E8 K (Tag.E8.rootCertificate.root 4) μ ∈ H := by
    have h := pinnedX_word_mem hn [2, 0, 3, 2, 4, 3] (k := 0) (by decide +kernel) hz
    rwa [show wordPos Tag.E8.rootCertificate [2, 0, 3, 2, 4, 3] 0 = 4 by decide +kernel] at h
  have hk5 : pinnedX .E8 K (Tag.E8.rootCertificate.root 5) μ ∈ H := by
    have h := pinnedX_word_mem hn [2, 0, 3, 2, 4, 3, 5, 4] (k := 0) (by decide +kernel) hz
    rwa [show wordPos Tag.E8.rootCertificate [2, 0, 3, 2, 4, 3, 5, 4] 0 = 5 by
      decide +kernel] at h
  have hk6 : pinnedX .E8 K (Tag.E8.rootCertificate.root 6) μ ∈ H := by
    have h := pinnedX_word_mem hn [2, 0, 3, 2, 4, 3, 5, 4, 6, 5] (k := 0) (by decide +kernel) hz
    rwa [show wordPos Tag.E8.rootCertificate [2, 0, 3, 2, 4, 3, 5, 4, 6, 5] 0 = 6 by
      decide +kernel] at h
  have hk7 : pinnedX .E8 K (Tag.E8.rootCertificate.root 7) μ ∈ H := by
    have h := pinnedX_word_mem hn [2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] (k := 0)
      (by decide +kernel) hz
    rwa [show wordPos Tag.E8.rootCertificate [2, 0, 3, 2, 4, 3, 5, 4, 6, 5, 7, 6] 0 = 7 by
      decide +kernel] at h
  have hbasis_all : ∀ j : Fin Tag.E8.rank, pinnedX .E8 K (Pi.single j 1) μ ∈ H := by
    intro j
    have h : pinnedX .E8 K (Tag.E8.rootCertificate.root (j : ℕ)) μ ∈ H := by
      fin_cases j
      · exact hz
      · exact hk1
      · exact hk2
      · exact hk3
      · exact hk4
      · exact hk5
      · exact hk6
      · exact hk7
    simpa [(CFSG.LieType.Chevalley.RootWalk.rootCertificate_basis_table (τ := .E8)).2.1 j]
      using h
  have hPμ : ∀ α, IsRoot .E8 α → pinnedX .E8 K α μ ∈ H :=
    pinnedX_mem_of_basis hn hbasis_all
  have hP0 : ∀ α, IsRoot .E8 α → pinnedX .E8 K α 0 ∈ H := by
    intro α _
    simp [pinnedX_zero]
  have hPadd : ∀ c d : K, (∀ α, IsRoot .E8 α → pinnedX .E8 K α c ∈ H) →
      (∀ α, IsRoot .E8 α → pinnedX .E8 K α d ∈ H) →
      ∀ α, IsRoot .E8 α → pinnedX .E8 K α (c + d) ∈ H := by
    intro c d hc hd α hα
    rw [pinnedX_add .E8 K α c d]
    exact mul_mem (hc α hα) (hd α hα)
  have hPmul : ∀ c d : K, (∀ α, IsRoot .E8 α → pinnedX .E8 K α c ∈ H) →
      (∀ α, IsRoot .E8 α → pinnedX .E8 K α d ∈ H) →
      ∀ α, IsRoot .E8 α → pinnedX .E8 K α (c * d) ∈ H := by
    intro c d hc hd
    have hbasis_cd : ∀ j : Fin Tag.E8.rank, pinnedX .E8 K (Pi.single j 1) (c * d) ∈ H := by
      intro j
      fin_cases j
      · have hroot : IsRoot .E8 ((Pi.single (0 : Fin 8) 1 : Fin Tag.E8.rank → ℤ) +
            (Pi.single (2 : Fin 8) 1 : Fin Tag.E8.rank → ℤ)) := by
          have h := CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single (τ := .E8)
            (i := (2 : Fin 8)) (k := (0 : Fin 8)) (by decide +kernel)
          simpa using h
        exact pinnedX_single_mul_mem hroot (by decide +kernel) (by decide +kernel)
          (hc _ hroot) (hd _ (isRoot_neg_single .E8 (2 : Fin 8)))
      · have hroot : IsRoot .E8 ((Pi.single (1 : Fin 8) 1 : Fin Tag.E8.rank → ℤ) +
            (Pi.single (3 : Fin 8) 1 : Fin Tag.E8.rank → ℤ)) := by
          have h := CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single (τ := .E8)
            (i := (3 : Fin 8)) (k := (1 : Fin 8)) (by decide +kernel)
          simpa using h
        exact pinnedX_single_mul_mem hroot (by decide +kernel) (by decide +kernel)
          (hc _ hroot) (hd _ (isRoot_neg_single .E8 (3 : Fin 8)))
      · have hroot : IsRoot .E8 ((Pi.single (2 : Fin 8) 1 : Fin Tag.E8.rank → ℤ) +
            (Pi.single (0 : Fin 8) 1 : Fin Tag.E8.rank → ℤ)) := by
          have h := CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single (τ := .E8)
            (i := (0 : Fin 8)) (k := (2 : Fin 8)) (by decide +kernel)
          simpa using h
        exact pinnedX_single_mul_mem hroot (by decide +kernel) (by decide +kernel)
          (hc _ hroot) (hd _ (isRoot_neg_single .E8 (0 : Fin 8)))
      · have hroot : IsRoot .E8 ((Pi.single (3 : Fin 8) 1 : Fin Tag.E8.rank → ℤ) +
            (Pi.single (1 : Fin 8) 1 : Fin Tag.E8.rank → ℤ)) := by
          have h := CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single (τ := .E8)
            (i := (1 : Fin 8)) (k := (3 : Fin 8)) (by decide +kernel)
          simpa using h
        exact pinnedX_single_mul_mem hroot (by decide +kernel) (by decide +kernel)
          (hc _ hroot) (hd _ (isRoot_neg_single .E8 (1 : Fin 8)))
      · have hroot : IsRoot .E8 ((Pi.single (4 : Fin 8) 1 : Fin Tag.E8.rank → ℤ) +
            (Pi.single (3 : Fin 8) 1 : Fin Tag.E8.rank → ℤ)) := by
          have h := CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single (τ := .E8)
            (i := (3 : Fin 8)) (k := (4 : Fin 8)) (by decide +kernel)
          simpa using h
        exact pinnedX_single_mul_mem hroot (by decide +kernel) (by decide +kernel)
          (hc _ hroot) (hd _ (isRoot_neg_single .E8 (3 : Fin 8)))
      · have hroot : IsRoot .E8 ((Pi.single (5 : Fin 8) 1 : Fin Tag.E8.rank → ℤ) +
            (Pi.single (4 : Fin 8) 1 : Fin Tag.E8.rank → ℤ)) := by
          have h := CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single (τ := .E8)
            (i := (4 : Fin 8)) (k := (5 : Fin 8)) (by decide +kernel)
          simpa using h
        exact pinnedX_single_mul_mem hroot (by decide +kernel) (by decide +kernel)
          (hc _ hroot) (hd _ (isRoot_neg_single .E8 (4 : Fin 8)))
      · have hroot : IsRoot .E8 ((Pi.single (6 : Fin 8) 1 : Fin Tag.E8.rank → ℤ) +
            (Pi.single (5 : Fin 8) 1 : Fin Tag.E8.rank → ℤ)) := by
          have h := CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single (τ := .E8)
            (i := (5 : Fin 8)) (k := (6 : Fin 8)) (by decide +kernel)
          simpa using h
        exact pinnedX_single_mul_mem hroot (by decide +kernel) (by decide +kernel)
          (hc _ hroot) (hd _ (isRoot_neg_single .E8 (5 : Fin 8)))
      · have hroot : IsRoot .E8 ((Pi.single (7 : Fin 8) 1 : Fin Tag.E8.rank → ℤ) +
            (Pi.single (6 : Fin 8) 1 : Fin Tag.E8.rank → ℤ)) := by
          have h := CFSG.LieType.Steinberg.Adjoint.isRoot_single_add_single (τ := .E8)
            (i := (6 : Fin 8)) (k := (7 : Fin 8)) (by decide +kernel)
          simpa using h
        exact pinnedX_single_mul_mem hroot (by decide +kernel) (by decide +kernel)
          (hc _ hroot) (hd _ (isRoot_neg_single .E8 (6 : Fin 8)))
    exact pinnedX_mem_of_basis hn hbasis_cd
  have hPpow : ∀ k : ℕ, ∀ α, IsRoot .E8 α → pinnedX .E8 K α (μ ^ k) ∈ H := by
    intro k
    induction k with
    | zero => simpa [pow_zero] using h1
    | succ k ih =>
      intro α hα
      rw [pow_succ]
      exact hPmul (μ ^ k) μ ih hPμ α hα
  have hallP : ∀ c : K, ∀ α, IsRoot .E8 α → pinnedX .E8 K α c ∈ H := by
    intro c α hα
    by_cases hc : c = 0
    · rw [hc]
      exact hP0 α hα
    · obtain ⟨k, hk⟩ := hμ c hc
      rw [← hk]
      exact hPpow k α hα
  rw [adjointGroup_eq_rootSpan (τ := .E8)]
  refine iSup₂_le fun α hα => ?_
  exact (Subgroup.closure_le H).2 (Set.range_subset_iff.2 fun c => hallP c α hα)

end Gen

end CFSG.LocalAnalysis.WeakClosure81.GS03E8
