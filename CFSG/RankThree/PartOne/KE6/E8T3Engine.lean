module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.RankThree.Lattice.SteinbergBIRoots

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint

abbrev V8 : Type := Fin Tag.E8.rank → ℤ

@[expose] def e8RootsIn (J : List (Fin Tag.E8.rank)) : List V8 :=
  (Tag.E8.artifactRoots.map (toVec Tag.E8.rank)).filter fun v =>
    (List.finRange Tag.E8.rank).all fun i => J.contains i || v i == 0

@[expose] def cartanZ (j j' : Fin Tag.E8.rank) : ℤ :=
  iform (τ := Tag.E8) (Pi.single j 1 : V8) (Pi.single j' 1 : V8)

@[expose] def consistent (c : V8) (j : Fin Tag.E8.rank) (part : List (Fin Tag.E8.rank × V8)) : Bool :=
  iform (τ := Tag.E8) c (Pi.single j 1 : V8) == -1 &&
    part.all fun p => iform (τ := Tag.E8) c p.2 == cartanZ j p.1

@[expose] def tsearch (R : List V8) :
    List (Fin Tag.E8.rank) → List (Fin Tag.E8.rank × V8) → (List (Fin Tag.E8.rank × V8) → Bool) → Bool
  | [], part, goal => goal part
  | j :: js, part, goal =>
    R.all fun c => !(consistent c j part) || tsearch R js (part ++ [(j, c)]) goal

@[expose] def relOK (part : List (Fin Tag.E8.rank × V8)) : Bool :=
  part.all fun p => decide ((part.foldl (fun (acc : V8) q => acc + (p.2 q.1) • q.2) (0 : V8)) +
    p.2 + (Pi.single p.1 1 : V8) = 0)

@[expose] def jlist (J : Finset (Fin Tag.E8.rank)) : List (Fin Tag.E8.rank) := (List.finRange Tag.E8.rank).filter (· ∈ J)

@[expose] def noT (J : List (Fin Tag.E8.rank)) : Bool :=
  tsearch (e8RootsIn J) J [] (fun part => !relOK part)

@[expose] def TValid (R : List V8) : List (Fin Tag.E8.rank) → List (Fin Tag.E8.rank × V8) → List V8 → Prop
  | [], _, [] => True
  | j :: js, part, c :: cs =>
    c ∈ R ∧ consistent c j part = true ∧ TValid R js (part ++ [(j, c)]) cs
  | _, _, _ => False

theorem tsearch_sound (R : List V8) (goal : List (Fin Tag.E8.rank × V8) → Bool) :
    ∀ (js : List (Fin Tag.E8.rank)) (part : List (Fin Tag.E8.rank × V8)) (cs : List V8),
      tsearch R js part goal = true → TValid R js part cs →
        goal (part ++ js.zip cs) = true := by
  intro js
  induction js with
  | nil =>
    intro part cs h hv
    cases cs with
    | nil => simpa [tsearch] using h
    | cons c cs => exact hv.elim
  | cons j js ih =>
    intro part cs h hv
    cases cs with
    | nil => exact hv.elim
    | cons c cs =>
      obtain ⟨hc, hcons, hv'⟩ := hv
      have h1 := (List.all_eq_true.1 h) c hc
      simp only [hcons, Bool.not_true, Bool.false_or] at h1
      have := ih (part ++ [(j, c)]) cs h1 hv'
      simpa [List.zip_cons_cons, List.append_assoc] using this

@[expose] def colT (T : WeylGroup Tag.E8) (j : Fin Tag.E8.rank) : V8 := T • (Pi.single j 1 : V8)

theorem smul_add_E8 (T : WeylGroup Tag.E8) (x y : V8) : T • (x + y) = T • x + T • y := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, ← weylMatrix_mulVec, Matrix.mulVec_add]

theorem smul_zsmul_E8 (T : WeylGroup Tag.E8) (c : ℤ) (x : V8) : T • (c • x) = c • (T • x) := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, Matrix.mulVec_smul]

theorem smul_sum_E8 (T : WeylGroup Tag.E8) {ι : Type} (s : Finset ι) (f : ι → V8) :
    T • (∑ i ∈ s, f i) = ∑ i ∈ s, T • f i := by
  rw [← weylMatrix_mulVec, Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [weylMatrix_mulVec]

theorem smul_zero_E8 (T : WeylGroup Tag.E8) : T • (0 : V8) = 0 := by
  rw [← weylMatrix_mulVec, Matrix.mulVec_zero]

variable {T : WeylGroup Tag.E8}

theorem T_cube (hrel : ∀ x : V8, T • T • x + T • x + x = 0) (x : V8) : T • T • T • x = x := by
  have h1 := hrel x
  have h2 := congrArg (fun y => T • y) h1
  simp only [smul_add_E8, smul_zero_E8] at h2
  have h3 := hrel (T • x)
  have h4 : T • T • T • x - x = 0 := by
    have : T • T • T • x + T • T • x + T • x - (T • T • x + T • x + x) = 0 := by
      rw [h2, h1, sub_zero]
    rw [← this]
    abel
  exact sub_eq_zero.1 h4

theorem cartanZ_self (j : Fin Tag.E8.rank) : cartanZ j j = 2 := by
  revert j
  decide +kernel

theorem iform_colT_single (hrel : ∀ x : V8, T • T • x + T • x + x = 0) (j : Fin Tag.E8.rank) :
    iform (τ := Tag.E8) (colT T j) (Pi.single j 1 : V8) = -1 := by
  set e : V8 := (Pi.single j 1 : V8) with he
  have h1 : iform (τ := Tag.E8) (e + T • e + T • T • e) e = 0 := by
    have : e + T • e + T • T • e = 0 := by
      have := hrel e
      rw [← this]
      abel
    rw [this]
    simp [iform]
  rw [iform_add_left, iform_add_left] at h1
  have h2 : iform (τ := Tag.E8) (T • T • e) e = iform (τ := Tag.E8) (T • e) e := by
    have h3 := iform_smul T (T • T • e) e
    rw [T_cube hrel e] at h3
    rw [← h3, iform_comm (τ := Tag.E8) e (T • e)]
  have h4 : iform (τ := Tag.E8) e e = 2 := cartanZ_self j
  change iform (τ := Tag.E8) (T • e) e = -1
  linarith

theorem iform_colT_colT (j k : Fin Tag.E8.rank) :
    iform (τ := Tag.E8) (colT T j) (colT T k) = cartanZ j k := iform_smul T _ _

theorem isRoot_colT (j : Fin Tag.E8.rank) : IsRoot Tag.E8 (colT T j) :=
  IsRoot.smul (isRoot_single Tag.E8 j) T

theorem colT_mem_e8RootsIn (js : List (Fin Tag.E8.rank)) {j : Fin Tag.E8.rank}
    (hsupp : ∀ i, i ∉ js → colT T j i = 0) : colT T j ∈ e8RootsIn js := by
  obtain ⟨l, hl, hlv⟩ := isRoot_iff_exists_mem.1 (isRoot_colT (T := T) j)
  rw [e8RootsIn, List.mem_filter]
  refine ⟨List.mem_map.2 ⟨l, hl, hlv.symm⟩, ?_⟩
  rw [List.all_eq_true]
  intro i _
  by_cases hi : i ∈ js
  · simp [hi]
  · simp [hsupp i hi]

theorem tvalid_colT (hrel : ∀ x : V8, T • T • x + T • x + x = 0) (R : List V8)
    (js : List (Fin Tag.E8.rank)) (hR : ∀ j ∈ js, colT T j ∈ R) :
    ∀ part : List (Fin Tag.E8.rank × V8), (∀ p ∈ part, p.2 = colT T p.1) →
      TValid R js part (js.map (colT T)) := by
  induction js with
  | nil => intro part _; trivial
  | cons j js ih =>
    intro part hpart
    refine ⟨hR j (List.mem_cons_self), ?_, ih (fun j' hj' => hR j' (List.mem_cons_of_mem _ hj'))
      _ ?_⟩
    · simp only [consistent, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
      refine ⟨iform_colT_single hrel j, fun p hp => ?_⟩
      rw [hpart p hp, iform_colT_colT]
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hpart p hp
      · rw [List.mem_singleton] at hp
        rw [hp]

theorem zip_map_self (js : List (Fin Tag.E8.rank)) (f : Fin Tag.E8.rank → V8) :
    js.zip (js.map f) = js.map fun j => (j, f j) := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [List.zip_cons_cons, ih]

theorem sum_single_of_supp (js : List (Fin Tag.E8.rank)) (c : V8) (hc : ∀ i, i ∉ js → c i = 0) :
    ∑ k ∈ js.toFinset, c k • (Pi.single k 1 : V8) = c := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hi : i ∈ js
  · simp [hi]
  · simp [hi, hc i hi]

theorem foldl_add_eq_sum (f : Fin Tag.E8.rank → V8) (js : List (Fin Tag.E8.rank)) (a : V8) :
    js.foldl (fun (acc : V8) k => acc + f k) a = a + (js.map f).sum := by
  induction js generalizing a with
  | nil => simp
  | cons k js ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, add_assoc]

theorem foldl_colT_eq_smul (js : List (Fin Tag.E8.rank)) (hnd : js.Nodup) (x : V8)
    (hx : ∀ i, i ∉ js → x i = 0) :
    js.foldl (fun (acc : V8) k => acc + x k • colT T k) (0 : V8) = T • x := by
  rw [foldl_add_eq_sum (fun k => x k • colT T k), zero_add, ← List.sum_toFinset _ hnd]
  conv_rhs => rw [← sum_single_of_supp js x hx]
  rw [smul_sum_E8]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_zsmul_E8]
  rfl

theorem relOK_colT (hrel : ∀ x : V8, T • T • x + T • x + x = 0) (js : List (Fin Tag.E8.rank))
    (hnd : js.Nodup) (hsupp : ∀ j ∈ js, ∀ i, i ∉ js → colT T j i = 0) :
    relOK (js.map fun j => (j, colT T j)) = true := by
  rw [relOK, List.all_eq_true]
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
  rw [decide_eq_true_eq]
  have hsum : (js.map fun j' => (j', colT T j')).foldl
      (fun (acc : V8) q => acc + (colT T j q.1) • q.2) (0 : V8) = T • colT T j := by
    rw [List.foldl_map]
    exact foldl_colT_eq_smul js hnd (colT T j) (hsupp j hj)
  change (_ : V8) + colT T j + (Pi.single j 1 : V8) = 0
  rw [hsum]
  exact hrel (Pi.single j 1 : V8)

theorem tsearch_colT (hrel : ∀ x : V8, T • T • x + T • x + x = 0) (js : List (Fin Tag.E8.rank))
    (hsupp : ∀ j ∈ js, ∀ i, i ∉ js → colT T j i = 0)
    (goal : List (Fin Tag.E8.rank × V8) → Bool)
    (h : tsearch (e8RootsIn js) js [] goal = true) :
    goal (js.map fun j => (j, colT T j)) = true := by
  have hv := tvalid_colT hrel (e8RootsIn js) js (fun j hj => colT_mem_e8RootsIn js (hsupp j hj))
    [] (fun p hp => absurd hp (List.not_mem_nil))
  have := tsearch_sound (e8RootsIn js) goal js [] (js.map (colT T)) h hv
  rwa [List.nil_append, zip_map_self] at this

theorem not_of_noT (hrel : ∀ x : V8, T • T • x + T • x + x = 0) (js : List (Fin Tag.E8.rank))
    (hnd : js.Nodup) (hsupp : ∀ j ∈ js, ∀ i, i ∉ js → colT T j i = 0) (h : noT js = true) :
    False := by
  have := tsearch_colT hrel js hsupp (fun part => !relOK part) h
  have h2 := relOK_colT hrel js hnd hsupp
  rw [h2] at this
  simp at this

end CFSG.RankThree.PartOne.KE6
