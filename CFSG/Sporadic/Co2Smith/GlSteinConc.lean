module

public import CFSG.Sporadic.Co2Smith.GlSteinEnc
public import CFSG.Sporadic.Co2Smith.GlU62SteinCheck
public import CFSG.Sporadic.Co2Smith.GlDataRoot
public import CFSG.LieType.Steinberg.Presentation

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits CFSG.Fischer
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  Native

theorem su6D_steinbergPresentation : su6D.SteinbergPresentation.{0, 0} := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero natCard_F4
  exact CFSG.LieType.Steinberg.steinbergPresentation_of_extras
    (isCTGroupDatum natCard_F4 6 (by norm_num) ζ hζ)
    (steinbergExtras natCard_F4 6 (by norm_num) ζ hζ)

section Graph

variable (gens : List (Array F4 × Array ℕ))

@[expose] def stGamma : Array (Array F4 × Array ℕ) := stBFS gens 200 #[(m6One, idRows 22)] 0

theorem stCheck_spec (h : stCheck gens = true) :
    0 < (stGamma gens).size ∧
      ((stGamma gens).getD 0 (m6One, idRows 22)).1 = m6One ∧
      ((stGamma gens).getD 0 (m6One, idRows 22)).2 = idRows 22 ∧
      (∀ i < (stGamma gens).size, ∀ j < (stGamma gens).size, i ≠ j →
        ((stGamma gens).getD i (m6One, idRows 22)).1 ≠
          ((stGamma gens).getD j (m6One, idRows 22)).1) ∧
      ∀ i < (stGamma gens).size, ∀ g ∈ gens, ∃ j < (stGamma gens).size,
        ((stGamma gens).getD j (m6One, idRows 22)).1 =
          m6Mul ((stGamma gens).getD i (m6One, idRows 22)).1 g.1 ∧
        ((stGamma gens).getD j (m6One, idRows 22)).2 =
          mulRows 22 ((stGamma gens).getD i (m6One, idRows 22)).2 g.2 := by
  simp only [stCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h0, h1, h2, fun i hi j hj hij e => ?_, fun i hi g hg => ?_⟩
  · rcases h3 i hi j hj with h | h
    · exact hij h
    · have e' : ((stBFS gens 200 #[(m6One, idRows 22)] 0).getD i (m6One, idRows 22)).1 =
          ((stBFS gens 200 #[(m6One, idRows 22)] 0).getD j (m6One, idRows 22)).1 := e
      rw [e', beq_self_eq_true] at h
      exact absurd h (by decide)
  · obtain ⟨j, hj, h5, h6⟩ := h4 i hi g hg
    exact ⟨j, hj, h5, h6⟩

theorem stCheck_fold (h : stCheck gens = true) (w : List (Array F4 × Array ℕ))
    (hw : ∀ g ∈ w, g ∈ gens) (h1 : w.foldl (fun a g => m6Mul a g.1) m6One = m6One) :
    w.foldl (fun a g => mulRows 22 a g.2) (idRows 22) = idRows 22 := by
  obtain ⟨hpos, h01, h02, hnd, hcl⟩ := stCheck_spec gens h
  set Γ := stGamma gens
  have key : ∀ w' : List (Array F4 × Array ℕ), (∀ g ∈ w', g ∈ gens) → ∀ i < Γ.size,
      ∃ j < Γ.size, (Γ.getD j (m6One, idRows 22)).1 =
          w'.foldl (fun a g => m6Mul a g.1) (Γ.getD i (m6One, idRows 22)).1 ∧
        (Γ.getD j (m6One, idRows 22)).2 =
          w'.foldl (fun a g => mulRows 22 a g.2) (Γ.getD i (m6One, idRows 22)).2 := by
    intro w'
    induction w' with
    | nil => exact fun _ i hi => ⟨i, hi, rfl, rfl⟩
    | cons g w'' ih =>
      intro hw' i hi
      obtain ⟨j₁, hj₁, e1, e2⟩ := hcl i hi g (hw' g List.mem_cons_self)
      obtain ⟨j, hj, f1, f2⟩ := ih (fun g' hg' => hw' g' (List.mem_cons_of_mem _ hg')) j₁ hj₁
      refine ⟨j, hj, ?_, ?_⟩
      · rw [f1, e1, List.foldl_cons]
      · rw [f2, e2, List.foldl_cons]
  obtain ⟨j, hj, e1, e2⟩ := key w hw 0 hpos
  rw [h01, h1] at e1
  have hj0 : j = 0 := by
    by_contra hne
    exact hnd j hj 0 hpos hne (e1.trans h01.symm)
  subst hj0
  rw [h02] at e2
  exact e2.symm

end Graph

@[expose] noncomputable def su6Root (r : Fin 18) : Fin su6D.rank → ℤ := su6Fund r

@[expose] noncomputable def su6Idx (γ : Fin su6D.rank → ℤ) : Option (Fin 18) :=
  (List.finRange 18).find? fun r => decide (su6Root r = γ)

theorem su6Idx_su6Root : ∀ r : Fin 18, su6Idx (su6Root r) = some r := by decide

@[expose] noncomputable def psiRootK (γ : Fin su6D.rank → ℤ)
    (x : su6D.rootGroup γ) : K :=
  match su6Idx γ with
  | some r => xRootK r.val (su6Entry r x).code.val
  | none => 1

theorem psiRootK_su6Root (r : Fin 18)
    (x : su6D.rootGroup (su6Root r)) :
    psiRootK (su6Root r) x = xRootK r.val (su6Entry r x).code.val := by
  unfold psiRootK
  rw [su6Idx_su6Root]

theorem su6Entry_code_mem {r : Fin 18} {x : SU6} (hx : x ∈ su6D.rootGroup (su6Fund r)) :
    (su6Entry r x).code.val ∈ stParams r.val := by
  by_cases hr : r.val < 12
  · simp only [stParams, hr, ite_true, List.mem_cons, List.not_mem_nil, or_false]
    have := (su6Entry r x).code.isLt
    omega
  · simp only [stParams, hr, ite_false, List.mem_cons, List.not_mem_nil, or_false]
    obtain ⟨c, rfl⟩ := rootGroup_le_range_long (by omega : 12 ≤ r.val) hx
    rw [su6Entry, mat_apply, coe_longRootHom, su6Pos_long r (by omega)]
    simp only [longRootMatrix, Matrix.add_apply, Matrix.one_apply_ne (su6Pos_fst_ne_rev r),
      Matrix.single_apply_same, zero_add]
    rcases (mem_traceZero_su6σ_iff _).1 (Multiplicative.toAdd c).2 with h | h
    · left
      rw [h]
      rfl
    · right
      rw [h]
      rfl

theorem rows_foldl (xs : List K) (R : Array ℕ)
    (Rs : List (Array ℕ)) (hR : (1 : K).val.val = rowsMatrix 22 R)
    (hxs : List.Forall₂ (fun x S => x.val.val = rowsMatrix 22 S) xs Rs) :
    (xs.foldl (· * ·) 1).val.val = rowsMatrix 22 (Rs.foldl (fun a S => mulRows 22 a S) R) := by
  suffices h : ∀ (a : K) (A : Array ℕ), a.val.val = rowsMatrix 22 A →
      (xs.foldl (· * ·) a).val.val = rowsMatrix 22 (Rs.foldl (fun a S => mulRows 22 a S) A) from
    h 1 R hR
  induction hxs with
  | nil => exact fun a A h => h
  | cons hxS _ ih =>
    intro a A h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ (by rw [val_val_mul, h, hxS, rowsMatrix_mulRows])

theorem m6_foldl (xs : List SU6) :
    m6Arr (mat su6σ 6 (xs.foldl (· * ·) 1)) =
      (xs.map fun x => m6Arr (mat su6σ 6 x)).foldl m6Mul m6One := by
  suffices h : ∀ a : SU6, m6Arr (mat su6σ 6 (xs.foldl (· * ·) a)) =
      (xs.map fun x => m6Arr (mat su6σ 6 x)).foldl m6Mul (m6Arr (mat su6σ 6 a)) by
    rw [h, map_one, ← m6One_eq]
  induction xs with
  | nil => exact fun a => rfl
  | cons x xs ih =>
    intro a
    rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons, map_mul, ← m6Mul_m6Arr]

@[expose] noncomputable def letIdx (p : Σ γ : Fin su6D.rank → ℤ, su6D.rootGroup γ) : Fin 18 :=
  (su6Idx p.1).getD 0

@[expose] noncomputable def letPair (p : Σ γ : Fin su6D.rank → ℤ, su6D.rootGroup γ) :
    Array F4 × Array ℕ :=
  (stElt (letIdx p).val (su6Entry (letIdx p) p.2).code.val,
    glRootRows (letIdx p).val (su6Entry (letIdx p) p.2).code.val)

theorem letIdx_eq {p : Σ γ : Fin su6D.rank → ℤ, su6D.rootGroup γ} {t : Fin 18}
    (h : p.1 = su6Root t) : letIdx p = t := by
  rw [letIdx, h, su6Idx_su6Root]
  rfl

theorem letter_mem {p : Σ γ : Fin su6D.rank → ℤ, su6D.rootGroup γ} {t : Fin 18}
    (h : p.1 = su6Root t) : (p.2 : SU6) ∈ su6D.rootGroup (su6Fund (letIdx p)) := by
  rw [letIdx_eq h]
  obtain ⟨γ, x⟩ := p
  dsimp only at h
  subst h
  exact x.2

theorem m6Arr_letter {p : Σ γ : Fin su6D.rank → ℤ, su6D.rootGroup γ} {t : Fin 18}
    (h : p.1 = su6Root t) : m6Arr (mat su6σ 6 (p.2 : SU6)) = (letPair p).1 := by
  have e := eq_su6Elt_entry (letter_mem h)
  rw [letPair]
  dsimp only
  rw [← m6Arr_su6Elt, ← e]

theorem psiRootK_letter
    {p : Σ γ : Fin su6D.rank → ℤ, su6D.rootGroup γ} {t : Fin 18} (h : p.1 = su6Root t) :
    (psiRootK p.1 p.2).val.val = rowsMatrix 22 (letPair p).2 := by
  have hs : su6Idx p.1 = some (letIdx p) := by rw [letIdx_eq h, h, su6Idx_su6Root]
  unfold psiRootK
  rw [hs, letPair, xRootK_val]

theorem relationsHold_block {B : List ℕ}
    (h : stCheck (stGens B) = true) :
    RelationsHold su6D.rootGroup {γ | ∃ t : Fin 18, t.val ∈ B ∧ γ = su6Root t} psiRootK := by
  intro l hl h1
  have hw : ∀ g ∈ l.map letPair, g ∈ stGens B := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    obtain ⟨t, htB, ht⟩ := hl p hp
    simp only [stGens, List.mem_flatMap, List.mem_map]
    refine ⟨(letIdx p).val, by rw [letIdx_eq ht]; exact htB, (su6Entry (letIdx p) p.2).code.val,
      su6Entry_code_mem (letter_mem ht), rfl⟩
  have hA : (l.map letPair).foldl (fun a g => m6Mul a g.1) m6One = m6One := by
    have e := m6_foldl (l.map fun p => (p.2 : SU6))
    rw [← List.prod_eq_foldl, h1, map_one, ← m6One_eq, List.map_map, List.foldl_map] at e
    rw [List.foldl_map]
    refine (List.foldl_ext _ _ _ fun a p hp => ?_).trans e.symm
    obtain ⟨t, -, ht⟩ := hl p hp
    simp only [Function.comp_apply, m6Arr_letter ht]
  have hK := stCheck_fold (stGens B) h (l.map letPair) hw hA
  have hKv := rows_foldl (l.map fun p => psiRootK p.1 p.2) (idRows 22)
    ((l.map letPair).map Prod.snd)
    (by rw [rowsMatrix_idRows]; rfl) (by
      simp only [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine List.forall₂_same.2 fun p hp => ?_
      obtain ⟨t, -, ht⟩ := hl p hp
      exact psiRootK_letter ht)
  have e2 : ((l.map letPair).map Prod.snd).foldl (fun a S => mulRows 22 a S) (idRows 22) =
      idRows 22 := by
    rw [List.foldl_map]
    exact hK
  rw [e2, rowsMatrix_idRows, ← List.prod_eq_foldl] at hKv
  exact eq_of_val_eq hKv


theorem mem_su6D_roots_iff' (γ : Fin su6D.rank → ℤ) :
    γ ∈ su6D.roots ↔ ∃ r, γ = su6Root r :=
  mem_su6D_roots_iff γ

theorem stFund_eq : ∀ r : Fin 18, stFund.getD r.val (0, 0, 0) =
    (su6Fund r 0, su6Fund r 1, su6Fund r 2) := by decide

theorem stOpp_iff : ∀ r s : Fin 18, stOpp r.val s.val = true ↔ su6Root s = -su6Root r := by
  decide

theorem cone_subset_block (r s : Fin 18) :
    su6D.cone (su6Root r) (su6Root s) ⊆
      {γ | ∃ t : Fin 18, t.val ∈ stBlock r.val s.val ∧ γ = su6Root t} := by
  rintro γ ⟨hγ, a, b, hab⟩
  obtain ⟨t, rfl⟩ := (mem_su6D_roots_iff' γ).1 hγ
  refine ⟨t, ?_, rfl⟩
  have e : ∀ i : Fin (6 / 2), su6Fund t i = a * su6Fund r i + b * su6Fund s i := fun i => by
    have := congrFun hab i
    simp only [su6Root] at this
    exact this
  simp only [stBlock, List.mem_filter, List.mem_range, t.isLt, true_and, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    not_le, decide_eq_true_eq]
  intro f _
  rw [stFund_eq, stFund_eq, stFund_eq]
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
  simp only [stDot] at h1 h2 h3
  rw [e 0, e 1, e 2] at h3
  have ha : (0 : ℤ) ≤ a := Int.natCast_nonneg a
  have hb : (0 : ℤ) ≤ b := Int.natCast_nonneg b
  nlinarith [mul_nonneg ha h1, mul_nonneg hb h2]

theorem glStein_parts :
    (∀ r < 18, ∀ s < 18, stOpp r s = true ∨ stCheck (stGens (stBlock r s)) = true) ∧
      stCheck (stGens [3, 9]) = true ∧ stCheck (stGens [5, 11]) = true ∧
      stCheck (stGens [14, 17]) = true := by
  have h := glStein_check
  simp only [glSteinOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem relationsHold_of_subset {S T : Set (Fin su6D.rank → ℤ)}
    (h : RelationsHold su6D.rootGroup T psiRootK) (hST : S ⊆ T) :
    RelationsHold su6D.rootGroup S psiRootK :=
  fun l hl h1 => h l (fun p hp => hST (hl p hp)) h1

theorem psiRootK_relations :
    ∀ S ∈ su6D.relsR1 ∪ su6D.relsR2, RelationsHold su6D.rootGroup S psiRootK := by
  obtain ⟨hcone, h39, h511, h1417⟩ := glStein_parts
  rintro S (⟨α, hα, β, hβ, hneg, rfl⟩ | ⟨i, rfl⟩)
  · obtain ⟨r, rfl⟩ := (mem_su6D_roots_iff' α).1 hα
    obtain ⟨s, rfl⟩ := (mem_su6D_roots_iff' β).1 hβ
    rcases hcone r.val r.isLt s.val s.isLt with hopp | hchk
    · exfalso
      apply hneg
      refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
      rw [one_smul, one_smul]
      exact (stOpp_iff r s).1 hopp
    · exact relationsHold_of_subset (relationsHold_block hchk) (cone_subset_block r s)
  · fin_cases i
    · refine relationsHold_of_subset (relationsHold_block h39) ?_
      rintro γ (rfl | rfl)
      · exact ⟨3, by decide, by decide⟩
      · exact ⟨9, by decide, by decide⟩
    · refine relationsHold_of_subset (relationsHold_block h511) ?_
      rintro γ (rfl | rfl)
      · exact ⟨5, by decide, by decide⟩
      · exact ⟨11, by decide, by decide⟩
    · refine relationsHold_of_subset (relationsHold_block h1417) ?_
      rintro γ (rfl | rfl)
      · exact ⟨14, by decide, by decide⟩
      · exact ⟨17, by decide, by decide⟩

theorem exists_thetaK :
    ∃ θ : SU6 →* K, ∀ γ ∈ su6D.roots, ∀ x : su6D.rootGroup γ, θ x = psiRootK γ x :=
  su6D_steinbergPresentation.2 K psiRootK psiRootK_relations

@[expose] noncomputable def thetaK :
    SU6 →* K :=
  Classical.choose exists_thetaK

theorem thetaK_spec
    {γ : Fin su6D.rank → ℤ} (hγ : γ ∈ su6D.roots) (x : su6D.rootGroup γ) :
    thetaK x = psiRootK γ x :=
  Classical.choose_spec exists_thetaK γ hγ x

theorem thetaK_root (r : Fin 18)
    {x : SU6} (hx : x ∈ su6D.rootGroup (su6Root r)) :
    thetaK x = xRootK r.val (su6Entry r x).code.val := by
  have := thetaK_spec ((mem_su6D_roots_iff' _).2 ⟨r, rfl⟩) ⟨x, hx⟩
  rw [this, psiRootK_su6Root]

end CFSG.Sporadic.Co2Smith
