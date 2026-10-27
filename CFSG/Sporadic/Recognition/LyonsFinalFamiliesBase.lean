
module

public import CFSG.Sporadic.Recognition.LyonsFinalFamilyInputs
public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueFacts

@[expose] public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Recognition.McLMultiplier CFSG.CosetTable

theorem getElem!_ofFn' {α : Type*} [Inhabited α] {n : ℕ} (f : Fin n → α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem lift_mk_single {G : Type*} [Group G] {m : ℕ} (g : Fin m → G) (l : Fin m × Bool) :
    FreeGroup.lift g (FreeGroup.mk [l]) = if l.2 then g l.1 else (g l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  cases b
  · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
      FreeGroup.lift_apply_of]
    simp only [Bool.false_eq_true, ite_false]
  · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
    simp only [ite_true]

theorem rep_foldr {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] {m : ℕ} (hn : n < 2 ^ 32)
    (T : Fin m × Bool → Table) (g : Fin m → G) (w : List (Fin m × Bool))
    (hT : ∀ l ∈ w, Rep n (T l) (if l.2 then g l.1 else (g l.1)⁻¹)) :
    Rep n (w.foldr (fun l acc => compT n (T l) acc) (idT n))
      (FreeGroup.lift g (FreeGroup.mk w)) := by
  induction w with
  | nil =>
    rw [← FreeGroup.one_eq_mk, map_one]
    exact Rep.idT hn
  | cons l w ih =>
    have e : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := rfl
    rw [List.foldr_cons, e, map_mul, lift_mk_single]
    exact Rep.compT (hT l List.mem_cons_self) (ih fun l' hl' => hT l' (List.mem_cons_of_mem _ hl'))

theorem lift_mk_append {G : Type*} [Group G] {m : ℕ} (g : Fin m → G) (u v : List (Fin m × Bool)) :
    FreeGroup.lift g (FreeGroup.mk (u ++ v)) =
      FreeGroup.lift g (FreeGroup.mk u) * FreeGroup.lift g (FreeGroup.mk v) := by
  rw [← FreeGroup.mul_mk, map_mul]

theorem genZ_mem (i : Fin 6) : ∀ l ∈ genZ i, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  unfold genZ at hl
  split_ifs at hl
  · simp only [List.mem_singleton] at hl
    subst hl
    simp
  · simp only [List.mem_singleton] at hl
    subst hl
    simp
  · exact Ly0.decodeWord_mem _ l hl
  · exact Ly0.decodeWord_mem _ l hl
  · exact Ly0.decodeWord_mem _ l hl
  · simp at hl

theorem invW_mem {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) :
    ∀ l ∈ invW w, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  simp only [invW, List.mem_reverse, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := hw l' hl'
  omega

noncomputable def gB (i : Fin 6) : Perm (Fin Ly0.deg) := Ly0.wG Ly0.gens0 (genZ i)

theorem gB_mem (i : Fin 6) : gB i ∈ Ly0.B0 :=
  Ly0.wG_mem Ly0.B0 Ly0.gens0 2 Ly0.gens0_mem _ (genZ_mem i)

noncomputable def gBs (i : Fin 6) : Ly0.B0 := ⟨gB i, gB_mem i⟩

theorem rep_genTabsB (h : Ly0.tabCheck = true) (i : Fin 6) :
    Rep Ly0.deg genTabsB[i.val]! (gB i) := by
  unfold genTabsB
  rw [getElem!_ofFn' _ i.isLt]
  exact Ly0.rep_word0 h _ (genZ_mem i)

theorem rep_genInvTabsB (h : Ly0.tabCheck = true) (i : Fin 6) :
    Rep Ly0.deg genInvTabsB[i.val]! (gB i)⁻¹ := by
  have e : (gB i)⁻¹ = Ly0.wG Ly0.gens0 (invW (genZ i)) := by
    unfold gB
    rw [Ly0.wG_invW Ly0.gens0 (fun l hl => (genZ_mem i l hl).1)]
  rw [e]
  unfold genInvTabsB
  rw [getElem!_ofFn' _ i.isLt]
  exact Ly0.rep_word0 h _ (invW_mem (genZ_mem i))

theorem rep_letterTabB (h : Ly0.tabCheck = true) (l : Fin 6 × Bool) :
    Rep Ly0.deg (letterTabB l) (if l.2 then gB l.1 else (gB l.1)⁻¹) := by
  unfold letterTabB
  split_ifs with hb
  · exact rep_genTabsB h l.1
  · exact rep_genInvTabsB h l.1

theorem rep_wordTabB (h : Ly0.tabCheck = true) (w : List (Fin 6 × Bool)) :
    Rep Ly0.deg (wordTabB w) (FreeGroup.lift gB (FreeGroup.mk w)) :=
  rep_foldr (by norm_num [Ly0.deg]) letterTabB gB w fun l _ => rep_letterTabB h l

theorem coe_lift_gBs (x : FreeGroup (Fin 6)) :
    ((FreeGroup.lift gBs x : Ly0.B0) : Perm (Fin Ly0.deg)) = FreeGroup.lift gB x := by
  have : Ly0.B0.subtype.comp (FreeGroup.lift gBs) = FreeGroup.lift gB :=
    FreeGroup.ext_hom _ _ fun i => by simp [gBs]
  exact DFunLike.congr_fun this x

theorem lift_gBs_eq_one (h : Ly0.tabCheck = true) {r : List (Fin 6 × Bool)}
    (hr : bWordCheck r = true) : FreeGroup.lift gBs (FreeGroup.mk r) = 1 := by
  unfold bWordCheck at hr
  rw [Bool.and_eq_true] at hr
  have h1 := (tblEq_idT_iff (by norm_num [Ly0.deg]) (rep_wordTabB h r)).1 hr.2
  apply Subtype.ext
  rw [coe_lift_gBs]
  exact h1

section Transfer

variable {G : Type} [Group G]

@[expose] noncomputable def ιG {x₁ : G} (φ : ↥(NormX x₁) ≃* Ly0.B0) : Ly0.B0 →* G :=
  (NormX x₁).subtype.comp φ.symm.toMonoidHom

@[expose] noncomputable def gOf {x₁ : G} (φ : ↥(NormX x₁) ≃* Ly0.B0) (k : G) : Fin 6 → G :=
  fun i => if i.val = 5 then k else ιG φ (gBs i)

theorem lift_gOf_bword {x₁ : G} (φ : ↥(NormX x₁) ≃* Ly0.B0) (k : G) {r : List (Fin 6 × Bool)}
    (hr : isBWord r = true) :
    FreeGroup.lift (gOf φ k) (FreeGroup.mk r) = ιG φ (FreeGroup.lift gBs (FreeGroup.mk r)) := by
  induction r with
  | nil => rw [← FreeGroup.one_eq_mk, map_one, map_one, map_one]
  | cons l r ih =>
    simp only [isBWord, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hne : l.1.val ≠ 5 := by omega
    have e : FreeGroup.mk (l :: r) = FreeGroup.mk [l] * FreeGroup.mk r := rfl
    rw [e, map_mul, map_mul, map_mul, ih (by simpa [isBWord] using hr.2), lift_mk_single,
      lift_mk_single]
    obtain ⟨i, b⟩ := l
    cases b
    · simp only [gOf, hne, Bool.false_eq_true, ite_false, map_inv]
    · simp only [gOf, hne, ite_true, ite_false]

theorem lift_gOf_bword_eq_one {x₁ : G} (φ : ↥(NormX x₁) ≃* Ly0.B0) (k : G)
    (h : Ly0.tabCheck = true) {r : List (Fin 6 × Bool)} (hr : bWordCheck r = true) :
    FreeGroup.lift (gOf φ k) (FreeGroup.mk r) = 1 := by
  have hb : isBWord r = true := (Bool.and_eq_true_iff.1 hr).1
  rw [lift_gOf_bword φ k hb, lift_gBs_eq_one h hr, map_one]

theorem lift_gOf_kk {x₁ : G} (φ : ↥(NormX x₁) ≃* Ly0.B0) {k : G} (hk : k * k = 1) :
    FreeGroup.lift (gOf φ k) (FreeGroup.mk kkRel) = 1 := by
  have e : FreeGroup.mk kkRel = FreeGroup.mk [kLetter] * FreeGroup.mk [kLetter] := rfl
  rw [e, map_mul, lift_mk_single]
  simpa [kLetter, gOf] using hk

end Transfer

section ERel

variable {G : Type} [Group G]

theorem map_wordG_wordLetter {H K : Type*} [Group H] [Group K] (ψ : H →* K) (u : ℕ → H)
    (w : List ℤ) : ψ (wordG (wordLetter u) w) = wordG (wordLetter fun j => ψ (u j)) w := by
  induction w with
  | nil => simp [wordG]
  | cons l w ih =>
    have e : ∀ (f : ℤ → H), wordG f (l :: w) = f l * wordG f w := by
      intro f
      simp [wordG]
    have e' : ∀ (f : ℤ → K), wordG f (l :: w) = f l * wordG f w := by
      intro f
      simp [wordG]
    rw [e, map_mul, ih, e']
    congr 1
    unfold wordLetter
    split_ifs
    · rfl
    · rw [map_inv]

theorem wordG_append' {X : Type*} [Group X] (f : ℤ → X) (u v : List ℤ) :
    wordG f (u ++ v) = wordG f u * wordG f v := by
  simp [wordG]

theorem wordG_cons' {X : Type*} [Group X] (f : ℤ → X) (l : ℤ) (w : List ℤ) :
    wordG f (l :: w) = f l * wordG f w := by
  simp [wordG]

theorem wordLetter_neg {X : Type*} [Group X] (u : ℕ → X) {l : ℤ} (hl : l ≠ 0) :
    wordLetter u (-l) = (wordLetter u l)⁻¹ := by
  rcases lt_trichotomy l 0 with h | h | h
  · have h1 : ¬ 0 < l := by omega
    have h2 : 0 < -l := by omega
    simp only [wordLetter, h1, h2, ite_false, ite_true, neg_neg, inv_inv]
  · exact absurd h hl
  · have h1 : ¬ 0 < -l := by omega
    simp only [wordLetter, h1, h, ite_false, ite_true, neg_neg]

theorem wordLetter_of_pos {X : Type*} [Group X] (u : ℕ → X) {l : ℤ} (h : 0 < l) :
    wordLetter u l = u (l.toNat - 1) := by
  simp only [wordLetter, h, ite_true]

theorem wordLetter_of_not_pos {X : Type*} [Group X] (u : ℕ → X) {l : ℤ} (h : ¬ 0 < l) :
    wordLetter u l = (u ((-l).toNat - 1))⁻¹ := by
  simp only [wordLetter, h, ite_false]

theorem wordG_invW {X : Type*} [Group X] (u : ℕ → X) {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0) :
    wordG (wordLetter u) (invW w) = (wordG (wordLetter u) w)⁻¹ := by
  induction w with
  | nil => simp [invW, wordG]
  | cons l w ih =>
    have hl : l ≠ 0 := hw l (by simp)
    have ih' := ih fun l' hl' => hw l' (by simp [hl'])
    have hinv : invW (l :: w) = invW w ++ [-l] := by simp [invW]
    have e1 : wordG (wordLetter u) [-l] = (wordLetter u l)⁻¹ := by
      simp [wordG, wordLetter_neg u hl]
    rw [hinv, wordG_append', ih', e1, wordG_cons', mul_inv_rev]

theorem wordG_flatMap_subst {X : Type*} [Group X] (u : ℕ → X) (E : ℕ → List ℤ)
    (hE : ∀ j < 4, ∀ l ∈ E j, l ≠ 0) (Ut : List ℤ) (hUt : ∀ l ∈ Ut, l ≠ 0 ∧ l.natAbs ≤ 4) :
    wordG (wordLetter u)
        (Ut.flatMap fun l => if 0 < l then E (l - 1).toNat else invW (E (-l - 1).toNat)) =
      wordG (wordLetter fun j => wordG (wordLetter u) (E j)) Ut := by
  induction Ut with
  | nil => simp [wordG]
  | cons l Ut ih =>
    have hl := hUt l List.mem_cons_self
    have ih' := ih fun l' hl' => hUt l' (List.mem_cons_of_mem _ hl')
    rw [List.flatMap_cons, wordG_append', ih', wordG_cons']
    congr 1
    by_cases h : 0 < l
    · rw [ite_eq_left h, wordLetter_of_pos _ h]
      have : (l - 1).toNat = l.toNat - 1 := by omega
      rw [this]
    · rw [ite_eq_right h, wordLetter_of_not_pos _ h, wordG_invW u (hE _ (by omega))]
      have : (-l - 1).toNat = (-l).toNat - 1 := by omega
      rw [this]

theorem wordG_wordLetter_congr {X : Type*} [Group X] (f g : ℕ → X) (hfg : ∀ j < 4, f j = g j)
    (w : List ℤ) (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 4) :
    wordG (wordLetter f) w = wordG (wordLetter g) w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have hl := hw l List.mem_cons_self
    rw [wordG_cons', wordG_cons', ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')]
    congr 1
    by_cases h : 0 < l
    · rw [wordLetter_of_pos _ h, wordLetter_of_pos _ h, hfg _ (by omega)]
    · rw [wordLetter_of_not_pos _ h, wordLetter_of_not_pos _ h, hfg _ (by omega)]

theorem substW_range (hY : Ly1080.YOK) {Ut : List ℤ}
    (hUt : ∀ l ∈ Ut, l ≠ 0 ∧ l.natAbs ≤ 4) : ∀ l ∈ substW Ut, l ≠ 0 ∧ l.natAbs ≤ 4 := by
  intro l' hl'
  simp only [substW, List.mem_flatMap] at hl'
  obtain ⟨l, hl, hl'⟩ := hl'
  have hl0 := hUt l hl
  split_ifs at hl' with h
  · exact Ly1080.words_range₄ hY _ (List.mem_append_left _ (erelWords_get_mem hY (by omega))) l' hl'
  · have hneg : -l' ∈ Ly1080.erelWords[(-l - 1).toNat]! := by simpa [invW] using hl'
    have := Ly1080.words_range₄ hY _
      (List.mem_append_left _ (erelWords_get_mem hY (i := (-l - 1).toNat) (by omega))) (-l') hneg
    omega

theorem isBWord_iff (r : List (Fin 6 × Bool)) : isBWord r = true ↔ ∀ l ∈ r, l.1.val < 5 := by
  simp [isBWord]

@[expose] def EEvHolds (ev : EEv) : Prop :=
  (∀ l ∈ ev.1, l ≠ 0 ∧ l.natAbs ≤ 4) ∧ (∀ l ∈ ev.2.1, l.1.val < 5) ∧
    (∀ l ∈ ev.2.2, l.1.val < 5) ∧
    FreeGroup.lift gB (FreeGroup.mk ev.2.1) = wordG (wordLetter Ly0.uG) ev.1 ∧
    wordG (wordLetter Ly0.uG) (substW ev.1) * FreeGroup.lift gB (FreeGroup.mk ev.2.2) = 1

theorem eEvHolds_of_eCheck (hY : Ly1080.YOK) (hM : Ly0.tabCheck = true) {ev : EEv}
    (h : eCheck ev = true) : EEvHolds ev := by
  obtain ⟨Ut, U, V⟩ := ev
  simp only [eCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hUt, hU⟩, hV⟩, hE1⟩, hE2⟩ := h
  have hUt' : ∀ l ∈ Ut, l ≠ 0 ∧ l.natAbs ≤ 4 := by
    intro l hl
    simp only [isUWord, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hUt
    exact hUt l hl
  have hn : Ly0.deg < 2 ^ 32 := by norm_num [Ly0.deg]
  have hrepU : Rep Ly0.deg (wordT Ly0.deg Glue.uLetB Ut) (wordG (wordLetter Ly0.uG) Ut) :=
    Rep.wordT hn _ fun l hl => Glue.rep_uLetB hM (hUt' l hl)
  have hrepS : Rep Ly0.deg (wordT Ly0.deg Glue.uLetB (substW Ut))
      (wordG (wordLetter Ly0.uG) (substW Ut)) :=
    Rep.wordT hn _ fun l hl => Glue.rep_uLetB hM (substW_range hY hUt' l hl)
  exact ⟨hUt', (isBWord_iff U).1 hU, (isBWord_iff V).1 hV,
    (tblEq_iff_eq (rep_wordTabB hM U) hrepU).1 hE1,
    (tblEq_idT_iff hn (Rep.compT hrepS (rep_wordTabB hM V))).1 hE2⟩

theorem lift_gOf_erel_of_holds {x₁ x₂ x₃ : G} (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hφY : ((NN x₁ x₂).subgroupOf (NormX x₁)).map φ.toMonoidHom = Ly0.Y0) (M : ModelGlue)
    {k : G} (hk : IsSwapY0 x₁ x₂ x₃ (borelPhiY φ hφY M.ιY) k) (hY : Ly1080.YOK)
    {ev : EEv} (h : EEvHolds ev) :
    FreeGroup.lift (gOf φ k) (FreeGroup.mk (eRelOf ev)) = 1 := by
  obtain ⟨Ut, U, V⟩ := ev
  obtain ⟨hUt', hU, hV, hUperm, hWV⟩ := h
  have hU : isBWord U = true := (isBWord_iff U).2 hU
  have hV : isBWord V = true := (isBWord_iff V).2 hV
  have hE0 : ∀ j < 4, ∀ l ∈ Ly1080.erelWords[j]!, l ≠ 0 := fun j hj l hl =>
    (Ly1080.words_range₄ hY _ (List.mem_append_left _ (erelWords_get_mem hY hj)) l hl).1
  have hcoe : ∀ w : List ℤ, ((wordG (wordLetter Ly0.uB) w : Ly0.B0) : Perm (Fin Ly0.deg)) =
      wordG (wordLetter Ly0.uG) w := fun w => map_wordG_wordLetter Ly0.B0.subtype Ly0.uB w
  have hUs : FreeGroup.lift gBs (FreeGroup.mk U) = wordG (wordLetter Ly0.uB) Ut :=
    Subtype.ext (by rw [coe_lift_gBs, hUperm, hcoe])
  have hWVs : wordG (wordLetter Ly0.uB) (substW Ut) * FreeGroup.lift gBs (FreeGroup.mk V) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hcoe, coe_lift_gBs]
    exact hWV
  have hVs : FreeGroup.lift gBs (FreeGroup.mk V) = (wordG (wordLetter Ly0.uB) (substW Ut))⁻¹ :=
    eq_inv_of_mul_eq_one_right hWVs
  have hkk : k * k = 1 := hk.mul_self
  have hmapι : ∀ w : List ℤ, ιG φ (wordG (wordLetter Ly0.uB) w) =
      wordG (wordLetter (borelU φ)) w := fun w => map_wordG_wordLetter (ιG φ) Ly0.uB w
  have hsubst : wordG (wordLetter (borelU φ)) (substW Ut) =
      k * wordG (wordLetter (borelU φ)) Ut * k⁻¹ := by
    have h1 := wordG_flatMap_subst (borelU φ) (fun j => Ly1080.erelWords[j]!) hE0 Ut hUt'
    have h2 := map_wordG_wordLetter (MulAut.conj k).toMonoidHom (borelU φ) Ut
    unfold substW
    rw [h1]
    have h3 : wordG (wordLetter fun j => wordG (wordLetter (borelU φ)) Ly1080.erelWords[j]!) Ut =
        wordG (wordLetter fun j => (MulAut.conj k).toMonoidHom (borelU φ j)) Ut :=
      wordG_wordLetter_congr _ _ (fun j hj => (borel_erelators hk hY hj).symm) Ut hUt'
    rw [h3, ← h2]
    rfl
  have e : eRelOf (Ut, U, V) = [kLetter] ++ (U ++ ([kLetter] ++ V)) := rfl
  rw [e, lift_mk_append, lift_mk_append, lift_mk_append, lift_mk_single,
    lift_gOf_bword φ k hU, lift_gOf_bword φ k hV, hUs, hVs, map_inv, hmapι, hmapι, hsubst]
  have h5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  simp only [kLetter, gOf, h5, ite_true]
  set a := wordG (wordLetter (borelU φ)) Ut
  have e2 : k * (a * (k * (k * a * k⁻¹)⁻¹)) = k * a * (k * k) * a⁻¹ * k⁻¹ := by group
  rw [e2, hkk]
  group

theorem lift_gOf_erel {x₁ x₂ x₃ : G} (φ : ↥(NormX x₁) ≃* Ly0.B0)
    (hφY : ((NN x₁ x₂).subgroupOf (NormX x₁)).map φ.toMonoidHom = Ly0.Y0) (M : ModelGlue)
    {k : G} (hk : IsSwapY0 x₁ x₂ x₃ (borelPhiY φ hφY M.ιY) k) (hY : Ly1080.YOK)
    (hM : Ly0.tabCheck = true) {ev : EEv} (h : eCheck ev = true) :
    FreeGroup.lift (gOf φ k) (FreeGroup.mk (eRelOf ev)) = 1 :=
  lift_gOf_erel_of_holds φ hφY M hk hY (eEvHolds_of_eCheck hY hM h)

end ERel

section TrRel

theorem zOf_true (i : Fin 5) : zOf (i, true) = (i.val : ℤ) + 1 := by simp [zOf]

theorem zOf_false (i : Fin 5) : zOf (i, false) = -((i.val : ℤ) + 1) := by simp [zOf]

theorem zOf_ne_zero (l : Fin 5 × Bool) : zOf l ≠ 0 := by
  obtain ⟨i, b⟩ := l
  cases b
  · rw [zOf_false]; omega
  · rw [zOf_true]; omega

theorem zOf_natAbs (l : Fin 5 × Bool) : (zOf l).natAbs = l.1.val + 1 := by
  obtain ⟨i, b⟩ := l
  cases b
  · show (zOf (i, false)).natAbs = i.val + 1
    rw [zOf_false]; omega
  · show (zOf (i, true)).natAbs = i.val + 1
    rw [zOf_true]; omega

theorem trLetG_zOf (l : Fin 5 × Bool) :
    Ly243.trLetG (zOf l) = if l.2 then Ly243.gg l.1.val else (Ly243.gg l.1.val)⁻¹ := by
  obtain ⟨i, b⟩ := l
  cases b
  · have h1 : ¬ (0 : ℤ) < zOf (i, false) := by rw [zOf_false]; omega
    have h2 : (-zOf (i, false)).toNat - 1 = i.val := by rw [zOf_false]; omega
    simp only [Ly243.trLetG, h1, ite_false, h2, Bool.false_eq_true]
  · have h1 : (0 : ℤ) < zOf (i, true) := by rw [zOf_true]; omega
    have h2 : (zOf (i, true)).toNat - 1 = i.val := by rw [zOf_true]; omega
    simp only [Ly243.trLetG, h1, ite_true, h2]

theorem wordLetter_txG_zOf (l : Fin 5 × Bool) :
    wordLetter Glue.txG (zOf l) = if l.2 then Glue.txG l.1.val else (Glue.txG l.1.val)⁻¹ := by
  obtain ⟨i, b⟩ := l
  cases b
  · have h1 : ¬ (0 : ℤ) < zOf (i, false) := by rw [zOf_false]; omega
    have h2 : (-zOf (i, false)).toNat - 1 = i.val := by rw [zOf_false]; omega
    simp only [wordLetter, h1, ite_false, h2, Bool.false_eq_true]
  · have h1 : (0 : ℤ) < zOf (i, true) := by rw [zOf_true]; omega
    have h2 : (zOf (i, true)).toNat - 1 = i.val := by rw [zOf_true]; omega
    simp only [wordLetter, h1, ite_true, h2]

theorem rep_trWordTab (hT : Ly243.trCheck = true) (w : List (Fin 5 × Bool)) :
    Rep Ly243.deg (trWordTab w)
      (FreeGroup.lift (fun i : Fin 5 => Ly243.gg i.val) (FreeGroup.mk w)) :=
  rep_foldr (by norm_num [Ly243.deg]) (fun l => Ly243.trLet (zOf l))
    (fun i : Fin 5 => Ly243.gg i.val) w fun l _ => by
      have := Ly243.rep_trLet hT (l := zOf l)
        ⟨zOf_ne_zero l, by have := l.1.isLt; rw [zOf_natAbs]; omega⟩
      rwa [trLetG_zOf] at this

noncomputable def txP (i : Fin 5) : Perm (Fin Ly0.deg) := Glue.txG i.val

theorem txP_def (i : Fin 5) : txP i = Glue.txG i.val := by unfold txP; rfl

theorem rep_txWordTab (hM : Ly0.tabCheck = true) {t : List (Fin 5 × Bool)}
    (ht : isTxWord t = true) :
    Rep Ly0.deg (txWordTab t) (FreeGroup.lift txP (FreeGroup.mk t)) :=
  rep_foldr (by norm_num [Ly0.deg]) (fun l => Glue.txLetB (zOf l)) txP t fun l hl => by
    have hl4 : l.1.val < 4 := by
      simp only [isTxWord, List.all_eq_true, decide_eq_true_eq] at ht
      exact ht l hl
    have := Glue.rep_txLetB hM (l := zOf l) ⟨zOf_ne_zero l, by rw [zOf_natAbs]; omega⟩
    rwa [wordLetter_txG_zOf] at this

theorem lift_congr {K : Type*} [Group K] {m : ℕ} (g g' : Fin m → K) (w : List (Fin m × Bool))
    (h : ∀ l ∈ w, g l.1 = g' l.1) :
    FreeGroup.lift g (FreeGroup.mk w) = FreeGroup.lift g' (FreeGroup.mk w) := by
  induction w with
  | nil => rw [← FreeGroup.one_eq_mk, map_one, map_one]
  | cons l w ih =>
    have e : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := rfl
    rw [e, map_mul, map_mul, ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'), lift_mk_single,
      lift_mk_single, h l List.mem_cons_self]

theorem map_lift_mk {H K : Type*} [Group H] [Group K] {m : ℕ} (ψ : H →* K) (g : Fin m → H)
    (w : List (Fin m × Bool)) :
    ψ (FreeGroup.lift g (FreeGroup.mk w)) = FreeGroup.lift (fun i => ψ (g i)) (FreeGroup.mk w) := by
  induction w with
  | nil => rw [← FreeGroup.one_eq_mk, map_one, map_one, map_one]
  | cons l w ih =>
    have e : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := rfl
    rw [e, map_mul, map_mul, map_mul, ih, lift_mk_single, lift_mk_single]
    obtain ⟨i, b⟩ := l
    cases b <;> simp [map_inv]

end TrRel

section TrTransfer

variable {G : Type} [Group G]

noncomputable def gT5 {x₁ : G} (φ : ↥(NormX x₁) ≃* Ly0.B0) (M : ModelGlue) (k : G) : Fin 5 → G :=
  fun i => if h : i.val < 4 then borelTx φ M ⟨i.val, h⟩ else k

@[expose] def TrSegHolds (sg : TrSeg) : Prop :=
  (∀ l ∈ sg.1, l.1.val < 5) ∧ (∀ l ∈ sg.2, l.1.val < 4) ∧
    FreeGroup.lift gB (FreeGroup.mk sg.1) = FreeGroup.lift txP (FreeGroup.mk sg.2)

theorem trSegHolds_of_segCheck (hM : Ly0.tabCheck = true) {sg : TrSeg} (h : segCheck sg = true) :
    TrSegHolds sg := by
  obtain ⟨s, t⟩ := sg
  simp only [segCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hs, ht⟩, hE⟩ := h
  refine ⟨(isBWord_iff s).1 hs, ?_, (tblEq_iff_eq (rep_wordTabB hM s) (rep_txWordTab hM ht)).1 hE⟩
  intro l hl
  simp only [isTxWord, List.all_eq_true, decide_eq_true_eq] at ht
  exact ht l hl

theorem lift_gOf_seg_of_holds {x₁ : G} (φ : ↥(NormX x₁) ≃* Ly0.B0) (M : ModelGlue)
    (hMtx : ∀ i : Fin 4, M.txW i = Glue.txWords.getD i.val []) (k : G) {sg : TrSeg}
    (h : TrSegHolds sg) :
    FreeGroup.lift (gOf φ k) (FreeGroup.mk sg.1) =
      FreeGroup.lift (gT5 φ M k) (FreeGroup.mk sg.2) := by
  obtain ⟨s, t⟩ := sg
  obtain ⟨hs, hl4, h1⟩ := h
  have hs : isBWord s = true := (isBWord_iff s).2 hs
  let txBs : Fin 5 → Ly0.B0 := fun i =>
    if h : i.val < 4 then ((M.tx ⟨i.val, h⟩ : ↥Ly0.Tx) : Ly0.B0) else 1
  have hcoe : ∀ l ∈ t, ((txBs l.1 : Ly0.B0) : Perm (Fin Ly0.deg)) = txP l.1 := by
    intro l hl
    have h4 := hl4 l hl
    simp only [txBs, h4, dite_true]
    rw [M.tx_val, hMtx]
    rfl
  have h2 : FreeGroup.lift gBs (FreeGroup.mk s) = FreeGroup.lift txBs (FreeGroup.mk t) := by
    apply Subtype.ext
    rw [coe_lift_gBs, h1]
    change _ = Ly0.B0.subtype (FreeGroup.lift txBs (FreeGroup.mk t))
    rw [map_lift_mk]
    exact (lift_congr _ _ t fun l hl => (hcoe l hl).symm)
  rw [lift_gOf_bword φ k hs, h2, map_lift_mk]
  apply lift_congr
  intro l hl
  have h4 := hl4 l hl
  simp only [txBs, gT5, h4, dite_true]
  rfl

theorem lift_gOf_rest {x₁ : G} (φ : ↥(NormX x₁) ≃* Ly0.B0) (M : ModelGlue)
    (hMtx : ∀ i : Fin 4, M.txW i = Glue.txWords.getD i.val []) (k : G) (rest : List TrSeg)
    (h : ∀ sg ∈ rest, TrSegHolds sg) :
    FreeGroup.lift (gOf φ k) (FreeGroup.mk (rest.flatMap fun sg => kLetter :: sg.1)) =
      FreeGroup.lift (gT5 φ M k)
        (FreeGroup.mk (rest.flatMap fun sg => ((4 : Fin 5), true) :: sg.2)) := by
  induction rest with
  | nil => simp only [List.flatMap_nil, ← FreeGroup.one_eq_mk, map_one]
  | cons sg rest ih =>
    rw [List.flatMap_cons, List.flatMap_cons,
      show kLetter :: sg.1 = [kLetter] ++ sg.1 from rfl,
      show ((4 : Fin 5), true) :: sg.2 = [((4 : Fin 5), true)] ++ sg.2 from rfl,
      lift_mk_append, lift_mk_append, lift_mk_append, lift_mk_append, lift_mk_single,
      lift_mk_single, lift_gOf_seg_of_holds φ M hMtx k (h sg List.mem_cons_self),
      ih fun sg' hsg' => h sg' (List.mem_cons_of_mem _ hsg')]
    simp [kLetter, gOf, gT5]

end TrTransfer

section TrFinal

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

@[expose] def TrEvHolds (ev : TrEv) : Prop :=
  TrSegHolds ev.1 ∧ (∀ sg ∈ ev.2, TrSegHolds sg) ∧
    FreeGroup.lift (fun i : Fin 5 => Ly243.gg i.val) (FreeGroup.mk (trWord ev)) = 1

theorem trEvHolds_of_trCheck (hT : Ly243.trCheck = true) (hM : Ly0.tabCheck = true) {ev : TrEv}
    (h : trCheck ev = true) : TrEvHolds ev := by
  simp only [trCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h0, hrest⟩, h243⟩ := h
  exact ⟨trSegHolds_of_segCheck hM h0, fun sg hsg => trSegHolds_of_segCheck hM (hrest sg hsg),
    (tblEq_idT_iff (by norm_num [Ly243.deg]) (rep_trWordTab hT _)).1 h243⟩

theorem lift_gOf_trrel_of_holds (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hY : Ly1080.YOK) (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true)
    (φ : ↥(NormX (x₁ : G)) ≃* Ly0.B0)
    (hφY : ((NN (x₁ : G) (x₂ : G)).subgroupOf (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Y0)
    (hφT : ((normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Tx)
    (hφK : ((NN (x₁ : G) (x₂ : G) ⊓ normalizer (zpowers (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Txy) (M : ModelGlue)
    (hMtx : ∀ i : Fin 4, M.txW i = Glue.txWords.getD i.val []) {k : G}
    (hk : IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) (borelPhiY φ hφY M.ιY) k) {ev : TrEv}
    (h : TrEvHolds ev) :
    FreeGroup.lift (gOf φ k) (FreeGroup.mk (trRel ev)) = 1 := by
  obtain ⟨⟨s0, t0⟩, rest⟩ := ev
  obtain ⟨h0, hrest, hmodel⟩ := h
  have key := D.lift_eq_one_of_tr_borel S hY hT hτ φ hφY hφT hφK M hk
    (FreeGroup.mk (trWord ((s0, t0), rest))) hmodel
  have hsegs := lift_gOf_rest φ M hMtx k rest hrest
  have hseg0 := lift_gOf_seg_of_holds φ M hMtx k (sg := (s0, t0)) h0
  rw [trRel, lift_mk_append]
  simp only at hseg0
  rw [hseg0, hsegs, ← lift_mk_append]
  exact key

theorem lift_gOf_trrel (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hY : Ly1080.YOK) (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true)
    (hM : Ly0.tabCheck = true) (φ : ↥(NormX (x₁ : G)) ≃* Ly0.B0)
    (hφY : ((NN (x₁ : G) (x₂ : G)).subgroupOf (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Y0)
    (hφT : ((normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Tx)
    (hφK : ((NN (x₁ : G) (x₂ : G) ⊓ normalizer (zpowers (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Txy) (M : ModelGlue)
    (hMtx : ∀ i : Fin 4, M.txW i = Glue.txWords.getD i.val []) {k : G}
    (hk : IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) (borelPhiY φ hφY M.ιY) k) {ev : TrEv}
    (h : trCheck ev = true) :
    FreeGroup.lift (gOf φ k) (FreeGroup.mk (trRel ev)) = 1 :=
  lift_gOf_trrel_of_holds D S hY hT hτ φ hφY hφT hφK M hMtx hk (trEvHolds_of_trCheck hT hM h)

end TrFinal

section Final

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

omit [Finite G] in
theorem gOf_zero_ne_one {x₁ : G} (φ : ↥(NormX x₁) ≃* Ly0.B0) (k : G) (hM : Ly0.ModelChecks) :
    gOf φ k 0 ≠ 1 := by
  have h0 : ((0 : Fin 6) : ℕ) ≠ 5 := by decide
  have hc : gBs 0 ≠ 1 := by
    intro h1
    have hcG : (gBs 0 : Perm (Fin Ly0.deg)) = Ly0.cG := by
      show Ly0.wG Ly0.gens0 (genZ 0) = Ly0.cG
      have : genZ 0 = [1] := rfl
      rw [this, Ly0.wG_cons, Ly0.wG_nil, mul_one,
        Ly0.letterG_pos Ly0.gens0 (by norm_num : (0 : ℤ) < 1)]
      exact Ly0.gens0_zero
    have h2 : Ly0.cB = 1 := Subtype.ext (by rw [Ly0.coe_cB, ← hcG, h1])
    exact Ly0.cB_xB_ne hM.tab hM.struct (by rw [h2, one_mul, mul_one])
  intro h1
  simp only [gOf, h0, ite_false] at h1
  apply hc
  have : φ.symm (gBs 0) = 1 := Subtype.ext h1
  simpa using this

@[expose] def FamRel (eEvs : List EEv) (trEvs : List TrEv) (r : List (Fin 6 × Bool)) : Prop :=
  ((∀ l ∈ r, l.1.val < 5) ∧ FreeGroup.lift gBs (FreeGroup.mk r) = 1) ∨ r = kkRel ∨
    (∃ e ∈ eEvs, r = eRelOf e ∧ EEvHolds e) ∨ ∃ ev ∈ trEvs, r = trRel ev ∧ TrEvHolds ev

theorem lift_gOf_of_famRel (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (hY : Ly1080.YOK)
    (hT : Ly243.trCheck = true) (hτ : Tau.tauOK = true) (φ : ↥(NormX (x₁ : G)) ≃* Ly0.B0)
    (hφY : ((NN (x₁ : G) (x₂ : G)).subgroupOf (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Y0)
    (hφT : ((normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Tx)
    (hφK : ((NN (x₁ : G) (x₂ : G) ⊓ normalizer (zpowers (x₃ : G) : Set G)).subgroupOf
      (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Txy) (M : ModelGlue)
    (hMtx : ∀ i : Fin 4, M.txW i = Glue.txWords.getD i.val []) {k : G}
    (hk : IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) (borelPhiY φ hφY M.ιY) k)
    {eEvs : List EEv} {trEvs : List TrEv} {R : List (List (Fin 6 × Bool))}
    (hfam : ∀ r ∈ R, FamRel eEvs trEvs r) :
    ∀ r ∈ R, FreeGroup.lift (gOf φ k) (FreeGroup.mk r) = 1 := by
  intro r hr
  rcases hfam r hr with ⟨hb, h1⟩ | hkk | ⟨e, -, hre, hce⟩ | ⟨ev, -, hrev, hcev⟩
  · rw [lift_gOf_bword φ k ((isBWord_iff r).2 hb), h1, map_one]
  · rw [hkk]
    exact lift_gOf_kk φ hk.mul_self
  · rw [hre]
    exact lift_gOf_erel_of_holds φ hφY M hk hY hce
  · rw [hrev]
    exact lift_gOf_trrel_of_holds D S hY hT hτ φ hφY hφT hφK M hMtx hk hcev

end Final

end CFSG.Sporadic.Recognition.LyonsSims.LyFinal
