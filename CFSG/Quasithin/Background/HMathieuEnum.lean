module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Gen

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.QuasithinUnique.Setup.X1

variable {P : Type*} [Group P]

section Subprods

theorem mem_subprods_cons {y z : P} {l : List P} :
    z ∈ subprods (y :: l) ↔ z ∈ subprods l ∨ ∃ w ∈ subprods l, y * w = z := by
  simp [subprods, List.mem_append, List.mem_map]

theorem mem_subprods_of_mem {y : P} {l : List P} (h : y ∈ l) : y ∈ subprods l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [mem_subprods_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inr ⟨1, one_mem_subprods l, mul_one _⟩
    · exact Or.inl (ih h)

@[expose] def IsCommInvol (l : List P) : Prop :=
  (∀ x ∈ l, x * x = 1) ∧ ∀ x ∈ l, ∀ y ∈ l, x * y = y * x

theorem IsCommInvol.tail {y : P} {l : List P} (h : IsCommInvol (y :: l)) : IsCommInvol l :=
  ⟨fun x hx => h.1 x (List.mem_cons_of_mem y hx),
    fun x hx z hz => h.2 x (List.mem_cons_of_mem y hx) z (List.mem_cons_of_mem y hz)⟩

theorem isCommInvol_of_indepList {l : List P} (h : IndepList l) : IsCommInvol l := by
  induction h with
  | nil => exact ⟨by simp, by simp⟩
  | cons x l hx _ hc _ _ ih =>
    refine ⟨fun z hz => ?_, fun a ha b hb => ?_⟩
    · rcases List.mem_cons.1 hz with hz' | hz'
      · rw [hz']; exact hx
      · exact ih.1 z hz'
    · rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
      · rw [ha', hb']
      · rw [ha']; exact hc b hb'
      · rw [hb']; exact (hc a ha').symm
      · exact ih.2 a ha' b hb'

theorem commute_subprods {y : P} {l : List P} (h : ∀ x ∈ l, y * x = x * y) :
    ∀ z ∈ subprods l, y * z = z * y := by
  induction l with
  | nil =>
    intro z hz
    simp only [subprods, List.mem_singleton] at hz
    rw [hz, mul_one, one_mul]
  | cons a l ih =>
    intro z hz
    have hl : ∀ x ∈ l, y * x = x * y := fun x hx => h x (List.mem_cons_of_mem a hx)
    rcases mem_subprods_cons.1 hz with hz | ⟨w, hw, rfl⟩
    · exact ih hl z hz
    · rw [← mul_assoc, h a List.mem_cons_self, mul_assoc, ih hl w hw, ← mul_assoc]

theorem mul_mem_subprods {l : List P} (h : IsCommInvol l) :
    ∀ s ∈ subprods l, ∀ t ∈ subprods l, s * t ∈ subprods l := by
  induction l with
  | nil =>
    intro s hs t ht
    simp only [subprods, List.mem_singleton] at hs ht
    rw [hs, ht, mul_one]
    simp [subprods]
  | cons y l ih =>
    have hl := h.tail
    have hy : y * y = 1 := h.1 y List.mem_cons_self
    have hyc : ∀ x ∈ l, y * x = x * y := fun x hx =>
      h.2 y List.mem_cons_self x (List.mem_cons_of_mem y hx)
    intro s hs t ht
    rw [mem_subprods_cons] at hs ht ⊢
    rcases hs with hs | ⟨s', hs', rfl⟩ <;> rcases ht with ht | ⟨t', ht', rfl⟩
    · exact Or.inl (ih hl s hs t ht)
    · right
      refine ⟨s * t', ih hl s hs t' ht', ?_⟩
      rw [← mul_assoc, commute_subprods hyc s hs, mul_assoc]
    · exact Or.inr ⟨s' * t, ih hl s' hs' t ht, by rw [mul_assoc]⟩
    · left
      have : y * s' * (y * t') = s' * t' := by
        rw [mul_assoc, ← mul_assoc s', ← commute_subprods hyc s' hs', ← mul_assoc,
          ← mul_assoc, hy, one_mul]
      rw [this]
      exact ih hl s' hs' t' ht'

theorem sq_eq_one_of_mem_subprods {l : List P} (h : IsCommInvol l) :
    ∀ s ∈ subprods l, s * s = 1 := by
  induction l with
  | nil =>
    intro s hs
    simp only [subprods, List.mem_singleton] at hs
    rw [hs, mul_one]
  | cons y l ih =>
    have hl := h.tail
    have hy : y * y = 1 := h.1 y List.mem_cons_self
    have hyc : ∀ x ∈ l, y * x = x * y := fun x hx =>
      h.2 y List.mem_cons_self x (List.mem_cons_of_mem y hx)
    intro s hs
    rcases mem_subprods_cons.1 hs with hs | ⟨w, hw, rfl⟩
    · exact ih hl s hs
    · rw [mul_assoc, ← mul_assoc w, ← commute_subprods hyc w hw, mul_assoc, ih hl w hw,
        mul_one, hy]

theorem nodup_subprods {l : List P} (h : IndepList l) : (subprods l).Nodup := by
  induction h with
  | nil => simp [subprods]
  | cons x l hx _ hc hnot hl ih =>
    have hci := isCommInvol_of_indepList hl
    rw [subprods, List.nodup_append]
    refine ⟨ih, ih.map (mul_right_injective x), ?_⟩
    intro a ha b hb hab
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
    apply hnot
    have : x = a * w := by
      rw [hab, mul_assoc, sq_eq_one_of_mem_subprods hci w hw, mul_one]
    rw [this]
    exact mul_mem_subprods hci a ha w hw

end Subprods

section Greedy

variable [DecidableEq P]

@[expose] def pos (Rinv : List P) (x : P) : ℕ := Rinv.idxOf x

@[expose] def startPos (Rinv : List P) : List P → ℕ
  | [] => 0
  | a :: _ => pos Rinv a + 1

@[expose] def greedyExt (Rinv : List P) (l : List P) : List P :=
  (Rinv.drop (startPos Rinv l)).filter fun x =>
    (l.all fun y => decide (x * y = y * x)) && !(decide (x ∈ subprods l)) &&
      ((subprods l).all fun s => decide (s = 1) || decide (pos Rinv x < pos Rinv (x * s)))

@[expose] def forallGreedy (Rinv : List P) (pred : List P → Bool) : ℕ → List P → Bool
  | 0, l => pred l
  | k + 1, l => (greedyExt Rinv l).all fun x => forallGreedy Rinv pred k (x :: l)

@[expose] def greedyExtP (posF : P → ℕ) (Rinv : List P) (l : List P) : List P :=
  let S := subprods l
  let st := match l with
    | [] => 0
    | a :: _ => posF a + 1
  (Rinv.drop st).filter fun x =>
    (l.all fun y => decide (x * y = y * x)) && !(decide (x ∈ S)) &&
      (S.all fun s => decide (s = 1) || decide (posF x < posF (x * s)))

@[expose] def forallGreedyP (posF : P → ℕ) (Rinv : List P) (pred : List P → Bool) :
    ℕ → List P → Bool
  | 0, l => pred l
  | k + 1, l => (greedyExtP posF Rinv l).all fun x => forallGreedyP posF Rinv pred k (x :: l)

theorem greedyExtP_eq {posF : P → ℕ} {Rinv : List P} (h : ∀ x, posF x = pos Rinv x)
    (l : List P) : greedyExtP posF Rinv l = greedyExt Rinv l := by
  have hf : posF = pos Rinv := funext h
  subst hf
  cases l <;> rfl

theorem forallGreedyP_eq {posF : P → ℕ} {Rinv : List P} (h : ∀ x, posF x = pos Rinv x)
    (pred : List P → Bool) : ∀ (k : ℕ) (l : List P),
    forallGreedyP posF Rinv pred k l = forallGreedy Rinv pred k l
  | 0, l => rfl
  | k + 1, l => by
    rw [forallGreedyP, forallGreedy, greedyExtP_eq h]
    congr 1
    funext x
    exact forallGreedyP_eq h pred k (x :: l)

inductive GreedyOver (Rinv : List P) (l : List P) : List P → Prop
  | refl : GreedyOver Rinv l l
  | step {l' : List P} {x : P} : GreedyOver Rinv l l' → x ∈ greedyExt Rinv l' →
      GreedyOver Rinv l (x :: l')

theorem GreedyOver.length_ge {Rinv l l' : List P} (h : GreedyOver Rinv l l') :
    l.length ≤ l'.length := by
  induction h with
  | refl => exact le_rfl
  | step _ _ ih => simp only [List.length_cons]; omega

theorem forallGreedy_chain (Rinv : List P) (pred : List P → Bool) :
    ∀ (k : ℕ) (l : List P), forallGreedy Rinv pred k l = true →
      ∀ l' : List P, l'.length = l.length + k → GreedyOver Rinv l l' → pred l' = true := by
  intro k
  induction k with
  | zero =>
    intro l h l' hlen hg
    cases hg with
    | refl => simpa [forallGreedy] using h
    | step hg' _ =>
      have := hg'.length_ge
      simp only [List.length_cons] at hlen
      omega
  | succ k ih =>
    intro l h l' hlen hg
    have key : ∀ m (l' : List P), GreedyOver Rinv l l' → l'.length = l.length + (m + 1) →
        ∃ x ∈ greedyExt Rinv l, GreedyOver Rinv (x :: l) l' := by
      intro m l' hg hlen
      induction hg generalizing m with
      | refl => omega
      | @step l'' x hg'' hx ih' =>
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · have h1 : l''.length = l.length := by
            simp only [List.length_cons] at hlen
            omega
          have : l'' = l := by
            cases hg'' with
            | refl => rfl
            | step hg3 _ =>
              have := hg3.length_ge
              simp only [List.length_cons] at h1
              omega
          subst this
          exact ⟨x, hx, GreedyOver.refl⟩
        · obtain ⟨y, hy, hgy⟩ := ih' (m - 1) (by simp only [List.length_cons] at hlen; omega)
          exact ⟨y, hy, GreedyOver.step hgy hx⟩
    obtain ⟨x, hx, hgx⟩ := key k l' hg hlen
    have hall : forallGreedy Rinv pred k (x :: l) = true := by
      simp only [forallGreedy, List.all_eq_true] at h
      exact h x hx
    exact ih (x :: l) hall l' (by simp only [List.length_cons]; omega) hgx

variable {Rinv : List P}

inductive IsBGreedy (Rinv : List P) (B : Subgroup P) : List P → Prop
  | nil : IsBGreedy Rinv B []
  | cons {x : P} {l : List P} : IsBGreedy Rinv B l → x ∈ B → x ∉ subprods l →
      (∀ y ∈ B, y ∉ subprods l → pos Rinv x ≤ pos Rinv y) → IsBGreedy Rinv B (x :: l)

theorem IsBGreedy.mem {B : Subgroup P} {l : List P} (h : IsBGreedy Rinv B l) :
    ∀ y ∈ l, y ∈ B := by
  induction h with
  | nil => simp
  | cons _ hx _ _ ih =>
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact ih y hy

theorem IsBGreedy.indep {B : Subgroup P} (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) {l : List P} (h : IsBGreedy Rinv B l) : IndepList l := by
  induction h with
  | nil => exact IndepList.nil
  | @cons x l hl hx hnot _ ih =>
    refine IndepList.cons x l (hsq x hx) ?_ (fun y hy => hcomm x hx y (hl.mem y hy)) hnot ih
    rintro rfl
    exact hnot (one_mem_subprods l)

omit [Group P] in
theorem pos_lt_of_mem_drop' {x : P} (m : ℕ) (hx : x ∈ Rinv) (hm : m ≤ pos Rinv x) :
    x ∈ Rinv.drop m := by
  have hlt : Rinv.idxOf x < Rinv.length := List.idxOf_lt_length_iff.2 hx
  rw [List.mem_iff_getElem]
  refine ⟨Rinv.idxOf x - m, by simp only [List.length_drop]; unfold pos at hm; omega, ?_⟩
  rw [List.getElem_drop]
  have : m + (Rinv.idxOf x - m) = Rinv.idxOf x := by unfold pos at hm; omega
  simp only [this, List.getElem_idxOf]

omit [Group P] in
theorem pos_injOn {x y : P} (hx : x ∈ Rinv) (hy : y ∈ Rinv)
    (h : pos Rinv x = pos Rinv y) : x = y := by
  unfold pos at h
  have hx' := List.getElem_idxOf (List.idxOf_lt_length_iff.2 hx)
  have hy' := List.getElem_idxOf (List.idxOf_lt_length_iff.2 hy)
  rw [← hx', ← hy']
  simp only [h]

theorem IsBGreedy.mem_greedyExt {B : Subgroup P}
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hR : ∀ x ∈ B, x ≠ 1 → x ∈ Rinv) {x : P} {l : List P}
    (h : IsBGreedy Rinv B (x :: l)) : x ∈ greedyExt Rinv l := by
  obtain _ | ⟨hl, hx, hnot, hmin⟩ := h
  have hindep := hl.indep hcomm hsq
  have hci := isCommInvol_of_indepList hindep
  have hx1 : x ≠ 1 := fun e => hnot (e ▸ one_mem_subprods l)
  have hxR := hR x hx hx1
  rw [greedyExt, List.mem_filter]
  refine ⟨?_, ?_⟩
  ·
    refine pos_lt_of_mem_drop' _ hxR ?_
    cases hl with
    | nil => exact Nat.zero_le _
    | @cons a l₀ hl₀ ha hanot hamin =>
      show pos Rinv a + 1 ≤ pos Rinv x
      have hx₀ : x ∉ subprods l₀ := fun h' => hnot (by
        rw [mem_subprods_cons]; exact Or.inl h')
      have h1 := hamin x hx hx₀
      have hne : x ≠ a := fun e => hnot (e ▸ mem_subprods_of_mem List.mem_cons_self)
      have h2 : pos Rinv x ≠ pos Rinv a := fun e =>
        hne (pos_injOn hxR (hR a ha (fun e1 => hanot (e1 ▸ one_mem_subprods l₀))) e)
      omega
  · simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not, Bool.or_eq_true]
    refine ⟨⟨fun y hy => hcomm x hx y (hl.mem y hy), hnot⟩, fun s hs => ?_⟩
    by_cases hs1 : s = 1
    · exact Or.inl hs1
    · right
      have hsB : s ∈ B := subprods_subset hl.mem s hs
      have hxs : x * s ∈ B := B.mul_mem hx hsB
      have hxs_not : x * s ∉ subprods l := by
        intro h'
        apply hnot
        have : x = (x * s) * s := by
          rw [mul_assoc, sq_eq_one_of_mem_subprods hci s hs, mul_one]
        rw [this]
        exact mul_mem_subprods hci _ h' s hs
      have h1 := hmin (x * s) hxs hxs_not
      have hxs1 : x * s ≠ 1 := fun e => hxs_not (e ▸ one_mem_subprods l)
      have hne : x ≠ x * s := fun e => hs1 (by
        have := congrArg (x⁻¹ * ·) e
        simpa using this.symm)
      have h2 : pos Rinv x ≠ pos Rinv (x * s) := fun e =>
        hne (pos_injOn hxR (hR _ hxs hxs1) e)
      omega

theorem IsBGreedy.greedyOver {B : Subgroup P}
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hR : ∀ x ∈ B, x ≠ 1 → x ∈ Rinv) {l : List P} (h : IsBGreedy Rinv B l) :
    GreedyOver Rinv [] l := by
  induction h with
  | nil => exact GreedyOver.refl
  | @cons x l hl hx hnot hmin ih =>
    exact GreedyOver.step ih ((IsBGreedy.cons hl hx hnot hmin).mem_greedyExt hcomm hsq hR)

theorem exists_isBGreedy {B : Subgroup P} [Finite B] {k : ℕ} (hcard : Nat.card B = 2 ^ k) :
    ∀ m ≤ k, ∃ l : List P, l.length = m ∧ IsBGreedy Rinv B l := by
  intro m
  induction m with
  | zero => intro _; exact ⟨[], rfl, IsBGreedy.nil⟩
  | succ m ih =>
    intro hm
    obtain ⟨l, hlen, hl⟩ := ih (by omega)
    classical
    have hex : ∃ y ∈ B, y ∉ subprods l := by
      by_contra hno
      push Not at hno
      have hle : (B : Set P) ⊆ ((subprods l).toFinset : Set P) := fun x hx => by
        simpa using hno x hx
      have h1 : Nat.card B ≤ (subprods l).toFinset.card := by
        calc Nat.card B = (B : Set P).ncard := Nat.card_coe_set_eq _
          _ ≤ ((subprods l).toFinset : Set P).ncard := Set.ncard_le_ncard hle
          _ = (subprods l).toFinset.card := Set.ncard_coe_finset _
      have h2 : (subprods l).toFinset.card ≤ 2 ^ m := by
        calc (subprods l).toFinset.card ≤ (subprods l).length := List.toFinset_card_le _
          _ = 2 ^ l.length := length_subprods l
          _ = 2 ^ m := by rw [hlen]
      have h3 : 2 ^ m < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hfin : (({y | y ∈ B ∧ y ∉ subprods l} : Set P).image (pos Rinv)).Nonempty := by
      obtain ⟨y, hy, hyn⟩ := hex
      exact ⟨pos Rinv y, y, ⟨hy, hyn⟩, rfl⟩
    obtain ⟨y, ⟨hyB, hyn⟩, hymin⟩ := Nat.sInf_mem hfin
    refine ⟨y :: l, by simp [hlen], IsBGreedy.cons hl hyB hyn fun z hz hzn => ?_⟩
    rw [hymin]
    exact Nat.sInf_le ⟨z, ⟨hz, hzn⟩, rfl⟩

theorem forallGreedy_sound {pred : List P → Bool} {k : ℕ}
    (h : forallGreedy Rinv pred k [] = true) (B : Subgroup P) [Finite B]
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hR : ∀ x ∈ B, x ≠ 1 → x ∈ Rinv) (hcard : Nat.card B = 2 ^ k) :
    ∃ l : List P, l.length = k ∧ IndepList l ∧ (∀ x, x ∈ B ↔ x ∈ subprods l) ∧
      pred l = true := by
  classical
  obtain ⟨l, hlen, hl⟩ := exists_isBGreedy (Rinv := Rinv) hcard k le_rfl
  have hindep := hl.indep hcomm hsq
  refine ⟨l, hlen, hindep, fun x => ⟨fun hx => ?_, fun hx => subprods_subset hl.mem x hx⟩,
    forallGreedy_chain Rinv pred k [] h l (by simp [hlen]) (hl.greedyOver hcomm hsq hR)⟩
  by_contra hxn
  have hsub : ((subprods l).toFinset : Set P) ⊆ (B : Set P) := fun y hy => by
    simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hy
    exact subprods_subset hl.mem y hy
  have hss : ((subprods l).toFinset : Set P) ⊂ (B : Set P) :=
    Set.ssubset_iff_subset_ne.2 ⟨hsub, fun e => hxn (by
      have : x ∈ ((subprods l).toFinset : Set P) := e ▸ hx
      simpa using this)⟩
  have h1 := Set.ncard_lt_ncard hss (Set.toFinite _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup (nodup_subprods hindep),
    length_subprods, hlen, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard] at h1
  exact lt_irrefl _ h1

end Greedy

end CFSG.Quasithin.H.Mathieu
