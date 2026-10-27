module

public import CFSG.Perm.ChainSpec
public import Certificates.Data.CFSGNative.J1.Prim

public section

namespace CFSG.Sporadic.J1

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native Native

theorem isPreprimitive_of_closure {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) (H : Subgroup G) (hH : ∀ h ∈ H, h • x = x)
    (lab : X → ℕ) (horb : ∀ p q : X, lab p = lab q → ∃ h ∈ H, h • p = q)
    (t : ℕ → G) (ht : ∀ p : X, lab (t (lab p) • x) = lab p)
    (hcl : ∀ y : X, lab y ≠ lab x → ∀ L : Set ℕ, lab x ∈ L → lab y ∈ L →
      (∀ p w : X, lab p ∈ L → lab w ∈ L → lab (t (lab p) • w) ∈ L) → ∀ p : X, lab p ∈ L) :
    MulAction.IsPreprimitive G X := by
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base x fun {B} hxB hB => ?_
  have hclass : ∀ p q : X, p ∈ B → lab p = lab q → q ∈ B := by
    intro p q hp hpq
    obtain ⟨h, hh, rfl⟩ := horb p q hpq
    have hhx : h • x ∈ B := by rw [hH h hh]; exact hxB
    rw [← hB.smul_eq_of_mem hxB hhx]
    exact Set.smul_mem_smul_set hp
  by_cases hsub : ∀ y ∈ B, y = x
  · left
    intro p hp q hq
    rw [hsub p hp, hsub q hq]
  · right
    push Not at hsub
    obtain ⟨y, hyB, hyx⟩ := hsub
    have hlab : lab y ≠ lab x := by
      intro he
      obtain ⟨h, hh, hhy⟩ := horb x y he.symm
      exact hyx (by rw [← hhy, hH h hh])
    have hall := hcl y hlab {l | ∀ p : X, lab p = l → p ∈ B} (fun p hp => hclass x p hxB hp.symm)
      (fun p hp => hclass y p hyB hp.symm) (by
        intro p w hp hw q hq
        have htx : t (lab p) • x ∈ B := hp _ (ht p)
        have hwB : w ∈ B := hw w rfl
        have hg : t (lab p) • w ∈ B := by
          rw [← hB.smul_eq_of_mem hxB htx]
          exact Set.smul_mem_smul_set hwB
        exact hclass _ q hg hq.symm)
    exact Set.eq_univ_of_forall fun p => hall p p rfl

theorem getElem!_set!_true {D : Array Bool} {m l : ℕ} (h : (D.set! m true)[l]! = true) :
    l = m ∨ D[l]! = true := by
  by_cases hl : l < D.size
  · have hl' : l < (D.set! m true).size := by simpa using hl
    rw [getElem!_pos _ l hl'] at h
    simp only [Array.set!_eq_setIfInBounds] at h
    rw [Array.getElem_setIfInBounds hl] at h
    split_ifs at h with hml
    · exact Or.inl hml.symm
    · right
      rw [getElem!_pos _ l hl]
      exact h
  · have hl' : ¬l < (D.set! m true).size := by simpa using hl
    rw [getElem!_neg _ l hl'] at h
    exact absurd h (by decide)

theorem replicate_getElem!_false {k l : ℕ} : (Array.replicate k false)[l]! = false := by
  by_cases hl : l < (Array.replicate k false).size
  · rw [getElem!_pos _ l hl, Array.getElem_replicate]
  · rw [getElem!_neg _ l hl]
    rfl

theorem derRun_sound {n k l0 i : ℕ} {lab : Array ℕ} {imgs : Array (Array ℕ)} (L : Set ℕ)
    (h0 : l0 ∈ L) (hi : i ∈ L)
    (hstep : ∀ j w, j < k → w < n → j ∈ L → lab[w]! ∈ L → lab[(imgs[j]!)[w]!]! ∈ L)
    (steps : List (ℕ × ℕ)) : ∀ l, (derRun n k l0 i lab imgs steps)[l]! = true → l ∈ L := by
  have key : ∀ (ss : List (ℕ × ℕ)) (D : Array Bool), (∀ l, D[l]! = true → l ∈ L) →
      ∀ l, (ss.foldl (derStep n k lab imgs) D)[l]! = true → l ∈ L := by
    intro ss
    induction ss with
    | nil => intro D hD; exact hD
    | cons s ss ih =>
      intro D hD
      apply ih
      intro l hl
      unfold derStep at hl
      split_ifs at hl with hc
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨hj, hw⟩, hDj⟩, hDw⟩ := hc
        rcases getElem!_set!_true hl with rfl | hl'
        · exact hstep _ _ hj hw (hD _ hDj) (hD _ hDw)
        · exact hD l hl'
      · exact hD l hl
  apply key
  intro l hl
  rcases getElem!_set!_true hl with rfl | hl'
  · exact hi
  rcases getElem!_set!_true hl' with rfl | hl''
  · exact h0
  · rw [replicate_getElem!_false] at hl''
    exact absurd hl'' (by decide)

section Cert

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem inTree_iff_exists {T : Tree} {p : ℕ} :
    inTree T p = true ↔ ap T.pos p < T.pts.size ∧ ap T.pts (ap T.pos p) = p := by
  simp [inTree]

theorem mem_orbit_of_inTree {T : Tree} {lv : Array ℕ} {lG : ℕ → G} {r : ℕ}
    (hT : TreeFacts n T lv lG r) {p : Fin n} (hp : inTree T p.val = true) :
    p ∈ MulAction.orbit (lettersGroup lv lG) (⟨r, hT.r_lt⟩ : Fin n) := by
  rw [hT.mem_orbit_iff]
  rw [inTree_iff_exists] at hp
  exact ⟨_, hp.1, hp.2⟩

theorem isPreprimitive_of_primOK [MulAction.IsPretransitive G (Fin n)] {letters : Array Table}
    {lG : ℕ → G} {lv lv0 : Array ℕ} {T0 : Tree} (hT0 : TreeFacts n T0 lv0 lG 0)
    (hW : WalkFacts n T0 letters lG) (hrep : ∀ l ∈ lv, Rep n letters[l]! (lG l))
    (hfix : ∀ g ∈ lettersGroup lv lG, idx n g 0 = 0) {D : PrimData}
    (h : primOK n letters lv T0 D = true) : MulAction.IsPreprimitive G (Fin n) := by
  unfold primOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hlab, hsubs⟩, himgs⟩, hders⟩, hn⟩, hper⟩, hpts⟩ := h
  set k := D.reps.size with hk
  have hper' : ∀ l < k, D.reps[l]! < n ∧ D.lab[D.reps[l]!]! = l ∧ inTree T0 D.reps[l]! = true ∧
      CFSG.Perm.Native.treeOK n D.reps[l]! D.subs[l]! letters lv = true ∧
      D.imgs[l]! = treeImg n T0 letters D.reps[l]! ∧
      (l = D.lab[0]! ∨ derOK n k D.lab[0]! l D.lab D.imgs D.ders[l]! = true) := by
    intro l hl
    have := (allIn_eq_true.1 hper) l (Nat.zero_le _) hl
    simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true, and_assoc]
      using this
  have hpts' : ∀ p < n, D.lab[p]! < k ∧ inTree D.subs[D.lab[p]!]! p = true := by
    intro p hp
    have := (allIn_eq_true.1 hpts) p (Nat.zero_le _) hp
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  have hsubF : ∀ l < k, TreeFacts n D.subs[l]! lv lG D.reps[l]! := fun l hl =>
    treeOK_facts hrep (hper' l hl).2.2.2.1
  let x : Fin n := ⟨0, hn⟩
  let H := lettersGroup lv lG
  have hH : ∀ h ∈ H, h • x = x := by
    intro h hh
    apply Fin.ext
    rw [smul_val_eq_idx]
    exact hfix h hh
  let lab : Fin n → ℕ := fun p => D.lab[p.val]!
  have horb : ∀ p q : Fin n, lab p = lab q → ∃ h ∈ H, h • p = q := by
    intro p q hpq
    have hp := hpts' p.val p.isLt
    have hq := hpts' q.val q.isLt
    have hq' : inTree D.subs[D.lab[p.val]!]! q.val = true := by
      have : D.lab[p.val]! = D.lab[q.val]! := hpq
      rw [this]; exact hq.2
    have hT := hsubF _ hp.1
    set r : Fin n := ⟨D.reps[D.lab[p.val]!]!, hT.r_lt⟩ with hr
    obtain ⟨⟨u, hu⟩, hup⟩ := mem_orbit_of_inTree hT hp.2
    obtain ⟨⟨v, hv⟩, hvq⟩ := mem_orbit_of_inTree hT hq'
    have e1 : u • r = p := hup
    have e2 : v • r = q := hvq
    refine ⟨v * u⁻¹, H.mul_mem hv (H.inv_mem hu), ?_⟩
    rw [← e1, ← e2, mul_smul, inv_smul_smul]
  let t : ℕ → G := fun j => treeG T0 lG (ap T0.pos D.reps[j]!)
  have hpos : ∀ j < k, ap T0.pos D.reps[j]! < T0.pts.size ∧
      ap T0.pts (ap T0.pos D.reps[j]!) = D.reps[j]! := fun j hj =>
    inTree_iff_exists.1 (hper' j hj).2.2.1
  have htx : ∀ j < k, (t j • x).val = D.reps[j]! := by
    intro j hj
    rw [smul_val_eq_idx, hT0.elt _ (hpos j hj).1, (hpos j hj).2]
  have ht : ∀ p : Fin n, lab (t (lab p) • x) = lab p := by
    intro p
    have hj := (hpts' p.val p.isLt).1
    show D.lab[(t (lab p) • x).val]! = lab p
    rw [htx _ hj]
    exact (hper' _ hj).2.1
  have himg : ∀ j < k, ∀ w : Fin n, (t j • w).val = (D.imgs[j]!)[w.val]! := by
    intro j hj w
    rw [(hper' j hj).2.2.2.2.1, treeImg]
    have hq : ∀ i < (Array.range n).size, (Array.range n)[i]! < n := by
      intro i hi
      rw [Array.size_range] at hi
      rw [getElem!_pos _ i (by simpa using hi), Array.getElem_range]
      exact hi
    obtain ⟨-, he⟩ := walk_spec hW (hpos j hj).1 (Array.range n) hq
    rw [he w.val (by simp), getElem!_pos _ w.val (by simp), Array.getElem_range, smul_val_eq_idx]
  refine isPreprimitive_of_closure x H hH lab horb t ht ?_
  intro y hy L hx hyL hclL p
  have hyk := (hpts' y.val y.isLt).1
  have hd := (hper' _ hyk).2.2.2.2.2.resolve_left (fun he => hy he)
  unfold derOK at hd
  simp only [Bool.and_eq_true, beq_iff_eq] at hd
  have hsound := derRun_sound (n := n) (k := k) (imgs := D.imgs) L hx hyL (by
    intro j w hj hw hjL hwL
    have hrj : D.reps[j]! < n := (hper' j hj).1
    have hp := hclL ⟨D.reps[j]!, hrj⟩ ⟨w, hw⟩ (by
      show D.lab[D.reps[j]!]! ∈ L
      rw [(hper' j hj).2.1]; exact hjL) hwL
    have e : lab ⟨D.reps[j]!, hrj⟩ = j := (hper' j hj).2.1
    rw [e] at hp
    show D.lab[(D.imgs[j]!)[w]!]! ∈ L
    rw [← himg j hj ⟨w, hw⟩]
    exact hp) D.ders[lab y]!
  exact hsound _ ((allIn_eq_true.1 hd.2) (lab p) (Nat.zero_le _) (hpts' p.val p.isLt).1)

end Cert

end CFSG.Sporadic.J1
