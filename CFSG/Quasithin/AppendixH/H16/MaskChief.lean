module

public import CFSG.Milestones.ASVolI.H1
public import CFSG.Quasithin.Background.HCocBase
public import CFSG.Quasithin.Background.HFixSylBase

public section

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc

@[expose] def redStep (v p : ℕ) : ℕ := min v (v ^^^ p)

@[expose] def reduceBy (bs : List ℕ) (v : ℕ) : ℕ := bs.foldl redStep v

@[expose] def echelon (l : List ℕ) : List ℕ :=
  l.foldl (fun bs v => if reduceBy bs v = 0 then bs else bs ++ [reduceBy bs v]) []

private theorem redStep_eq (v p : ℕ) :
    redStep v p = v ^^^ (if v ≤ v ^^^ p then 0 else p) := by
  rw [redStep]
  by_cases h : v ≤ v ^^^ p
  · rw [if_pos h, Nat.xor_zero, min_eq_left h]
  · rw [if_neg h, min_eq_right (le_of_lt (not_le.mp h))]

private theorem exists_reduceBy_xor : ∀ (bs : List ℕ) (v : ℕ),
    ∃ c ∈ combos bs, reduceBy bs v = v ^^^ c := by
  intro bs
  induction bs with
  | nil =>
    intro v
    exact ⟨0, by simp [combos], by simp [reduceBy]⟩
  | cons b bs ih =>
    intro v
    obtain ⟨c, hc, hcv⟩ := ih (redStep v b)
    refine ⟨(if v ≤ v ^^^ b then 0 else b) ^^^ c, ?_, ?_⟩
    · refine xor_mem_combos (b :: bs) ?_ ?_
      · by_cases h : v ≤ v ^^^ b
        · rw [if_pos h]
          exact zero_mem_combos (b :: bs)
        · rw [if_neg h]
          exact mem_combos_of_mem List.mem_cons_self
      · rw [combos]
        exact List.mem_append_left _ hc
    · unfold reduceBy
      rw [List.foldl_cons]
      rw [show List.foldl redStep (redStep v b) bs = redStep v b ^^^ c from hcv]
      rw [redStep_eq, Nat.xor_assoc]

private theorem mem_combos_of_subset {L bs : List ℕ} (h : ∀ b ∈ bs, b ∈ combos L) :
    ∀ c ∈ combos bs, c ∈ combos L :=
  mem_of_combos (fun x => x ∈ combos L) (zero_mem_combos L)
    (fun a b ha hb => xor_mem_combos L ha hb) bs h

private theorem mem_combos_reduceBy_iff {L bs : List ℕ} (h : ∀ b ∈ bs, b ∈ combos L) (v : ℕ) :
    reduceBy bs v ∈ combos L ↔ v ∈ combos L := by
  constructor
  · intro hred
    obtain ⟨c, hc, he⟩ := exists_reduceBy_xor bs v
    have hcL := mem_combos_of_subset h c hc
    have hred' : v ^^^ c ∈ combos L := he ▸ hred
    have h2 : (v ^^^ c) ^^^ c ∈ combos L := xor_mem_combos L hred' hcL
    rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at h2
  · intro hv
    obtain ⟨c, hc, he⟩ := exists_reduceBy_xor bs v
    rw [he]
    exact xor_mem_combos L hv (mem_combos_of_subset h c hc)

private theorem combos_append_left (l₁ l₂ : List ℕ) :
    ∀ x ∈ combos l₁, x ∈ combos (l₁ ++ l₂) := by
  induction l₁ with
  | nil =>
    intro x hx
    simp only [combos, List.mem_singleton] at hx
    rw [hx]
    simpa using zero_mem_combos l₂
  | cons a l₁ ih =>
    intro x hx
    rw [combos, List.mem_append, List.mem_map] at hx
    rw [List.cons_append, combos, List.mem_append, List.mem_map]
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Or.inl (ih x hx)
    · exact Or.inr ⟨y, ih y hy, rfl⟩

private def echStep (bs : List ℕ) (v : ℕ) : List ℕ :=
  if reduceBy bs v = 0 then bs else bs ++ [reduceBy bs v]

private theorem echelon_eq (l : List ℕ) : echelon l = l.foldl echStep [] := rfl

private theorem echelon_fold_subset :
    ∀ (r : List ℕ) (p bs0 : List ℕ), (∀ b ∈ bs0, b ∈ combos p) →
      ∀ b ∈ r.foldl echStep bs0, b ∈ combos (p ++ r) := by
  intro r
  induction r with
  | nil =>
    intro p bs0 hbs0 b hb
    simpa using hbs0 b hb
  | cons v r ih =>
    intro p bs0 hbs0
    have hv : v ∈ combos (p ++ [v]) :=
      mem_combos_of_mem (List.mem_append_right _ (List.mem_singleton_self v))
    have hbs0' : ∀ b ∈ bs0, b ∈ combos (p ++ [v]) := fun b hb =>
      combos_append_left p [v] b (hbs0 b hb)
    have hred : reduceBy bs0 v ∈ combos (p ++ [v]) :=
      (mem_combos_reduceBy_iff hbs0' v).2 hv
    have hbs1 : ∀ b ∈ echStep bs0 v, b ∈ combos (p ++ [v]) := by
      intro b hb
      by_cases h : reduceBy bs0 v = 0
      · rw [echStep, if_pos h] at hb
        exact hbs0' b hb
      · rw [echStep, if_neg h] at hb
        rcases List.mem_append.1 hb with hb | hb
        · exact hbs0' b hb
        · rw [List.mem_singleton] at hb
          rw [hb]
          exact hred
    have ih' := ih (p ++ [v]) (echStep bs0 v) hbs1
    rw [List.foldl_cons]
    intro b hb
    simpa [List.append_assoc] using ih' b hb

theorem mem_combos_of_reduceBy_echelon (l : List ℕ) (v : ℕ)
    (h : reduceBy (echelon l) v = 0) : v ∈ combos l := by
  have hsub : ∀ b ∈ echelon l, b ∈ combos l := by
    have h := echelon_fold_subset l [] [] (by intro b hb; simp at hb)
    simpa [echelon_eq, List.nil_append] using h
  exact (mem_combos_reduceBy_iff hsub v).1 (by rw [h]; exact zero_mem_combos l)

@[expose] def chiefCheck (cs : List (List ℕ)) (bx by_ : List ℕ) (words : List (List ℕ)) : Bool :=
  (combos by_).all fun m =>
    reduceBy (echelon bx) m == 0 ||
      by_.all fun b => reduceBy (echelon (bx ++ words.map fun u => wAct cs u m)) b == 0

theorem isChiefFactorUnder_maskSub {n : ℕ} {G : Subgroup (MulAut (Wn n))}
    (gs : List (MulAut (Wn n))) (cs : List (List ℕ))
    (hgs : ∀ i < gs.length, gs.getD i 1 ∈ G)
    (hact : ∀ i < gs.length, ActsBy (gs.getD i 1) (cs.getD i []))
    (bx by_ : List ℕ) (words : List (List ℕ)) (hw : ∀ u ∈ words, ∀ i ∈ u, i < gs.length)
    (hcheck : chiefCheck cs bx by_ words = true)
    (hlt : maskSub n bx < maskSub n by_)
    (hXinv : IsActsInv (actsOnModule G) (maskSub n bx))
    (hYinv : IsActsInv (actsOnModule G) (maskSub n by_)) :
    IsChiefFactorUnder (actsOnModule G) (maskSub n bx) (maskSub n by_) := by
  classical
  refine ⟨hlt, hXinv, hYinv, ?_⟩
  intro W hXW hWY hWi
  by_cases hWX : W = maskSub n bx
  · exact Or.inl hWX
  · right
    have hnot : ¬ W ≤ maskSub n bx := fun h => hWX (le_antisymm h hXW)
    have hex : ∃ w, w ∈ W ∧ w ∉ maskSub n bx := by
      by_contra h
      apply hnot
      intro w hw
      by_contra hwX
      exact h ⟨w, hw, hwX⟩
    obtain ⟨w, hwW, hwX⟩ := hex
    have hwY : w ∈ maskSub n by_ := hWY hwW
    rw [mem_maskSub] at hwY
    obtain ⟨m, hm, hmeq⟩ := hwY
    have hchk := List.all_eq_true.1 hcheck m hm
    rw [Bool.or_eq_true] at hchk
    have hbL : ∀ b ∈ by_, b ∈ combos (bx ++ words.map (fun u => wAct cs u m)) := by
      rcases hchk with h1 | h2
      · rw [beq_iff_eq] at h1
        have hmx : m ∈ combos bx := mem_combos_of_reduceBy_echelon bx m h1
        exact absurd (hmeq ▸ toW_mem_maskSub hmx) hwX
      · rw [List.all_eq_true] at h2
        intro b hb
        exact mem_combos_of_reduceBy_echelon _ b ((beq_iff_eq).1 (h2 b hb))
    have hLW : ∀ c ∈ bx ++ words.map (fun u => wAct cs u m), toW n c ∈ W := by
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact hXW (toW_mem_maskSub (mem_combos_of_mem hc))
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hc
        rw [← wProd_toW hact u (hw u hu) m]
        exact hWi (fun v => wProd gs u v) ⟨wProd gs u, wProd_mem hgs u, rfl⟩ (toW n m)
          (hmeq.symm ▸ hwW)
    have hbyW : ∀ b ∈ by_, toW n b ∈ W := fun b hb =>
      mem_of_combos (fun x => toW n x ∈ W) (by rw [toW_zero]; exact W.one_mem)
        (fun a b ha hb => by rw [toW_xor]; exact W.mul_mem ha hb)
        (bx ++ words.map (fun u => wAct cs u m)) hLW b (hbL b hb)
    refine le_antisymm hWY ?_
    intro y hy
    rw [mem_maskSub] at hy
    obtain ⟨m', hm', rfl⟩ := hy
    exact mem_of_combos (fun x => toW n x ∈ W) (by rw [toW_zero]; exact W.one_mem)
      (fun a b ha hb => by rw [toW_xor]; exact W.mul_mem ha hb) by_ hbyW m' hm'

end CFSG.ASVolI.H16
