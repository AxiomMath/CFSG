module

public import CFSG.Monster.B.TwoA.Sp8.P0RankLin
public import CFSG.Monster.B.TwoA.Sp8.P0RankWalk
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Finset.Prod

public section

namespace CFSG.Monster.B.TwoA.Sp8.P0Rank

open MonsterB.P0Rank

private lemma count_map_true (f : ℕ → Bool) (n : ℕ) :
    (List.map f (List.range n)).count true = (List.filter f (List.range n)).length := by
  rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  congr 1

private lemma card_le_length_of_mem_iff {S : Finset ℕ} {l : List ℕ}
    (h : ∀ x, x ∈ l ↔ x ∈ S) : S.card ≤ l.length := by
  have hts : l.toFinset = S := Finset.ext (fun x => by rw [List.mem_toFinset, h x])
  calc S.card = l.toFinset.card := by rw [hts]
    _ ≤ l.length := List.toFinset_card_le l

private lemma lt_pow_log2_succ (v : ℕ) : v < 2 ^ (Nat.log2 v + 1) := by
  rw [Nat.log2_eq_log_two]
  simpa using Nat.lt_pow_succ_log_self (b := 2) (by decide) v

private lemma lamList_length : lamList.length = 16 := by
  simp [lamList]

private lemma emb_zero : emb 0 = 0 := by
  simpa [emb] using colsAct_zero embCols

private lemma emb_xor (z z' : ℕ) : emb (z ^^^ z') = emb z ^^^ emb z' := by
  simpa [emb] using colsAct_xor embCols z z'

private lemma emb_lt (z : ℕ) : emb z < 2 ^ 9 :=
  colsAct_lt (cs := embCols) (w := 9) (by decide) z

private lemma aMat_getElem! (dat : Data) {κ : ℕ} (hκ : κ < 1024) :
    (aMat dat)[κ]! = colsOf 16 (actK dat.aCols κ) := by
  rw [aMat, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hκ]
  rfl

private lemma bRows_getElem! (dat : Data) {v : ℕ} (hv : v < 65536) :
    (bRows dat)[v]! = if qN dat.beta v = 0 then colsOf 16 (betaN dat.beta v) else [] := by
  rw [bRows, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hv]
  rfl

private lemma colsAct_aMat (dat : Data) {κ v : ℕ} (hκ : κ < 2 ^ 10) (hv : v < 2 ^ 16) :
    colsAct (aMat dat)[κ]! v = actK dat.aCols κ v := by
  rw [aMat_getElem! dat (by simpa using hκ)]
  exact colsAct_colsOf (actK_xor dat.aCols κ) hv

private lemma yTab_snd_fst_getElem! (dat : Data) (e : List ℕ) {κ : ℕ} (hκ : κ < 1024) :
    ((e, ((List.range 1024).map (inCU dat e)).toArray,
        ((List.range 1024).map (inCU dat e)).count true) :
        List ℕ × Array Bool × Nat).2.1[κ]! = inCU dat e κ := by
  rw [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hκ]
  rfl

private noncomputable def fixedC (dat : Data) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range 32).filter fun z => ∀ κ ∈ W, actK dat.uConjT κ (emb z) = emb z

private lemma fixedC_xorClosed (dat : Data) (W : Finset ℕ) : XorClosed (fixedC dat W) := by
  constructor
  · simp [fixedC, emb_zero, actK_zero]
  · intro z hz z' hz'
    simp only [fixedC, Finset.mem_filter, Finset.mem_range] at hz hz' ⊢
    obtain ⟨hz32, hzfix⟩ := hz
    obtain ⟨hz'32, hz'fix⟩ := hz'
    refine ⟨?_, ?_⟩
    · have h1 : z < 2 ^ 5 := by omega
      have h2 : z' < 2 ^ 5 := by omega
      have h3 := Nat.xor_lt_two_pow h1 h2
      omega
    · intro κ hκ
      rw [emb_xor, actK_xor, hzfix κ hκ, hz'fix κ hκ]

private lemma inCU_of_mem_fixedC {dat : Data} {W : Finset ℕ} {e : List ℕ}
    (heC : ∀ z, z ∈ e ↔ z ∈ fixedC dat W) {κ : ℕ} (hκ : κ ∈ W) :
    inCU dat e κ = true := by
  simp only [inCU, List.all_eq_true]
  intro z hz
  have hz' : z ∈ fixedC dat W := (heC z).mp hz
  simp only [fixedC, Finset.mem_filter] at hz'
  exact beq_iff_eq.mpr (hz'.2 κ hκ)

private lemma lamOK_fixes {dat : Data} (h : lamOK dat = true) :
    ∀ κ < 2 ^ 10, ∀ l ∈ lamList, actK dat.uConjT κ l = l := by
  rw [lamOK, Bool.and_eq_true] at h
  have h1 := h.1
  rw [List.all_eq_true] at h1
  intro κ hκ l hl
  have h2 := h1 κ (List.mem_range.mpr (by simpa using hκ))
  rw [List.all_eq_true] at h2
  exact beq_iff_eq.mp (h2 l hl)

private lemma lamOK_cover {dat : Data} (h : lamOK dat = true) :
    ∀ τ, τ < 2 ^ 9 → ∃ l ∈ lamList, ∃ z, z < 32 ∧ l ^^^ emb z = τ := by
  rw [lamOK, Bool.and_eq_true] at h
  have h2 := h.2
  rw [List.all_eq_true] at h2
  intro τ hτ
  have h3 := h2 τ (List.mem_range.mpr (by simpa using hτ))
  rw [List.any_eq_true] at h3
  obtain ⟨l, hl, h4⟩ := h3
  rw [List.any_eq_true] at h4
  obtain ⟨z, hz, h5⟩ := h4
  exact ⟨l, hl, z, List.mem_range.mp hz, by rwa [beq_iff_eq] at h5⟩

private lemma Y_card_le {dat : Data} {W Y : Finset ℕ}
    (hlam : lamOK dat = true) (hW10 : ∀ κ ∈ W, κ < 2 ^ 10)
    (hY9 : ∀ τ ∈ Y, τ < 2 ^ 9)
    (hYW : ∀ τ ∈ Y, ∀ κ ∈ W, actK dat.uConjT κ τ = τ) :
    Y.card ≤ 16 * (fixedC dat W).card := by
  classical
  have hfixlam := lamOK_fixes hlam
  have hcover := lamOK_cover hlam
  have hcover2 : ∀ τ, τ < 2 ^ 9 →
      ∃ p : ℕ × ℕ, p.1 ∈ lamList ∧ p.2 < 32 ∧ p.1 ^^^ emb p.2 = τ := by
    intro τ hτ
    obtain ⟨l, hl, z, hz, heq⟩ := hcover τ hτ
    exact ⟨(l, z), hl, hz, heq⟩
  let f : ℕ → ℕ × ℕ := fun τ =>
    if hτ : τ < 2 ^ 9 then Classical.choose (hcover2 τ hτ) else (0, 0)
  have hf_prop : ∀ τ ∈ Y, (f τ).1 ∈ lamList ∧ (f τ).2 < 32 ∧
      (f τ).1 ^^^ emb (f τ).2 = τ := by
    intro τ hτ
    have hτ' : τ < 2 ^ 9 := hY9 τ hτ
    have hfτ : f τ = Classical.choose (hcover2 τ hτ') := by
      dsimp only [f]
      rw [dif_pos hτ']
    rw [hfτ]
    exact Classical.choose_spec (hcover2 τ hτ')
  have hfixC : ∀ τ ∈ Y, ∀ κ ∈ W,
      actK dat.uConjT κ (emb (f τ).2) = emb (f τ).2 := by
    intro τ hτ κ hκ
    have hτ' : τ < 2 ^ 9 := hY9 τ hτ
    set p : ℕ × ℕ := Classical.choose (hcover2 τ hτ') with hp
    have hspec : p.1 ∈ lamList ∧ p.2 < 32 ∧ p.1 ^^^ emb p.2 = τ := by
      rw [hp]
      exact Classical.choose_spec (hcover2 τ hτ')
    have hfτ : f τ = p := by
      dsimp only [f]
      rw [dif_pos hτ']
    rw [hfτ]
    have h1 : actK dat.uConjT κ τ = τ := hYW τ hτ κ hκ
    have h3 : actK dat.uConjT κ p.1 = p.1 := hfixlam κ (hW10 κ hκ) p.1 hspec.1
    have hkey : p.1 ^^^ actK dat.uConjT κ (emb p.2) = p.1 ^^^ emb p.2 := by
      calc p.1 ^^^ actK dat.uConjT κ (emb p.2)
          = actK dat.uConjT κ p.1 ^^^ actK dat.uConjT κ (emb p.2) := by rw [h3]
        _ = actK dat.uConjT κ (p.1 ^^^ emb p.2) :=
            (actK_xor dat.uConjT κ p.1 (emb p.2)).symm
        _ = actK dat.uConjT κ τ := by rw [hspec.2.2]
        _ = τ := h1
        _ = p.1 ^^^ emb p.2 := hspec.2.2.symm
    exact Nat.xor_right_injective (x := p.1) hkey
  have hmaps : Set.MapsTo f ↑Y ↑(lamList.toFinset ×ˢ fixedC dat W) := by
    intro τ hτ
    obtain ⟨hl, hz32, hτeq⟩ := hf_prop τ hτ
    change f τ ∈ lamList.toFinset ×ˢ fixedC dat W
    rw [Finset.mem_product]
    refine ⟨List.mem_toFinset.mpr hl, ?_⟩
    simp only [fixedC, Finset.mem_filter, Finset.mem_range]
    exact ⟨hz32, hfixC τ hτ⟩
  have hinj : Set.InjOn f ↑Y := by
    intro τ hτ τ' hτ' heq
    have h1 := (hf_prop τ hτ).2.2
    have h2 := (hf_prop τ' hτ').2.2
    have hpair1 : (f τ).1 = (f τ').1 := by rw [heq]
    have hpair2 : (f τ).2 = (f τ').2 := by rw [heq]
    calc τ = (f τ).1 ^^^ emb (f τ).2 := h1.symm
      _ = (f τ').1 ^^^ emb (f τ').2 := by rw [hpair1, hpair2]
      _ = τ' := h2
  calc Y.card ≤ (lamList.toFinset ×ˢ fixedC dat W).card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ = lamList.toFinset.card * (fixedC dat W).card := Finset.card_product _ _
    _ ≤ 16 * (fixedC dat W).card :=
        Nat.mul_le_mul_right _ (by
          calc lamList.toFinset.card ≤ lamList.length := List.toFinset_card_le _
            _ = 16 := lamList_length)


private lemma walk_D {dat : Data} {F : List Fact} {D : Finset ℕ}
    (hD : XorClosed D) (hD16 : ∀ x ∈ D, x < 2 ^ 16)
    (hDq : ∀ x ∈ D, qN dat.beta x = 0)
    (hDb : ∀ x ∈ D, ∀ y ∈ D, betaN dat.beta x y = 0)
    (hsw : swalk (fun s : List ℕ × List ℕ => s.1) (dUpd (aMat dat) (bRows dat))
      (dVisit dat F (yTab dat (ylist ()))) 17 [0] 0
      (singList dat, List.range 1024) = true) :
    ∃ node s, (∀ x, x ∈ node ↔ x ∈ D) ∧
      (∀ κ, κ ∈ s.2 ↔ κ < 2 ^ 10 ∧ ∀ x ∈ node, actK dat.aCols κ x = x) ∧
      dVisit dat F (yTab dat (ylist ())) node s = true := by
  classical
  let I : List ℕ → ℕ → List ℕ × List ℕ → Prop := fun node top s =>
    (∀ w ∈ D, 2 ^ top ≤ w → w ∈ s.1) ∧
    (∀ κ, κ ∈ s.2 ↔ κ < 2 ^ 10 ∧ ∀ x ∈ node, actK dat.aCols κ x = x)
  have hcand : ∀ node top s, I node top s →
      (∀ x, x ∈ node ↔ x ∈ D ∧ x < 2 ^ top) →
      ∀ v ∈ D, 2 ^ top ≤ v → v ∈ (fun s : List ℕ × List ℕ => s.1) s := by
    intro node top s hI _ v hv hvt
    exact hI.1 v hv hvt
  have hupd : ∀ node top s v, I node top s →
      (∀ x, x ∈ node ↔ x ∈ D ∧ x < 2 ^ top) →
      v ∈ D → 2 ^ top ≤ v → (∀ w ∈ D, 2 ^ top ≤ w → v ≤ w) →
      I (node ++ node.map (v ^^^ ·)) (Nat.log2 v + 1)
        (dUpd (aMat dat) (bRows dat) s v) := by
    intro node top s v hI hnode hvD hvt hmin
    obtain ⟨hIcand, hIact⟩ := hI
    constructor
    · intro w hwD hpw
      have hwtop : 2 ^ top ≤ w :=
        le_trans hvt (le_trans (le_of_lt (lt_pow_log2_succ v)) hpw)
      have hws : w ∈ s.1 := hIcand w hwD hwtop
      simp only [dUpd, List.mem_filter]
      refine ⟨hws, ?_⟩
      rw [Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rw [decide_eq_true_eq]; exact hpw
      · rw [beq_iff_eq]
        have hbr : (bRows dat)[v]! = colsOf 16 (betaN dat.beta v) := by
          rw [bRows_getElem! dat (by simpa using hD16 v hvD), if_pos (hDq v hvD)]
        rw [hbr, colsAct_colsOf (betaN_xor_right dat.beta v) (hD16 w hwD)]
        exact hDb v hvD w hwD
    · intro κ
      simp only [dUpd, List.mem_filter]
      constructor
      · rintro ⟨hκs, hfix⟩
        obtain ⟨hκ10, hfixnode⟩ := (hIact κ).mp hκs
        rw [beq_iff_eq, colsAct_aMat dat hκ10 (hD16 v hvD)] at hfix
        refine ⟨hκ10, ?_⟩
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hfixnode x hx
        · rw [List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          rw [actK_xor, hfix, hfixnode y hy]
      · rintro ⟨hκ10, hfixall⟩
        have hfixnode : ∀ x ∈ node, actK dat.aCols κ x = x := by
          intro x hx
          exact hfixall x (List.mem_append_left _ hx)
        have h0node : 0 ∈ node := (hnode 0).mpr ⟨hD.1, Nat.two_pow_pos top⟩
        have hvfix : actK dat.aCols κ v = v := by
          have hvmem : v ∈ node ++ node.map (v ^^^ ·) :=
            List.mem_append_right _ (List.mem_map.mpr ⟨0, h0node, by rw [Nat.xor_zero]⟩)
          exact hfixall v hvmem
        refine ⟨(hIact κ).mpr ⟨hκ10, hfixnode⟩, ?_⟩
        rw [beq_iff_eq, colsAct_aMat dat hκ10 (hD16 v hvD)]
        exact hvfix
  have hI0 : I [0] 0 (singList dat, List.range 1024) := by
    constructor
    · intro w hwD hw1
      simp only [singList, List.mem_filter, List.mem_range]
      rw [Bool.and_eq_true]
      have hw0 : w ≠ 0 := by
        have h1 : 1 ≤ w := by simpa using hw1
        omega
      exact ⟨by simpa using hD16 w hwD, by rw [bne_iff_ne]; exact hw0,
        by rw [beq_iff_eq]; exact hDq w hwD⟩
    · intro κ
      rw [List.mem_range]
      exact ⟨fun hκ => ⟨hκ, by
          intro x hx
          rw [List.mem_singleton] at hx
          subst hx
          exact actK_zero dat.aCols κ⟩,
        fun hκ => hκ.1⟩
  have hnode0 : ∀ x, x ∈ ([0] : List ℕ) ↔ x ∈ D ∧ x < 2 ^ 0 := by
    intro x
    rw [List.mem_singleton]
    constructor
    · intro hx
      subst hx
      exact ⟨hD.1, by decide⟩
    · rintro ⟨hxD, hx⟩
      rw [pow_zero] at hx
      omega
  obtain ⟨node, top, s, hnode, hI, hvisit⟩ :=
    swalk_sound (S := D) (I := I)
      (cands := fun s : List ℕ × List ℕ => s.1)
      (upd := dUpd (aMat dat) (bRows dat))
      (visit := dVisit dat F (yTab dat (ylist ())))
      hD hcand hupd hsw hI0 hnode0
  exact ⟨node, s, hnode, hI.2, hvisit⟩

private lemma walk_W {dat : Data} {F : List Fact} {W : Finset ℕ} {node M' : List ℕ} {a : ℕ}
    (hW : XorClosed W) (hWM : ∀ w ∈ W, w ∈ M')
    (hww : wwalk dat F node M' a = true) :
    ∃ V, (∀ x, x ∈ V ↔ x ∈ W) ∧
      (a * V.length ≤ 2 ^ 14 ∨ farkasCase dat F node V = true) := by
  classical
  let I : List ℕ → ℕ → List ℕ → Prop := fun _ top c => ∀ w ∈ W, 2 ^ top ≤ w → w ∈ c
  let upd : List ℕ → ℕ → List ℕ := fun c v =>
    let p := 2 ^ (Nat.log2 v + 1)
    c.filter (p ≤ ·)
  have hcand : ∀ node top c, I node top c →
      (∀ x, x ∈ node ↔ x ∈ W ∧ x < 2 ^ top) →
      ∀ v ∈ W, 2 ^ top ≤ v → v ∈ (fun c : List ℕ => c) c := by
    intro node top c hI _ v hv hvt
    exact hI v hv hvt
  have hupd : ∀ node top c v, I node top c →
      (∀ x, x ∈ node ↔ x ∈ W ∧ x < 2 ^ top) →
      v ∈ W → 2 ^ top ≤ v → (∀ w ∈ W, 2 ^ top ≤ w → v ≤ w) →
      I (node ++ node.map (v ^^^ ·)) (Nat.log2 v + 1) (upd c v) := by
    intro node top c v hI _ hv hvt hmin w hw hwle
    rw [List.mem_filter]
    refine ⟨hI w hw (le_trans hvt (le_trans (le_of_lt (lt_pow_log2_succ v)) hwle)), ?_⟩
    rw [decide_eq_true_eq]
    exact hwle
  have hI0 : I [0] 0 M' := by
    intro w hw _
    exact hWM w hw
  have hnode0 : ∀ x, x ∈ ([0] : List ℕ) ↔ x ∈ W ∧ x < 2 ^ 0 := by
    intro x
    rw [List.mem_singleton]
    constructor
    · intro hx
      subst hx
      exact ⟨hW.1, by decide⟩
    · rintro ⟨hx, hx1⟩
      rw [pow_zero] at hx1
      omega
  obtain ⟨V, top, c, hV, hI, hvisit⟩ :=
    swalk_sound (S := W) (I := I)
      (cands := fun c : List ℕ => c)
      (upd := upd)
      (visit := fun V _ => a * V.length ≤ 2 ^ 14 || farkasCase dat F node V)
      hW hcand hupd hww hI0 hnode0
  refine ⟨V, hV, ?_⟩
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using hvisit


theorem card_le_of_p0Check {dat : Data} {F : List Fact} (h : p0Check dat F = true)
    (hA : ∀ κ < 2 ^ 10, ∀ κ' < 2 ^ 10, ∀ x < 2 ^ 16,
      actK dat.aCols (κ ^^^ κ') x = actK dat.aCols κ (actK dat.aCols κ' x))
    (hB : ∀ κ < 2 ^ 10, ∀ κ' < 2 ^ 10, ∀ x < 2 ^ 9,
      actK dat.uConjT (κ ^^^ κ') x = actK dat.uConjT κ (actK dat.uConjT κ' x))
    {D W Y : Finset ℕ} (hD : XorClosed D) (hD16 : ∀ x ∈ D, x < 2 ^ 16)
    (hDq : ∀ x ∈ D, qN dat.beta x = 0) (hDb : ∀ x ∈ D, ∀ y ∈ D, betaN dat.beta x y = 0)
    (hW : XorClosed W) (hW10 : ∀ κ ∈ W, κ < 2 ^ 10)
    (hWD : ∀ κ ∈ W, ∀ x ∈ D, actK dat.aCols κ x = x)
    (hY9 : ∀ τ ∈ Y, τ < 2 ^ 9) (hYW : ∀ τ ∈ Y, ∀ κ ∈ W, actK dat.uConjT κ τ = τ)
    (hsol : ∀ ds ks : List ℕ, (∀ δ ∈ ds, δ ∈ D) → (∀ κ ∈ ks, κ ∈ W) →
      ∃ X, LiftSol dat F ds ks X) :
    D.card * W.card * Y.card ≤ 2 ^ 14 := by
  classical
  rw [p0Check] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hyc, hlam⟩, hsw⟩ := h
  have hYle := Y_card_le (dat := dat) (W := W) (Y := Y) hlam hW10 hY9 hYW
  have hCxor : XorClosed (fixedC dat W) := fixedC_xorClosed dat W
  have hC32 : ∀ z ∈ fixedC dat W, z < 2 ^ 5 := by
    intro z hz
    simp only [fixedC, Finset.mem_filter] at hz
    exact Finset.mem_range.mp hz.1
  obtain ⟨e, he, heC⟩ := ycover_sound hyc hCxor hC32
  have heCeq : e.toFinset = fixedC dat W :=
    Finset.ext (fun z => by rw [List.mem_toFinset, heC z])
  have hCle : (fixedC dat W).card ≤ e.length := by
    calc (fixedC dat W).card = e.toFinset.card := by rw [heCeq]
      _ ≤ e.length := List.toFinset_card_le e
  obtain ⟨node, s, hnodeD, hMspec, hdv⟩ := walk_D hD hD16 hDq hDb hsw
  have hDle : D.card ≤ node.length := card_le_length_of_mem_iff hnodeD
  have hWsub : W ⊆ s.2.toFinset := by
    intro κ hκ
    rw [List.mem_toFinset, hMspec]
    exact ⟨hW10 κ hκ, fun x hx => hWD κ hκ x ((hnodeD x).mp hx)⟩
  have hWleM : W.card ≤ s.2.length :=
    le_trans (Finset.card_le_card hWsub) (List.toFinset_card_le s.2)
  set cu : List Bool := (List.range 1024).map (inCU dat e) with hcu
  set M' : List ℕ := s.2.filter fun κ =>
    ((e, cu.toArray, cu.count true) : List ℕ × Array Bool × Nat).2.1[κ]! with hM'def
  have hy0 : ((e, cu.toArray, cu.count true) : List ℕ × Array Bool × Nat) ∈
      yTab dat (ylist ()) := by
    rw [yTab, List.mem_map]
    exact ⟨e, he, rfl⟩
  have hy := (List.all_eq_true.mp (by simpa only [dVisit] using hdv))
    ((e, cu.toArray, cu.count true) : List ℕ × Array Bool × Nat) hy0
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hy
  have hWleC : W.card ≤ List.count true cu := by
    have hsub : W ⊆ ((List.range 1024).filter (inCU dat e)).toFinset := by
      intro w hw
      rw [List.mem_toFinset, List.mem_filter]
      exact ⟨List.mem_range.mpr (hW10 w hw), inCU_of_mem_fixedC heC hw⟩
    calc W.card ≤ ((List.range 1024).filter (inCU dat e)).toFinset.card :=
          Finset.card_le_card hsub
      _ ≤ ((List.range 1024).filter (inCU dat e)).length := List.toFinset_card_le _
      _ = cu.count true := by
          rw [hcu]
          exact (count_map_true (inCU dat e) 1024).symm
  have hWM' : ∀ w ∈ W, w ∈ M' := by
    intro w hw
    rw [hM'def, List.mem_filter]
    refine ⟨List.mem_toFinset.mp (hWsub hw), ?_⟩
    have hget : ((e, cu.toArray, cu.count true) : List ℕ × Array Bool × Nat).2.1[w]! =
        inCU dat e w :=
      yTab_snd_fst_getElem! dat e (by simpa using hW10 w hw)
    rw [hget]
    exact inCU_of_mem_fixedC heC hw
  have hWleM' : W.card ≤ M'.length := by
    have hsub : W ⊆ M'.toFinset := fun w hw => List.mem_toFinset.mpr (hWM' w hw)
    exact le_trans (Finset.card_le_card hsub) (List.toFinset_card_le M')
  have hM'xor : XorClosed M'.toFinset := by
    constructor
    · rw [List.mem_toFinset, hM'def, List.mem_filter]
      refine ⟨(hMspec 0).mpr ⟨by decide, fun x _ => actK_zero_left dat.aCols x⟩, ?_⟩
      have hget : ((e, cu.toArray, cu.count true) : List ℕ × Array Bool × Nat).2.1[0]! =
          inCU dat e 0 :=
        yTab_snd_fst_getElem! dat e (by decide)
      rw [hget]
      exact inCU_of_mem_fixedC heC hW.1
    · intro κ hκ κ' hκ'
      rw [List.mem_toFinset] at hκ hκ'
      rw [hM'def, List.mem_filter] at hκ hκ'
      obtain ⟨hκs, hκc⟩ := hκ
      obtain ⟨hκ's, hκ'c⟩ := hκ'
      have hκ10 : κ < 2 ^ 10 := ((hMspec κ).mp hκs).1
      have hκ'10 : κ' < 2 ^ 10 := ((hMspec κ').mp hκ's).1
      have hfixc : inCU dat e κ = true := by
        have hget : ((e, cu.toArray, cu.count true) : List ℕ × Array Bool × Nat).2.1[κ]! =
            inCU dat e κ :=
          yTab_snd_fst_getElem! dat e (by simpa using hκ10)
        rwa [hget] at hκc
      have hfixc' : inCU dat e κ' = true := by
        have hget : ((e, cu.toArray, cu.count true) : List ℕ × Array Bool × Nat).2.1[κ']! =
            inCU dat e κ' :=
          yTab_snd_fst_getElem! dat e (by simpa using hκ'10)
        rwa [hget] at hκ'c
      rw [List.mem_toFinset, hM'def, List.mem_filter]
      refine ⟨(hMspec (κ ^^^ κ')).mpr ⟨by
          have h := Nat.xor_lt_two_pow hκ10 hκ'10
          simpa using h, ?_⟩, ?_⟩
      · intro x hx
        rw [hA κ hκ10 κ' hκ'10 x (hD16 x ((hnodeD x).mp hx)),
          ((hMspec κ').mp hκ's).2 x hx, ((hMspec κ).mp hκs).2 x hx]
      · have hget : ((e, cu.toArray, cu.count true) : List ℕ × Array Bool × Nat).2.1[κ ^^^ κ']! =
            inCU dat e (κ ^^^ κ') :=
          yTab_snd_fst_getElem! dat e (by
            have h := Nat.xor_lt_two_pow hκ10 hκ'10
            simpa using h)
        rw [hget]
        simp only [inCU, List.all_eq_true]
        intro z hz
        have hzC : z ∈ fixedC dat W := (heC z).mp hz
        simp only [fixedC, Finset.mem_filter] at hzC
        have hz32 : z < 32 := Finset.mem_range.mp hzC.1
        have hzκ : actK dat.uConjT κ (emb z) = emb z :=
          beq_iff_eq.mp (List.all_eq_true.mp hfixc z hz)
        have hzκ' : actK dat.uConjT κ' (emb z) = emb z :=
          beq_iff_eq.mp (List.all_eq_true.mp hfixc' z hz)
        refine beq_iff_eq.mpr ?_
        rw [hB κ hκ10 κ' hκ'10 (emb z) (emb_lt z), hzκ', hzκ]
  have hC0 : 0 ∈ fixedC dat W := by simp [fixedC, emb_zero, actK_zero]
  have he0 : 0 ∈ e := (heC 0).mpr hC0
  have hnode0 : 0 ∈ node := (hnodeD 0).mpr hD.1
  have hnode_len : 0 < node.length := List.length_pos_of_mem hnode0
  have he_len : 0 < e.length := List.length_pos_of_mem he0
  have hpos_a : 0 < node.length * 16 * e.length :=
    Nat.mul_pos (Nat.mul_pos hnode_len (by decide)) he_len
  set a : ℕ := node.length * 16 * e.length with ha
  have hsum : D.card * W.card * Y.card ≤ a * W.card := by
    have hY16 : Y.card ≤ 16 * e.length :=
      le_trans hYle (Nat.mul_le_mul_left 16 hCle)
    rw [ha]
    calc D.card * W.card * Y.card
        ≤ node.length * W.card * (16 * e.length) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right W.card hDle) hY16
      _ = node.length * 16 * e.length * W.card := by ac_rfl
  by_cases hW14 : a * W.card ≤ 2 ^ 14
  · exact le_trans hsum hW14
  have hWgt : 2 ^ 14 < a * W.card := Nat.lt_of_not_ge hW14
  by_cases h1 : a * s.2.length ≤ 2 ^ 14
  · exact le_trans hsum (le_trans (Nat.mul_le_mul_left a hWleM) h1)
  by_cases h2 : a * List.count true cu ≤ 2 ^ 14
  · exact le_trans hsum (le_trans (Nat.mul_le_mul_left a hWleC) h2)
  by_cases h3 : a * M'.length ≤ 2 ^ 14
  · exact le_trans hsum (le_trans (Nat.mul_le_mul_left a hWleM') h3)
  have hcand : candOK dat F node M' a = true := by
    rcases hy with (h | h) | (h | h)
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3
    · exact h
  rw [candOK, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hcand
  rcases hcand with ⟨h15, hfc⟩ | ⟨h16, hww⟩
  ·
    have hM'lt : M'.length < 2 * W.card := by
      have h215 : (2 : ℕ) ^ 15 = 2 * 2 ^ 14 := by decide
      have h2 : 2 ^ 15 < 2 * (a * W.card) := by
        rw [h215]
        exact Nat.mul_lt_mul_of_pos_left hWgt (by decide)
      have h3 : a * M'.length < a * (2 * W.card) := by
        calc a * M'.length ≤ 2 ^ 15 := h15
          _ < 2 * (a * W.card) := h2
          _ = a * (2 * W.card) := by ac_rfl
      exact (Nat.mul_lt_mul_left hpos_a).mp h3
    have hM'card : M'.toFinset.card < 2 * W.card :=
      lt_of_le_of_lt (List.toFinset_card_le M') hM'lt
    have hsub : W ⊆ M'.toFinset := fun w hw => List.mem_toFinset.mpr (hWM' w hw)
    have hWeq : W = M'.toFinset := eq_of_card_lt_two_mul hW hM'xor hsub hM'card
    obtain ⟨X, hX⟩ := hsol (basisIn node) (basisIn M')
      (fun δ hδ => (hnodeD δ).mp (mem_of_mem_basisIn hδ))
      (fun κ hκ => by
        have hκ' : κ ∈ M'.toFinset :=
          List.mem_toFinset.mpr (mem_of_mem_basisIn hκ)
        rwa [← hWeq] at hκ')
    exact absurd hX (farkasCase_sound hfc X)
  ·
    obtain ⟨V, hVW, hvisit⟩ := walk_W hW hWM' hww
    have hWV : W.card ≤ V.length := card_le_length_of_mem_iff hVW
    rcases hvisit with hV14 | hfc
    · exact le_trans hsum (le_trans (Nat.mul_le_mul_left a hWV) hV14)
    · obtain ⟨X, hX⟩ := hsol (basisIn node) (basisIn V)
        (fun δ hδ => (hnodeD δ).mp (mem_of_mem_basisIn hδ))
        (fun κ hκ => (hVW κ).mp (mem_of_mem_basisIn hκ))
      exact absurd hX (farkasCase_sound hfc X)


end CFSG.Monster.B.TwoA.Sp8.P0Rank
