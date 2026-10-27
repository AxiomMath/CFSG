module

public import Mathlib.Data.Set.Card

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem w16l_eq_univ_of_line_closed {Ω : Type} [Finite Ω] {q : ℕ}
    (hΩ : Nat.card Ω = q ^ 3 + 1) (line : Ω → Ω → Set Ω)
    (hxl : ∀ x y, x ≠ y → x ∈ line x y) (hyl : ∀ x y, x ≠ y → y ∈ line x y)
    (hcard : ∀ x y, x ≠ y → (line x y).ncard = q + 1)
    (hline : ∀ x y z w, x ≠ y → z ∈ line x y → w ∈ line x y → z ≠ w → line z w = line x y)
    {S : Set Ω} (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → line x y ⊆ S)
    {a b c : Ω} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hcab : c ∉ line a b) :
    S = Set.univ := by
  classical
  haveI := Fintype.ofFinite Ω
  rw [Set.eq_univ_iff_forall]
  intro p
  by_contra hp
  have hq1 : 1 ≤ q := by
    have hsub : ({a, b} : Set Ω) ⊆ line a b := by
      rw [Set.pair_subset_iff]
      exact ⟨hxl a b hab, hyl a b hab⟩
    have h2 : 2 ≤ (line a b).ncard := by
      rw [← Set.ncard_pair hab]
      exact Set.ncard_le_ncard hsub
    rw [hcard a b hab] at h2
    omega
  have hqpos : 0 < q := by omega
  let A : Ω → Set Ω := fun x => line p x \ {p}
  let t : Ω → Finset Ω := fun x => Finset.univ.filter fun z => z ∈ line p x ∧ z ≠ p
  have ht_coe : ∀ x, (t x : Set Ω) = A x := by
    intro x
    ext z
    simp [t, A]
  have hA_card : ∀ x ∈ S, (A x).ncard = q := by
    intro x hx
    have hxp : x ≠ p := fun h => hp (h ▸ hx)
    have hp_mem : p ∈ line p x := hxl p x hxp.symm
    have h := Set.ncard_sdiff_singleton_of_mem (s := line p x) hp_mem
    rw [hcard p x hxp.symm] at h
    simpa [A] using h
  have hA_disj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (A x) (A y) := by
    intro x hx y hy hxy
    rw [Set.disjoint_left]
    intro z hzx hzy
    have hpx : p ≠ x := fun h => hp (h.symm ▸ hx)
    have hpy : p ≠ y := fun h => hp (h.symm ▸ hy)
    have hpz : p ≠ z := fun h => hzx.2 (by simp [h])
    have heqx : line p z = line p x :=
      hline p x p z hpx (hxl p x hpx) hzx.1 hpz
    have heqy : line p z = line p y :=
      hline p y p z hpy (hxl p y hpy) hzy.1 hpz
    have heq : line p x = line p y := heqx.symm.trans heqy
    have hyx : y ∈ line p x := heq.symm ▸ hyl p y hpy
    have hlin : line x y = line p x :=
      hline p x x y hpx (hyl p x hpx) hyx hxy
    exact hp (hS x hx y hy hxy (hlin.symm ▸ hxl p x hpx))
  let Sf : Finset Ω := Finset.univ.filter fun z => z ∈ S
  have hSf_mem : ∀ x, x ∈ Sf ↔ x ∈ S := by
    intro x
    simp [Sf]
  have hSf_card : Sf.card = S.ncard := by
    rw [← Set.ncard_coe_finset Sf, show (Sf : Set Ω) = S by ext z; simp [Sf]]
  have ht_card : ∀ x ∈ S, (t x).card = q := by
    intro x hx
    rw [← Set.ncard_coe_finset (t x), ht_coe x]
    exact hA_card x hx
  have ht_disj : (Sf : Set Ω).PairwiseDisjoint t := by
    rw [← Finset.pairwiseDisjoint_coe]
    intro x hx y hy hxy
    simp only [Function.onFun]
    rw [ht_coe x, ht_coe y]
    exact hA_disj x ((hSf_mem x).mp hx) y ((hSf_mem y).mp hy) hxy
  have hunion_card : (Sf.biUnion t).card = S.ncard * q := by
    rw [Finset.card_biUnion ht_disj]
    rw [Finset.sum_const_nat (fun x hx => ht_card x ((hSf_mem x).mp hx))]
    rw [hSf_card]
  have hsub : (Sf.biUnion t : Set Ω) ⊆ {p}ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [Finset.mem_coe, Finset.mem_biUnion] at hz
    obtain ⟨x, -, hzx⟩ := hz
    have hzA : z ∈ A x := by rw [← ht_coe x]; exact hzx
    exact fun h => hzA.2 (by simp [h])
  have hcompl : ({p}ᶜ : Set Ω).ncard = q ^ 3 := by
    have h := Set.ncard_sdiff_singleton_of_mem (s := (Set.univ : Set Ω)) (Set.mem_univ p)
    rw [Set.ncard_univ, hΩ, Nat.add_sub_cancel] at h
    rw [show ({p}ᶜ : Set Ω) = Set.univ \ {p} by ext z; simp]
    exact h
  have hle : (Sf.biUnion t).card ≤ ({p}ᶜ : Set Ω).ncard := by
    rw [← Set.ncard_coe_finset (Sf.biUnion t)]
    exact Set.ncard_le_ncard hsub
  have hupper : S.ncard * q ≤ q ^ 3 := by
    rw [← hunion_card, ← hcompl]
    exact hle
  have hScard_le : S.ncard ≤ q ^ 2 := by
    have hq3 : q ^ 3 = q ^ 2 * q := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
    rw [hq3] at hupper
    exact Nat.le_of_mul_le_mul_right hupper hqpos
  have hac : a ≠ c := by
    intro h
    refine hcab ?_
    rw [← h]
    exact hxl a b hab
  have hLsub : line a c ⊆ S := hS a ha c hc hac
  let Lf : Finset Ω := Finset.univ.filter fun z => z ∈ line a c
  have hLf_mem : ∀ y, y ∈ Lf ↔ y ∈ line a c := by
    intro y
    simp [Lf]
  have hLf_card : Lf.card = q + 1 := by
    rw [← Set.ncard_coe_finset Lf,
      show (Lf : Set Ω) = line a c by ext z; simp [Lf], hcard a c hac]
  have hbL : b ∉ line a c := by
    intro hbL
    have heq : line a b = line a c := hline a c a b hac (hxl a c hac) hbL hab
    exact hcab (heq.symm ▸ hyl a c hac)
  let B : Ω → Set Ω := fun y => line b y \ {b}
  let tB : Ω → Finset Ω := fun y => Finset.univ.filter fun z => z ∈ line b y ∧ z ≠ b
  have htB_coe : ∀ y, (tB y : Set Ω) = B y := by
    intro y
    ext z
    simp [tB, B]
  have hB_card : ∀ y ∈ line a c, (B y).ncard = q := by
    intro y hy
    have hby : b ≠ y := by
      intro h
      exact hbL (by rw [h]; exact hy)
    have hb_mem : b ∈ line b y := hxl b y hby
    have h := Set.ncard_sdiff_singleton_of_mem (s := line b y) hb_mem
    rw [hcard b y hby] at h
    simpa [B] using h
  have hB_sub : ∀ y ∈ line a c, B y ⊆ S := by
    intro y hy
    have hby : b ≠ y := by
      intro h
      exact hbL (by rw [h]; exact hy)
    have hlineS : line b y ⊆ S := hS b hb y (hLsub hy) hby
    intro z hz
    exact hlineS hz.1
  have hB_disj : ∀ y ∈ line a c, ∀ y' ∈ line a c, y ≠ y' → Disjoint (B y) (B y') := by
    intro y hy y' hy' hyy'
    rw [Set.disjoint_left]
    intro z hzy hzy'
    have hby : b ≠ y := by
      intro h
      exact hbL (by rw [h]; exact hy)
    have hby' : b ≠ y' := by
      intro h
      exact hbL (by rw [h]; exact hy')
    have hbz : b ≠ z := by
      intro h
      exact hzy.2 (by simp [h])
    have heq1 : line b z = line b y :=
      hline b y b z hby (hxl b y hby) hzy.1 hbz
    have heq2 : line b z = line b y' :=
      hline b y' b z hby' (hxl b y' hby') hzy'.1 hbz
    have heq : line b y = line b y' := heq1.symm.trans heq2
    have hy'_mem : y' ∈ line b y := heq.symm ▸ hyl b y' hby'
    have heq3 : line y y' = line b y :=
      hline b y y y' hby (hyl b y hby) hy'_mem hyy'
    have heq4 : line y y' = line a c :=
      hline a c y y' hac hy hy' hyy'
    have hbl : line b y = line a c := heq3.symm.trans heq4
    exact hbL (hbl ▸ hxl b y hby)
  have htB_card : ∀ y ∈ line a c, (tB y).card = q := by
    intro y hy
    rw [← Set.ncard_coe_finset (tB y), htB_coe y]
    exact hB_card y hy
  have htB_disj : (Lf : Set Ω).PairwiseDisjoint tB := by
    rw [← Finset.pairwiseDisjoint_coe]
    intro y hy y' hy' hyy'
    simp only [Function.onFun]
    rw [htB_coe y, htB_coe y']
    exact hB_disj y ((hLf_mem y).mp hy) y' ((hLf_mem y').mp hy') hyy'
  have hunionB_card : (Lf.biUnion tB).card = (q + 1) * q := by
    rw [Finset.card_biUnion htB_disj]
    rw [Finset.sum_const_nat (fun y hy => htB_card y ((hLf_mem y).mp hy))]
    rw [hLf_card]
  have hb_notin : b ∉ Lf.biUnion tB := by
    intro hb'
    rw [Finset.mem_biUnion] at hb'
    obtain ⟨y, hy, hby_mem⟩ := hb'
    have hzB : b ∈ B y := by rw [← htB_coe y]; exact hby_mem
    exact hzB.2 (by simp)
  have hFcard : (insert b (Lf.biUnion tB)).card = q ^ 2 + q + 1 := by
    rw [Finset.card_insert_of_notMem hb_notin, hunionB_card, Nat.add_mul, one_mul, pow_two]
  have hFsub : insert b (Lf.biUnion tB) ⊆ Sf := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact (hSf_mem b).mpr hb
    · rw [Finset.mem_biUnion] at hz
      obtain ⟨y, hy, hzy⟩ := hz
      have hyL : y ∈ line a c := (hLf_mem y).mp hy
      have hzB : z ∈ B y := by rw [← htB_coe y]; exact hzy
      exact (hSf_mem z).mpr (hB_sub y hyL hzB)
  have hlower : q ^ 2 + q + 1 ≤ S.ncard := by
    have hle' := Finset.card_le_card hFsub
    rw [hFcard] at hle'
    rwa [hSf_card] at hle'
  have hq2lt : q ^ 2 < q ^ 2 + q + 1 := by
    have h : q ^ 2 < q ^ 2 + (q + 1) := Nat.lt_add_of_pos_right (Nat.succ_pos q)
    rwa [← Nat.add_assoc] at h
  exact absurd (lt_of_lt_of_le (lt_of_lt_of_le hq2lt hlower) hScard_le) (lt_irrefl (q ^ 2))

end CFSG.LocalAnalysis.WeakClosure81

end
