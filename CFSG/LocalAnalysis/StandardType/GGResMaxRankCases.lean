module

public import CFSG.LocalAnalysis.StandardType.GGResMaxRankDefs
public import CFSG.LocalAnalysis.StandardType.GGRCCaseI

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def ggMaxRankDyn : Fin 8 → Fin 8 ⊕ Fin 2 :=
  ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inr 0]

private def ggMaxRankG8 (i j : Fin 8) : ZMod 3 :=
  ggMaxRankPairing 3 0 0 false (ggMaxRankDyn i) (ggMaxRankDyn j)

private def ggMaxRankG8Inv : Fin 8 → Fin 8 → ZMod 3 :=
  ![![1, 1, 1, 2, 0, 1, 2, 2], ![1, 2, 2, 1, 0, 2, 1, 1], ![1, 2, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 2, 0, 1, 2, 0], ![0, 0, 0, 0, 0, 2, 1, 0], ![1, 2, 0, 1, 2, 0, 0, 0], ![2, 1, 0, 2, 1, 0, 2, 0], ![2, 1, 0, 0, 0, 0, 0, 2]]

private def ggMaxRankW0 : List (Fin 8) :=
  [0, 1, 0, 2, 1, 0, 3, 2, 1, 0, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1, 0, 6, 5, 4, 3, 2, 1, 0, 7, 2, 1,
   0, 3, 2, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4, 7, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4, 7, 2,
   1, 0, 3, 2, 1, 4, 3, 2, 5, 4, 3, 6, 5, 4, 7, 2, 1, 0, 3, 2, 1, 4, 3, 2, 5, 4, 3, 6, 7, 2, 1,
   0, 3, 2, 1, 4, 3, 2, 5, 4, 3, 6, 7, 2, 1, 0, 3, 2, 4, 3, 5, 4, 7, 2, 1, 3, 2, 7]

private def ggMaxRankAct (i : Fin 8) (c : Fin 8 → ZMod 3) : Fin 8 → ZMod 3 :=
  Function.update c i (c i - ∑ j, ggMaxRankG8 i j * c j)

private def ggMaxRankW0Elt {G : Type} [Group G] {Bs : Subgroup G}
    (φ : Fin 8 ⊕ Fin 2 → MulAut ↥Bs) : MulAut ↥Bs :=
  ggMaxRankW0.foldl (fun g k => φ (ggMaxRankDyn k) * g) 1

private theorem ggMaxRank_G8_inv_mul (i j : Fin 8) :
    ∑ k, ggMaxRankG8Inv i k * ggMaxRankG8 k j = if i = j then 1 else 0 := by
  revert i j
  decide +kernel

private theorem ggMaxRank_pairing_dyn (u v : ZMod 3) (apos : Bool) (i j : Fin 8) :
    ggMaxRankPairing 3 u v apos (ggMaxRankDyn i) (ggMaxRankDyn j) = ggMaxRankG8 i j := by
  revert u v apos i j
  decide +kernel

private theorem ggMaxRank_w0_check (j : Fin 8) :
    ggMaxRankW0.foldl (fun c i => ggMaxRankAct i c) (fun k => if k = j then 1 else 0) =
      fun k => if k = j then -1 else 0 := by
  revert j
  decide +kernel

private theorem l6x1_dyn_indep_three {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 8 ⊕ Fin 2 → V} {α : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod 3) V}
    {u v : ZMod 3} {apos : Bool}
    (hpair : ∀ o o', α o (h o') = ggMaxRankPairing 3 u v apos o o') :
    LinearIndependent (ZMod 3) fun i : Fin 8 => h (ggMaxRankDyn i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  first | funext j | intro j
  have hk : ∀ k : Fin 8, ∑ i : Fin 8, c i * ggMaxRankG8 k i = 0 := by
    intro k
    have h1 : α (ggMaxRankDyn k) (∑ i : Fin 8, c i • h (ggMaxRankDyn i)) = 0 := by
      rw [hc, map_zero]
    have h2 : α (ggMaxRankDyn k) (∑ i : Fin 8, c i • h (ggMaxRankDyn i)) =
        ∑ i : Fin 8, c i * ggMaxRankG8 k i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, hpair, ggMaxRank_pairing_dyn, smul_eq_mul]
    rw [← h2]
    exact h1
  have h1 : ∑ i : Fin 8, c i * (∑ k : Fin 8, ggMaxRankG8Inv j k * ggMaxRankG8 k i) = c j := by
    have hinner : ∀ i : Fin 8, (∑ k : Fin 8, ggMaxRankG8Inv j k * ggMaxRankG8 k i) =
        if j = i then (1 : ZMod 3) else 0 := fun i => ggMaxRank_G8_inv_mul j i
    simp only [hinner]
    rw [show ∑ i : Fin 8, c i * (if j = i then (1 : ZMod 3) else 0) =
        ∑ i : Fin 8, (if j = i then c i else 0) from by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : j = i <;> simp [h]]
    exact Finset.sum_ite_eq_of_mem Finset.univ j (fun i : Fin 8 => c i) (Finset.mem_univ j)
  have h3 : ∑ i : Fin 8, c i * (∑ k : Fin 8, ggMaxRankG8Inv j k * ggMaxRankG8 k i) =
      ∑ k : Fin 8, ggMaxRankG8Inv j k * (∑ i : Fin 8, c i * ggMaxRankG8 k i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  have h4 : c j = ∑ k : Fin 8, ggMaxRankG8Inv j k * (∑ i : Fin 8, c i * ggMaxRankG8 k i) :=
    h1.symm.trans h3
  rw [h4]
  apply Finset.sum_eq_zero
  intro k _
  rw [hk k, mul_zero]

private theorem ggMaxRank_dyn_indep {p : ℕ} [Fact p.Prime] (hp : p = 3) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin 8 ⊕ Fin 2 → V}
    {α : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod p) V} {u v : ZMod p} {apos : Bool}
    (hpair : ∀ o o', α o (h o') = ggMaxRankPairing p u v apos o o') :
    LinearIndependent (ZMod p) fun i : Fin 8 => h (ggMaxRankDyn i) := by
  subst hp
  exact l6x1_dyn_indep_three hpair

private theorem l6x1_dyn_inl (i : Fin 8) (hi : i.val < 7) :
    ggMaxRankDyn i = Sum.inl i := by
  revert i
  decide +kernel

private theorem l6x1_dyn_seven : ggMaxRankDyn (7 : Fin 8) = Sum.inr 0 := by
  decide +kernel

private theorem l6x1_dyn_ne_a (i : Fin 8) : ggMaxRankDyn i ≠ Sum.inr 1 := by
  revert i
  decide +kernel

private theorem ggMaxRank_span_L {p : ℕ} [Fact p.Prime] (hp : p = 3) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin 8 ⊕ Fin 2 → V}
    (hrel : ∑ j : Fin 8, ((ggMaxRankMarks j : ℕ) : ZMod p) • h (Sum.inl j) = 0) :
    Submodule.span (ZMod p) (h '' {o : Fin 8 ⊕ Fin 2 | o ≠ Sum.inr 1}) =
      Submodule.span (ZMod p) (Set.range fun i : Fin 8 => h (ggMaxRankDyn i)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨o, ho, rfl⟩
    rcases o with i | k
    · by_cases hi : i.val < 7
      · rw [← l6x1_dyn_inl i hi]
        exact Submodule.subset_span ⟨i, rfl⟩
      · have hi7 : i = 7 := Fin.ext (by omega)
        subst hi7
        let f : Fin 8 → V := fun j => ((ggMaxRankMarks j : ℕ) : ZMod p) • h (Sum.inl j)
        have hf7 : f 7 = h (Sum.inl 7) := by
          simp [f, ggMaxRankMarks]
        have hzero : f 7 + ∑ x ∈ Finset.univ \ {(7 : Fin 8)}, f x = 0 := by
          rw [← Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ (7 : Fin 8)) f]
          exact hrel
        have hneg : h (Sum.inl 7) = - ∑ x ∈ Finset.univ \ {(7 : Fin 8)}, f x := by
          rw [← hf7, eq_neg_iff_add_eq_zero]
          exact hzero
        rw [hneg]
        refine Submodule.neg_mem _ ?_
        apply Submodule.sum_mem
        intro x hx
        have hxne : x ≠ 7 := by
          simpa using (Finset.mem_sdiff.mp hx).2
        have hxval : x.val < 7 := by
          have hxv : x.val ≠ 7 := by
            intro hv
            exact hxne (Fin.ext hv)
          omega
        change ((ggMaxRankMarks x : ℕ) : ZMod p) • h (Sum.inl x) ∈
          Submodule.span (ZMod p) (Set.range fun i : Fin 8 => h (ggMaxRankDyn i))
        apply Submodule.smul_mem
        rw [← l6x1_dyn_inl x hxval]
        exact Submodule.subset_span ⟨x, rfl⟩
    · fin_cases k
      · change h (Sum.inr (0 : Fin 2)) ∈
          Submodule.span (ZMod p) (Set.range fun i : Fin 8 => h (ggMaxRankDyn i))
        rw [← l6x1_dyn_seven]
        exact Submodule.subset_span ⟨7, rfl⟩
      · exact absurd rfl ho
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨ggMaxRankDyn i, l6x1_dyn_ne_a i, rfl⟩

private theorem ggMaxRank_span_top {p : ℕ} [Fact p.Prime] (hp : p = 3) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin 8 ⊕ Fin 2 → V}
    {α : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod p) V} {u v : ZMod p} {apos : Bool}
    (hd : Module.finrank (ZMod p) V = 9)
    (hpair : ∀ o o', α o (h o') = ggMaxRankPairing p u v apos o o')
    (hrel : ∑ j : Fin 8, ((ggMaxRankMarks j : ℕ) : ZMod p) • h (Sum.inl j) = 0)
    (hI : h (Sum.inr 1) ∉ Submodule.span (ZMod p) (h '' {o : Fin 8 ⊕ Fin 2 | o ≠ Sum.inr 1})) :
    Submodule.span (ZMod p) (Set.range h) = ⊤ := by
  have hind : LinearIndependent (ZMod p) (fun i : Fin 8 => h (ggMaxRankDyn i)) :=
    ggMaxRank_dyn_indep hp hpair
  have hS := ggMaxRank_span_L hp hrel
  have hx : h (Sum.inr 1) ∉
      Submodule.span (ZMod p) (Set.range fun i : Fin 8 => h (ggMaxRankDyn i)) := by
    rw [← hS]
    exact hI
  have hsnoc : LinearIndependent (ZMod p)
      (Fin.snoc (fun i : Fin 8 => h (ggMaxRankDyn i)) (h (Sum.inr 1))) :=
    LinearIndependent.finSnoc hind hx
  have htop := LinearIndependent.span_eq_top_of_card_eq_finrank hsnoc (by simp [hd])
  refine le_antisymm le_top ?_
  rw [← htop]
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
  · exact ⟨ggMaxRankDyn i, by rw [Fin.snoc_castSucc]⟩
  · exact ⟨Sum.inr 1, by rw [Fin.snoc_last]⟩

private theorem l6x1_rtg_symm {β : Type} {r : β → β → Prop}
    (hsymm : ∀ a b, r a b → r b a) :
    ∀ {a b : β}, Relation.ReflTransGen r a b → Relation.ReflTransGen r b a := by
  intro a b h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      exact (Relation.ReflTransGen.single (hsymm _ _ hbc)).trans ih

private theorem l6x1_pair_inl_adj (a b : Fin 8)
    (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val) (u v : ZMod 3) (apos : Bool) :
    ggMaxRankPairing 3 u v apos (Sum.inl a) (Sum.inl b) = -1 := by
  revert a b u v apos
  decide +kernel

private theorem l6x1_pair_b_c2 (u v : ZMod 3) (apos : Bool) :
    ggMaxRankPairing 3 u v apos (Sum.inr 0) (Sum.inl 2) = -1 := by
  revert u v apos
  decide +kernel

private theorem l6x1_pair_c2_b (u v : ZMod 3) (apos : Bool) :
    ggMaxRankPairing 3 u v apos (Sum.inl 2) (Sum.inr 0) = -1 := by
  revert u v apos
  decide +kernel

private theorem l6x1_pair_a_c2 (u v : ZMod 3) :
    ggMaxRankPairing 3 u v false (Sum.inr 1) (Sum.inl 2) = -1 := by
  revert u v
  decide +kernel

private theorem l6x1_pair_c2_a (u v : ZMod 3) :
    ggMaxRankPairing 3 u v false (Sum.inl 2) (Sum.inr 1) = -1 := by
  revert u v
  decide +kernel

private theorem l6x1_pair_a_c5 (u v : ZMod 3) :
    ggMaxRankPairing 3 u v true (Sum.inr 1) (Sum.inl 5) = -1 := by
  revert u v
  decide +kernel

private theorem l6x1_pair_c5_a (u v : ZMod 3) :
    ggMaxRankPairing 3 u v true (Sum.inl 5) (Sum.inr 1) = -1 := by
  revert u v
  decide +kernel

private theorem l6x1_neg_ne_zero_three : (-1 : ZMod 3) ≠ 0 := by
  decide +kernel

private theorem ggMaxRank_conn {p : ℕ} [Fact p.Prime] (hp : p = 3) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin 8 ⊕ Fin 2 → V}
    {α : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod p) V} {u v : ZMod p} {apos : Bool}
    (hpair : ∀ o o', α o (h o') = ggMaxRankPairing p u v apos o o') :
    ∀ o o' : Fin 8 ⊕ Fin 2,
      Relation.ReflTransGen (fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0) o o' := by
  subst hp
  let step : Fin 8 ⊕ Fin 2 → Fin 8 ⊕ Fin 2 → Prop :=
    fun a b => α a (h b) ≠ 0 ∧ α b (h a) ≠ 0
  change ∀ o o' : Fin 8 ⊕ Fin 2, Relation.ReflTransGen step o o'
  have hadj : ∀ i : Fin 7, step (Sum.inl i.succ) (Sum.inl i.castSucc) := by
    intro i
    constructor
    · rw [hpair, l6x1_pair_inl_adj i.succ i.castSucc (Or.inr rfl) u v apos]
      exact l6x1_neg_ne_zero_three
    · rw [hpair, l6x1_pair_inl_adj i.castSucc i.succ (Or.inl rfl) u v apos]
      exact l6x1_neg_ne_zero_three
  have hb : step (Sum.inr 0) (Sum.inl 2) := by
    constructor
    · rw [hpair, l6x1_pair_b_c2 u v apos]; exact l6x1_neg_ne_zero_three
    · rw [hpair, l6x1_pair_c2_b u v apos]; exact l6x1_neg_ne_zero_three
  have haF : apos = false → step (Sum.inr 1) (Sum.inl 2) := by
    intro hap
    constructor
    · rw [hpair, hap, l6x1_pair_a_c2 u v]; exact l6x1_neg_ne_zero_three
    · rw [hpair, hap, l6x1_pair_c2_a u v]; exact l6x1_neg_ne_zero_three
  have haT : apos = true → step (Sum.inr 1) (Sum.inl 5) := by
    intro hap
    constructor
    · rw [hpair, hap, l6x1_pair_a_c5 u v]; exact l6x1_neg_ne_zero_three
    · rw [hpair, hap, l6x1_pair_c5_a u v]; exact l6x1_neg_ne_zero_three
  have hchain : ∀ n (hn : n < 8),
      Relation.ReflTransGen step (Sum.inl ⟨n, hn⟩) (Sum.inl (0 : Fin 8)) := by
    intro n
    induction n with
    | zero =>
        intro hn
        have h0 : (⟨0, hn⟩ : Fin 8) = 0 := Fin.ext rfl
        rw [h0]
    | succ n ih =>
        intro hn
        have hn7 : n < 7 := by omega
        have hn' : n < 8 := by omega
        have hstep : step (Sum.inl ⟨n + 1, hn⟩) (Sum.inl ⟨n, hn'⟩) :=
          hadj ⟨n, hn7⟩
        exact (Relation.ReflTransGen.single hstep).trans (ih hn')
  have hreach : ∀ o : Fin 8 ⊕ Fin 2, Relation.ReflTransGen step o (Sum.inl (0 : Fin 8)) := by
    intro o
    rcases o with i | k
    · simpa using hchain i.val i.isLt
    · have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
      rcases hk with rfl | rfl
      · exact (Relation.ReflTransGen.single hb).trans
          (hchain (2 : Fin 8).val (2 : Fin 8).isLt)
      · cases hap : apos
        · exact (Relation.ReflTransGen.single (haF hap)).trans
            (hchain (2 : Fin 8).val (2 : Fin 8).isLt)
        · exact (Relation.ReflTransGen.single (haT hap)).trans
            (hchain (5 : Fin 8).val (5 : Fin 8).isLt)
  intro o o'
  exact (hreach o).trans (l6x1_rtg_symm (fun a b hab => ⟨hab.2, hab.1⟩) (hreach o'))

private theorem ggMaxRank_basis_of_x {p : ℕ} [Fact p.Prime] (hp : p = 3) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin 8 ⊕ Fin 2 → V}
    {α : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod p) V} {u v : ZMod p} {apos : Bool}
    (hd : Module.finrank (ZMod p) V = 9)
    (hpair : ∀ o o', α o (h o') = ggMaxRankPairing p u v apos o o') {wx : V} (hwx : wx ≠ 0)
    (hwxα : ∀ i : Fin 8, α (ggMaxRankDyn i) wx = 0) :
    ∃ b : Module.Basis (Option (Fin 8)) (ZMod p) V,
      b none = wx ∧ ∀ i, b (some i) = h (ggMaxRankDyn i) := by
  subst hp
  have hinv : ∀ (c : Fin 8 → ZMod 3) (j : Fin 8),
      c j = ∑ k, ggMaxRankG8Inv j k * (∑ i, c i * ggMaxRankG8 k i) := by
    intro c j
    have h4 : (∑ k, ggMaxRankG8Inv j k * (∑ i, c i * ggMaxRankG8 k i)) = c j := by
      calc ∑ k, ggMaxRankG8Inv j k * (∑ i, c i * ggMaxRankG8 k i)
          = ∑ k, ∑ i, ggMaxRankG8Inv j k * (c i * ggMaxRankG8 k i) := by
              simp only [Finset.mul_sum]
        _ = ∑ i, ∑ k, ggMaxRankG8Inv j k * (c i * ggMaxRankG8 k i) := Finset.sum_comm
        _ = ∑ i, c i * ∑ k, ggMaxRankG8Inv j k * ggMaxRankG8 k i := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ = ∑ i, c i * (if j = i then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [ggMaxRank_G8_inv_mul j i]
        _ = c j := by
              rw [Finset.sum_eq_single j]
              · simp
              · intro i _ hij
                rw [if_neg (Ne.symm hij), mul_zero]
              · intro hj
                exact absurd (Finset.mem_univ j) hj
    exact h4.symm
  let v : Option (Fin 8) → V := fun o => Option.elim o wx (fun i => h (ggMaxRankDyn i))
  have hli : LinearIndependent (ZMod 3) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g none • wx + ∑ i, g (some i) • h (ggMaxRankDyn i) = 0 := by
      rw [Fintype.sum_option] at hg
      simpa [v] using hg
    have hk : ∀ k : Fin 8, ∑ i, g (some i) * ggMaxRankG8 k i = 0 := by
      intro k
      have h1 := congrArg (α (ggMaxRankDyn k)) hg'
      rw [map_add, map_smul, hwxα k, smul_zero, zero_add, map_zero, map_sum] at h1
      have hcongr : (∑ i, α (ggMaxRankDyn k) (g (some i) • h (ggMaxRankDyn i))) =
          ∑ i, g (some i) * ggMaxRankG8 k i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul, hpair (ggMaxRankDyn k) (ggMaxRankDyn i), ggMaxRank_pairing_dyn]
        simp [smul_eq_mul]
      rw [← hcongr]
      exact h1
    have hsome : ∀ j, g (some j) = 0 := by
      intro j
      rw [hinv (fun i => g (some i)) j]
      apply Finset.sum_eq_zero
      intro k _
      rw [hk k, mul_zero]
    have hnone : g none = 0 := by
      have h0 : g none • wx = 0 := by
        have h2 := hg'
        rw [Finset.sum_eq_zero (fun i _ => by rw [hsome i, zero_smul])] at h2
        simpa using h2
      exact (smul_eq_zero.mp h0).resolve_right hwx
    intro o
    cases o with
    | none => simpa using hnone
    | some j => simpa using hsome j
  have hcard : Fintype.card (Option (Fin 8)) = Module.finrank (ZMod 3) V := by
    rw [hd]
    simp
  haveI : Nonempty (Option (Fin 8)) := ⟨none⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_, ?_⟩
  · rw [congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) none]
    simp [v]
  · intro i
    rw [congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) (some i)]
    simp [v]

private theorem ggMaxRank_w0_mem {G : Type} [Group G] {Bs : Subgroup G}
    (A : Subgroup (MulAut ↥Bs)) (φ : Fin 8 ⊕ Fin 2 → MulAut ↥Bs)
    (hA : ∀ i : Fin 8, φ (ggMaxRankDyn i) ∈ A) : ggMaxRankW0Elt φ ∈ A := by
  have hmain : ∀ (l : List (Fin 8)) (g : MulAut ↥Bs), g ∈ A →
      l.foldl (fun g k => φ (ggMaxRankDyn k) * g) g ∈ A := by
    intro l
    induction l with
    | nil => intro g hg; simpa using hg
    | cons k l ih =>
      intro g hg
      rw [List.foldl_cons]
      exact ih (φ (ggMaxRankDyn k) * g) (A.mul_mem (hA k) hg)
  simpa [ggMaxRankW0Elt] using hmain ggMaxRankW0 1 A.one_mem

private def l6x2_H {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin 8 ⊕ Fin 2 → V) (c : Fin 8 → ZMod p) : V :=
  ∑ j : Fin 8, c j • h (ggMaxRankDyn j)

private lemma l6x2_H_update {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin 8 ⊕ Fin 2 → V) (c : Fin 8 → ZMod p) (k : Fin 8) (t : ZMod p) :
    l6x2_H h (Function.update c k t) =
      l6x2_H h c + (t - c k) • h (ggMaxRankDyn k) := by
  have hterm : ∀ j : Fin 8,
      Function.update c k t j = c j + (if j = k then t - c k else 0) := by
    intro j
    rw [Function.update_apply]
    split_ifs with h
    · rw [h]
      ring
    · simp
  calc l6x2_H h (Function.update c k t)
      = ∑ j, (c j + (if j = k then t - c k else 0)) • h (ggMaxRankDyn j) := by
        simp only [l6x2_H]
        exact Finset.sum_congr rfl (fun j _ => by rw [hterm j])
    _ = ∑ j, (c j • h (ggMaxRankDyn j) +
          (if j = k then t - c k else 0) • h (ggMaxRankDyn j)) := by
        exact Finset.sum_congr rfl (fun j _ => by rw [add_smul])
    _ = (∑ j, c j • h (ggMaxRankDyn j)) +
          ∑ j, (if j = k then t - c k else 0) • h (ggMaxRankDyn j) := by
        rw [Finset.sum_add_distrib]
    _ = l6x2_H h c + (t - c k) • h (ggMaxRankDyn k) := by
        simp only [l6x2_H]
        have hs : (∑ j, (if j = k then t - c k else 0) • h (ggMaxRankDyn j)) =
            (t - c k) • h (ggMaxRankDyn k) := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro j _ hj
            rw [if_neg hj, zero_smul]
          · intro hk
            exact absurd (Finset.mem_univ k) hk
        rw [hs]

private def l6x2_step {G : Type} [Group G] {Bs : Subgroup G}
    (φ : Fin 8 ⊕ Fin 2 → MulAut ↥Bs) : MulAut ↥Bs → Fin 8 → MulAut ↥Bs :=
  fun g k => φ (ggMaxRankDyn k) * g

private lemma l6x2_w0Elt_eq {G : Type} [Group G] {Bs : Subgroup G}
    (φ : Fin 8 ⊕ Fin 2 → MulAut ↥Bs) :
    ggMaxRankW0Elt φ = ggMaxRankW0.foldl (l6x2_step φ) 1 := rfl

private theorem ggMaxRank_w0_act {G : Type} [Group G] {Bs : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp : p = 3) {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Fin 8 ⊕ Fin 2 → MulAut ↥Bs) {h : Fin 8 ⊕ Fin 2 → V}
    {α : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod p) V} {u v : ZMod p} {apos : Bool}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hpair : ∀ o o', α o (h o') = ggMaxRankPairing p u v apos o o') (i : Fin 8) :
    ggLin (p := p) ι (ggMaxRankW0Elt φ) (h (ggMaxRankDyn i)) = - h (ggMaxRankDyn i) := by
  subst hp
  rw [l6x2_w0Elt_eq φ]
  have hstep : ∀ (k : Fin 8) (c : Fin 8 → ZMod 3),
      ggLin (p := 3) ι (φ (ggMaxRankDyn k)) (l6x2_H h c) =
        l6x2_H h (ggMaxRankAct k c) := by
    intro k c
    rw [hφ (ggMaxRankDyn k) (l6x2_H h c)]
    have hα : α (ggMaxRankDyn k) (l6x2_H h c) = ∑ j, ggMaxRankG8 k j * c j := by
      simp only [l6x2_H, map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro j _
      rw [hpair (ggMaxRankDyn k) (ggMaxRankDyn j), ggMaxRank_pairing_dyn, smul_eq_mul]
      ring
    have hact : ggMaxRankAct k c =
        Function.update c k (c k - ∑ j, ggMaxRankG8 k j * c j) := rfl
    rw [hα, hact, l6x2_H_update]
    have ht : c k - (∑ j, ggMaxRankG8 k j * c j) - c k =
        -(∑ j, ggMaxRankG8 k j * c j) := by ring
    rw [ht, neg_smul]
    abel
  have hmain : ∀ (l : List (Fin 8)) (c : Fin 8 → ZMod 3),
      ggLin (p := 3) ι (l.foldl (l6x2_step φ) 1) (l6x2_H h c) =
        l6x2_H h (l.foldl (fun c k => ggMaxRankAct k c) c) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => intro c; simp
    | append_singleton l k ih =>
      intro c
      rw [List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change ggLin ι (φ (ggMaxRankDyn k) * List.foldl (l6x2_step φ) 1 l) (l6x2_H h c) =
        l6x2_H h (ggMaxRankAct k (List.foldl (fun c k => ggMaxRankAct k c) c l))
      rw [map_mul, LinearEquiv.mul_apply, ih, hstep]
  have hHe : l6x2_H h (fun k => if k = i then (1 : ZMod 3) else 0) = h (ggMaxRankDyn i) := by
    simp only [l6x2_H]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg hj, zero_smul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hHneg : l6x2_H h (fun k => if k = i then (-1 : ZMod 3) else 0) = - h (ggMaxRankDyn i) := by
    simp only [l6x2_H]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg hj, zero_smul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hgen := hmain ggMaxRankW0 (fun k => if k = i then (1 : ZMod 3) else 0)
  conv_lhs =>
    rw [show h (ggMaxRankDyn i) =
        l6x2_H h (fun k => if k = i then (1 : ZMod 3) else 0) from hHe.symm]
  rw [hgen]
  rw [show ggMaxRankW0.foldl (fun c k => ggMaxRankAct k c)
        (fun k => if k = i then (1 : ZMod 3) else 0) =
      (fun k => if k = i then (-1 : ZMod 3) else 0) from ggMaxRank_w0_check i]
  exact hHneg

private theorem ggMaxRank_w0_fix {G : Type} [Group G] {Bs : Subgroup G} {p : ℕ} [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Fin 8 ⊕ Fin 2 → MulAut ↥Bs) {h : Fin 8 ⊕ Fin 2 → V}
    {α : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) {wx : V}
    (hwxα : ∀ i : Fin 8, α (ggMaxRankDyn i) wx = 0) :
    ggLin (p := p) ι (ggMaxRankW0Elt φ) wx = wx := by
  rw [l6x2_w0Elt_eq φ]
  have hfix : ∀ k : Fin 8, ggLin (p := p) ι (φ (ggMaxRankDyn k)) wx = wx := by
    intro k
    rw [hφ (ggMaxRankDyn k) wx, hwxα k, zero_smul, sub_zero]
  have hmain : ∀ (l : List (Fin 8)) (g : MulAut ↥Bs),
      ggLin (p := p) ι g wx = wx →
      ggLin (p := p) ι (l.foldl (l6x2_step φ) g) wx = wx := by
    intro l
    induction l with
    | nil => intro g hg; simpa using hg
    | cons k l ih =>
      intro g hg
      rw [List.foldl_cons]
      exact ih (φ (ggMaxRankDyn k) * g) (by
        rw [map_mul, LinearEquiv.mul_apply, hg, hfix k])
  have hone : ggLin (p := p) ι (1 : MulAut ↥Bs) wx = wx := by
    rw [map_one]
    rfl
  have h := hmain ggMaxRankW0 1 hone
  exact h

private theorem ggMaxRank_transv_lin {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (b : Module.Basis (Option (Fin 8)) (ZMod p) V) {ha : V}
    (hha : ha ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 8 => b (some i)))
    (αa : Module.Dual (ZMod p) V) (hα2 : αa ha = 2) (hκ : αa (b none) ≠ 0)
    (ra s : V ≃ₗ[ZMod p] V) (hra : ∀ v, ra v = v - αa v • ha)
    (hs : ∀ i : Fin 8, s (b (some i)) = - b (some i)) (hsx : s (b none) = b none) :
    ∃ f : Module.Dual (ZMod p) V, f ≠ 0 ∧ f ha = 0 ∧ ha ≠ 0 ∧
      ∀ v, (ra * s * ra * s⁻¹) v = v + f v • ha := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')
  have hcomp : s.toLinearMap.comp s.toLinearMap = LinearMap.id := by
    apply b.ext
    intro i
    rcases i with _ | j
    · simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, hsx]
    · simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, hs j,
        map_neg, neg_neg]
  have hss : s * s = 1 := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply]
    change s (s v) = v
    exact LinearMap.congr_fun hcomp v
  have hsinv : s⁻¹ = s := by
    calc s⁻¹ = s⁻¹ * 1 := (mul_one _).symm
      _ = s⁻¹ * (s * s) := by rw [hss]
      _ = (s⁻¹ * s) * s := (mul_assoc _ _ _).symm
      _ = 1 * s := by rw [inv_mul_cancel]
      _ = s := one_mul _
  have hsha : s ha = -ha := by
    refine Submodule.span_induction (p := fun x _ => s x = -x) ?_ ?_ ?_ ?_ hha
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      exact hs i
    · simp
    · intro y z _ _ hy hz
      rw [map_add, hy, hz]
      abel
    · intro a y _ hy
      rw [map_smul, hy, smul_neg]
  have hcoord : b.coord none ha = 0 := by
    refine Submodule.span_induction (p := fun x _ => b.coord none x = 0) ?_ ?_ ?_ ?_ hha
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      rw [b.coord_apply, b.repr_self_apply]
      simp
    · simp
    · intro y z _ _ hy hz
      rw [map_add, hy, hz, add_zero]
    · intro a y _ hy
      rw [map_smul, hy, smul_eq_mul, mul_zero]
  let f : Module.Dual (ZMod p) V := (-2 * αa (b none)) • b.coord none
  have hfx : f (b none) = -2 * αa (b none) := by
    dsimp only [f]
    rw [LinearMap.smul_apply, b.coord_apply, b.repr_self_apply]
    simp [smul_eq_mul]
  have hf_ne : f ≠ 0 := by
    intro hf0
    have hx0 : f (b none) = 0 := by rw [hf0, LinearMap.zero_apply]
    rw [hfx] at hx0
    exact (mul_ne_zero (neg_ne_zero.mpr h2) hκ) hx0
  have hf_ha : f ha = 0 := by
    dsimp only [f]
    rw [LinearMap.smul_apply, hcoord, smul_zero]
  have hha_ne : ha ≠ 0 := by
    intro h
    have h20 : (2 : ZMod p) = 0 := by rw [← hα2, h, map_zero]
    exact h2 h20
  refine ⟨f, hf_ne, hf_ha, hha_ne, ?_⟩
  intro v
  have key : (ra * s * ra * s⁻¹).toLinearMap = LinearMap.id + f.smulRight ha := by
    apply b.ext
    intro i
    rcases i with _ | j
    · change (ra * s * ra * s⁻¹) (b none) = b none + f (b none) • ha
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsinv, hsx,
        hra (b none)]
      rw [map_sub, hsx, map_smul, hsha, smul_neg]
      rw [hra, hfx]
      simp only [map_sub, map_neg, map_smul, hα2, smul_eq_mul]
      module
    · change (ra * s * ra * s⁻¹) (b (some j)) = b (some j) + f (b (some j)) • ha
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsinv, hs j]
      have h1 : ra (- b (some j)) = - b (some j) + αa (b (some j)) • ha := by
        rw [hra, map_neg, neg_smul, sub_neg_eq_add]
      rw [h1]
      have h2 : s (- b (some j) + αa (b (some j)) • ha) =
          b (some j) - αa (b (some j)) • ha := by
        rw [map_add, map_neg, hs j, map_smul, hsha, smul_neg, neg_neg, sub_eq_add_neg]
      rw [h2]
      have h3 : ra (b (some j) - αa (b (some j)) • ha) = b (some j) := by
        rw [hra, map_sub, map_smul, hα2, smul_eq_mul]
        module
      have hfj : f (b (some j)) = 0 := by
        dsimp only [f]
        rw [LinearMap.smul_apply, b.coord_apply, b.repr_self_apply]
        simp
      rw [h3, hfj, zero_smul, add_zero]
  have h := LinearMap.congr_fun key v
  change (ra * s * ra * s⁻¹) v = v + f v • ha at h
  exact h


private theorem l6x4_fix_closure {E : Type*} [Group E] {S : Set (MulAut E)} {b : E}
    (hb : ∀ ψ ∈ S, ψ b = b) : ∀ ψ ∈ Subgroup.closure S, ψ b = b := by
  intro ψ hψ
  have hle : Subgroup.closure S ≤ MulAction.stabilizer (MulAut E) b := by
    rw [Subgroup.closure_le]
    exact hb
  exact hle hψ

private theorem l6x4_x_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : x ≠ 1 := by
  intro hx1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by rw [hDgen]; exact Subgroup.subset_closure (by simp)
  have hyp : y ^ p = 1 := hDea.2 y hyD
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hDgen, hx1, Subgroup.closure_le]
    intro a ha
    have ha' : a = 1 ∨ a = y := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers y
  have hyle : Nat.card (Subgroup.zpowers y) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hyp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hDle
      _ ≤ p := hyle
  nlinarith [hcon, hp.two_le]

private theorem ggMaxRank_ker (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Fin 8 ⊕ Fin 2 → MulAut ↥Bs}
    {h : Fin 8 ⊕ Fin 2 → V} {α : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAL : ggAutomizer L Bs = Subgroup.closure
      (Set.range (fun j : Fin 8 => φ (Sum.inl j)) ∪ {φ (Sum.inr 0)}))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : Fin 8 => φ (Sum.inl j)) ∪ {φ (Sum.inr 1)})) :
    ∀ w, (∀ o, α o w = 0) → w = 0 := by
  classical
  intro w hαw
  let bb : Bs := Additive.toMul (ι.symm w)
  have hbbw : ι (Additive.ofMul bb) = w := by
    dsimp only [bb]
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hbb : ∀ o, φ o bb = bb := by
    intro o
    have h1 := hφ o w
    rw [hαw o, zero_smul, sub_zero] at h1
    refine (ggLin_fix_iff (p := p) ι (φ o) bb).mpr ?_
    rw [hbbw]
    exact h1
  have hfixL : ∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb := by
    rw [hAL]
    refine l6x4_fix_closure (b := bb) ?_
    rintro ψ (⟨j, rfl⟩ | rfl)
    · exact hbb (Sum.inl j)
    · exact hbb (Sum.inr 0)
  have hfixK : ∀ ψ ∈ ggAutomizer K Bs, ψ bb = bb := by
    rw [hAK]
    refine l6x4_fix_closure (b := bb) ?_
    rintro ψ (⟨j, rfl⟩ | rfl)
    · exact hbb (Sum.inl j)
    · exact hbb (Sum.inr 1)
  have hxmem : (bb : G) ∈ Subgroup.zpowers x :=
    hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hfixL
  have hbb1 : bb = 1 :=
    Subtype.ext (hFixK.1 G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hxmem hfixK)
  rw [← hbbw, hbb1]
  simp

private theorem l6x4_automizer_fixes_x {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hxBs : x ∈ Bs) :
    ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
  have hcent : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  intro ψ hψ
  obtain ⟨g, hgL, hgN, hg⟩ := mem_ggAutomizer_iff.mp hψ
  have hmem : g ∈ Subgroup.centralizer ({x} : Set G) := hcent hgL
  have hcomm : g * x = x * g :=
    ((Subgroup.mem_centralizer_iff.mp hmem) x (by simp)).symm
  apply Subtype.ext
  have h : ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = g * x * g⁻¹ := by
    have h1 := hg (⟨x, hxBs⟩ : ↥Bs)
    simpa using h1
  rw [h, hcomm]
  group

private theorem ggMaxRank_kerK (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Fin 8 ⊕ Fin 2 → MulAut ↥Bs} {h : Fin 8 ⊕ Fin 2 → V}
    {α : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : Fin 8 => φ (Sum.inl j)) ∪ {φ (Sum.inr 1)})) :
    ∀ w, (∀ o : Fin 8 ⊕ Fin 2, o ≠ Sum.inr 0 → α o w = 0) →
      ((Additive.toMul (ι.symm w) : ↥Bs) : G) ∈ Subgroup.zpowers x → w = 0 := by
  classical
  intro w hαw hxmem
  let bb : Bs := Additive.toMul (ι.symm w)
  have hbbw : ι (Additive.ofMul bb) = w := by
    dsimp only [bb]
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hbb : ∀ o, o ≠ Sum.inr 0 → φ o bb = bb := by
    intro o ho
    have h1 := hφ o w
    rw [hαw o ho, zero_smul, sub_zero] at h1
    refine (ggLin_fix_iff (p := p) ι (φ o) bb).mpr ?_
    rw [hbbw]
    exact h1
  have hfixK : ∀ ψ ∈ ggAutomizer K Bs, ψ bb = bb := by
    rw [hAK]
    refine l6x4_fix_closure (b := bb) ?_
    rintro ψ (⟨j, rfl⟩ | rfl)
    · exact hbb (Sum.inl j) (by simp)
    · exact hbb (Sum.inr 1) (by simp)
  have hbb1 : bb = 1 :=
    Subtype.ext (hFixK.1 G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hxmem hfixK)
  rw [← hbbw, hbb1]
  simp

private theorem ggMaxRank_xvec {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Fin 8 ⊕ Fin 2 → MulAut ↥Bs} {h : Fin 8 ⊕ Fin 2 → V}
    {α : Fin 8 ⊕ Fin 2 → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o) (hα : ∀ o, α o (h o) = 2)
    (hAL : ggAutomizer L Bs = Subgroup.closure
      (Set.range (fun j : Fin 8 => φ (Sum.inl j)) ∪ {φ (Sum.inr 0)})) :
    ∃ wx : V, wx ≠ 0 ∧ (∀ o : Fin 8 ⊕ Fin 2, o ≠ Sum.inr 1 → α o wx = 0) ∧
      ((Additive.toMul (ι.symm wx) : ↥Bs) : G) ∈ Subgroup.zpowers x := by
  classical
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hxne : x ≠ 1 := l6x4_x_ne_one hH
  let wx : V := ι (Additive.ofMul (⟨x, hxBs⟩ : Bs))
  refine ⟨wx, ?_, ?_, ?_⟩
  · intro hwx0
    have hof : Additive.ofMul (⟨x, hxBs⟩ : Bs) = 0 := by
      apply ι.injective
      rw [map_zero]
      change wx = 0
      exact hwx0
    have h0 : (⟨x, hxBs⟩ : Bs) = 1 := by simpa using hof
    exact hxne (by simpa using congrArg Subtype.val h0)
  · intro o ho
    have hmem : φ o ∈ ggAutomizer L Bs := by
      rw [hAL]
      apply Subgroup.subset_closure
      rcases o with j | k
      · exact Or.inl ⟨j, rfl⟩
      · fin_cases k
        · exact Or.inr rfl
        · exact absurd rfl ho
    have hfix : φ o ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := l6x4_automizer_fixes_x hH hxBs (φ o) hmem
    have hfixlin : ggLin (p := p) ι (φ o) wx = wx := by
      have h := (ggLin_fix_iff (p := p) ι (φ o) ⟨x, hxBs⟩).mp hfix
      simpa only [wx] using h
    have hzero : α o wx • h o = 0 := by
      have h1 : wx = wx - α o wx • h o := by
        rw [← hφ o wx]
        exact hfixlin.symm
      exact sub_eq_self.mp h1.symm
    have hhne : h o ≠ 0 := (ne_zero_of_apply_eq_two hp2 (hα o)).1
    exact (smul_eq_zero.mp hzero).resolve_right hhne
  · have hsymm : Additive.toMul (ι.symm wx) = (⟨x, hxBs⟩ : Bs) := by
      dsimp only [wx]
      rw [AddEquiv.symm_apply_apply, toMul_ofMul]
    rw [hsymm]
    exact Subgroup.mem_zpowers x

private lemma l6x5_coxeterMatrix_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

private lemma l6x5_isWeyl_E8 : GGIsWeylMatrix CoxeterMatrix.E₈ :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, l6x5_coxeterMatrix_reindex_refl _⟩)))

theorem ggMaxRank_caseI_weyl
    (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hD : GGResMaxRankDatum p Bs L J K ggMaxRankSelI) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨V, i1, i2, ι, φ, h, α, u, v, apos, hp, hd, hφ, hrefl, hpair, hrel,
    ⟨fJ, hfJ⟩, hAJ, hAL, hAK, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hsel⟩ := hD
  have hp2 : p ≠ 2 := by omega
  have hxB : x ∈ B := hH.1.1.2.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hH.1.2.1.1 hxB
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let A : Subgroup (V ≃ₗ[ZMod p] V) := A'.map (ggLin (p := p) ι)
  change GGWeylReflectionGroup p A'
  have hA' : A' = Subgroup.closure (Set.range φ) := by
    dsimp [A']
    rw [hAL, hAK, ← Subgroup.closure_union]
    congr 1
    ext γ
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ((⟨j, rfl⟩ | rfl) | (⟨j, rfl⟩ | rfl))
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr 0, rfl⟩
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr 1, rfl⟩
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl (Or.inl ⟨j, rfl⟩)
      | inr k =>
          fin_cases k
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr (Or.inr rfl)
  have hA : A = Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)) := by
    dsimp [A]
    rw [hA', MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hspan := ggMaxRank_span_top hp hd hpair hrel hsel
  have hker : ∀ w, (∀ o, α o w = 0) → w = 0 :=
    fun w hw => ggMaxRank_ker hFix hFixK hH hφ hAL hAK w hw
  have hconn := ggMaxRank_conn hp hpair
  have hα : ∀ o, α o (h o) = 2 := by
    intro o
    have h1 := hpair o o
    simpa [ggMaxRankPairing] using h1
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hirr : ZS.AbsIrred p A :=
    ggRC_absIrred_of_connected (p := p) (V := V) hp2 (fun o => ggLin (p := p) ι (φ o)) h α
      hφ hα hspan hker hconn A hA
  have hreflLin : ∀ o, GGLinRefl (ggLin (p := p) ι (φ o)) :=
    fun o => (ggRC_isReflection_iff_linRefl (p := p) ι (φ o)).mp (hrefl o)
  have hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} := by
    rw [hA]
    apply le_antisymm
    · apply Subgroup.closure_mono
      intro z hz
      obtain ⟨o, rfl⟩ := hz
      exact ⟨Subgroup.subset_closure (Set.mem_range_self o), hreflLin o⟩
    · rw [Subgroup.closure_le]
      intro z hz
      exact hz.1
  have hcardA : Nat.card A = Nat.card A' := by
    change Nat.card ↥(A'.map (ggLin (p := p) ι)) = Nat.card ↥A'
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι)).toEquiv).symm
  have hWcard : Nat.card ↥(ggAutomizer L Bs) = Nat.card CoxeterMatrix.E₈.Group :=
    (Nat.card_congr fL.toEquiv).symm
  have hjoin : Nat.card A' ≤
      Nat.card ↥Bs * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) :=
    ggRC_card_join_le hOrb hH hxBs
  have hNB : Nat.card ↥Bs = p ^ (Fintype.card (Fin 8) + 1) := by
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = p ^ Module.finrank (ZMod p) V := (FiniteField.pow_finrank_eq_natCard p V).symm
      _ = p ^ (Fintype.card (Fin 8) + 1) := by rw [hd]; norm_num
  have hsmall' : 8 * Nat.card A' <
      p ^ ((Fintype.card (Fin 8) + 1) * Fintype.card (Fin 8) / 2) :=
    ggRC_small_of_card (Fact.out : p.Prime) hp2 CoxeterMatrix.E₈ l6x5_isWeyl_E8
      (by simp) hNB (by rw [← hWcard]; exact hjoin)
  have hsmall : 8 * Nat.card A < p ^ (9 * (9 - 1) / 2) := by
    rw [hcardA]
    simpa using hsmall'
  have hpm1 : 5 ≤ p → ∀ f : Module.Basis (Fin 9) (ZMod p) V,
      (∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin 9)) (c : Fin 9 → ZMod p),
        (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) →
      ∃ b' : Module.Basis (Fin 9) (ZMod p) V, ∀ a ∈ A,
        ∃ (σ : Equiv.Perm (Fin 9)) (c : Fin 9 → ZMod p),
          (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b' i) = c i • b' (σ i) := by
    intro hp5
    exact absurd hp5 (by omega)
  obtain hclass | ⟨N, hN, e, he⟩ :=
    ggRC_classify hKG hp2 hd (by norm_num : 9 ≤ 9) A hirr hgen hsmall hpm1
  ·
    exact ggRC_weylReflGroup_of_linWeyl ι A' hclass
  ·
    let e' : A' ≃* Equiv.Perm (Fin N) :=
      (Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι)).trans e
    have hrefl' : ∀ r : A', GGIsReflection p (r : MulAut ↥Bs) →
        ∃ i j, i ≠ j ∧ e' r = Equiv.swap i j := by
      intro r hr
      have hrlin : GGLinRefl (ggLin (p := p) ι (r : MulAut ↥Bs)) :=
        (ggRC_isReflection_iff_linRefl (p := p) ι (r : MulAut ↥Bs)).mp hr
      obtain ⟨i, j, hij, heij⟩ :=
        he (Subgroup.equivMapOfInjective A' (ggLin (p := p) ι) (ggLin_injective ι) r) hrlin
      exact ⟨i, j, hij, heij⟩
    have hgen' : GGReflGenerated p A' := by
      rw [GGReflGenerated, hA']
      apply le_antisymm
      · apply Subgroup.closure_mono
        intro z hz
        obtain ⟨o, rfl⟩ := hz
        exact ⟨Subgroup.subset_closure (Set.mem_range_self o), hrefl o⟩
      · rw [Subgroup.closure_le]
        intro z hz
        exact hz.1
    exact ggRC_weyl_of_perm A' hN e' hrefl' hgen'

theorem ggMaxRank_caseII_false (hFixK : GGTBFixNbrInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hD : GGResMaxRankDatum p Bs L J K ggMaxRankSelII) : False := by
  obtain ⟨V, i1, i2, ι, φ, h, α, u, v, apos, hp, hd, hφ, hrefl, hpair, hrel,
    ⟨fJ, hfJ⟩, hAJ, hAL, hAK, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hsel⟩ := hD
  have hp2 : p ≠ 2 := by omega
  have hα : ∀ o, α o (h o) = 2 := by
    intro o
    rw [hpair o o]
    simp [ggMaxRankPairing]
  have hsel' : h (Sum.inr 1) ∈ Submodule.span (ZMod p)
      (h '' {o : Fin 8 ⊕ Fin 2 | o ≠ Sum.inr 1}) := hsel
  obtain ⟨wx, hwx0, hwxL, hwxx⟩ := ggMaxRank_xvec hp2 hH hφ hα hAL
  have hκ : α (Sum.inr 1) wx ≠ 0 := by
    intro h0
    refine hwx0 (ggMaxRank_kerK hFixK hH hφ hAK wx (fun o ho => ?_) hwxx)
    by_cases hoa : o = Sum.inr 1
    · subst hoa; exact h0
    · exact hwxL o hoa
  have hwxdyn : ∀ i : Fin 8, α (ggMaxRankDyn i) wx = 0 := by
    intro i
    exact hwxL _ (by fin_cases i <;> simp [ggMaxRankDyn])
  obtain ⟨b, hbn, hbs⟩ := ggMaxRank_basis_of_x hp hd hpair hwx0 hwxdyn
  have hrange : Set.range (fun i : Fin 8 => b (some i)) =
      Set.range (fun i : Fin 8 => h (ggMaxRankDyn i)) := by
    ext z
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, (hbs i).symm⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, hbs i⟩
  have hha : h (Sum.inr 1) ∈ Submodule.span (ZMod p)
      (Set.range fun i : Fin 8 => b (some i)) := by
    rw [hrange, ← ggMaxRank_span_L hp hrel]
    exact hsel'
  let w0 : MulAut ↥Bs := ggMaxRankW0Elt φ
  let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι (φ (Sum.inr 1))
  let s : V ≃ₗ[ZMod p] V := ggLin (p := p) ι w0
  have hs : ∀ i : Fin 8, s (b (some i)) = - b (some i) := by
    intro i
    rw [hbs i]
    exact ggMaxRank_w0_act hp ι φ hφ hpair i
  have hsx : s (b none) = b none := by
    rw [hbn]
    exact ggMaxRank_w0_fix ι φ hφ hwxdyn
  have hra : ∀ v, ra v = v - α (Sum.inr 1) v • h (Sum.inr 1) := by
    intro v
    exact hφ (Sum.inr 1) v
  obtain ⟨f, hf, hfw, hha0, htrans⟩ :=
    ggMaxRank_transv_lin hp2 b hha (α (Sum.inr 1)) (hα (Sum.inr 1))
      (by rw [hbn]; exact hκ) ra s hra hs hsx
  let τ : MulAut ↥Bs := φ (Sum.inr 1) * w0 * φ (Sum.inr 1) * w0⁻¹
  have hlinτ : ggLin (p := p) ι τ = ra * s * ra * s⁻¹ := by
    dsimp only [τ, w0, ra, s]
    rw [map_mul, map_mul, map_mul, map_inv]
  have htr : GGIsTransvection p τ := by
    refine ggIsTransvection_of_apply ι hha0 hf hfw (fun v => ?_)
    rw [hlinτ]
    exact htrans v
  have hφa_K : φ (Sum.inr 1) ∈ ggAutomizer K Bs := by
    rw [hAK]
    exact Subgroup.subset_closure (Or.inr (Set.mem_singleton _))
  have hφdyn_L : ∀ i : Fin 8, φ (ggMaxRankDyn i) ∈ ggAutomizer L Bs := by
    intro i
    rw [hAL]
    apply Subgroup.subset_closure
    fin_cases i <;> simp [ggMaxRankDyn]
  have hw0_L : w0 ∈ ggAutomizer L Bs := ggMaxRank_w0_mem (ggAutomizer L Bs) φ hφdyn_L
  have hτ_mem : τ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    have h1 : φ (Sum.inr 1) ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
      Subgroup.mem_sup_right hφa_K
    have h2 : w0 ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := Subgroup.mem_sup_left hw0_L
    dsimp only [τ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h1)
      (Subgroup.inv_mem _ h2)
  have hle : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  exact hH.2.2.2.1 τ (mem_ggAutomizer_iff.mp (hle hτ_mem)) htr

end CFSG.StandardType

end

