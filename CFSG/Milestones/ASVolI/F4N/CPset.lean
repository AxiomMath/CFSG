module

public import CFSG.Milestones.ASVolI.F4N.A19
public import CFSG.Milestones.ASVolI.F4Sylow
public import CFSG.Milestones.ASVolI.F4N.Cor

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

section Ext

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite Y] {c : α.Completion Y}

@[expose] def burnsideF4nC_ext (c : α.Completion Y) (a l y : c.Γ) (n : ℕ) :
    Set (GPath c.graph n) :=
  {p | p ∈ GPath.nbPaths c.graph a n ∧ p 1 = l ∧ p 2 = y}

theorem burnsideF4nC_card_ext_succ (hc : c.IsFaithful) (a l y : c.Γ) {n : ℕ} (hn : 2 ≤ n) :
    Nat.card ↥(burnsideF4nC_ext c a l y (n + 1)) = Nat.card ↥(burnsideF4nC_ext c a l y n) *
      α.qv (if n % 2 = 0 then CosetGeom.vtype a else !CosetGeom.vtype a) := by
  have := finite_gpath (c := c) n
  have := finite_gpath (c := c) (n + 1)
  have := Fintype.ofFinite ↥(burnsideF4nC_ext c a l y n)
  let f : ↥(burnsideF4nC_ext c a l y (n + 1)) → ↥(burnsideF4nC_ext c a l y n) := fun p =>
    ⟨p.1.take n (Nat.le_succ n),
      ⟨by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le n)]; exact p.2.1.1, p.2.1.2.take n _⟩,
      by rw [GPath.take_apply_of_le _ _ _ (by omega)]; exact p.2.2.1,
      by rw [GPath.take_apply_of_le _ _ _ hn]; exact p.2.2.2⟩
  have hfib : ∀ q : ↥(burnsideF4nC_ext c a l y n), Nat.card {p // f p = q} =
      α.qv (if n % 2 = 0 then CosetGeom.vtype a else !CosetGeom.vtype a) := by
    intro q
    let q' : ↥(GPath.nbPaths c.graph a n) := ⟨q.1, q.2.1⟩
    have e1 : {p // f p = q} ≃ {p : ↥(GPath.nbPaths c.graph a (n + 1)) //
        p.1.take n (Nat.le_succ n) = q'.1} :=
      { toFun := fun p => ⟨⟨p.1.1, p.1.2.1⟩, congrArg Subtype.val p.2⟩
        invFun := fun p => ⟨⟨p.1.1, p.1.2, by
            rw [← GPath.take_apply_of_le p.1.1 n (Nat.le_succ n) (by omega : 1 ≤ n), p.2]
            exact q.2.2.1, by
            rw [← GPath.take_apply_of_le p.1.1 n (Nat.le_succ n) hn, p.2]
            exact q.2.2.2⟩, Subtype.ext p.2⟩
        left_inv := fun p => rfl
        right_inv := fun p => rfl }
    rw [Nat.card_congr (e1.trans (fiberEquiv a q')), card_extSet hc]
    simp only [show n ≠ 0 by omega, ↓reduceIte, vtype_path_end q']
  have hsum : Nat.card ↥(burnsideF4nC_ext c a l y (n + 1)) =
      ∑ q : ↥(burnsideF4nC_ext c a l y n), Nat.card {p // f p = q} := by
    have : ∀ q : ↥(burnsideF4nC_ext c a l y n), Finite {p // f p = q} := fun q => inferInstance
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv f).symm
  rw [hsum]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Fintype.card_eq_nat_card]

theorem burnsideF4nC_card_ext_two {a l y : c.Γ} (hal : c.graph.Adj a l) (hly : c.graph.Adj l y)
    (hay : a ≠ y) : Nat.card ↥(burnsideF4nC_ext c a l y 2) = 1 := by
  let r : GPath c.graph 2 := ((GPath.triv a).snoc l hal).snoc y hly
  have hr0 : r 0 = a := rfl
  have hr1 : r 1 = l := rfl
  have hr2 : r 2 = y := GPath.snoc_last _ _ _
  have hrmem : r ∈ burnsideF4nC_ext c a l y 2 := by
    refine ⟨⟨hr0, fun i hi heq => ?_⟩, hr1, hr2⟩
    have hi0 : i = 0 := by omega
    subst hi0
    rw [hr0, hr2] at heq
    exact hay heq
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨r, hrmem⟩, fun p => Subtype.ext (GPath.ext' fun i hi => ?_)⟩
  obtain ⟨⟨h0, -⟩, h1, h2⟩ := p.2
  interval_cases i
  · exact h0.trans hr0.symm
  · exact h1.trans hr1.symm
  · exact h2.trans hr2.symm

theorem burnsideF4nC_card_ext (hc : c.IsFaithful) (hq1 : α.qOne = 4) (hq2 : α.qTwo = 2) {y : c.Γ}
    (hy : y ∈ CosetGeom.nbrs c.lv) (hyx : y ≠ c.xv) :
    Nat.card ↥(burnsideF4nC_ext c c.xv c.lv y 8) = 2 ^ 9 := by
  have hv : CosetGeom.vtype c.xv = false := rfl
  have q0 : α.qv false = 4 := hq1
  have q1 : α.qv true = 2 := hq2
  have h2 := burnsideF4nC_card_ext_two (c := c) (CosetGeom.adj_γ₀_γ₁ : c.graph.Adj c.xv c.lv) hy
    (Ne.symm hyx)
  rw [burnsideF4nC_card_ext_succ hc _ _ _ (by norm_num : 2 ≤ 7),
    burnsideF4nC_card_ext_succ hc _ _ _ (by norm_num : 2 ≤ 6),
    burnsideF4nC_card_ext_succ hc _ _ _ (by norm_num : 2 ≤ 5),
    burnsideF4nC_card_ext_succ hc _ _ _ (by norm_num : 2 ≤ 4),
    burnsideF4nC_card_ext_succ hc _ _ _ (by norm_num : 2 ≤ 3),
    burnsideF4nC_card_ext_succ hc _ _ _ (by norm_num : 2 ≤ 2), h2, hv]
  norm_num [q0, q1]

end Ext

section Apartments

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite Y] {c : α.Completion Y}

theorem burnsideF4nC_eq_end_of_mem {m : ℕ} {a b : c.Γ} {p q : GPath c.graph m}
    (hp : p ∈ c.geods m a b) (hq : q ∈ c.geods m a b) {v : c.Γ} (hv : v ∈ p.verts ∪ q.verts)
    (hd : c.graph.dist a v = m) : v = b := by
  have hΓ := connected_graph c
  rcases hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · have h1 := GPath.dist_prefix hΓ p hp.2.2 hi
    rw [hp.1] at h1
    rw [h1] at hd
    subst hd
    exact hp.2.1
  · have h1 := GPath.dist_prefix hΓ q hq.2.2 hi
    rw [hq.1] at h1
    rw [h1] at hd
    subst hd
    exact hq.2.1

theorem burnsideF4nC_ncard_Bset (F : c.Facts46 GLKind.Tits.m) (hs : c.IsSmall GLKind.Tits.m)
    {cc y : c.Γ} (hcc : cc ∈ CosetGeom.nbrs c.xv) (hccl : cc ≠ c.lv)
    (hy : y ∈ CosetGeom.nbrs c.lv) (hyx : y ≠ c.xv) (y' : c.Γ) :
    (Bset c GLKind.Tits cc y y').ncard = (burnsideF4nC_ext c c.xv c.lv y GLKind.Tits.m).ncard := by
  have hm := F.hm
  have hU := F.uniqueGeod
  have hq : ∀ p ∈ burnsideF4nC_ext c c.xv c.lv y GLKind.Tits.m,
      ∃! t : GPath c.graph GLKind.Tits.m, t ∈ c.geods GLKind.Tits.m c.xv (p GLKind.Tits.m) ∧
        t 1 = cc := fun p hp =>
    F.lemma_F414_2 hs (F.dist_m c.xv p hp.1) hcc
  symm
  refine Set.ncard_congr (fun p hp => Set.range (GPath.cycSeq p (hq p hp).choose)) ?_ ?_ ?_
  ·
    intro p hp
    obtain ⟨⟨ht, ht1⟩, -⟩ := (hq p hp).choose_spec
    have hpg := F.mem_geods hp.1
    have hne : p ≠ (hq p hp).choose := fun h => hccl (by rw [← ht1, ← h, hp.2.1])
    obtain ⟨hS, -, -⟩ := (F.lemma_F414_1 (F.dist_m c.xv p hp.1) _).2
      ⟨p, (hq p hp).choose, hpg, ht, hne, rfl⟩
    refine ⟨hS, ?_⟩
    rw [if_pos rfl, GPath.range_cycSeq (by omega) (hpg.1.trans ht.1.symm)
      (hpg.2.1.trans ht.2.1.symm)]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with h | h | h | h
    · rw [h]
      exact Or.inr ⟨1, by decide, ht1⟩
    · rw [h]
      exact Or.inl ⟨0, Nat.zero_le _, hp.1.1⟩
    · rw [h]
      exact Or.inl ⟨1, by decide, hp.2.1⟩
    · rw [h]
      exact Or.inl ⟨2, by decide, hp.2.2⟩
  ·
    intro p p' hp hp' heq
    obtain ⟨⟨ht, -⟩, -⟩ := (hq p hp).choose_spec
    obtain ⟨⟨ht', -⟩, -⟩ := (hq p' hp').choose_spec
    have hpg := F.mem_geods hp.1
    have hpg' := F.mem_geods hp'.1
    rw [GPath.range_cycSeq (by omega) (hpg.1.trans ht.1.symm) (hpg.2.1.trans ht.2.1.symm),
      GPath.range_cycSeq (by omega) (hpg'.1.trans ht'.1.symm) (hpg'.2.1.trans ht'.2.1.symm)] at heq
    have hmem : p' GLKind.Tits.m ∈ p.verts ∪ (hq p hp).choose.verts := by
      rw [heq]
      exact Or.inl (GPath.mem_verts le_rfl)
    have hend := burnsideF4nC_eq_end_of_mem hpg ht hmem (F.dist_m c.xv p' hp'.1)
    have hpg'' : p' ∈ c.geods GLKind.Tits.m c.xv (p GLKind.Tits.m) := by
      rw [← hend]
      exact hpg'
    obtain ⟨u, -, hu⟩ := F.lemma_F414_2 hs (F.dist_m c.xv p hp.1)
      (CosetGeom.adj_γ₀_γ₁ : c.graph.Adj c.xv c.lv)
    exact (hu p ⟨hpg, hp.2.1⟩).trans (hu p' ⟨hpg'', hp'.2.1⟩).symm
  ·
    intro S hS
    obtain ⟨hSap, hsub⟩ := hS
    rw [if_pos rfl] at hsub
    have hccS : cc ∈ S := hsub (by simp)
    have hx : c.xv ∈ S := hsub (by simp)
    have hl : c.lv ∈ S := hsub (by simp)
    have hyS : y ∈ S := hsub (by simp)
    obtain ⟨z, hz, hnb, hper, rfl, hz0, hz1⟩ :=
      burnsideF4k_asm_label hm hU hSap hx hl CosetGeom.adj_γ₀_γ₁
    have hz16 : z 16 = z 0 := hper 0
    have hc15 : cc = z 15 := by
      rcases burnsideF4k_polyNbr c _ hm hU z hz hnb hper 0 cc hccS (by rw [hz0]; exact hcc) with
        h | h
      · exact absurd (h.trans hz1) hccl
      · exact h
    have hy2 : y = z 2 := by
      rcases burnsideF4k_polyNbr c _ hm hU z hz hnb hper 1 y hyS (by rw [hz1]; exact hy) with
        h | h
      · exact h
      · have h' : y = z 16 := h
        exact absurd (h'.trans (hz16.trans hz0)) hyx
    obtain ⟨hA1, hA2, -, hrange⟩ := burnsideF4k_polyArcs c _ hm hU z hz hnb hper 0
    have hp : GPath.arc₁ z hz GLKind.Tits.m 0 ∈ burnsideF4nC_ext c c.xv c.lv y GLKind.Tits.m := by
      refine ⟨⟨by rw [GPath.arc₁_zero, hz0], GPath.arc₁_noBack z hz hnb _ 0⟩, ?_, ?_⟩
      · rw [GPath.arc₁_one z hz _ (by omega), zero_add, hz1]
      · rw [GPath.arc₁, GPath.seqPath_apply _ _ _ _ (by decide), zero_add, hy2]
    refine ⟨GPath.arc₁ z hz GLKind.Tits.m 0, hp, ?_⟩
    obtain ⟨⟨ht, ht1⟩, hu⟩ := (hq _ hp).choose_spec
    have hA2' : GPath.arc₂ z hz GLKind.Tits.m 0 ∈
        c.geods GLKind.Tits.m c.xv (GPath.arc₁ z hz GLKind.Tits.m 0 GLKind.Tits.m) := by
      rw [GPath.arc₁_last, ← hz0]
      exact hA2
    have heq2 : (hq _ hp).choose = GPath.arc₂ z hz GLKind.Tits.m 0 :=
      (hu _ ⟨hA2', by rw [GPath.arc₂_one z hz _ (by omega), hc15]; rfl⟩).symm
    rw [heq2, GPath.range_cycSeq (by omega) (by rw [hA1.1, hA2.1]) (by rw [hA1.2.1, hA2.2.1]),
      hrange]

end Apartments

section Count


theorem burnsideF4nC_ncard_Pset (h45 : F_4_5) (h46 : F_4_6) {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 GLKind.Tits p f Gp M₁ M₂) (hGp : Gp = ⊤) {Y : Type}
    [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall GLKind.Tits.m) {cc y y' : β.Γ}
    (hcc : cc ∈ CosetGeom.nbrs β.xv) (hccl : cc ≠ β.lv) (hy : y ∈ CosetGeom.nbrs β.lv)
    (hyx : y ≠ β.xv) (hy' : y' ∈ CosetGeom.nbrs cc) (hy'x : y' ≠ β.xv) :
    (Pset β GLKind.Tits cc y y').ncard = 2 ^ 9 := by
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have F := burnsideF4n_facts46_at h46 hyp β hβ
  haveI : Finite Y := burnsideF4b_finite_of_small F hs
  have hbij := burnside_as_F_4_19_of h45 h46 GLKind.Tits p f E Gp M₁ M₂ hyp hGp (Or.inr rfl) Y β
    hβ hs cc hcc hccl y hy hyx y' hy' hy'x
  obtain ⟨hq1, hq2⟩ := burnsideF45_q_Tits hyp hGp
  rw [← hbij.injOn.ncard_image, hbij.image_eq,
    burnsideF4nC_ncard_Bset F hs hcc hccl hy hyx y', ← Nat.card_coe_set_eq]
  exact burnsideF4nC_card_ext hβ hq1 hq2 hy hyx

end Count

end CFSG.ASVolI
