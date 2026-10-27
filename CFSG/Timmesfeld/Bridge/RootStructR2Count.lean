module

public import CFSG.Timmesfeld.Bridge.RootStructR2Incidence
public import CFSG.Timmesfeld.Bridge.RootStructR2Orbit

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem ncard_biUnion_eq_mul {ι α : Type*} [Finite α] {t : Set ι} (ht : t.Finite)
    {s : ι → Set α} (hd : t.PairwiseDisjoint s) {m : ℕ} (hm : ∀ i ∈ t, (s i).ncard = m) :
    (⋃ i ∈ t, s i).ncard = t.ncard * m := by
  rw [ht.ncard_biUnion (fun _ _ => Set.toFinite _) hd, finsum_mem_congr rfl hm,
    finsum_mem_eq_finite_toFinset_sum _ ht, Finset.sum_const, smul_eq_mul,
    ← Set.ncard_eq_toFinset_card t ht]

@[expose] def pointLines (D : Set G) (C : Subgroup G) : Set (Subgroup G) :=
  {L | ∃ c ∈ D, C = rootGroup D c ∧ L ∈ rootLines D c}

@[expose] def offPoints (D : Set G) (E L : Subgroup G) : Set (Subgroup G) :=
  ⋃ L' ∈ pointLines D E \ {L}, linePoints D L' \ {E}

@[expose] def pathPoints (D : Set G) (C T : Subgroup G) : Set (Subgroup G) :=
  ⋃ E ∈ offPoints D C T, offPoints D E (C ⊔ E)

section Lines

variable (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
include h hc hs

theorem pointLines_eq {c : G} (hcD : c ∈ D) : pointLines D (rootGroup D c) = rootLines D c := by
  have := h.finite
  ext L
  constructor
  · rintro ⟨c', hc', hcc', hL⟩
    have hc'T : c' ∈ rootSet D c := mem_rootSet_of_mem_rootGroup_of_ne_one h.root hc hcD
      (hcc' ▸ rootSet_subset_rootGroup D c' (mem_rootSet_self hc')) (h.root.ne_one hc')
    rwa [rootLines_eq_of_mem_rootSet h hc hs hcD hc'T] at hL
  · exact fun hL => ⟨c, hcD, rfl, hL⟩

theorem collinear_of_mem_rootLines {u v : G} {L : Subgroup G} (hu : u ∈ D) (hv : v ∈ D)
    (hL : L ∈ rootLines D u) (hvL : v ∈ L) (hvu : rootGroup D v ≠ rootGroup D u) :
    Commute u v ∧ u * v ∈ D ∧ v ∉ rootSet D u ∧ rootGroup D u ⊔ rootGroup D v = L := by
  have hD := h.root
  obtain ⟨b, hb, hub, hubD, hbT, rfl⟩ := hL
  have hvT : v ∉ rootSet D u := fun h' => hvu (rootGroup_eq_of_mem h')
  refine ⟨commute_of_mem_sup_rootGroup hu hb hub (left_mem_line hu) hvL,
    mem_of_mem_sup_rootGroup h hc hs hu hb hub hubD hbT (Subgroup.mul_mem _ (left_mem_line hu)
      hvL) fun h1 => hvT ?_, hvT, sup_rootGroup_eq_of_mem h hc hs hu hb hub hubD hbT
      (left_mem_line hu) hvL (hD.ne_one hu) (hD.ne_one hv) hvT⟩
  rw [show v = u⁻¹ from eq_inv_of_mul_eq_one_right h1, hD.inv_eq hu]
  exact mem_rootSet_self hu

theorem mem_offPoints_iff {e : G} (heD : e ∈ D) {L : Subgroup G} (hL : L ∈ rootLines D e)
    {B : Subgroup G} : B ∈ offPoints D (rootGroup D e) L ↔
      ∃ x ∈ D, B = rootGroup D x ∧ Commute e x ∧ e * x ∈ D ∧ x ∉ rootSet D e ∧ x ∉ L := by
  have hD := h.root
  constructor
  · intro hB
    simp only [offPoints, Set.mem_iUnion, exists_prop] at hB
    obtain ⟨L', ⟨hL', hL'L⟩, ⟨x, hx, hxL', rfl⟩, hxe⟩ := hB
    rw [pointLines_eq h hc hs heD] at hL'
    rw [Set.mem_singleton_iff] at hL'L hxe
    obtain ⟨hex, hexD, hxT, -⟩ := collinear_of_mem_rootLines h hc hs heD hx hL' hxL' hxe
    refine ⟨x, hx, rfl, hex, hexD, hxT, fun hxL => hxe ?_⟩
    exact eq_of_mem_linePoints_of_mem_linePoints h hc hs heD hL' hL hL'L ⟨x, hx, hxL', rfl⟩
      ⟨x, hx, hxL, rfl⟩
  · rintro ⟨x, hx, rfl, hex, hexD, hxT, hxL⟩
    simp only [offPoints, Set.mem_iUnion, exists_prop]
    refine ⟨rootGroup D e ⊔ rootGroup D x, ⟨?_, ?_⟩, ⟨x, hx, right_mem_line hx, rfl⟩, ?_⟩
    · rw [pointLines_eq h hc hs heD]
      exact ⟨x, hx, hex, hexD, hxT, rfl⟩
    · rw [Set.mem_singleton_iff]
      rintro rfl
      exact hxL (right_mem_line hx)
    · rw [Set.mem_singleton_iff]
      intro hxe
      exact hxT (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc heD
        (hxe ▸ rootSet_subset_rootGroup D x (mem_rootSet_self hx)) (hD.ne_one hx))

end Lines

theorem LineSetting.ncard_offPoints (hL : LineSetting G D) {Q : ℕ}
    (hQ : ∀ c ∈ D, (rootLines D c).ncard = Q + 1) {e : G} (heD : e ∈ D) {L : Subgroup G}
    (hLe : L ∈ rootLines D e) :
    (offPoints D (rootGroup D e) L).ncard = Q * Nat.card (rootGroup D e) := by
  have := hL.hyp.finite
  have h := hL.hyp
  have hc := hL.closure
  have hs := hL.special
  rw [offPoints, pointLines_eq h hc hs heD]
  have hdisj : (rootLines D e \ {L}).PairwiseDisjoint
      (fun L' => linePoints D L' \ {rootGroup D e}) := by
    intro L₁ hL₁ L₂ hL₂ hne
    refine Set.disjoint_left.2 fun P hP₁ hP₂ => hP₁.2 ?_
    rw [Set.mem_singleton_iff]
    exact eq_of_mem_linePoints_of_mem_linePoints h hc hs heD hL₁.1 hL₂.1 hne hP₁.1 hP₂.1
  have hpiece : ∀ L' ∈ rootLines D e \ {L},
      (linePoints D L' \ {rootGroup D e}).ncard = Nat.card (rootGroup D e) := by
    intro L' hL'
    obtain ⟨b, hb, heb, hebD, hbT, rfl⟩ := hL'.1
    exact ncard_linePoints_diff h hc hs heD hb heb hebD hbT
  have hcnt : (rootLines D e \ {L}).ncard = Q := by
    rw [Set.ncard_sdiff_singleton_of_mem hLe, hQ e heD, Nat.add_sub_cancel]
  rw [ncard_biUnion_eq_mul (α := Subgroup G) (Set.toFinite _) hdisj hpiece, hcnt]

section Paths

variable (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
include h hc hs

theorem mem_pathPoints_iff {c : G} (hcD : c ∈ D) {T : Subgroup G} (hTc : T ∈ rootLines D c)
    {B : Subgroup G} : B ∈ pathPoints D (rootGroup D c) T ↔
      ∃ e ∈ D, ∃ x ∈ D, B = rootGroup D x ∧ Commute c e ∧ c * e ∈ D ∧ e ∉ rootSet D c ∧ e ∉ T ∧
        Commute e x ∧ e * x ∈ D ∧ x ∉ rootSet D e ∧ x ∉ rootGroup D c ⊔ rootGroup D e := by
  have hline : ∀ {e : G}, e ∈ D → Commute c e → c * e ∈ D → e ∉ rootSet D c →
      rootGroup D c ⊔ rootGroup D e ∈ rootLines D e := fun he hce hceD heT =>
    mem_rootLines_of_mem h hc hs hcD he hce hceD heT he (right_mem_line he)
  constructor
  · intro hB
    simp only [pathPoints, Set.mem_iUnion, exists_prop] at hB
    obtain ⟨E, hE, hBE⟩ := hB
    obtain ⟨e, he, rfl, hce, hceD, heT, heT'⟩ := (mem_offPoints_iff h hc hs hcD hTc).1 hE
    obtain ⟨x, hx, rfl, hex, hexD, hxT, hxL⟩ :=
      (mem_offPoints_iff h hc hs he (hline he hce hceD heT)).1 hBE
    exact ⟨e, he, x, hx, rfl, hce, hceD, heT, heT', hex, hexD, hxT, hxL⟩
  · rintro ⟨e, he, x, hx, rfl, hce, hceD, heT, heT', hex, hexD, hxT, hxL⟩
    simp only [pathPoints, Set.mem_iUnion, exists_prop]
    exact ⟨rootGroup D e, (mem_offPoints_iff h hc hs hcD hTc).2 ⟨e, he, rfl, hce, hceD, heT, heT'⟩,
      (mem_offPoints_iff h hc hs he (hline he hce hceD heT)).2 ⟨x, hx, rfl, hex, hexD, hxT, hxL⟩⟩

theorem orderOf_mul_eq_four_of_path (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    {c e x : G} (hcD : c ∈ D) (he : e ∈ D) (hx : x ∈ D) (hce : Commute c e) (hceD : c * e ∈ D)
    (heT : e ∉ rootSet D c) (hex : Commute e x) (hexD : e * x ∈ D)
    (hxL : x ∉ rootGroup D c ⊔ rootGroup D e) : orderOf (c * x) = 4 := by
  have hD := h.root
  have hcx : ¬ Commute c x := fun hcx => hxL (mem_sup_of_commute_of_lineTI h hc hs hconn hcD he
    hce hceD heT (hAll c hcD e he hce hceD heT) hx hcx.symm hex.symm)
  have hxeD : x * e ∈ D := by rw [← hex.eq]; exact hexD
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hcD hx with h' | h' | ⟨hodd, -⟩
  · exact absurd h' hcx
  · exact h'
  · exact absurd hce (not_commute_of_collinear hD hcD he hcx hodd hex.symm hxeD)

end Paths

theorem LineSetting.ncard_pathPoints (hL : LineSetting G D) (hAll : AllLinesTI D) {Q : ℕ}
    (hQ : ∀ c ∈ D, (rootLines D c).ncard = Q + 1) {c : G} (hcD : c ∈ D) {T : Subgroup G}
    (hTc : T ∈ rootLines D c) :
    (pathPoints D (rootGroup D c) T).ncard =
      Q * Nat.card (rootGroup D c) * (Q * Nat.card (rootGroup D c)) := by
  have := hL.hyp.finite
  have h := hL.hyp
  have hc := hL.closure
  have hs := hL.special
  have hD := h.root
  have hclass := h.isClass
  have hdisj : (offPoints D (rootGroup D c) T).PairwiseDisjoint
      (fun E => offPoints D E (rootGroup D c ⊔ E)) := by
    intro E₁ hE₁ E₂ hE₂ hne
    obtain ⟨e₁, he₁, rfl, hce₁, hce₁D, he₁T, -⟩ := (mem_offPoints_iff h hc hs hcD hTc).1 hE₁
    obtain ⟨e₂, he₂, rfl, hce₂, hce₂D, he₂T, -⟩ := (mem_offPoints_iff h hc hs hcD hTc).1 hE₂
    refine Set.disjoint_left.2 fun B hB₁ hB₂ => hne ?_
    have hline : ∀ {e : G}, e ∈ D → Commute c e → c * e ∈ D → e ∉ rootSet D c →
        rootGroup D c ⊔ rootGroup D e ∈ rootLines D e := fun he hce hceD heT =>
      mem_rootLines_of_mem h hc hs hcD he hce hceD heT he (right_mem_line he)
    obtain ⟨x, hx, rfl, he₁x, he₁xD, hxT₁, hxL₁⟩ :=
      (mem_offPoints_iff h hc hs he₁ (hline he₁ hce₁ hce₁D he₁T)).1 hB₁
    obtain ⟨x', hx', hxx', he₂x', -, -, -⟩ :=
      (mem_offPoints_iff h hc hs he₂ (hline he₂ hce₂ hce₂D he₂T)).1 hB₂
    have hx'T : x' ∈ rootSet D x := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx
      (hxx' ▸ rootSet_subset_rootGroup D x' (mem_rootSet_self hx')) (hD.ne_one hx')
    have he₂x : Commute e₂ x := ((hx'T.2 e₂ he₂).1 he₂x'.symm).symm
    have h4 := orderOf_mul_eq_four_of_path h hc hs hL.conn hAll hcD he₁ hx hce₁ hce₁D he₁T he₁x
      he₁xD hxL₁
    have hT₁ := mem_rootSet_sq_of_lineTI h hc hs hcD hx he₁ h4 hce₁ hce₁D he₁x.symm
      (hAll c hcD e₁ he₁ hce₁ hce₁D he₁T)
    have hT₂ := mem_rootSet_sq_of_lineTI h hc hs hcD hx he₂ h4 hce₂ hce₂D he₂x.symm
      (hAll c hcD e₂ he₂ hce₂ hce₂D he₂T)
    rw [← rootSet_eq_of_mem hT₁] at hT₂
    exact (rootGroup_eq_of_mem hT₂).symm
  have hpiece : ∀ E ∈ offPoints D (rootGroup D c) T,
      (offPoints D E (rootGroup D c ⊔ E)).ncard = Q * Nat.card (rootGroup D c) := by
    intro E hE
    obtain ⟨e, he, rfl, hce, hceD, heT, -⟩ := (mem_offPoints_iff h hc hs hcD hTc).1 hE
    rw [hL.ncard_offPoints hQ he (mem_rootLines_of_mem h hc hs hcD he hce hceD heT he
      (right_mem_line he)), card_rootGroup_eq hclass he hcD]
  rw [pathPoints, ncard_biUnion_eq_mul (α := Subgroup G) (Set.toFinite _) hdisj hpiece,
    hL.ncard_offPoints hQ hcD hTc]

theorem gatedPoints_eq_biUnion (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) {a : G} (ha : a ∈ D)
    {T : Subgroup G} (hT : T ∈ rootLines D a) :
    gatedPoints D a T = ⋃ C ∈ linePoints D T \ {rootGroup D a}, pathPoints D C T := by
  have := h.finite
  have hD := h.root
  ext B
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hB, x, hx, rfl, c, hcD, hcT, h4⟩
    obtain ⟨x₀, hx₀, hxx₀, hax₀, hoddax₀, -⟩ := hB
    have hx₀T : x₀ ∈ rootSet D x := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx
      (hxx₀ ▸ rootSet_subset_rootGroup D x₀ (mem_rootSet_self hx₀)) (hD.ne_one hx₀)
    have hopp := opposite_of_mem_rootSet_of_opposite hD ha hx₀ (mem_rootSet_self ha)
      (mem_rootSet_comm hx hx₀T) ⟨hax₀, hoddax₀⟩
    have hca : rootGroup D c ≠ rootGroup D a := by
      intro hca
      have hcT : c ∈ rootSet D a := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc ha
        (hca ▸ rootSet_subset_rootGroup D c (mem_rootSet_self hcD)) (hD.ne_one hcD)
      have h4a : orderOf (x * a) = 4 := by
        rw [orderOf_mul_comm_eq] at h4 ⊢
        exact (orderOf_mul_eq_four_iff_of_mem_rootSet hD ha hcT hx).1 h4
      rw [orderOf_mul_comm_eq, h4a] at hopp
      exact absurd hopp.2 (by decide)
    obtain ⟨hac, hacD, hcTa, hTeq⟩ := collinear_of_mem_rootLines h hc hs ha hcD hT hcT hca
    have hG := GateConfig.of h hc hs hconn hAll ha hx hcD hac hacD hopp.1 hopp.2 h4
    have hTc := mem_rootLines_of_mem_rootLines h hc hs ha hT hcD hcT
    have hxc : ¬ Commute x c := not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hx)
      (hD.mul_self_eq_one hcD) h4
    refine ⟨rootGroup D c, ⟨⟨c, hcD, hcT, rfl⟩, hca⟩, (mem_pathPoints_iff h hc hs hcD hTc).2
      ⟨_, hG.heD, x, hx, rfl, hG.hce, hG.hceD, fun h' => hG.hcTe (mem_rootSet_comm hcD h'),
        fun h' => hG.heL (hTeq ▸ h'), hG.hxe.symm, ?_, ?_, ?_⟩⟩
    · rw [← hG.hxe.eq]; exact hG.hxeD
    · intro hxT
      exact hxc ((hxT.2 c hcD).2 hG.hce.symm)
    · intro hxL
      exact hxc (commute_of_mem_sup_rootGroup hcD hG.heD hG.hce hxL (left_mem_line hcD))
  · rintro ⟨C, ⟨⟨c, hcD, hcT, rfl⟩, hca⟩, hB⟩
    have hTc := mem_rootLines_of_mem_rootLines h hc hs ha hT hcD hcT
    obtain ⟨e, he, x, hx, rfl, hce, hceD, heT, heT', hex, hexD, hxT, hxL⟩ :=
      (mem_pathPoints_iff h hc hs hcD hTc).1 hB
    refine mem_gatedPoints_of_path h hc hs hconn hAll ha hcD he hx hT hcT hca
      (L₂ := rootGroup D c ⊔ rootGroup D e) ⟨e, he, hce, hceD, heT, rfl⟩ ?_ (right_mem_line he) ?_
      (L₃ := rootGroup D e ⊔ rootGroup D x) ⟨x, hx, hex, hexD, hxT, rfl⟩ ?_ (right_mem_line hx) ?_
    · rw [Set.mem_singleton_iff]
      rintro hL₂
      exact heT' (hL₂ ▸ right_mem_line he)
    · rw [Set.mem_singleton_iff]
      exact fun h' => heT (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hcD
        (h' ▸ rootSet_subset_rootGroup D e (mem_rootSet_self he)) (hD.ne_one he))
    · rw [Set.mem_singleton_iff]
      rintro hL₃
      exact hxL (hL₃ ▸ right_mem_line hx)
    · rw [Set.mem_singleton_iff]
      exact fun h' => hxT (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc he
        (h' ▸ rootSet_subset_rootGroup D x (mem_rootSet_self hx)) (hD.ne_one hx))

theorem LineSetting.ncard_gatedPoints (hL : LineSetting G D) (hAll : AllLinesTI D) {Q : ℕ}
    (hQ : ∀ c ∈ D, (rootLines D c).ncard = Q + 1) {a : G} (ha : a ∈ D) {T : Subgroup G}
    (hT : T ∈ rootLines D a) :
    (gatedPoints D a T).ncard = Nat.card (rootGroup D a) *
      (Q * Nat.card (rootGroup D a) * (Q * Nat.card (rootGroup D a))) := by
  have := hL.hyp.finite
  have h := hL.hyp
  have hc := hL.closure
  have hs := hL.special
  have hD := h.root
  have hclass := h.isClass
  obtain ⟨b, hb, hab, habD, hbT, rfl⟩ := hT
  set T := rootGroup D a ⊔ rootGroup D b with hTdef
  have hT : T ∈ rootLines D a := ⟨b, hb, hab, habD, hbT, rfl⟩
  have hdisj : (linePoints D T \ {rootGroup D a}).PairwiseDisjoint
      (fun C => pathPoints D C T) := by
    rintro _ ⟨⟨c₁, hc₁, hc₁T, rfl⟩, hc₁a⟩ _ ⟨⟨c₂, hc₂, hc₂T, rfl⟩, hc₂a⟩ hne
    refine Set.disjoint_left.2 fun B hB₁ hB₂ => hne ?_
    have hTc₁ := mem_rootLines_of_mem_rootLines h hc hs ha hT hc₁ hc₁T
    have hTc₂ := mem_rootLines_of_mem_rootLines h hc hs ha hT hc₂ hc₂T
    obtain ⟨e₁, he₁, x, hx, rfl, hce₁, hce₁D, he₁T, -, he₁x, he₁xD, -, hxL₁⟩ :=
      (mem_pathPoints_iff h hc hs hc₁ hTc₁).1 hB₁
    obtain ⟨e₂, he₂, x', hx', hxx', hce₂, hce₂D, he₂T, -, he₂x', he₂x'D, -, hx'L₂⟩ :=
      (mem_pathPoints_iff h hc hs hc₂ hTc₂).1 hB₂
    have h4₁ := orderOf_mul_eq_four_of_path h hc hs hL.conn hAll hc₁ he₁ hx hce₁ hce₁D he₁T he₁x
      he₁xD hxL₁
    have h4₂ := orderOf_mul_eq_four_of_path h hc hs hL.conn hAll hc₂ he₂ hx' hce₂ hce₂D he₂T he₂x'
      he₂x'D hx'L₂
    have hx'T : x' ∈ rootSet D x := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx
      (hxx' ▸ rootSet_subset_rootGroup D x' (mem_rootSet_self hx')) (hD.ne_one hx')
    have hB₁' : rootGroup D x ∈ gatedPoints D a T := by
      rw [gatedPoints_eq_biUnion h hc hs hL.conn hAll ha hT]
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨_, ⟨⟨c₁, hc₁, hc₁T, rfl⟩, hc₁a⟩, hB₁⟩
    obtain ⟨⟨x₀, hx₀, hxx₀, hax₀, hoddax₀, -⟩, -⟩ := hB₁'
    have hx₀T : x₀ ∈ rootSet D x := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx
      (hxx₀ ▸ rootSet_subset_rootGroup D x₀ (mem_rootSet_self hx₀)) (hD.ne_one hx₀)
    have hopp := opposite_of_mem_rootSet_of_opposite hD ha hx₀ (mem_rootSet_self ha)
      (mem_rootSet_comm hx hx₀T) ⟨hax₀, hoddax₀⟩
    have h4₁' : orderOf (x * c₁) = 4 := by rw [orderOf_mul_comm_eq]; exact h4₁
    have h4₂' : orderOf (x * c₂) = 4 :=
      (orderOf_mul_eq_four_iff_of_mem_rootSet hD hx hx'T hc₂).1 (by
        rw [orderOf_mul_comm_eq]; exact h4₂)
    have hoddax : Odd (orderOf (a * x)) := hopp.2
    have hgate := mem_rootSet_of_special_of_special h hc hs hL.conn hAll ha hb hab habD hbT hx ha
      (left_mem_line ha) hopp.1 hoddax hc₁ hc₁T hc₂ hc₂T h4₁' h4₂'
    exact (rootGroup_eq_of_mem hgate).symm
  have hpiece : ∀ C ∈ linePoints D T \ {rootGroup D a}, (pathPoints D C T).ncard =
      Q * Nat.card (rootGroup D a) * (Q * Nat.card (rootGroup D a)) := by
    rintro _ ⟨⟨c, hcD, hcT, rfl⟩, -⟩
    rw [hL.ncard_pathPoints hAll hQ hcD (mem_rootLines_of_mem_rootLines h hc hs ha hT hcD hcT),
      card_rootGroup_eq hclass hcD ha]
  rw [gatedPoints_eq_biUnion h hc hs hL.conn hAll ha hT,
    ncard_biUnion_eq_mul (α := Subgroup G) (Set.toFinite _) hdisj hpiece,
    ncard_linePoints_diff h hc hs ha hb hab habD hbT]

theorem LineSetting.ncard_oneOmega_mul (hL : LineSetting G D) (hAll : AllLinesTI D) {Q k : ℕ}
    (hQ : ∀ c ∈ D, (rootLines D c).ncard = Q + 1) {a : G} (ha : a ∈ D)
    (hk : ∀ x ∈ D, ¬ Commute a x → Odd (orderOf (a * x)) → OneOpposite D a x →
      (gatedLines D a x).ncard = k) :
    (oneOmega D a).ncard * k = (Q + 1) * (Nat.card (rootGroup D a) *
      (Q * Nat.card (rootGroup D a) * (Q * Nat.card (rootGroup D a)))) := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hc := hL.closure
  set N := Nat.card (rootGroup D a) * (Q * Nat.card (rootGroup D a) *
    (Q * Nat.card (rootGroup D a))) with hN
  set P : Set (Subgroup G × Subgroup G) := ⋃ T ∈ rootLines D a, gatedPoints D a T ×ˢ {T}
    with hP
  have h1 : P.ncard = (Q + 1) * N := by
    rw [hP, ncard_biUnion_eq_mul (α := Subgroup G × Subgroup G) (Set.toFinite _) ?_ ?_, hQ a ha]
    · intro T₁ _ T₂ _ hne
      refine Set.disjoint_left.2 fun p hp₁ hp₂ => hne ?_
      exact (Set.mem_singleton_iff.1 (Set.mem_prod.1 hp₁).2).symm.trans
        (Set.mem_singleton_iff.1 (Set.mem_prod.1 hp₂).2)
    · intro T hT
      rw [Set.ncard_prod, Set.ncard_singleton, mul_one, hN]
      exact hL.ncard_gatedPoints hAll hQ ha hT
  have hfib : ∀ B ∈ oneOmega D a,
      ({T | T ∈ rootLines D a ∧ B ∈ gatedPoints D a T}).ncard = k := by
    rintro B ⟨x, hx, rfl, hax, hoddax, hx1⟩
    rw [← hk x hx hax hoddax hx1]
    congr 1
    ext T
    constructor
    · rintro ⟨hT, -, x', hx', hxx', p, hp, hpT, h4⟩
      have hx'T : x' ∈ rootSet D x := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hx
        (hxx' ▸ rootSet_subset_rootGroup D x' (mem_rootSet_self hx')) (hD.ne_one hx')
      exact ⟨hT, p, hp, hpT, (orderOf_mul_eq_four_iff_of_mem_rootSet hD hx hx'T hp).1 h4⟩
    · rintro ⟨hT, p, hp, hpT, h4⟩
      exact ⟨hT, ⟨x, hx, rfl, hax, hoddax, hx1⟩, x, hx, rfl, p, hp, hpT, h4⟩
  have hPeq : P = ⋃ B ∈ oneOmega D a,
      ({B} : Set (Subgroup G)) ×ˢ {T | T ∈ rootLines D a ∧ B ∈ gatedPoints D a T} := by
    ext ⟨B, T⟩
    simp only [hP, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      exists_prop]
    constructor
    · rintro ⟨T', hT', hB, rfl⟩
      exact ⟨B, hB.1, rfl, hT', hB⟩
    · rintro ⟨B', hB', rfl, hT, hB⟩
      exact ⟨T, hT, hB, rfl⟩
  have h2 : P.ncard = (oneOmega D a).ncard * k := by
    rw [hPeq, ncard_biUnion_eq_mul (α := Subgroup G × Subgroup G) (Set.toFinite _) ?_ ?_]
    · intro B₁ _ B₂ _ hne
      refine Set.disjoint_left.2 fun p hp₁ hp₂ => hne ?_
      exact (Set.mem_singleton_iff.1 (Set.mem_prod.1 hp₁).1).symm.trans
        (Set.mem_singleton_iff.1 (Set.mem_prod.1 hp₂).1)
    · intro B hB
      rw [Set.ncard_prod, Set.ncard_singleton, one_mul]
      exact hfib B hB
  rw [← h2, h1]

theorem gatedLines_eq_of_mem_rootSet (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    {a a' x x' : G} (ha : a ∈ D) (ha' : a' ∈ rootSet D a) (hx : x ∈ D)
    (hx' : x' ∈ rootSet D x) : gatedLines D a' x' = gatedLines D a x := by
  have hD := h.root
  ext L
  change (L ∈ rootLines D a' ∧ _) ↔ (L ∈ rootLines D a ∧ _)
  rw [rootLines_eq_of_mem_rootSet h hc hs ha ha']
  constructor
  · rintro ⟨hL, p, hp, hpL, h4⟩
    exact ⟨hL, p, hp, hpL, (orderOf_mul_eq_four_iff_of_mem_rootSet hD hx hx' hp).1 h4⟩
  · rintro ⟨hL, p, hp, hpL, h4⟩
    exact ⟨hL, p, hp, hpL, (orderOf_mul_eq_four_iff_of_mem_rootSet hD hx hx' hp).2 h4⟩

theorem map_conj_mem_gatedLines (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a x : G}
    {L : Subgroup G} (hL : L ∈ gatedLines D a x) (g : G) :
    L.map (MulAut.conj g).toMonoidHom ∈ gatedLines D (g * a * g⁻¹) (g * x * g⁻¹) := by
  obtain ⟨hL, p, hp, hpL, h4⟩ := hL
  refine ⟨map_conj_mem_rootLines_conj hclass hL g, g * p * g⁻¹, conj_mem_of_isClass hclass g hp,
    ⟨p, hpL, rfl⟩, ?_⟩
  rw [show g * x * g⁻¹ * (g * p * g⁻¹) = g * (x * p) * g⁻¹ by group, orderOf_conj_eq]
  exact h4

theorem ncard_gatedLines_le_conj [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (a x g : G) :
    (gatedLines D a x).ncard ≤ (gatedLines D (g * a * g⁻¹) (g * x * g⁻¹)).ncard := by
  rw [← Set.ncard_image_of_injective _
    (Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)]
  exact Set.ncard_le_ncard (by rintro _ ⟨L, hL, rfl⟩; exact map_conj_mem_gatedLines hclass hL g)

theorem ncard_gatedLines_eq {G : Type} [Group G] {D : Set G} (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    (hReg : RootLinesRegularStep) (h3 : ThreeLines D) {a x a' x' : G} (ha : a ∈ D) (hx : x ∈ D)
    (hax : ¬ Commute a x) (hoddax : Odd (orderOf (a * x))) (hx1 : OneOpposite D a x)
    (ha' : a' ∈ D) (hx' : x' ∈ D) (ha'x' : ¬ Commute a' x') (hodda'x' : Odd (orderOf (a' * x')))
    (hx'1 : OneOpposite D a' x') : (gatedLines D a' x').ncard = (gatedLines D a x).ncard := by
  have := h.finite
  have hclass := h.isClass
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_isClass hclass ha' ha)
  set y := g * x' * g⁻¹ with hy
  have hyD : y ∈ D := conj_mem_of_isClass hclass g hx'
  have hay : ¬ Commute a y := by
    rw [← hg, hy]
    exact fun h' => ha'x' ((Commute.conj_iff g).1 h')
  have hodday : Odd (orderOf (a * y)) := by
    rw [← hg, hy, show g * a' * g⁻¹ * (g * x' * g⁻¹) = g * (a' * x') * g⁻¹ by group,
      orderOf_conj_eq]
    exact hodda'x'
  have hy1 : OneOpposite D a y := by
    obtain ⟨e, he, ha'e, ha'eD, h4⟩ := hx'1
    refine ⟨g * e * g⁻¹, conj_mem_of_isClass hclass g he, ?_, ?_, ?_⟩
    · rw [← hg]; exact (Commute.conj_iff g).2 ha'e
    · rw [← hg, show g * a' * g⁻¹ * (g * e * g⁻¹) = g * (a' * e) * g⁻¹ by group]
      exact conj_mem_of_isClass hclass g ha'eD
    · rw [hy, show g * x' * g⁻¹ * (g * e * g⁻¹) = g * (x' * e) * g⁻¹ by group, orderOf_conj_eq]
      exact h4
  have h1 : (gatedLines D a' x').ncard = (gatedLines D a y).ncard := by
    refine le_antisymm ?_ ?_
    · have := ncard_gatedLines_le_conj hclass a' x' g
      rwa [hg] at this
    · have := ncard_gatedLines_le_conj hclass a y g⁻¹
      have e1 : g⁻¹ * a * g⁻¹⁻¹ = a' := by rw [← hg]; group
      have e2 : g⁻¹ * y * g⁻¹⁻¹ = x' := by rw [hy]; group
      rwa [e1, e2] at this
  have h2 : ∀ {u v : G}, u ∈ D → ¬ Commute a u → Odd (orderOf (a * u)) → OneOpposite D a u →
      v ∈ D → ¬ Commute a v → Odd (orderOf (a * v)) → OneOpposite D a v →
      (gatedLines D a v).ncard ≤ (gatedLines D a u).ncard := by
    intro u v hu hau hoddau hu1 hv hav hoddav hv1
    obtain ⟨k, hka, hkv⟩ := exists_conj_of_oneOpposite h hc hs hconn hAll hReg h3 ha hu hau
      hoddau hu1 hv hav hoddav hv1
    have := ncard_gatedLines_le_conj hclass a v k
    rwa [gatedLines_eq_of_mem_rootSet h hc hs ha hka hu hkv] at this
  rw [h1]
  exact le_antisymm (h2 hx hax hoddax hx1 hyD hay hodday hy1)
    (h2 hyD hay hodday hy1 hx hax hoddax hx1)

end CFSG.Timmesfeld.Bridge
