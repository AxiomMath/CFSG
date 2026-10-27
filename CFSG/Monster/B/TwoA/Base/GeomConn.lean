
module

public import CFSG.Monster.B.TwoA.Base.GeomConnBase

public import CFSG.Monster.B.TwoA.Base.GeomFano
public import CFSG.Monster.B.TwoA.Base.ResGen

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module Relation

open scoped IsMulCommutative

attribute [local instance] parAction

theorem mem_parRes_stdSub
    {J : Set ℕ} (hJ : J ⊆ Set.Icc 1 5) (x : ParGeom) :
    x ∈ parRes (stdSub J) ↔ parType x ∉ J ∧ ∀ s ∈ J,
      (s < parType x → Echain s ≤ x.1.2) ∧ (parType x < s → x.1.2 ≤ Echain s) := by
  change (parType x ∉ parType '' stdSub J ∧ ∀ y ∈ stdSub J, parInc x y) ↔ _
  rw [parType_stdSub _ hJ]
  refine and_congr_right fun hxJ => ⟨fun h s hs => ?_, fun h y hy => ?_⟩
  · obtain ⟨hs1, hs5⟩ := hJ hs
    have hinc := h (stdObj s hs1 hs5) ⟨stdObj_mem s hs1 hs5, hs⟩
    refine ⟨fun hlt => le_of_parInc (parInc_symm hinc) hlt.le, fun hlt => ?_⟩
    exact le_of_parInc hinc hlt.le
  · obtain ⟨hy1, hyJ⟩ := hy
    have hyE : y.1.2 = Echain (parType y) := hy1
    have hne : parType x ≠ parType y := fun e => hxJ (e ▸ hyJ)
    refine (parInc_iff_of_ne hne).2 ?_
    rw [hyE]
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact .inl ((h _ hyJ).2 hlt)
    · exact .inr ((h _ hyJ).1 hlt)

theorem stdObj_mem_parRes
    {J : Set ℕ} (hJ : J ⊆ Set.Icc 1 5) {t : ℕ} (h1 : 1 ≤ t) (h5 : t ≤ 5)
    (ht : t ∉ J) : stdObj t h1 h5 ∈ parRes (stdSub J) := by
  rw [mem_parRes_stdSub hJ]
  refine ⟨ht, fun s hs => ⟨fun hlt => Echain_mono (hJ hs).1 hlt.le h5,
    fun hlt => Echain_mono h1 hlt.le (hJ hs).2⟩⟩

theorem reach_of_separated
    {J : Set ℕ} (hJ : J ⊆ Set.Icc 1 5) {s m₁ m₂ : ℕ} (hs : s ∈ J)
    (h₁ : m₁ < s) (h₂ : s < m₂) (hm₁ : 1 ≤ m₁) (hm₂ : m₂ ≤ 5) (hm₁J : m₁ ∉ J)
    (hm₂J : m₂ ∉ J) (x y : ParGeom) (hx : x ∈ parRes (stdSub J)) (hy : y ∈ parRes (stdSub J)) :
    RReach (parRes (stdSub J)) x y := by
  have hsep : ∀ u v : ParGeom, u ∈ parRes (stdSub J) → v ∈ parRes (stdSub J) →
      ∀ s' ∈ J, parType u < s' → s' < parType v → parInc u v := by
    intro u v hu hv s' hs' hus hsv
    have h1 := ((mem_parRes_stdSub hJ u).1 hu).2 s' hs'
    have h2 := ((mem_parRes_stdSub hJ v).1 hv).2 s' hs'
    exact (parInc_iff_of_ne (by omega)).2 (.inl ((h1.2 hus).trans (h2.1 hsv)))
  have hsep' : ∀ u v : ParGeom, u ∈ parRes (stdSub J) → v ∈ parRes (stdSub J) →
      parType u < s → s < parType v → RReach (parRes (stdSub J)) u v :=
    fun u v hu hv h1 h2 => RAdj.reach hu hv (hsep u v hu hv s hs h1 h2)
  have hxs : parType x ≠ s := fun e => ((mem_parRes_stdSub hJ x).1 hx).1 (e ▸ hs)
  have hys : parType y ≠ s := fun e => ((mem_parRes_stdSub hJ y).1 hy).1 (e ▸ hs)
  have z₁ := stdObj_mem_parRes hJ hm₁ (by omega) hm₁J
  have z₂ := stdObj_mem_parRes hJ (by omega) hm₂ hm₂J
  rcases Nat.lt_or_gt_of_ne hxs with hx' | hx' <;> rcases Nat.lt_or_gt_of_ne hys with hy' | hy'
  · exact (hsep' x _ hx z₂ hx' h₂).trans (hsep' y _ hy z₂ hy' h₂).symm
  · exact hsep' x y hx hy hx' hy'
  · exact (hsep' y x hy hx hy' hx').symm
  · exact (hsep' _ x z₁ hx h₁ hx').symm.trans (hsep' _ y z₁ hy h₁ hy')

theorem reach_interval
    {a b : ℕ} (hab : a + 3 ≤ b) (hb : b ≤ 5) {R : Set ParGeom}
    (hR : ∀ x, x ∈ R ↔ a < parType x ∧ parType x < b ∧ Echain a ≤ x.1.2 ∧ x.1.2 ≤ Echain b) :
    ∃ x₀ ∈ R, ∀ x ∈ R, RReach R x₀ x := by
  obtain ⟨hinst, -⟩ := echain_data b (by omega) hb
  set E := Echain b
  have hLE : Echain a ≤ E := Echain_mono' (by omega) hb
  have hL : finrank (ZMod 2) (subOf E (Echain a)) = a :=
    finrank_subOf E hLE (natCard_Echain' a (by omega))
  have hEobj : IsObj b E := (stdObj b (by omega) hb).2
  have hfin : ∀ x ∈ R, finrank (ZMod 2) (subOf E x.1.2) = parType x := fun x hx =>
    finrank_subOf E ((hR x).1 hx).2.2.2 (natCard_obj x)
  have hmk : ∀ (U : Submodule (ZMod 2) (Additive E)) (k : ℕ), subOf E (Echain a) ≤ U →
      finrank (ZMod 2) U = k → a < k → k < b →
      ∃ x ∈ R, parType x = k ∧ x.1.2 = ofSub E U := by
    intro U k hU hk h1 h2
    have hc := natCard_ofSub_of_finrank hk
    refine ⟨mkObj k (ofSub E U) (isObj_of_le hEobj (ofSub_le U) hc (by omega) (by omega)),
      (hR _).2 ⟨h1, h2, fun g hg => ⟨hLE hg, hU hg⟩, ofSub_le U⟩, rfl, rfl⟩
  have hpt : ∀ x ∈ R, ∃ p ∈ R, parType p = a + 1 ∧ p.1.2 ≤ x.1.2 := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := (hR x).1 hx
    obtain ⟨U, hLU, hUx, hU⟩ := exists_submodule_between (k := a + 1)
      ((subOf_le_subOf_iff hLE).2 h3) (by rw [hL]; omega) (by rw [hfin x hx]; omega)
    obtain ⟨p, hp, hpt, hpU⟩ := hmk U (a + 1) hLU hU (by omega) (by omega)
    refine ⟨p, hp, hpt, ?_⟩
    rw [hpU]
    intro g hg
    obtain ⟨hgE, hgU⟩ := hg
    exact hUx hgU
  have hline : ∀ p ∈ R, ∀ q ∈ R, parType p = a + 1 → parType q = a + 1 → RReach R p q := by
    intro p hp q hq hpt hqt
    by_cases hpq : p = q
    · rw [hpq]
    have hpL := (subOf_le_subOf_iff hLE).2 ((hR p).1 hp).2.2.1
    have hqL := (subOf_le_subOf_iff hLE).2 ((hR q).1 hq).2.2.1
    have hne : subOf E p.1.2 ≠ subOf E q.1.2 := fun e =>
      hpq (obj_ext (by rw [hpt, hqt]) (subOf_injective ((hR p).1 hp).2.2.2
        ((hR q).1 hq).2.2.2 e))
    have hd := finrank_sup_of_ne_of_le hpL hqL (by rw [hfin p hp, hpt, hL])
      (by rw [hfin q hq, hqt, hL]) hne
    obtain ⟨s, hs, hst, hsU⟩ := hmk _ (a + 2) (hpL.trans le_sup_left) (by rw [hd, hL])
      (by omega) (by omega)
    have hps : p.1.2 ≤ s.1.2 := by
      rw [hsU]
      intro g hg
      exact ⟨((hR p).1 hp).2.2.2 hg, Submodule.mem_sup_left hg⟩
    have hqs : q.1.2 ≤ s.1.2 := by
      rw [hsU]
      intro g hg
      exact ⟨((hR q).1 hq).2.2.2 hg, Submodule.mem_sup_right hg⟩
    have h1 : RReach R p s :=
      RAdj.reach hp hs ((parInc_iff_of_ne (by omega)).2 (.inl hps))
    have h2 : RReach R s q :=
      RAdj.reach hs hq ((parInc_iff_of_ne (by omega)).2 (.inr hqs))
    exact h1.trans h2
  have hx₀ : stdObj (a + 1) (by omega) (by omega) ∈ R :=
    (hR _).2 ⟨by change a < a + 1; omega, by change a + 1 < b; omega,
      Echain_mono' (by omega) (by omega), Echain_mono' (by omega) hb⟩
  refine ⟨_, hx₀, fun x hx => ?_⟩
  obtain ⟨p, hp, hpt, hpx⟩ := hpt x hx
  refine (hline _ hx₀ p hp rfl hpt).trans ?_
  by_cases e : p = x
  · rw [e]
  · have hne : parType p ≠ parType x := fun h => e (obj_ext h
      (Subgroup.eq_of_le_of_card_ge hpx (by rw [natCard_obj, natCard_obj, h])))
    exact RAdj.reach hp hx ((parInc_iff_of_ne hne).2 (.inl hpx))

theorem exists_Kchain_smul_std
    {a : ℕ} (ha1 : 1 ≤ a) {x : ParGeom} (hax : a < parType x)
    (hEx : Echain a ≤ x.1.2) : ∃ h : Shat, (h : Dfull) ∈ Kchain a ∧
      h • stdObj (parType x) (parType_bounds x).1 (parType_bounds x).2 = x := by
  have hb := parType_bounds x
  obtain ⟨-, -, g, hg, hxg⟩ := x.2
  change x.1.2 = conjSub g (Echain (parType x)) at hxg
  obtain ⟨hinst, hsurj⟩ := echain_data (parType x) (by omega) hb.2
  obtain ⟨h, hh, he⟩ := exists_normalizer_conjSub_eq hsurj
    (Echain_mono ha1 hax.le (parType_bounds x).2) (hxg ▸ hEx)
  refine ⟨⟨h, Kchain_le_Shat a ha1 (by omega) hh⟩, hh, obj_ext rfl ?_⟩
  change conjSub h (Echain (parType x)) = x.1.2
  rw [hxg, he]

theorem upper_reach_zero
    {R : Set ParGeom} (hR : ∀ x, x ∈ R) :
    ∃ x₀ ∈ R, ∀ x ∈ R, RReach R x₀ x := by
  have hsup : (Kchain 1).subgroupOf Shat ⊔ (Kchain 2).subgroupOf Shat = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (Kchain_le_Shat 1 le_rfl (by norm_num))
      (Kchain_le_Shat 2 (by norm_num) (by norm_num)), Kchain_one, Kchain_two, ← Shat_eq_sup,
      Subgroup.subgroupOf_self]
  refine ⟨_, hR (stdObj 1 le_rfl (by norm_num)), reach_of_sup (H₁ := (Kchain 1).subgroupOf Shat)
    (H₂ := (Kchain 2).subgroupOf Shat) (fun _ _ x _ => hR _)
    (std_reach _ _ (by norm_num : 1 ≤ 2) (by norm_num) (hR _) (hR _))
    (fun h hh => smul_stdObj_of_mem _ _ hh) (fun h hh => smul_stdObj_of_mem _ _ hh) ?_⟩
  intro x _
  obtain ⟨-, -, g, hg, hxg⟩ := x.2
  refine ⟨⟨g, hg⟩, by rw [hsup]; trivial, stdObj _ (parType_bounds x).1 (parType_bounds x).2,
    std_reach _ _ _ _ (hR _) (hR _), obj_ext rfl ?_⟩
  exact hxg.symm

theorem upper_reach_one
    {R : Set ParGeom}
    (hR : ∀ x, x ∈ R ↔ 1 < parType x ∧ Echain 1 ≤ x.1.2) :
    ∃ x₀ ∈ R, ∀ x ∈ R, RReach R x₀ x := by
  have hstd : ∀ t (h1 : 1 ≤ t) (h5 : t ≤ 5), 1 < t → stdObj t h1 h5 ∈ R := fun t h1 h5 ht =>
    (hR _).2 ⟨ht, Echain_mono le_rfl ht.le h5⟩
  have hsup : (Kchain 1 ⊓ Kchain 2).subgroupOf Shat ⊔ (Kchain 1 ⊓ Kchain 3).subgroupOf Shat =
      (Kchain 1).subgroupOf Shat := by
    refine (subgroupOf_sup_eq (inf_le_left.trans (Kchain_le_Shat 1 le_rfl (by norm_num)))
      (inf_le_left.trans (Kchain_le_Shat 1 le_rfl (by norm_num))) ?_).symm
    rw [Kchain_one]
    exact Jhat_eq_sup
  have hpres : ∀ h ∈ (Kchain 1 ⊓ Kchain 2).subgroupOf Shat ⊔ (Kchain 1 ⊓ Kchain 3).subgroupOf Shat,
      ∀ x ∈ R, h • x ∈ R := by
    intro h hh x hx
    rw [hsup, Subgroup.mem_subgroupOf] at hh
    obtain ⟨h1, h2⟩ := (hR x).1 hx
    refine (hR _).2 ⟨h1, ?_⟩
    have := conjSub_mono (g := (h : Dfull)) h2
    rwa [conjSub_eq_self_iff.2 hh] at this
  refine ⟨_, hstd 2 (by norm_num) (by norm_num) (by norm_num),
    reach_of_sup hpres (std_reach _ _ (by norm_num : 1 ≤ 3) (by norm_num)
      (hstd 2 _ _ (by norm_num)) (hstd 3 _ _ (by norm_num)))
    (fun h hh => smul_stdObj_of_mem _ _ (Subgroup.mem_subgroupOf.1 hh).2)
    (fun h hh => smul_stdObj_of_mem _ _ (Subgroup.mem_subgroupOf.1 hh).2) ?_⟩
  intro x hx
  obtain ⟨h1, h2⟩ := (hR x).1 hx
  obtain ⟨h, hh, hhx⟩ := exists_Kchain_smul_std le_rfl h1 h2
  exact ⟨h, by rw [hsup]; exact hh, _, std_reach _ _ _ _ (hstd 2 _ _ (by norm_num))
    (hstd _ _ _ h1), hhx⟩

theorem Ntwo_eq_sup :
    Ntwo = (Ntwo ⊓ K3) ⊔ (Ntwo ⊓ K4) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  refine Ntwo_eq_closure.le.trans ?_
  rw [Subgroup.closure_le]
  rintro _ (rfl | h)
  · exact Subgroup.mem_sup_left ⟨tauhat_mem_Ntwo, tauhat_mem_K3⟩
  · have h' := Ptwo_eq_sup.le h
    exact (sup_le_sup (inf_le_inf_right _ Ptwo_le_Ntwo) (inf_le_inf_right _ Ptwo_le_Ntwo)) h'

theorem upper_reach_two
    {R : Set ParGeom}
    (hR : ∀ x, x ∈ R ↔ 2 < parType x ∧ Echain 2 ≤ x.1.2) :
    ∃ x₀ ∈ R, ∀ x ∈ R, RReach R x₀ x := by
  have hstd : ∀ t (h1 : 1 ≤ t) (h5 : t ≤ 5), 2 < t → stdObj t h1 h5 ∈ R := fun t h1 h5 ht =>
    (hR _).2 ⟨ht, Echain_mono (by norm_num) ht.le h5⟩
  have hsup : (Kchain 2 ⊓ Kchain 3).subgroupOf Shat ⊔ (Kchain 2 ⊓ Kchain 4).subgroupOf Shat =
      (Kchain 2).subgroupOf Shat :=
    (subgroupOf_sup_eq (inf_le_left.trans (Kchain_le_Shat 2 (by norm_num) (by norm_num)))
      (inf_le_left.trans (Kchain_le_Shat 2 (by norm_num) (by norm_num))) Ntwo_eq_sup).symm
  have hpres : ∀ h ∈ (Kchain 2 ⊓ Kchain 3).subgroupOf Shat ⊔ (Kchain 2 ⊓ Kchain 4).subgroupOf Shat,
      ∀ x ∈ R, h • x ∈ R := by
    intro h hh x hx
    rw [hsup, Subgroup.mem_subgroupOf] at hh
    obtain ⟨h1, h2⟩ := (hR x).1 hx
    refine (hR _).2 ⟨h1, ?_⟩
    have := conjSub_mono (g := (h : Dfull)) h2
    rwa [conjSub_eq_self_iff.2 hh] at this
  refine ⟨_, hstd 3 (by norm_num) (by norm_num) (by norm_num),
    reach_of_sup hpres (std_reach _ _ (by norm_num : 1 ≤ 4) (by norm_num)
      (hstd 3 _ _ (by norm_num)) (hstd 4 _ _ (by norm_num)))
    (fun h hh => smul_stdObj_of_mem _ _ (Subgroup.mem_subgroupOf.1 hh).2)
    (fun h hh => smul_stdObj_of_mem _ _ (Subgroup.mem_subgroupOf.1 hh).2) ?_⟩
  intro x hx
  obtain ⟨h1, h2⟩ := (hR x).1 hx
  obtain ⟨h, hh, hhx⟩ := exists_Kchain_smul_std (by norm_num) h1 h2
  exact ⟨h, by rw [hsup]; exact hh, _, std_reach _ _ _ _ (hstd 3 _ _ (by norm_num))
    (hstd _ _ _ h1), hhx⟩

theorem upper_reach_three
    {R : Set ParGeom}
    (hR : ∀ x, x ∈ R ↔ 3 < parType x ∧ Echain 3 ≤ x.1.2) :
    ∃ x₀ ∈ R, ∀ x ∈ R, RReach R x₀ x := by
  have hX4 : ∀ c, IsObj 4 (Y4 c) := fun c => by
    obtain ⟨⟨g, hg, hgc⟩, -⟩ := Y4_mem_X4 c
    exact ⟨by norm_num, by norm_num, g, hg, hgc⟩
  have hX5 : ∀ d, IsObj 5 (Y5 d) := fun d => by
    obtain ⟨⟨g, hg, hgd⟩, -⟩ := Y5_mem_X5 d
    exact ⟨by norm_num, by norm_num, g, hg, hgd⟩
  let o4 : Fin 15 → ParGeom := fun c => mkObj 4 (Y4 c) (hX4 c)
  let o5 : Fin 10 → ParGeom := fun d => mkObj 5 (Y5 d) (hX5 d)
  have h4 : ∀ c, o4 c ∈ R := fun c => (hR _).2 ⟨by change 3 < 4; norm_num, (Y4_mem_X4 c).2⟩
  have h5 : ∀ d, o5 d ∈ R := fun d => (hR _).2 ⟨by change 3 < 5; norm_num, (Y5_mem_X5 d).2⟩
  have hinc : ∀ c d, (d = ev4 c 0 ∨ d = ev4 c 1) → RReach R (o4 c) (o5 d) := fun c d hcd =>
    RAdj.reach (h4 c) (h5 d) ((parInc_iff_of_ne (by change (4 : ℕ) ≠ 5; decide)).2
      (.inl ((Y4_le_Y5_iff c d).2 ((R4_subset_R5_iff c d).2 hcd))))
  have hedge : ∀ c d d', ((ev4 c 0 = d ∧ ev4 c 1 = d') ∨ (ev4 c 0 = d' ∧ ev4 c 1 = d)) →
      RReach R (o5 d) (o5 d') := by
    rintro c d d' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact (hinc c _ (.inl rfl)).symm.trans (hinc c _ (.inr rfl))
    · exact (hinc c _ (.inr rfl)).symm.trans (hinc c _ (.inl rfl))
  have h5reach : ∀ d, RReach R (o5 0) (o5 d) := by
    intro d
    rcases petersen_diam d with rfl | ⟨c, hc⟩ | ⟨c, c', d', hc, hc'⟩
    · exact ReflTransGen.refl
    · exact hedge c 0 d hc
    · exact (hedge c 0 d' hc).trans (hedge c' d' d hc')
  refine ⟨o5 0, h5 0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := (hR x).1 hx
  have hb := parType_bounds x
  obtain ⟨-, -, g, hg, hxg⟩ := x.2
  change x.1.2 = conjSub g (Echain (parType x)) at hxg
  have ht : parType x = 4 ∨ parType x = 5 := by omega
  rcases ht with ht | ht
  · rw [ht] at hxg
    obtain ⟨c, hc⟩ := enum4.surjective ⟨x.1.2, ⟨g, hg, hxg⟩, h2⟩
    have hxc : x = o4 c := obj_ext ht ((congrArg Subtype.val hc).symm.trans (coe_enum4 c))
    rw [hxc]
    exact (h5reach _).trans (hinc c _ (.inl rfl)).symm
  · rw [ht] at hxg
    obtain ⟨d, hd⟩ := enum5.surjective ⟨x.1.2, ⟨g, hg, hxg⟩, h2⟩
    have hxd : x = o5 d := obj_ext ht ((congrArg Subtype.val hd).symm.trans (coe_enum5 d))
    rw [hxd]
    exact h5reach d

theorem upper_reach
    {a : ℕ} (ha : a ≤ 3) {R : Set ParGeom}
    (hR : ∀ x, x ∈ R ↔ a < parType x ∧ Echain a ≤ x.1.2) :
    ∃ x₀ ∈ R, ∀ x ∈ R, RReach R x₀ x := by
  interval_cases a
  · exact upper_reach_zero fun x => (hR x).2 ⟨(parType_bounds x).1, bot_le⟩
  · exact upper_reach_one hR
  · exact upper_reach_two hR
  · exact upper_reach_three hR

theorem std_res_reach
    {J : Set ℕ} [DecidablePred (· ∈ J)] (hJ : J ⊆ Set.Icc 1 5)
    (hc : 2 ≤ ((Finset.Icc 1 5).filter (· ∉ J)).card) :
    ∃ x₀ ∈ parRes (stdSub J), ∀ x ∈ parRes (stdSub J), RReach (parRes (stdSub J)) x₀ x := by
  set M := (Finset.Icc 1 5).filter (· ∉ J) with hM
  have hmemM : ∀ t, t ∈ M ↔ (1 ≤ t ∧ t ≤ 5) ∧ t ∉ J := fun t => by
    rw [hM, Finset.mem_filter, Finset.mem_Icc]
  have hMne : M.Nonempty := Finset.card_pos.1 (by omega)
  set m₁ := M.min' hMne
  set m₂ := M.max' hMne
  have hm₁ := (hmemM m₁).1 (M.min'_mem hMne)
  have hm₂ := (hmemM m₂).1 (M.max'_mem hMne)
  have hlt : m₁ < m₂ := M.min'_lt_max'_of_card (by omega)
  by_cases hsep : ∃ s ∈ J, m₁ < s ∧ s < m₂
  · obtain ⟨s, hs, h1, h2⟩ := hsep
    have hx₀ := stdObj_mem_parRes hJ hm₁.1.1 hm₁.1.2 hm₁.2
    exact ⟨_, hx₀, fun x hx => reach_of_separated hJ hs h1 h2 hm₁.1.1 hm₂.1.2 hm₁.2 hm₂.2
      _ x hx₀ hx⟩
  push Not at hsep
  have hint : ∀ t, m₁ ≤ t → t ≤ m₂ → t ∉ J := by
    intro t h1 h2 ht
    rcases eq_or_lt_of_le h1 with rfl | h1'
    · exact hm₁.2 ht
    rcases eq_or_lt_of_le h2 with rfl | h2'
    · exact hm₂.2 ht
    exact absurd (hsep t ht h1') (by omega)
  have hout : ∀ t, 1 ≤ t → t ≤ 5 → (t < m₁ ∨ m₂ < t) → t ∈ J := by
    intro t h1 h5 h
    by_contra ht
    have htM : t ∈ M := (hmemM t).2 ⟨⟨h1, h5⟩, ht⟩
    rcases h with h | h
    · exact absurd (M.min'_le t htM) (by omega)
    · exact absurd (M.le_max' t htM) (by omega)
  have hres : ∀ x, x ∈ parRes (stdSub J) ↔ (m₁ ≤ parType x ∧ parType x ≤ m₂) ∧
      Echain (m₁ - 1) ≤ x.1.2 ∧ (m₂ < 5 → x.1.2 ≤ Echain (m₂ + 1)) := by
    intro x
    rw [mem_parRes_stdSub hJ]
    have hb := parType_bounds x
    constructor
    · rintro ⟨hxJ, hinc⟩
      have hxM : m₁ ≤ parType x ∧ parType x ≤ m₂ :=
        ⟨M.min'_le _ ((hmemM _).2 ⟨hb, hxJ⟩), M.le_max' _ ((hmemM _).2 ⟨hb, hxJ⟩)⟩
      refine ⟨hxM, ?_, fun h5 => ?_⟩
      · rcases Nat.lt_or_ge m₁ 2 with h | h
        · rw [show m₁ - 1 = 0 by omega]
          exact bot_le
        · exact (hinc _ (hout _ (by omega) (by omega) (.inl (by omega)))).1 (by omega)
      · exact (hinc _ (hout _ (by omega) (by omega) (.inr (by omega)))).2 (by omega)
    · rintro ⟨hxM, hlo, hhi⟩
      refine ⟨hint _ hxM.1 hxM.2, fun s hs => ?_⟩
      obtain ⟨hs1, hs5⟩ := hJ hs
      have hsout : s < m₁ ∨ m₂ < s := by
        by_contra h
        exact hint s (by omega) (by omega) hs
      rcases hsout with h | h
      · exact ⟨fun _ => (Echain_mono' (by omega) (by omega)).trans hlo, fun h' => by omega⟩
      · exact ⟨fun h' => by omega, fun _ => (hhi (by omega)).trans
          (Echain_mono' (by omega) hs5)⟩
  rcases Nat.lt_or_ge m₂ 5 with h5 | h5
  · exact reach_interval (a := m₁ - 1) (b := m₂ + 1) (by omega) (by omega) fun x => by
      rw [hres]
      constructor
      · rintro ⟨hxM, hlo, hhi⟩
        exact ⟨by omega, by omega, hlo, hhi h5⟩
      · rintro ⟨h1, h2, hlo, hhi⟩
        exact ⟨⟨by omega, by omega⟩, hlo, fun _ => hhi⟩
  · exact upper_reach (a := m₁ - 1) (by omega) fun x => by
      rw [hres]
      have hb := parType_bounds x
      constructor
      · rintro ⟨hxM, hlo, -⟩
        exact ⟨by omega, hlo⟩
      · rintro ⟨h1, hlo⟩
        exact ⟨⟨by omega, by omega⟩, hlo, fun h => absurd h (by omega)⟩

theorem parRes_connected
    {F : Set ParGeom} (hF : IsParFlag F) (hrank : (parType '' F).ncard ≤ 3) :
    (parGraph.induce (parRes F)).Connected := by
  classical
  obtain ⟨g, hg⟩ := flag_eq_smul_std hF
  have hJ : parType '' F ⊆ Set.Icc 1 5 := by
    rintro _ ⟨x, -, rfl⟩
    exact parType_bounds x
  obtain ⟨x₀, hx₀, hreach⟩ := std_res_reach hJ (card_filter_notMem_ge hJ hrank)
  rw [hg, parRes_smul]
  refine connected_of_reach ⟨x₀, hx₀, rfl⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact (hreach x hx).smul g

end CFSG.Monster.B.TwoA
