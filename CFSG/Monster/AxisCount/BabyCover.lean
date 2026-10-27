module

public import CFSG.Monster.AxisCount.BabyShort
public import CFSG.Monster.AxisCount.CoverLetters
public import CFSG.Monster.AxisCount.BabyCoverCheckInputs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.Baby

open CFSG.Monster CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.Generated CFSG.Monster.B

@[expose] noncomputable def wgen (us : List (List Native.Gen)) (j : ℕ) : SpaceB ≃ₗ[ℚ] SpaceB :=
  wordLin (us[j]!)

@[expose] noncomputable def wordGroup (us : List (List Native.Gen)) :
    Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  Subgroup.closure (wgen us '' Set.Iio us.length)

@[expose] noncomputable def ggen (us : List (List Native.Gen)) (j : ℕ) : GLV :=
  psiAmb (wgen us j)

section Words

variable {us : List (List Native.Gen)}

theorem wgen_mem_Gvis (hus : ∀ w ∈ us, ∀ g ∈ w, g.isVis = true) {j : ℕ} (hj : j < us.length) :
    wgen us j ∈ Gvis := by
  rw [wgen, getElem!_pos us j hj]
  exact wordLin_mem_Gvis_of_isVis _ (hus _ (List.getElem_mem hj))

theorem wordGroup_le_Gvis (hus : ∀ w ∈ us, ∀ g ∈ w, g.isVis = true) : wordGroup us ≤ Gvis :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨j, hj, rfl⟩
    exact wgen_mem_Gvis hus (Set.mem_Iio.1 hj))

theorem wordGroup_le_of_mem (hU : ∀ w ∈ us, wordLin w ∈ Jstar) : wordGroup us ≤ Jstar :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨j, hj, rfl⟩
    have hj' : j < us.length := Set.mem_Iio.1 hj
    rw [wgen, getElem!_pos us j hj']
    exact hU _ (List.getElem_mem hj'))

theorem wordGroup_le_stabilizer {v : SpaceB} (hU : ∀ w ∈ us, wordLin w v = v) :
    wordGroup us ≤ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) v :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨j, hj, rfl⟩
    have hj' : j < us.length := Set.mem_Iio.1 hj
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, wgen, getElem!_pos us j hj']
    exact hU _ (List.getElem_mem hj'))

theorem psiOrbit_wordGroup (hus : ∀ w ∈ us, ∀ g ∈ w, g.isVis = true) (x : L2) :
    psiOrbit (wordGroup us) x =
      MulAction.orbit (Subgroup.closure (ggen us '' Set.Iio us.length)) x := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    have key : u ∈ Gvis ∧ psiAmb u ∈ Subgroup.closure (ggen us '' Set.Iio us.length) := by
      induction hu using Subgroup.closure_induction with
      | mem a ha =>
        obtain ⟨j, hj, rfl⟩ := ha
        exact ⟨wgen_mem_Gvis hus (Set.mem_Iio.1 hj),
          Subgroup.subset_closure (Set.mem_image_of_mem _ hj)⟩
      | one => exact ⟨Gvis.one_mem, by rw [psiAmb_one]; exact Subgroup.one_mem _⟩
      | mul a b _ _ ha hb =>
        exact ⟨Gvis.mul_mem ha.1 hb.1, by
          rw [psiAmb_mul ha.1 hb.1]
          exact Subgroup.mul_mem _ ha.2 hb.2⟩
      | inv a _ ha =>
        exact ⟨Gvis.inv_mem ha.1, by
          rw [psiAmb_inv ha.1]
          exact Subgroup.inv_mem _ ha.2⟩
    exact ⟨⟨psiAmb u, key.2⟩, rfl⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    have key : ∃ u ∈ wordGroup us, psiAmb u = k := by
      induction hk using Subgroup.closure_induction with
      | mem a ha =>
        obtain ⟨j, hj, rfl⟩ := ha
        exact ⟨wgen us j, Subgroup.subset_closure (Set.mem_image_of_mem _ hj), rfl⟩
      | one => exact ⟨1, Subgroup.one_mem _, psiAmb_one⟩
      | mul a b _ _ ha hb =>
        obtain ⟨u, hu, rfl⟩ := ha
        obtain ⟨u', hu', rfl⟩ := hb
        exact ⟨u * u', Subgroup.mul_mem _ hu hu', psiAmb_mul (wordGroup_le_Gvis hus hu)
          (wordGroup_le_Gvis hus hu')⟩
      | inv a _ ha =>
        obtain ⟨u, hu, rfl⟩ := ha
        exact ⟨u⁻¹, Subgroup.inv_mem _ hu, psiAmb_inv (wordGroup_le_Gvis hus hu)⟩
    obtain ⟨u, hu, rfl⟩ := key
    exact ⟨u, hu, rfl⟩

theorem ggen_smul_dec (hus : ∀ w ∈ us, ∀ g ∈ w, g.isVis = true) {j : ℕ} (hj : j < us.length)
    (v : ℕ) :
    ggen us j • dec v = dec (Native.Cover.actRows (Native.Cover.wordRows us[j]!) v) := by
  have hw : ∀ g ∈ us[j]!, g.isVis = true := by
    rw [getElem!_pos us j hj]
    exact hus _ (List.getElem_mem hj)
  rw [ggen, wgen, psiAmb_of_mem (wordLin_mem_Gvis_of_isVis _ hw)]
  exact psiVis_wordLin_smul_dec_wordRows _ hw v

end Words

structure OrbitFacts (us hs : List (List Native.Gen)) (lams sizes : List ℕ) : Prop where
  us_vis : ∀ w ∈ us, ∀ g ∈ w, g.isVis = true
  hs_vis : ∀ w ∈ hs, ∀ g ∈ w, g.isVis = true
  len_hs : hs.length = lams.length
  len_sizes : lams.length = sizes.length
  lam_eq : ∀ r < hs.length, psiAmb (wordLin hs[r]!) • dec lams[r]! = twoΩCls
  disjoint : ∀ r r', r < lams.length → r' < lams.length → r ≠ r' →
    Disjoint (MulAction.orbit (Subgroup.closure (ggen us '' Set.Iio us.length)) (dec lams[r]!))
      (MulAction.orbit (Subgroup.closure (ggen us '' Set.Iio us.length)) (dec lams[r']!))
  card : ∀ r < lams.length,
    (MulAction.orbit (Subgroup.closure (ggen us '' Set.Iio us.length)) (dec lams[r]!)).ncard =
      sizes[r]!
  total : (⋃ r ∈ Set.Iio lams.length,
    MulAction.orbit (Subgroup.closure (ggen us '' Set.Iio us.length)) (dec lams[r]!)).ncard = 46575

theorem toArray_getElem!_eq (l : List ℕ) {r : ℕ} (hr : r < l.length) : l.toArray[r]! = l[r]! := by
  simp [getElem!_pos, hr]

theorem map_wordRows_getElem! (us : List (List Native.Gen)) {j : ℕ} (hj : j < us.length) :
    ((us.map Native.Cover.wordRows).toArray)[j]! = Native.Cover.wordRows us[j]! := by
  simp [getElem!_pos, hj]

theorem hk_ggen {us : List (List Native.Gen)} (hus : ∀ w ∈ us, ∀ g ∈ w, g.isVis = true) :
    ∀ g < us.length, ∀ p,
      dec (Native.Cover.cvImg ((us.map Native.Cover.wordRows).toArray) g p) =
        ggen us g • dec p := by
  intro g hg p
  rw [Native.Cover.cvImg, map_wordRows_getElem! us hg, ggen_smul_dec hus hg]

theorem orbit_eq_image_rows {us : List (List Native.Gen)}
    (hus : ∀ w ∈ us, ∀ g ∈ w, g.isVis = true) {s : ℕ}
    (hfin : CFSG.KC.AxisPlane.natOrbit ((us.map Native.Cover.wordRows).toArray) s ⊆
      Set.Iio (2 ^ 24)) :
    MulAction.orbit (Subgroup.closure (ggen us '' Set.Iio us.length)) (dec s) =
      dec '' CFSG.KC.AxisPlane.natOrbit ((us.map Native.Cover.wordRows).toArray) s := by
  have hk := hk_ggen hus
  have hsz : ((us.map Native.Cover.wordRows).toArray).size = us.length := by simp
  refine Set.Subset.antisymm (orbit_closure_subset (((Set.finite_Iio _).subset hfin).image dec)
    ?_ ⟨s, Relation.ReflTransGen.refl, rfl⟩) ?_
  · rintro _ ⟨j, hj, rfl⟩ _ ⟨v, hv, rfl⟩
    have hj' : j < us.length := Set.mem_Iio.1 hj
    exact ⟨Native.Cover.cvImg ((us.map Native.Cover.wordRows).toArray) j v,
      Relation.ReflTransGen.tail hv ⟨j, by rw [hsz]; exact hj', rfl⟩, hk j hj' v⟩
  · rintro _ ⟨v, hv, rfl⟩
    induction hv with
    | refl => exact MulAction.mem_orbit_self _
    | tail _ hab ih =>
      obtain ⟨g, hg, rfl⟩ := hab
      rw [hsz] at hg
      rw [hk g hg]
      exact smul_mem_orbit_closure (S := ggen us '' Set.Iio us.length)
        (Set.mem_image_of_mem _ (Set.mem_Iio.2 hg)) ih

theorem ncard_iUnion_disj {α : Type*} (S : ℕ → Set α) : ∀ n, (∀ r < n, (S r).Finite) →
    (∀ r < n, ∀ r' < n, r ≠ r' → Disjoint (S r) (S r')) →
    (⋃ r ∈ Set.Iio n, S r).ncard = ((List.range n).map fun r => (S r).ncard).sum
  | 0, _, _ => by simp
  | n + 1, hfin, h => by
    have e : (⋃ r ∈ Set.Iio (n + 1), S r) = (⋃ r ∈ Set.Iio n, S r) ∪ S n := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨r, hr, hx⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
        · exact Or.inl ⟨r, hr, hx⟩
        · exact Or.inr hx
      · rintro (⟨r, hr, hx⟩ | hx)
        · exact ⟨r, by omega, hx⟩
        · exact ⟨n, by omega, hx⟩
    have hd : Disjoint (⋃ r ∈ Set.Iio n, S r) (S n) := by
      rw [Set.disjoint_iUnion₂_left]
      intro r hr
      exact h r (by simp at hr; omega) n (by omega) (by simp at hr; omega)
    have hf : (⋃ r ∈ Set.Iio n, S r).Finite :=
      Set.Finite.biUnion (Set.finite_Iio n) (fun r hr => hfin r (by simp at hr; omega))
    rw [e, Set.ncard_union_eq hd hf (hfin n (by omega)),
      ncard_iUnion_disj S n (fun r hr => hfin r (by omega))
        (fun r hr r' hr' => h r (by omega) r' (by omega)),
      List.range_succ, List.map_append, List.sum_append]
    simp

theorem map_range_getElem! (l : List ℕ) : (List.range l.length).map (fun r => l[r]!) = l := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [h2]

theorem orbitFacts_of {o : BabyOrbit} (h : BabyOrbits o) :
    OrbitFacts o.U o.h.toList o.lam.toList o.size.toList := by
  obtain ⟨hw, horb⟩ := h
  unfold babyRows at horb
  simp only [babyWordsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨hus, hhs⟩, hlen1⟩, hlen2⟩, hlam⟩, htot⟩ := hw
  have hn : o.lam.toList.length = o.lam.size := Array.length_toList
  have hget : ∀ r, o.lam.toList[r]! = o.lam[r]! := fun r => Array.getElem!_toList
  have hsget : ∀ r, o.size.toList[r]! = o.size[r]! := fun r => Array.getElem!_toList
  have hdisj : ∀ r < o.lam.size, ∀ r' < o.lam.size, r ≠ r' →
      Disjoint (MulAction.orbit (Subgroup.closure (ggen o.U '' Set.Iio o.U.length))
        (dec o.lam[r]!))
      (MulAction.orbit (Subgroup.closure (ggen o.U '' Set.Iio o.U.length)) (dec o.lam[r']!)) := by
    intro r hr r' hr' hne
    obtain ⟨h1, -, hd⟩ := horb r hr
    obtain ⟨h1', -, -⟩ := horb r' hr'
    rw [orbit_eq_image_rows hus h1, orbit_eq_image_rows hus h1', Set.disjoint_left]
    rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hwv⟩
    have := dec_inj w v (Set.mem_Iio.1 (h1' hw)) (Set.mem_Iio.1 (h1 hv)) hwv
    subst this
    exact Set.disjoint_left.1 (hd r' hr' hne) hv hw
  have hcard : ∀ r < o.lam.size,
      (MulAction.orbit (Subgroup.closure (ggen o.U '' Set.Iio o.U.length))
        (dec o.lam[r]!)).ncard = o.size[r]! := by
    intro r hr
    obtain ⟨h1, h2, -⟩ := horb r hr
    rw [orbit_eq_image_rows hus h1, Set.InjOn.ncard_image (fun a ha b hb hab =>
      dec_inj a b (Set.mem_Iio.1 (h1 ha)) (Set.mem_Iio.1 (h1 hb)) hab), h2]
  have hfin : ∀ r < o.lam.size,
      (MulAction.orbit (Subgroup.closure (ggen o.U '' Set.Iio o.U.length))
        (dec o.lam[r]!)).Finite := by
    intro r hr
    rw [orbit_eq_image_rows hus (horb r hr).1]
    exact ((Set.finite_Iio _).subset (horb r hr).1).image dec
  refine ⟨hus, hhs, by simpa using hlen1, by simpa using hlen2, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have hr' : r < (o.h.toList.zip o.lam.toList).length := by
      simp only [List.length_zip, Array.length_toList] at hr ⊢
      omega
    have h1 := hlam _ (List.getElem_mem hr')
    simp only [List.getElem_zip] at h1
    have hw : ∀ g ∈ o.h.toList[r]!, g.isVis = true := by
      rw [getElem!_pos o.h.toList r hr]
      exact hhs _ (List.getElem_mem hr)
    rw [psiAmb_of_mem (wordLin_mem_Gvis_of_isVis _ hw), psiVis_wordLin_smul_dec _ hw,
      getElem!_pos o.h.toList r hr, getElem!_pos o.lam.toList r (by
        simp only [Array.length_toList] at hr ⊢
        omega), h1]
    exact dec_seed
  · intro r r' hr hr' hne
    rw [hget, hget]
    exact hdisj r (by omega) r' (by omega) hne
  · intro r hr
    rw [hget, hsget]
    exact hcard r (by omega)
  · rw [ncard_iUnion_disj _ _ (fun r hr => by rw [hget]; exact hfin r (by omega))
      (fun r hr r' hr' hne => by rw [hget, hget]; exact hdisj r (by omega) r' (by omega) hne),
      ← htot, ← map_range_getElem! o.size.toList]
    simp only [Array.length_toList] at hlen2 ⊢
    rw [← hlen2]
    refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
    rw [hget, hsget]
    exact hcard r (by simpa using hr)

section Groups

variable {us hs : List (List Native.Gen)} {lams sizes : List ℕ}

theorem OrbitFacts.dec_lam_eq (F : OrbitFacts us hs lams sizes) {r : ℕ} (hr : r < hs.length) :
    dec lams[r]! = (psiAmb (wordLin hs[r]!))⁻¹ • twoΩCls := by
  rw [eq_inv_smul_iff]
  exact F.lam_eq r hr

theorem hs_mem_Jstar (hh : ∀ w ∈ hs, wordLin w ∈ Jstar) {r : ℕ} (hr : r < hs.length) :
    wordLin hs[r]! ∈ Jstar := by
  rw [getElem!_pos hs r hr]
  exact hh _ (List.getElem_mem hr)

theorem OrbitFacts.cover
    (F : OrbitFacts us hs lams sizes)
    (hU : ∀ w ∈ us, wordLin w ∈ Jstar) (hh : ∀ w ∈ hs, wordLin w ∈ Jstar)
    (hΔ : babyDelta.ncard ≤ 46575) :
    ∀ x ∈ babyDelta, ∃ r < lams.length,
      x ∈ MulAction.orbit (Subgroup.closure (ggen us '' Set.Iio us.length)) (dec lams[r]!) := by
  have hsub : (⋃ r ∈ Set.Iio lams.length,
      MulAction.orbit (Subgroup.closure (ggen us '' Set.Iio us.length)) (dec lams[r]!)) ⊆
      babyDelta := by
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hy
    obtain ⟨r, hr, hy⟩ := hy
    have hr' : r < hs.length := by rw [F.len_hs]; exact hr
    rw [← psiOrbit_wordGroup F.us_vis] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    rw [F.dec_lam_eq hr']
    exact psiAmb_smul_mem_babyDelta (wordGroup_le_of_mem hU hu)
      (psiAmb_inv_smul_twoΩCls_mem_babyDelta (hs_mem_Jstar hh hr'))
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [F.total]; exact hΔ) (Set.toFinite _)
  intro x hx
  rw [← heq] at hx
  simpa only [Set.mem_iUnion, Set.mem_Iio, exists_prop] using hx

theorem OrbitFacts.cover_doubleCoset
    (F : OrbitFacts us hs lams sizes)
    (hU : ∀ w ∈ us, wordLin w ∈ Jstar) (hh : ∀ w ∈ hs, wordLin w ∈ Jstar)
    (hΔ : babyDelta.ncard ≤ 46575) :
    (Jstar : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ⊆ ⋃ r : Fin hs.length,
      DoubleCoset.doubleCoset (wordLin hs[(r : ℕ)]!) ((Jstar ⊓ Nfr : Subgroup _) : Set _)
        (wordGroup us : Set _) := by
  refine subset_iUnion_doubleCoset_amb Jstar_le_Gvis (wordGroup_le_of_mem hU)
    (h := fun r : Fin hs.length => wordLin hs[(r : ℕ)]!) (fun r => hs_mem_Jstar hh r.2) ?_
  intro g hg
  obtain ⟨r, hr, hx⟩ := F.cover hU hh hΔ _ (psiAmb_inv_smul_twoΩCls_mem_babyDelta hg)
  have hr' : r < hs.length := by rw [F.len_hs]; exact hr
  rw [← psiOrbit_wordGroup F.us_vis] at hx
  obtain ⟨u, hu, hux⟩ := hx
  refine ⟨⟨r, hr'⟩, u, hu, ?_⟩
  rw [← hux, F.dec_lam_eq hr']

theorem OrbitFacts.pairwise_disjoint_doubleCoset (F : OrbitFacts us hs lams sizes)
    (hU : ∀ w ∈ us, wordLin w ∈ Jstar) (hh : ∀ w ∈ hs, wordLin w ∈ Jstar) :
    Pairwise (Function.onFun Disjoint fun r : Fin hs.length =>
      DoubleCoset.doubleCoset (wordLin hs[(r : ℕ)]!) ((Jstar ⊓ Nfr : Subgroup _) : Set _)
        (wordGroup us : Set _)) := by
  intro r r' hne
  refine disjoint_doubleCoset_amb Jstar_le_Gvis (wordGroup_le_of_mem hU) (hs_mem_Jstar hh r.2)
    (hs_mem_Jstar hh r'.2) ?_
  rw [← F.dec_lam_eq r.2, ← F.dec_lam_eq r'.2]
  simp only [psiOrbit_wordGroup F.us_vis]
  exact F.disjoint r r' (by rw [← F.len_hs]; exact r.2) (by rw [← F.len_hs]; exact r'.2)
    (fun h => hne (Fin.ext h))

theorem OrbitFacts.natCard_doubleCoset (F : OrbitFacts us hs lams sizes)
    (hU : ∀ w ∈ us, wordLin w ∈ Jstar) (hh : ∀ w ∈ hs, wordLin w ∈ Jstar) (r : Fin hs.length) :
    Nat.card (DoubleCoset.doubleCoset (wordLin hs[(r : ℕ)]!)
        ((Jstar ⊓ Nfr : Subgroup _) : Set _) (wordGroup us : Set _)) =
      Nat.card (Jstar ⊓ Nfr : Subgroup _) * sizes[(r : ℕ)]! := by
  rw [natCard_doubleCoset_amb Jstar_le_Gvis (wordGroup_le_of_mem hU) (hs_mem_Jstar hh r.2),
    ← F.dec_lam_eq r.2, psiOrbit_wordGroup F.us_vis, Nat.card_coe_set_eq,
    F.card r (by rw [← F.len_hs]; exact r.2)]

theorem psiOn_Jstar_eq (g : Jstar) : psiOn Jstar_le_Gvis g = psiAmb (g : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [psiOn_apply, psiAmb_of_mem (Jstar_le_Gvis g.2)]

theorem OrbitFacts.relIndex_Jstar_inf_Nfr
    (F : OrbitFacts us hs lams sizes)
    (hU : ∀ w ∈ us, wordLin w ∈ Jstar) (hh : ∀ w ∈ hs, wordLin w ∈ Jstar)
    (hΔ : babyDelta.ncard ≤ 46575) :
    (Jstar ⊓ Nfr).relIndex Jstar = 46575 := by
  rw [relIndex_inf_Nfr Jstar_le_Gvis]
  have e : MulAction.orbit (psiOn Jstar_le_Gvis).range twoΩCls = ⋃ r ∈ Set.Iio lams.length,
      MulAction.orbit (Subgroup.closure (ggen us '' Set.Iio us.length)) (dec lams[r]!) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop]
    constructor
    · rintro ⟨⟨k, g, rfl⟩, rfl⟩
      have hy : psiAmb (g : SpaceB ≃ₗ[ℚ] SpaceB) • twoΩCls ∈ babyDelta :=
        psiAmb_smul_mem_babyDelta g.2 twoΩCls_mem_babyDelta
      obtain ⟨r, hr, hr'⟩ := F.cover hU hh hΔ _ hy
      refine ⟨r, hr, ?_⟩
      show psiOn Jstar_le_Gvis g • twoΩCls ∈ _
      rw [psiOn_Jstar_eq]
      exact hr'
    · rintro ⟨r, hr, hx⟩
      have hr' : r < hs.length := by rw [F.len_hs]; exact hr
      rw [← psiOrbit_wordGroup F.us_vis] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      rw [F.dec_lam_eq hr']
      have hu' : u ∈ Jstar := wordGroup_le_of_mem hU hu
      have hh' := hs_mem_Jstar hh hr'
      refine ⟨⟨psiOn Jstar_le_Gvis ⟨u * (wordLin hs[r]!)⁻¹,
        Jstar.mul_mem hu' (Jstar.inv_mem hh')⟩, _, rfl⟩, ?_⟩
      show psiOn Jstar_le_Gvis ⟨u * (wordLin hs[r]!)⁻¹, _⟩ • twoΩCls = _
      rw [psiOn_Jstar_eq, psiAmb_mul (Jstar_le_Gvis hu') (Gvis.inv_mem (Jstar_le_Gvis hh')),
        psiAmb_inv (Jstar_le_Gvis hh'), mul_smul]
  rw [e]
  exact F.total

end Groups

end CFSG.Monster.AxisCount.Baby
