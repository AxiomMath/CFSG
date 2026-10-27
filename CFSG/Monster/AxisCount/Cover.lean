module

public import CFSG.Monster.AxisCount.CoverAbstract
public import CFSG.Monster.AxisCount.CoverLetters
public import CFSG.Monster.AxisCount.CoverSpec
public import CFSG.Monster.AxisCount.CoverCheck

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.VisCert

@[reducible, expose] noncomputable def gvisAct : MulAction Gvis L2 := MulAction.compHom L2 psiVis

attribute [local instance] gvisAct

theorem gvis_smul_def (g : Gvis) (x : L2) : g • x = psiVis g • x := rfl

theorem stabilizer_gvis : MulAction.stabilizer Gvis twoΩCls =
    (MulAction.stabilizer GLV twoΩCls).comap psiVis := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_comap]
  rfl

theorem Nfr_eq_map : Nfr = (MulAction.stabilizer Gvis twoΩCls).map Gvis.subtype := by
  rw [stabilizer_gvis]
  rfl

section Generic

variable (cA cB : List Native.Gen) (hA : ∀ g ∈ cA, g.isVis = true) (hB : ∀ g ∈ cB, g.isVis = true)

include hA hB in
noncomputable def wordGroup : Subgroup Gvis :=
  Subgroup.closure {⟨wordLin cA, wordLin_mem_Gvis_of_isVis cA hA⟩,
    ⟨wordLin cB, wordLin_mem_Gvis_of_isVis cB hB⟩}

noncomputable def gensU : ℕ → GLV := fun g =>
  if g = 0 then psiVis ⟨wordLin cA, wordLin_mem_Gvis_of_isVis cA hA⟩
  else psiVis ⟨wordLin cB, wordLin_mem_Gvis_of_isVis cB hB⟩

theorem image_gensU : gensU cA cB hA hB '' Set.Iio 2 =
    {psiVis ⟨wordLin cA, wordLin_mem_Gvis_of_isVis cA hA⟩,
      psiVis ⟨wordLin cB, wordLin_mem_Gvis_of_isVis cB hB⟩} := by
  ext x
  simp only [Set.mem_image, Set.mem_Iio, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    interval_cases g
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩

theorem wordGroup_map : (wordGroup cA cB hA hB).map psiVis =
    Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2) := by
  rw [wordGroup, MonoidHom.map_closure, image_gensU]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl | rfl, rfl⟩
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

theorem orbit_wordGroup (x : L2) : MulAction.orbit (wordGroup cA cB hA hB) x =
    MulAction.orbit (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2)) x := by
  ext y
  constructor
  · rintro ⟨⟨u, hu⟩, rfl⟩
    refine ⟨⟨psiVis u, ?_⟩, rfl⟩
    rw [← wordGroup_map]
    exact ⟨u, hu, rfl⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    rw [← wordGroup_map] at hk
    obtain ⟨u, hu, rfl⟩ := hk
    exact ⟨⟨u, hu⟩, rfl⟩

theorem gensU_mem_Hvis
    (g : ℕ) : gensU cA cB hA hB g ∈ Hvis := by
  unfold gensU
  split_ifs <;> exact psiVis_mem_Hvis _

theorem closure_gensU_le :
    Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2) ≤ Hvis :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨g, -, rfl⟩
    exact gensU_mem_Hvis cA cB hA hB g)

theorem gensU_smul_dec (g v : ℕ) :
    gensU cA cB hA hB g • dec v =
      dec (Native.Cover.actRows (Native.Cover.wordRows (if g = 0 then cA else cB)) v) := by
  unfold gensU
  by_cases h0 : g = 0
  · simp only [h0, ite_true]
    exact psiVis_wordLin_smul_dec_wordRows cA hA v
  · simp only [h0, ite_false]
    exact psiVis_wordLin_smul_dec_wordRows cB hB v

@[expose] def rowsU : Array (Array ℕ) := #[Native.Cover.wordRows cA, Native.Cover.wordRows cB]

theorem hk_gensU : ∀ g < 2, ∀ p, dec (Native.Cover.cvImg (rowsU cA cB) g p) =
    gensU cA cB hA hB g • dec p := by
  intro g hg p
  rw [gensU_smul_dec cA cB hA hB g p]
  interval_cases g <;> rfl

theorem dec_eq_inv_smul {w : List Native.Gen} (hw : ∀ g ∈ w, g.isVis = true) {v : ℕ}
    (hv : Native.Cover.l2Word w v = 63) :
    dec v = (psiVis ⟨wordLin w, wordLin_mem_Gvis_of_isVis w hw⟩)⁻¹ • twoΩCls := by
  rw [eq_inv_smul_iff, psiVis_wordLin_smul_dec w hw, hv, dec_seed]

theorem dec_mem_frameDelta
    {w : List Native.Gen} (hw : ∀ g ∈ w, g.isVis = true) {v : ℕ}
    (hv : Native.Cover.l2Word w v = 63) : dec v ∈ frameDelta := by
  rw [dec_eq_inv_smul hw hv]
  exact (smul_mem_frameDelta_iff (Hvis.inv_mem (psiVis_mem_Hvis _))).2 twoΩCls_mem_frameDelta

theorem frameDelta_eq_iUnion_orbit
    {T : Native.Cover.CoverTables} {seeds sizes : Array ℕ}
    (hF : Native.Cover.CoverFacts T (rowsU cA cB) seeds sizes)
    (hseed : ∀ r < seeds.size, dec seeds[r]! ∈ frameDelta) :
    frameDelta = ⋃ r ∈ Set.Iio seeds.size,
      MulAction.orbit (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2)) (dec seeds[r]!) := by
  have hk := hk_gensU cA cB hA hB
  have h1 := hF.image_foundSet_eq_iUnion hk
  have h2 := hF.ncard_image_foundSet (dec := dec) dec_inj
  have hsub : (⋃ r ∈ Set.Iio seeds.size,
      MulAction.orbit (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2)) (dec seeds[r]!)) ⊆
      frameDelta := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hx
    obtain ⟨r, hr, ⟨⟨k, hk'⟩, rfl⟩⟩ := hx
    exact (smul_mem_frameDelta_iff (closure_gensU_le cA cB hA hB hk')).2 (hseed r hr)
  have hfin : frameDelta.Finite :=
    Set.finite_of_ncard_ne_zero (by rw [ncard_frameDelta]; norm_num)
  have hcard : frameDelta.ncard ≤ (⋃ r ∈ Set.Iio seeds.size, MulAction.orbit
      (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2)) (dec seeds[r]!)).ncard := by
    rw [← h1, h2, ncard_frameDelta]
    exact le_of_eq rfl
  exact (Set.eq_of_subset_of_ncard_le hsub hcard hfin).symm

theorem orbit_eq_image {s : ℕ}
    (hfin : CFSG.KC.AxisPlane.natOrbit (rowsU cA cB) s ⊆ Set.Iio (2 ^ 24)) :
    MulAction.orbit (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2)) (dec s) =
      dec '' CFSG.KC.AxisPlane.natOrbit (rowsU cA cB) s := by
  have hk := hk_gensU cA cB hA hB
  have hsz : (rowsU cA cB).size = 2 := rfl
  refine Set.Subset.antisymm (orbit_closure_subset (((Set.finite_Iio _).subset hfin).image dec)
    ?_ ⟨s, Relation.ReflTransGen.refl, rfl⟩) ?_
  · rintro _ ⟨j, hj, rfl⟩ _ ⟨v, hv, rfl⟩
    have hj' : j < 2 := Set.mem_Iio.1 hj
    exact ⟨Native.Cover.cvImg (rowsU cA cB) j v,
      Relation.ReflTransGen.tail hv ⟨j, by rw [hsz]; exact hj', rfl⟩, hk j hj' v⟩
  · rintro _ ⟨v, hv, rfl⟩
    induction hv with
    | refl => exact MulAction.mem_orbit_self _
    | tail _ hab ih =>
      obtain ⟨g, hg, rfl⟩ := hab
      rw [hsz] at hg
      rw [hk g hg]
      exact smul_mem_orbit_closure (S := gensU cA cB hA hB '' Set.Iio 2)
        (Set.mem_image_of_mem _ (Set.mem_Iio.2 hg)) ih

end Generic

theorem ncard_iUnion_lt {α : Type*} (S : ℕ → Set α) : ∀ n, (∀ r < n, (S r).Finite) →
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
      ncard_iUnion_lt S n (fun r hr => hfin r (by omega))
        (fun r hr r' hr' => h r (by omega) r' (by omega)),
      List.range_succ, List.map_append, List.sum_append]
    simp

structure CoverHyp (cA cB : List Native.Gen) (hs : ℕ → List Native.Gen) (n : ℕ)
    (lam size : ℕ → ℕ) : Prop where
  hH : ∀ r < n, ∀ g ∈ hs r, g.isVis = true
  hlam : ∀ r < n, Native.Cover.l2Word (hs r) (lam r) = 63
  orb : ∀ r < n, CFSG.KC.AxisPlane.natOrbit (rowsU cA cB) (lam r) ⊆ Set.Iio (2 ^ 24) ∧
    (CFSG.KC.AxisPlane.natOrbit (rowsU cA cB) (lam r)).ncard = size r ∧
    ∀ r' < n, r ≠ r' → Disjoint (CFSG.KC.AxisPlane.natOrbit (rowsU cA cB) (lam r))
      (CFSG.KC.AxisPlane.natOrbit (rowsU cA cB) (lam r'))
  total : ((List.range n).map size).sum = 8292375

theorem seeds_size (n : ℕ) (lam : ℕ → ℕ) : ((List.range n).map lam).toArray.size = n := by simp

theorem seeds_get (n : ℕ) (lam : ℕ → ℕ) {r : ℕ} (hr : r < n) :
    ((List.range n).map lam).toArray[r]! = lam r := by
  simp [getElem!_pos, hr]

namespace CoverHyp

variable {cA cB : List Native.Gen} {hs : ℕ → List Native.Gen} {n : ℕ} {lam size : ℕ → ℕ}
  (hA : ∀ g ∈ cA, g.isVis = true) (hB : ∀ g ∈ cB, g.isVis = true)
  (H : CoverHyp cA cB hs n lam size)

include H in
theorem disjoint_orbit {r r' : ℕ} (hr : r < n) (hr' : r' < n) (hne : r ≠ r') :
    Disjoint (MulAction.orbit (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2)) (dec (lam r)))
      (MulAction.orbit (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2)) (dec (lam r'))) := by
  obtain ⟨h1, -, hd⟩ := H.orb r hr
  obtain ⟨h1', -, -⟩ := H.orb r' hr'
  rw [orbit_eq_image cA cB hA hB h1, orbit_eq_image cA cB hA hB h1', Set.disjoint_left]
  rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hwv⟩
  have := dec_inj w v (Set.mem_Iio.1 (h1' hw)) (Set.mem_Iio.1 (h1 hv)) hwv
  subst this
  exact Set.disjoint_left.1 (hd r' hr' hne) hv hw

include H in
theorem ncard_orbit {r : ℕ} (hr : r < n) :
    (MulAction.orbit (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2)) (dec (lam r))).ncard =
      size r := by
  obtain ⟨h1, h2, -⟩ := H.orb r hr
  rw [orbit_eq_image cA cB hA hB h1, Set.InjOn.ncard_image (fun a ha b hb hab =>
    dec_inj a b (Set.mem_Iio.1 (h1 ha)) (Set.mem_Iio.1 (h1 hb)) hab), h2]

include H in
theorem frameDelta_eq :
    frameDelta = ⋃ r ∈ Set.Iio n,
      MulAction.orbit (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2)) (dec (lam r)) := by
  have hsub : (⋃ r ∈ Set.Iio n,
      MulAction.orbit (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2)) (dec (lam r))) ⊆
      frameDelta := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hx
    obtain ⟨r, hr, ⟨⟨k, hk'⟩, rfl⟩⟩ := hx
    exact (smul_mem_frameDelta_iff (closure_gensU_le cA cB hA hB hk')).2
      (dec_mem_frameDelta (H.hH r hr) (H.hlam r hr))
  have hfin : ∀ r < n, (MulAction.orbit (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2))
      (dec (lam r))).Finite := fun r hr => by
    rw [orbit_eq_image cA cB hA hB (H.orb r hr).1]
    exact ((Set.finite_Iio _).subset (H.orb r hr).1).image dec
  have hcard : (⋃ r ∈ Set.Iio n, MulAction.orbit
      (Subgroup.closure (gensU cA cB hA hB '' Set.Iio 2)) (dec (lam r))).ncard = 8292375 := by
    rw [ncard_iUnion_lt _ n hfin (fun r hr r' hr' hne => H.disjoint_orbit hA hB hr hr' hne),
      ← H.total]
    congr 1
    exact List.map_congr_left fun r hr => H.ncard_orbit hA hB (List.mem_range.1 hr)
  have hF : frameDelta.Finite :=
    Set.finite_of_ncard_ne_zero (by rw [ncard_frameDelta]; norm_num)
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, ncard_frameDelta]) hF).symm

include H in
@[expose] noncomputable def hElt (r : Fin n) : Gvis :=
  ⟨wordLin (hs r), wordLin_mem_Gvis_of_isVis _ (H.hH r r.2)⟩

theorem hElt_val (r : Fin n) : (hElt H r : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin (hs r) := rfl

theorem dec_lam_eq (r : Fin n) : dec (lam r) = (hElt H r)⁻¹ • twoΩCls := by
  rw [gvis_smul_def, map_inv]
  exact dec_eq_inv_smul (H.hH r r.2) (H.hlam r r.2)

include H in
theorem subset_iUnion :
    ((⊤ : Subgroup Gvis) : Set Gvis) ⊆ ⋃ r : Fin n, DoubleCoset.doubleCoset (hElt H r)
      ((⊤ ⊓ MulAction.stabilizer Gvis twoΩCls : Subgroup Gvis) : Set Gvis)
      (wordGroup cA cB hA hB : Set Gvis) := by
  refine subset_iUnion_doubleCoset (H := ⊤) (U := wordGroup cA cB hA hB) twoΩCls le_top
    (fun r => Subgroup.mem_top _) ?_
  intro g _
  have hx : g⁻¹ • twoΩCls ∈ frameDelta := by
    rw [gvis_smul_def, map_inv]
    exact (smul_mem_frameDelta_iff (Hvis.inv_mem (psiVis_mem_Hvis g))).2 twoΩCls_mem_frameDelta
  rw [H.frameDelta_eq hA hB] at hx
  simp only [Set.mem_iUnion, Set.mem_Iio, exists_prop] at hx
  obtain ⟨r, hr, hxr⟩ := hx
  rw [← orbit_wordGroup cA cB hA hB] at hxr
  obtain ⟨⟨u, hu⟩, hux⟩ := hxr
  refine ⟨⟨r, hr⟩, u, hu, ?_⟩
  rw [← hux, dec_lam_eq H ⟨r, hr⟩]
  rfl

include H in
theorem pairwise_disjoint :
    Pairwise (Function.onFun Disjoint fun r : Fin n => DoubleCoset.doubleCoset (hElt H r)
      ((⊤ ⊓ MulAction.stabilizer Gvis twoΩCls : Subgroup Gvis) : Set Gvis)
      (wordGroup cA cB hA hB : Set Gvis)) := by
  refine pairwise_disjoint_doubleCoset (R := Fin n) (H := ⊤) (U := wordGroup cA cB hA hB)
    twoΩCls (h := hElt H) fun r r' hne => ?_
  rw [orbit_wordGroup, orbit_wordGroup, ← dec_lam_eq, ← dec_lam_eq]
  exact H.disjoint_orbit hA hB r.2 r'.2 fun h => hne (Fin.ext h)

include H in
theorem natCard_doubleCoset (r : Fin n) :
    Nat.card (DoubleCoset.doubleCoset (hElt H r)
      ((⊤ ⊓ MulAction.stabilizer Gvis twoΩCls : Subgroup Gvis) : Set Gvis)
      (wordGroup cA cB hA hB : Set Gvis)) =
      Nat.card (⊤ ⊓ MulAction.stabilizer Gvis twoΩCls : Subgroup Gvis) * size r := by
  rw [CFSG.Monster.AxisCount.natCard_doubleCoset (H := ⊤) (U := wordGroup cA cB hA hB) twoΩCls
    le_top (Subgroup.mem_top _), orbit_wordGroup, ← dec_lam_eq, Nat.card_coe_set_eq,
    H.ncard_orbit hA hB r.2]

theorem map_top_stabilizer :
    ((⊤ ⊓ MulAction.stabilizer Gvis twoΩCls : Subgroup Gvis).map Gvis.subtype) = Nfr := by
  rw [top_inf_eq, Nfr_eq_map]

theorem wordGroup_map_subtype : (wordGroup cA cB hA hB).map Gvis.subtype =
    Subgroup.closure {x | ∃ c ∈ [cA, cB], wordLin c = x} := by
  rw [wordGroup, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons,
    List.not_mem_nil, or_false, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, rfl | rfl, rfl⟩
    · exact ⟨cA, Or.inl rfl, rfl⟩
    · exact ⟨cB, Or.inr rfl, rfl⟩
  · rintro ⟨c, rfl | rfl, rfl⟩
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

include hA hB H in
theorem cover :
    (Gvis : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ⊆ ⋃ r : Fin n, DoubleCoset.doubleCoset (wordLin (hs r))
      (Nfr : Set (SpaceB ≃ₗ[ℚ] SpaceB))
      (Subgroup.closure {x | ∃ c ∈ [cA, cB], wordLin c = x} : Set (SpaceB ≃ₗ[ℚ] SpaceB)) := by
  intro g hg
  have h1 := H.subset_iUnion hA hB
    (show (⟨g, hg⟩ : Gvis) ∈ ((⊤ : Subgroup Gvis) : Set Gvis) from Subgroup.mem_top _)
  simp only [Set.mem_iUnion] at h1 ⊢
  obtain ⟨r, hr⟩ := h1
  refine ⟨r, ?_⟩
  have h2 := Set.mem_image_of_mem Gvis.subtype hr
  rw [image_doubleCoset, map_top_stabilizer, wordGroup_map_subtype hA hB] at h2
  exact h2

include hA hB H in
theorem pairwise_disjoint' :
    Pairwise (Function.onFun Disjoint fun r : Fin n => DoubleCoset.doubleCoset (wordLin (hs r))
      (Nfr : Set (SpaceB ≃ₗ[ℚ] SpaceB))
      (Subgroup.closure {x | ∃ c ∈ [cA, cB], wordLin c = x} : Set (SpaceB ≃ₗ[ℚ] SpaceB))) := by
  intro r r' hne
  have h1 := (Set.disjoint_image_iff (f := Gvis.subtype) Subtype.val_injective).2
    (H.pairwise_disjoint hA hB hne)
  rw [image_doubleCoset, image_doubleCoset, map_top_stabilizer,
    wordGroup_map_subtype hA hB] at h1
  exact h1

include hA hB H in
theorem natCard' (r : Fin n) :
    Nat.card (DoubleCoset.doubleCoset (wordLin (hs r)) (Nfr : Set (SpaceB ≃ₗ[ℚ] SpaceB))
      (Subgroup.closure {x | ∃ c ∈ [cA, cB], wordLin c = x} : Set (SpaceB ≃ₗ[ℚ] SpaceB))) =
      size r * Nat.card Nfr := by
  have h1 := natCard_doubleCoset_map (φ := Gvis.subtype) Subtype.val_injective (hElt H r)
    (⊤ ⊓ MulAction.stabilizer Gvis twoΩCls : Subgroup Gvis) (wordGroup cA cB hA hB)
  rw [map_top_stabilizer, wordGroup_map_subtype hA hB] at h1
  have h2 : Nat.card Nfr = Nat.card (⊤ ⊓ MulAction.stabilizer Gvis twoΩCls : Subgroup Gvis) := by
    rw [← map_top_stabilizer]
    exact Subgroup.card_map_of_injective Subtype.val_injective
  rw [h2, mul_comm, ← H.natCard_doubleCoset hA hB r]
  exact h1

end CoverHyp



namespace Cert

open Native

theorem sizeW_total : ∀ i : Fin 12, ((List.range (nW i)).map (sizeW i)).sum = 8292375 := by
  decide +kernel

theorem coverHyp (i : Fin 12) :
    (∀ g ∈ UA i, g.isVis = true) ∧ (∀ g ∈ UB i, g.isVis = true) ∧
      CoverHyp (UA i) (UB i) (hW i) (nW i) (lamW i) (sizeW i) := by
  obtain ⟨hw, horb⟩ := orbitOK_all i
  simp only [wordsOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range] at hw
  obtain ⟨⟨hA, hB⟩, hh⟩ := hw
  exact ⟨hA, hB, ⟨fun r hr g hg => (hh r hr).1 g hg, fun r hr => (hh r hr).2, horb,
    sizeW_total i⟩⟩

@[expose] noncomputable def Ui (i : Fin 12) : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  Subgroup.closure {wordLin c | c ∈ UW i}

@[expose] noncomputable def hh (i : Fin 12) (r : ℕ) : SpaceB ≃ₗ[ℚ] SpaceB := wordLin (hW i r)

theorem hh_eq (i : Fin 12) (r : ℕ) : hh i r = wordLin (hW i r) := rfl

theorem Ui_eq (i : Fin 12) : Ui i = Subgroup.closure {wordLin (UA i), wordLin (UB i)} := by
  unfold Ui UW
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, rfl | rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr rfl, rfl⟩

theorem Ui_le_Gvis (i : Fin 12) : Ui i ≤ Gvis := by
  obtain ⟨hA, hB, -⟩ := coverHyp i
  show Subgroup.closure {x | ∃ c ∈ [UA i, UB i], wordLin c = x} ≤ Gvis
  rw [← CoverHyp.wordGroup_map_subtype hA hB]
  rintro _ ⟨u, -, rfl⟩
  exact u.2

theorem hh_mem_Gvis
    (i : Fin 12) {r : ℕ} (hr : r < nW i) : hh i r ∈ Gvis := by
  obtain ⟨-, -, H⟩ := coverHyp i
  exact wordLin_mem_Gvis_of_isVis _ (H.hH r hr)

theorem cover (i : Fin 12) :
    (Gvis : Set (SpaceB ≃ₗ[ℚ] SpaceB)) ⊆ ⋃ r : Fin (nW i), DoubleCoset.doubleCoset (hh i r)
      (Nfr : Set (SpaceB ≃ₗ[ℚ] SpaceB)) (Ui i : Set (SpaceB ≃ₗ[ℚ] SpaceB)) := by
  obtain ⟨hA, hB, H⟩ := coverHyp i
  exact H.cover hA hB

theorem pairwise_disjoint (i : Fin 12) :
    Pairwise (Function.onFun Disjoint fun r : Fin (nW i) => DoubleCoset.doubleCoset (hh i r)
      (Nfr : Set (SpaceB ≃ₗ[ℚ] SpaceB)) (Ui i : Set (SpaceB ≃ₗ[ℚ] SpaceB))) := by
  obtain ⟨hA, hB, H⟩ := coverHyp i
  exact H.pairwise_disjoint' hA hB

theorem natCard_doubleCoset (i : Fin 12) (r : Fin (nW i)) :
    Nat.card (DoubleCoset.doubleCoset (hh i r) (Nfr : Set (SpaceB ≃ₗ[ℚ] SpaceB))
      (Ui i : Set (SpaceB ≃ₗ[ℚ] SpaceB))) = sizeW i r * Nat.card Nfr := by
  obtain ⟨hA, hB, H⟩ := coverHyp i
  exact H.natCard' hA hB r

theorem natCard_doubleCoset_eq (i : Fin 12) (r : Fin (nW i)) :
    Nat.card (DoubleCoset.doubleCoset (hh i r) (Nfr : Set (SpaceB ≃ₗ[ℚ] SpaceB))
      (Ui i : Set (SpaceB ≃ₗ[ℚ] SpaceB))) = Nat.card Nfr * sizeW i r := by
  rw [natCard_doubleCoset, mul_comm]

end Cert

end CFSG.Monster.AxisCount
