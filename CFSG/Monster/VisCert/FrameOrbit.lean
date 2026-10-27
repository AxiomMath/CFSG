module

public import CFSG.Monster.VisCert.FrameCert
public import CFSG.Monster.VisCert.FrameGens
public import CFSG.Monster.VisCert.FrameSpec
public import CFSG.Monster.VisCert.Fusion
public import CFSG.Monster.CodeAut.BridgeData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisCert

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible

theorem pA_eq_bridgePA : pA = bridgePA := Equiv.ext (by decide +kernel)

theorem pB_eq_bridgePB : pB = bridgePB := Equiv.ext (by decide +kernel)

theorem native_actGo_eq (rows : Array ℕ) (v : ℕ) :
    ∀ n acc, Native.actGo rows v n acc = actGo rows v n acc
  | 0, _ => rfl
  | n + 1, acc => by rw [Native.actGo, actGo, native_actGo_eq rows v n]

theorem native_actRows_eq (rows : Array ℕ) (v : ℕ) : Native.actRows rows v = actRows rows v :=
  native_actGo_eq rows v 24 0

theorem native_frameReps_eq : Native.frameReps = fusionOrbitReps := by decide +kernel

theorem native_frameSizes_eq : Native.frameSizes = fusionOrbitSizes := by decide +kernel

theorem kGenN_smul_dec : ∀ g < 15, ∀ p, dec (Native.gimg g p) = kGenN g • dec p := by
  intro g hg p
  rw [kGenN_smul_dec' hg, Native.gimg, native_actRows_eq, native_frameRows_eq]

theorem dec_inj : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b :=
  fun _ _ ha hb h => dec_injective ha hb h

theorem image_kGenN_Iio : kGenN '' Set.Iio 15 = Set.range kGen := by
  ext u
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, by rw [kGenN, dite_eq_left (show j < 15 from hj)]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, j.2, by rw [kGenN, dite_eq_left j.2]⟩

theorem image_kGenN_Ico : kGenN '' Set.Ico 1 15 = kGen '' {j | 1 ≤ (j : ℕ)} := by
  ext u
  constructor
  · rintro ⟨j, ⟨hj1, hj⟩, rfl⟩
    exact ⟨⟨j, hj⟩, hj1, by rw [kGenN, dite_eq_left hj]⟩
  · rintro ⟨j, hj1, rfl⟩
    exact ⟨j, ⟨hj1, j.2⟩, by rw [kGenN, dite_eq_left j.2]⟩

theorem closure_kGenN_Iio : Subgroup.closure (kGenN '' Set.Iio 15) = Kvis := by
  rw [image_kGenN_Iio, Kvis]

theorem closure_kGenN_Ico : Subgroup.closure (kGenN '' Set.Ico 1 15) = Nvis := by
  rw [image_kGenN_Ico, Nvis]

theorem dec_frameSeed : dec Native.frameSeed = twoΩCls := dec_seed

theorem orbit_Kvis_subset : MulAction.orbit Kvis twoΩCls ⊆ frameDelta := by
  rintro _ ⟨⟨u, hu⟩, rfl⟩
  exact (smul_mem_frameDelta_iff (Kvis_le_Hvis hu)).2 twoΩCls_mem_frameDelta

section NOrbits

open CFSG.KC.AxisPlane CFSG.KC.VisFrame

theorem reps_getD : ∀ t : Fin 6, reps.getD t 0 = fusionOrbitReps[(t : ℕ)]! := by decide +kernel

theorem sizes_getD : ∀ t : Fin 6, sizes.getD t 0 = fusionOrbitSizes[(t : ℕ)]! := by
  decide +kernel

theorem frameRep_eq_dec_reps (t : Fin 6) : frameRep t = dec (reps.getD t 0) := by
  rw [frameRep, reps_getD]

theorem natOrbit_reps_lt (t : Fin 6) {v : ℕ}
    (hv : v ∈ natOrbit gens (reps.getD t 0)) : v < 2 ^ 24 :=
  (frameOrbits t t.2).1 hv

theorem natOrbit_reps_finite (t : Fin 6) :
    (natOrbit gens (reps.getD t 0)).Finite :=
  (Set.finite_Iio (2 ^ 24)).subset fun _ hv => natOrbit_reps_lt t hv

theorem orbit_Nvis_eq (t : Fin 6) :
    MulAction.orbit Nvis (frameRep t) = dec '' natOrbit gens (reps.getD t 0) := by
  refine Set.Subset.antisymm ?_ ?_
  · rw [frameRep_eq_dec_reps, ← closure_kGenN_Ico]
    refine orbit_closure_subset ((natOrbit_reps_finite t).image dec) ?_
      ⟨_, Relation.ReflTransGen.refl, rfl⟩
    rintro _ ⟨j, ⟨hj1, hj⟩, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [kGenN_smul_dec_wordAct hj1 hj (natOrbit_reps_lt t hv)]
    exact ⟨_, wordAct_mem_natOrbit _ (wordOK_spec (by omega)).1 hv, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hv' : Relation.ReflTransGen
        (fun a b => ∃ g < gens.size, b = CFSG.Monster.AxisCount.Native.Cover.cvImg gens g a)
        (reps.getD t 0) v := hv
    clear hv
    induction hv' with
    | refl =>
      rw [frameRep_eq_dec_reps]
      exact MulAction.mem_orbit_self _
    | tail hab hbc ih =>
      obtain ⟨g, hg, rfl⟩ := hbc
      obtain ⟨n, hn, e⟩ := dec_cvImg_gens hg (natOrbit_reps_lt t hab)
      rw [e]
      exact MulAction.mem_orbit_of_mem_orbit (⟨n, hn⟩ : Nvis) ih

theorem ncard_orbit_Nvis (t : Fin 6) :
    (MulAction.orbit Nvis (frameRep t)).ncard = fusionOrbitSizes[(t : ℕ)]! := by
  rw [orbit_Nvis_eq, Set.InjOn.ncard_image (fun a ha b hb h =>
    dec_injective (natOrbit_reps_lt t ha) (natOrbit_reps_lt t hb) h), (frameOrbits t t.2).2.1,
    sizes_getD]

theorem disjoint_orbit_Nvis {t t' : Fin 6} (h : t ≠ t') :
    Disjoint (MulAction.orbit Nvis (frameRep t)) (MulAction.orbit Nvis (frameRep t')) := by
  rw [orbit_Nvis_eq, orbit_Nvis_eq, Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  obtain rfl := dec_injective (natOrbit_reps_lt t' hb) (natOrbit_reps_lt t ha) hab
  exact Set.disjoint_left.1 ((frameOrbits t t.2).2.2 t' t'.2 (fun e => h (Fin.ext e))) ha hb

end NOrbits

theorem frameRep_mem_orbit_Kvis (t : Fin 6) : frameRep t ∈ MulAction.orbit Kvis twoΩCls := by
  refine Fin.cases ?_ (fun j => ?_) t
  · rw [frameRep_zero]
    exact MulAction.mem_orbit_self _
  · exact ⟨⟨tAmb j, tAmb_mem_Kvis j⟩, tAmb_smul j⟩

theorem orbit_Nvis_subset_orbit_Kvis (t : Fin 6) :
    MulAction.orbit Nvis (frameRep t) ⊆ MulAction.orbit Kvis twoΩCls := by
  rintro _ ⟨⟨n, hn⟩, rfl⟩
  obtain ⟨⟨k, hk⟩, e⟩ := frameRep_mem_orbit_Kvis t
  change k • twoΩCls = frameRep t at e
  refine ⟨⟨n * k, Kvis.mul_mem (Nvis_le_Kvis hn) hk⟩, ?_⟩
  change (n * k) • twoΩCls = n • frameRep t
  rw [mul_smul, e]

theorem frameDelta_eq_iUnion :
    frameDelta = ⋃ t : Fin 6, MulAction.orbit Nvis (frameRep t) := by
  have hsub : (⋃ t : Fin 6, MulAction.orbit Nvis (frameRep t)) ⊆ frameDelta :=
    Set.iUnion_subset fun t => (orbit_Nvis_subset_orbit_Kvis t).trans orbit_Kvis_subset
  have hfin : ∀ t : Fin 6, (MulAction.orbit Nvis (frameRep t)).Finite := fun t => by
    rw [orbit_Nvis_eq]
    exact (natOrbit_reps_finite t).image _
  have hcard : (⋃ t : Fin 6, MulAction.orbit Nvis (frameRep t)).ncard = 8292375 := by
    rw [Set.ncard_iUnion_of_finite hfin (fun t t' h => disjoint_orbit_Nvis h)]
    simp only [ncard_orbit_Nvis]
    rw [finsum_eq_sum_of_fintype, Fin.sum_univ_six]
    rfl
  have hD : frameDelta.Finite := Set.finite_of_ncard_ne_zero (by rw [ncard_frameDelta]; norm_num)
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_frameDelta, hcard]) hD).symm

theorem orbit_Kvis_twoΩCls :
    MulAction.orbit Kvis twoΩCls = frameDelta := by
  refine Set.Subset.antisymm orbit_Kvis_subset ?_
  rw [frameDelta_eq_iUnion]
  exact Set.iUnion_subset orbit_Nvis_subset_orbit_Kvis

theorem exists_Kvis_smul_eq
    {x y : L2} (hx : x ∈ frameDelta) (hy : y ∈ frameDelta) :
    ∃ k ∈ Kvis, k • x = y := by
  rw [← orbit_Kvis_twoΩCls] at hx hy
  obtain ⟨⟨a, ha⟩, rfl⟩ := hx
  obtain ⟨⟨b, hb⟩, rfl⟩ := hy
  refine ⟨b * a⁻¹, Kvis.mul_mem hb (Kvis.inv_mem ha), ?_⟩
  change (b * a⁻¹) • a • twoΩCls = b • twoΩCls
  rw [smul_smul, inv_mul_cancel_right]

theorem exists_Kvis_smul_twoΩCls
    {x : L2} (hx : x ∈ frameDelta) : ∃ u ∈ Kvis, u • twoΩCls = x :=
  exists_Kvis_smul_eq twoΩCls_mem_frameDelta hx

theorem frameRep_eq (t : Fin 6) : frameRep t = dec Native.frameReps[(t : ℕ) + 1 - 1]! := by
  rw [frameRep, native_frameReps_eq]
  rfl

theorem frameRep_mem_frameDelta
    (t : Fin 6) : frameRep t ∈ frameDelta := by
  rw [frameDelta_eq_iUnion]
  exact Set.mem_iUnion.2 ⟨t, MulAction.mem_orbit_self _⟩

theorem visible_frame_orbit_certificate :
    pA = bridgePA ∧ pB = bridgePB ∧
    frameDelta.ncard = 8292375 ∧ twoΩCls ∈ frameDelta ∧
    MulAction.orbit Kvis twoΩCls = frameDelta ∧
    (∀ x ∈ frameDelta, ∀ y ∈ frameDelta, ∃ k ∈ Kvis, k • x = y) ∧
    (∀ (j : Fin 15) (i : Fin 24), kGen j • ellCls i =
      ∑ l : Fin 24, bvec 24 (frameMatrices[(j : ℕ)]!)[(i : ℕ)]! l • ellCls l) ∧
    twoΩCls = ∑ l : Fin 24, bvec 24 frameSeedVec l • ellCls l ∧
    fusionOrbitReps = #[63, 61440, 13135901, 267519, 798985, 14989736] ∧
    fusionOrbitSizes = #[1, 3542, 1457280, 48576, 2637824, 4145152] ∧
    (∀ t : Fin 6, frameRep t ∈ frameDelta ∧
      (MulAction.orbit Nvis (frameRep t)).ncard = fusionOrbitSizes[(t : ℕ)]!) ∧
    frameDelta = ⋃ t : Fin 6, MulAction.orbit Nvis (frameRep t) ∧
    (∀ t t' : Fin 6, t ≠ t' →
      Disjoint (MulAction.orbit Nvis (frameRep t)) (MulAction.orbit Nvis (frameRep t'))) :=
  ⟨pA_eq_bridgePA, pB_eq_bridgePB, ncard_frameDelta, twoΩCls_mem_frameDelta, orbit_Kvis_twoΩCls,
    fun _ hx _ hy => exists_Kvis_smul_eq hx hy, kGen_smul_ellCls, dec_seed.symm, rfl, rfl,
    fun t => ⟨frameRep_mem_frameDelta t, ncard_orbit_Nvis t⟩, frameDelta_eq_iUnion,
    fun _ _ h => disjoint_orbit_Nvis h⟩

end CFSG.Monster.VisCert
