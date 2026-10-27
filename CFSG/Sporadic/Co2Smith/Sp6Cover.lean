module

public import CFSG.Sporadic.Co2Smith.Sp6Group

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.CosetTable
open scoped commutatorElement

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem invRevN_eq {m : ℕ} (w : List (Fin m × Bool)) : Native.invRevN w = FreeGroup.invRev w :=
  rfl

theorem mk_commWordN {m : ℕ} (u v : List (Fin m × Bool)) :
    FreeGroup.mk (Native.commWordN u v) = ⁅FreeGroup.mk u, FreeGroup.mk v⁆ := by
  simp only [Native.commWordN, invRevN_eq, commutatorElement_def, ← FreeGroup.mul_mk,
    FreeGroup.inv_mk]

theorem mem_coverWordsN {m : ℕ} {R : List (List (Fin m × Bool))} {w : Fin m → List (Fin m × Bool)}
    {r : List (Fin m × Bool)} (hr : r ∈ Native.coverWordsN R w) :
    (∃ i, ∃ s ∈ R, r = Native.commWordN [(i, true)] s) ∨ ∃ i, r = (i, false) :: w i := by
  simp only [Native.coverWordsN, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hr
  rcases hr with ⟨i, s, hs, rfl⟩ | ⟨i, rfl⟩
  · exact Or.inl ⟨i, s, hs, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

theorem lift_coverWordsN_eq_one {G : Type*} [Group G] {m : ℕ} {R : List (List (Fin m × Bool))}
    {w : Fin m → List (Fin m × Bool)} {e : Fin m → G}
    (hc : ∀ i, ∀ s ∈ R, ⁅e i, FreeGroup.lift e (FreeGroup.mk s)⁆ = 1)
    (hw : ∀ i, FreeGroup.lift e (FreeGroup.mk (w i)) = e i) :
    ∀ r ∈ (Native.coverWordsN R w).map FreeGroup.mk, FreeGroup.lift e r = 1 := by
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  rcases mem_coverWordsN hr' with ⟨i, s, hs, rfl⟩ | ⟨i, rfl⟩
  · rw [mk_commWordN, map_commutatorElement]
    have h1 : FreeGroup.lift e (FreeGroup.mk [(i, true)]) = e i := by
      simp [FreeGroup.lift_mk]
    rw [h1]
    exact hc i s hs
  · have h1 : FreeGroup.mk ((i, false) :: w i) = (FreeGroup.of i)⁻¹ * FreeGroup.mk (w i) := by
      rw [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.mul_mk]
      rfl
    rw [h1, map_mul, map_inv, FreeGroup.lift_apply_of, hw i, inv_mul_cancel]

abbrev sp6CoverSet : Set (FreeGroup (Fin 8)) := {r | r ∈ Native.sp6CoverR.map FreeGroup.mk}

abbrev PGcov : Type := PG 8 Native.sp6CoverR

theorem lift_sp6Gen_cover :
    ∀ r ∈ sp6CoverSet, FreeGroup.lift sp6Gen r = 1 :=
  lift_coverWordsN_eq_one
    (fun i s hs => by rw [lift_sp6Gen_rel hs, commutatorElement_one_right])
    lift_sp6Gen_comm

@[expose] noncomputable def covMap :
    PGcov →* S0 := PresentedGroup.toGroup lift_sp6Gen_cover

theorem covMap_of
    (i : Fin 8) : covMap (PresentedGroup.of i) = sp6Gen i :=
  PresentedGroup.toGroup.of _

theorem covMap_mk
    (f : FreeGroup (Fin 8)) :
    covMap (PresentedGroup.mk _ f) = FreeGroup.lift sp6Gen f := rfl

theorem covMap_surjective :
    Function.Surjective covMap := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_sp6Gen, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, covMap_of i⟩

theorem mk_rel_mem_center {s : List (Fin 8 × Bool)} (hs : s ∈ Native.sp6Rels) :
    PresentedGroup.mk sp6CoverSet (FreeGroup.mk s) ∈ Subgroup.center PGcov := by
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← PresentedGroup.closure_range_of,
    Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro _ ⟨i, rfl⟩
  have hmem : FreeGroup.mk (Native.commWordN [(i, true)] s) ∈ sp6CoverSet := by
    refine List.mem_map.mpr ⟨_, ?_, rfl⟩
    simp only [Native.sp6CoverR, Native.coverWordsN, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_finRange, true_and]
    exact Or.inl ⟨i, s, hs, rfl⟩
  have h := PresentedGroup.one_of_mem hmem
  rw [mk_commWordN, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem covMap_ker_le_center :
    covMap.ker ≤ Subgroup.center PGcov := by
  intro x hx
  obtain ⟨f, rfl⟩ := PresentedGroup.mk_surjective _ x
  rw [MonoidHom.mem_ker, covMap_mk, lift_sp6Gen_eq_one_iff] at hx
  have hmap : (Subgroup.normalClosure sp6RelSet).map (PresentedGroup.mk sp6CoverSet) ≤
      Subgroup.center PGcov := by
    rw [Subgroup.map_normalClosure _ _ (PresentedGroup.mk_surjective _)]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact mk_rel_mem_center hs
  exact hmap (Subgroup.mem_map_of_mem _ hx)

theorem finite_card_PGcov :
    Finite PGcov ∧ Nat.card PGcov ≤ 2903040 :=
  sp6Cover_card

instance : Finite PGcov := finite_card_PGcov.1

theorem card_PGcov_le :
    Nat.card PGcov ≤ 2903040 := finite_card_PGcov.2

theorem mk_commWordsN_mem {m : ℕ} (c : List (List (Fin m × Bool) × List (Fin m × Bool))) :
    FreeGroup.mk (Native.commWordsN c) ∈ commutator (FreeGroup (Fin m)) := by
  induction c with
  | nil => exact Subgroup.one_mem _
  | cons p c ih =>
    have e : Native.commWordsN (p :: c) = Native.commWordN p.1 p.2 ++ Native.commWordsN c := by
      simp [Native.commWordsN]
    rw [e, ← FreeGroup.mul_mk, mk_commWordN]
    exact Subgroup.mul_mem _
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) ih

theorem lift_commWordsN_mul_central {G : Type*} [Group G] {m : ℕ} (g k : Fin m → G)
    (hk : ∀ i, k i ∈ Subgroup.center G)
    (c : List (List (Fin m × Bool) × List (Fin m × Bool))) :
    FreeGroup.lift (fun i => g i * k i) (FreeGroup.mk (Native.commWordsN c)) =
      FreeGroup.lift g (FreeGroup.mk (Native.commWordsN c)) := by
  set κ := FreeGroup.lift k
  have hκ : ∀ f, κ f ∈ Subgroup.center G := by
    intro f
    have h : κ f ∈ κ.range := ⟨f, rfl⟩
    rw [FreeGroup.range_lift_eq_closure] at h
    exact (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hk i) h
  let φ : FreeGroup (Fin m) →* G :=
    { toFun := fun f => FreeGroup.lift g f * κ f
      map_one' := by simp
      map_mul' := fun f f' => by
        rw [map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (κ f),
          (Subgroup.mem_center_iff.mp (hκ f) (FreeGroup.lift g f')).symm]
        group }
  have hφ : φ = FreeGroup.lift fun i => g i * k i :=
    FreeGroup.ext_hom _ _ fun i => by simp [φ, κ]
  rw [← hφ]
  show FreeGroup.lift g _ * κ _ = _
  let κ' : FreeGroup (Fin m) →* Subgroup.center G := κ.codRestrict _ hκ
  have h1 : κ' (FreeGroup.mk (Native.commWordsN c)) = 1 :=
    Abelianization.commutator_subset_ker κ' (mk_commWordsN_mem c)
  have h2 : κ (FreeGroup.mk (Native.commWordsN c)) = 1 := congrArg Subtype.val h1
  rw [h2, mul_one]

theorem exists_cover_hom
    {T : Type*} [Group T] (π : T →* S0) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center T) :
    ∃ φ : PGcov →* T, ∀ i, π (φ (PresentedGroup.of i)) = sp6Gen i := by
  choose g hg using fun i => hπ (sp6Gen i)
  have hcomp : ∀ h : Fin 8 → T, (∀ i, π (h i) = sp6Gen i) → ∀ f,
      π (FreeGroup.lift h f) = FreeGroup.lift sp6Gen f := by
    intro h hh f
    have e : π.comp (FreeGroup.lift h) = FreeGroup.lift sp6Gen :=
      FreeGroup.ext_hom _ _ fun i => by simp [hh]
    exact DFunLike.congr_fun e f
  set e : Fin 8 → T := fun i =>
    FreeGroup.lift g (FreeGroup.mk (Native.commWordsN (Native.sp6Pairs i))) with he
  have hπe : ∀ i, π (e i) = sp6Gen i := fun i => by
    rw [he, hcomp g hg, lift_sp6Gen_comm]
  set k : Fin 8 → T := fun i => (g i)⁻¹ * e i with hk
  have hkc : ∀ i, k i ∈ Subgroup.center T := fun i => hc (by
    rw [MonoidHom.mem_ker, hk, map_mul, map_inv, hπe, hg, inv_mul_cancel])
  have hgk : (fun i => g i * k i) = e := funext fun i => by rw [hk, mul_inv_cancel_left]
  have hw : ∀ i, FreeGroup.lift e (FreeGroup.mk (Native.commWordsN (Native.sp6Pairs i))) =
      e i := fun i => by
    rw [← hgk, lift_commWordsN_mul_central g k hkc, hgk]
  have hrel : ∀ i, ∀ s ∈ Native.sp6Rels, ⁅e i, FreeGroup.lift e (FreeGroup.mk s)⁆ = 1 := by
    intro i s hs
    have hker : FreeGroup.lift e (FreeGroup.mk s) ∈ Subgroup.center T := hc (by
      rw [MonoidHom.mem_ker, hcomp e hπe, lift_sp6Gen_rel hs])
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hker (e i))
  have hcov : ∀ r ∈ sp6CoverSet, FreeGroup.lift e r = 1 := lift_coverWordsN_eq_one hrel hw
  refine ⟨PresentedGroup.toGroup hcov, fun i => ?_⟩
  rw [PresentedGroup.toGroup.of]
  exact hπe i

theorem commutator_mul_central {G : Type*} [Group G] {a b k k' : G}
    (hk : k ∈ Subgroup.center G) (hk' : k' ∈ Subgroup.center G) :
    ⁅a * k, b * k'⁆ = ⁅a, b⁆ := by
  have c1 := Subgroup.mem_center_iff.mp hk
  have c2 := Subgroup.mem_center_iff.mp hk'
  have e1 : ⁅a * k, b * k'⁆ = ⁅a, b * k'⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * k * (b * k') * (a * k)⁻¹ * (b * k')⁻¹
        = a * (k * (b * k')) * k⁻¹ * a⁻¹ * (b * k')⁻¹ := by group
      _ = a * ((b * k') * k) * k⁻¹ * a⁻¹ * (b * k')⁻¹ := by rw [← c1 (b * k')]
      _ = a * (b * k') * a⁻¹ * (b * k')⁻¹ := by group
  have e2 : ⁅a, b * k'⁆ = ⁅a, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a * (b * k') * a⁻¹ * (b * k')⁻¹ = a * b * (k' * a⁻¹) * k'⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * k') * k'⁻¹ * b⁻¹ := by rw [← c2 a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  rw [e1, e2]

theorem cover_hom_surjective
    {T : Type*} [Group T] (π : T →* S0) (hc : π.ker ≤ Subgroup.center T)
    (hT : commutator T = ⊤) (φ : PGcov →* T) (hφ : ∀ i, π (φ (PresentedGroup.of i)) = sp6Gen i) :
    Function.Surjective φ := by
  have hmap : φ.range.map π = ⊤ := by
    rw [eq_top_iff, ← closure_sp6Gen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨φ (PresentedGroup.of i), ⟨_, rfl⟩, hφ i⟩
  have hdec : ∀ t : T, ∃ r ∈ φ.range, ∃ k ∈ Subgroup.center T, t = r * k := by
    intro t
    obtain ⟨r, hr, hrt⟩ : π t ∈ φ.range.map π := hmap ▸ Subgroup.mem_top _
    refine ⟨r, hr, r⁻¹ * t, hc ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrt, inv_mul_cancel]
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← hT, commutator_def, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨r, hr, k, hk, rfl⟩ := hdec a
  obtain ⟨r', hr', k', hk', rfl⟩ := hdec b
  rw [commutator_mul_central hk hk', commutatorElement_def]
  exact φ.range.mul_mem (φ.range.mul_mem (φ.range.mul_mem hr hr') (φ.range.inv_mem hr))
    (φ.range.inv_mem hr')

end CFSG.Sporadic.Co2Smith
