module

public import CFSG.Monster.B.E6.StdF4RadicalGroup
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.Monster.B.E6.FieldInvF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical
open Matrix

theorem not_mem_setA_iff (i : Fin 6) : i ∉ setA ↔ i = 1 := by
  simp only [setA, Set.mem_insert_iff, Set.mem_singleton_iff]
  revert i
  decide

theorem mem_parabolicRadicalRoots_iff {a : Fin Tag.E6.rank → ℤ} :
    a ∈ parabolicRadicalRoots Tag.E6 (nativeUnion firstJ) ↔ a ∈ radRootList := by
  rw [mem_radRootList_iff, nativeUnion_firstJ]
  constructor
  · rintro ⟨⟨ha, hh⟩, hnot⟩
    refine ⟨ha, hh, ?_⟩
    have h1 : a 1 ≠ 0 := fun h1 => hnot ⟨⟨ha, fun i hi => by
      rw [(not_mem_setA_iff i).mp hi]
      exact h1⟩, ha, hh⟩
    rcases ha.nonneg_or_nonpos with hs | hs
    · exact lt_of_le_of_ne (hs 1) (Ne.symm h1)
    · exact absurd hh (not_lt.mpr (Finset.sum_nonpos fun j _ => hs j))
  · rintro ⟨ha, hh, h1⟩
    refine ⟨⟨ha, hh⟩, fun h => ?_⟩
    have := h.1.2 1 ((not_mem_setA_iff 1).mpr rfl)
    omega

@[expose] def radF (i : Fin 21) : Fin Tag.E6.rank → ℤ := rr i

theorem radF_injective : Function.Injective radF :=
  fun i j h => Fin.ext (rr_injOn i.2 j.2 h)

theorem range_radF :
    Set.range radF = parabolicRadicalRoots Tag.E6 (nativeUnion firstJ) := by
  ext a
  rw [mem_parabolicRadicalRoots_iff, radRootList_eq, List.mem_map]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, List.mem_range.2 i.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, List.mem_range.1 hk⟩, rfl⟩

theorem radRoots_pos : ∀ α ∈ parabolicRadicalRoots Tag.E6 (nativeUnion firstJ),
    IsRoot Tag.E6 α ∧ 0 < height α :=
  fun _ h => h.1

theorem radRoots_closed :
    ∀ α ∈ parabolicRadicalRoots Tag.E6 (nativeUnion firstJ),
    ∀ β ∈ parabolicRadicalRoots Tag.E6 (nativeUnion firstJ), ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot Tag.E6 (a • α + b • β) →
        a • α + b • β ∈ parabolicRadicalRoots Tag.E6 (nativeUnion firstJ) := by
  intro α hα β hβ a b ha hb hr
  rw [mem_parabolicRadicalRoots_iff, mem_radRootList_iff] at hα hβ ⊢
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  refine ⟨hr, ?_, ?_⟩
  · rw [height_nsmul_add_nsmul]
    nlinarith [hα.2.1, hβ.2.1]
  · change 0 < a • α 1 + b • β 1
    simp only [nsmul_eq_mul]
    nlinarith [hα.2.2, hβ.2.2]

@[expose] def radProd
    (c : (Fin Tag.E6.rank → ℤ) → K) : ModGL Tag.E6 K :=
  (radRootList.map fun a => pinnedX Tag.E6 K a (c a)).prod

theorem idxOf_rr {k : ℕ} (hk : k < 21) : radRootList.idxOf (rr k) = k := by
  have h := idxCheck
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h k hk

@[expose] def coefOf (c : Fin 21 → K) (a : Fin Tag.E6.rank → ℤ) : K :=
  c ⟨radRootList.idxOf a % 21, Nat.mod_lt _ (by norm_num)⟩

theorem coefOf_rr (c : Fin 21 → K) {k : ℕ} (hk : k < 21) : coefOf c (rr k) = c ⟨k, hk⟩ := by
  simp only [coefOf, idxOf_rr hk, Nat.mod_eq_of_lt hk]

theorem ofFn_eq_radProd
    (c : Fin 21 → K) :
    (List.ofFn fun i : Fin 21 => pinnedX Tag.E6 K (radF i) (c i)).prod = radProd (coefOf c) := by
  rw [radProd, radRootList_eq, List.map_map]
  refine congrArg List.prod (List.ext_getElem (by simp) fun n h1 h2 => ?_)
  have hn : n < 21 := by simpa using h1
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range, Function.comp_apply,
    coefOf_rr c hn]
  rfl

theorem exists_radProd_eq
    {u : ModGL Tag.E6 K}
    (hu : u ∈ parabolicRadical Tag.E6 K (nativeUnion firstJ)) : ∃ c, u = radProd c := by
  have hbij := (positive_root_collection Tag.E6 K).1 _ radRoots_pos radRoots_closed radF
    radF_injective range_radF
  obtain ⟨c, -, hc⟩ := hbij.2.2 hu
  exact ⟨coefOf c, hc.symm.trans (ofFn_eq_radProd c)⟩

theorem eq_of_radProd_eq
    {c c' : (Fin Tag.E6.rank → ℤ) → K} (h : radProd c = radProd c') :
    ∀ a ∈ radRootList, c a = c' a :=
  pinnedX_list_prod_injective radRootList radRootList_nodup radRoot_pos c c' h

theorem betaGL_radProd
    (c : (Fin Tag.E6.rank → ℤ) → K) :
    betaGL (radProd c) = radProd fun a => barHom (c a) := by
  rw [radProd, map_list_prod, List.map_map, radProd]
  exact congrArg List.prod
    (List.map_congr_left fun a _ => Units.ext (entrywise_pinnedX barHom a (c a)))

theorem orbIdx_cases {i : ℕ} (hi : i < 15) :
    (∃ k, orbIdx i = [k] ∧ k < 21 ∧ rhoIdx k = k) ∨
      ∃ k k', orbIdx i = [k, k'] ∧ k < 21 ∧ k' < 21 ∧ rhoIdx k = k' ∧ rhoIdx k' = k ∧
        rr k ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ rr k') = 0 := by
  interval_cases i
  all_goals first
    | exact Or.inl ⟨_, rfl, by norm_num, rfl⟩
    | exact Or.inr ⟨_, _, rfl, by norm_num, by norm_num, rfl, rfl, by decide⟩

theorem block_eq
    (c : (Fin Tag.E6.rank → ℤ) → K) {i : ℕ} (hi : i < 15) :
    (((orbIdx i).map rr).map fun a => pinnedX Tag.E6 K (rho a) (c a)).prod =
      (((orbIdx i).map rr).map fun a => pinnedX Tag.E6 K a (c (rho a))).prod := by
  rcases orbIdx_cases hi with ⟨k, he, hk, hρ⟩ | ⟨k, k', he, hk, hk', hρ, hρ', h0⟩
  · simp only [he, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [rho, permLattice_rr hk, hρ]
  · simp only [he, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [rho, rho, permLattice_rr hk, permLattice_rr hk', hρ, hρ']
    exact (commute_pinnedX_of_rootForm_eq_zero K (t := TwistTag.E6) (isRoot_rr hk)
      (isRoot_rr hk') h0 _ _).eq.symm

theorem radRootList_eq_flatMap :
    radRootList = (List.range 15).flatMap fun i => (orbIdx i).map rr := by
  rw [radRootList_eq, ← range_flatMap_orbIdx, List.map_flatMap]

theorem prod_rho_eq
    (c : (Fin Tag.E6.rank → ℤ) → K) :
    (radRootList.map fun a => pinnedX Tag.E6 K (rho a) (c a)).prod =
      radProd fun a => c (rho a) := by
  rw [radProd, radRootList_eq_flatMap, prod_map_flatMap, prod_map_flatMap]
  exact congrArg List.prod (List.map_congr_left fun i hi => block_eq c (List.mem_range.1 hi))

theorem conj_radProd
    (c : (Fin Tag.E6.rank → ℤ) → K) :
    diagE6GL * radProd c * diagE6GL⁻¹ = radProd fun a => c (rho a) := by
  rw [← prod_rho_eq, radProd, ← MulAut.conj_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun a ha => ?_)
  rw [Function.comp_apply, MulAut.conj_apply, ← C2E6Std.twistHom_id_eq]
  exact twistHom_id_pinnedX (t := TwistTag.E6) two_eq_zero_K (radRoot_pos a ha).1 (c a)

theorem headIdxCheck : (List.range 21).all (fun k =>
    (orbIdx (orbOf k)).headD 0 == k || (orbIdx (orbOf k)).headD 0 == rhoIdx k) = true := by
  decide +kernel

theorem headD_orbIdx_orbOf {k : ℕ} (hk : k < 21) :
    (orbIdx (orbOf k)).headD 0 = k ∨ (orbIdx (orbOf k)).headD 0 = rhoIdx k := by
  have h := headIdxCheck
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  exact h k hk

theorem eq_zero_or_one_of_bar {a : K} (h : bar a = a) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem eq_zero_or_one_of_barHom {a : K} (h : barHom a = a) : a = 0 ∨ a = 1 :=
  eq_zero_or_one_of_bar h

theorem stdRadical_inf_groupJ_le :
    stdRadical firstJ ⊓ groupJ ≤ radicalQ := by
  intro u hmem
  obtain ⟨hQ, hJ⟩ := Subgroup.mem_inf.mp hmem
  obtain ⟨hu, hΓ⟩ := Subgroup.mem_inf.mp hQ
  obtain ⟨c, rfl⟩ := exists_radProd_eq hu
  have hβ : ∀ a ∈ radRootList, barHom (c a) = c a := by
    have h := betaGL_radProd c
    rw [hJ.2] at h
    exact fun a ha => (eq_of_radProd_eq h a ha).symm
  have hP : diagE6GL * radProd c * diagE6GL⁻¹ = radProd c := by
    have hF := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).1 hΓ).2
    rw [twistHom_eq_conj, hJ.2] at hF
    exact hF
  rw [conj_radProd] at hP
  have hρ : ∀ a ∈ radRootList, c (rho a) = c a := fun a ha => eq_of_radProd_eq hP a ha
  rw [mem_radicalQ_iff]
  refine ⟨fun j => decide (c (rr ((orbIdx j).headD 0)) = 1), ?_⟩
  rw [nfQ_eq_prod, radProd]
  refine congrArg List.prod (List.map_congr_left fun a ha => ?_)
  refine congrArg (pinnedX Tag.E6 K a) ?_
  obtain ⟨k, hk, rfl⟩ : ∃ k < 21, rr k = a := by
    rw [radRootList_eq, List.mem_map] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    exact ⟨k, List.mem_range.1 hk, rfl⟩
  have hmem : rr k ∈ radRootList := by
    rw [radRootList_eq]
    exact List.mem_map_of_mem (List.mem_range.2 hk)
  have hhead : c (rr ((orbIdx (orbOfV (rr k))).headD 0)) = c (rr k) := by
    rw [orbOfV_rr hk]
    rcases headD_orbIdx_orbOf hk with h | h
    · rw [h]
    · rw [h, ← permLattice_rr hk]
      exact hρ _ hmem
  rw [hhead]
  rcases eq_zero_or_one_of_barHom (hβ _ hmem) with h | h <;> simp [h]

theorem rr_mem_parabolicRadicalRoots {k : ℕ} (hk : k < 21) :
    rr k ∈ parabolicRadicalRoots Tag.E6 (nativeUnion firstJ) := by
  rw [mem_parabolicRadicalRoots_iff, radRootList_eq]
  exact List.mem_map_of_mem (List.mem_range.2 hk)

theorem qr_mem_stdRadical
    {i : ℕ} (hi : i < 15) : qr i ∈ stdRadical firstJ := by
  refine ⟨?_, graphFixedRootGroup_le _ _ _ (groupJ_le_stdGroup (qr_mem_groupJ hi))⟩
  rw [qr_eq_prod]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
  exact (le_iSup₂_of_le (rr k) (rr_mem_parabolicRadicalRoots (orbIdx_lt hi k hk)) le_rfl :
    rootSubgroup Tag.E6 K (rr k) ≤ parabolicRadical Tag.E6 K (nativeUnion firstJ))
      (Subgroup.subset_closure ⟨1, rfl⟩)

theorem stdRadical_inf_groupJ :
    stdRadical firstJ ⊓ groupJ = radicalQ := by
  refine le_antisymm stdRadical_inf_groupJ_le (le_inf ?_ radicalQ_le_groupJ)
  rw [radicalQ_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact qr_mem_stdRadical hi

theorem card_stdRadical_inf_groupJ :
    Nat.card (stdRadical firstJ ⊓ groupJ : Subgroup (ModGL Tag.E6 K)) = 2 ^ 15 := by
  rw [stdRadical_inf_groupJ, card_radicalQ]

end CFSG.Monster.B.E6.FieldInvF4
