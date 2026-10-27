module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinPair
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinSylow7
public import CFSG.RankThree.GF2n.Smith81.S81E5Uni
public import CFSG.RankThree.GF2n.Smith81.S81Gen76E7

public section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

section Roots


@[expose] def compatMask7 (i : ℕ) : ℕ :=
  bitsOf e7R.length fun j => decide (j ≠ i) && !(e7rNb.getD i 0).testBit j

private theorem psi_chk : (List.range e7R.length).all (fun i =>
    decide ((e7R.getD i []).getD 6 0 = 1) ||
      (pairGraph 0 e7rNb 1 1).bnb e7rO1 200 (compatMask7 i) 25) = true := by
  decide +kernel

theorem getD_ofFn_six (γ : Fin Tag.E7.rank → ℤ) : (List.ofFn γ).getD 6 0 = γ node7 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dif_pos (show 6 < Tag.E7.rank by decide)]
  rfl

theorem node7_eq_one_of_abelian (X : Finset (Fin Tag.E7.rank → ℤ))
    (hXP : ∀ γ ∈ X, IsRoot .E7 γ ∧ 0 < ht γ) (hXX : ∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot .E7 (γ + δ))
    (hX : 27 ≤ X.card) {ρ : Fin Tag.E7.rank → ℤ} (hρ : ρ ∈ X) : ρ node7 = 1 := by
  classical
  by_contra hne
  let idx : (Fin Tag.E7.rank → ℤ) → ℕ := fun γ => e7R.idxOf (List.ofFn γ)
  have hR : ∀ γ ∈ X, List.ofFn γ ∈ e7R := fun γ hγ => (posData_E7.mem γ).1 (hXP γ hγ)
  have hidxlt : ∀ γ ∈ X, idx γ < e7R.length := fun γ hγ => List.idxOf_lt_length_iff.2 (hR γ hγ)
  have hget : ∀ γ ∈ X, e7R.getD (idx γ) [] = List.ofFn γ := fun γ hγ => getD_idxOf e7R (hR γ hγ)
  have hinj : Set.InjOn idx X := by
    intro γ hγ δ hδ h
    exact List.ofFn_injective ((List.idxOf_inj (hR γ hγ)).1 h)
  have hchk : (pairGraph 0 e7rNb 1 1).bnb e7rO1 200 (compatMask7 (idx ρ)) 25 = true := by
    have h := List.all_eq_true.1 psi_chk (idx ρ) (List.mem_range.2 (hidxlt ρ hρ))
    rw [hget ρ hρ, getD_ofFn_six] at h
    simpa [hne] using h
  have hnb' : e7rNb = (List.range (([] : List (List ℤ)).length + e7R.length)).map fun v =>
      bitsOf (([] : List (List ℤ)).length + e7R.length) (adjP e7R [] v) := by
    simpa using e7r_nb
  have hadj : ∀ γ ∈ X, ∀ δ ∈ X, adjP e7R [] (idx γ) (idx δ) = false := by
    intro γ hγ δ hδ
    have h1 := hidxlt γ hγ
    have h2 := hidxlt δ hδ
    simp only [adjP, List.length_nil, Nat.not_lt_zero, ite_false, Nat.sub_zero,
      decide_eq_true h1, decide_eq_true h2, Bool.true_and, decide_eq_false_iff_not]
    rw [hget γ hγ, hget δ hδ, zipWith_add_ofFn, ← posData_E7.mem]
    exact fun h => hXX γ hγ δ hδ h.1
  set I := (X.erase ρ).image idx with hI
  have hmask : ∀ v ∈ I, (compatMask7 (idx ρ)).testBit v = true := by
    intro v hv
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨hγρ, hγX⟩ := Finset.mem_erase.1 hγ
    rw [compatMask7, testBit_bitsOf, nb_testBit e7R [] e7rNb hnb', hadj ρ hρ γ hγX]
    have hne' : idx γ ≠ idx ρ := fun h => hγρ (hinj hγX hρ h)
    simp [hidxlt γ hγX, hne']
  have hind : (pairGraph 0 e7rNb 1 1).Indep I := by
    intro u hu v hv _
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hv
    rw [pairGraph]
    simp only
    rw [nb_testBit e7R [] e7rNb hnb', hadj γ (Finset.mem_of_mem_erase hγ) δ
      (Finset.mem_of_mem_erase hδ)]
    simp
  have hsum := WGraph.bnb_sound (pairGraph 0 e7rNb 1 1) e7rO1 200 _ 25 hchk I hmask hind
  have hcardI : I.card = (X.erase ρ).card :=
    Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.2 (Finset.erase_subset _ _)))
  have hwt : ∑ v ∈ I, (pairGraph 0 e7rNb 1 1).wt v = I.card := by
    simp [pairGraph]
  rw [hwt, hcardI, Finset.card_erase_of_mem hρ] at hsum
  omega

private theorem chk_top : ∀ l ∈ Tag.E7.artifactRoots, l.getD 6 0 = 1 → 7 ^ 6 ≤ horner l := by
  decide +kernel

private theorem chk_low : ∀ l ∈ Tag.E7.artifactRoots, 0 < horner l → l.getD 6 0 ≠ 1 →
    horner l < 7 ^ 6 := by
  decide +kernel

private theorem chk_high : ∀ l ∈ Tag.E7.artifactRoots, horner l < 2 * 7 ^ 6 := by
  decide +kernel

theorem le_fWt_iff {γ : Fin Tag.E7.rank → ℤ} (hγ : IsRoot .E7 γ) :
    7 ^ 6 ≤ fWt Tag.E7.rank γ ↔ γ node7 = 1 := by
  have hl := isRoot_iff_mem_artifactRoots.1 hγ
  rw [← horner_ofFn, ← getD_ofFn_six γ]
  constructor
  · intro h
    by_contra hne
    have h0 : (0 : ℤ) < horner (List.ofFn γ) := lt_of_lt_of_le (by norm_num) h
    have := chk_low _ hl h0 hne
    omega
  · exact chk_top _ hl

theorem fWt_lt {γ : Fin Tag.E7.rank → ℤ} (hγ : IsRoot .E7 γ) : fWt Tag.E7.rank γ < 2 * 7 ^ 6 := by
  rw [← horner_ofFn]
  exact chk_high _ (isRoot_iff_mem_artifactRoots.1 hγ)

theorem pr_topIdx (γ : Fin (Tag.rank .E7) → ℤ) : pr topIdx γ = γ node7 := by
  unfold pr
  rw [wt_topIdx]
  simp

end Roots

section Level


variable {K : Type} [Field K]

theorem le_lvlU_top [Finite K] {A : Subgroup (e7Data_valid.minGroup K)}
    (hA : A ≤ posUnip e7Data_valid K) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card K ^ 27 ≤ Nat.card A) :
    A ≤ lvlU e7Data_valid K (fWt Tag.E7.rank) (7 ^ 6) := by
  classical
  have := finite_minGroup (hV := e7Data_valid) (k := K)
  have hLD : LevelData (e7Data_valid.rootGroup K) (posRoots (fWt Tag.E7.rank)) (fWt Tag.E7.rank) :=
    levelData posData_E7.inj
  have hP : (posRoots (fWt Tag.E7.rank)).Finite := posRoots_finite
  have hA1 : A ≤ lvlU e7Data_valid K (fWt Tag.E7.rank) 1 := by
    rw [lvlU_one_eq e7Data_valid posData_E7 K]
    exact hA
  have hq2 : 1 < Nat.card K := Finite.one_lt_card
  have hle := card_le_pow_leadSet hLD hP hq2.le (fun γ _ => card_rootGroup_le γ) hA1
  have h27 : 27 ≤ (leadSet (X := e7Data_valid.rootGroup K) (lev := fWt Tag.E7.rank) hP A).card := by
    by_contra h
    push Not at h
    have := Nat.pow_lt_pow_right hq2 h
    omega
  have hlead : ∀ γ ∈ leadSet (X := e7Data_valid.rootGroup K) (lev := fWt Tag.E7.rank) hP A,
      γ node7 = 1 := fun γ hγ =>
    node7_eq_one_of_abelian _ (fun δ hδ => ⟨(mem_leadSet.1 hδ).1.1,
        (posData_E7.pos δ (mem_leadSet.1 hδ).1.1).1 (mem_leadSet.1 hδ).1.2⟩)
      (fun γ hγ δ hδ =>
        not_isRoot_add_of_lead (MinData.det_cartan_pos posDef_cartan_E7) hLD hP hAc hγ hδ) h27 hγ
  have key : ∀ n : ℕ, (n : ℤ) < 7 ^ 6 → A ≤ lvlU e7Data_valid K (fWt Tag.E7.rank) (n + 1) := by
    intro n
    induction n with
    | zero => intro _; simpa using hA1
    | succ n ih =>
      intro hn
      push_cast at hn
      have hA' := ih (by omega)
      have e : ((n + 1 : ℕ) : ℤ) + 1 = (n : ℤ) + 1 + 1 := by push_cast; ring
      rw [e]
      by_cases hex : ∃ γ ∈ posRoots (fWt Tag.E7.rank), fWt Tag.E7.rank γ = (n : ℤ) + 1
      · obtain ⟨γ, hγP, hγr⟩ := hex
        have hnot : γ ∉ leadSet (X := e7Data_valid.rootGroup K) (lev := fWt Tag.E7.rank) hP A := by
          intro h
          have h2 := (le_fWt_iff hγP.1).2 (hlead γ h)
          omega
        rw [mem_leadSet, not_and, not_not] at hnot
        have heq := hnot hγP
        rw [hγr] at heq
        intro a ha
        have hmem : a ∈ A ⊓ lvl (e7Data_valid.rootGroup K) (posRoots (fWt Tag.E7.rank))
            (fWt Tag.E7.rank) ((n : ℤ) + 1 + 1) := by
          rw [heq]
          exact ⟨ha, hA' ha⟩
        exact hmem.2
      · push Not at hex
        unfold lvlU
        rw [← lvl_eq_succ _ _ _ hex]
        exact hA'
  have h := key (7 ^ 6 - 1) (by norm_num)
  have e : (((7 ^ 6 - 1 : ℕ) : ℤ) + 1) = 7 ^ 6 := by norm_num
  rwa [e] at h

theorem card_lvlU_top_le [Finite K] :
    Nat.card (lvlU e7Data_valid K (fWt Tag.E7.rank) (7 ^ 6)) ≤ Nat.card K ^ 27 := by
  classical
  have := finite_minGroup (hV := e7Data_valid) (k := K)
  have hLD : LevelData (e7Data_valid.rootGroup K) (posRoots (fWt Tag.E7.rank)) (fWt Tag.E7.rank) :=
    levelData posData_E7.inj
  have hP : (posRoots (fWt Tag.E7.rank)).Finite := posRoots_finite
  set U := lvlU e7Data_valid K (fWt Tag.E7.rank) (7 ^ 6) with hU
  have hU1 : U ≤ lvlU e7Data_valid K (fWt Tag.E7.rank) 1 := lvl_anti _ _ _ (by norm_num)
  have hq1 : 0 < Nat.card K := Nat.card_pos
  have hle := card_le_pow_leadSet hLD hP hq1 (fun γ _ => card_rootGroup_le γ) hU1
  have hsub : ∀ γ ∈ leadSet (X := e7Data_valid.rootGroup K) (lev := fWt Tag.E7.rank) hP U,
      7 ^ 6 ≤ fWt Tag.E7.rank γ := by
    intro γ hγ
    obtain ⟨-, hne⟩ := mem_leadSet.1 hγ
    by_contra hlt
    push Not at hlt
    apply hne
    have h1 : U ≤ lvl (e7Data_valid.rootGroup K) (posRoots (fWt Tag.E7.rank)) (fWt Tag.E7.rank)
        (fWt Tag.E7.rank γ + 1) := lvl_anti _ _ _ (by omega)
    have h2 : U ≤ lvl (e7Data_valid.rootGroup K) (posRoots (fWt Tag.E7.rank)) (fWt Tag.E7.rank)
        (fWt Tag.E7.rank γ) := lvl_anti _ _ _ (by omega)
    rw [inf_eq_left.2 h1, inf_eq_left.2 h2]
  have hcardL :
      (leadSet (X := e7Data_valid.rootGroup K) (lev := fWt Tag.E7.rank) hP U).card ≤ 27 := by
    refine e7_abelian_card_le _ (fun γ hγ => ?_) (fun γ hγ δ hδ hr => ?_)
    · obtain ⟨hγP, -⟩ := mem_leadSet.1 hγ
      exact ⟨hγP.1, (posData_E7.pos γ hγP.1).1 hγP.2⟩
    · have h1 := hsub γ hγ
      have h2 := hsub δ hδ
      have h3 := fWt_lt hr
      rw [map_add] at h3
      omega
  exact hle.trans (Nat.pow_le_pow_right hq1 hcardL)

theorem eq_lvlU_top [Finite K] {A : Subgroup (e7Data_valid.minGroup K)}
    (hA : A ≤ posUnip e7Data_valid K) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card K ^ 27 ≤ Nat.card A) :
    A = lvlU e7Data_valid K (fWt Tag.E7.rank) (7 ^ 6) := by
  have := finite_minGroup (hV := e7Data_valid) (k := K)
  exact Subgroup.eq_of_le_of_card_ge (le_lvlU_top hA hAc hcard) (card_lvlU_top_le.trans hcard)

theorem map_lvlU_top_eq_rootRad7 :
    (lvlU e7Data_valid K (fWt Tag.E7.rank) (7 ^ 6)).map
      ((vAut K).toMonoidHom.comp (EGrp K).subtype) = rootRad7 K := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    unfold lvlU lvl
    refine iSup₂_le fun γ hγ => ?_
    intro y hy
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hy
    refine Subgroup.subset_closure ⟨γ, hγ.1.1, ?_, c, rfl⟩
    rw [pr_topIdx γ]
    exact (le_fWt_iff hγ.1.1).1 hγ.2
  · rw [rootRad7, Subgroup.closure_le]
    rintro _ ⟨γ, hγ, hpr, c, rfl⟩
    have h6 : γ node7 = 1 := by rw [← pr_topIdx γ]; exact hpr
    have h7 := (le_fWt_iff hγ).2 h6
    exact ⟨e7Data_valid.xm K γ c, le_lvl (e7Data_valid.rootGroup K) (posRoots (fWt Tag.E7.rank))
      (fWt Tag.E7.rank) (γ := γ) ⟨hγ, lt_of_lt_of_le (by norm_num) h7⟩ h7
      (e7Data_valid.xm_mem_rootGroup K γ c), rfl⟩

theorem rootRad7_apply_w0 [CharP K 2] {u : V K ≃ₗ[K] V K} (hu : u ∈ rootRad7 K) :
    u (w0 : V K) = w0 := by
  refine Subgroup.closure_induction (p := fun u _ => u (w0 : V K) = w0) ?_ rfl
    (fun x y _ _ hx hy => by rw [LinearEquiv.mul_apply, hy, hx])
    (fun x _ hx => by
      rw [LinearEquiv.coe_inv]
      conv_lhs => rw [← hx]
      exact LinearEquiv.symm_apply_apply x _) hu
  rintro _ ⟨γ, hγ, hpr, c, rfl⟩
  have h6 : γ node7 = 1 := by rw [← pr_topIdx γ]; exact hpr
  have hpos : 0 < ht γ :=
    (posData_E7.pos γ hγ).1 (lt_of_lt_of_le (by norm_num) ((le_fWt_iff hγ).2 h6))
  rw [vAut_apply, e7Data_valid.xu_apply, rootOp_w0_eq_zero_of_pos hγ hpos, smul_zero, add_zero]

end Level

section Conj


variable {K : Type} [Field K]

theorem exists_map_conj_eq_lvlU_top [Finite K] [CharP K 2] (A : Subgroup (e7Data_valid.minGroup K))
    (hel : ∀ a ∈ A, a ^ 2 = 1) (hcard : Nat.card K ^ 27 ≤ Nat.card A) :
    ∃ g : e7Data_valid.minGroup K,
      A.map (MulAut.conj g).toMonoidHom = lvlU e7Data_valid K (fWt Tag.E7.rank) (7 ^ 6) := by
  obtain ⟨g, hg⟩ := e7_conj_into_posU7 K A (isPGroup_of_sq A hel)
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h1 : a * a = 1 := by rw [← pow_two]; exact hel a ha
    have h2 : b * b = 1 := by rw [← pow_two]; exact hel b hb
    have h3 : a * b * (a * b) = 1 := by rw [← pow_two]; exact hel _ (mul_mem ha hb)
    rw [eq_inv_of_mul_eq_one_left h3, mul_inv_rev, inv_eq_of_mul_eq_one_left h1,
      inv_eq_of_mul_eq_one_left h2]
  refine ⟨g, eq_lvlU_top ?_ ?_ ?_⟩
  · have e : posU7 K = posUnip e7Data_valid K := by
      unfold posU7 posUnip
      simp only [one_mul]
    rw [← e]
    exact hg
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard

theorem exists_eq_conjSub_rootRad7 [Finite K] [CharP K 2] {A : Subgroup (V K ≃ₗ[K] V K)}
    (hAE : A ≤ EAut K) (hel : ∀ a ∈ A, a ^ 2 = 1) (hcard : Nat.card K ^ 27 ≤ Nat.card A) :
    ∃ g ∈ EAut K, A = EGeom.conjSub g (rootRad7 K) := by
  set ι : e7Data_valid.minGroup K →* (V K ≃ₗ[K] V K) :=
    (vAut K).toMonoidHom.comp (EGrp K).subtype with hι
  have hιinj : Function.Injective ι := (vAut K).injective.comp Subtype.val_injective
  set A₀ := A.comap ι with hA₀def
  have hmap : A₀.map ι = A := by
    refine Subgroup.map_comap_eq_self ?_
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hAE hx
    exact ⟨⟨u, hu⟩, rfl⟩
  have hcard0 : Nat.card A₀ = Nat.card A := by
    rw [← hmap, Subgroup.card_map_of_injective hιinj]
  have hel0 : ∀ a ∈ A₀, a ^ 2 = 1 := by
    intro a ha
    apply hιinj
    rw [map_pow, map_one]
    exact hel _ ha
  obtain ⟨g, hg⟩ := exists_map_conj_eq_lvlU_top A₀ hel0 (hcard0 ▸ hcard)
  refine ⟨ι g⁻¹, ⟨_, (g⁻¹).2, rfl⟩, ?_⟩
  have hA₀ : A₀ = (lvlU e7Data_valid K (fWt Tag.E7.rank) (7 ^ 6)).map
      (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hg, Subgroup.map_map]
    conv_lhs => rw [← Subgroup.map_id A₀]
    congr 1
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [← hmap, hA₀, ← map_lvlU_top_eq_rootRad7, EGeom.conjSub, Subgroup.map_map,
    Subgroup.map_map]
  congr 1

end Conj

end CFSG.RankThree.GF2n.Smith81.E7Model
