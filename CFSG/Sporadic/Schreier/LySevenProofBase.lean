
module

public import CFSG.Sporadic.Schreier.LySeven
public import CFSG.Sporadic.Schreier.LySevenRep

@[expose] public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native Matrix
open CFSG.Sporadic.Th (allIn_eq_true)

theorem repM_asArr [LySeed]
    (j : ℕ) : RepM (pairAt asArr j).1 (aStar j) ∧
    RepM (pairAt asArr j).2 (aStar j)⁻¹ := by
  have hstart : ∀ j < (#[(matA, matA), (matB, powM 5 111 matB 4)] : Array (Mat × Mat)).size,
      RepM (pairAt #[(matA, matA), (matB, powM 5 111 matB 4)] j).1 ([a, b].getD j 1) := by
    intro j hj
    have hj2 : j < 2 := by simpa using hj
    interval_cases j
    · exact repM_matA
    · exact repM_matB
  exact repM_extendM _ _ [a, b] rfl hstart sevenFacts.inv j

theorem aStarList_length [LySeed] : aStarList.length = 7 := by
  rw [aStarList, extendByWords_length]; simp

theorem aStar_of_ge [LySeed] {j : ℕ} (hj : 7 ≤ j) : aStar j = 1 := by
  rw [aStar, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [aStarList_length]; omega),
    Option.getD_none]

theorem aStar_mem_lyH [LySeed] {j : ℕ} (h2 : 2 ≤ j) : aStar j ∈ lyH := by
  by_cases h7 : j ≤ 6
  · exact Subgroup.subset_closure ⟨j, ⟨h2, h7⟩, rfl⟩
  · rw [aStar_of_ge (by omega)]; exact lyH.one_mem

theorem aStar_fix
    [LySeed]
    {j : ℕ} (h2 : 2 ≤ j) (h7 : j < 7) :
    aStar j • CFSG.Sporadic.Ly.Omega.opE = CFSG.Sporadic.Ly.Omega.opE := by
  have hk := (sevenFacts.gens j h2 h7).1
  have e := keyT_actKey (pairAt asArr j).1 bpRoot_canon.1 hk
  rw [(repM_asArr j).1] at e
  ext1
  change mat (aStar j) * lyE * mat (aStar j)⁻¹ = lyE
  have hE : lyE = keyT bpRootKey * lyF := by rw [keyT_bpRoot]; rfl
  rw [hE, conj_tensor, ← e]

theorem aStar_mem_stabU
    [LySeed] {j : ℕ} (h2 : 2 ≤ j) (h7 : j < 7) : aStar j ∈ stabU :=
  mem_stabU_of_stabOK (repM_asArr j).1 (sevenFacts.gens j h2 h7).2

theorem lyH_le_stabU
    [LySeed] : lyH ≤ stabU := by
  rw [lyH, Subgroup.closure_le]
  rintro _ ⟨j, ⟨h2, h6⟩, rfl⟩
  exact aStar_mem_stabU h2 (by omega)

@[expose] def dagJ [LySeed] (k : ℕ) : J :=
  if hDag[k]!.1 = 0 then aStar (hDag[k]!.2.1 + 2)
  else if hDag[k]!.1 = 1 then (if hDag[k]!.2.1 < k then (dagJ hDag[k]!.2.1)⁻¹ else 1)
  else if hDag[k]!.2.1 < k ∧ hDag[k]!.2.2 < k then dagJ hDag[k]!.2.1 * dagJ hDag[k]!.2.2
  else 1
termination_by k
decreasing_by all_goals omega

theorem mat7_genArr [LySeed]
    (j : ℕ) : mat7 (genArr j) = restr7 (aStar (j + 2)) :=
  mat7_restrArr (repM_asArr (j + 2)).1

theorem dag_local (k : ℕ) (hk : k < hDag.size) :
    valsArr[k]! = (if hDag[k]!.1 = 0 then genArr hDag[k]!.2.1
      else if hDag[k]!.1 = 1 then inv7 (valsArr.getD hDag[k]!.2.1 id7)
      else mul7 (valsArr.getD hDag[k]!.2.1 id7) (valsArr.getD hDag[k]!.2.2 id7)) := by
  have h := sevenFacts.dagLocal
  unfold dagLocalOK at h
  have := (allIn_eq_true.1 h) k (Nat.zero_le _) hk
  simpa using this

theorem dag_inv (k : ℕ) (hk : k < hDag.size) (h1 : hDag[k]!.1 = 1) :
    mul7 (valsArr.getD hDag[k]!.2.1 id7) valsArr[k]! = id7 := by
  have h := sevenFacts.dagInv
  unfold dagInvOK at h
  have := (allIn_eq_true.1 h) k (Nat.zero_le _) hk
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at this
  rcases this with h' | h'
  · exact absurd h1 h'
  · exact h'

theorem getD_valsArr
    {i : ℕ} (hi : i < hDag.size) : valsArr.getD i id7 = valsArr[i]! := by
  rw [Array.getD_eq_getD_getElem?, getElem!_pos valsArr i (by rw [sevenFacts.valsSize]; exact hi),
    Array.getElem?_eq_getElem (by rw [sevenFacts.valsSize]; exact hi), Option.getD_some]

theorem mat7_valsArr

    [LySeed] : ∀ k < hDag.size, mat7 valsArr[k]! = restr7 (dagJ k) ∧ dagJ k ∈ lyH := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [dag_local k hk, dagJ]
    split_ifs with h0 h1 hlt hlt2
    · exact ⟨mat7_genArr _, aStar_mem_lyH (by omega)⟩
    ·
      obtain ⟨hm, hH⟩ := ih _ hlt (by omega)
      have hinv := dag_inv k hk h1
      rw [dag_local k hk, ite_eq_right h0, ite_eq_left h1, getD_valsArr (by omega)] at hinv
      rw [getD_valsArr (by omega)]
      refine ⟨?_, lyH.inv_mem hH⟩
      have e := congrArg mat7 hinv
      rw [mat7_mul7, mat7_id7, hm] at e
      have hS := lyH_le_stabU hH
      have : restr7 (dagJ hDag[k]!.2.1)⁻¹ = (restr7 (dagJ hDag[k]!.2.1))⁻¹ :=
        rho7_inv ⟨_, hS⟩
      rw [this]
      exact (Matrix.inv_eq_right_inv e).symm
    · exfalso
      rcases sevenFacts.dagOrder k hk with h | h
      · exact h0 h
      · exact hlt h.1
    ·
      obtain ⟨hm1, hH1⟩ := ih _ hlt2.1 (by omega)
      obtain ⟨hm2, hH2⟩ := ih _ hlt2.2 (by omega)
      rw [getD_valsArr (by omega), getD_valsArr (by omega), mat7_mul7, hm1, hm2]
      refine ⟨?_, lyH.mul_mem hH1 hH2⟩
      exact (rho7.map_mul ⟨_, lyH_le_stabU hH1⟩ ⟨_, lyH_le_stabU hH2⟩).symm
    · exfalso
      rcases sevenFacts.dagOrder k hk with h | h
      · exact h0 h
      · exact hlt2 ⟨h.1, h.2.resolve_left h1⟩

@[expose] def lyH'
    [LySeed] : Subgroup stabU := lyH.subgroupOf stabU

@[expose] def lyK
    [LySeed] : Subgroup (Equiv.Perm (Fin 7 → ZMod 5)) := lyH'.map rhoP

theorem rhoP_mem_lyK
    [LySeed] {h : J} (hH : h ∈ lyH) : rhoP ⟨h, lyH_le_stabU hH⟩ ∈ lyK :=
  ⟨⟨h, lyH_le_stabU hH⟩, Subgroup.mem_subgroupOf.2 hH, rfl⟩

theorem rhoP_apply_restr [LySeed]
    {h : J} (hS : h ∈ stabU) (v : Fin 7 → ZMod 5) :
    rhoP ⟨h, hS⟩ v = restr7 h *ᵥ v := rfl

theorem mat7_lvArr
    [LySeed] {i : ℕ} {R : Array ℕ} (hR : R ∈ lvArr i) :
    ∃ h ∈ lyH, mat7 R = restr7 h := by
  rw [lvArr, List.mem_toArray, List.mem_map] at hR
  obtain ⟨m, -, rfl⟩ := hR
  by_cases hm : m < hDag.size
  · rw [getD_valsArr hm]
    exact ⟨dagJ m, (mat7_valsArr m hm).2, (mat7_valsArr m hm).1⟩
  · refine ⟨1, lyH.one_mem, ?_⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by
      rw [sevenFacts.valsSize]; omega), Option.getD_none, mat7_id7, restr7_one]

theorem vecTree_parts {root : Array ℕ} {gens : Array (Array ℕ)}
    {T : Array (Array ℕ) × Array ℕ × Array ℕ} (h : vecTreeOK root gens T = true) :
    T.1[0]! = root ∧ (∀ v ∈ T.1, v.size = 7 ∧ ∀ x ∈ v, x < 5) ∧
    (∀ k, 1 ≤ k → k < T.1.size → T.2.1[k]! < k ∧ T.2.2[k]! < gens.size ∧
      mv7 gens[T.2.2[k]!]! T.1[T.2.1[k]!]! = T.1[k]!) ∧
    (∀ k < T.1.size, ∀ k' < T.1.size, T.1[k]! = T.1[k']! → k = k') := by
  unfold vecTreeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, h0⟩, hred⟩, htree⟩, hidx⟩ := h
  refine ⟨h0, fun v hv => ?_, fun k hk1 hk2 => ?_, fun k hk k' hk' he => ?_⟩
  · rw [Array.all_eq_true'] at hred
    have := hred v hv
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq] at this
    exact ⟨this.1, this.2⟩
  · have := (allIn_eq_true.1 htree) k hk1 hk2
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have e1 := (allIn_eq_true.1 hidx) k (Nat.zero_le _) hk
    have e2 := (allIn_eq_true.1 hidx) k' (Nat.zero_le _) hk'
    simp only [beq_iff_eq] at e1 e2
    rw [← e1, ← e2, he]

theorem level_witness
    [LySeed] (i : ℕ) (hfix : ∀ R ∈ lvArr i, ∀ l < i,
      mat7 R *ᵥ toVec7 (stdVec l) = toVec7 (stdVec l))
    (htree : vecTreeOK (stdVec i) (lvArr i) (vecBFS (stdVec i) (lvArr i)) = true) :
    ∀ k < (vecBFS (stdVec i) (lvArr i)).1.size, ∃ g ∈ lyK,
      (∀ l < i, g (toVec7 (stdVec l)) = toVec7 (stdVec l)) ∧
      g (toVec7 (stdVec i)) = toVec7 ((vecBFS (stdVec i) (lvArr i)).1[k]!) := by
  obtain ⟨h0, -, hstep, -⟩ := vecTree_parts htree
  set T := vecBFS (stdVec i) (lvArr i)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨1, lyK.one_mem, fun l _ => rfl, by rw [h0]; rfl⟩
    · obtain ⟨hp, hl, he⟩ := hstep k hpos hk
      obtain ⟨g, hg, hgfix, hgv⟩ := ih _ hp (by omega)
      have hR : (lvArr i)[T.2.2[k]!]! ∈ lvArr i := by
        rw [getElem!_pos (lvArr i) T.2.2[k]! hl]; exact Array.getElem_mem hl
      obtain ⟨h, hH, hhR⟩ := mat7_lvArr hR
      refine ⟨rhoP ⟨h, lyH_le_stabU hH⟩ * g, lyK.mul_mem (rhoP_mem_lyK hH) hg,
        fun l hli => ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, hgfix l hli, rhoP_apply_restr, ← hhR]
        exact hfix _ hR l hli
      · rw [Equiv.Perm.mul_apply, hgv, rhoP_apply_restr, ← hhR, ← toVec7_mv7, he]

theorem levelFix_parts (i : ℕ) (h : levelFixOK (lvArr i) i = true) :
    ∀ R ∈ lvArr i, ∀ l < i, mat7 R *ᵥ toVec7 (stdVec l) = toVec7 (stdVec l) := by
  intro R hR l hl
  unfold levelFixOK at h
  rw [Array.all_eq_true'] at h
  have := (allIn_eq_true.1 (h R hR)) l (Nat.zero_le _) hl
  rw [beq_iff_eq] at this
  rw [← toVec7_mv7, this]

theorem card_level (i : ℕ) (htree : vecTreeOK (stdVec i) (lvArr i) (vecBFS (stdVec i) (lvArr i)) =
    true) : ((Finset.range (vecBFS (stdVec i) (lvArr i)).1.size).image
      fun k => toVec7 ((vecBFS (stdVec i) (lvArr i)).1[k]!)).card =
      (vecBFS (stdVec i) (lvArr i)).1.size := by
  obtain ⟨-, hred, -, hidx⟩ := vecTree_parts htree
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro k hk k' hk' he
  simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
  apply hidx k hk k' hk'
  apply toVec7_inj _ _ he
  · rw [getElem!_pos (vecBFS (stdVec i) (lvArr i)).1 k hk]; exact hred _ (Array.getElem_mem hk)
  · rw [getElem!_pos (vecBFS (stdVec i) (lvArr i)).1 k' hk']
    exact hred _ (Array.getElem_mem hk')

theorem card_image_ge
    [LySeed] : 5859000000 ≤ Nat.card lyK := by
  have hfix : ∀ i < 3, ∀ R ∈ lvArr i, ∀ l < i,
      mat7 R *ᵥ toVec7 (stdVec l) = toVec7 (stdVec l) := by
    intro i hi
    interval_cases i
    · intro R _ l hl; omega
    · exact levelFix_parts 1 sevenFacts.fix1
    · exact levelFix_parts 2 sevenFacts.fix2
  have htree : ∀ i < 3, vecTreeOK (stdVec i) (lvArr i) (vecBFS (stdVec i) (lvArr i)) = true := by
    intro i hi
    interval_cases i
    · exact sevenFacts.tree0
    · exact sevenFacts.tree1
    · exact sevenFacts.tree2
  have h := prod_card_le_card_of_witnesses lyK (fun i => toVec7 (stdVec i)) 3
    (fun i => (Finset.range (vecBFS (stdVec i) (lvArr i)).1.size).image
      fun k => toVec7 ((vecBFS (stdVec i) (lvArr i)).1[k]!))
    (fun i hi y hy => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨g, hg, hgfix, hgv⟩ := level_witness i (hfix i hi) (htree i hi) k
        (Finset.mem_range.1 hk)
      exact ⟨g, hg, hgfix, hgv⟩)
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, card_level 0 (htree 0 (by norm_num)),
    card_level 1 (htree 1 (by norm_num)), card_level 2 (htree 2 (by norm_num)),
    sevenFacts.size0, sevenFacts.size1, sevenFacts.size2] at h
  norm_num at h
  exact h

theorem repM_vArr
    [LySeed] : RepM vArr lyv := repM_evalWordM repM_seedM repM_seedMInv _

theorem repM_tArr
    [LySeed] : RepM tArr lyt := by
  have hvi := repM_vArr.inv_of_check sevenFacts.vInv
  exact (hvi.mul repM_matA).mul repM_vArr

theorem conjTree_parts :
    conjTree.1[0]! = restrArr tArr ∧ (∀ X ∈ conjTree.1, X.size = 49 ∧ ∀ x ∈ X, x < 5) ∧
    (∀ k, 1 ≤ k → k < conjTree.1.size → conjTree.2.1[k]! < k ∧
      conjTree.2.2[k]! < (hGenPairs asArr).size ∧
      mul7 (mul7 (hGenPairs asArr)[conjTree.2.2[k]!]!.1 conjTree.1[conjTree.2.1[k]!]!)
        (hGenPairs asArr)[conjTree.2.2[k]!]!.2 = conjTree.1[k]!) ∧
    (∀ k < conjTree.1.size, ∀ k' < conjTree.1.size, conjTree.1[k]! = conjTree.1[k']! → k = k') := by
  have h := sevenFacts.conj
  unfold conjTreeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, h0⟩, hred⟩, htree⟩, hidx⟩ := h
  refine ⟨h0, fun v hv => ?_, fun k hk1 hk2 => ?_, fun k hk k' hk' he => ?_⟩
  · rw [Array.all_eq_true'] at hred
    have := hred v hv
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq] at this
    exact ⟨this.1, this.2⟩
  · have := (allIn_eq_true.1 htree) k hk1 hk2
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have e1 := (allIn_eq_true.1 hidx) k (Nat.zero_le _) hk
    have e2 := (allIn_eq_true.1 hidx) k' (Nat.zero_le _) hk'
    simp only [beq_iff_eq] at e1 e2
    rw [← e1, ← e2, he]

theorem hGenPairs_size : (hGenPairs asArr).size = 5 := by simp [hGenPairs]

theorem hGenPairs_get {j : ℕ} (hj : j < 5) :
    (hGenPairs asArr)[j]! = (genArr j, inv7 (genArr j)) := by
  rw [getElem!_pos (hGenPairs asArr) j (by rw [hGenPairs_size]; exact hj)]
  simp [hGenPairs, genArr]

theorem mat7_hGenPair
    [LySeed] {j : ℕ} (hj : j < 5) :
    mat7 (hGenPairs asArr)[j]!.1 = restr7 (aStar (j + 2)) ∧
    mat7 (hGenPairs asArr)[j]!.2 = restr7 (aStar (j + 2))⁻¹ := by
  have hS := aStar_mem_stabU (j := j + 2) (by omega) (by omega)
  have hinv := sevenFacts.hpInv (hGenPairs asArr)[j]! (by
    rw [getElem!_pos (hGenPairs asArr) j (by rw [hGenPairs_size]; exact hj)]
    exact Array.getElem_mem _)
  rw [hGenPairs_get hj] at hinv ⊢
  refine ⟨mat7_genArr j, ?_⟩
  have e := congrArg mat7 hinv
  rw [mat7_mul7, mat7_id7, mat7_genArr] at e
  rw [show restr7 (aStar (j + 2))⁻¹ = (restr7 (aStar (j + 2)))⁻¹ from rho7_inv ⟨_, hS⟩]
  exact (Matrix.inv_eq_right_inv e).symm

theorem conj_witness
    [LySeed] (ht : lyt ∈ stabU) : ∀ k < conjTree.1.size, ∃ h ∈ lyH,
    mat7 (conjTree.1[k]!) = restr7 (h * lyt * h⁻¹) := by
  obtain ⟨h0, -, hstep, -⟩ := conjTree_parts
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · refine ⟨1, lyH.one_mem, ?_⟩
      rw [h0, mat7_restrArr repM_tArr]
      simp
    · obtain ⟨hp, hl, he⟩ := hstep k hpos hk
      rw [hGenPairs_size] at hl
      obtain ⟨h, hH, hhm⟩ := ih _ hp (by omega)
      obtain ⟨m1, m2⟩ := mat7_hGenPair hl
      refine ⟨aStar (conjTree.2.2[k]! + 2) * h, lyH.mul_mem (aStar_mem_lyH (by omega)) hH, ?_⟩
      rw [← he, mat7_mul7, mat7_mul7, m1, m2, hhm]
      have hS1 := aStar_mem_stabU (j := conjTree.2.2[k]! + 2) (by omega) (by omega)
      have hS2 : h * lyt * h⁻¹ ∈ stabU :=
        stabU.mul_mem (stabU.mul_mem (lyH_le_stabU hH) ht) (stabU.inv_mem (lyH_le_stabU hH))
      have e1 := rho7.map_mul ⟨_, hS1⟩ ⟨_, hS2⟩
      have e2 := rho7.map_mul (⟨_, hS1⟩ * ⟨_, hS2⟩) ⟨_, stabU.inv_mem hS1⟩
      simp only [rho7_apply] at e1 e2
      rw [← e1, ← e2]
      refine congrArg restr7 ?_
      simp only [Subgroup.coe_mul]
      group

theorem card_conj_class_ge
    [LySeed] (ht : lyt ∈ lyH) :
    406875 ≤ Nat.card (MulAction.orbit (ConjAct lyH) (⟨lyt, ht⟩ : lyH)) := by
  obtain ⟨-, hred, -, hidx⟩ := conjTree_parts
  have hw := conj_witness (lyH_le_stabU ht)
  choose! hk hkH hkm using hw
  let φ : Fin 406875 → MulAction.orbit (ConjAct lyH) (⟨lyt, ht⟩ : lyH) := fun k =>
    ⟨⟨hk k * lyt * (hk k)⁻¹, lyH.mul_mem (lyH.mul_mem (hkH k (by
        have := sevenFacts.conjSize; omega)) ht) (lyH.inv_mem (hkH k (by
        have := sevenFacts.conjSize; omega)))⟩,
      ⟨ConjAct.toConjAct ⟨hk k, hkH k (by have := sevenFacts.conjSize; omega)⟩, by
        apply Subtype.ext
        simp [ConjAct.smul_def]⟩⟩
  have hφ : Function.Injective φ := by
    intro k k' h
    have hk1 : k.val < conjTree.1.size := by have := sevenFacts.conjSize; omega
    have hk2 : k'.val < conjTree.1.size := by have := sevenFacts.conjSize; omega
    have e := congrArg (fun x => restr7 ((x : lyH) : J)) (congrArg Subtype.val h)
    simp only [φ] at e
    rw [← hkm k hk1, ← hkm k' hk2] at e
    apply Fin.ext
    apply hidx k hk1 k' hk2
    apply mat7_inj _ _ e
    · rw [getElem!_pos conjTree.1 k.val hk1]; exact hred _ (Array.getElem_mem hk1)
    · rw [getElem!_pos conjTree.1 k'.val hk2]; exact hred _ (Array.getElem_mem hk2)
  have := Nat.card_le_card_of_injective φ hφ
  simpa using this

theorem card_stabilizer_conjAct {G : Type*} [Group G] (x : G) :
    Nat.card (MulAction.stabilizer (ConjAct G) x) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨ConjAct.ofConjAct g.1, ?_⟩
      invFun := fun g => ⟨ConjAct.toConjAct g.1, ?_⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }
  · obtain ⟨g, hg⟩ := g
    rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, mul_inv_eq_iff_eq_mul] at hg
    exact Subgroup.mem_centralizer_singleton_iff.2 hg
  · obtain ⟨g, hg⟩ := g
    rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct,
      mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 hg

end CFSG.Sporadic.LySchreier
