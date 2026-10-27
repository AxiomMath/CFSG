module

public import CFSG.Sporadic.Schreier.TitsDAction
public import CFSG.Sporadic.Schreier.TitsStabCheck

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem titsT_rep
    {i : ℕ} (hi : i < 13) : Rep 1755 titsDerivedArrs[i]! (titsT i) :=
  rep_of_allPermsOK titsChains_check.2.2.2.2.2.2.1 (by rw [titsDerivedArrs_size]; exact hi)

theorem rep_wordArr_titsT {w : List ℤ} (hw : lettersOK 13 w = true) :
    Rep 1755 (wordArr 1755 titsDerivedArrs w) (wordIn 13 titsT w) :=
  rep_wordArr (by rw [titsDerivedArrs_size]) (fun _ hi => titsT_rep hi)
    (fun _ hi => isInvA_of_allPermsOK titsChains_check.2.2.2.2.2.2.1
      (by rw [titsDerivedArrs_size]; exact hi)) hw

theorem titsLocalWords_letters
    {ws : List (List ℤ)} (hws : ws ∈ titsLocalWords) {w : List ℤ}
    (hw : w ∈ ws) : lettersOK 13 w = true :=
  List.all_eq_true.1 (List.all_eq_true.1 titsLocalData_letters ws hws) w hw

theorem titsWordGroup_eq_closure_range (ws : List (List ℤ)) :
    titsWordGroup ws = Subgroup.closure {g | g ∈ ws.map (wordIn 13 titsT)} := by
  rw [titsWordGroup]
  congr 1
  ext g
  simp [List.mem_map]

theorem localChain_facts
    {S : Array (Array ℕ)} {k s : ℕ} (hk : k ≤ S.size) {b : List ℕ}
    (hb : (finList 1755 b).Nodup) {D : List (List ℤ)} {ws : List (List ℤ)}
    (hP : allPermsOK 1755 S = true)
    (hc : rawChainOK 1755 (S.extract 0 k) S (baseArr 1755 b) (wordsArr k s D) 4 = true)
    (hlen : ws.length = k) (hinit : initialWordsOK S ws = true) :
    ValidSchreier (RawSchreierDatum.ofArrays 1755 (by norm_num) S k hk (finList 1755 b) hb
        (wordsArr k s D)) ∧
      (RawSchreierDatum.ofArrays 1755 (by norm_num) S k hk (finList 1755 b) hb
        (wordsArr k s D)).original.toList = ws.map (wordIn 13 titsT) ∧
      (RawSchreierDatum.ofArrays 1755 (by norm_num) S k hk (finList 1755 b) hb
        (wordsArr k s D)).originalSubgroup = titsWordGroup ws ∧
      Nat.card (titsWordGroup ws) = (rawOrbitSizes 1755 S (baseArr 1755 b)).prod := by
  have hinit' : ∀ i < ws.length, lettersOK 13 ws[i]! = true ∧
      eqA 1755 S[i]! (wordArr 1755 titsDerivedArrs ws[i]!) = true := by
    intro i hi
    have := allLt_spec hinit hi
    simpa using this
  have horig : (RawSchreierDatum.ofArrays 1755 (by norm_num) S k hk (finList 1755 b) hb
      (wordsArr k s D)).original.toList = ws.map (wordIn 13 titsT) := by
    show (Vector.ofFn fun i : Fin k => permOfArr 1755 S[(i : ℕ)]!).toList = _
    rw [Vector.toList_ofFn]
    apply List.ext_getElem
    · simp [hlen]
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map]
      have hi : i < ws.length := by simpa using h2
      obtain ⟨hl, he⟩ := hinit' i hi
      rw [eq_of_eqA (rep_of_allPermsOK hP (by omega)) (rep_wordArr_titsT hl) he]
      rw [getElem!_pos ws i hi]
  have hsub : (RawSchreierDatum.ofArrays 1755 (by norm_num) S k hk (finList 1755 b) hb
      (wordsArr k s D)).originalSubgroup = titsWordGroup ws := by
    rw [RawSchreierDatum.originalSubgroup, horig, titsWordGroup_eq_closure_range]
  refine ⟨(valid_ofArrays hP (by norm_num) hc).1, horig, hsub, ?_⟩
  rw [← hsub]
  exact card_ofArrays hP (by norm_num) hc

theorem titsLocalWords_mem :
    titsHWords ∈ titsLocalWords ∧ titsSWords ∈ titsLocalWords ∧ titsNWords ∈ titsLocalWords ∧
      titsJWords ∈ titsLocalWords ∧ titsKWords ∈ titsLocalWords ∧
      titsRWords ∈ titsLocalWords := by
  simp [titsLocalWords]

theorem titsQH_facts :
    ValidSchreier titsQH ∧
    titsQH.original.toList = titsHWords.map (wordIn 13 titsT) ∧
    titsQH.originalSubgroup = titsH ∧ Nat.card titsH = 10240 := by
  obtain ⟨c, -, -, -, -, -, o, -, -, -, -, -, l, -, -, -, -, -, i, -⟩ := titsLocalChains_check
  obtain ⟨h1, h2, h3, h4⟩ := localChain_facts (hk := by rw [titsHArrs_size]; norm_num)
    (hb := by decide) titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c l i
  exact ⟨h1, h2, h3, by rw [titsH, h4, o]; rfl⟩

theorem titsQS_facts :
    ValidSchreier titsQS ∧
    titsQS.original.toList = titsSWords.map (wordIn 13 titsT) ∧
    titsQS.originalSubgroup = titsS ∧ Nat.card titsS = 2048 := by
  obtain ⟨-, c, -, -, -, -, -, o, -, -, -, -, -, l, -, -, -, -, -, i, -⟩ := titsLocalChains_check
  obtain ⟨h1, h2, h3, h4⟩ := localChain_facts (hk := by rw [titsSArrs_size]; norm_num)
    (hb := by decide) titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c l i
  exact ⟨h1, h2, h3, by rw [titsS, h4, o]; rfl⟩

theorem titsQN_facts :
    ValidSchreier titsQN ∧
    titsQN.original.toList = titsNWords.map (wordIn 13 titsT) ∧
    titsQN.originalSubgroup = titsN ∧ Nat.card titsN = 6144 := by
  obtain ⟨-, -, c, -, -, -, -, -, o, -, -, -, -, -, l, -, -, -, -, -, i, -⟩ :=
    titsLocalChains_check
  obtain ⟨h1, h2, h3, h4⟩ := localChain_facts (hk := by rw [titsNArrs_size]; norm_num)
    (hb := by decide) titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c l i
  exact ⟨h1, h2, h3, by rw [titsN, h4, o]; rfl⟩

theorem titsQJ_facts :
    ValidSchreier titsQJ ∧
    titsQJ.original.toList = titsJWords.map (wordIn 13 titsT) ∧
    titsQJ.originalSubgroup = titsJ ∧ Nat.card titsJ = 512 := by
  obtain ⟨-, -, -, c, -, -, -, -, -, o, -, -, -, -, -, l, -, -, -, -, -, i, -⟩ :=
    titsLocalChains_check
  obtain ⟨h1, h2, h3, h4⟩ := localChain_facts (hk := by rw [titsJArrs_size]; norm_num)
    (hb := by decide) titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c l i
  exact ⟨h1, h2, h3, by rw [titsJ, h4, o]; rfl⟩

theorem titsQK_facts :
    ValidSchreier titsQK ∧
    titsQK.original.toList = titsKWords.map (wordIn 13 titsT) ∧
    titsQK.originalSubgroup = titsK ∧ Nat.card titsK = 1024 := by
  obtain ⟨-, -, -, -, c, -, -, -, -, -, o, -, -, -, -, -, l, -, -, -, -, -, i, -⟩ :=
    titsLocalChains_check
  obtain ⟨h1, h2, h3, h4⟩ := localChain_facts (hk := by rw [titsKArrs_size]; norm_num)
    (hb := by decide) titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c l i
  exact ⟨h1, h2, h3, by rw [titsK, h4, o]; rfl⟩

theorem titsQR_facts :
    ValidSchreier titsQR ∧
    titsQR.original.toList = titsRWords.map (wordIn 13 titsT) ∧
    titsQR.originalSubgroup = titsR ∧ Nat.card titsR = 256 := by
  obtain ⟨-, -, -, -, -, c, -, -, -, -, -, o, -, -, -, -, -, l, -, -, -, -, -, i⟩ :=
    titsLocalChains_check
  obtain ⟨h1, h2, h3, h4⟩ := localChain_facts (hk := by rw [titsRArrs_size]; norm_num)
    (hb := by decide) titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c l i
  exact ⟨h1, h2, h3, by rw [titsR, h4, o]; rfl⟩

theorem titsDFlag_rep
    {j : ℕ} (hj : j < 2) : Rep 8775 titsDFlagArrs[j]! (titsDFlag j) := by
  obtain ⟨hu, hv, -, -⟩ := titsStab_check.1 j hj
  obtain ⟨lu, lv⟩ := titsLocalData_uv j hj
  rw [titsDFlagArrs, getElem!_ofFn_of_lt _ hj]
  have hsz : 4 ≤ titsFlagArrs.size := by rw [titsLocalData_check.1]
  have hP : ∀ i < 4, isInvA 8775 titsFlagArrs[i]! (invCand 8775 titsFlagArrs[i]!) = true :=
    fun i hi => isInvA_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.1
      (by rw [titsLocalData_check.1]; exact hi)
  exact rep_commArr (rep_wordArr hsz (fun _ hi => titsP_rep hi) hP lu)
    (rep_wordArr hsz (fun _ hi => titsP_rep hi) hP lv) hu hv

theorem titsDStar_rep
    {j : ℕ} (hj : j < 2) : Rep 2925 titsDStarArrs[j]! (titsDStar j) := by
  obtain ⟨-, -, hu, hv⟩ := titsStab_check.1 j hj
  obtain ⟨lu, lv⟩ := titsLocalData_uv j hj
  rw [titsDStarArrs, getElem!_ofFn_of_lt _ hj]
  have hsz : 4 ≤ titsAStarArrs.size := by rw [titsLocalData_check.2.1]
  have hP : ∀ i < 4, isInvA 2925 titsAStarArrs[i]! (invCand 2925 titsAStarArrs[i]!) = true :=
    fun i hi => isInvA_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [titsLocalData_check.2.1]; exact hi)
  exact rep_commArr (rep_wordArr hsz (fun _ hi => titsAStar_rep hi) hP lu)
    (rep_wordArr hsz (fun _ hi => titsAStar_rep hi) hP lv) hu hv

theorem titsTFlagArrs_size :
    titsTFlagArrs.size = 13 := by
  rw [size_of_strongOK titsStab_check.2.1, titsLocalData_derivLen]

theorem titsTStarArrs_size :
    titsTStarArrs.size = 13 := by
  rw [size_of_strongOK titsStab_check.2.2.1, titsLocalData_derivLen]

theorem titsTFlag_rep
    {i : ℕ} (hi : i < 13) : Rep 8775 titsTFlagArrs[i]! (titsTFlag i) :=
  rep_of_strongOK titsStab_check.2.1 (fun _ hj => titsDFlag_rep hj) i
    (by rw [titsTFlagArrs_size]; exact hi)

theorem titsTStar_rep
    {i : ℕ} (hi : i < 13) : Rep 2925 titsTStarArrs[i]! (titsTStar i) :=
  rep_of_strongOK titsStab_check.2.2.1 (fun _ hj => titsDStar_rep hj) i
    (by rw [titsTStarArrs_size]; exact hi)

theorem rep_wordArr_tflag
    {w : List ℤ} (hw : lettersOK 13 w = true) :
    Rep 8775 (wordArr 8775 titsTFlagArrs w) (wordIn 13 titsTFlag w) :=
  rep_wordArr (by rw [titsTFlagArrs_size]) (fun _ hi => titsTFlag_rep hi)
    (fun _ hi => isInvA_of_strongOK titsStab_check.2.1 (by rw [titsTFlagArrs_size]; exact hi)) hw

theorem rep_wordArr_tstar
    {w : List ℤ} (hw : lettersOK 13 w = true) :
    Rep 2925 (wordArr 2925 titsTStarArrs w) (wordIn 13 titsTStar w) :=
  rep_wordArr (by rw [titsTStarArrs_size]) (fun _ hi => titsTStar_rep hi)
    (fun _ hi => isInvA_of_strongOK titsStab_check.2.2.1 (by rw [titsTStarArrs_size]; exact hi)) hw

theorem range_le_of_closure {G M : Type*} [Group G] [Group M] (φ : G →* M) {T : Set M}
    (hT : T ⊆ φ.range) : Subgroup.closure T ≤ φ.range :=
  (Subgroup.closure_le _).2 hT

theorem card_comap_stabilizer {G X : Type*} [Group G] [Finite G] [Finite X]
    (φ : G →* Equiv.Perm X) (x₀ : X) (htr : ∀ x, ∃ g, φ g x₀ = x) :
    Nat.card ((MulAction.stabilizer (Equiv.Perm X) x₀).comap φ) * Nat.card X = Nat.card G := by
  let _ : MulAction G X := MulAction.compHom X φ
  have hst : (MulAction.stabilizer (Equiv.Perm X) x₀).comap φ = MulAction.stabilizer G x₀ := by
    ext g
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    rfl
  have horb : MulAction.orbit G x₀ = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    obtain ⟨g, hg⟩ := htr x
    exact ⟨g, hg⟩
  rw [hst, ← Subgroup.card_mul_index (MulAction.stabilizer G x₀), MulAction.index_stabilizer,
    horb, Set.ncard_univ]

theorem titsDFlag_transitive
    (x : Fin 8775) : ∃ g : titsD, titsDFlagAct g 0 = x := by
  have hrep : ∀ i < titsDFlagArrs.size, Rep 8775 titsDFlagArrs[i]! (titsDFlag i) :=
    fun i hi => titsDFlag_rep (by simpa [titsDFlagArrs] using hi)
  obtain ⟨g, hg, hgx⟩ := mem_orbit_rep titsStab_check.2.2.2.2.1 hrep x
  have hle : genGroup titsDFlagArrs titsDFlag ≤ titsDFlagAct.range := by
    refine range_le_of_closure _ ?_
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < 2 := by simpa [titsDFlagArrs] using hi
    exact ⟨⟨titsDGen i, titsDGen_mem_titsD hi'⟩, titsDFlagAct_dGen hi'⟩
  obtain ⟨h, rfl⟩ := hle hg
  refine ⟨h, ?_⟩
  rw [← hgx]
  congr 1
  apply Fin.ext
  have hl : (orbitForest 8775 titsDFlagArrs #[0]).1[(x : ℕ)]! = 0 := by
    have := (orbitLabelOK_parts titsStab_check.2.2.2.2.1).1 x x.2
    simp only [Array.size_singleton] at this
    omega
  simp [hl]

theorem titsDLine_transitive
    (x : Fin 2925) : ∃ g : titsD, titsDLineAct g 0 = x := by
  have hrep : ∀ i < titsDStarArrs.size, Rep 2925 titsDStarArrs[i]! (titsDStar i) :=
    fun i hi => titsDStar_rep (by simpa [titsDStarArrs] using hi)
  obtain ⟨g, hg, hgx⟩ := mem_orbit_rep titsStab_check.2.2.2.2.2.1 hrep x
  have hle : genGroup titsDStarArrs titsDStar ≤ titsDLineAct.range := by
    refine range_le_of_closure _ ?_
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < 2 := by simpa [titsDStarArrs] using hi
    exact ⟨⟨titsDGen i, titsDGen_mem_titsD hi'⟩, titsDLineAct_dGen hi'⟩
  obtain ⟨h, rfl⟩ := hle hg
  refine ⟨h, ?_⟩
  rw [← hgx]
  congr 1
  apply Fin.ext
  have hl : (orbitForest 2925 titsDStarArrs #[0]).1[(x : ℕ)]! = 0 := by
    have := (orbitLabelOK_parts titsStab_check.2.2.2.2.2.1).1 x x.2
    simp only [Array.size_singleton] at this
    omega
  simp [hl]

theorem titsDPoint_transitive
    (x : Fin 1755) : ∃ g : titsD, titsD.subtype g 0 = x := by
  have := titsD_pretransitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq titsD (0 : Fin 1755) x
  exact ⟨g, hg⟩

abbrev titsPointStab : Subgroup titsD :=
  (MulAction.stabilizer (Equiv.Perm (Fin 1755)) (0 : Fin 1755)).comap titsD.subtype

abbrev titsFlagStab :
    Subgroup titsD :=
  (MulAction.stabilizer (Equiv.Perm (Fin 8775)) (0 : Fin 8775)).comap titsDFlagAct

abbrev titsLineStab :
    Subgroup titsD :=
  (MulAction.stabilizer (Equiv.Perm (Fin 2925)) (0 : Fin 2925)).comap titsDLineAct

theorem card_titsPointStab : Nat.card titsPointStab = 10240 := by
  have h := card_comap_stabilizer titsD.subtype 0 titsDPoint_transitive
  rw [card_titsD, Nat.card_eq_fintype_card (α := Fin 1755), Fintype.card_fin] at h
  have h' : Nat.card titsPointStab * 1755 = 10240 * 1755 := by rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem card_titsFlagStab :
    Nat.card titsFlagStab = 2048 := by
  have h := card_comap_stabilizer titsDFlagAct 0 titsDFlag_transitive
  rw [card_titsD, Nat.card_eq_fintype_card (α := Fin 8775), Fintype.card_fin] at h
  have h' : Nat.card titsFlagStab * 8775 = 2048 * 8775 := by rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem card_titsLineStab :
    Nat.card titsLineStab = 6144 := by
  have h := card_comap_stabilizer titsDLineAct 0 titsDLine_transitive
  rw [card_titsD, Nat.card_eq_fintype_card (α := Fin 2925), Fintype.card_fin] at h
  have h' : Nat.card titsLineStab * 2925 = 6144 * 2925 := by rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem wordArr_fix_iff {n : ℕ} [NeZero n] {a : Array ℕ} {g : Equiv.Perm (Fin n)} (ha : Rep n a g)
    {p : ℕ} (hp : p < n) : a[p]! = p ↔ g (finPt n p) = finPt n p := by
  rw [ha.apply hp, finPt_eq hp, Fin.ext_iff]

theorem titsH_gen_fix
    {w : List ℤ} (hw : w ∈ titsHWords) : wordIn 13 titsT w 0 = 0 := by
  have h := List.all_eq_true.1 titsStab_check.2.2.2.2.2.2.1 w hw
  rw [beq_iff_eq] at h
  have := (wordArr_fix_iff (rep_wordArr_titsT (titsLocalWords_letters titsLocalWords_mem.1 hw))
    (by norm_num : 0 < 1755)).1 h
  simpa [finPt] using this

theorem titsS_gen_fix
    {w : List ℤ} (hw : w ∈ titsSWords) : wordIn 13 titsTFlag w 0 = 0 := by
  have h := List.all_eq_true.1 titsStab_check.2.2.2.2.2.2.2.1 w hw
  rw [beq_iff_eq] at h
  have := (wordArr_fix_iff (rep_wordArr_tflag (titsLocalWords_letters titsLocalWords_mem.2.1 hw))
    (by norm_num : 0 < 8775)).1 h
  simpa [finPt] using this

theorem titsR_gen_fix
    {w : List ℤ} (hw : w ∈ titsRWords) : wordIn 13 titsTFlag w 0 = 0 := by
  have h := List.all_eq_true.1 titsStab_check.2.2.2.2.2.2.2.2.1 w hw
  rw [beq_iff_eq] at h
  have := (wordArr_fix_iff
    (rep_wordArr_tflag (titsLocalWords_letters titsLocalWords_mem.2.2.2.2.2 hw))
    (by norm_num : 0 < 8775)).1 h
  simpa [finPt] using this

theorem titsN_gen_fix
    {w : List ℤ} (hw : w ∈ titsNWords) : wordIn 13 titsTStar w 0 = 0 := by
  have h := List.all_eq_true.1 titsStab_check.2.2.2.2.2.2.2.2.2.1 w hw
  rw [beq_iff_eq] at h
  have := (wordArr_fix_iff
    (rep_wordArr_tstar (titsLocalWords_letters titsLocalWords_mem.2.2.1 hw))
    (by norm_num : 0 < 2925)).1 h
  simpa [finPt] using this

theorem titsWordGroup_le_of {ws : List (List ℤ)} {K : Subgroup titsD}
    (h : ∀ w ∈ ws, (⟨wordIn 13 titsT w, wordIn_titsT_mem_titsD w⟩ : titsD) ∈ K) :
    titsWordGroup ws ≤ K.map titsD.subtype := by
  rw [titsWordGroup, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨_, h w hw, rfl⟩

theorem titsH_le_stab :
    titsH ≤ titsPointStab.map titsD.subtype :=
  titsWordGroup_le_of fun w hw => by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    exact titsH_gen_fix hw

theorem titsS_le_stab :
    titsS ≤ titsFlagStab.map titsD.subtype :=
  titsWordGroup_le_of fun w hw => by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, titsDFlagAct_word]
    exact titsS_gen_fix hw

theorem titsR_le_flagStab :
    titsR ≤ titsFlagStab.map titsD.subtype :=
  titsWordGroup_le_of fun w hw => by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, titsDFlagAct_word]
    exact titsR_gen_fix hw

theorem titsN_le_stab :
    titsN ≤ titsLineStab.map titsD.subtype :=
  titsWordGroup_le_of fun w hw => by
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, titsDLineAct_word]
    exact titsN_gen_fix hw

theorem titsH_eq_stab :
    titsH = titsPointStab.map titsD.subtype :=
  Subgroup.eq_of_le_of_card_ge titsH_le_stab (by
    rw [Subgroup.card_map_of_injective titsD.subtype_injective, card_titsPointStab,
      titsQH_facts.2.2.2])

theorem titsS_eq_stab :
    titsS = titsFlagStab.map titsD.subtype :=
  Subgroup.eq_of_le_of_card_ge titsS_le_stab (by
    rw [Subgroup.card_map_of_injective titsD.subtype_injective, card_titsFlagStab,
      titsQS_facts.2.2.2])

theorem titsN_eq_stab :
    titsN = titsLineStab.map titsD.subtype :=
  Subgroup.eq_of_le_of_card_ge titsN_le_stab (by
    rw [Subgroup.card_map_of_injective titsD.subtype_injective, card_titsLineStab,
      titsQN_facts.2.2.2])

theorem titsBeta_zero :
    titsBeta 0 = 0 := by
  apply Fin.ext
  rw [titsBeta_val]
  have h := allLt_spec titsStab_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num : 0 < 8775)
  rw [titsStab_check.2.2.2.2.2.2.2.2.2.2.2.2.1] at h
  simpa using h

theorem titsKappa_zero :
    titsKappa 0 = 0 := by
  apply Fin.ext
  rw [titsKappa_val]
  have h := allLt_spec titsStab_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by norm_num : 0 < 8775)
  rw [titsStab_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at h
  simpa using h

theorem titsS_le_titsH :
    titsS ≤ titsH := by
  rw [titsS_eq_stab, titsH_eq_stab]
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨g, ?_, rfl⟩
  have hg' : titsDFlagAct g 0 = 0 := hg
  show (g : Equiv.Perm (Fin 1755)) 0 = 0
  rw [← titsBeta_zero, ← titsBeta_dflag, hg']

theorem titsS_le_titsN :
    titsS ≤ titsN := by
  rw [titsS_eq_stab, titsN_eq_stab]
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨g, ?_, rfl⟩
  have hg' : titsDFlagAct g 0 = 0 := hg
  show titsDLineAct g 0 = 0
  rw [← titsKappa_zero, ← titsKappa_dflag, hg']

theorem titsR_le_titsS :
    titsR ≤ titsS := titsS_eq_stab ▸ titsR_le_flagStab

theorem card_subgroupOf_titsD {X : Subgroup (Equiv.Perm (Fin 1755))} (hX : X ≤ titsD) :
    Nat.card (X.subgroupOf titsD) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem titsS_index :
    (titsS.subgroupOf titsD).index = 8775 := by
  have h := Subgroup.card_mul_index (titsS.subgroupOf titsD)
  rw [card_subgroupOf_titsD titsS_le_titsD, titsQS_facts.2.2.2, card_titsD] at h
  have h' : 2048 * (titsS.subgroupOf titsD).index = 2048 * 8775 := by rw [h]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'

theorem titsS_isPGroup :
    IsPGroup 2 (titsS.subgroupOf titsD) :=
  IsPGroup.of_card (n := 11) (by
    rw [card_subgroupOf_titsD titsS_le_titsD, titsQS_facts.2.2.2]
    norm_num)

@[expose] def titsSylow :
    Sylow 2 titsD :=
  titsS_isPGroup.toSylow (by rw [titsS_index]; decide)

theorem coe_titsSylow :
    (titsSylow : Subgroup titsD) = titsS.subgroupOf titsD :=
  IsPGroup.toSylow_coe _ _

@[expose] def titsF5 : Set (Fin 8775) := {j | titsBeta j = 0}

@[expose] def titsF3 : Set (Fin 8775) := {j | titsKappa j = 0}

theorem mem_titsF5_iff
    (j : Fin 8775) : j ∈ titsF5 ↔ (j : ℕ) ∈ titsFiveFlags := by
  have h := allLt_spec titsStab_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j.2
  simp only [beq_iff_eq] at h
  have h2 : titsBetaArr[(j : ℕ)]! = 0 ↔ (j : ℕ) ∈ titsFiveFlags := by
    rw [← beq_iff_eq (a := titsBetaArr[(j : ℕ)]!) (b := 0), h, List.contains_iff_mem]
  rw [← h2, titsF5, Set.mem_ofPred_eq, ← titsBeta_val, Fin.ext_iff]
  rfl

theorem mem_titsF3_iff
    (j : Fin 8775) : j ∈ titsF3 ↔ (j : ℕ) ∈ titsThreeFlags := by
  have h := allLt_spec titsStab_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j.2
  simp only [beq_iff_eq] at h
  have h2 : titsKappaArr[(j : ℕ)]! = 0 ↔ (j : ℕ) ∈ titsThreeFlags := by
    rw [← beq_iff_eq (a := titsKappaArr[(j : ℕ)]!) (b := 0), h, List.contains_iff_mem]
  rw [← h2, titsF3, Set.mem_ofPred_eq, ← titsKappa_val, Fin.ext_iff]
  rfl

theorem titsF5_eq :
    titsF5 = (({0, 2, 5, 10, 20} : Finset (Fin 8775)) : Set (Fin 8775)) := by
  ext j
  rw [mem_titsF5_iff, titsStab_check.2.2.2.2.2.2.2.2.2.2.2.2.1]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
  rfl

theorem titsF3_eq :
    titsF3 = (({0, 1, 3} : Finset (Fin 8775)) : Set (Fin 8775)) := by
  ext j
  rw [mem_titsF3_iff, titsStab_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
  rfl

theorem titsF5_ncard :
    titsF5.ncard = 5 := by
  rw [titsF5_eq, Set.ncard_coe_finset]
  rfl

theorem titsF3_ncard :
    titsF3.ncard = 3 := by
  rw [titsF3_eq, Set.ncard_coe_finset]
  rfl

@[expose] def titsHFlag :
    titsH →* Equiv.Perm (Fin 8775) :=
  titsDFlagAct.comp (Subgroup.inclusion titsH_le_titsD)

@[expose] def titsNFlag :
    titsN →* Equiv.Perm (Fin 8775) :=
  titsDFlagAct.comp (Subgroup.inclusion titsN_le_titsD)

theorem titsH_fix
    (g : titsH) : (g : Equiv.Perm (Fin 1755)) 0 = 0 := by
  obtain ⟨d, hd, e⟩ := Subgroup.mem_map.1 (titsH_eq_stab.le g.2)
  rw [← e]
  exact hd

theorem titsN_fix
    (g : titsN) : titsDLineAct (Subgroup.inclusion titsN_le_titsD g) 0 = 0 := by
  obtain ⟨d, hd, e⟩ := Subgroup.mem_map.1 (titsN_eq_stab.le g.2)
  have : Subgroup.inclusion titsN_le_titsD g = d := Subtype.ext e.symm
  rw [this]
  exact hd

theorem titsHFlag_mem
    (g : titsH) (j : Fin 8775) : titsHFlag g j ∈ titsF5 ↔ j ∈ titsF5 := by
  show titsBeta (titsDFlagAct _ j) = 0 ↔ titsBeta j = 0
  rw [titsBeta_dflag]
  change (g : Equiv.Perm (Fin 1755)) (titsBeta j) = 0 ↔ _
  rw [← titsH_fix g, (g : Equiv.Perm (Fin 1755)).injective.eq_iff, titsH_fix]

theorem titsNFlag_mem
    (g : titsN) (j : Fin 8775) : titsNFlag g j ∈ titsF3 ↔ j ∈ titsF3 := by
  show titsKappa (titsDFlagAct (Subgroup.inclusion titsN_le_titsD g) j) = 0 ↔ titsKappa j = 0
  rw [titsKappa_dflag]
  constructor
  · intro h
    apply (titsDLineAct (Subgroup.inclusion titsN_le_titsD g)).injective
    rw [h, titsN_fix g]
  · intro h
    rw [h, titsN_fix g]

@[expose] def titsH5 :
    titsH →* Equiv.Perm titsF5 where
  toFun g := (titsHFlag g).subtypePerm (titsHFlag_mem g)
  map_one' := Equiv.ext fun j => Subtype.ext (by simp)
  map_mul' g h := Equiv.ext fun j => Subtype.ext (by
    show (titsHFlag (g * h)) j = (titsHFlag g) ((titsHFlag h) j)
    rw [map_mul]
    rfl)

@[expose] def titsN3 :
    titsN →* Equiv.Perm titsF3 where
  toFun g := (titsNFlag g).subtypePerm (titsNFlag_mem g)
  map_one' := Equiv.ext fun j => Subtype.ext (by simp)
  map_mul' g h := Equiv.ext fun j => Subtype.ext (by
    show (titsNFlag (g * h)) j = (titsNFlag g) ((titsNFlag h) j)
    rw [map_mul]
    rfl)

theorem titsH5_eq_one_iff
    (g : titsH) : titsH5 g = 1 ↔ ∀ j ∈ titsF5, titsHFlag g j = j := by
  constructor
  · intro h j hj
    have := congrArg (fun σ : Equiv.Perm titsF5 => (σ ⟨j, hj⟩ : Fin 8775)) h
    simpa [titsH5] using this
  · intro h
    exact Equiv.ext fun j => Subtype.ext (by simpa [titsH5] using h j j.2)

theorem titsN3_eq_one_iff
    (g : titsN) : titsN3 g = 1 ↔ ∀ j ∈ titsF3, titsNFlag g j = j := by
  constructor
  · intro h j hj
    have := congrArg (fun σ : Equiv.Perm titsF3 => (σ ⟨j, hj⟩ : Fin 8775)) h
    simpa [titsN3] using this
  · intro h
    exact Equiv.ext fun j => Subtype.ext (by simpa [titsN3] using h j j.2)

theorem iterA_rep {n : ℕ} {a : Array ℕ} {g : Equiv.Perm (Fin n)} (ha : Rep n a g) :
    ∀ (k : ℕ) (x : Fin n), iterA a k x = ((g ^ k) x : ℕ)
  | 0, x => rfl
  | k + 1, x => by
    rw [iterA, iterA_rep ha k x, ha.apply (Fin.isLt _), pow_succ', Equiv.Perm.mul_apply]

theorem powFixes_iff {n : ℕ} {a : Array ℕ} {g : Equiv.Perm (Fin n)} (ha : Rep n a g) (k : ℕ)
    {pts : List ℕ} (hpts : ∀ p ∈ pts, p < n) :
    powFixes a k pts = true ↔ ∀ x : Fin n, (x : ℕ) ∈ pts → (g ^ k) x = x := by
  rw [powFixes, List.all_eq_true]
  constructor
  · intro h x hx
    have := h x hx
    rw [beq_iff_eq, iterA_rep ha k x] at this
    exact Fin.ext this
  · intro h p hp
    have := h ⟨p, hpts p hp⟩ hp
    rw [beq_iff_eq]
    have e := iterA_rep ha k ⟨p, hpts p hp⟩
    rw [this] at e
    exact e

abbrev titsFix5 :
    Subgroup titsD :=
  (fixingSubgroup (Equiv.Perm (Fin 8775)) titsF5).comap titsDFlagAct

abbrev titsFix3 :
    Subgroup titsD :=
  (fixingSubgroup (Equiv.Perm (Fin 8775)) titsF3).comap titsDFlagAct

theorem titsJ_le_fix5 :
    titsJ ≤ titsFix5.map titsD.subtype :=
  titsWordGroup_le_of fun w hw => by
    rw [Subgroup.mem_comap, mem_fixingSubgroup_iff, titsDFlagAct_word]
    intro j hj
    rw [Equiv.Perm.smul_def]
    have h := List.all_eq_true.1 titsStab_check.2.2.2.2.2.2.2.2.2.2.1 w hw
    have hl := titsLocalWords_letters titsLocalWords_mem.2.2.2.1 hw
    have hj' := (mem_titsF5_iff j).1 hj
    have := List.all_eq_true.1 h j hj'
    rw [beq_iff_eq] at this
    simpa [finPt_eq j.2] using (wordArr_fix_iff (rep_wordArr_tflag hl) j.2).1 this

theorem titsK_le_fix3 :
    titsK ≤ titsFix3.map titsD.subtype :=
  titsWordGroup_le_of fun w hw => by
    rw [Subgroup.mem_comap, mem_fixingSubgroup_iff, titsDFlagAct_word]
    intro j hj
    rw [Equiv.Perm.smul_def]
    have h := List.all_eq_true.1 titsStab_check.2.2.2.2.2.2.2.2.2.2.2.1 w hw
    have hl := titsLocalWords_letters titsLocalWords_mem.2.2.2.2.1 hw
    have hj' := (mem_titsF3_iff j).1 hj
    have := List.all_eq_true.1 h j hj'
    rw [beq_iff_eq] at this
    simpa [finPt_eq j.2] using (wordArr_fix_iff (rep_wordArr_tflag hl) j.2).1 this

theorem titsFix5_le_flagStab :
    titsFix5 ≤ titsFlagStab := fun g hg => by
  rw [Subgroup.mem_comap, mem_fixingSubgroup_iff] at hg
  have := hg 0 (by rw [titsF5, Set.mem_ofPred_eq, titsBeta_zero])
  exact this

theorem titsFix3_le_flagStab :
    titsFix3 ≤ titsFlagStab := fun g hg => by
  rw [Subgroup.mem_comap, mem_fixingSubgroup_iff] at hg
  have := hg 0 (by rw [titsF3, Set.mem_ofPred_eq, titsKappa_zero])
  exact this

theorem titsJ_le_titsS :
    titsJ ≤ titsS := by
  rw [titsS_eq_stab]
  exact titsJ_le_fix5.trans (Subgroup.map_mono titsFix5_le_flagStab)

theorem titsK_le_titsS :
    titsK ≤ titsS := by
  rw [titsS_eq_stab]
  exact titsK_le_fix3.trans (Subgroup.map_mono titsFix3_le_flagStab)

theorem titsJ_le_titsH :
    titsJ ≤ titsH := titsJ_le_titsS.trans titsS_le_titsH

theorem titsK_le_titsN :
    titsK ≤ titsN := titsK_le_titsS.trans titsS_le_titsN

theorem titsJ_le_ker :
    titsJ.subgroupOf titsH ≤ titsH5.ker := by
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨d, hd, e⟩ := Subgroup.mem_map.1 (titsJ_le_fix5 hg)
  rw [MonoidHom.mem_ker, titsH5_eq_one_iff]
  intro j hj
  have hdg : Subgroup.inclusion titsH_le_titsD g = d := Subtype.ext e.symm
  show titsDFlagAct (Subgroup.inclusion titsH_le_titsD g) j = j
  rw [hdg]
  exact (mem_fixingSubgroup_iff _).1 hd j hj

theorem titsK_le_ker :
    titsK.subgroupOf titsN ≤ titsN3.ker := by
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨d, hd, e⟩ := Subgroup.mem_map.1 (titsK_le_fix3 hg)
  rw [MonoidHom.mem_ker, titsN3_eq_one_iff]
  intro j hj
  have hdg : Subgroup.inclusion titsN_le_titsD g = d := Subtype.ext e.symm
  show titsDFlagAct (Subgroup.inclusion titsN_le_titsD g) j = j
  rw [hdg]
  exact (mem_fixingSubgroup_iff _).1 hd j hj

theorem card_range_mul_card_ker {G M : Type*} [Group G] [Group M] [Finite G] (f : G →* M) :
    Nat.card f.range * Nat.card f.ker = Nat.card G := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

theorem titsH_word_mem {w : List ℤ} (hw : w ∈ titsHWords) : wordIn 13 titsT w ∈ titsH :=
  Subgroup.subset_closure ⟨w, hw, rfl⟩

theorem titsN_word_mem {w : List ℤ} (hw : w ∈ titsNWords) : wordIn 13 titsT w ∈ titsN :=
  Subgroup.subset_closure ⟨w, hw, rfl⟩

theorem titsHFlag_word
    {w : List ℤ} (hw : wordIn 13 titsT w ∈ titsH) :
    titsHFlag ⟨wordIn 13 titsT w, hw⟩ = wordIn 13 titsTFlag w :=
  titsDFlagAct_word w

theorem titsNFlag_word
    {w : List ℤ} (hw : wordIn 13 titsT w ∈ titsN) :
    titsNFlag ⟨wordIn 13 titsT w, hw⟩ = wordIn 13 titsTFlag w :=
  titsDFlagAct_word w

theorem powFixes_F5_iff
    {w : List ℤ} (hw : lettersOK 13 w = true) (k : ℕ) :
    powFixes (wordArr 8775 titsTFlagArrs w) k titsFiveFlags = true ↔
      ∀ j ∈ titsF5, (wordIn 13 titsTFlag w ^ k) j = j := by
  rw [powFixes_iff (rep_wordArr_tflag hw) k (by
    rw [titsStab_check.2.2.2.2.2.2.2.2.2.2.2.2.1]; decide)]
  simp only [mem_titsF5_iff]

theorem powFixes_F3_iff
    {w : List ℤ} (hw : lettersOK 13 w = true) (k : ℕ) :
    powFixes (wordArr 8775 titsTFlagArrs w) k titsThreeFlags = true ↔
      ∀ j ∈ titsF3, (wordIn 13 titsTFlag w ^ k) j = j := by
  rw [powFixes_iff (rep_wordArr_tflag hw) k (by
    rw [titsStab_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; decide)]
  simp only [mem_titsF3_iff]

theorem titsH5_pow_eq_one_iff
    {w : List ℤ} (hw : wordIn 13 titsT w ∈ titsH) (k : ℕ) :
    titsH5 ⟨wordIn 13 titsT w, hw⟩ ^ k = 1 ↔ ∀ j ∈ titsF5, (wordIn 13 titsTFlag w ^ k) j = j := by
  rw [← map_pow, titsH5_eq_one_iff, map_pow, titsHFlag_word]

theorem titsN3_pow_eq_one_iff
    {w : List ℤ} (hw : wordIn 13 titsT w ∈ titsN) (k : ℕ) :
    titsN3 ⟨wordIn 13 titsT w, hw⟩ ^ k = 1 ↔ ∀ j ∈ titsF3, (wordIn 13 titsTFlag w ^ k) j = j := by
  rw [← map_pow, titsN3_eq_one_iff, map_pow, titsNFlag_word]

theorem titsHWords_eq : titsHWords = [[3], [4], [13]] :=
  titsStab_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem mem_titsH_3 :
    wordIn 13 titsT [3] ∈ titsH := titsH_word_mem (by simp [titsHWords_eq])

theorem mem_titsH_3_4_13 : wordIn 13 titsT [3, 4, 13] ∈ titsH := by
  rw [show ([3, 4, 13] : List ℤ) = [3] ++ [4] ++ [13] from rfl, wordIn_append, wordIn_append]
  exact mul_mem (mul_mem mem_titsH_3 (titsH_word_mem (by simp [titsHWords_eq])))
    (titsH_word_mem (by simp [titsHWords_eq]))

theorem titsNWords_2_mem : titsNWords[2]! ∈ titsNWords := by
  rw [getElem!_pos titsNWords 2 (by
    rw [titsLocalChains_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; norm_num)]
  exact List.getElem_mem _

theorem titsNWords_3_mem : titsNWords[3]! ∈ titsNWords := by
  rw [getElem!_pos titsNWords 3 (by
    rw [titsLocalChains_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; norm_num)]
  exact List.getElem_mem _

theorem mem_titsN_2 :
    wordIn 13 titsT titsNWords[2]! ∈ titsN := titsN_word_mem titsNWords_2_mem

theorem mem_titsN_2_3 :
    wordIn 13 titsT (titsNWords[2]! ++ titsNWords[3]!) ∈ titsN := by
  rw [wordIn_append]
  exact mul_mem mem_titsN_2 (titsN_word_mem titsNWords_3_mem)

theorem letters_append {w₁ w₂ : List ℤ} (h₁ : lettersOK 13 w₁ = true)
    (h₂ : lettersOK 13 w₂ = true) : lettersOK 13 (w₁ ++ w₂) = true := by
  simp only [lettersOK, List.all_append, Bool.and_eq_true] at h₁ h₂ ⊢
  exact ⟨h₁, h₂⟩

theorem letters_N2 : lettersOK 13 titsNWords[2]! = true :=
  titsLocalWords_letters titsLocalWords_mem.2.2.1 titsNWords_2_mem

theorem letters_N3 : lettersOK 13 titsNWords[3]! = true :=
  titsLocalWords_letters titsLocalWords_mem.2.2.1 titsNWords_3_mem

theorem orderOf_titsH5_four :
    orderOf (titsH5 ⟨wordIn 13 titsT [3], mem_titsH_3⟩) = 4 := by
  have hl : lettersOK 13 [3] = true := by decide
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h4, h2, -⟩ := titsStab_check
  have hfin : titsH5 ⟨wordIn 13 titsT [3], mem_titsH_3⟩ ^ 2 ^ (1 + 1) = 1 :=
    (titsH5_pow_eq_one_iff _ 4).2 ((powFixes_F5_iff hl 4).1 h4)
  have hnot : ¬ titsH5 ⟨wordIn 13 titsT [3], mem_titsH_3⟩ ^ 2 ^ 1 = 1 := fun h => by
    have := (powFixes_F5_iff hl 2).2 ((titsH5_pow_eq_one_iff _ 2).1 h)
    rw [h2] at this
    exact Bool.false_ne_true this
  exact orderOf_eq_prime_pow hnot hfin

theorem orderOf_titsH5_five :
    orderOf (titsH5 ⟨wordIn 13 titsT [3, 4, 13], mem_titsH_3_4_13⟩) = 5 := by
  have hl : lettersOK 13 [3, 4, 13] = true := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h5, h1, -⟩ := titsStab_check
  refine orderOf_eq_prime ((titsH5_pow_eq_one_iff _ 5).2 ((powFixes_F5_iff hl 5).1 h5)) ?_
  intro h
  have := (powFixes_F5_iff hl 1).2 ((titsH5_pow_eq_one_iff _ 1).1 (by rw [pow_one]; exact h))
  rw [h1] at this
  exact Bool.false_ne_true this

theorem orderOf_titsN3_two :
    orderOf (titsN3 ⟨wordIn 13 titsT titsNWords[2]!, mem_titsN_2⟩) = 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h2, h1, -⟩ :=
    titsStab_check
  refine orderOf_eq_prime ((titsN3_pow_eq_one_iff _ 2).2 ((powFixes_F3_iff letters_N2 2).1 h2)) ?_
  intro h
  have := (powFixes_F3_iff letters_N2 1).2
    ((titsN3_pow_eq_one_iff _ 1).1 (by rw [pow_one]; exact h))
  rw [h1] at this
  exact Bool.false_ne_true this

theorem orderOf_titsN3_three :
    orderOf (titsN3 ⟨wordIn 13 titsT (titsNWords[2]! ++ titsNWords[3]!), mem_titsN_2_3⟩) = 3 := by
  have hl := letters_append letters_N2 letters_N3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h3, h1⟩ :=
    titsStab_check
  refine orderOf_eq_prime ((titsN3_pow_eq_one_iff _ 3).2 ((powFixes_F3_iff hl 3).1 h3)) ?_
  intro h
  have := (powFixes_F3_iff hl 1).2 ((titsN3_pow_eq_one_iff _ 1).1 (by rw [pow_one]; exact h))
  rw [h1] at this
  exact Bool.false_ne_true this

theorem dvd_card_range {G M : Type*} [Group G] [Group M] [Finite G] (f : G →* M) (g : G) :
    orderOf (f g) ∣ Nat.card f.range := by
  have := orderOf_dvd_natCard (⟨f g, g, rfl⟩ : f.range)
  rwa [← Subgroup.orderOf_coe] at this

theorem card_subgroupOf_eq {G : Type*} [Group G] {X Y : Subgroup G} (h : X ≤ Y) :
    Nat.card (X.subgroupOf Y) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem titsH5_range_ker :
    Nat.card titsH5.range = 20 ∧ titsH5.ker = titsJ.subgroupOf titsH := by
  have hcard := card_range_mul_card_ker titsH5
  rw [titsQH_facts.2.2.2] at hcard
  have h4 := dvd_card_range titsH5 ⟨_, mem_titsH_3⟩
  have h5 := dvd_card_range titsH5 ⟨_, mem_titsH_3_4_13⟩
  rw [orderOf_titsH5_four] at h4
  rw [orderOf_titsH5_five] at h5
  have h20 : 20 ∣ Nat.card titsH5.range :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h5
  have hJ : Nat.card (titsJ.subgroupOf titsH) = 512 := by
    rw [card_subgroupOf_eq titsJ_le_titsH, titsQJ_facts.2.2.2]
  have hle : 512 ≤ Nat.card titsH5.ker := hJ ▸ Subgroup.card_le_of_le titsJ_le_ker
  have hpos : 0 < Nat.card titsH5.range := Nat.card_pos
  have hR : Nat.card titsH5.range * 512 ≤ 10240 :=
    hcard ▸ Nat.mul_le_mul_left _ hle
  have hR20 : Nat.card titsH5.range = 20 := by omega
  rw [hR20] at hcard
  have hK : Nat.card titsH5.ker = 512 := by omega
  exact ⟨hR20, (Subgroup.eq_of_le_of_card_ge titsJ_le_ker (by rw [hK, hJ])).symm⟩

theorem titsN3_range_ker :
    Nat.card titsN3.range = 6 ∧ titsN3.ker = titsK.subgroupOf titsN := by
  have hcard := card_range_mul_card_ker titsN3
  rw [titsQN_facts.2.2.2] at hcard
  have h2 := dvd_card_range titsN3 ⟨_, mem_titsN_2⟩
  have h3 := dvd_card_range titsN3 ⟨_, mem_titsN_2_3⟩
  rw [orderOf_titsN3_two] at h2
  rw [orderOf_titsN3_three] at h3
  have h6 : 6 ∣ Nat.card titsN3.range :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hK0 : Nat.card (titsK.subgroupOf titsN) = 1024 := by
    rw [card_subgroupOf_eq titsK_le_titsN, titsQK_facts.2.2.2]
  have hle : 1024 ≤ Nat.card titsN3.ker := hK0 ▸ Subgroup.card_le_of_le titsK_le_ker
  have hpos : 0 < Nat.card titsN3.range := Nat.card_pos
  have hR : Nat.card titsN3.range * 1024 ≤ 6144 :=
    hcard ▸ Nat.mul_le_mul_left _ hle
  have hR6 : Nat.card titsN3.range = 6 := by omega
  rw [hR6] at hcard
  have hK : Nat.card titsN3.ker = 1024 := by omega
  exact ⟨hR6, (Subgroup.eq_of_le_of_card_ge titsK_le_ker (by rw [hK, hK0])).symm⟩

theorem AT_Tits_local_stabilizers_and_normal_cores :
    (ValidSchreier titsQH ∧ ValidSchreier titsQS ∧ ValidSchreier titsQN ∧ ValidSchreier titsQJ ∧
      ValidSchreier titsQK ∧ ValidSchreier titsQR) ∧
    (titsQH.original.toList = titsHWords.map (wordIn 13 titsT) ∧
      titsQS.original.toList = titsSWords.map (wordIn 13 titsT) ∧
      titsQN.original.toList = titsNWords.map (wordIn 13 titsT) ∧
      titsQJ.original.toList = titsJWords.map (wordIn 13 titsT) ∧
      titsQK.original.toList = titsKWords.map (wordIn 13 titsT) ∧
      titsQR.original.toList = titsRWords.map (wordIn 13 titsT)) ∧
    (titsQH.originalSubgroup = titsH ∧ titsQS.originalSubgroup = titsS ∧
      titsQN.originalSubgroup = titsN ∧ titsQJ.originalSubgroup = titsJ ∧
      titsQK.originalSubgroup = titsK ∧ titsQR.originalSubgroup = titsR) ∧
    (Nat.card titsH = 10240 ∧ Nat.card titsS = 2048 ∧ Nat.card titsN = 6144 ∧
      Nat.card titsJ = 512 ∧ Nat.card titsK = 1024 ∧ Nat.card titsR = 256) ∧
    titsH = ((MulAction.stabilizer (Equiv.Perm (Fin 1755)) (0 : Fin 1755)).comap
      titsD.subtype).map titsD.subtype ∧
    titsS = ((MulAction.stabilizer (Equiv.Perm (Fin 8775)) (0 : Fin 8775)).comap
      titsDFlagAct).map titsD.subtype ∧
    titsN = ((MulAction.stabilizer (Equiv.Perm (Fin 2925)) (0 : Fin 2925)).comap
      titsDLineAct).map titsD.subtype ∧
    (∃ P : Sylow 2 titsD, (P : Subgroup titsD) = titsS.subgroupOf titsD) ∧
    titsS ≤ titsH ⊓ titsN ∧
    titsF5.ncard = 5 ∧ titsF3.ncard = 3 ∧
    (∀ (g : titsH) (j : Fin 8775), titsHFlag g j ∈ titsF5 ↔ j ∈ titsF5) ∧
    (∀ (g : titsN) (j : Fin 8775), titsNFlag g j ∈ titsF3 ↔ j ∈ titsF3) ∧
    Nat.card titsH5.range = 20 ∧ Nat.card titsN3.range = 6 ∧
    titsH5.ker = titsJ.subgroupOf titsH ∧ titsN3.ker = titsK.subgroupOf titsN ∧
    (titsJ.subgroupOf titsH).Normal ∧ (titsK.subgroupOf titsN).Normal ∧
    titsJ ≤ titsS ∧ titsK ≤ titsS ∧ titsR ≤ titsS := by
  obtain ⟨hH1, hH2, hH3, hH4⟩ := titsQH_facts
  obtain ⟨hS1, hS2, hS3, hS4⟩ := titsQS_facts
  obtain ⟨hN1, hN2, hN3, hN4⟩ := titsQN_facts
  obtain ⟨hJ1, hJ2, hJ3, hJ4⟩ := titsQJ_facts
  obtain ⟨hK1, hK2, hK3, hK4⟩ := titsQK_facts
  obtain ⟨hR1, hR2, hR3, hR4⟩ := titsQR_facts
  obtain ⟨h5r, h5k⟩ := titsH5_range_ker
  obtain ⟨h3r, h3k⟩ := titsN3_range_ker
  refine ⟨⟨hH1, hS1, hN1, hJ1, hK1, hR1⟩, ⟨hH2, hS2, hN2, hJ2, hK2, hR2⟩,
    ⟨hH3, hS3, hN3, hJ3, hK3, hR3⟩, ⟨hH4, hS4, hN4, hJ4, hK4, hR4⟩, titsH_eq_stab,
    titsS_eq_stab, titsN_eq_stab, ⟨titsSylow, coe_titsSylow⟩,
    le_inf titsS_le_titsH titsS_le_titsN, titsF5_ncard, titsF3_ncard, titsHFlag_mem,
    titsNFlag_mem, h5r, h3r, h5k, h3k, h5k ▸ titsH5.normal_ker, h3k ▸ titsN3.normal_ker,
    titsJ_le_titsS, titsK_le_titsS, titsR_le_titsS⟩

end CFSG.Sporadic.Schreier.Tits
