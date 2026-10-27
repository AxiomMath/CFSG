module

public import CFSG.Sporadic.Fi22.Classes
public import CFSG.Sporadic.Fi22.Centralizer
public import CFSG.Sporadic.Fi22.NfpCert

public section

namespace CFSG.Sporadic.Fi22

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev nfpTabs : Array Table := nfpBase.map (tabOf orb)

noncomputable abbrev nfpU : Table := reconTab (closTree nfpTabs 6) (uImg.map (tabOf orb)) uImg[0]!

theorem nfp_parts :
    (∀ i, 1 ≤ i → i < 7 → closOK nfpTabs i = true) ∧ (closTree nfpTabs 6).pts.size = 3510 ∧
    (∀ i, 1 ≤ i → i < 6 → candCount orb nfpTabs i = nfpBounds[i]!) ∧
    (∀ i < 3510, ap nfpU i < 3510) ∧ invoOK 3510 nfpU = true ∧
    (∀ j < 6, ap nfpU nfpBase[j]! = uImg[j]!) ∧
    (∀ j < 6, compT 3510 nfpU (compT 3510 nfpTabs[j]! nfpU) = (uImg.map (tabOf orb))[j]!) ∧
    (∀ j < sylWords.size,
      sift TS LS sylQb chainQ 0 (apT (compT 3510 nfpU (compT 3510 LS[2 * j]! nfpU)) chainQ) =
        true) ∧
    ∀ k < (tabS 0).size, ∀ B ∈ tabS 1, leafNfp (tabS 0)[k]! B nfpU = true := by
  have h : nfpChecks orb 3 = true := nfp_certificate
  unfold nfpChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allIn_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, fun i hi => h4 i (Nat.zero_le _) hi, h5,
    fun j hj => h6 j (Nat.zero_le _) hj, fun j hj => h7 j (Nat.zero_le _) hj,
    fun j hj => h8 j (Nat.zero_le _) hj, fun k hk => Array.all_eq_true'.1 (parAll_eq_true h9 k hk)⟩

noncomputable abbrev idxPerm :
    J →* Equiv.Perm (Fin 3510) := MulAction.toPermHom J (Fin 3510)

theorem idxPerm_apply
    (h : J) (i : Fin 3510) : idxPerm h i = h • i := rfl

theorem idxPerm_injective : Function.Injective idxPerm := by
  intro g h e
  exact FaithfulSMul.eq_of_smul_eq_smul fun i : Fin 3510 => by
    rw [← idxPerm_apply, ← idxPerm_apply, e]

theorem idx_idxPerm
    (h : J) (i : ℕ) : idx 3510 (idxPerm h) i = idx 3510 h i := by
  unfold idx
  split_ifs <;> rfl

theorem rep_idxPerm
    {T : Table} {h : J} (hT : Rep 3510 T h) : Rep 3510 T (idxPerm h) :=
  fun i hi => by rw [idx_idxPerm]; exact hT i hi

theorem rep_of_rep_idxPerm
    {T : Table} {h : J} (hT : Rep 3510 T (idxPerm h)) : Rep 3510 T h :=
  fun i hi => by rw [← idx_idxPerm]; exact hT i hi

theorem idx_perm (σ : Equiv.Perm (Fin 3510)) {i : ℕ} (hi : i < 3510) :
    idx 3510 σ i = (σ ⟨i, hi⟩).val :=
  idx_of_lt σ hi

private theorem perm_eq_of_rep {T : Table} {σ π : Equiv.Perm (Fin 3510)} (h1 : Rep 3510 T σ)
    (h2 : Rep 3510 T π) : σ = π := by
  ext i
  have := (h1 i.val i.2).symm.trans (h2 i.val i.2)
  rwa [idx_perm σ i.2, idx_perm π i.2] at this

noncomputable abbrev tauIdx
    (i : Fin 3510) : Equiv.Perm (Fin 3510) := idxPerm (conjPt i.val)

theorem conjPt_mul_self
    {i : ℕ} (hi : i < 3510) : conjPt i * conjPt i = 1 := by
  rw [← pow_two, ← orderOf_of_mem_D (mem_D_iff.2 ⟨i, hi, rfl⟩)]
  exact pow_orderOf_eq_one _

theorem conjPt_inv
    {i : ℕ} (hi : i < 3510) : (conjPt i)⁻¹ = conjPt i :=
  inv_eq_of_mul_eq_one_right (conjPt_mul_self hi)

theorem tauIdx_mul_self
    (i : Fin 3510) : tauIdx i * tauIdx i = 1 := by
  rw [← map_mul, conjPt_mul_self i.2, map_one]

theorem tauIdx_inv (i : Fin 3510) : (tauIdx i)⁻¹ = tauIdx i :=
  inv_eq_of_mul_eq_one_right (tauIdx_mul_self i)

theorem tauIdx_apply
    (i j : Fin 3510) : tauIdx i j = (conjPt i.val : J) • j := rfl

theorem tauIdx_tauIdx
    (i j : Fin 3510) : tauIdx (tauIdx i j) = tauIdx i * tauIdx j * tauIdx i := by
  show idxPerm (conjPt (conjPt i.val • j).val) = _
  rw [conjPt_smul, map_mul, map_mul, conjPt_inv i.2]

theorem rep_tabOf
    {c : ℕ} (hc : c < 3510) : Rep 3510 (tabOf orb c) (tauIdx ⟨c, hc⟩) :=
  rep_idxPerm (rep_cTab c hc)

noncomputable def tauAut : Subgroup (Equiv.Perm (Fin 3510)) where
  carrier := {σ | ∀ i, σ * tauIdx i * σ⁻¹ = tauIdx (σ i)}
  mul_mem' {σ π} hσ hπ i := by
    simp only [Set.mem_ofPred_eq] at hσ hπ ⊢
    rw [mul_inv_rev, show σ * π * tauIdx i * (π⁻¹ * σ⁻¹) = σ * (π * tauIdx i * π⁻¹) * σ⁻¹ by group,
      hπ, hσ, Equiv.Perm.mul_apply]
  one_mem' i := by simp
  inv_mem' {σ} hσ i := by
    simp only [Set.mem_ofPred_eq] at hσ ⊢
    have h := hσ (σ⁻¹ i)
    rw [show σ (σ⁻¹ i) = i from σ.apply_symm_apply i] at h
    rw [← h]
    group

theorem mem_tauAut {σ : Equiv.Perm (Fin 3510)} :
    σ ∈ tauAut ↔ ∀ i, σ * tauIdx i * σ⁻¹ = tauIdx (σ i) := Iff.rfl

theorem tauAut_apply
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ tauAut) (i j : Fin 3510) :
    σ (tauIdx i j) = tauIdx (σ i) (σ j) := by
  rw [← mem_tauAut.1 hσ i]
  simp [Equiv.Perm.mul_apply]

theorem mem_tauAut_of_apply {σ : Equiv.Perm (Fin 3510)}
    (h : ∀ i j, σ (tauIdx i j) = tauIdx (σ i) (σ j)) : σ ∈ tauAut := by
  intro i
  ext j
  simp only [Equiv.Perm.mul_apply]
  rw [h, show σ (σ⁻¹ j) = j from σ.apply_symm_apply j]

theorem idxPerm_mem_tauAut (h : J) : idxPerm h ∈ tauAut := by
  intro i
  rw [← map_inv, ← map_mul, ← map_mul]
  show idxPerm (h * conjPt i.val * h⁻¹) = idxPerm (conjPt (h • i).val)
  rw [conjPt_smul]

theorem nfpBase_lt {j : ℕ} (hj : j < 6) : nfpBase[j]! < 3510 := by
  interval_cases j <;> decide

theorem uImg_lt {j : ℕ} (hj : j < 6) : uImg[j]! < 3510 := by
  interval_cases j <;> decide

@[expose] def nfpPt (j : ℕ) : Fin 3510 := ⟨nfpBase[j]! % 3510, Nat.mod_lt _ (by norm_num)⟩

theorem nfpPt_val {j : ℕ} (hj : j < 6) : (nfpPt j).val = nfpBase[j]! :=
  Nat.mod_eq_of_lt (nfpBase_lt hj)

noncomputable abbrev nfpG
    (l : ℕ) : Equiv.Perm (Fin 3510) := tauIdx (nfpPt l)

theorem nfpBase_size : nfpBase.size = 6 := rfl

theorem nfpTabs_get {j : ℕ} (hj : j < 6) : nfpTabs[j]! = tabOf orb nfpBase[j]! := by
  unfold nfpTabs
  rw [getElem!_pos _ j (by rw [Array.size_map, nfpBase_size]; exact hj), Array.getElem_map,
    getElem!_pos nfpBase j (by rw [nfpBase_size]; exact hj)]

theorem rep_nfpTabs
    {l : ℕ} (hl : l < 6) : Rep 3510 nfpTabs[l]! (nfpG l) := by
  rw [nfpTabs_get hl]
  have h := rep_tabOf (nfpBase_lt hl)
  have e : (⟨nfpBase[l]!, nfpBase_lt hl⟩ : Fin 3510) = nfpPt l := Fin.ext (nfpPt_val hl).symm
  rwa [e] at h

theorem nfpTreeFacts
    {i : ℕ} (h1 : 1 ≤ i) (h7 : i < 7) :
    TreeFacts 3510 (closTree nfpTabs i) (Array.range i) nfpG nfpBase[0]! :=
  treeOK_facts (fun l hl => rep_nfpTabs (by rw [Array.mem_range] at hl; omega))
    (nfp_parts.1 i h1 h7)

theorem nfpPt_zero : nfpPt 0 = ⟨nfpBase[0]!, nfpBase_lt (by norm_num)⟩ :=
  Fin.ext (nfpPt_val (by norm_num))

theorem nfpTree_pt
    {i : ℕ} (h1 : 1 ≤ i) (h7 : i < 7) {k : ℕ}
    (hk : k < (closTree nfpTabs i).pts.size) :
    (⟨ap (closTree nfpTabs i).pts k, (nfpTreeFacts h1 h7).pts_lt k hk⟩ : Fin 3510) =
      treeG (closTree nfpTabs i) nfpG k (nfpPt 0) := by
  apply Fin.ext
  show ap (closTree nfpTabs i).pts k = _
  rw [nfpPt_zero, ← idx_perm _ (nfpBase_lt (by norm_num)), (nfpTreeFacts h1 h7).elt k hk]

theorem commute_nfpG
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ tauAut) {l : ℕ}
    (hl : σ (nfpPt l) = nfpPt l) : σ * nfpG l = nfpG l * σ := by
  have h := mem_tauAut.1 hσ (nfpPt l)
  rw [hl] at h
  calc σ * nfpG l = σ * nfpG l * σ⁻¹ * σ := by group
    _ = nfpG l * σ := by rw [h]

theorem fix_nfpTree
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ tauAut) {i : ℕ} (h1 : 1 ≤ i) (h7 : i < 7)
    (hfix : ∀ j < i, σ (nfpPt j) = nfpPt j) {k : ℕ} (hk : k < (closTree nfpTabs i).pts.size) :
    σ ⟨ap (closTree nfpTabs i).pts k, (nfpTreeFacts h1 h7).pts_lt k hk⟩ =
      ⟨ap (closTree nfpTabs i).pts k, (nfpTreeFacts h1 h7).pts_lt k hk⟩ := by
  have hle : lettersGroup (Array.range i) nfpG ≤ Subgroup.centralizer {σ} := by
    unfold lettersGroup
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rw [Array.mem_range] at hl
    exact (commute_nfpG hσ (hfix l hl)).symm
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (hle ((nfpTreeFacts h1 h7).treeG_mem hk))
  rw [nfpTree_pt h1 h7 hk, ← Equiv.Perm.mul_apply, ← hc, Equiv.Perm.mul_apply, hfix 0 (by omega)]

theorem mem_nfpTree_six
    (v : Fin 3510) :
    ∃ k, ∃ hk : k < (closTree nfpTabs 6).pts.size,
      v = ⟨ap (closTree nfpTabs 6).pts k,
        (nfpTreeFacts (by norm_num) (by norm_num)).pts_lt k hk⟩ := by
  have hT := nfpTreeFacts (i := 6) (by norm_num) (by norm_num)
  have hsz := nfp_parts.2.1
  let f : Fin 3510 → Fin 3510 := fun k => ⟨ap (closTree nfpTabs 6).pts k.val,
    hT.pts_lt k.val (by rw [hsz]; exact k.2)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have e : ap (closTree nfpTabs 6).pts x.val = ap (closTree nfpTabs 6).pts y.val := Fin.mk.inj hxy
    exact Fin.ext (hT.pts_inj (by rw [hsz]; exact x.2) (by rw [hsz]; exact y.2) e)
  obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hf) v
  exact ⟨k.val, by rw [hsz]; exact k.2, hk.symm⟩

theorem eq_one_of_fix_nfpPt
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ tauAut)
    (hfix : ∀ j < 6, σ (nfpPt j) = nfpPt j) : σ = 1 := by
  ext v
  obtain ⟨k, hk, rfl⟩ := mem_nfpTree_six v
  rw [fix_nfpTree hσ (by norm_num) (by norm_num) hfix hk]
  rfl

noncomputable abbrev nfpCs (i : ℕ) : Array Table :=
  (closTree nfpTabs i).pts.map fun c => tabOf orb c.toNat

@[expose] noncomputable def nfpCand (i : ℕ) : Finset (Fin 3510) :=
  if i = 0 then Finset.univ else
    Finset.univ.filter fun v => candAt (closTree nfpTabs i).pts (nfpCs i) nfpBase[i]! v.val = true

theorem relKey_eq {c : ℕ} (hc : c < 3510) (v : Fin 3510) :
    relKey c (tabOf orb c) v.val =
      if v.val = c then 2 else if tauIdx ⟨c, hc⟩ v = v then 1 else 0 := by
  unfold relKey
  have h : ap (tabOf orb c) v.val = (tauIdx ⟨c, hc⟩ v).val :=
    (rep_tabOf hc v.val v.2).trans (idx_perm _ v.2)
  by_cases h1 : v.val = c
  · rw [ite_eq_left (beq_iff_eq.2 h1), ite_eq_left h1]
  · rw [ite_eq_right (by rwa [beq_iff_eq]), ite_eq_right h1, h]
    by_cases h2 : tauIdx ⟨c, hc⟩ v = v
    · rw [ite_eq_left (beq_iff_eq.2 (congrArg Fin.val h2)), ite_eq_left h2]
    · rw [ite_eq_right (fun e => h2 (Fin.ext (beq_iff_eq.1 e))), ite_eq_right h2]

theorem relKey_perm
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ tauAut) {c : ℕ} (hc : c < 3510)
    (hfix : σ ⟨c, hc⟩ = ⟨c, hc⟩) (v : Fin 3510) :
    relKey c (tabOf orb c) (σ v).val = relKey c (tabOf orb c) v.val := by
  rw [relKey_eq hc, relKey_eq hc]
  have e1 : (σ v).val = c ↔ v.val = c := by
    rw [← Fin.ext_iff (b := ⟨c, hc⟩), ← Fin.ext_iff (b := ⟨c, hc⟩)]
    conv_lhs => rw [← hfix]
    exact σ.injective.eq_iff
  have e2 : tauIdx ⟨c, hc⟩ (σ v) = σ v ↔ tauIdx ⟨c, hc⟩ v = v := by
    have h := tauAut_apply hσ ⟨c, hc⟩ v
    rw [hfix] at h
    rw [← h]
    exact σ.injective.eq_iff
  by_cases h1 : v.val = c
  · rw [ite_eq_left h1, ite_eq_left (e1.2 h1)]
  · rw [ite_eq_right h1, ite_eq_right (mt e1.1 h1)]
    by_cases h2 : tauIdx ⟨c, hc⟩ v = v
    · rw [ite_eq_left h2, ite_eq_left (e2.2 h2)]
    · rw [ite_eq_right h2, ite_eq_right (mt e2.1 h2)]

theorem nfpCs_get {i k : ℕ} (hk : k < (closTree nfpTabs i).pts.size) :
    (nfpCs i)[k]! = tabOf orb (ap (closTree nfpTabs i).pts k) := by
  unfold nfpCs
  rw [getElem!_pos _ k (by rw [Array.size_map]; exact hk), Array.getElem_map]
  unfold ap
  rw [getElem!_pos _ k hk]

theorem mem_nfpCand
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ tauAut) {i : ℕ} (hi : i < 6)
    (hfix : ∀ j < i, σ (nfpPt j) = nfpPt j) : σ (nfpPt i) ∈ nfpCand i := by
  unfold nfpCand
  split_ifs with h0
  · exact Finset.mem_univ _
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  unfold candAt
  rw [allIn_eq_true]
  intro k _ hk
  have h1 : 1 ≤ i := by omega
  have hc := (nfpTreeFacts h1 (by omega)).pts_lt k hk
  rw [beq_iff_eq, nfpCs_get hk, ← nfpPt_val hi]
  exact relKey_perm hσ hc (fix_nfpTree hσ h1 (by omega) hfix hk) (nfpPt i)

private theorem card_filter_fin (p : ℕ → Bool) :
    (Finset.univ.filter fun v : Fin 3510 => p v.val = true).card = (List.range 3510).countP p := by
  have h : (Finset.univ.filter fun v : Fin 3510 => p v.val = true).map Fin.valEmbedding =
      (Finset.range 3510).filter fun i => p i = true := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.2, hv⟩
    · rintro ⟨hi, hp⟩
      exact ⟨⟨i, hi⟩, hp, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h, List.countP_eq_length_filter]
  simp [Finset.card, Finset.filter, Finset.range, Multiset.range]

theorem card_nfpCand
    {i : ℕ} (h1 : 1 ≤ i) (h6 : i < 6) : (nfpCand i).card = nfpBounds[i]! := by
  unfold nfpCand
  rw [ite_eq_right (by omega), card_filter_fin, ← nfp_parts.2.2.1 i h1 h6]
  rfl

noncomputable abbrev nfpList : List (Fin 3510) := List.ofFn (n := 6) fun j => nfpPt j.val

theorem nfpList_length : nfpList.length = 6 := List.length_ofFn

theorem nfpList_getElem (i : ℕ) (hi : i < nfpList.length) : nfpList[i] = nfpPt i := by
  simp only [nfpList, List.getElem_ofFn]

theorem card_tauAut_le :
    Nat.card tauAut ≤ 129123503308800 := by
  have h := CFSG.Fischer.card_le_prod_of_candidates (G := tauAut) nfpList
    (fun g hg => by
      have : (g : Equiv.Perm (Fin 3510)) = 1 := eq_one_of_fix_nfpPt g.2 fun j hj => by
        have := hg (nfpPt j) (List.mem_ofFn.2 ⟨⟨j, hj⟩, rfl⟩)
        exact this
      exact Subtype.ext this)
    nfpCand
    (fun i hi g hg => by
      rw [nfpList_getElem]
      rw [nfpList_length] at hi
      refine mem_nfpCand g.2 hi fun j hj => ?_
      rw [CFSG.Fischer.mem_fixFirst] at hg
      have := hg j (by rw [nfpList_length]; omega)
      rwa [nfpList_getElem] at this)
  rw [nfpList_length] at h
  have hc0 : (nfpCand 0).card = 3510 := by
    unfold nfpCand; rw [ite_eq_left rfl, Finset.card_univ, Fintype.card_fin]
  have hprod : ∏ i ∈ Finset.range 6, (nfpCand i).card = 129123503308800 := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one, hc0,
      card_nfpCand (i := 1) (by norm_num) (by norm_num),
      card_nfpCand (i := 2) (by norm_num) (by norm_num),
      card_nfpCand (i := 3) (by norm_num) (by norm_num),
      card_nfpCand (i := 4) (by norm_num) (by norm_num),
      card_nfpCand (i := 5) (by norm_num) (by norm_num)]
    rfl
  rw [hprod] at h
  exact h

theorem nfpU_lt
    {i : ℕ} (hi : i < 3510) : ap nfpU i < 3510 := nfp_parts.2.2.2.1 i hi

theorem nfpU_nfpU
    {i : ℕ} (hi : i < 3510) : ap nfpU (ap nfpU i) = i := by
  have := allIn_eq_true.1 nfp_parts.2.2.2.2.1 i (Nat.zero_le _) hi
  rwa [beq_iff_eq] at this

@[expose] noncomputable def uOut : Equiv.Perm (Fin 3510) :=
  Function.Involutive.toPerm (fun i => ⟨ap nfpU i.val, nfpU_lt i.2⟩)
    (fun i => Fin.ext (nfpU_nfpU i.2))

theorem uOut_val (i : Fin 3510) : (uOut i).val = ap nfpU i.val := rfl

theorem rep_uOut :
    Rep 3510 nfpU uOut := fun i hi => by rw [idx_perm _ hi, uOut_val]

theorem uOut_mul_self : uOut * uOut = 1 := by
  ext i
  rw [Equiv.Perm.mul_apply, uOut_val, uOut_val, nfpU_nfpU i.2]
  rfl

theorem uOut_inv :
    uOut⁻¹ = uOut := inv_eq_of_mul_eq_one_right uOut_mul_self

theorem uOut_pt
    {j : ℕ} (hj : j < 6) : uOut (nfpPt j) = ⟨uImg[j]!, uImg_lt hj⟩ := by
  apply Fin.ext
  rw [uOut_val, nfpPt_val hj]
  exact nfp_parts.2.2.2.2.2.1 j hj

theorem uImg_size : uImg.size = 6 := rfl

theorem uImg_tab_get {j : ℕ} (hj : j < 6) :
    (uImg.map (tabOf orb))[j]! = tabOf orb uImg[j]! := by
  rw [getElem!_pos _ j (by rw [Array.size_map]; exact hj), Array.getElem_map,
    getElem!_pos uImg j (by rw [uImg_size]; exact hj)]

theorem uOut_conj_pt
    {j : ℕ} (hj : j < 6) :
    uOut * nfpG j * uOut⁻¹ = tauIdx (uOut (nfpPt j)) := by
  have h := nfp_parts.2.2.2.2.2.2.1 j hj
  rw [uImg_tab_get hj] at h
  have h1 : Rep 3510 (compT 3510 nfpU (compT 3510 nfpTabs[j]! nfpU)) (uOut * nfpG j * uOut⁻¹) := by
    rw [uOut_inv, mul_assoc]
    exact rep_uOut.compT ((rep_nfpTabs hj).compT rep_uOut)
  rw [h] at h1
  rw [uOut_pt hj]
  exact perm_eq_of_rep h1 (rep_tabOf (uImg_lt hj))

@[expose] def TauCompatAt
    (σ : Equiv.Perm (Fin 3510)) (x : Fin 3510) : Prop :=
  σ * tauIdx x * σ⁻¹ = tauIdx (σ x)

theorem tauCompatAt_tauIdx
    {σ : Equiv.Perm (Fin 3510)} {b x : Fin 3510} (hb : TauCompatAt σ b)
    (hx : TauCompatAt σ x) :
    TauCompatAt σ (tauIdx b x) := by
  unfold TauCompatAt at *
  have e : σ (tauIdx b x) = tauIdx (σ b) (σ x) := by
    rw [← hb]
    simp [Equiv.Perm.mul_apply]
  rw [e, tauIdx_tauIdx, tauIdx_tauIdx, ← hb, ← hx]
  group

theorem uOut_mem_tauAut :
    uOut ∈ tauAut := by
  have hT := nfpTreeFacts (i := 6) (by norm_num) (by norm_num)
  have hg : ∀ h ∈ lettersGroup (Array.range 6) nfpG, ∀ x,
      TauCompatAt uOut x → TauCompatAt uOut (h x) := by
    intro h hh
    unfold lettersGroup at hh
    induction hh using Subgroup.closure_induction_left with
    | one => intro x hx; exact hx
    | mul_left y hy z _ ih =>
      obtain ⟨l, hl, rfl⟩ := hy
      rw [Array.mem_range] at hl
      intro x hx
      rw [Equiv.Perm.mul_apply]
      exact tauCompatAt_tauIdx (uOut_conj_pt hl) (ih x hx)
    | inv_mul_cancel y hy z _ ih =>
      obtain ⟨l, hl, rfl⟩ := hy
      rw [Array.mem_range] at hl
      intro x hx
      rw [Equiv.Perm.mul_apply, tauIdx_inv]
      exact tauCompatAt_tauIdx (uOut_conj_pt hl) (ih x hx)
  intro v
  obtain ⟨k, hk, rfl⟩ := mem_nfpTree_six v
  rw [nfpTree_pt (by norm_num) (by norm_num) hk]
  exact hg _ (hT.treeG_mem hk) _ (uOut_conj_pt (j := 0) (by norm_num))

end CFSG.Sporadic.Fi22
