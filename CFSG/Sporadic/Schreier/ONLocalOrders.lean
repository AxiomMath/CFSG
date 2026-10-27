module

public import CFSG.Sporadic.Schreier.ONThreePoint
public import CFSG.Sporadic.Schreier.ONOuterDefs
public import CFSG.Sporadic.Schreier.ONCheckLocal

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates

theorem prep_qS
    {j : ℕ} (hj : j < 7) :
    PRep N qonStrongArrs[j]! (sgen j) ∧ PRep N qonInvArrs[j]! (sgen j)⁻¹ := by
  have hF := chainFacts qon_chain_cert.1
  have hs : j < qonStrongArrs.size := by rw [strong_parts.1]; exact hj
  have h1 := qon_arrays.prep_strong hF j hs
  have h2 := qon_arrays.prep_strongInv hF hs
  have e : strongAt QON j = sgen j := by
    rw [strongAt_of_lt QON (by rw [cert_on_schreier_action_data.2.1]; exact hj)]
    exact cert_on_schreier_action_data.2.2.2.2.1 ⟨j, _⟩
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

theorem prep_wordArr
    {w : List ℤ} (hw : plettersOK 7 w = true) : PRep N (wordArr w) (evalS w) :=
  prep_pword (gs := sgen) (fun _ hh => (prep_qS hh).1) (fun _ hh => (prep_qS hh).2) w hw

theorem prep_wordArrs
    {ws : Array (List ℤ)} (hw : ∀ w ∈ ws.toList, plettersOK 7 w = true) :
    ∀ j (hj : j < (evalList ws).length), PRep N (wordArrs ws)[j]! (evalList ws)[j] := by
  intro j hj
  have hj' : j < ws.size := by simpa [evalList] using hj
  rw [wordArrs, pwords_eq, getElem!_map' _ _ hj']
  simp only [evalList, List.getElem_map, Array.getElem_toList]
  rw [getElem!_pos ws j hj']
  exact prep_wordArr (hw _ (by simp))

theorem wordArrs_size
    (ws : Array (List ℤ)) : (wordArrs ws).size = (evalList ws).length := by
  simp [wordArrs, pwords_eq, evalList]

theorem words_ok :
    (∀ w ∈ Data.TWords.toList, plettersOK 7 w = true) ∧
      (∀ w ∈ Data.MWords.toList, plettersOK 7 w = true) ∧
      (∀ w ∈ Data.LWords.toList, plettersOK 7 w = true) ∧
      (∀ w ∈ Data.intersectionWords.toList, plettersOK 7 w = true) ∧
      plettersOK 7 Data.zWord = true ∧ plettersOK 7 Data.centerGeneratorWord = true ∧
      plettersOK 7 Data.tWord = true ∧ plettersOK 7 Data.pairConjugatorWord = true := by
  decide

theorem onTgens_length :
    onTgens.length = 6 := by simp [onTgens, evalList]; decide
theorem onMgens_length :
    onMgens.length = 3 := by simp [onMgens, evalList]; decide
theorem onLgens_length :
    onLgens.length = 2 := by simp [onLgens, evalList]; decide
theorem onDgens_length :
    onDgens.length = 4 := by simp [onDgens, evalList]; decide

theorem prep_onc :
    PRep N (wordArr Data.pairConjugatorWord) onc :=
  prep_wordArr words_ok.2.2.2.2.2.2.2

theorem prep_onc_inv :
    PRep N (pinvCand nPts (wordArr Data.pairConjugatorWord)) onc⁻¹ :=
  prep_inv_of_pisInv prep_onc seed_invs_cert.2.2

theorem onc_mem :
    onc ∈ Pv := evalS_mem _

theorem prep_wm :
    ∀ j (hj : j < onWMgens.length),
    PRep N (commGens nPts (wordArrs Data.MWords) Data.MCommutatorSpecs)[j]! onWMgens[j] := by
  intro j hj
  have hj' : j < Data.MCommutatorSpecs.size := by simpa [onWMgens] using hj
  rw [commGens_eq, getElem!_map' _ _ hj']
  simp only [onWMgens, List.getElem_map, Array.getElem_toList]
  rw [getElem!_pos _ j hj']
  have hspec : ∀ s ∈ Data.MCommutatorSpecs.toList, (1 ≤ s.1 ∧ s.1 ≤ 3) ∧
      (1 ≤ s.2.1 ∧ s.2.1 ≤ 3) ∧ s.2.2 ≤ 3 := by decide
  obtain ⟨ha, hb, hk⟩ := hspec Data.MCommutatorSpecs[j] (by simp)
  have h3 : (evalList Data.MWords).length = 3 := onMgens_length
  rw [← h3] at ha hb hk
  exact prep_commArr (prep_wordArrs words_ok.2.1) (fun j hj => allBelowN_spec seed_invs_cert.1
    (by omega)) ha hb hk

theorem prep_wl :
    ∀ j (hj : j < onWLgens.length),
    PRep N (commGens nPts (wordArrs Data.LWords) Data.LCommutatorSpecs)[j]! onWLgens[j] := by
  intro j hj
  have hj' : j < Data.LCommutatorSpecs.size := by simpa [onWLgens] using hj
  rw [commGens_eq, getElem!_map' _ _ hj']
  simp only [onWLgens, List.getElem_map, Array.getElem_toList]
  rw [getElem!_pos _ j hj']
  have hspec : ∀ s ∈ Data.LCommutatorSpecs.toList, (1 ≤ s.1 ∧ s.1 ≤ 2) ∧
      (1 ≤ s.2.1 ∧ s.2.1 ≤ 2) ∧ s.2.2 ≤ 2 := by decide
  obtain ⟨ha, hb, hk⟩ := hspec Data.LCommutatorSpecs[j] (by simp)
  have h2 : (evalList Data.LWords).length = 2 := onLgens_length
  rw [← h2] at ha hb hk
  exact prep_commArr (prep_wordArrs words_ok.2.2.1) (fun j hj => allBelowN_spec seed_invs_cert.2.1
    (by omega)) ha hb hk

theorem commSpec_mem {G : Type*} [Group G] {H : Subgroup G} {g : List G} (hg : ∀ x ∈ g, x ∈ H)
    (s : ℕ × ℕ × ℕ) : commSpec g s ∈ H := by
  have hd : ∀ i, g.getD i 1 ∈ H := by
    intro i
    by_cases hi : i < g.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hg _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact one_mem H
  unfold commSpec listComm
  split_ifs
  · exact mul_mem (mul_mem (mul_mem (hd _) (hd _)) (inv_mem (hd _))) (inv_mem (hd _))
  · exact mul_mem (mul_mem (hd _) (mul_mem (mul_mem (mul_mem (hd _) (hd _)) (inv_mem (hd _)))
      (inv_mem (hd _)))) (inv_mem (hd _))

theorem onWMgens_mem
    {g : Equiv.Perm (Fin N)} (hg : g ∈ onWMgens) : g ∈ Pv := by
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hg
  exact commSpec_mem (fun x hx => evalList_mem hx) s

theorem onWLgens_mem
    {g : Equiv.Perm (Fin N)} (hg : g ∈ onWLgens) : g ∈ Pv := by
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hg
  exact commSpec_mem (fun x hx => evalList_mem hx) s

theorem getElem!_append_left' {α : Type*} [Inhabited α] (a b : Array α) {j : ℕ}
    (hj : j < a.size) : (a ++ b)[j]! = a[j]! := by
  rw [getElem!_pos _ j (by simp; omega), getElem!_pos a j hj, Array.getElem_append_left hj]

theorem getElem!_append_right' {α : Type*} [Inhabited α] (a b : Array α) {j : ℕ}
    (hj : a.size ≤ j) : (a ++ b)[j]! = b[j - a.size]! := by
  by_cases h : j - a.size < b.size
  · rw [getElem!_pos _ j (by simp; omega), getElem!_pos b (j - a.size) h,
      Array.getElem_append_right (by omega)]
  · rw [getElem!_neg _ j (by simp; omega), getElem!_neg b (j - a.size) h]

theorem prep_append {a b : Array (Array ℕ)} {la lb : List (Equiv.Perm (Fin N))}
    (ha : a.size = la.length) (hA : ∀ j (hj : j < la.length), PRep N a[j]! la[j])
    (hB : ∀ j (hj : j < lb.length), PRep N b[j]! lb[j]) :
    ∀ j (hj : j < (la ++ lb).length), PRep N (a ++ b)[j]! (la ++ lb)[j] := by
  intro j hj
  by_cases h : j < la.length
  · rw [List.getElem_append_left h, getElem!_append_left' a b (by omega)]
    exact hA j h
  · rw [List.getElem_append_right (by omega), getElem!_append_right' a b (by omega), ha]
    exact hB _ _

theorem jointArrs_eq : jointArrs = wordArrs Data.MWords ++
    conjAll nPts (wordArr Data.pairConjugatorWord)
      (pinvCand nPts (wordArr Data.pairConjugatorWord)) (wordArrs Data.MWords) := rfl

theorem prep_onMgens :
    ∀ j (hj : j < onMgens.length), PRep N (wordArrs Data.MWords)[j]! onMgens[j] :=
  prep_wordArrs words_ok.2.1

theorem prep_conj {t c ci : Array ℕ} {g x : Equiv.Perm (Fin N)} (hc : PRep N c x)
    (hci : PRep N ci x⁻¹) (ht : PRep N t g) :
    PRep N (pcomp nPts c (pcomp nPts t ci)) (x * g * x⁻¹) := by
  have := prep_pcomp hc (prep_pcomp ht hci)
  rwa [← mul_assoc] at this

theorem prep_conjAll {g : Array (Array ℕ)} {gl : List (Equiv.Perm (Fin N))} {c ci : Array ℕ}
    {x : Equiv.Perm (Fin N)} (hc : PRep N c x) (hci : PRep N ci x⁻¹) (hsz : g.size = gl.length)
    (hg : ∀ j (hj : j < gl.length), PRep N g[j]! gl[j]) :
    ∀ j (hj : j < (gl.map fun y => x * y * x⁻¹).length),
      PRep N (conjAll nPts c ci g)[j]! (gl.map fun y => x * y * x⁻¹)[j] := by
  intro j hj
  have hj' : j < gl.length := by simpa using hj
  rw [conjAll_eq, getElem!_map' _ _ (by omega), List.getElem_map]
  exact prep_conj hc hci (hg j hj')

theorem prep_joint :
    ∀ j (hj : j < onJgens.length), PRep N jointArrs[j]! onJgens[j] := by
  have hsz : (wordArrs Data.MWords).size = onMgens.length := wordArrs_size _
  rw [jointArrs_eq]
  exact prep_append hsz prep_onMgens (prep_conjAll prep_onc prep_onc_inv hsz prep_onMgens)

theorem jointArrs_size :
    jointArrs.size = onJgens.length := by
  simp [jointArrs, conjAll_eq, wordArrs_size, onJgens, onMgens]

theorem onJgens_mem
    {g : Equiv.Perm (Fin N)} (hg : g ∈ onJgens) : g ∈ Pv := by
  rcases List.mem_append.1 hg with hg | hg
  · exact evalList_mem hg
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
    exact mul_mem (mul_mem onc_mem (evalList_mem hx)) (inv_mem onc_mem)

structure LocalFacts
    (Q : RawSchreierDatum N) (S : Array (Array ℕ)) (ch : Data.BigChain) :
    Prop where
  arrays : CArrays Q Q.originalCount S ch.base ch.strongWords
  chain : pointChainOK nPts Q.originalCount S ch.base ch.strongWords 4 = true
  point : ValidPointSchreier Q
  valid : ValidSchreier Q
  le : Q.originalSubgroup ≤ Pv
  stab : Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {b | b ∈ Q.base.toList} = ⊥
  card : Nat.card Q.originalSubgroup = ch.orbitSizes.toList.prod
  base : Q.base.toList = base3

theorem base3_set : {b | b ∈ base3} = threeBase := by
  ext x
  simp [base3, threeBase]

theorem bigBase_map_val {ch : Data.BigChain} (h : ∀ i < ch.base.size, ch.base[i]! < nPts) :
    (bigBase ch).map Fin.val = ch.base.toList := by
  apply List.ext_getElem (by simp [bigBase])
  intro k h1 h2
  simp only [bigBase, ptN, List.map_map, List.getElem_map, Function.comp_apply,
    Array.getElem_toList]
  have hk : k < ch.base.size := by simpa using h2
  have := h k hk
  rw [getElem!_pos _ k hk] at this
  exact Nat.mod_eq_of_lt this

theorem bigChain_originalSubgroup (ch : Data.BigChain) (orig : List (Equiv.Perm (Fin N))) (hk hb) :
    (bigChain ch orig hk hb).originalSubgroup = Subgroup.closure {g | g ∈ orig} := by
  rw [RawSchreierDatum.originalSubgroup, bigChain, ofWords_original_toList]

theorem localFacts_of
    (ch : Data.BigChain) (orig : List (Equiv.Perm (Fin N)))
    (hk : orig.length ≤ ch.strongWords.size) (hb : (bigBase ch).Nodup)
    (origArr : Array (Array ℕ)) (hsz : origArr.size = orig.length)
    (hrep : ∀ j (hj : j < orig.length), PRep N origArr[j]! orig[j])
    (hP : ∀ g ∈ orig, g ∈ Pv) (hbase : bigBase ch = base3)
    (h : localChainOK origArr ch = true) :
    LocalFacts (bigChain ch orig hk hb) (extendStrong nPts origArr ch.strongWords) ch := by
  simp only [localChainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨-, hfirst⟩, hchain⟩, hsizes⟩ := h
  rw [hsz] at hfirst hchain
  have hF := chainFacts hchain
  have hA : CArrays (bigChain ch orig hk hb) orig.length
      (extendStrong nPts origArr ch.strongWords) ch.base ch.strongWords :=
    ofWords_arrays hF.words_size.symm
      (fun j hj => prep_of_peq (allBelowN_spec hfirst hj) (hrep j hj)) (bigBase_map_val hF.base_lt)
  obtain ⟨hpt, horb⟩ := validPointSchreier_of_pointChainOK hA (by norm_num) hchain
  have hle : (bigChain ch orig hk hb).originalSubgroup ≤ Pv := by
    rw [bigChain_originalSubgroup, Subgroup.closure_le]
    exact fun g hg => hP g hg
  have hbase' : (bigChain ch orig hk hb).base.toList = base3 := by
    rw [← hbase]
    simp [bigChain, RawSchreierDatum.ofWords]
  have hstab : Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N))
      {b | b ∈ (bigChain ch orig hk hb).base.toList} = ⊥ := by
    rw [hbase', base3_set]
    exact pv_inf_fixing_three
  have hV := ((bigChain ch orig hk hb).certified_base_point_sift_soundness hpt
    (eq_bot_iff.2 fun g hg => by
      rw [← hstab]
      exact ⟨hle hg.1, hg.2⟩)).1
  refine ⟨hA, hchain, hpt, hV, hle, hstab, ?_, hbase'⟩
  rw [card_eq_prod_cOrbitSizes hV hA.base_size horb, hsizes]

theorem LocalFacts.mem
    {Q : RawSchreierDatum N} {S : Array (Array ℕ)} {ch : Data.BigChain}
    (hL : LocalFacts Q S ch) {g : Array ℕ} {G : Equiv.Perm (Fin N)} (hg : PRep N g G)
    (hG : G ∈ Pv)
    (h : memPoint (levelsOf nPts S ch.base) (invsOf nPts S ch.base) ch.base g = true) :
    G ∈ Q.originalSubgroup :=
  mem_of_memPoint hL.arrays hL.chain hL.point hL.le hL.stab hg hG h

theorem tFacts :
    LocalFacts onTChain (extendStrong nPts (wordArrs Data.TWords) Data.TChain.strongWords)
      Data.TChain :=
  localFacts_of _ _ _ _ _ (wordArrs_size _) (prep_wordArrs words_ok.1)
    (fun _ hg => evalList_mem hg) bigBase_T t_chain_cert

theorem mFacts :
    LocalFacts onMChain (extendStrong nPts (wordArrs Data.MWords) Data.MChain.strongWords)
      Data.MChain :=
  localFacts_of _ _ _ _ _ (wordArrs_size _) (prep_wordArrs words_ok.2.1)
    (fun _ hg => evalList_mem hg) bigBase_M m_chain_cert

theorem lFacts :
    LocalFacts onLChain (extendStrong nPts (wordArrs Data.LWords) Data.LChain.strongWords)
      Data.LChain :=
  localFacts_of _ _ _ _ _ (wordArrs_size _) (prep_wordArrs words_ok.2.2.1)
    (fun _ hg => evalList_mem hg) bigBase_L l_chain_cert

theorem mcommFacts :
    LocalFacts onMcommChain (extendStrong nPts
      (commGens nPts (wordArrs Data.MWords) Data.MCommutatorSpecs) Data.McommChain.strongWords)
      Data.McommChain :=
  localFacts_of _ _ _ _ _ (by simp [commGens_eq, onWMgens]) prep_wm
    (fun _ hg => onWMgens_mem hg) bigBase_Mcomm mcomm_chain_cert

theorem lcommFacts :
    LocalFacts onLcommChain (extendStrong nPts
      (commGens nPts (wordArrs Data.LWords) Data.LCommutatorSpecs) Data.LcommChain.strongWords)
      Data.LcommChain :=
  localFacts_of _ _ _ _ _ (by simp [commGens_eq, onWLgens]) prep_wl
    (fun _ hg => onWLgens_mem hg) bigBase_Lcomm lcomm_chain_cert

theorem jointFacts :
    LocalFacts onJointChain (extendStrong nPts jointArrs Data.jointChain.strongWords)
      Data.jointChain :=
  localFacts_of _ _ _ _ _ jointArrs_size prep_joint (fun _ hg => onJgens_mem hg) bigBase_joint
    joint_chain_cert

theorem onTChain_sub :
    onTChain.originalSubgroup = onT := bigChain_originalSubgroup _ _ _ _
theorem onMChain_sub :
    onMChain.originalSubgroup = onM := bigChain_originalSubgroup _ _ _ _
theorem onLChain_sub :
    onLChain.originalSubgroup = onL := bigChain_originalSubgroup _ _ _ _
theorem onMcommChain_sub :
    onMcommChain.originalSubgroup = onWM :=
  bigChain_originalSubgroup _ _ _ _
theorem onLcommChain_sub :
    onLcommChain.originalSubgroup = onWL :=
  bigChain_originalSubgroup _ _ _ _

theorem onJointChain_sub :
    onJointChain.originalSubgroup = onM ⊔ onM1 := by
  rw [onJointChain, bigChain_originalSubgroup, onM1, onM, MonoidHom.map_closure,
    ← Subgroup.closure_union]
  congr 1
  ext g
  simp [onJgens, List.mem_append, MulAut.conj_apply]

theorem onT_le :
    onT ≤ Pv := onTChain_sub ▸ tFacts.le
theorem onM_le :
    onM ≤ Pv := onMChain_sub ▸ mFacts.le
theorem onL_le :
    onL ≤ Pv := onLChain_sub ▸ lFacts.le

theorem card_onT :
    Nat.card onT = 512 := by
  rw [← onTChain_sub, tFacts.card]
  decide

theorem card_onM :
    Nat.card onM = 161280 := by
  rw [← onMChain_sub, mFacts.card]
  decide

theorem card_onL :
    Nat.card onL = 80640 := by
  rw [← onLChain_sub, lFacts.card]
  decide

theorem card_onWM :
    Nat.card onWM = 80640 := by
  rw [← onMcommChain_sub, mcommFacts.card]
  decide

theorem card_onWL :
    Nat.card onWL = 80640 := by
  rw [← onLcommChain_sub, lcommFacts.card]
  decide

theorem card_joint :
    Nat.card (onM ⊔ onM1 : Subgroup (Equiv.Perm (Fin N))) = 460815505920 := by
  rw [← onJointChain_sub, jointFacts.card]
  decide

theorem card_onT_subgroupOf :
    Nat.card (onT.subgroupOf Pv) = 512 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onT_le).toEquiv, card_onT]

theorem onT_index :
    (onT.subgroupOf Pv).index = 900030285 := by
  have h := (onT.subgroupOf Pv).card_mul_index
  rw [card_onT_subgroupOf, card_Pv] at h
  omega

theorem onT_isPGroup :
    IsPGroup 2 (onT.subgroupOf Pv) :=
  IsPGroup.of_card (n := 9) (by rw [card_onT_subgroupOf]; norm_num)

theorem onT_not_dvd_index :
    ¬ 2 ∣ (onT.subgroupOf Pv).index := by
  rw [onT_index]
  decide

@[expose] def onTSylow :
    Sylow 2 Pv :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  onT_isPGroup.toSylow onT_not_dvd_index

theorem onTSylow_coe :
    (onTSylow : Subgroup Pv) = onT.subgroupOf Pv := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.toSylow_coe onT_isPGroup onT_not_dvd_index


theorem at_on_local_subgroup_orders :
    ValidPointSchreier onTChain ∧ ValidSchreier onTChain ∧
      ValidPointSchreier onMChain ∧ ValidSchreier onMChain ∧
      ValidPointSchreier onLChain ∧ ValidSchreier onLChain ∧
      ValidPointSchreier onMcommChain ∧ ValidSchreier onMcommChain ∧
      ValidPointSchreier onLcommChain ∧ ValidSchreier onLcommChain ∧
      ValidPointSchreier onJointChain ∧ ValidSchreier onJointChain ∧
      onTChain.base.toList = base3 ∧ onMChain.base.toList = base3 ∧
      onLChain.base.toList = base3 ∧ onMcommChain.base.toList = base3 ∧
      onLcommChain.base.toList = base3 ∧ onJointChain.base.toList = base3 ∧
      Nat.card onT = 512 ∧ Nat.card onM = 161280 ∧ Nat.card onL = 80640 ∧
      Nat.card onWM = 80640 ∧ Nat.card onWL = 80640 ∧
      Nat.card (onM ⊔ onM1 : Subgroup (Equiv.Perm (Fin N))) = 460815505920 ∧
      onT ≤ Pv ∧ ∃ S : Sylow 2 Pv, (S : Subgroup Pv) = onT.subgroupOf Pv :=
  ⟨tFacts.point, tFacts.valid, mFacts.point, mFacts.valid, lFacts.point, lFacts.valid,
    mcommFacts.point, mcommFacts.valid, lcommFacts.point, lcommFacts.valid, jointFacts.point,
    jointFacts.valid, tFacts.base, mFacts.base, lFacts.base, mcommFacts.base, lcommFacts.base,
    jointFacts.base, card_onT, card_onM, card_onL, card_onWM, card_onWL, card_joint, onT_le,
    onTSylow, onTSylow_coe⟩

end CFSG.ONSchreier
