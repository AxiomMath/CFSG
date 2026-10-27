module

public import CFSG.Sporadic.Co2Schreier.FullAut
public import Certificates.Certificate744102
public import CFSG.RankThree.Asc83Table.E9
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2I301
  CFSG.Sporadic.Co2Schreier.IndexNineData
open scoped Matrix

@[expose] def co2NineR :
    Subgroup (Equiv.Perm (Fin 63)) :=
  sixAction.range.map toPerm63

@[expose] def ninePhi :
    locC →* co2NineR where
  toFun c := ⟨toPerm63 (sixAction c), Subgroup.mem_map.mpr ⟨sixAction c, ⟨c, rfl⟩, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [map_mul]

abbrev nineStab :
    Subgroup ↥co2NineR :=
  MulAction.stabilizer ↥co2NineR nineEll

@[expose] def co2NineU : Subgroup ↥co2P := locS.subgroupOf co2P

@[expose] def co2NineP :
    Subgroup ↥co2P :=
  ((nineStab.comap ninePhi).map locC.subtype).subgroupOf co2P

@[expose] def nineXPerm : Equiv.Perm (Fin 2300) := wordValue cTuple (nineXSig)

@[expose] def nineYPerm : Equiv.Perm (Fin 2300) := wordValue cTuple (nineYSig)

@[expose] def nineX : locC :=
  ⟨nineXPerm, wordValue_mem cTuple locC (fun _ hg => Subgroup.subset_closure hg)
    (nineXSig)⟩

@[expose] def nineY : locC :=
  ⟨nineYPerm, wordValue_mem cTuple locC (fun _ hg => Subgroup.subset_closure hg)
    (nineYSig)⟩

@[expose] def nineQ : Subgroup ↥co2P :=
  (Subgroup.closure {nineXPerm, nineYPerm}).subgroupOf co2P

theorem nineSub_ext {a b : NineSub} (h : a.carrier = b.carrier) : a = b := by
  cases a
  cases b
  simpa using h

@[expose] def nineGensC : List locC := [cGen 0, cGen 1]

theorem nineGensC_map_val :
    nineGensC.map (Subgroup.subtype locC) = cTuple := by
  have hl : cTuple.length = 2 := cTuple_length
  have hg0 : ((cGen 0 : locC) : Equiv.Perm (Fin 2300)) = cTuple[0] := by
    show cTuple.getD 0 1 = cTuple[0]
    rw [List.getD_eq_getElem _ _ (by rw [cTuple_length]; norm_num)]
  have hg1 : ((cGen 1 : locC) : Equiv.Perm (Fin 2300)) = cTuple[1] := by
    show cTuple.getD 1 1 = cTuple[1]
    rw [List.getD_eq_getElem _ _ (by rw [cTuple_length]; norm_num)]
  have hct : cTuple = [cTuple[0], cTuple[1]] := by
    apply List.ext_getElem
    · simp [cTuple_length]
    · intro n h1 h2
      have hn : n < 2 := by simpa using h2
      interval_cases n <;> simp
  rw [hct, nineGensC]
  simp [hg0, hg1]

theorem nineX_eq_word :
    nineX = wordValue nineGensC (nineXSig) := by
  apply Subtype.ext
  change Subgroup.subtype locC nineX =
    Subgroup.subtype locC (wordValue nineGensC (nineXSig))
  rw [nineWordValue_map (Subgroup.subtype locC) nineGensC, nineGensC_map_val]
  rfl

theorem nineY_eq_word :
    nineY = wordValue nineGensC (nineYSig) := by
  apply Subtype.ext
  change Subgroup.subtype locC nineY =
    Subgroup.subtype locC (wordValue nineGensC (nineYSig))
  rw [nineWordValue_map (Subgroup.subtype locC) nineGensC, nineGensC_map_val]
  rfl

theorem nineX_sixAction :
    toPerm63 (sixAction nineX) = wordValue [sixPi 0, sixPi 1] (nineXSig) := by
  have hlist : (nineGensC.map ninePhi).map (Subgroup.subtype co2NineR) = [sixPi 0, sixPi 1] := by
    have h0 : Subgroup.subtype co2NineR (ninePhi (cGen 0)) = sixPi 0 :=
      toPerm63_sixAction_cGen (i := 0) (by norm_num)
    have h1 : Subgroup.subtype co2NineR (ninePhi (cGen 1)) = sixPi 1 :=
      toPerm63_sixAction_cGen (i := 1) (by norm_num)
    simp only [nineGensC, List.map_cons, List.map_nil, h0, h1]
  have h1 : toPerm63 (sixAction nineX) = Subgroup.subtype co2NineR (ninePhi nineX) := rfl
  rw [h1, nineX_eq_word, nineWordValue_map ninePhi nineGensC,
    nineWordValue_map (Subgroup.subtype co2NineR) (nineGensC.map ninePhi), hlist]

theorem nineY_sixAction :
    toPerm63 (sixAction nineY) = wordValue [sixPi 0, sixPi 1] (nineYSig) := by
  have hlist : (nineGensC.map ninePhi).map (Subgroup.subtype co2NineR) = [sixPi 0, sixPi 1] := by
    have h0 : Subgroup.subtype co2NineR (ninePhi (cGen 0)) = sixPi 0 :=
      toPerm63_sixAction_cGen (i := 0) (by norm_num)
    have h1 : Subgroup.subtype co2NineR (ninePhi (cGen 1)) = sixPi 1 :=
      toPerm63_sixAction_cGen (i := 1) (by norm_num)
    simp only [nineGensC, List.map_cons, List.map_nil, h0, h1]
  have h1 : toPerm63 (sixAction nineY) = Subgroup.subtype co2NineR (ninePhi nineY) := rfl
  rw [h1, nineY_eq_word, nineWordValue_map ninePhi nineGensC,
    nineWordValue_map (Subgroup.subtype co2NineR) (nineGensC.map ninePhi), hlist]

theorem nineCol_pos_lt_of
    (i p : ℕ) (hi : i < 15) (hp : p < 63) :
    0 < co2NineXorF (colFun i) (p + 1) ∧ co2NineXorF (colFun i) (p + 1) < 64 := by
  interval_cases i
  · exact col_pos_lt_0 p hp
  · exact col_pos_lt_1 p hp
  · exact col_pos_lt_2 p hp
  · exact col_pos_lt_3 p hp
  · exact col_pos_lt_4 p hp
  · exact col_pos_lt_5 p hp
  · exact col_pos_lt_6 p hp
  · exact col_pos_lt_7 p hp
  · exact col_pos_lt_8 p hp
  · exact col_pos_lt_9 p hp
  · exact col_pos_lt_10 p hp
  · exact col_pos_lt_11 p hp
  · exact col_pos_lt_12 p hp
  · exact col_pos_lt_13 p hp
  · exact col_pos_lt_14 p hp

theorem nineCode_lt
    {i p : ℕ} (hi : i < 15) (hp : p < 63) :
    co2NineCode i p < 63 := by
  have := (nineCol_pos_lt_of i p hi hp).2
  rw [co2NineCode]
  omega

theorem sPt_eq_of
    (i p : ℕ) (hi : i < 15) (hp : p < 63) :
    sixAction (co2NineSC i) (sixPt p) = sixPt (co2NineCode i p) := by
  interval_cases i
  · exact sPt_eq_0 p hp
  · exact sPt_eq_1 p hp
  · exact sPt_eq_2 p hp
  · exact sPt_eq_3 p hp
  · exact sPt_eq_4 p hp
  · exact sPt_eq_5 p hp
  · exact sPt_eq_6 p hp
  · exact sPt_eq_7 p hp
  · exact sPt_eq_8 p hp
  · exact sPt_eq_9 p hp
  · exact sPt_eq_10 p hp
  · exact sPt_eq_11 p hp
  · exact sPt_eq_12 p hp
  · exact sPt_eq_13 p hp
  · exact sPt_eq_14 p hp

theorem toPerm63_sixAction_sC
    {i : ℕ} (hi : i < 15) (p : Fin 63) :
    toPerm63 (sixAction (co2NineSC i)) p = ⟨co2NineCode i p.val, nineCode_lt hi p.isLt⟩ := by
  apply nzEquiv.injective
  rw [toPerm63_apply]
  apply Subtype.ext
  change sixAction (co2NineSC i) (sixPt p.val) = sixPt (co2NineCode i p.val)
  exact sPt_eq_of i p.val hi p.isLt

theorem code_forty_three
    {i : ℕ} (hi : i < 15) : co2NineCode i 43 = 43 := by
  have h := (allLtE_eq 15 (fun i => co2NineCode i 43 == 43)).1 fixedOK_true i hi
  simpa using h

theorem pairFixed_of
    {i : ℕ} (hi : i < 15) :
    (co2NineCode i 25 = 25 ∧ co2NineCode i 53 = 53) ∨
      (co2NineCode i 25 = 53 ∧ co2NineCode i 53 = 25) := by
  have h := (allLtE_eq 15 (fun i => pairFixed i 25 53)).1 pairPreservedOK_true i hi
  simpa [pairFixed, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] using h

theorem mem_nineEll_image
    {i : ℕ} (hi : i < 15) {p : Fin 63} (hp : p ∈ nineEll.carrier) :
    toPerm63 (sixAction (co2NineSC i)) p ∈ nineEll.carrier := by
  have hmem : ∀ q : Fin 63, q ∈ nineEll.carrier ↔
      q.val = 25 ∨ q.val = 43 ∨ q.val = 53 := by
    intro q
    show q ∈ ({25, 43, 53} : Finset (Fin 63)) ↔ q.val = 25 ∨ q.val = 43 ∨ q.val = 53
    simp [Fin.ext_iff]
  have hp' : p.val = 25 ∨ p.val = 43 ∨ p.val = 53 := (hmem p).1 hp
  have hcode : co2NineCode i p.val = 25 ∨ co2NineCode i p.val = 43 ∨ co2NineCode i p.val = 53 := by
    rcases hp' with h | h | h
    · rcases pairFixed_of hi with ⟨h25, -⟩ | ⟨h25, -⟩
      · exact Or.inl (by rw [h, h25])
      · exact Or.inr (Or.inr (by rw [h, h25]))
    · exact Or.inr (Or.inl (by rw [h, code_forty_three hi]))
    · rcases pairFixed_of hi with ⟨-, h53⟩ | ⟨-, h53⟩
      · exact Or.inr (Or.inr (by rw [h, h53]))
      · exact Or.inl (by rw [h, h53])
  rw [toPerm63_sixAction_sC hi p, hmem]
  exact hcode

theorem nineStab_sC_mem
    {i : ℕ} (hi : i < 15) : ninePhi (co2NineSC i) ∈ nineStab := by
  rw [nineStab, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  apply nineSub_ext
  show nineEll.carrier.image (toPerm63 (sixAction (co2NineSC i))) = nineEll.carrier
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact mem_nineEll_image hi hy
  · rw [Finset.card_image_of_injOn (fun x _ y _ h => (toPerm63 _).injective h)]

theorem nineU_le_P :
    co2NineU ≤ co2NineP := by
  have hclosure : locS ≤ (nineStab.comap ninePhi).map locC.subtype := by
    rw [locS, Subgroup.closure_le]
    intro g hg
    obtain ⟨i, hi, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hg
    rw [sTuple_length] at hi
    exact Subgroup.mem_map.mpr ⟨co2NineSC i, nineStab_sC_mem hi, rfl⟩
  intro x hx
  rw [co2NineU, Subgroup.mem_subgroupOf] at hx
  rw [co2NineP, Subgroup.mem_subgroupOf]
  exact hclosure hx

theorem nineX_fix :
    toPerm63 (sixAction nineX) • nineEll = nineEll := by
  apply nineSub_ext
  show nineEll.carrier.image (toPerm63 (sixAction nineX)) = nineEll.carrier
  have hfun : (nineXPos.map fun i => [sixPi 0, sixPi 1].getD i 1).prod = ninePt nineXPos := by
    funext p
    exact ninePt_eq nineXPos_lt p
  have hinj : Function.Injective (ninePt nineXPos) := by
    rw [← hfun]
    exact Equiv.injective _
  rw [nineX_sixAction, show nineXSig = nineSigned nineXPos from rfl, wordValue_nineSigned, hfun]
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact nineX_pt_mem z hz
  · rw [Finset.card_image_of_injOn (fun a _ b _ h => hinj h)]

theorem nineY_fix :
    toPerm63 (sixAction nineY) • nineEll = nineEll := by
  apply nineSub_ext
  show nineEll.carrier.image (toPerm63 (sixAction nineY)) = nineEll.carrier
  have hfun : (nineYPos.map fun i => [sixPi 0, sixPi 1].getD i 1).prod = ninePt nineYPos := by
    funext p
    exact ninePt_eq nineYPos_lt p
  have hinj : Function.Injective (ninePt nineYPos) := by
    rw [← hfun]
    exact Equiv.injective _
  rw [nineY_sixAction, show nineYSig = nineSigned nineYPos from rfl, wordValue_nineSigned, hfun]
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact nineY_pt_mem z hz
  · rw [Finset.card_image_of_injOn (fun a _ b _ h => hinj h)]

theorem nineX_mem_P :
    (⟨nineXPerm, locC_le_P nineX.2⟩ : ↥co2P) ∈ co2NineP := by
  rw [co2NineP, Subgroup.mem_subgroupOf]
  refine Subgroup.mem_map.mpr ⟨nineX, ?_, rfl⟩
  rw [Subgroup.mem_comap, nineStab, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  exact nineX_fix

theorem nineY_mem_P :
    (⟨nineYPerm, locC_le_P nineY.2⟩ : ↥co2P) ∈ co2NineP := by
  rw [co2NineP, Subgroup.mem_subgroupOf]
  refine Subgroup.mem_map.mpr ⟨nineY, ?_, rfl⟩
  rw [Subgroup.mem_comap, nineStab, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  exact nineY_fix

theorem nineX_rep :
    Rep 2300 (wordArr cArrs (nineXSig)) nineXPerm :=
  repTuple_c.word wordFacts.invC (by decide)

theorem nineY_rep :
    Rep 2300 (wordArr cArrs (nineYSig)) nineYPerm :=
  repTuple_c.word wordFacts.invC (by decide)

private theorem wordValue_append' {G : Type*} [Group G] (gs : List G) (u v : List ℤ) :
    wordValue gs (u ++ v) = wordValue gs u * wordValue gs v := by
  simp [wordValue, List.map_append, List.prod_append]

theorem nineX_pow_three :
    nineXPerm ^ 3 = 1 := by
  have hchk := (co2IndexNineWordCheck_spec Certificates.certificate744102).1
  have hl := nineX3Signed_letters
  have hrep : Rep 2300 (wordArr cArrs nineX3Sig) (nineXPerm ^ 3) := by
    have h := repTuple_c.word wordFacts.invC (w := nineX3Sig) hl
    have hw : wordValue cTuple nineX3Sig = nineXPerm ^ 3 := by
      rw [nineX3Sig, nineX2Sig, wordValue_append', wordValue_append', pow_three, mul_assoc]
      rfl
    rw [← hw]
    exact h
  have h1 : nineXPerm ^ 3 = 1 := eq_of_eqA hrep rep_idA hchk
  exact h1

theorem nineY_pow_three :
    nineYPerm ^ 3 = 1 := by
  have hchk := (co2IndexNineWordCheck_spec Certificates.certificate744102).2.1
  have hl := nineY3Signed_letters
  have hrep : Rep 2300 (wordArr cArrs nineY3Sig) (nineYPerm ^ 3) := by
    have h := repTuple_c.word wordFacts.invC (w := nineY3Sig) hl
    have hw : wordValue cTuple nineY3Sig = nineYPerm ^ 3 := by
      rw [nineY3Sig, wordValue_append', wordValue_append', pow_three, mul_assoc]
      rfl
    rw [← hw]
    exact h
  have h1 : nineYPerm ^ 3 = 1 := eq_of_eqA hrep rep_idA hchk
  exact h1

theorem nineXY_comm :
    Commute nineXPerm nineYPerm := by
  have hchk := (co2IndexNineWordCheck_spec Certificates.certificate744102).2.2.1
  have hl1 := nineXYSigned_letters
  have hl2 := nineYXSigned_letters
  have hrep1 : Rep 2300 (wordArr cArrs nineXYSig) (nineXPerm * nineYPerm) := by
    have h := repTuple_c.word wordFacts.invC (w := nineXYSig) hl1
    have hw : wordValue cTuple nineXYSig = nineXPerm * nineYPerm := by
      rw [nineXYSig, wordValue_append']
      rfl
    rw [← hw]
    exact h
  have hrep2 : Rep 2300 (wordArr cArrs nineYXSig) (nineYPerm * nineXPerm) := by
    have h := repTuple_c.word wordFacts.invC (w := nineYXSig) hl2
    have hw : wordValue cTuple nineYXSig = nineYPerm * nineXPerm := by
      rw [nineYXSig, wordValue_append']
      rfl
    rw [← hw]
    exact h
  exact eq_of_eqA hrep1 hrep2 hchk

theorem nineX_ne_one :
    nineXPerm ≠ 1 := by
  intro h
  have hchk := (co2IndexNineWordCheck_spec Certificates.certificate744102).2.2.2.1
  have htrue : eqA 2300 (wordArr cArrs nineXSig) (idA 2300) = true :=
    (eqA_iff nineX_rep rep_idA).2 h
  rw [htrue] at hchk
  cases hchk

theorem nineY_ne_one :
    nineYPerm ≠ 1 := by
  intro h
  have hchk := (co2IndexNineWordCheck_spec Certificates.certificate744102).2.2.2.2.1
  have htrue : eqA 2300 (wordArr cArrs nineYSig) (idA 2300) = true :=
    (eqA_iff nineY_rep rep_idA).2 h
  rw [htrue] at hchk
  cases hchk

theorem nineY_ne_X :
    nineYPerm ≠ nineXPerm := by
  intro h
  have hchk := (co2IndexNineWordCheck_spec Certificates.certificate744102).2.2.2.2.2.1
  have htrue : eqA 2300 (wordArr cArrs nineYSig) (wordArr cArrs nineXSig) = true :=
    (eqA_iff nineY_rep nineX_rep).2 h
  rw [htrue] at hchk
  cases hchk

theorem nineY_ne_X_sq :
    nineYPerm ≠ nineXPerm ^ 2 := by
  intro h
  have hchk := (co2IndexNineWordCheck_spec Certificates.certificate744102).2.2.2.2.2.2
  have hl := nineX2Signed_letters
  have hx2 : Rep 2300 (wordArr cArrs nineX2Sig) (nineXPerm * nineXPerm) := by
    have h' := repTuple_c.word wordFacts.invC (w := nineX2Sig) hl
    have hw : wordValue cTuple nineX2Sig = nineXPerm * nineXPerm := by
      rw [nineX2Sig, wordValue_append']
      rfl
    rw [← hw]
    exact h'
  have htrue : eqA 2300 (wordArr cArrs nineYSig) (wordArr cArrs nineX2Sig) = true := by
    rw [pow_two] at h
    exact (eqA_iff nineY_rep hx2).2 h
  rw [htrue] at hchk
  cases hchk

theorem nineY_not_mem_zpowers :
    nineYPerm ∉ Subgroup.zpowers nineXPerm :=
  CFSG.RankThree.Asc83Table.not_mem_zpowers_of_ne nineX_pow_three nineY_ne_one nineY_ne_X
    nineY_ne_X_sq

theorem nineQ_card :
    Nat.card nineQ = 9 := by
  have hle : Subgroup.closure {nineXPerm, nineYPerm} ≤ co2P := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact locC_le_P nineX.2
    · exact locC_le_P nineY.2
  rw [nineQ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine nineX_pow_three nineY_pow_three
      nineXY_comm nineX_ne_one nineY_not_mem_zpowers]

theorem nineQ_le_P :
    nineQ ≤ co2NineP := by
  have hxP := Subgroup.mem_subgroupOf.mp nineX_mem_P
  have hyP := Subgroup.mem_subgroupOf.mp nineY_mem_P
  have hcl : Subgroup.closure {nineXPerm, nineYPerm} ≤
      (nineStab.comap ninePhi).map locC.subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hxP
    · exact hyP
  intro z hz
  rw [nineQ, Subgroup.mem_subgroupOf] at hz
  rw [co2NineP, Subgroup.mem_subgroupOf]
  exact hcl hz

theorem nineQ_pow_three :
    ∀ q ∈ nineQ, q ^ 3 = 1 := by
  let E : CFSG.RankThree.Asc83Table.E9Basis (Equiv.Perm (Fin 2300)) :=
    CFSG.RankThree.Asc83Table.E9Basis.ofNe nineX_pow_three nineY_pow_three nineXY_comm
      nineX_ne_one nineY_ne_one nineY_ne_X nineY_ne_X_sq
  intro q hq
  have hq' : (q : Equiv.Perm (Fin 2300)) ∈ E.sub := by
    rw [nineQ, Subgroup.mem_subgroupOf] at hq
    simpa [E, CFSG.RankThree.Asc83Table.E9Basis.ofNe, CFSG.RankThree.Asc83Table.E9Basis.sub]
      using hq
  obtain ⟨i, j, -, -, hqij⟩ := E.exists_pow_mul_pow hq'
  apply Subtype.ext
  change (q : Equiv.Perm (Fin 2300)) ^ 3 = 1
  simp only [E, CFSG.RankThree.Asc83Table.E9Basis.ofNe,
    CFSG.RankThree.Asc83Table.E9Basis.sub] at hqij
  rw [hqij]
  have hpow_comm : Commute (nineXPerm ^ i) (nineYPerm ^ j) :=
    Commute.pow_right (Commute.pow_left nineXY_comm i) j
  rw [Commute.mul_pow hpow_comm]
  rw [show (nineXPerm ^ i) ^ 3 = 1 by
    rw [← pow_mul, mul_comm i 3, pow_mul, nineX_pow_three, one_pow]]
  rw [show (nineYPerm ^ j) ^ 3 = 1 by
    rw [← pow_mul, mul_comm j 3, pow_mul, nineY_pow_three, one_pow]]
  rw [one_mul]

theorem nineGen_mem
    {i : ℕ} (hi : i < 2) : sixPi i ∈ co2NineR := by
  rw [← toPerm63_sixAction_cGen hi]
  exact Subgroup.mem_map.mpr ⟨sixAction (cGen i), ⟨cGen i, rfl⟩, rfl⟩

theorem nineProd_mem
    (w : List ℕ) (hw : ∀ i ∈ w, i < 2) :
    (w.map fun i => [sixPi 0, sixPi 1].getD i 1).prod ∈ co2NineR := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hi := hw i List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 2 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    rw [List.map_cons, List.prod_cons, sixPi_getD hi]
    exact Subgroup.mul_mem _ (nineGen_mem hi) (ih hw')

theorem nineOrbit_ge :
    315 ≤ Nat.card (MulAction.orbit ↥co2NineR nineEll) := by
  letI : Fintype ↥co2NineR :=
    Fintype.ofInjective (Subtype.val : ↥co2NineR → Equiv.Perm (Fin 63)) Subtype.val_injective
  letI : Fintype ↥(MulAction.orbit ↥co2NineR nineEll) :=
    Fintype.ofInjective (fun x : ↥(MulAction.orbit ↥co2NineR nineEll) => (x.val : NineSub))
      (fun a b h => Subtype.ext h)
  letI : Fintype ↥(MulAction.stabilizer ↥co2NineR nineEll) :=
    Fintype.ofInjective
      (fun x : ↥(MulAction.stabilizer ↥co2NineR nineEll) => (x.val : ↥co2NineR))
      (fun a b h => Subtype.ext h)
  have hlen : (nineOrbitWords.map nineOrbSet).length = 315 := by
    rw [List.length_map, nineOrbitWords_length]
  have hnd : (nineOrbitWords.map nineOrbSet).Nodup := nineOrbitWords_nodup
  have hcard : (nineOrbitWords.map nineOrbSet).toFinset.card = 315 := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have hsub : (nineOrbitWords.map nineOrbSet).toFinset ⊆
      (MulAction.orbit ↥co2NineR nineEll).toFinset := by
    intro S hS
    simp only [List.mem_toFinset, List.mem_map] at hS
    obtain ⟨w, hw, rfl⟩ := hS
    have hwlt := nineOrbitWords_lt w hw
    have hfun : (w.map fun i => [sixPi 0, sixPi 1].getD i 1).prod = ninePt w := by
      funext p
      exact ninePt_eq hwlt p
    have hset : nineOrbSet w =
        (⟨(w.map fun i => [sixPi 0, sixPi 1].getD i 1).prod, nineProd_mem w hwlt⟩ :
          ↥co2NineR) • nineEll := by
      apply nineSub_ext
      show nineEll.carrier.image (ninePt w) =
        nineEll.carrier.image (w.map fun i => [sixPi 0, sixPi 1].getD i 1).prod
      rw [← hfun]
    rw [hset]
    exact Set.mem_toFinset.mpr (MulAction.mem_orbit_iff.mpr ⟨_, rfl⟩)
  calc
    315 = (nineOrbitWords.map nineOrbSet).toFinset.card := hcard.symm
    _ ≤ (MulAction.orbit ↥co2NineR nineEll).toFinset.card := Finset.card_le_card hsub
    _ = Nat.card (MulAction.orbit ↥co2NineR nineEll) := by
      rw [Set.toFinset_card, Nat.card_eq_fintype_card]

theorem nineR_card :
    Nat.card ↥co2NineR = 1451520 := by
  have h := Nat.card_congr (Subgroup.equivMapOfInjective sixAction.range toPerm63
    toPerm63_injective).toEquiv
  rw [co2NineR, ← h]
  exact card_sixAction_range

theorem nineStab_card_le :
    Nat.card nineStab ≤ 4608 := by
  letI : Fintype ↥co2NineR :=
    Fintype.ofInjective (Subtype.val : ↥co2NineR → Equiv.Perm (Fin 63)) Subtype.val_injective
  letI : Fintype ↥(MulAction.orbit ↥co2NineR nineEll) :=
    Fintype.ofInjective (fun x : ↥(MulAction.orbit ↥co2NineR nineEll) => (x.val : NineSub))
      (fun a b h => Subtype.ext h)
  letI : Fintype ↥(MulAction.stabilizer ↥co2NineR nineEll) :=
    Fintype.ofInjective
      (fun x : ↥(MulAction.stabilizer ↥co2NineR nineEll) => (x.val : ↥co2NineR))
      (fun a b h => Subtype.ext h)
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (G := ↥co2NineR) (X := NineSub) (b := nineEll)
  have hnat : Nat.card (MulAction.orbit ↥co2NineR nineEll) * Nat.card nineStab =
      1451520 := by
    rw [← nineR_card]
    simp only [Nat.card_eq_fintype_card]
    exact h
  have hge := nineOrbit_ge
  have hmono : 315 * Nat.card nineStab ≤ 1451520 := by
    calc 315 * Nat.card nineStab
        ≤ Nat.card (MulAction.orbit ↥co2NineR nineEll) * Nat.card nineStab :=
          Nat.mul_le_mul_right _ hge
      _ = 1451520 := hnat
  omega

theorem nineP_card_le :
    Nat.card co2NineP ≤ 9 * 2 ^ 18 := by
  have hkerPhi : ninePhi.ker = sixAction.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : toPerm63 (sixAction x) = 1 := congrArg Subtype.val h
      exact toPerm63_injective (by simpa using h1)
    · intro h
      apply Subtype.ext
      show toPerm63 (sixAction x) = 1
      rw [h, map_one]
  have hker : ninePhi.ker = locQ.subgroupOf locC := hkerPhi.trans sixAction_ker
  have hQK : locQ.subgroupOf locC ≤ nineStab.comap ninePhi := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hy : (x : Equiv.Perm (Fin 2300)) ∈ locQ := hx
    have h1 : (x : ↥locC) ∈ sixAction.ker := by
      rw [sixAction_ker]
      exact hx
    rw [MonoidHom.mem_ker] at h1
    have h2 : x ∈ ninePhi.ker := by
      rw [hkerPhi]
      exact h1
    rw [MonoidHom.mem_ker] at h2
    rw [h2]
    exact nineStab.one_mem
  have hle : (nineStab.comap ninePhi).map locC.subtype ≤ co2P := by
    intro x hx
    obtain ⟨y, -, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    exact locC_le_P y.2
  have h1 : Nat.card co2NineP = Nat.card ↥(nineStab.comap ninePhi) := by
    rw [co2NineP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.card_map_of_injective locC.subtype_injective]
  have hmap_le : (nineStab.comap ninePhi).map ninePhi ≤ nineStab := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have h2 : Nat.card ↥(nineStab.comap ninePhi) ≤ 512 * Nat.card nineStab := by
    let K : Subgroup locC := nineStab.comap ninePhi
    have hcard := Subgroup.card_ker_mul_card_range (ninePhi.comp K.subtype)
    have hker' : (ninePhi.comp K.subtype).ker = (locQ.subgroupOf locC).subgroupOf K := by
      ext x
      show ninePhi (x : locC) = 1 ↔ (x : Equiv.Perm (Fin 2300)) ∈ locQ
      constructor
      · intro h
        have h' : x.val ∈ ninePhi.ker := MonoidHom.mem_ker.2 h
        rwa [hker] at h'
      · intro h
        exact MonoidHom.mem_ker.1 (by rwa [hker])
    have hrange' : Nat.card ↥((ninePhi.comp K.subtype).range) ≤ Nat.card nineStab := by
      apply Subgroup.card_le_of_le
      rintro _ ⟨x, rfl⟩
      exact x.2
    rw [hker', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv,
      card_locQ_subgroupOf] at hcard
    rw [← hcard]
    exact Nat.mul_le_mul_left 512 hrange'
  calc Nat.card co2NineP = Nat.card ↥(nineStab.comap ninePhi) := h1
    _ ≤ 512 * Nat.card nineStab := h2
    _ ≤ 512 * 4608 := Nat.mul_le_mul_left _ nineStab_card_le
    _ = 9 * 2 ^ 18 := by norm_num

theorem nineU_card :
    Nat.card co2NineU = 2 ^ 18 := by
  rw [co2NineU, card_locS_subgroupOf]
  norm_num

theorem nineP_card :
    Nat.card co2NineP = 9 * Nat.card co2NineU := by
  have h312 : 2 ^ 18 ∣ Nat.card co2NineP := by
    rw [← nineU_card]
    exact Subgroup.card_dvd_of_le nineU_le_P
  have h9 : 9 ∣ Nat.card co2NineP := by
    rw [← nineQ_card]
    exact Subgroup.card_dvd_of_le nineQ_le_P
  have hcop : Nat.Coprime (2 ^ 18) 9 := by norm_num
  have hdvd : 9 * 2 ^ 18 ∣ Nat.card co2NineP := by
    have h := hcop.mul_dvd_of_dvd_of_dvd h312 h9
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hpos : 0 < Nat.card co2NineP := Nat.card_pos
  have hge : 9 * 2 ^ 18 ≤ Nat.card co2NineP := Nat.le_of_dvd hpos hdvd
  have hle := nineP_card_le
  have heq : Nat.card co2NineP = 9 * 2 ^ 18 := le_antisymm hle hge
  rw [heq, nineU_card]

private theorem nine_normalizes
    (g : ↥CFSG.Sporadic.Co2Cert.co2P)
    (hg : co2NineU.map (MulAut.conj g).toMonoidHom = co2NineU) :
    ∀ x : Equiv.Perm (Fin 2300), x ∈ locS →
      (g : Equiv.Perm (Fin 2300)) * x * (g : Equiv.Perm (Fin 2300))⁻¹ ∈ locS := by
  intro x hx
  have hxU : (⟨x, locS_le_P hx⟩ : ↥CFSG.Sporadic.Co2Cert.co2P) ∈ co2NineU := by
    rw [co2NineU, Subgroup.mem_subgroupOf]
    exact hx
  have h1 : (MulAut.conj g) ⟨x, locS_le_P hx⟩ ∈ co2NineU := by
    rw [← hg]
    exact Subgroup.mem_map_of_mem _ hxU
  rw [co2NineU, Subgroup.mem_subgroupOf] at h1
  have h2 : ((MulAut.conj g) ⟨x, locS_le_P hx⟩ : Equiv.Perm (Fin 2300)) =
      (g : Equiv.Perm (Fin 2300)) * x * (g : Equiv.Perm (Fin 2300))⁻¹ := by
    rw [MulAut.conj_apply]
    rfl
  rwa [h2] at h1

private theorem nine_normalizes_inv
    (g : ↥CFSG.Sporadic.Co2Cert.co2P)
    (hg : co2NineU.map (MulAut.conj g).toMonoidHom = co2NineU) :
    ∀ x : Equiv.Perm (Fin 2300), x ∈ locS →
      (g : Equiv.Perm (Fin 2300))⁻¹ * x * (g : Equiv.Perm (Fin 2300)) ∈ locS := by
  have hcomp : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
      MonoidHom.id ↥CFSG.Sporadic.Co2Cert.co2P := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hg' : co2NineU.map (MulAut.conj g⁻¹).toMonoidHom = co2NineU := by
    calc co2NineU.map (MulAut.conj g⁻¹).toMonoidHom
        = (co2NineU.map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj g⁻¹).toMonoidHom := by rw [hg]
      _ = co2NineU.map ((MulAut.conj g⁻¹).toMonoidHom.comp
            (MulAut.conj g).toMonoidHom) := by rw [Subgroup.map_map]
      _ = co2NineU.map (MonoidHom.id _) := by rw [hcomp]
      _ = co2NineU := Subgroup.map_id ..
  intro x hx
  have h := nine_normalizes g⁻¹ hg' x hx
  simpa using h

private theorem nine_centralizes_z
    (g : ↥CFSG.Sporadic.Co2Cert.co2P)
    (hS : ∀ x : Equiv.Perm (Fin 2300), x ∈ locS →
      (g : Equiv.Perm (Fin 2300)) * x * (g : Equiv.Perm (Fin 2300))⁻¹ ∈ locS)
    (hSinv : ∀ x : Equiv.Perm (Fin 2300), x ∈ locS →
      (g : Equiv.Perm (Fin 2300))⁻¹ * x * (g : Equiv.Perm (Fin 2300)) ∈ locS) :
    (g : Equiv.Perm (Fin 2300)) * locZ * (g : Equiv.Perm (Fin 2300))⁻¹ = locZ := by
  have hmemS : (g : Equiv.Perm (Fin 2300)) * locZ * (g : Equiv.Perm (Fin 2300))⁻¹ ∈ locS :=
    hS locZ locZ_mem_S
  have hz_center : locZ ∈ CFSG.centerIn locS := (mem_centerIn_S_iff locZ).2 (Or.inr rfl)
  have hz_comm : ∀ y : Equiv.Perm (Fin 2300), y ∈ locS → y * locZ = locZ * y := by
    intro y hy
    exact (Subgroup.mem_inf.1 hz_center).2 y hy
  have hcent : (g : Equiv.Perm (Fin 2300)) * locZ * (g : Equiv.Perm (Fin 2300))⁻¹ ∈
      CFSG.centerIn locS := by
    refine Subgroup.mem_inf.2 ⟨hmemS, ?_⟩
    intro y hy
    have hy' : (g : Equiv.Perm (Fin 2300))⁻¹ * y * (g : Equiv.Perm (Fin 2300)) ∈ locS :=
      hSinv y hy
    have hcy := hz_comm ((g : Equiv.Perm (Fin 2300))⁻¹ * y * (g : Equiv.Perm (Fin 2300))) hy'
    calc y * ((g : Equiv.Perm (Fin 2300)) * locZ * (g : Equiv.Perm (Fin 2300))⁻¹)
        = (g : Equiv.Perm (Fin 2300)) *
            ((g : Equiv.Perm (Fin 2300))⁻¹ * y * (g : Equiv.Perm (Fin 2300))) *
              locZ * (g : Equiv.Perm (Fin 2300))⁻¹ := by group
      _ = (g : Equiv.Perm (Fin 2300)) *
            (((g : Equiv.Perm (Fin 2300))⁻¹ * y * (g : Equiv.Perm (Fin 2300))) * locZ) *
              (g : Equiv.Perm (Fin 2300))⁻¹ := by group
      _ = (g : Equiv.Perm (Fin 2300)) *
            (locZ * ((g : Equiv.Perm (Fin 2300))⁻¹ * y * (g : Equiv.Perm (Fin 2300)))) *
              (g : Equiv.Perm (Fin 2300))⁻¹ := by rw [hcy]
      _ = ((g : Equiv.Perm (Fin 2300)) * locZ * (g : Equiv.Perm (Fin 2300))⁻¹) * y := by
            group
  rcases (mem_centerIn_S_iff _).1 hcent with h1 | hz
  · exfalso
    have hconj : locZ = 1 := by
      have := congrArg
        (fun t => (g : Equiv.Perm (Fin 2300))⁻¹ * t * (g : Equiv.Perm (Fin 2300))) h1
      simpa [mul_assoc] using this
    exact locZ_ne_one hconj
  · exact hz

private theorem nine_mem_C
    (g : ↥CFSG.Sporadic.Co2Cert.co2P)
    (hZ : (g : Equiv.Perm (Fin 2300)) * locZ * (g : Equiv.Perm (Fin 2300))⁻¹ = locZ) :
    (g : Equiv.Perm (Fin 2300)) ∈ locC := by
  rw [mem_C_iff]
  apply Subtype.ext
  have h1 : (g : Equiv.Perm (Fin 2300)) * locZ = locZ * (g : Equiv.Perm (Fin 2300)) := by
    have := congrArg (fun t => t * (g : Equiv.Perm (Fin 2300))) hZ
    simpa [mul_assoc] using this
  show (zP : Equiv.Perm (Fin 2300)) * (g : Equiv.Perm (Fin 2300)) =
    (g : Equiv.Perm (Fin 2300)) * (zP : Equiv.Perm (Fin 2300))
  show locZ * (g : Equiv.Perm (Fin 2300)) = (g : Equiv.Perm (Fin 2300)) * locZ
  exact h1.symm

private theorem nineSC_mem_S {i : ℕ} (hi : i < 15) :
    (co2NineSC i : locC).1 ∈ locS := by
  rw [locS]
  refine Subgroup.subset_closure ?_
  show sTuple.getD i 1 ∈ sTuple
  exact (mem_iff_exists_getD (d := 1)).2 ⟨i, by rw [sTuple_length]; exact hi, rfl⟩

private theorem nineLocS_le_of_gens (K : Subgroup locS)
    (h : ∀ (i : ℕ) (hi : i < 15),
      (⟨(co2NineSC i : locC).1, nineSC_mem_S hi⟩ : locS) ∈ K) : K = ⊤ := by
  have hmap : K.map (Subgroup.subtype locS) = locS := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    · show Subgroup.closure {g | g ∈ sTuple} ≤ K.map (Subgroup.subtype locS)
      rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨i, hi, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hg
      rw [sTuple_length] at hi
      refine Subgroup.mem_map.2 ⟨⟨sTuple.getD i 1, Subgroup.subset_closure hg⟩, ?_, rfl⟩
      exact h i hi
  rw [eq_top_iff]
  intro s _
  have hs : (s : Equiv.Perm (Fin 2300)) ∈ K.map (Subgroup.subtype locS) := by
    rw [hmap]
    exact s.2
  obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.1 hs
  rw [← Subtype.ext hks]
  exact hk

private def ninePsiS :
    locS →* Equiv.Perm (Fin 63) where
  toFun s := toPerm63 (sixAction ⟨s.1, locS_le_C s.2⟩)
  map_one' := by
    show toPerm63 (sixAction ⟨(1 : locS).1, locS_le_C (1 : locS).2⟩) = 1
    rw [show (⟨(1 : locS).1, locS_le_C (1 : locS).2⟩ : locC) = 1 from Subtype.ext rfl,
      map_one, map_one]
  map_mul' a b := by
    show toPerm63 (sixAction ⟨(a * b).1, locS_le_C (a * b).2⟩) =
      toPerm63 (sixAction ⟨a.1, locS_le_C a.2⟩) * toPerm63 (sixAction ⟨b.1, locS_le_C b.2⟩)
    rw [← map_mul, ← map_mul]
    exact congrArg (fun x => toPerm63 (sixAction x)) (Subtype.ext rfl)

private def nineFix43 :
    Subgroup locS where
  carrier := {s : locS | ninePsiS s (43 : Fin 63) = 43}
  one_mem' := by
    show ninePsiS 1 (43 : Fin 63) = 43
    rw [map_one]
    rfl
  mul_mem' := by
    intro a b ha hb
    show ninePsiS (a * b) (43 : Fin 63) = 43
    rw [map_mul, Equiv.Perm.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    show ninePsiS a⁻¹ (43 : Fin 63) = 43
    rw [map_inv]
    have h1 : (ninePsiS a : Equiv.Perm (Fin 63)) ((ninePsiS a)⁻¹ 43) = (ninePsiS a) 43 := by
      rw [show (ninePsiS a : Equiv.Perm (Fin 63)) ((ninePsiS a)⁻¹ 43) = 43 from
        Equiv.apply_symm_apply (ninePsiS a) (43 : Fin 63), ha]
    exact (ninePsiS a).injective h1

private def nineFixPair :
    Subgroup locS where
  carrier := {s : locS | Set.image (ninePsiS s) ({25, 53} : Set (Fin 63)) = {25, 53}}
  one_mem' := by
    show Set.image (ninePsiS 1) ({25, 53} : Set (Fin 63)) = {25, 53}
    rw [map_one]
    simp
  mul_mem' := by
    intro a b ha hb
    show Set.image (ninePsiS (a * b)) ({25, 53} : Set (Fin 63)) = {25, 53}
    rw [map_mul]
    rw [show (Set.image ((ninePsiS a) * (ninePsiS b)) ({25, 53} : Set (Fin 63))) =
      Set.image (ninePsiS a) (Set.image (ninePsiS b) ({25, 53} : Set (Fin 63))) from by
        rw [Equiv.Perm.coe_mul, Set.image_comp]]
    rw [hb, ha]
  inv_mem' := by
    intro a ha
    show Set.image (ninePsiS a⁻¹) ({25, 53} : Set (Fin 63)) = {25, 53}
    rw [map_inv]
    apply Set.eq_of_subset_of_subset
    · rintro x ⟨y, hy, rfl⟩
      have hψ : Set.image (ninePsiS a) ({25, 53} : Set (Fin 63)) = {25, 53} := ha
      have hxS : (ninePsiS a : Equiv.Perm (Fin 63)) (((ninePsiS a : Equiv.Perm (Fin 63)))⁻¹ y) ∈
          Set.image (ninePsiS a) ({25, 53} : Set (Fin 63)) := by
        rw [show (ninePsiS a : Equiv.Perm (Fin 63)) ((ninePsiS a)⁻¹ y) = y from
          Equiv.apply_symm_apply (ninePsiS a) y, hψ]
        exact hy
      obtain ⟨z, hz, hzx⟩ := hxS
      have hzy : z = (ninePsiS a)⁻¹ y := (ninePsiS a).injective hzx
      rw [← hzy]
      exact hz
    · intro x hx
      have hψxS : (ninePsiS a : Equiv.Perm (Fin 63)) x ∈ ({25, 53} : Set (Fin 63)) := by
        have := Set.mem_image_of_mem (ninePsiS a) hx
        rwa [ha] at this
      exact ⟨(ninePsiS a) x, hψxS, Equiv.symm_apply_apply (ninePsiS a) x⟩

private theorem nineFix43_top :
    nineFix43 = ⊤ := by
  refine nineLocS_le_of_gens nineFix43 ?_
  intro i hi
  show toPerm63 (sixAction (co2NineSC i)) (43 : Fin 63) = 43
  rw [toPerm63_sixAction_sC (i := i) hi (43 : Fin 63)]
  exact Fin.ext (code_forty_three hi)

private theorem nineFixPair_top :
    nineFixPair = ⊤ := by
  refine nineLocS_le_of_gens nineFixPair ?_
  intro i hi
  show Set.image (toPerm63 (sixAction (co2NineSC i))) ({25, 53} : Set (Fin 63)) = {25, 53}
  have hset : ({25, 53} : Set (Fin 63)) = {25} ∪ {53} := by
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases pairFixed_of hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hp25 : toPerm63 (sixAction (co2NineSC i)) (25 : Fin 63) = 25 := by
      rw [toPerm63_sixAction_sC (i := i) hi (25 : Fin 63)]
      exact Fin.ext h1
    have hp53 : toPerm63 (sixAction (co2NineSC i)) (53 : Fin 63) = 53 := by
      rw [toPerm63_sixAction_sC (i := i) hi (53 : Fin 63)]
      exact Fin.ext h2
    rw [hset, Set.image_union, Set.image_singleton, Set.image_singleton, hp25, hp53]
  · have hp25 : toPerm63 (sixAction (co2NineSC i)) (25 : Fin 63) = 53 := by
      rw [toPerm63_sixAction_sC (i := i) hi (25 : Fin 63)]
      exact Fin.ext h1
    have hp53 : toPerm63 (sixAction (co2NineSC i)) (53 : Fin 63) = 25 := by
      rw [toPerm63_sixAction_sC (i := i) hi (53 : Fin 63)]
      exact Fin.ext h2
    rw [hset, Set.image_union, Set.image_singleton, Set.image_singleton, hp25, hp53]
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact or_comm

private theorem nine_locS_fix43
    {s : Equiv.Perm (Fin 2300)} (hs : s ∈ locS) :
    toPerm63 (sixAction ⟨s, locS_le_C hs⟩) (43 : Fin 63) = 43 := by
  have h : (⟨s, hs⟩ : locS) ∈ nineFix43 := by rw [nineFix43_top]; exact Subgroup.mem_top _
  exact h

private theorem nine_locS_pair
    {s : Equiv.Perm (Fin 2300)} (hs : s ∈ locS) :
    toPerm63 (sixAction ⟨s, locS_le_C hs⟩) '' ({25, 53} : Set (Fin 63)) = {25, 53} := by
  have h : (⟨s, hs⟩ : locS) ∈ nineFixPair := by rw [nineFixPair_top]; exact Subgroup.mem_top _
  exact h

private theorem nine_conj_image
    (g : ↥CFSG.Sporadic.Co2Cert.co2P) (hgC : (g : Equiv.Perm (Fin 2300)) ∈ locC)
    (x : locC) {hmem : (g : Equiv.Perm (Fin 2300))⁻¹ * (x : Equiv.Perm (Fin 2300)) *
      (g : Equiv.Perm (Fin 2300)) ∈ locS} :
    (toPerm63 (sixAction ⟨g, hgC⟩))⁻¹ * toPerm63 (sixAction x) *
        toPerm63 (sixAction ⟨g, hgC⟩) =
    toPerm63 (sixAction ⟨(g : Equiv.Perm (Fin 2300))⁻¹ * (x : Equiv.Perm (Fin 2300)) *
      (g : Equiv.Perm (Fin 2300)), locS_le_C hmem⟩) := by
  have h1 : (toPerm63 (sixAction ⟨g, hgC⟩))⁻¹ = toPerm63 (sixAction ⟨g, hgC⟩⁻¹) := by
    change ((toPerm63.comp sixAction) ⟨g, hgC⟩)⁻¹ = (toPerm63.comp sixAction) ⟨g, hgC⟩⁻¹
    rw [← map_inv]
  rw [h1]
  have h2 : sixAction ⟨g, hgC⟩⁻¹ * sixAction x * sixAction ⟨g, hgC⟩ =
      sixAction ((⟨g, hgC⟩ : locC)⁻¹ * x * ⟨g, hgC⟩) := by rw [map_mul, map_mul]
  rw [← map_mul, ← map_mul, h2]
  rw [show (⟨g, hgC⟩ : locC)⁻¹ * x * ⟨g, hgC⟩ =
    (⟨(g : Equiv.Perm (Fin 2300))⁻¹ * (x : Equiv.Perm (Fin 2300)) *
      (g : Equiv.Perm (Fin 2300)), locS_le_C hmem⟩ : locC) from Subtype.ext rfl]

private theorem nine_unique_fixed_code :
    ∀ p < 63, (∀ i < 15, co2NineCode i p = p) → p = 43 := by decide +kernel

private theorem nine_unique_fixed
    {p : Fin 63}
    (h : ∀ i < 15, toPerm63 (sixAction (co2NineSC i)) p = p) : p = 43 := by
  have hcode : ∀ i < 15, co2NineCode i p.val = p.val := by
    intro i hi
    have hfix := h i hi
    rw [toPerm63_sixAction_sC (i := i) hi p] at hfix
    exact congrArg Fin.val hfix
  exact Fin.ext (nine_unique_fixed_code p.val p.isLt hcode)

private theorem nine_pair_split {b : Equiv.Perm (Fin 63)} {x y : Fin 63} (hxy : x ≠ y)
    (h : Set.image b ({x, y} : Set (Fin 63)) = {x, y}) :
    (b x = x ∧ b y = y) ∨ (b x = y ∧ b y = x) := by
  have hx : b x ∈ ({x, y} : Set (Fin 63)) := by
    rw [← h]
    exact Set.mem_image_of_mem b (by simp)
  have hy : b y ∈ ({x, y} : Set (Fin 63)) := by
    rw [← h]
    exact Set.mem_image_of_mem b (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with hx | hx
  · refine Or.inl ⟨hx, ?_⟩
    rcases hy with hy | hy
    · exfalso
      exact hxy (b.injective (by rw [hy, hx]))
    · exact hy
  · refine Or.inr ⟨hx, ?_⟩
    rcases hy with hy | hy
    · exact hy
    · exfalso
      exact hxy (b.injective (by rw [hx, hy]))

private theorem nine_unique_pair_code :
    ∀ x : Fin 63, ∀ y : Fin 63, x ≠ y →
      (∀ i : Fin 15, pairFixed i.val x.val y.val = true) →
      (x = 25 ∧ y = 53) ∨ (x = 53 ∧ y = 25) := by decide +kernel

private theorem nine_unique_pair
    {x y : Fin 63} (hxy : x ≠ y)
    (h : ∀ i < 15, (toPerm63 (sixAction (co2NineSC i)) x = x ∧
        toPerm63 (sixAction (co2NineSC i)) y = y) ∨
      (toPerm63 (sixAction (co2NineSC i)) x = y ∧
        toPerm63 (sixAction (co2NineSC i)) y = x)) :
    (x = 25 ∧ y = 53) ∨ (x = 53 ∧ y = 25) := by
  have hpair : ∀ i < 15, pairFixed i x.val y.val = true := by
    intro i hi
    have hcode : ∀ (a : Fin 63),
        toPerm63 (sixAction (co2NineSC i)) a =
          (⟨co2NineCode i a.val, nineCode_lt hi a.isLt⟩ : Fin 63) := fun a =>
      toPerm63_sixAction_sC (i := i) hi a
    rcases h i hi with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have h1 : co2NineCode i x.val = x.val := by
        have := congrArg Fin.val hx
        rw [hcode x] at this
        exact this
      have h2 : co2NineCode i y.val = y.val := by
        have := congrArg Fin.val hy
        rw [hcode y] at this
        exact this
      simp only [pairFixed, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact Or.inl ⟨h1, h2⟩
    · have h1 : co2NineCode i x.val = y.val := by
        have := congrArg Fin.val hx
        rw [hcode x] at this
        exact this
      have h2 : co2NineCode i y.val = x.val := by
        have := congrArg Fin.val hy
        rw [hcode y] at this
        exact this
      simp only [pairFixed, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact Or.inr ⟨h1, h2⟩
  have hpair' : ∀ i : Fin 15, pairFixed i.val x.val y.val = true := fun i =>
    hpair i.val i.isLt
  exact nine_unique_pair_code x y hxy hpair'

private theorem nine_stab_fixes
    (g : ↥CFSG.Sporadic.Co2Cert.co2P)
    (hgC : (g : Equiv.Perm (Fin 2300)) ∈ locC)
    (hSinv : ∀ x : Equiv.Perm (Fin 2300), x ∈ locS →
      (g : Equiv.Perm (Fin 2300))⁻¹ * x * (g : Equiv.Perm (Fin 2300)) ∈ locS) :
    toPerm63 (sixAction ⟨g, hgC⟩) (43 : Fin 63) = 43 := by
  apply nine_unique_fixed
  intro i hi
  have hmem : (g : Equiv.Perm (Fin 2300))⁻¹ * (co2NineSC i : locC).1 *
      (g : Equiv.Perm (Fin 2300)) ∈ locS := hSinv _ (nineSC_mem_S hi)
  have hconj := nine_conj_image g hgC (co2NineSC i) (hmem := hmem)
  have hfix := nine_locS_fix43 hmem
  have hid : toPerm63 (sixAction (co2NineSC i)) * toPerm63 (sixAction ⟨g, hgC⟩) =
      toPerm63 (sixAction ⟨g, hgC⟩) * ((toPerm63 (sixAction ⟨g, hgC⟩))⁻¹ *
        toPerm63 (sixAction (co2NineSC i)) * toPerm63 (sixAction ⟨g, hgC⟩)) := by group
  calc toPerm63 (sixAction (co2NineSC i)) (toPerm63 (sixAction ⟨g, hgC⟩) 43)
      = (toPerm63 (sixAction (co2NineSC i)) * toPerm63 (sixAction ⟨g, hgC⟩)) 43 := by
          rw [Equiv.Perm.mul_apply]
    _ = (toPerm63 (sixAction ⟨g, hgC⟩) * ((toPerm63 (sixAction ⟨g, hgC⟩))⁻¹ *
          toPerm63 (sixAction (co2NineSC i)) * toPerm63 (sixAction ⟨g, hgC⟩))) 43 := by rw [hid]
    _ = toPerm63 (sixAction ⟨g, hgC⟩) (((toPerm63 (sixAction ⟨g, hgC⟩))⁻¹ *
          toPerm63 (sixAction (co2NineSC i)) * toPerm63 (sixAction ⟨g, hgC⟩)) 43) := by
          rw [Equiv.Perm.mul_apply]
    _ = toPerm63 (sixAction ⟨g, hgC⟩) 43 := by rw [hconj, hfix]

private theorem nine_stab_pair
    (g : ↥CFSG.Sporadic.Co2Cert.co2P)
    (hgC : (g : Equiv.Perm (Fin 2300)) ∈ locC)
    (hSinv : ∀ x : Equiv.Perm (Fin 2300), x ∈ locS →
      (g : Equiv.Perm (Fin 2300))⁻¹ * x * (g : Equiv.Perm (Fin 2300)) ∈ locS) :
    Set.image (toPerm63 (sixAction ⟨g, hgC⟩)) ({25, 53} : Set (Fin 63)) = {25, 53} := by
  have hx : toPerm63 (sixAction ⟨g, hgC⟩) 25 ≠ toPerm63 (sixAction ⟨g, hgC⟩) 53 := by
    intro h
    exact (by decide : (25 : Fin 63) ≠ 53) ((toPerm63 (sixAction ⟨g, hgC⟩)).injective h)
  have hpres : ∀ i < 15, Set.image (toPerm63 (sixAction (co2NineSC i)))
      (Set.image (toPerm63 (sixAction ⟨g, hgC⟩)) ({25, 53} : Set (Fin 63))) =
      Set.image (toPerm63 (sixAction ⟨g, hgC⟩)) ({25, 53} : Set (Fin 63)) := by
    intro i hi
    have hmem : (g : Equiv.Perm (Fin 2300))⁻¹ * (co2NineSC i : locC).1 *
        (g : Equiv.Perm (Fin 2300)) ∈ locS := hSinv _ (nineSC_mem_S hi)
    have hconj := nine_conj_image g hgC (co2NineSC i) (hmem := hmem)
    have hfix := nine_locS_pair hmem
    have hid : toPerm63 (sixAction (co2NineSC i)) * toPerm63 (sixAction ⟨g, hgC⟩) =
        toPerm63 (sixAction ⟨g, hgC⟩) * ((toPerm63 (sixAction ⟨g, hgC⟩))⁻¹ *
          toPerm63 (sixAction (co2NineSC i)) * toPerm63 (sixAction ⟨g, hgC⟩)) := by group
    calc Set.image (toPerm63 (sixAction (co2NineSC i)))
          (Set.image (toPerm63 (sixAction ⟨g, hgC⟩)) ({25, 53} : Set (Fin 63)))
        = Set.image (toPerm63 (sixAction (co2NineSC i)) *
            toPerm63 (sixAction ⟨g, hgC⟩)) ({25, 53} : Set (Fin 63)) := by
            rw [Equiv.Perm.coe_mul, Set.image_comp]
      _ = Set.image (toPerm63 (sixAction ⟨g, hgC⟩) * ((toPerm63 (sixAction ⟨g, hgC⟩))⁻¹ *
            toPerm63 (sixAction (co2NineSC i)) * toPerm63 (sixAction ⟨g, hgC⟩)))
            ({25, 53} : Set (Fin 63)) := by rw [hid]
      _ = Set.image (toPerm63 (sixAction ⟨g, hgC⟩))
            (Set.image ((toPerm63 (sixAction ⟨g, hgC⟩))⁻¹ *
              toPerm63 (sixAction (co2NineSC i)) * toPerm63 (sixAction ⟨g, hgC⟩))
              ({25, 53} : Set (Fin 63))) := by
            rw [Equiv.Perm.coe_mul, Set.image_comp]
      _ = Set.image (toPerm63 (sixAction ⟨g, hgC⟩)) ({25, 53} : Set (Fin 63)) := by
            rw [hconj, hfix]
  have hpres' : ∀ i < 15, Set.image (toPerm63 (sixAction (co2NineSC i)))
      ({(toPerm63 (sixAction ⟨g, hgC⟩)) 25, (toPerm63 (sixAction ⟨g, hgC⟩)) 53} :
        Set (Fin 63)) =
      {(toPerm63 (sixAction ⟨g, hgC⟩)) 25, (toPerm63 (sixAction ⟨g, hgC⟩)) 53} := by
    intro i hi
    rw [← Set.image_pair]
    exact hpres i hi
  have huniq := nine_unique_pair hx (fun i hi => nine_pair_split hx (hpres' i hi))
  rcases huniq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [show ({25, 53} : Set (Fin 63)) = {25} ∪ {53} by
        ext x; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff],
      Set.image_union, Set.image_singleton, Set.image_singleton, h1, h2]
  · rw [show ({25, 53} : Set (Fin 63)) = {25} ∪ {53} by
        ext x; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff],
      Set.image_union, Set.image_singleton, Set.image_singleton, h1, h2]
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact or_comm

private theorem nine_stab_of_pair
    (g : ↥CFSG.Sporadic.Co2Cert.co2P)
    (hgC : (g : Equiv.Perm (Fin 2300)) ∈ locC)
    (h43 : toPerm63 (sixAction ⟨g, hgC⟩) (43 : Fin 63) = 43)
    (hpair : Set.image (toPerm63 (sixAction ⟨g, hgC⟩)) ({25, 53} : Set (Fin 63)) = {25, 53}) :
    ninePhi ⟨g, hgC⟩ ∈ nineStab := by
  rw [nineStab, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
  apply nineSub_ext
  show nineEll.carrier.image (toPerm63 (sixAction ⟨g, hgC⟩)) = nineEll.carrier
  have hmem : ∀ q : Fin 63, q ∈ nineEll.carrier ↔ q = 25 ∨ q = 43 ∨ q = 53 := by
    intro q
    show q ∈ ({25, 43, 53} : Finset (Fin 63)) ↔ q = 25 ∨ q = 43 ∨ q = 53
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have h25 : toPerm63 (sixAction ⟨g, hgC⟩) 25 ∈ ({25, 53} : Set (Fin 63)) := by
    rw [← hpair]
    exact Set.mem_image_of_mem _ (by simp)
  have h53 : toPerm63 (sixAction ⟨g, hgC⟩) 53 ∈ ({25, 53} : Set (Fin 63)) := by
    rw [← hpair]
    exact Set.mem_image_of_mem _ (by simp)
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    rw [hmem] at hp ⊢
    rcases hp with hp | hp | hp
    · subst hp
      rcases h25 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · subst hp
      exact Or.inr (Or.inl h43)
    · subst hp
      rcases h53 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  · rw [Finset.card_image_of_injOn (fun a _ b _ h => (toPerm63 _).injective h)]

theorem nineP_map
    (α : MulAut ↥CFSG.Sporadic.Co2Cert.co2P)
    (hα : co2NineU.map α.toMonoidHom = co2NineU) :
    co2NineP.map α.toMonoidHom = co2NineP := by
  obtain ⟨g, rfl⟩ := CTUC_Co2_full_automorphisms_inner α
  have hS := nine_normalizes g hα
  have hSinv := nine_normalizes_inv g hα
  have hZ := nine_centralizes_z g hS hSinv
  have hgC : (g : Equiv.Perm (Fin 2300)) ∈ locC := nine_mem_C g hZ
  have h43 := nine_stab_fixes g hgC hSinv
  have hpair := nine_stab_pair g hgC hSinv
  have hstab : ninePhi ⟨g, hgC⟩ ∈ nineStab := nine_stab_of_pair g hgC h43 hpair
  have hle : co2NineP.map (MulAut.conj g).toMonoidHom ≤ co2NineP := by
    intro z hz
    obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.mp hz
    rw [co2NineP, Subgroup.mem_subgroupOf] at hxP ⊢
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxP
    have hyStab : ninePhi y ∈ nineStab := hy
    have hmemC : (g : Equiv.Perm (Fin 2300)) * (y : Equiv.Perm (Fin 2300)) *
        (g : Equiv.Perm (Fin 2300))⁻¹ ∈ locC :=
      (⟨g, hgC⟩ * y * ⟨g, hgC⟩⁻¹ : locC).2
    refine Subgroup.mem_map.mpr ⟨⟨(g : Equiv.Perm (Fin 2300)) * (y : Equiv.Perm (Fin 2300)) *
      (g : Equiv.Perm (Fin 2300))⁻¹, hmemC⟩, ?_, ?_⟩
    · rw [Subgroup.mem_comap]
      have hprod : ninePhi ⟨(g : Equiv.Perm (Fin 2300)) * (y : Equiv.Perm (Fin 2300)) *
          (g : Equiv.Perm (Fin 2300))⁻¹, hmemC⟩ =
          ninePhi ⟨g, hgC⟩ * ninePhi y * (ninePhi ⟨g, hgC⟩)⁻¹ := by
        apply Subtype.ext
        show toPerm63 (sixAction ⟨(g : Equiv.Perm (Fin 2300)) * (y : Equiv.Perm (Fin 2300)) *
            (g : Equiv.Perm (Fin 2300))⁻¹, hmemC⟩) =
          toPerm63 (sixAction ⟨g, hgC⟩) * toPerm63 (sixAction y) *
            (toPerm63 (sixAction ⟨g, hgC⟩))⁻¹
        rw [show (⟨(g : Equiv.Perm (Fin 2300)) * (y : Equiv.Perm (Fin 2300)) *
            (g : Equiv.Perm (Fin 2300))⁻¹, hmemC⟩ : locC) =
            ⟨g, hgC⟩ * y * ⟨g, hgC⟩⁻¹ from Subtype.ext rfl]
        simp only [map_mul, map_inv]
      rw [hprod]
      exact mul_mem (mul_mem hstab hyStab) (inv_mem hstab)
    · change (g : Equiv.Perm (Fin 2300)) * (y : Equiv.Perm (Fin 2300)) *
          (g : Equiv.Perm (Fin 2300))⁻¹ =
        ((MulAut.conj g) x : ↥CFSG.Sporadic.Co2Cert.co2P).val
      rw [MulAut.conj_apply]
      change (g : Equiv.Perm (Fin 2300)) * (y : Equiv.Perm (Fin 2300)) *
          (g : Equiv.Perm (Fin 2300))⁻¹ =
        (g : Equiv.Perm (Fin 2300)) * (x : Equiv.Perm (Fin 2300)) *
          (g : Equiv.Perm (Fin 2300))⁻¹
      rw [← hyx]
      rfl
  have hcard : Nat.card ↥(co2NineP.map (MulAut.conj g).toMonoidHom) =
      Nat.card ↥co2NineP :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

theorem nineU_isSylow :
    CFSG.QuasithinUnique.IsSylowTwoOf co2NineU ⊤ := by
  refine ⟨le_top, isPGroup_locS_subgroupOf, ?_⟩
  have hcardU : Nat.card ↥(co2NineU.subgroupOf ⊤) = 262144 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv]
    exact card_locS_subgroupOf
  have hcardT : Nat.card ↥(⊤ : Subgroup (↥co2P)) = 42305421312000 := by
    rw [Subgroup.card_top]
    exact card_co2P
  have h := Subgroup.card_mul_index (H := co2NineU.subgroupOf ⊤)
  rw [hcardU, hcardT] at h
  have hidx : (co2NineU.subgroupOf ⊤).index = 161382375 := by omega
  rw [hidx]
  norm_num

theorem co2_index_nine_package :
    ∃ U P Q : Subgroup ↥CFSG.Sporadic.Co2Cert.co2P,
      CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧ U ≤ P ∧
      Nat.card P = 9 * Nat.card U ∧
      (∀ α : MulAut ↥CFSG.Sporadic.Co2Cert.co2P,
        U.map α.toMonoidHom = U → P.map α.toMonoidHom = P) ∧
      Q ≤ P ∧ Nat.card Q = 9 ∧ ∀ q ∈ Q, q ^ 3 = 1 :=
  ⟨co2NineU, co2NineP, nineQ, nineU_isSylow, nineU_le_P, nineP_card,
    fun α hα => nineP_map α hα, nineQ_le_P, nineQ_card, nineQ_pow_three⟩

end CFSG.Sporadic.Co2Schreier

end
