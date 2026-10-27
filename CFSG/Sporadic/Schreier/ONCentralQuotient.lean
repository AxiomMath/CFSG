module

public import CFSG.Sporadic.Schreier.ONPerfect
public import CFSG.Sporadic.Schreier.ONStandardAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates
open scoped Pointwise

theorem prep_q :
    PRep N qArr onq := prep_wordArr words_ok.2.2.2.2.2.1

theorem onq_mem_L :
    onq ∈ onL := by
  have h := lFacts.mem prep_q (evalS_mem _) qt_cert.1
  rwa [onLChain_sub] at h

theorem onq_pow4 :
    onq ^ 4 = 1 := by
  have h := eq_of_peq (prep_pcomp prep_q (prep_pcomp prep_q (prep_pcomp prep_q prep_q)))
    prep_pid qt_cert.2.1
  calc onq ^ 4 = onq * (onq * (onq * onq)) := by simp [pow_succ, mul_assoc]
    _ = 1 := h

theorem onq_sq_ne :
    onq ^ 2 ≠ 1 := by
  intro h
  have h1 : peq nPts (pcomp nPts qArr qArr) (pid nPts) = true :=
    (peq_iff (prep_pcomp prep_q prep_q) prep_pid).2 (by rw [← h, sq])
  rw [qt_cert.2.2.1] at h1
  exact absurd h1 (by decide)

theorem orderOf_onq :
    orderOf onq = 4 := by
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using onq_sq_ne)
    (by simpa using onq_pow4)
  simpa using this

theorem card_onQ :
    Nat.card onQ = 4 := by
  rw [onQ, Nat.card_zpowers, orderOf_onq]

theorem onQ_le_L :
    onQ ≤ onL := Subgroup.zpowers_le.2 onq_mem_L

theorem onQ_le_M :
    onQ ≤ onM := onQ_le_L.trans onL_le_M

theorem onL_le_centralizer_q :
    onL ≤ Subgroup.centralizer {onq} := by
  rw [onL, Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hj2 : j < 2 := by rw [onLgens_length] at hj; exact hj
  have h := eq_of_peq (prep_pcomp (prep_onLgens j hj) prep_q)
    (prep_pcomp prep_q (prep_onLgens j hj))
    (allBelowN_spec qt_cert.2.2.2.1 hj2)
  exact Subgroup.mem_centralizer_singleton_iff.2 h

theorem onQ_le_centralizer_L :
    onQ ≤ Subgroup.centralizer (onL : Set (Equiv.Perm (Fin N))) := by
  rw [onQ, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro g hg
  exact (Subgroup.mem_centralizer_singleton_iff.1 (onL_le_centralizer_q hg))

theorem qblocks_size : Data.quotientBlocks.size = 120 := by decide

theorem blocks_wf {i : ℕ} (hi : i < 120) :
    Data.quotientBlocks[i]!.size = 2 ∧ (Data.quotientBlocks[i]!)[0]! < N ∧
      (Data.quotientBlocks[i]!)[1]! < N ∧
      (Data.quotientBlocks[i]!)[0]! ≠ (Data.quotientBlocks[i]!)[1]! ∧
      bPos[(Data.quotientBlocks[i]!)[0]!]! = i ∧ bPos[(Data.quotientBlocks[i]!)[1]!]! = i := by
  have h := block_cert.1
  simp only [blocksOK, Bool.and_eq_true, beq_iff_eq] at h
  have := allBelowN_spec h.2 (by rw [qblocks_size]; exact hi)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem onB_length : onB.length = 120 := by simp [onB, qblocks_size]

theorem onB_get {i : ℕ} (hi : i < onB.length) :
    onB[i] = (Data.quotientBlocks[i]!).toList.map ptN := by
  have hi' : i < Data.quotientBlocks.size := by simpa [onB] using hi
  have e := List.getElem_of_eq (show onB = Data.quotientBlocks.toList.map
    fun b => b.toList.map ptN from rfl) hi
  rw [e, List.getElem_map, Array.getElem_toList, getElem!_pos _ i hi']

theorem mem_onB {i : ℕ} (hi : i < onB.length) {x : Fin N} :
    x ∈ onB[i] ↔ (x : ℕ) = (Data.quotientBlocks[i]!)[0]! ∨
      (x : ℕ) = (Data.quotientBlocks[i]!)[1]! := by
  have hi' : i < 120 := by rwa [onB_length] at hi
  obtain ⟨hs, h0, h1, -⟩ := blocks_wf hi'
  rw [onB_get, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    have hk2 : k < 2 := by simpa [hs] using hk
    simp only [Array.getElem_toList, ptN]
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · left
      rw [getElem!_pos _ 0 (by omega)] at h0 ⊢
      exact Nat.mod_eq_of_lt h0
    · right
      rw [getElem!_pos _ 1 (by omega)] at h1 ⊢
      exact Nat.mod_eq_of_lt h1
  · rintro (h | h)
    · refine ⟨(Data.quotientBlocks[i]!)[0]!, ?_, Fin.ext ?_⟩
      · rw [getElem!_pos _ 0 (by omega)]
        exact Array.getElem_mem_toList _
      · simp only [ptN]
        rw [h, Nat.mod_eq_of_lt h0]
    · refine ⟨(Data.quotientBlocks[i]!)[1]!, ?_, Fin.ext ?_⟩
      · rw [getElem!_pos _ 1 (by omega)]
        exact Array.getElem_mem_toList _
      · simp only [ptN]
        rw [h, Nat.mod_eq_of_lt h1]

theorem bPos_of_mem
    {i : ℕ} (hi : i < onB.length) {x : Fin N} (hx : x ∈ onB[i]) :
    bPos[(x : ℕ)]! = i := by
  have hi' : i < 120 := by rwa [onB_length] at hi
  rcases (mem_onB hi).1 hx with h | h
  · rw [h]; exact (blocks_wf hi').2.2.2.2.1
  · rw [h]; exact (blocks_wf hi').2.2.2.2.2

@[expose] def onBsets : List (Set (Fin N)) := onB.map fun b => {x | x ∈ b}

theorem onBsets_length : onBsets.length = 120 := by simp [onBsets, onB_length]

theorem onBsets_get {i : ℕ} (hi : i < onBsets.length) :
    onBsets[i] = {x | x ∈ onB[i]'(by simpa [onBsets] using hi)} := by
  simp [onBsets]

theorem onB_get_mem_left {i : ℕ} (hi : i < 120) :
    ptN (Data.quotientBlocks[i]!)[0]! ∈ onB[i]'(by rw [onB_length]; exact hi) := by
  rw [mem_onB]
  left
  exact Nat.mod_eq_of_lt (blocks_wf hi).2.1

theorem onBsets_nodup : onBsets.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro a b hab
  simp only [List.get_eq_getElem] at hab
  have ha : a.val < 120 := lt_of_lt_of_eq a.isLt onBsets_length
  have hb : b.val < 120 := lt_of_lt_of_eq b.isLt onBsets_length
  rw [onBsets_get, onBsets_get] at hab
  have hx := onB_get_mem_left ha
  have hx' : ptN (Data.quotientBlocks[a.val]!)[0]! ∈ onB[b.val]'(by rw [onB_length]; exact hb) := by
    have : ptN (Data.quotientBlocks[a.val]!)[0]! ∈
        {x | x ∈ onB[a.val]'(by rw [onB_length]; exact ha)} := hx
    rw [hab] at this
    exact this
  exact Fin.ext ((bPos_of_mem _ hx).symm.trans (bPos_of_mem _ hx'))

theorem pair_eq {a b c d y : Fin N} (hab : a ≠ b) (hcd : c ≠ d) (ha : a = c ∨ a = d)
    (hb : b = c ∨ b = d) (hy : y = c ∨ y = d) : y = a ∨ y = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hy with rfl | rfl <;> tauto

theorem smul_pair {g : Equiv.Perm (Fin N)} {a b c d : Fin N} (hab : a ≠ b) (hcd : c ≠ d)
    (hga : g a = c ∨ g a = d) (hgb : g b = c ∨ g b = d) :
    g • {x : Fin N | x = a ∨ x = b} = {x | x = c ∨ x = d} := by
  have habne : g a ≠ g b := fun e => hab (g.injective e)
  ext y
  rw [Set.mem_smul_set, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl
    · exact hga
    · exact hgb
  · intro hy
    rcases pair_eq habne hcd hga hgb hy with rfl | rfl
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr rfl, rfl⟩

theorem onBsets_eq_pair {i : ℕ} (hi : i < 120) :
    onBsets[i]'(by rw [onBsets_length]; exact hi) =
      {x | x = ⟨(Data.quotientBlocks[i]!)[0]!, (blocks_wf hi).2.1⟩ ∨
        x = ⟨(Data.quotientBlocks[i]!)[1]!, (blocks_wf hi).2.2.1⟩} := by
  ext x
  rw [onBsets_get, Set.mem_ofPred_eq, mem_onB, Set.mem_ofPred_eq, Fin.ext_iff, Fin.ext_iff]

theorem img_mem {garr : Array ℕ} {g : Equiv.Perm (Fin N)} (hg : PRep N garr g) {y c d : ℕ}
    (hy : y < N) (hc : c < N) (hd : d < N) (h : c = garr[y]! ∨ d = garr[y]!) :
    g ⟨y, hy⟩ = ⟨c, hc⟩ ∨ g ⟨y, hy⟩ = ⟨d, hd⟩ := by
  have e := hg ⟨y, hy⟩
  rcases h with h | h
  · left; exact Fin.ext (show (g ⟨y, hy⟩ : ℕ) = c by rw [h, ← e])
  · right; exact Fin.ext (show (g ⟨y, hy⟩ : ℕ) = d by rw [h, ← e])

theorem smul_bset
    {garr : Array ℕ} {g : Equiv.Perm (Fin N)} (hg : PRep N garr g) {t : Array ℕ}
    (h : blockImgOK garr Data.quotientBlocks t) {i : ℕ} (hi : i < 120) :
    ∃ ht : t[i]! < 120, g • onBsets[i]'(by rw [onBsets_length]; exact hi) =
      onBsets[t[i]!]'(by rw [onBsets_length]; exact ht) := by
  obtain ⟨ht, h0, h1⟩ := blockImgOK_spec h (by rw [qblocks_size]; exact hi)
  rw [qblocks_size] at ht
  refine ⟨ht, ?_⟩
  obtain ⟨-, ha, hb, hne, -⟩ := blocks_wf hi
  obtain ⟨-, hc, hd, hne', -⟩ := blocks_wf ht
  rw [onBsets_eq_pair hi, onBsets_eq_pair ht]
  rw [inBlock_iff] at h0 h1
  have hab : (⟨(Data.quotientBlocks[i]!)[0]!, ha⟩ : Fin N) ≠
      ⟨(Data.quotientBlocks[i]!)[1]!, hb⟩ := fun e => hne (Fin.mk.inj e)
  have hcd : (⟨(Data.quotientBlocks[t[i]!]!)[0]!, hc⟩ : Fin N) ≠
      ⟨(Data.quotientBlocks[t[i]!]!)[1]!, hd⟩ := fun e => hne' (Fin.mk.inj e)
  exact smul_pair hab hcd (img_mem hg ha hc hd h0) (img_mem hg hb hc hd h1)

theorem prep_onMgens' :
    ∀ j (hj : j < onMgens.length), PRep N (wordArrs Data.MWords)[j]! onMgens[j] :=
  prep_wordArrs words_ok.2.1

theorem onMgens_preserve :
    ∀ g ∈ onMgens, ∀ S ∈ onBsets, g • S ∈ onBsets := by
  intro g hg S hS
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hS
  have hj3 : j < 3 := by rw [onMgens_length] at hj; exact hj
  have hk' : k < 120 := by rwa [onBsets_length] at hk
  obtain ⟨ht, he⟩ := smul_bset (prep_onMgens' j hj) (allBelowN_spec block_cert.2.1 hj3) hk'
  rw [he]
  exact List.getElem_mem _

theorem onM_preserve :
    ∀ g ∈ onM, ∀ S ∈ onBsets, g • S ∈ onBsets :=
  listInvariant onBsets onMgens_preserve

@[expose] def rhoM :
    onM →* Equiv.Perm (Fin 120) :=
  (finCongr onBsets_length).permCongrHom.toMonoidHom.comp
    (listRestrict onBsets onM onM_preserve onBsets_nodup)

theorem rhoM_spec
    (g : onM) (k : Fin 120) :
    onBsets[(rhoM g k : ℕ)]'(by rw [onBsets_length]; exact (rhoM g k).isLt) =
      (g : Equiv.Perm (Fin N)) • onBsets[(k : ℕ)]'(by rw [onBsets_length]; exact k.isLt) :=
  get_listRestrict onBsets onM onM_preserve onBsets_nodup g (Fin.cast onBsets_length.symm k)

theorem prep_rhoM
    {garr : Array ℕ} {g : onM} (hg : PRep N garr (g : Equiv.Perm (Fin N)))
    {t : Array ℕ} (h : blockImgOK garr Data.quotientBlocks t) : PRep 120 t (rhoM g) := by
  intro k
  obtain ⟨ht, he⟩ := smul_bset hg h k.isLt
  have hs := rhoM_spec g k
  rw [he] at hs
  exact ((List.Nodup.getElem_inj_iff onBsets_nodup).1 hs).symm

@[expose] def mGen (j : ℕ) : onM :=
  if h : j < onMgens.length then ⟨onMgens[j], Subgroup.subset_closure (List.getElem_mem h)⟩
  else 1

theorem mGen_val
    {j : ℕ} (h : j < onMgens.length) :
    (mGen j : Equiv.Perm (Fin N)) = onMgens[j] := by
  rw [mGen, dite_eq_left h]

theorem onM_top :
    (⊤ : Subgroup onM) = Subgroup.closure (mGen '' {j | j < 3}) := by
  symm
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj3 : j < 3 := by rw [onMgens_length] at hj; exact hj
    exact Subgroup.subset_closure ⟨j, hj3, Subtype.ext (mGen_val hj)⟩
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx => exact Subgroup.inv_mem _ ihx

theorem prep_rhoM_gen :
    ∀ j < ((wordArrs Data.MWords).map bTab).size,
    PRep 120 ((wordArrs Data.MWords).map bTab)[j]! (rhoM (mGen j)) := by
  intro j hj
  have h3 : (evalList Data.MWords).length = 3 := onMgens_length
  have hj3 : j < 3 := by simp only [Array.size_map, wordArrs_size] at hj; omega
  have hjl : j < onMgens.length := by rw [onMgens_length]; exact hj3
  have hjs : j < (wordArrs Data.MWords).size := by rw [wordArrs_size]; exact hjl
  rw [getElem!_map' _ _ hjs]
  apply prep_rhoM (g := mGen j) _ (allBelowN_spec block_cert.2.1 hj3)
  rw [mGen_val hjl]
  exact prep_onMgens' j hjl

theorem m120_gens_size : Data.M120Chain.generators.size = 2 := by decide

theorem rhoM_range :
    rhoM.range = onM120Chain.originalSubgroup := by
  rw [MonoidHom.range_eq_map, onM_top, MonoidHom.map_closure, ← Set.image_comp, onM120Chain,
    smallChain_sub]
  have h3 : ((wordArrs Data.MWords).map bTab).size = 3 := by
    rw [Array.size_map, wordArrs_size]; exact onMgens_length
  have := closure_eq_of_coversOK prep_rhoM_gen (prep_smallGen small_chain_certs.2.1)
    block_cert.2.2.2.1 block_cert.2.2.2.2.1
  rw [h3] at this
  exact this

theorem card_rhoM_range :
    Nat.card rhoM.range = 40320 := by
  rw [rhoM_range, card_onM120]

@[expose] def qM :
    onM := ⟨onq, onQ_le_M (Subgroup.mem_zpowers _)⟩

theorem rhoM_q :
    rhoM qM = 1 :=
  (prep_rhoM (g := qM) prep_q block_cert.2.2.2.2.2.2.2).unique prep_pid

theorem onQ_subgroupOf_M :
    onQ.subgroupOf onM = Subgroup.zpowers qM := by
  apply Subgroup.map_injective onM.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 onQ_le_M, MonoidHom.map_zpowers]
  rfl

theorem card_onQ_subgroupOf_M :
    Nat.card (onQ.subgroupOf onM) = 4 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onQ_le_M).toEquiv, card_onQ]

theorem rhoM_ker :
    rhoM.ker = onQ.subgroupOf onM := by
  have h := card_range_mul_ker rhoM
  rw [card_rhoM_range, card_onM] at h
  have hle : onQ.subgroupOf onM ≤ rhoM.ker := by
    rw [onQ_subgroupOf_M, Subgroup.zpowers_le, MonoidHom.mem_ker]
    exact rhoM_q
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_onQ_subgroupOf_M]; omega)).symm

@[expose] def rhoL :
    onL →* Equiv.Perm (Fin 120) := rhoM.comp (Subgroup.inclusion onL_le_M)

@[expose] def lGen (j : ℕ) : onL :=
  if h : j < onLgens.length then ⟨onLgens[j], Subgroup.subset_closure (List.getElem_mem h)⟩
  else 1

theorem lGen_val
    {j : ℕ} (h : j < onLgens.length) :
    (lGen j : Equiv.Perm (Fin N)) = onLgens[j] := by
  rw [lGen, dite_eq_left h]

theorem onL_top :
    (⊤ : Subgroup onL) = Subgroup.closure (lGen '' {j | j < 2}) := by
  symm
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj2 : j < 2 := by rw [onLgens_length] at hj; exact hj
    exact Subgroup.subset_closure ⟨j, hj2, Subtype.ext (lGen_val hj)⟩
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx => exact Subgroup.inv_mem _ ihx

theorem prep_rhoM_of_le
    {H : Subgroup (Equiv.Perm (Fin N))} (hHM : H ≤ onM) {garr : Array ℕ}
    {g : H} (hg : PRep N garr (g : Equiv.Perm (Fin N))) {t : Array ℕ}
    (h : blockImgOK garr Data.quotientBlocks t) :
    PRep 120 t (rhoM (Subgroup.inclusion hHM g)) :=
  prep_rhoM (g := Subgroup.inclusion hHM g) hg h

theorem prep_rhoL_gen :
    ∀ j < ((wordArrs Data.LWords).map bTab).size,
    PRep 120 ((wordArrs Data.LWords).map bTab)[j]! (rhoL (lGen j)) := by
  intro j hj
  have h2 : (evalList Data.LWords).length = 2 := onLgens_length
  have hj2 : j < 2 := by simp only [Array.size_map, wordArrs_size] at hj; omega
  have hjl : j < onLgens.length := by rw [onLgens_length]; exact hj2
  have hjs : j < (wordArrs Data.LWords).size := by rw [wordArrs_size]; exact hjl
  rw [getElem!_map' _ _ hjs]
  have hg : PRep N (wordArrs Data.LWords)[j]! (lGen j : Equiv.Perm (Fin N)) := by
    rw [lGen_val hjl]
    exact prep_onLgens j hjl
  exact prep_rhoM_of_le onL_le_M hg (allBelowN_spec block_cert.2.2.1 hj2)

theorem l120_gens_size : Data.L120Chain.generators.size = 2 := by decide

theorem rhoL_range :
    rhoL.range = onL120Chain.originalSubgroup := by
  rw [MonoidHom.range_eq_map, onL_top, MonoidHom.map_closure, ← Set.image_comp, onL120Chain,
    smallChain_sub]
  have h2 : ((wordArrs Data.LWords).map bTab).size = 2 := by
    rw [Array.size_map, wordArrs_size]; exact onLgens_length
  have := closure_eq_of_coversOK prep_rhoL_gen (prep_smallGen small_chain_certs.2.2.1)
    block_cert.2.2.2.2.2.1 block_cert.2.2.2.2.2.2.1
  rw [h2] at this
  exact this

theorem card_rhoL_range :
    Nat.card rhoL.range = 20160 := by
  rw [rhoL_range, card_onL120]

@[expose] def qL :
    onL := ⟨onq, onq_mem_L⟩

theorem onQ_subgroupOf_L :
    onQ.subgroupOf onL = Subgroup.zpowers qL := by
  apply Subgroup.map_injective onL.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 onQ_le_L, MonoidHom.map_zpowers]
  rfl

theorem rhoL_ker :
    rhoL.ker = onQ.subgroupOf onL := by
  have h := card_range_mul_ker rhoL
  rw [card_rhoL_range, card_onL] at h
  have hle : onQ.subgroupOf onL ≤ rhoL.ker := by
    rw [onQ_subgroupOf_L, Subgroup.zpowers_le, MonoidHom.mem_ker]
    show rhoM qM = 1
    exact rhoM_q
  have hc : Nat.card (onQ.subgroupOf onL) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe onQ_le_L).toEquiv, card_onQ]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc]; omega)).symm

theorem prep_u :
    PRep 120 Data.quotientConjugator onu := (prep_permOfArr u_cert.1).1

theorem prep_u_inv :
    PRep 120 (pinvCand 120 Data.quotientConjugator) onu⁻¹ :=
  (prep_permOfArr u_cert.1).2

theorem psl120_mem
    {g : Array ℕ} {G : Equiv.Perm (Fin 120)} (hg : PRep 120 g G)
    (h : memFull 120 (cLevels 120 Data.PSL120Chain.base (allSteps Data.PSL120Chain.strongGenerators
          (pinvs 120 Data.PSL120Chain.strongGenerators) Data.PSL120Chain.base))
        (allInvSteps Data.PSL120Chain.strongGenerators
          (pinvs 120 Data.PSL120Chain.strongGenerators) Data.PSL120Chain.base)
        Data.PSL120Chain.base g = true) : G ∈ onX :=
  mem_of_memFull psl120_arrays.1 psl120_arrays.2 psl120_valid.1.validPointSchreier hg h

abbrev conjU : Equiv.Perm (Fin 120) →* Equiv.Perm (Fin 120) := (MulAut.conj onu).toMonoidHom

theorem rhoL_conj :
    rhoL.range.map conjU = onX := by
  have hle : rhoL.range.map conjU ≤ onX := by
    rw [MonoidHom.range_eq_map, onL_top, MonoidHom.map_closure, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨_, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
    have hj2 : j < 2 := hj
    have hj' : j < ((wordArrs Data.LWords).map bTab).size := by
      rw [Array.size_map, wordArrs_size]
      have : (evalList Data.LWords).length = 2 := onLgens_length
      omega
    have hrep := prep_rhoL_gen j hj'
    rw [getElem!_map' _ _ (by simpa using hj')] at hrep
    have h2 := prep_pcomp prep_u (prep_pcomp hrep prep_u_inv)
    rw [← mul_assoc] at h2
    show onu * rhoL (lGen j) * onu⁻¹ ∈ onX
    exact psl120_mem h2 (allBelowN_spec u_cert.2 hj2)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_onX, Nat.card_congr (Subgroup.equivMapOfInjective _ conjU
    (MulAut.conj onu).injective).toEquiv.symm, card_rhoL_range]

theorem rhoL_centralizer :
    Subgroup.centralizer (rhoL.range : Set (Equiv.Perm (Fin 120))) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h : conjU x ∈ Subgroup.centralizer (onX : Set (Equiv.Perm (Fin 120))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← rhoL_conj] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [conjU, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := Subgroup.mem_centralizer_iff.1 hx z hz
    calc onu * z * onu⁻¹ * (onu * x * onu⁻¹) = onu * (z * x) * onu⁻¹ := by group
      _ = onu * (x * z) * onu⁻¹ := by rw [this]
      _ = onu * x * onu⁻¹ * (onu * z * onu⁻¹) := by group
  rw [onX_centralizer, Subgroup.mem_bot] at h
  simp only [conjU, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  have : x = 1 := by
    have e : x = onu⁻¹ * (onu * x * onu⁻¹) * onu := by group
    rw [e, h]
    group
  rw [this]
  exact one_mem _

theorem mem_centralizer_range {G P : Type*} [Group G] [Group P] {M K : Subgroup G}
    (hKM : K ≤ M) (f : M →* P) (x : M) (hx : ∀ y ∈ K, y * (x : G) = (x : G) * y) :
    f x ∈ Subgroup.centralizer ((f.comp (Subgroup.inclusion hKM)).range : Set P) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, rfl⟩
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hx y y.2)

theorem onM_centralizer_L :
    onM ⊓ Subgroup.centralizer (onL : Set (Equiv.Perm (Fin N))) = onQ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxc⟩ := Subgroup.mem_inf.1 hx
    have hρ : rhoM ⟨x, hxM⟩ ∈ Subgroup.centralizer (rhoL.range : Set (Equiv.Perm (Fin 120))) :=
      mem_centralizer_range onL_le_M rhoM ⟨x, hxM⟩ fun y hy =>
        Subgroup.mem_centralizer_iff.1 hxc y hy
    rw [rhoL_centralizer, Subgroup.mem_bot, ← MonoidHom.mem_ker, rhoM_ker,
      Subgroup.mem_subgroupOf] at hρ
    exact hρ
  · exact le_inf onQ_le_M onQ_le_centralizer_L

theorem onL_centerIn :
    CFSG.centerIn onL = onQ := by
  apply le_antisymm
  · rw [← onM_centralizer_L]
    exact inf_le_inf_right _ onL_le_M
  · exact le_inf onQ_le_L onQ_le_centralizer_L

theorem center_L :
    Subgroup.center onL = rhoL.ker := by
  rw [rhoL_ker]
  apply Subgroup.map_injective onL.subtype_injective
  rw [← CFSG.centerIn_eq_map_center, onL_centerIn, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 onQ_le_L]

@[expose] def lQuotEquiv :
    onL ⧸ Subgroup.center onL ≃* onX :=
  (QuotientGroup.quotientMulEquivOfEq center_L).trans
    ((QuotientGroup.quotientKerEquivRange rhoL).trans
      ((Subgroup.equivMapOfInjective _ conjU (MulAut.conj onu).injective).trans
        (MulEquiv.subgroupCongr rhoL_conj)))

theorem onB_mem_facts
    {b : List (Fin N)} (hb : b ∈ onB) : b.length = 2 ∧ b.Nodup := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hi' : i < 120 := by rwa [onB_length] at hi
  obtain ⟨hs, h0, h1, hne, -⟩ := blocks_wf hi'
  refine ⟨by rw [onB_get]; simp [hs], ?_⟩
  rw [onB_get]
  have hl : (Data.quotientBlocks[i]!).toList = [(Data.quotientBlocks[i]!)[0]!,
      (Data.quotientBlocks[i]!)[1]!] := by
    apply List.ext_getElem (by simp [hs])
    intro k hk1 hk2
    have hk : k < 2 := by simpa using hk2
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · rw [Array.getElem_toList, List.getElem_cons_zero, getElem!_pos _ 0 (by omega)]
    · rw [Array.getElem_toList, List.getElem_cons_succ, List.getElem_cons_zero,
        getElem!_pos _ 1 (by omega)]
  rw [hl]
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, List.nodup_nil, and_true]
  refine ⟨fun e => ?_, not_false⟩
  have := congrArg Fin.val e
  simp only [ptN] at this
  rw [Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1] at this
  exact hne this

theorem onB_pairwise : onB.Pairwise fun b c => ∀ x ∈ b, x ∉ c := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij x hx hx'
  have := (bPos_of_mem hi hx).symm.trans (bPos_of_mem hj hx')
  omega

theorem onB_image
    {g : Equiv.Perm (Fin N)} (hg : g ∈ onM) {b : List (Fin N)} (hb : b ∈ onB) :
    ∃ c ∈ onB, g • {x | x ∈ b} = {x | x ∈ c} := by
  have hS : {x | x ∈ b} ∈ onBsets := List.mem_map_of_mem hb
  obtain ⟨c, hc, he⟩ := List.mem_map.1 (onM_preserve g hg _ hS)
  exact ⟨c, hc, he.symm⟩

theorem onB_union
    {g : Equiv.Perm (Fin N)} (hg : g ∈ onM) {b : List (Fin N)} (hb : b ∈ onB)
    {x : Fin N} (hx : x ∈ b) : ∃ c ∈ onB, g x ∈ c := by
  obtain ⟨c, hc, he⟩ := onB_image hg hb
  refine ⟨c, hc, ?_⟩
  have : g x ∈ g • {x | x ∈ b} := ⟨x, hx, rfl⟩
  rw [he] at this
  exact this

theorem rhoM_spec'
    (g : onM) (k : Fin 120) :
    {x | x ∈ onB[(rhoM g k : ℕ)]'(by rw [onB_length]; exact (rhoM g k).isLt)} =
      (g : Equiv.Perm (Fin N)) • {x | x ∈ onB[(k : ℕ)]'(by rw [onB_length]; exact k.isLt)} := by
  have := rhoM_spec g k
  rw [onBsets_get, onBsets_get] at this
  exact this

theorem at_on_local_central_quotient :
    onq ∈ onL ∧ orderOf onq = 4 ∧ Nat.card onQ = 4 ∧ IsCyclic onQ ∧
      CFSG.centerIn onL = onQ ∧
      onM ⊓ Subgroup.centralizer (onL : Set (Equiv.Perm (Fin N))) = onQ ∧
      onB.length = 120 ∧ (∀ b ∈ onB, b.length = 2 ∧ b.Nodup) ∧
      onB.Pairwise (fun b c => ∀ x ∈ b, x ∉ c) ∧
      (∀ g ∈ onM, ∀ b ∈ onB, ∀ x ∈ b, ∃ c ∈ onB, g x ∈ c) ∧
      (∀ g ∈ onM, ∀ b ∈ onB, ∃ c ∈ onB, g • {x | x ∈ b} = {x | x ∈ c}) ∧
      (∀ (g : onM) (k : Fin 120),
        {x | x ∈ onB[(rhoM g k : ℕ)]'(by rw [onB_length]; exact (rhoM g k).isLt)} =
          (g : Equiv.Perm (Fin N)) • {x | x ∈ onB[(k : ℕ)]'(by rw [onB_length]; exact k.isLt)}) ∧
      rhoM.range = onM120Chain.originalSubgroup ∧ rhoM.ker = onQ.subgroupOf onM ∧
      rhoL.range = onL120Chain.originalSubgroup ∧ rhoL.ker = onQ.subgroupOf onL ∧
      rhoL.range.map (MulAut.conj onu).toMonoidHom = onX ∧
      Nonempty (onL ⧸ Subgroup.center onL ≃* onX) :=
  ⟨onq_mem_L, orderOf_onq, card_onQ, by rw [onQ]; infer_instance, onL_centerIn,
    onM_centralizer_L, onB_length, fun _ hb => onB_mem_facts hb, onB_pairwise,
    fun _ hg _ hb _ hx => onB_union hg hb hx, fun _ hg _ hb => onB_image hg hb, rhoM_spec',
    rhoM_range, rhoM_ker, rhoL_range, rhoL_ker, rhoL_conj, ⟨lQuotEquiv⟩⟩

end CFSG.ONSchreier
