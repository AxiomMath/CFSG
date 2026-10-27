module

public import CFSG.Sporadic.Schreier.LyLocalAut
public import CFSG.Sporadic.Schreier.LyCentralizer
public import CFSG.Sporadic.SchreierLemmas.CentralizerAutomorphismKernel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Data.ExceptionalSL3

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native CFSG.LocalAnalysis.ComponentInitial CFSG.Sporadic.SchreierLemmas

abbrev C223 : Type := Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 3)

abbrev C223inv : Type := {x : C223 // x ≠ 1 ∧ x ^ 2 = 1}

abbrev C223three : Type := {x : C223 // x ≠ 1 ∧ x ^ 3 = 1}

theorem card_C223 : Nat.card C223 = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_C223inv : Fintype.card C223inv = 3 := by decide

theorem card_C223three : Fintype.card C223three = 2 := by decide

theorem C223_decomp :
    ∀ x : C223, (x ^ 3) ^ 2 = 1 ∧ (x⁻¹ ^ 2) ^ 3 = 1 ∧ x = x ^ 3 * x⁻¹ ^ 2 := by
  decide

@[expose] def autInv (α : MulAut C223) : Equiv.Perm C223inv :=
  α.toEquiv.subtypeEquiv fun x => by
    show x ≠ 1 ∧ x ^ 2 = 1 ↔ α x ≠ 1 ∧ (α x) ^ 2 = 1
    rw [ne_eq, ne_eq, ← map_pow, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]

@[expose] def autThree (α : MulAut C223) : Equiv.Perm C223three :=
  α.toEquiv.subtypeEquiv fun x => by
    show x ≠ 1 ∧ x ^ 3 = 1 ↔ α x ≠ 1 ∧ (α x) ^ 3 = 1
    rw [ne_eq, ne_eq, ← map_pow, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]

@[expose] def autHom : MulAut C223 →* Equiv.Perm C223inv × Equiv.Perm C223three where
  toFun α := (autInv α, autThree α)
  map_one' := by
    refine Prod.ext (Equiv.ext fun x => Subtype.ext ?_) (Equiv.ext fun x => Subtype.ext ?_)
    · show (1 : MulAut C223) x.1 = x.1
      rw [MulAut.one_apply]
    · show (1 : MulAut C223) x.1 = x.1
      rw [MulAut.one_apply]
  map_mul' α β := by
    refine Prod.ext (Equiv.ext fun x => Subtype.ext ?_) (Equiv.ext fun x => Subtype.ext ?_)
    · show (α * β) x.1 = α (β x.1)
      rw [MulAut.mul_apply]
    · show (α * β) x.1 = α (β x.1)
      rw [MulAut.mul_apply]

theorem autHom_injective : Function.Injective autHom := by
  intro α β h
  have h1 : ∀ x : C223, x ^ 2 = 1 → α x = β x := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1, map_one, map_one]
    · exact congrArg (fun p => (p.1 ⟨x, hx1, hx⟩ : C223inv).1) h
  have h3 : ∀ x : C223, x ^ 3 = 1 → α x = β x := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1, map_one, map_one]
    · exact congrArg (fun p => (p.2 ⟨x, hx1, hx⟩ : C223three).1) h
  refine MulEquiv.ext fun x => ?_
  obtain ⟨ha, hb, hx⟩ := C223_decomp x
  rw [hx, map_mul, map_mul, h1 _ ha, h3 _ hb]

theorem isSolvable_mulAut_C223 : Group.IsSolvable (MulAut C223) := by
  have : Group.IsSolvable (Equiv.Perm C223inv) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card, card_C223inv]; norm_num)
  have : Group.IsSolvable (Equiv.Perm C223three) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card, card_C223three]; norm_num)
  exact Group.isSolvable_of_isSolvable_injective autHom_injective

@[expose] def cycHom {G : Type*} [Group G] (p : ℕ) [Fact p.Prime] (g : G) (hg : orderOf g = p) :
    Multiplicative (ZMod p) →* G :=
  (Subgroup.zpowers g).subtype.comp
    ((mulEquivOfPrimeCardEq (G := Multiplicative (ZMod p)) (G' := Subgroup.zpowers g)
      (Nat.card_zmod p) (by rw [Nat.card_zpowers, hg]) :
      Multiplicative (ZMod p) ≃* Subgroup.zpowers g) :
      Multiplicative (ZMod p) →* Subgroup.zpowers g)

theorem cycHom_mem {G : Type*} [Group G] (p : ℕ) [Fact p.Prime] (g : G) (hg : orderOf g = p)
    (x : Multiplicative (ZMod p)) : cycHom p g hg x ∈ Subgroup.zpowers g :=
  Subtype.property _

theorem cycHom_injective {G : Type*} [Group G] (p : ℕ) [Fact p.Prime] (g : G)
    (hg : orderOf g = p) : Function.Injective (cycHom p g hg) :=
  (Subgroup.zpowers g).subtype_injective.comp (MulEquiv.injective _)

theorem pow_eq_one_of_mem_zpowers {G : Type*} [Group G] {g y : G} {n : ℕ} (hg : g ^ n = 1)
    (hy : y ∈ Subgroup.zpowers g) : y ^ n = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

theorem mem_zpowers_of_orderOf_two {G : Type*} [Group G] {g y : G} (hg : orderOf g = 2)
    (hy : y ∈ Subgroup.zpowers g) : y = 1 ∨ y = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_mod_orderOf, hg, Nat.cast_ofNat]
  rcases Int.emod_two_eq k with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem commute_of_mem_zpowers {G : Type*} [Group G] {g k x y : G} (hgk : Commute g k)
    (hx : x ∈ Subgroup.zpowers g) (hy : y ∈ Subgroup.zpowers k) : Commute x y := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact hgk.zpow_zpow i j

@[expose] def wArr : Mat := evalWordM seedM (seedMInv (powM 5 111 matB 4)) fusionWord

@[expose] def xArr : Mat := mulM 5 111 (mulM 5 111 wArr matA) (invM 5 111 wArr)

structure LocalFacts : Prop where
  invList : invConjugators.map (·.1) = (List.range 256).filter (fun i => isInv sTab i && i != 6)
  conj : ∀ e ∈ invConjugators,
    mulM 5 111 (evalWordM (fun i => (pairAt csArr i).1) (fun i => (pairAt csArr i).2) e.2)
      sPts[fIndex]! =
    mulM 5 111 sPts[e.1]!
      (evalWordM (fun i => (pairAt csArr i).1) (fun i => (pairAt csArr i).2) e.2)
  hCube : mulM 5 111 (pairAt csArr 11).2 (mulM 5 111 (pairAt csArr 11).2 (pairAt csArr 11).2) =
    idM 111
  hNe : diffMod5 (pairAt csArr 11).2 (idM 111) = true
  hComm : ∀ q ∈ qIndices, mulM 5 111 (pairAt csArr 11).2 sPts[q]! =
    mulM 5 111 sPts[q]! (pairAt csArr 11).2
  wInv : mulM 5 111 wArr (invM 5 111 wArr) = idM 111
  zx9 : powM 5 111 (mulM 5 111 matA xArr) 9 = idM 111
  xf15 : powM 5 111 (mulM 5 111 xArr sPts[fIndex]!) 15 = idM 111
  qw : ∀ e ∈ qWords,
    evalWordM (fun k => syGenArr[k]!) (fun k => syGenArr[k]!) e.2 = sPts[e.1]!

theorem localFacts : LocalFacts := by
  have h := sylow_parts.2.2.2.2
  unfold localOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h, h10⟩ := h
  obtain ⟨h, h9⟩ := h
  obtain ⟨h, h8⟩ := h
  obtain ⟨h, h7⟩ := h
  obtain ⟨h, h6⟩ := h
  obtain ⟨h, h5⟩ := h
  obtain ⟨h, h4⟩ := h
  obtain ⟨h, h3⟩ := h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun e he => ?_, h3, h4, fun q hq => ?_, h6, h7, h8, fun e he => ?_⟩
  · exact beq_iff_eq.1 ((List.all_eq_true.1 h2) e he)
  · exact beq_iff_eq.1 ((Array.all_eq_true'.1 h5) q hq)
  · exact beq_iff_eq.1 ((List.all_eq_true.1 h10) e he)

@[expose] def lyh : J := evalWord cStar qThreeWord

theorem lyh_eq : lyh = (cStar 11)⁻¹ := by
  simp [lyh, evalWord, letterVal, qThreeWord]

theorem repM_lyh :
    RepM (pairAt csArr 11).2 lyh := by
  rw [lyh_eq]; exact (repM_csArr 11).2

theorem lyh_cube :
    lyh ^ 3 = 1 := by
  have h := repM_lyh.mul (repM_lyh.mul repM_lyh)
  rw [localFacts.hCube] at h
  rw [pow_three]
  exact h.unique repM_id

theorem lyh_ne_one :
    lyh ≠ 1 := by
  intro h1
  apply toMat_ne_of_diffMod5 localFacts.hNe
  rw [repM_lyh, toMat_idM, h1, mat_one]

theorem orderOf_lyh :
    orderOf lyh = 3 :=
  orderOf_eq_prime lyh_cube lyh_ne_one

theorem lyh_comm
    {q : ℕ} (hq : q ∈ qList) : lyh * (sE q : J) = (sE q : J) * lyh := by
  have hql := tableFacts.qLt q hq
  have h := localFacts.hComm q (Array.mem_toList_iff.1 hq)
  have h1 := repM_lyh.mul (repM_sTree q hql).1
  have h2 := (repM_sTree q hql).1.mul repM_lyh
  rw [h] at h1
  rw [sE_val hql]
  exact h1.unique h2

abbrev lyCQ : Subgroup J := Subgroup.centralizer (lyQ : Set J)

theorem lyh_mem_lyCQ :
    lyh ∈ lyCQ := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨q, hq, rfl⟩ := mem_lyQ.1 hx
  exact (lyh_comm hq).symm

theorem sE_mem_lyCQ
    {q : ℕ} (hq : q ∈ zqList) : (sE q : J) ∈ lyCQ := by
  have hqQ := (tableFacts.zq q hq).1
  have hc := (mem_center_lyQ hqQ (mem_lyQ.2 ⟨q, hqQ, rfl⟩)).2 hq
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc) ⟨x, hx⟩)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
  exact h

theorem lyz_mem_lyQ :
    lyz ∈ lyQ := by
  rw [← sE_six]
  exact mem_lyQ.2 ⟨6, (tableFacts.zq 6 (by decide)).1, rfl⟩

theorem centralizer_lyQ_le :
    lyCQ ≤ lyC := by
  intro x hx
  rw [full_involution_centralizer.1, Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.1 hx lyz lyz_mem_lyQ).symm

@[expose] def imgCQ :
    lyCQ →* Equiv.Perm (Fin 11) :=
  imgC.comp (Subgroup.inclusion centralizer_lyQ_le)

@[expose] def uImg (k : ℕ) : Equiv.Perm (Fin 11) :=
  if k < 5 then evalWord pPerm (sylowWords[k]!) else 1

theorem qImg_eq : ∀ j : Fin 4, ∀ x : Fin 11,
    evalWord uImg (qWords[j.val]!).2 x = arrFun (qImgArr[j.val]!) x := by
  decide +kernel

theorem imgC_sylowGen'
    (k : Fin 6) : imgC ⟨sylowGen k, sylowGen_mem_lyC k⟩ = uImg k := by
  by_cases hk : k.val < 5
  · rw [uImg, ite_eq_left hk, ← imgC_sylowGen hk]
  · rw [uImg, ite_eq_right hk]
    have : (⟨sylowGen k, sylowGen_mem_lyC k⟩ : lyC) = zC := by
      apply Subtype.ext
      simp only [sylowGen, ite_eq_right hk]
      rfl
    rw [this, imgC_zC]

@[expose] def sylowGenC
    (k : ℕ) : lyC :=
  if h : k < 6 then ⟨sylowGen ⟨k, h⟩, sylowGen_mem_lyC _⟩ else 1

theorem imgC_sylowGenC
    (k : ℕ) : imgC (sylowGenC k) = uImg k := by
  unfold sylowGenC
  split_ifs with h
  · exact imgC_sylowGen' ⟨k, h⟩
  · rw [map_one, uImg, ite_eq_right (by omega)]

theorem imgC_evalWord_u
    (w : List ℤ) : imgC (evalWord sylowGenC w) = evalWord uImg w := by
  rw [map_evalWord]
  simp only [imgC_sylowGenC]

theorem qWord_letters : ∀ j : Fin 4, ∀ l ∈ (qWords[j.val]!).2, 0 < l ∧ l ≤ 6 := by decide

theorem qWord_entries : ∀ j : Fin 4, (qWords[j.val]!).1 ∈ qList := by decide

theorem repM_wordFrom' {g gi : ℕ → Mat} {gJ : ℕ → J} (w : List ℤ)
    (hw : ∀ l ∈ w, RepM (letterM g gi l) (letterVal gJ l)) {X : Mat} {x : J} (hX : RepM X x) :
    RepM (wordFromM g gi X w) (x * evalWord gJ w) := by
  induction w generalizing X x with
  | nil => simpa [wordFromM, evalWord] using hX
  | cons l w ih =>
    have e : wordFromM g gi X (l :: w) = wordFromM g gi (mulM 5 111 X (letterM g gi l)) w := by
      simp only [wordFromM, List.foldl_cons]
    rw [e, evalWord_cons, ← mul_assoc]
    exact ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) (hX.mul (hw l List.mem_cons_self))

theorem sTree_qWord
    (j : Fin 4) :
    sTree (qWords[j.val]!).1 = ((evalWord sylowGenC (qWords[j.val]!).2 : lyC) : J) := by
  have hmem : qWords[j.val]! ∈ qWords := by
    rw [getElem!_pos qWords j.val (by
      have := j.isLt; simp only [qWords, List.length_cons, List.length_nil]; omega)]
    exact List.getElem_mem _
  have hq := localFacts.qw _ hmem
  have hl := qWord_entries j
  have hrep : RepM (evalWordM (fun k => syGenArr[k]!) (fun k => syGenArr[k]!) (qWords[j.val]!).2)
      (evalWord (fun k => ((sylowGenC k : lyC) : J)) (qWords[j.val]!).2) := by
    have := repM_wordFrom' (g := fun k => syGenArr[k]!) (gi := fun k => syGenArr[k]!)
      (gJ := fun k => ((sylowGenC k : lyC) : J)) (qWords[j.val]!).2 (fun l hl' => by
        obtain ⟨h0, h6⟩ := qWord_letters j l hl'
        have hk : l.toNat - 1 < 6 := by omega
        have e1 : letterM (fun k => syGenArr[k]!) (fun k => syGenArr[k]!) l =
            syGenArr[l.toNat - 1]! := by
          simp only [letterM, ite_eq_left h0]
        have e2 : letterVal (fun k => ((sylowGenC k : lyC) : J)) l =
            sylowGen ⟨l.toNat - 1, hk⟩ := by
          simp only [letterVal, ite_eq_left h0, sylowGenC, dite_eq_left hk]
        rw [e1, e2]
        exact repM_syGen ⟨l.toNat - 1, hk⟩) repM_id
    rwa [one_mul] at this
  rw [hq] at hrep
  rw [(repM_sTree _ (tableFacts.qLt _ hl)).1.unique hrep]
  exact (map_evalWord lyC.subtype sylowGenC _).symm

@[expose] def natInv (m : ℕ) (y : Fin 11) : Fin 11 :=
  ((List.finRange 11).find? fun x => arrFun (qNaturalCentralizer[m]!) x = y).getD 0

theorem nat_natInv : ∀ m : Fin 12, ∀ y : Fin 11,
    arrFun (qNaturalCentralizer[m.val]!) (natInv m y) = y := by
  decide +kernel

theorem natInv_nat : ∀ m : Fin 12, ∀ x : Fin 11,
    natInv m (arrFun (qNaturalCentralizer[m.val]!) x) = x := by
  decide +kernel

@[expose] def natPerm (m : Fin 12) : Equiv.Perm (Fin 11) :=
  ⟨arrFun (qNaturalCentralizer[m.val]!), natInv m, natInv_nat m, nat_natInv m⟩

theorem sign_natPerm : ∀ m : Fin 12, m.val ∉ [1, 4, 6, 8, 9, 11] →
    Equiv.Perm.sign (natPerm m) = -1 := by
  decide

theorem imgC_mem_alternating
    (g : lyC) : imgC g ∈ alternatingGroup (Fin 11) :=
  (lyCoverEquiv (g : lyC ⧸ zGroup)).2

theorem imgCQ_mem
    (x : lyCQ) : ∃ m : Fin 12, m.val ∈ [1, 4, 6, 8, 9, 11] ∧ imgCQ x = natPerm m := by
  have hcomm : ∀ j : Fin 4, ∀ y, imgCQ x (arrFun (qImgArr[j.val]!) y) =
      arrFun (qImgArr[j.val]!) (imgCQ x y) := by
    intro j y
    have hl := qWord_entries j
    have hQ : sTree (qWords[j.val]!).1 ∈ lyQ := by
      rw [← sE_val (tableFacts.qLt _ hl)]
      exact mem_lyQ.2 ⟨_, hl, rfl⟩
    have hJ := Subgroup.mem_centralizer_iff.1 x.2 _ hQ
    rw [sTree_qWord j] at hJ
    have hC : Subgroup.inclusion centralizer_lyQ_le x * evalWord sylowGenC (qWords[j.val]!).2 =
        evalWord sylowGenC (qWords[j.val]!).2 * Subgroup.inclusion centralizer_lyQ_le x :=
      Subtype.ext hJ.symm
    have h := congrArg (fun g : lyC => imgC g (y)) hC
    simp only [map_mul, Equiv.Perm.mul_apply, imgC_evalWord_u] at h
    rw [qImg_eq j, qImg_eq j] at h
    exact h
  set σ := imgCQ x
  have hfold : ∀ (w : List ℕ) (y : Fin 11), (∀ k ∈ w, k < 4) →
      σ (w.foldr (fun k y => arrFun (qImgArr[k]!) y) y) =
        w.foldr (fun k y => arrFun (qImgArr[k]!) y) (σ y) := by
    intro w y hw
    induction w with
    | nil => rfl
    | cons k w ih =>
      simp only [List.foldr_cons]
      rw [hcomm ⟨k, hw k List.mem_cons_self⟩,
        ih (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'))]
  have hcand : ∀ y, σ y = qCand (σ 0) (σ 8) (σ 9) (σ 10) y := by
    intro y
    have := hfold (qWordL y) (qRep y) (qWord_lt y)
    rw [qWord_rep] at this
    rw [this, qCand_eq]
    congr 1
    unfold qRep
    split_ifs <;> rfl
  have hcomm' : ∀ j : Fin 4, ∀ y, qCand (σ 0) (σ 8) (σ 9) (σ 10) (arrFun (qImgArr[j.val]!) y) =
      arrFun (qImgArr[j.val]!) (qCand (σ 0) (σ 8) (σ 9) (σ 10) y) := by
    intro j y
    rw [← hcand, ← hcand, hcomm]
  have hinj : ∀ a b, qCand (σ 0) (σ 8) (σ 9) (σ 10) a = qCand (σ 0) (σ 8) (σ 9) (σ 10) b →
      a = b := fun a b h => σ.injective (by rw [hcand a, hcand b]; exact h)
  obtain ⟨m, hm⟩ := qCand_check _ _ _ _ hcomm' hinj
  have hσm : σ = natPerm m := Equiv.ext fun y => (hcand y).trans (hm y)
  refine ⟨m, ?_, hσm⟩
  by_contra hodd
  have hs := sign_natPerm m hodd
  have heven : Equiv.Perm.sign σ = 1 :=
    Equiv.Perm.mem_alternatingGroup.1
      (imgC_mem_alternating (Subgroup.inclusion centralizer_lyQ_le x))
  rw [hσm, hs] at heven
  exact absurd heven (by decide)

theorem card_lyCQ_le :
    Nat.card lyCQ ≤ 12 := by
  classical
  have hker : Nat.card imgCQ.ker ≤ 2 := by
    have hk : ∀ k : imgCQ.ker, ((k : lyCQ) : J) ∈ ({1, lyz} : Finset J) := by
      intro k
      have h1 : imgC (Subgroup.inclusion centralizer_lyQ_le (k : lyCQ)) = 1 :=
        MonoidHom.mem_ker.1 k.2
      rcases mem_zGroup.1 ((imgC_eq_one_iff _).1 h1) with h | h
      · have := congrArg Subtype.val h
        simp only [Finset.mem_insert, Finset.mem_singleton]
        left; exact this
      · have := congrArg Subtype.val h
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right; exact this
    calc Nat.card imgCQ.ker ≤ Nat.card ({1, lyz} : Finset J) :=
          Nat.card_le_card_of_injective (fun k => ⟨((k : lyCQ) : J), hk k⟩)
            (fun a b h => by
              have h' := congrArg Subtype.val h
              exact Subtype.ext (Subtype.ext h'))
      _ = ({1, lyz} : Finset J).card := Nat.card_eq_finsetCard _
      _ ≤ 2 := Finset.card_le_two
  have hrange : Nat.card imgCQ.range ≤ 6 := by
    have hsub : ∀ σ : imgCQ.range, (σ : Equiv.Perm (Fin 11)) ∈
        (Finset.univ.filter fun m : Fin 12 => m.val ∈ [1, 4, 6, 8, 9, 11]).image natPerm := by
      rintro ⟨_, x, rfl⟩
      obtain ⟨m, hm, hx⟩ := imgCQ_mem x
      exact Finset.mem_image.2 ⟨m, Finset.mem_filter.2 ⟨Finset.mem_univ _, hm⟩, hx.symm⟩
    calc Nat.card imgCQ.range ≤ Nat.card
          ((Finset.univ.filter fun m : Fin 12 => m.val ∈ [1, 4, 6, 8, 9, 11]).image natPerm) :=
          Nat.card_le_card_of_injective (fun σ => ⟨σ.1, hsub σ⟩)
            (fun a b h => by
              have h' := congrArg Subtype.val h
              exact Subtype.ext h')
      _ = ((Finset.univ.filter fun m : Fin 12 => m.val ∈ [1, 4, 6, 8, 9, 11]).image natPerm).card :=
          Nat.card_eq_finsetCard _
      _ ≤ (Finset.univ.filter fun m : Fin 12 => m.val ∈ [1, 4, 6, 8, 9, 11]).card :=
          Finset.card_image_le
      _ = 6 := by decide
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup imgCQ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange imgCQ).toEquiv] at h
  rw [h]
  calc Nat.card imgCQ.range * Nat.card imgCQ.ker ≤ 6 * 2 := Nat.mul_le_mul hrange hker
    _ = 12 := by norm_num

theorem lyf_eq :
    lyf = (sE fIndex : J) := by
  rw [lyf, sylowElt_eq (tableFacts.qLt _ tableFacts.fMem),
    sE_val (tableFacts.qLt _ tableFacts.fMem)]

theorem sE_ne
    {i j : ℕ} (hi : i < 256) (hj : j < 256) (h : i ≠ j) : (sE i : J) ≠ sE j :=
  fun e => h (sE_inj hi hj (Subtype.ext e))

theorem lyz_ne_one :
    lyz ≠ 1 := by
  rw [← sE_six, ← show ((sE 0 : lyS) : J) = 1 by rw [sE_zero]; rfl]
  exact sE_ne (by norm_num) (by norm_num) (by norm_num)

theorem lyf_ne_one :
    lyf ≠ 1 := by
  rw [lyf_eq, ← show ((sE 0 : lyS) : J) = 1 by rw [sE_zero]; rfl]
  exact sE_ne (by decide) (by norm_num) (by decide)

theorem lyz_ne_lyf :
    lyz ≠ lyf := by
  rw [← sE_six, lyf_eq]
  exact sE_ne (by norm_num) (by decide) (by decide)

theorem lyf_sq' :
    lyf ^ 2 = 1 := by
  rw [lyf_eq, pow_two, ← Subgroup.coe_mul, sE_mul (tableFacts.qLt _ tableFacts.fMem)
    (tableFacts.qLt _ tableFacts.fMem), (tableFacts.zq fIndex (by decide)).2, sE_zero]
  rfl

theorem orderOf_lyf :
    orderOf lyf = 2 := orderOf_eq_prime lyf_sq' lyf_ne_one

theorem orderOf_lyz : orderOf lyz = 2 := orderOf_a

theorem lyz_mem_lyCQ :
    lyz ∈ lyCQ := by
  rw [← sE_six]; exact sE_mem_lyCQ (by decide)

theorem lyf_mem_lyCQ :
    lyf ∈ lyCQ := by
  rw [lyf_eq]; exact sE_mem_lyCQ (by decide)

theorem lyf_mem_lyQ :
    lyf ∈ lyQ := by
  rw [lyf_eq]; exact mem_lyQ.2 ⟨_, tableFacts.fMem, rfl⟩

theorem commute_z_f :
    Commute lyz lyf :=
  (Subgroup.mem_centralizer_iff.1 lyz_mem_lyCQ lyf lyf_mem_lyQ).symm

theorem commute_z_h :
    Commute lyz lyh :=
  Subgroup.mem_centralizer_iff.1 lyh_mem_lyCQ lyz lyz_mem_lyQ

theorem commute_f_h :
    Commute lyf lyh :=
  Subgroup.mem_centralizer_iff.1 lyh_mem_lyCQ lyf lyf_mem_lyQ

theorem commute_cyc_zf
    (a b : Multiplicative (ZMod 2)) :
    Commute (cycHom 2 lyz orderOf_lyz a) (cycHom 2 lyf orderOf_lyf b) :=
  commute_of_mem_zpowers (G := J) commute_z_f (cycHom_mem 2 lyz orderOf_lyz a)
    (cycHom_mem 2 lyf orderOf_lyf b)

theorem commute_cyc_zh
    (a : Multiplicative (ZMod 2)) (c : Multiplicative (ZMod 3)) :
    Commute (cycHom 2 lyz orderOf_lyz a) (cycHom 3 lyh orderOf_lyh c) :=
  commute_of_mem_zpowers (G := J) commute_z_h (cycHom_mem 2 lyz orderOf_lyz a)
    (cycHom_mem 3 lyh orderOf_lyh c)

theorem commute_cyc_fh
    (b : Multiplicative (ZMod 2)) (c : Multiplicative (ZMod 3)) :
    Commute (cycHom 2 lyf orderOf_lyf b) (cycHom 3 lyh orderOf_lyh c) :=
  commute_of_mem_zpowers (G := J) commute_f_h (cycHom_mem 2 lyf orderOf_lyf b)
    (cycHom_mem 3 lyh orderOf_lyh c)

@[expose] def fhHom :
    Multiplicative (ZMod 2) × Multiplicative (ZMod 3) →* J :=
  MonoidHom.noncommCoprod (M := Multiplicative (ZMod 2)) (N := Multiplicative (ZMod 3)) (P := J)
    (cycHom 2 lyf orderOf_lyf) (cycHom 3 lyh orderOf_lyh) commute_cyc_fh

theorem fhHom_apply
    (bc : Multiplicative (ZMod 2) × Multiplicative (ZMod 3)) :
    fhHom bc = cycHom 2 lyf orderOf_lyf bc.1 * cycHom 3 lyh orderOf_lyh bc.2 := by
  rw [fhHom, MonoidHom.noncommCoprod_apply]

theorem commute_cyc_z_fh
    (a : Multiplicative (ZMod 2))
    (bc : Multiplicative (ZMod 2) × Multiplicative (ZMod 3)) :
    Commute (cycHom 2 lyz orderOf_lyz a) (fhHom bc) := by
  rw [fhHom_apply]
  exact (commute_cyc_zf a bc.1).mul_right (commute_cyc_zh a bc.2)

@[expose] def c223Hom :
    C223 →* J :=
  MonoidHom.noncommCoprod (M := Multiplicative (ZMod 2))
    (N := Multiplicative (ZMod 2) × Multiplicative (ZMod 3)) (P := J)
    (cycHom 2 lyz orderOf_lyz) fhHom commute_cyc_z_fh

theorem c223Hom_apply
    (x : C223) : c223Hom x =
    cycHom 2 lyz orderOf_lyz x.1 *
      (cycHom 2 lyf orderOf_lyf x.2.1 * cycHom 3 lyh orderOf_lyh x.2.2) := by
  rw [c223Hom, MonoidHom.noncommCoprod_apply, fhHom_apply]

theorem zpowers_le_lyCQ
    {g : J} (hg : g ∈ lyCQ) : Subgroup.zpowers g ≤ lyCQ :=
  (Subgroup.zpowers_le).2 hg

theorem c223Hom_mem
    (x : C223) : c223Hom x ∈ lyCQ := by
  rw [c223Hom_apply]
  exact lyCQ.mul_mem (zpowers_le_lyCQ lyz_mem_lyCQ (cycHom_mem _ _ _ _))
    (lyCQ.mul_mem (zpowers_le_lyCQ lyf_mem_lyCQ (cycHom_mem _ _ _ _))
      (zpowers_le_lyCQ lyh_mem_lyCQ (cycHom_mem _ _ _ _)))

theorem lyz_mul_self : lyz * lyz = 1 := by
  rw [← pow_two, ← orderOf_lyz, pow_orderOf_eq_one]

theorem lyf_mul_self :
    lyf * lyf = 1 := by
  rw [← pow_two]; exact lyf_sq'

theorem uv_mul_self
    {u v : J} (hu : u = 1 ∨ u = lyz) (hv : v = 1 ∨ v = lyf) :
    u * v * (u * v) = 1 := by
  have hzf : lyz * lyf = lyf * lyz := commute_z_f
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · rw [one_mul, one_mul]
  · rw [one_mul, lyf_mul_self]
  · rw [mul_one, lyz_mul_self]
  · calc lyz * lyf * (lyz * lyf) = lyz * (lyf * lyz) * lyf := by group
      _ = lyz * (lyz * lyf) * lyf := by rw [hzf]
      _ = (lyz * lyz) * (lyf * lyf) := by group
      _ = 1 := by rw [lyz_mul_self, lyf_mul_self, one_mul]

theorem c223Hom_injective :
    Function.Injective c223Hom := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b, c⟩ hx
  rw [c223Hom_apply] at hx
  simp only at hx
  have hu := mem_zpowers_of_orderOf_two (G := J) orderOf_lyz (cycHom_mem 2 lyz orderOf_lyz a)
  have hv := mem_zpowers_of_orderOf_two (G := J) orderOf_lyf (cycHom_mem 2 lyf orderOf_lyf b)
  have hw3 : cycHom 3 lyh orderOf_lyh c ^ 3 = 1 :=
    pow_eq_one_of_mem_zpowers (G := J) lyh_cube (cycHom_mem 3 lyh orderOf_lyh c)
  have hwe : cycHom 3 lyh orderOf_lyh c =
      (cycHom 2 lyz orderOf_lyz a * cycHom 2 lyf orderOf_lyf b)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [mul_assoc]; exact hx)
  have hww : cycHom 3 lyh orderOf_lyh c * cycHom 3 lyh orderOf_lyh c = 1 := by
    rw [hwe, ← mul_inv_rev, uv_mul_self hu hv, inv_one]
  have hw1 : cycHom 3 lyh orderOf_lyh c = 1 := by
    calc cycHom 3 lyh orderOf_lyh c = cycHom 3 lyh orderOf_lyh c ^ 3 *
          (cycHom 3 lyh orderOf_lyh c * cycHom 3 lyh orderOf_lyh c)⁻¹ := by group
      _ = 1 := by rw [hw3, hww, inv_one, one_mul]
  have huv1 : cycHom 2 lyz orderOf_lyz a * cycHom 2 lyf orderOf_lyf b = 1 := by
    rw [hw1, mul_one] at hx; exact hx
  have key : cycHom 2 lyz orderOf_lyz a = 1 ∧ cycHom 2 lyf orderOf_lyf b = 1 := by
    rcases hu with h1 | h1 <;> rcases hv with h2 | h2 <;> rw [h1, h2] at huv1
    · exact ⟨h1, h2⟩
    · rw [one_mul] at huv1; exact absurd huv1 lyf_ne_one
    · rw [mul_one] at huv1; exact absurd huv1 lyz_ne_one
    · exfalso
      apply lyz_ne_lyf
      have : lyf = lyz := by rw [← one_mul lyf, ← lyz_mul_self, mul_assoc, huv1, mul_one]
      exact this.symm
  have ha : a = 1 := cycHom_injective 2 lyz orderOf_lyz (key.1.trans (map_one _).symm)
  have hb : b = 1 := cycHom_injective 2 lyf orderOf_lyf (key.2.trans (map_one _).symm)
  have hc : c = 1 := cycHom_injective 3 lyh orderOf_lyh (hw1.trans (map_one _).symm)
  rw [ha, hb, hc]
  rfl

@[expose] def c223HomCQ :
    C223 →* lyCQ :=
  MonoidHom.codRestrict (M := C223) (N := J) c223Hom lyCQ c223Hom_mem

theorem c223HomCQ_bijective :
    Function.Bijective c223HomCQ :=
  Function.Injective.bijective_of_nat_card_le
    (fun x y h => by
      have h' := congrArg Subtype.val h
      exact c223Hom_injective h')
    (by rw [card_C223]; exact card_lyCQ_le)

theorem exists_mulEquiv_lyCQ :
    Nonempty (lyCQ ≃* C223) :=
  ⟨(MulEquiv.ofBijective (M := C223) (N := lyCQ) c223HomCQ c223HomCQ_bijective).symm⟩

theorem isSolvable_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Group.IsSolvable H) : Group.IsSolvable G :=
  Group.isSolvable_of_isSolvable_injective (f := (e : G →* H)) e.injective

theorem isSolvable_mulAut_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Group.IsSolvable (MulAut H)) : Group.IsSolvable (MulAut G) :=
  isSolvable_of_mulEquiv (MulAut.congr e) h

theorem isSolvable_lyCQ :
    Group.IsSolvable lyCQ := by
  obtain ⟨e⟩ := exists_mulEquiv_lyCQ
  exact isSolvable_of_mulEquiv (G := lyCQ) (H := C223) e inferInstance

theorem isSolvable_mulAut_lyCQ :
    Group.IsSolvable (MulAut lyCQ) := by
  obtain ⟨e⟩ := exists_mulEquiv_lyCQ
  exact isSolvable_mulAut_of_mulEquiv (G := lyCQ) (H := C223) e isSolvable_mulAut_C223

theorem lyCQ_le_lyN :
    lyCQ ≤ lyN := Subgroup.centralizer_le_normalizer _

theorem lyQ_le_lyN : lyQ ≤ lyN := Subgroup.le_normalizer

abbrev lyCQN :
    Subgroup lyN := Subgroup.centralizer ((lyQ.subgroupOf lyN : Subgroup lyN) : Set lyN)

theorem coe_mem_lyCQ (x : lyCQN) : ((x : lyN) : J) ∈ lyCQ := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h := Subgroup.mem_centralizer_iff.1 x.2 ⟨q, lyQ_le_lyN hq⟩ (by
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hq)
  have h' := congrArg Subtype.val h
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
  exact h'

@[expose] def centralizerHom : lyCQN →* lyCQ :=
  MonoidHom.codRestrict (M := lyCQN) (N := J) (lyN.subtype.comp lyCQN.subtype) lyCQ coe_mem_lyCQ

theorem centralizerHom_bijective :
    Function.Bijective centralizerHom := by
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  · refine ⟨⟨⟨y, lyCQ_le_lyN y.2⟩, ?_⟩, Subtype.ext rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hq
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_iff.1 y.2 _ hq

@[expose] def centralizerEquiv : lyCQN ≃* lyCQ :=
  MulEquiv.ofBijective (M := lyCQN) (N := lyCQ) centralizerHom centralizerHom_bijective

instance lyQ_normal_lyN :
    (lyQ.subgroupOf lyN).Normal := Subgroup.normal_in_normalizer

theorem isSolvable_fixes_Q :

    Group.IsSolvable (pointwiseFixingAut (lyQ.subgroupOf lyN)) := by
  have hT : Group.IsSolvable lyCQN :=
    isSolvable_of_mulEquiv (G := lyCQN) (H := lyCQ) centralizerEquiv isSolvable_lyCQ
  have hAT : Group.IsSolvable (MulAut lyCQN) :=
    isSolvable_mulAut_of_mulEquiv (G := lyCQN) (H := lyCQ) centralizerEquiv
      isSolvable_mulAut_lyCQ
  obtain ⟨-, -, -, -, hsolv⟩ := centralizer_automorphism_kernel _ hT hAT
  exact hsolv

theorem local_automorphism_bounds :
    IsPGroup 2 (pointwiseFixingAut (lyS.subgroupOf lyC)) ∧
    Nonempty (Subgroup.centralizer (lyQ : Set J) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 3)) ∧
    Group.IsSolvable (pointwiseFixingAut (lyQ.subgroupOf lyN)) :=
  ⟨isPGroup_fixes_S, exists_mulEquiv_lyCQ, isSolvable_fixes_Q⟩

end CFSG.Sporadic.LySchreier
