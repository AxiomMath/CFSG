module

public import CFSG.YGroups.DCE.B433Y333
public import CFSG.YGroups.DCE.FixUpper
public import CFSG.YGroups.DCE.FixForest
public import CFSG.YGroups.DCE.SiftChain

public section

namespace CFSG.YGroups.DCE.B433

open CFSG.YGroups.DCE.B433Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

@[expose] def dWord : Array ℕ := #[0, 1, 2, 3, 8, 9, 5]

@[expose] noncomputable def dY : YGroup 4 3 2 := evalWord (yGen 4 3 2) dWord.toList ^ 9

@[expose] def dArr (L : Array ByteArray) : ByteArray :=
  (List.range 9).foldl (fun acc _ => bcomp 31671 acc (wordB L dWord)) (bid 31671)

theorem dArr_rep {L : Array ByteArray}
    (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l))) :
    RepB 31671 (dArr L) (rho432F dY) := by
  have hw : RepB 31671 (wordB L dWord) (rho432F (evalWord (yGen 4 3 2) dWord.toList)) :=
    wordB_rep hL dWord (by decide)
  have key : ∀ m, RepB 31671 ((List.range m).foldl
      (fun acc _ => bcomp 31671 acc (wordB L dWord)) (bid 31671))
      (rho432F (evalWord (yGen 4 3 2) dWord.toList ^ m)) := by
    intro m
    induction m with
    | zero => simpa using repB_bid (by norm_num)
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, pow_succ,
        map_mul]
      exact repB_bcomp (by norm_num) ih hw
  exact key 9

@[expose] def wordPt (L : Array ByteArray) (w : Array ℕ) (x : ℕ) : ℕ :=
  w.foldr (fun l acc => bget L[l]! acc) x

theorem wordPt_spec {L : Array ByteArray}
    (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l))) {w : Array ℕ}
    (hw : ∀ l ∈ w, l < 10) {x : ℕ} (hx : x < 31671) :
    wordPt L w x = (rho432F (evalWord (yGen 4 3 2) w.toList) ⟨x, hx⟩ : ℕ) := by
  have hw' : ∀ l ∈ w.toList, l < 10 := fun l hl => hw l (Array.mem_toList_iff.1 hl)
  unfold wordPt
  rw [← Array.foldr_toList]
  generalize w.toList = ws at hw' ⊢
  induction ws with
  | nil => simp [evalWord_nil]
  | cons a ws ih =>
    rw [List.foldr_cons, ih fun l hl => hw' l (List.mem_cons_of_mem _ hl), evalWord_cons,
      map_mul, Equiv.Perm.mul_apply]
    exact (hL a (hw' a List.mem_cons_self)).2 _

@[expose] def transWords (L : Array ByteArray) : Array (Array ℕ) := Id.run do
  let n := 31671
  let mut par : Array ℕ := Array.replicate n n
  let mut lab : Array ℕ := Array.replicate n 0
  let mut order : Array ℕ := #[0]
  par := par.set! 0 0
  let mut h := 0
  for _ in [0:n] do
    if h < order.size then
      let x := order[h]!
      h := h + 1
      for l in [0:10] do
        let y := bget L[l]! x
        if y < n && par[y]! == n then
          par := par.set! y x
          lab := lab.set! y l
          order := order.push y
    else
      break
  let mut words : Array (Array ℕ) := Array.replicate n #[]
  for i in [1:order.size] do
    let y := order[i]!
    words := words.set! y (#[lab[y]!] ++ words[par[y]!]!)
  return words

@[expose] def transOK
    (L : Array ByteArray) (W : Array (Array ℕ)) : Bool :=
  W.size == 31671 && allLt 31671 fun ω => W[ω]!.all (· < 10) && wordPt L W[ω]! 0 == ω

@[expose] noncomputable def tau (W : Array (Array ℕ)) (ω : ℕ) : YGroup 4 3 2 :=
  evalWord (yGen 4 3 2) W[ω]!.toList

theorem tau_spec
    {L : Array ByteArray} (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l)))
    {W : Array (Array ℕ)} (hW : transOK L W = true) {ω : ℕ} (hω : ω < 31671) :
    (∀ l ∈ W[ω]!, l < 10) ∧ rho432F (tau W ω) 0 = ⟨ω, hω⟩ := by
  unfold transOK at hW
  simp only [Bool.and_eq_true, beq_iff_eq] at hW
  have h := allLt_spec hW.2 hω
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem, decide_eq_true_eq]
    at h
  refine ⟨h.1, Fin.ext ?_⟩
  have h2 := wordPt_spec hL h.1 (show 0 < 31671 by norm_num)
  rw [h.2] at h2
  exact h2.symm

theorem orbit_pt0_eq_univ
    {L : Array ByteArray}
    (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l))) {W : Array (Array ℕ)}
    (hW : transOK L W = true) : MulAction.orbit (YGroup 4 3 2) pt0 = Set.univ := by
  refine Set.eq_univ_of_forall fun ω => ?_
  obtain ⟨-, hτ⟩ := tau_spec hL hW (ofPt ω).2
  refine ⟨tau W (ofPt ω).1, ?_⟩
  show tau W (ofPt ω).1 • pt0 = ω
  rw [pt0, smul_toPt, hτ]
  rfl

@[expose] def dConj (L : Array ByteArray) (W : Array (Array ℕ)) (ω : ℕ) : ByteArray :=
  bcomp 31671 (bcomp 31671 (wordB L W[ω]!) (dArr L)) (binvCand 31671 (wordB L W[ω]!))

theorem dConj_rep
    {L : Array ByteArray}
    (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l)))
    {W : Array (Array ℕ)} (hW : transOK L W = true) {ω : ℕ} (hω : ω < 31671)
    (hinv : bisInv 31671 (wordB L W[ω]!) (binvCand 31671 (wordB L W[ω]!)) = true) :
    RepB 31671 (dConj L W ω) (rho432F (tau W ω * dY * (tau W ω)⁻¹)) := by
  have h1 : RepB 31671 (wordB L W[ω]!) (rho432F (tau W ω)) :=
    wordB_rep hL W[ω]! (tau_spec hL hW hω).1
  rw [map_mul, map_mul, map_inv]
  exact repB_bcomp (by norm_num) (repB_bcomp (by norm_num) h1 (dArr_rep hL)) (repB_binv h1 hinv)

theorem rho_conj_eq
    {W : Array (Array ℕ)} {ω : ℕ} (hω : ω < 31671)
    (hτ : rho432F (tau W ω) 0 = ⟨ω, hω⟩)
    (hJ : ∀ j ∈ J432, rho432F j * rho432F dY = rho432F dY * rho432F j)
    (hstab : MulAction.stabilizer (YGroup 4 3 2) pt0 = J432) {e : YGroup 4 3 2}
    (he : e⁻¹ • pt0 = toPt ⟨ω, hω⟩) :
    rho432F (e⁻¹ * dY * e) = rho432F (tau W ω * dY * (tau W ω)⁻¹) := by
  have hj : (tau W ω)⁻¹ * e⁻¹ ∈ J432 := by
    rw [← hstab, MulAction.mem_stabilizer_iff, mul_smul, he, pt0]
    show toPt (rho432F (tau W ω)⁻¹ ⟨ω, hω⟩) = toPt 0
    rw [map_inv, ← hτ, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have hc := hJ _ hj
  have e1 : e⁻¹ = tau W ω * ((tau W ω)⁻¹ * e⁻¹) := by group
  rw [show e⁻¹ * dY * e = e⁻¹ * dY * (e⁻¹)⁻¹ by group, e1]
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
  have hc' : rho432F (tau W ω)⁻¹ * rho432F e⁻¹ * rho432F dY =
      rho432F dY * (rho432F (tau W ω)⁻¹ * rho432F e⁻¹) := by
    simpa only [map_mul] using hc
  rw [map_inv, map_inv] at hc'
  calc rho432F (tau W ω) * ((rho432F (tau W ω))⁻¹ * (rho432F e)⁻¹) * rho432F dY *
        ((rho432F e) * rho432F (tau W ω)) * (rho432F (tau W ω))⁻¹
      = rho432F (tau W ω) * (((rho432F (tau W ω))⁻¹ * (rho432F e)⁻¹) * rho432F dY) *
        ((rho432F e) * rho432F (tau W ω)) * (rho432F (tau W ω))⁻¹ := by group
    _ = rho432F (tau W ω) * (rho432F dY * ((rho432F (tau W ω))⁻¹ * (rho432F e)⁻¹)) *
        ((rho432F e) * rho432F (tau W ω)) * (rho432F (tau W ω))⁻¹ := by rw [hc']
    _ = rho432F (tau W ω) * rho432F dY * (rho432F (tau W ω))⁻¹ := by group

@[expose] def dCommOK (L : Array ByteArray) (d0 : ByteArray) : Bool :=
  allLt 10 fun c => c == 4 || bEq 31671 (bcomp 31671 L[c]! d0) (bcomp 31671 d0 L[c]!)

theorem dComm_spec {L : Array ByteArray}
    (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l)))
    (h : dCommOK L (dArr L) = true) :
    ∀ j ∈ J432, rho432F j * rho432F dY = rho432F dY * rho432F j := by
  have hd := dArr_rep hL
  have hle : J432 ≤ (Subgroup.centralizer {rho432F dY}).comap rho432F := by
    rw [J432, Subgroup.closure_le]
    rintro _ ⟨c, ⟨hc, hc4⟩, rfl⟩
    have := allLt_spec h hc
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    rcases this with h4 | hb
    · exact absurd h4 hc4
    · rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (bEq_iff (repB_bcomp (by norm_num) (hL c hc) hd)
        (repB_bcomp (by norm_num) hd (hL c hc))).1 hb
  intro j hj
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hj)

@[expose] def dNe (L : Array ByteArray) (W : Array (Array ℕ)) (d0 : ByteArray) (ω : ℕ) : Bool :=
  !allLt 31671 fun y => wordPt L W[ω]! (bget d0 y) == bget d0 (wordPt L W[ω]! y)

theorem dNe_spec
    {L : Array ByteArray}
    (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l)))
    {W : Array (Array ℕ)} (hW : transOK L W = true) {ω : ℕ} (hω : ω < 31671)
    (h : dNe L W (dArr L) ω = true) :
    rho432F (tau W ω) * rho432F dY ≠ rho432F dY * rho432F (tau W ω) := by
  intro heq
  have hd := dArr_rep hL
  have hlet := (tau_spec hL hW hω).1
  unfold dNe at h
  have h' : ¬ (allLt 31671 fun y =>
      wordPt L W[ω]! (bget (dArr L) y) == bget (dArr L) (wordPt L W[ω]! y)) = true := by
    intro H
    simp [H] at h
  rw [allLt_iff] at h'
  push Not at h'
  obtain ⟨y, hy, hne⟩ := h'
  have h1 := congrArg (fun σ : Equiv.Perm (Fin 31671) => (σ ⟨y, hy⟩ : ℕ)) heq
  simp only [Equiv.Perm.mul_apply] at h1
  apply hne
  rw [beq_iff_eq]
  have e1 := wordPt_spec hL hlet (rho432F dY ⟨y, hy⟩).2
  have e2 := wordPt_spec hL hlet hy
  rw [Fin.eta] at e1
  rw [hd.apply hy, e1, e2,
    hd.apply (rho432F (evalWord (yGen 4 3 2) W[ω]!.toList) ⟨y, hy⟩).2, Fin.eta]
  exact h1

@[expose] def chainLevels {E : B.EnvB} (st : B.RSt E) (fin : B.NodeFin) :
    Array (ℕ × Array ByteArray) :=
  fin.chain.map fun lv => (lv.1, (slotGens st lv.2).map (·.1.2))

@[expose] def chainOK {E : B.EnvB} (st : B.RSt E) (j : ℕ) (fin : B.NodeFin) : Bool :=
  4089470473293004800 % E.chainBound st fin == 0 &&
    allLt fin.chain.size fun m =>
      decide (fin.chain[m]!.1 < 31671) &&
        (slotGens st fin.chain[m]!.2).all (fun s => s.1.1 == j) &&
        ((slotGens st fin.chain[m]!.2).map (·.1.2)).all (fun t =>
          bisInv 31671 t (binvCand 31671 t) &&
            allLt m fun m' => bget t fin.chain[m']!.1 == fin.chain[m']!.1) &&
        recValidN 31671 fin.chain[m]!.1 ((slotGens st fin.chain[m]!.2).map (·.1.2))
          (B.orbitRec 31671 fin.chain[m]!.1 ((slotGens st fin.chain[m]!.2).map (·.1.2)))

@[expose] def fixCount (L : Array ByteArray) (W : Array (Array ℕ)) (G : Array ByteArray)
    (levels : Array (ℕ × Array ByteArray)) : Option ℕ :=
  let f := forestRec 31671 G
  let pass : Array Bool := (Array.range 31671).map fun r =>
    f.2.2.2[r]! == r && siftB 31671 levels (dConj L W r)
  if forestValid 31671 G f && allLt 31671 (fun r => f.2.2.2[r]! != r ||
      bisInv 31671 (wordB L W[r]!) (binvCand 31671 (wordB L W[r]!))) then
    some ((List.range 31671).foldl (fun a w => if pass[f.2.2.2[w]!]! then a + 1 else a) 0)
  else none

@[expose] def nodeFix {E : B.EnvB} (st : B.RSt E) (L : Array ByteArray) (W : Array (Array ℕ))
    (fin : ℕ × B.NodeFin) : Option ℕ :=
  if (chainOK st fin.1 fin.2 && (slotGens st (allSlots fin.2)).all (fun s => s.1.1 == fin.1)) then
    fixCount L W ((slotGens st (allSlots fin.2)).map (·.1.2)) (chainLevels st fin.2)
  else none

@[expose] def fixTotalOK {E : B.EnvB} (st : B.RSt E) (fins : Array (ℕ × B.NodeFin))
    (counts : Array (Option ℕ)) : Bool :=
  allLt counts.size (fun l => counts[l]!.isSome) &&
    decide ((List.range fins.size).foldl (fun a l =>
      a + 4089470473293004800 / E.chainBound st fins[l]!.2 * counts[l]!.getD 0) 0 ≤
        75086567571456)

@[expose] def fixCheckSt
    {E : B.EnvB} (st : B.RSt E) (L : Array ByteArray) (W : Array (Array ℕ))
    (d0 : ByteArray) (fins : Array (ℕ × B.NodeFin)) : Bool :=
  transOK L W && allLt 10 (fun c => c == 4 || bget L[c]! 0 == 0) && dCommOK L d0 &&
    allLt 31671 (fun ω => ω == 0 || dNe L W d0 ω) &&
    fixTotalOK st fins (fins.map fun fin => nodeFix st L W fin)

@[expose] def fixCheck :
    Bool :=
  let L := lettersB ()
  let O := omegaB433 L
  let cert := certB433 ()
  if h : bigOK O L fixB = true ∧ smallOK O L cert = true then
    let S : Checked L O cert := ⟨rfl, rfl, h.1, h.2⟩
    let E := env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK
    fixCheckSt (B.replay E cert.prog) L (transWords L) (dArr L) cert.fins
  else false

section Node

variable {L : Array ByteArray} {O : BigOmega} {cert : B.Cert} (S : Checked L O cert)

theorem slotGens_rep
    {st : B.RSt (env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK)}
    {j : ℕ} {sl : Array ℕ} (hall : (slotGens st sl).all (fun s => s.1.1 == j) = true)
    {i : ℕ} (hi : i < ((slotGens st sl).map (·.1.2)).size) :
    ∃ e ∈ B.stabSub (setup S.good) (xNode S.good S.pt (ctxB433 O L cert).nodes j),
      RepB 31671 ((slotGens st sl).map (·.1.2))[i]! (rho432F e) := by
  have hi' : i < (slotGens st sl).size := by simpa using hi
  set w := (slotGens st sl)[i]'hi'
  have hwj : w.1.1 = j := by
    have := Array.all_eq_true_iff_forall_mem.1 hall w (Array.getElem_mem hi')
    simpa using this
  obtain ⟨e, hrep, he⟩ := w.2
  refine ⟨e, (B.mem_stabSub _ _ _).2 ?_, ?_⟩
  · rw [← hwj]
    exact he
  · have : ((slotGens st sl).map (·.1.2))[i]! = w.1.2 := by
      rw [getElem!_pos _ i hi]
      simp [w]
    rw [this]
    exact hrep

private theorem all_getElem! {α : Type} [Inhabited α] {a : Array α} {p : α → Bool}
    (h : a.all p = true) {i : ℕ} (hi : i < a.size) : p a[i]! = true := by
  rw [getElem!_pos a i hi]
  exact Array.all_eq_true_iff_forall_mem.1 h _ (Array.getElem_mem hi)

theorem nodeFix_spec
    {st : B.RSt (env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK)}
    {W : Array (Array ℕ)} (hW : transOK L W = true)
    (hJc : ∀ j ∈ J432, rho432F j * rho432F dY = rho432F dY * rho432F j)
    (hstab : MulAction.stabilizer (YGroup 4 3 2) pt0 = J432) {fin : ℕ × B.NodeFin} {c : ℕ}
    (hidx : (B.stabSub (setup S.good) (xNode S.good S.pt (ctxB433 O L cert).nodes fin.1)).index =
      4089470473293004800 /
        (env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK).chainBound st fin.2)
    (hnode : nodeFix st L W fin = some c) :
    ∃ Xc : Finset Pt432, Xc.card = c ∧
      (setup S.good).fixLabels (xNode S.good S.pt (ctxB433 O L cert).nodes fin.1) dY pt0 ⊆
        Xc := by
  classical
  have := finite_y432
  have hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l)) := fun l hl => S.letters_rep hl
  have hn : (env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK).C.n = 31671 :=
    S.ctxGood.n_eq
  set y := xNode S.good S.pt (ctxB433 O L cert).nodes fin.1 with hy
  set T := B.stabSub (setup S.good) y with hT
  set K : Subgroup (Equiv.Perm (Fin 31671)) := T.map rho432F with hK
  have hok : (chainOK st fin.1 fin.2 &&
      (slotGens st (allSlots fin.2)).all (fun s => s.1.1 == fin.1)) = true := by
    by_contra hcon
    rw [nodeFix, ite_eq_right hcon] at hnode
    cases hnode
  rw [nodeFix, ite_eq_left hok] at hnode
  rw [Bool.and_eq_true] at hok
  obtain ⟨hchain, hall⟩ := hok
  set G := (slotGens st (allSlots fin.2)).map (·.1.2) with hGdef
  set lv := chainLevels st fin.2 with hlv
  set f := forestRec 31671 G with hf
  set pass : Array Bool := (Array.range 31671).map fun r =>
    f.2.2.2[r]! == r && siftB 31671 lv (dConj L W r) with hpass
  have hc : (if forestValid 31671 G f && allLt 31671 (fun r => f.2.2.2[r]! != r ||
      bisInv 31671 (wordB L W[r]!) (binvCand 31671 (wordB L W[r]!))) then
      some ((List.range 31671).foldl (fun a w => if pass[f.2.2.2[w]!]! then a + 1 else a) 0)
    else none) = some c := hnode
  have hval : (forestValid 31671 G f && allLt 31671 (fun r => f.2.2.2[r]! != r ||
      bisInv 31671 (wordB L W[r]!) (binvCand 31671 (wordB L W[r]!)))) = true := by
    by_contra hcon
    rw [ite_eq_right hcon] at hc
    cases hc
  rw [ite_eq_left hval] at hc
  have hcount : (List.range 31671).foldl (fun a w => if pass[f.2.2.2[w]!]! then a + 1 else a) 0 =
      c := Option.some.inj hc
  rw [Bool.and_eq_true] at hval
  obtain ⟨hforest, hinvs⟩ := hval
  have hGK : ∀ i < G.size, ∃ g ∈ K, RepB 31671 G[i]! g := by
    intro i hi
    obtain ⟨e, he, hrep⟩ := slotGens_rep S hall hi
    exact ⟨_, Subgroup.mem_map_of_mem _ he, hrep⟩
  unfold chainOK at hchain
  rw [Bool.and_eq_true, beq_iff_eq] at hchain
  obtain ⟨hdvd, hlev⟩ := hchain
  set k := fin.2.chain.size with hk
  let β : ℕ → Fin 31671 := fun m => ⟨fin.2.chain[m]!.1 % 31671, Nat.mod_lt _ (by norm_num)⟩
  let gens : ℕ → Array ByteArray := fun m => (slotGens st fin.2.chain[m]!.2).map (·.1.2)
  have hlv' : ∀ m < k, fin.2.chain[m]!.1 < 31671 ∧
      (slotGens st fin.2.chain[m]!.2).all (fun s => s.1.1 == fin.1) = true ∧
      (gens m).all (fun t => bisInv 31671 t (binvCand 31671 t) &&
        allLt m fun m' => bget t fin.2.chain[m']!.1 == fin.2.chain[m']!.1) = true ∧
      recValidN 31671 fin.2.chain[m]!.1 (gens m)
        (B.orbitRec 31671 fin.2.chain[m]!.1 (gens m)) = true := by
    intro m hm
    have := allLt_spec hlev hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
    exact ⟨h1, h2, h3, h4⟩
  have hβv : ∀ m < k, (β m : ℕ) = fin.2.chain[m]!.1 := fun m hm =>
    Nat.mod_eq_of_lt (hlv' m hm).1
  have hgen : ∀ m < k, ∀ i < (gens m).size, ∃ g ∈ K, RepB 31671 (gens m)[i]! g ∧
      ∀ m' < m, g (β m') = β m' := by
    intro m hm i hi
    obtain ⟨-, hj, hall', -⟩ := hlv' m hm
    obtain ⟨e, he, hrep⟩ := slotGens_rep S hj hi
    refine ⟨_, Subgroup.mem_map_of_mem _ he, hrep, fun m' hm' => ?_⟩
    have ht := all_getElem! hall' hi
    simp only [Bool.and_eq_true] at ht
    have hfx := allLt_spec ht.2 hm'
    rw [beq_iff_eq] at hfx
    apply Fin.ext
    have h1 := hrep.apply (β m').2
    rw [Fin.eta] at h1
    rw [← h1, hβv m' (by omega)]
    exact hfx
  have hinv : ∀ m < k, ∀ i < (gens m).size,
      bisInv 31671 (gens m)[i]! (binvCand 31671 (gens m)[i]!) = true := by
    intro m hm i hi
    have ht := all_getElem! (hlv' m hm).2.2.1 hi
    simp only [Bool.and_eq_true] at ht
    exact ht.1
  have hrec : ∀ m < k, recValidN 31671 (β m) (gens m) (B.orbitRec 31671 (β m) (gens m)) =
      true := by
    intro m hm
    rw [hβv m hm]
    exact (hlv' m hm).2.2.2
  have hkerT : rho432F.ker ≤ T := by
    intro e he
    rw [hT, B.mem_stabSub]
    have h1 : (setup S.good).ψ e = 1 := ker_rho432F_le_ker_psi he
    rw [h1, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hTK := index_mul_card_map_of_ker_le rho432F T hkerT
  rw [card_range_rho432F, hidx] at hTK
  set cb := (env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK).chainBound st fin.2
    with hcb
  have hcbdvd : cb ∣ 4089470473293004800 := Nat.dvd_of_mod_eq_zero hdvd
  have hcbpos : 0 < cb := by
    rcases Nat.eq_zero_or_pos cb with h0 | h0
    · rw [h0, Nat.mod_zero] at hdvd
      norm_num at hdvd
    · exact h0
  have hdiv : cb * (4089470473293004800 / cb) = 4089470473293004800 := Nat.mul_div_cancel' hcbdvd
  have hq : 0 < 4089470473293004800 / cb :=
    Nat.div_pos (Nat.le_of_dvd (by norm_num) hcbdvd) hcbpos
  have hKcb : Nat.card K = cb := by
    refine Nat.eq_of_mul_eq_mul_left hq ?_
    rw [hTK, mul_comm, hdiv]
  have hprod : cb = ∏ m ∈ Finset.range k, (B.orbitRec 31671 (β m) (gens m)).1.size := by
    rw [hcb, B.EnvB.chainBound_eq]
    refine Finset.prod_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.1 hm
    rw [hβv m hm']
    unfold B.EnvB.levelLen
    rw [hn]
    show _ = (B.orbitRec 31671 fin.2.chain[m]!.1
      ((slotGens st fin.2.chain[m]!.2).map (·.1.2))).1.size
    rcases fin.2.chain[m]! with ⟨b, sl⟩
    rfl
  have hcardK : Nat.card K ≤ ∏ m ∈ Finset.range k, (B.orbitRec 31671 (β m) (gens m)).1.size :=
    (hKcb.trans hprod).le
  have hlsize : lv.size = k := by
    rw [hlv, chainLevels, Array.size_map]
  have hlget : ∀ m < k, lv[m]! = ((β m : ℕ), gens m) := by
    intro m hm
    rw [hlv, chainLevels, BigOmega.getElem!_map_lt hm, hβv m hm]
  let P : ℕ → Bool := fun w => pass[f.2.2.2[w]!]!
  refine ⟨Finset.univ.filter fun ω : Pt432 => P (ofPt ω).1 = true, ?_, ?_⟩
  · rw [← hcount]
    exact card_filter_fin 31671 P
  intro ω hω
  rw [Finset.mem_coe, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  set w := (ofPt ω).1 with hw
  have hwlt : w < 31671 := (ofPt ω).2
  obtain ⟨hr, hrr, g, hgK, hg⟩ := forestValid_spec hforest K hGK w hwlt
  set r := f.2.2.2[w]! with hrdef
  obtain ⟨s, hsT, rfl⟩ := Subgroup.mem_map.1 hgK
  have hsω : s • toPt ⟨r, hr⟩ = ω := by
    rw [smul_toPt, hg]
    rfl
  have hfixr : toPt ⟨r, hr⟩ ∈ (setup S.good).fixLabels y dY pt0 := by
    have := SymGen.Setup.smul_mem_fixLabels (S := setup S.good) hω (inv_mem hsT)
    rwa [← hsω, inv_smul_smul] at this
  obtain ⟨e', he', hed'⟩ := hfixr
  have hτ := tau_spec hL hW hr
  have hconj := rho_conj_eq hr hτ.2 hJc hstab he'
  have hinvr : bisInv 31671 (wordB L W[r]!) (binvCand 31671 (wordB L W[r]!)) = true := by
    have := allLt_spec hinvs hr
    simpa [hrr] using this
  have hrep := dConj_rep hL hW hr hinvr
  have hmemK : rho432F (tau W r * dY * (tau W r)⁻¹) ∈ K := by
    rw [← hconj]
    exact Subgroup.mem_map_of_mem _ hed'
  have hsift := siftB_of_mem (by norm_num) hgen hinv hrec hcardK hlsize hlget hmemK hrep
  show pass[r]! = true
  rw [hpass, BigOmega.getElem!_map_lt (by simpa using hr), BigOmega.getElem!_range_lt hr]
  simp [hrr, hsift]

end Node

theorem card_centralizer_psi_le
    {L : Array ByteArray}
    (hL : ∀ l < 10, RepB 31671 L[l]! (rho432F (yGen 4 3 2 l))) {W : Array (Array ℕ)}
    (hW : transOK L W = true)
    (hJc : ∀ j ∈ J432, rho432F j * rho432F dY = rho432F dY * rho432F j)
    (hstab : MulAction.stabilizer (YGroup 4 3 2) pt0 = J432)
    (hne : allLt 31671 (fun ω => ω == 0 || dNe L W (dArr L) ω) = true)
    (hpsi : 4089470473293004800 ≤ Nat.card psi.range) :
    Nat.card ((Subgroup.centralizer {psi dY}).subgroupOf psi.range) ≤ 129123503308800 := by
  classical
  have := finite_y432
  have := B433_finite_card_le.1
  have hker : psi.ker = rho432F.ker := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ker_rho432F_le_ker_psi ?_
    rw [card_ker_rho432F]
    have h1 := Subgroup.card_ker_mul_card_range psi
    have h2 := Subgroup.card_ker_mul_card_range rho432F
    rw [card_range_rho432F, card_ker_rho432F] at h2
    by_contra hlt
    rw [not_le] at hlt
    have h3 : 3 * 4089470473293004800 ≤ Nat.card psi.ker * Nat.card psi.range :=
      Nat.mul_le_mul hlt hpsi
    omega
  have hle : Subgroup.centralizer {psi dY} ⊓ psi.range ≤ J432.map psi := by
    rintro z ⟨hz, ⟨e, rfl⟩⟩
    have hc : psi e * psi dY = psi dY * psi e := Subgroup.mem_centralizer_singleton_iff.1 hz
    have hk : e * dY * e⁻¹ * dY⁻¹ ∈ psi.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    rw [hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hk
    have hcρ : rho432F e * rho432F dY * (rho432F e)⁻¹ = rho432F dY :=
      mul_inv_eq_one.1 hk
    set ω := (rho432F e 0 : ℕ) with hω
    have hωlt : ω < 31671 := (rho432F e 0).2
    by_cases h0 : ω = 0
    · refine ⟨e, ?_, rfl⟩
      rw [SetLike.mem_coe, ← hstab, MulAction.mem_stabilizer_iff, pt0, smul_toPt, toPt_inj]
      exact Fin.ext h0
    · exfalso
      have hd := allLt_spec hne hωlt
      simp only [Bool.or_eq_true, beq_iff_eq, h0, false_or] at hd
      apply dNe_spec hL hW hωlt hd
      have hτ := (tau_spec hL hW hωlt).2
      have hconj := rho_conj_eq hωlt hτ hJc hstab (e := e⁻¹)
        (by rw [inv_inv, pt0, smul_toPt])
      rw [inv_inv, map_mul, map_mul, map_inv, hcρ, map_mul, map_mul, map_inv] at hconj
      calc rho432F (tau W ω) * rho432F dY
          = rho432F (tau W ω) * rho432F dY * (rho432F (tau W ω))⁻¹ * rho432F (tau W ω) := by
            group
        _ = rho432F dY * rho432F (tau W ω) := by rw [← hconj]
  have hJmap : Nat.card (J432.map psi) ≤ 129123503308800 := by
    have hkerJ : psi.ker ≤ J432 := by
      rw [hker, ← hstab]
      intro e he
      rw [MulAction.mem_stabilizer_iff, pt0, smul_toPt, MonoidHom.mem_ker.1 he]
      rfl
    have h1 := index_mul_card_map_of_ker_le psi J432 hkerJ
    have h2 : J432.index = 31671 := by
      rw [← hstab, MulAction.index_stabilizer, orbit_pt0_eq_univ hL hW, Set.ncard_univ,
        card_pt432]
    rw [h2] at h1
    have h3 := card_range_psi_le
    omega
  calc Nat.card ((Subgroup.centralizer {psi dY}).subgroupOf psi.range)
      = Nat.card (((Subgroup.centralizer {psi dY}).subgroupOf psi.range).map
          psi.range.subtype) :=
        (Subgroup.card_map_of_injective psi.range.subtype_injective).symm
    _ = Nat.card (Subgroup.centralizer {psi dY} ⊓ psi.range : Subgroup B433) := by
        rw [Subgroup.subgroupOf_map_subtype]
    _ ≤ Nat.card (J432.map psi) := Subgroup.card_le_of_le hle
    _ ≤ 129123503308800 := hJmap

end CFSG.YGroups.DCE.B433
