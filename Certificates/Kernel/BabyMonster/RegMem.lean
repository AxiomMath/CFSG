module

public import CFSG.Certificates.Kernel.BabyMonster.RegRun
public import Certificates.Kernel.BabyMonster.MemChain
public meta import Certificates.Kernel.BabyMonster.RegTab
public import Certificates.Kernel.BabyMonster.RegTab

public section

namespace CFSG.KC.BM.Reg

open CFSG.KC.BM

@[expose] def MemsOK (srcs tgts : List (List ℕ)) : Prop :=
  ∀ S : Submonoid Mat, (∀ a ∈ srcs, stripMat a ∈ S) → ∀ t ∈ tgts, stripMat t ∈ S

@[expose] def memRun : List ℕ → List Ent → List ℕ
  | M, [] => M
  | M, (A, Ws, some c, []) :: t => memRun (cond ((A :: Ws).all (memB · M)) (c :: M) M) t
  | M, (A, [b], none, []) :: t => memRun (cond (memB A M) (b :: M) M) t
  | M, _ :: t => memRun M t

theorem wv_mem {S : Submonoid Mat} {val : ℕ → Mat} :
    ∀ w : List ℕ, (∀ i ∈ w, val i ∈ S) → wv val w ∈ S
  | [], _ => by rw [wv_nil]; exact S.one_mem
  | x :: w, h => by
    rw [wv_cons]
    exact S.mul_mem (h x List.mem_cons_self) (wv_mem w fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem allMem {M w : List ℕ} (h : w.all (memB · M) = true) : ∀ i ∈ w, i ∈ M := fun i hi =>
  memB_spec (List.all_eq_true.1 h i hi)

theorem memRun_sound {S : Submonoid Mat} {val : ℕ → Mat} :
    ∀ (tab : List Ent) (M : List ℕ), TabSound val tab → (∀ i ∈ M, val i ∈ S) →
      ∀ i ∈ memRun M tab, val i ∈ S
  | [], M, _, hM => hM
  | (A, Ws, some c, []) :: t, M, hs, hM => by
    have ht : TabSound val t := fun e he => hs e (List.mem_cons_of_mem _ he)
    have he := hs _ List.mem_cons_self
    simp only [lhsW, rhsW, wv_cons, wv_nil, mul_one] at he
    refine memRun_sound t _ ht ?_
    cases hc : (A :: Ws).all (memB · M)
    · simpa using hM
    · intro i hi
      rcases List.mem_cons.1 (by simpa [hc] using hi) with rfl | hi
      · rw [← he]
        have hl := allMem hc
        exact S.mul_mem (hM _ (hl A List.mem_cons_self))
          (wv_mem Ws fun j hj => hM j (hl j (List.mem_cons_of_mem _ hj)))
      · exact hM i hi
  | (A, [b], none, []) :: t, M, hs, hM => by
    have ht : TabSound val t := fun e he => hs e (List.mem_cons_of_mem _ he)
    have he := hs _ List.mem_cons_self
    simp only [lhsW, rhsW, wv_cons, wv_nil, mul_one] at he
    refine memRun_sound t _ ht ?_
    cases hc : memB A M
    · simpa using hM
    · intro i hi
      rcases List.mem_cons.1 (by simpa [hc] using hi) with rfl | hi
      · exact MemChain.mem_of_mul_eq_one (hM A (memB_spec hc)) he
      · exact hM i hi
  | (_, [], none, []) :: t, M, hs, hM =>
    memRun_sound t M (fun e he => hs e (List.mem_cons_of_mem _ he)) hM
  | (_, _ :: _ :: _, none, []) :: t, M, hs, hM =>
    memRun_sound t M (fun e he => hs e (List.mem_cons_of_mem _ he)) hM
  | (A, Ws, c, d :: ds) :: t, M, hs, hM => by
    have h := memRun_sound t M (fun e he => hs e (List.mem_cons_of_mem _ he)) hM
    cases c with
    | none => cases Ws with
      | nil => exact h
      | cons w Ws => cases Ws <;> exact h
    | some c => exact h

@[expose] def wfGrow : List ℕ → List Ent → List ℕ
  | K, [] => K
  | K, (_, _, some c, []) :: t => wfGrow (c :: K) t
  | K, _ :: t => wfGrow K t

theorem wfGrow_sound {L : List (List ℕ)} : ∀ (tab : List Ent) (K : List ℕ),
    (∀ i ∈ K, wfMat (L.getD i idStrips) = true) → wfOK K tab = true → TabOK L tab →
      ∀ i ∈ wfGrow K tab, wfMat (L.getD i idStrips) = true
  | [], _, hK, _, _ => hK
  | (A, Ws, C, Ds) :: t, K, hK, hw, htab => by
    obtain ⟨hs, htab⟩ := htab
    dsimp only at hs
    unfold wfOK at hw
    rw [Bool.and_eq_true, List.all_eq_true] at hw
    obtain ⟨hl, hw⟩ := hw
    have hA : wfMat (L.getD A idStrips) = true :=
      hK A (memB_spec (hl A (by simp [lhsW])))
    cases C with
    | none =>
      dsimp only at hw
      rw [Bool.and_eq_true] at hw
      obtain ⟨hD, hw⟩ := hw
      have hD := weq_spec hD
      subst hD
      exact wfGrow_sound t K hK hw htab
    | some c =>
      dsimp only at hw
      cases Ds with
      | cons d Ds =>
        have hD : weq (d :: Ds) [] = false := rfl
        rw [hD, cond_false, Bool.and_eq_true] at hw
        exact wfGrow_sound t K hK hw.2 htab
      | nil =>
        have hD : weq [] [] = true := rfl
        rw [hD, cond_true] at hw
        simp only [Option.elim_some, List.map_nil, map_mulW_nil] at hs
        have hc : wfMat (L.getD c idStrips) = true := wfMat_of_allStrips hA hs
        refine wfGrow_sound t (c :: K) (fun i hi => ?_) hw htab
        rcases List.mem_cons.1 hi with rfl | hi
        · exact hc
        · exact hK i hi

theorem memsCert {L : List (List ℕ)} {tab : List Ent} {wl M0 idx : List ℕ}
    {srcs tgts : List (List ℕ)} (hwl : WfL L wl) (htab : TabOK L tab) (hwf : wfOK wl tab = true)
    (hM : idx.all (memB · (memRun M0 tab)) = true)
    (hW : idx.all (memB · (wfGrow wl tab)) = true)
    (hs : M0.map (fun i => L.getD i idStrips) = srcs)
    (ht : idx.map (fun i => L.getD i idStrips) = tgts) :
    (∀ t ∈ tgts, wfMat t = true) ∧ MemsOK srcs tgts := by
  refine ⟨fun t htm => ?_, fun S hS t htm => ?_⟩
  · rw [← ht] at htm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 htm
    exact wfGrow_sound tab wl (wfL_spec hwl) hwf htab i (allMem hW i hi)
  have hts := wfOK_sound tab wl (wfL_spec hwl) hwf htab
  rw [← ht] at htm
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 htm
  exact memRun_sound (val := litV L) tab M0 hts
    (fun j hj => hS _ (hs ▸ List.mem_map_of_mem hj)) i (allMem hM i hi)

end CFSG.KC.BM.Reg

namespace CertificateChecks.KernelBM.Reg

open Lean Elab Tactic Meta

elab "bm_mem_cert " "[" ps:ident,* "]" : tactic => withMainContext do
  let Ps := ps.getElems.map (·.getId)
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  unless ty.isAppOfArity ``And 2 && (ty.getArg! 1).isAppOfArity ``CFSG.KC.BM.Reg.MemsOK 2 do
    throwError "bm_mem_cert: expected `(∀ t ∈ tgts, wfMat t = true) ∧ MemsOK srcs tgts`"
  let srcsE := (ty.getArg! 1).getArg! 0
  let tgtsE := (ty.getArg! 1).getArg! 1
  let some srcs ← names srcsE | throwError "bm_mem_cert: the sources are not constants"
  let some tgts ← names tgtsE | throwError "bm_mem_cert: the targets are not constants"
  let fams ← families Ps
  let mut defs : Std.HashMap Name CE := {}
  let mut invs : Std.HashMap Name CE := {}
  for e in fams do
    if e.c != `I && e.ds.isEmpty && !(e.a :: e.ws.toList).contains e.c && !defs.contains e.c then
      defs := defs.insert e.c e
  for e in fams do
    if e.c == `I && e.ds.isEmpty && e.ws.size == 1 && e.ws[0]! != e.a then
      let b := e.ws[0]!
      unless defs.contains b || invs.contains b do invs := invs.insert b e
  let deps (x : Name) : Array Name :=
    if srcs.contains x then #[]
    else match defs[x]? with
      | some e => #[e.a] ++ e.ws
      | none => match invs[x]? with
        | some e => #[e.a]
        | none => #[]
  let mut order : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array (Name × Bool) := tgts.reverse.map (·, false)
  while h : stack.size > 0 do
    let (x, done) := stack.back
    stack := stack.pop
    if done then
      order := order.push x
      continue
    if seen.contains x then continue
    unless srcs.contains x || defs.contains x || invs.contains x do
      throwError "bm_mem_cert: {x} is no source and has no defining entry"
    seen := seen.insert x
    stack := stack.push (x, true)
    for y in (deps x).reverse do
      unless seen.contains y do stack := stack.push (y, false)
  for s in srcs do
    unless seen.contains s do
      seen := seen.insert s
      order := order.push s
  let mut idx : Std.HashMap Name Nat := {}
  for x in order do idx := idx.insert x idx.size
  let ix (x : Name) : Nat := idx[x]!
  let mut tab : Array CE := #[]
  let mut wl : Array Name := #[]
  for x in order do
    if srcs.contains x then wl := wl.push x
    else match defs[x]? with
      | some e => tab := tab.push e
      | none =>
        let e := invs[x]!
        tab := tab.push e
        wl := wl.push x
  let optT := mkApp (mkConst ``Option [0]) natE
  let entT := prodT natE (prodT listNatE (prodT optT listNatE))
  let entE (e : CE) : Expr :=
    pairE natE (prodT listNatE (prodT optT listNatE)) (mkRawNatLit (ix e.a))
      (pairE listNatE (prodT optT listNatE) (natsE (e.ws.toList.map ix))
        (pairE optT listNatE (optE (if e.c == `I then none else some (ix e.c)))
          (natsE (e.ds.toList.map ix))))
  let LE := listE listNatE (order.toList.map mkConst)
  let tabE := listE entT (tab.toList.map entE)
  let mut htab := mkConst ``True.intro
  let mut suffix := mkApp (mkConst ``List.nil [0]) entT
  for k' in [0:tab.size] do
    let e := tab[tab.size - 1 - k']!
    let (pr, tyK) ← familyStrips e
    let rest := mkApp2 (mkConst ``CFSG.KC.BM.Reg.TabOK) LE suffix
    htab := mkApp4 (mkConst ``And.intro) tyK rest pr htab
    suffix := mkApp3 (mkConst ``List.cons [0]) entT (entE e) suffix
  let mut hwl := mkConst ``True.intro
  let mut wsuf := mkApp (mkConst ``List.nil [0]) natE
  for k' in [0:wl.size] do
    let x := wl[wl.size - 1 - k']!
    let .str pre s := x | throwError "bm_mem_cert: bad literal name {x}"
    let wn := Name.str pre ("wf_" ++ s)
    let some ci := (← getEnv).find? wn | throwError "bm_mem_cert: {x} has no {wn}"
    let rest := mkApp2 (mkConst ``CFSG.KC.BM.Reg.WfL) LE wsuf
    hwl := mkApp4 (mkConst ``And.intro) ci.type rest (mkConst wn) hwl
    wsuf := mkApp3 (mkConst ``List.cons [0]) natE (mkRawNatLit (ix x)) wsuf
  let lt := mkApp (mkConst ``List [0]) listNatE
  let pf := mkAppN (mkConst ``CFSG.KC.BM.Reg.memsCert)
    #[LE, tabE, natsE (wl.toList.map ix), natsE (srcs.toList.map ix),
      natsE (tgts.toList.map ix), srcsE, tgtsE, hwl, htab, boolRefl, boolRefl, boolRefl,
      mkApp2 (mkConst ``Eq.refl [1]) lt srcsE, mkApp2 (mkConst ``Eq.refl [1]) lt tgtsE]
  goal.assign pf
  replaceMainGoal []

end CertificateChecks.KernelBM.Reg

end
