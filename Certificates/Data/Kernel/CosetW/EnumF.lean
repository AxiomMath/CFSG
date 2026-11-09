module

public import Certificates.Data.Kernel.CosetW.EnumW

public noncomputable section
namespace CFSG.CosetTable

@[expose] def seqF {α : Sort _} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) y

theorem seqF_eq {α : Sort _} (y : Nat) (k : Nat → α) : seqF y k = k y := by
  cases y <;> rfl

@[expose] def StW.force (st : StW) : StW :=
  seqF st.tab.n fun tn => seqF st.tab.t fun tt => seqF st.fwd.n fun fn => seqF st.fwd.t fun ft =>
  seqF st.par.n fun pn => seqF st.par.t fun pt => seqF st.next fun nx => seqF st.qi fun qi =>
  match st.ded, st.queue with
  | ⟨d⟩, ⟨q⟩ => cond st.overflow ⟨⟨tn, tt⟩, ⟨fn, ft⟩, ⟨pn, pt⟩, nx, ⟨d⟩, ⟨q⟩, qi, true⟩
      ⟨⟨tn, tt⟩, ⟨fn, ft⟩, ⟨pn, pt⟩, nx, ⟨d⟩, ⟨q⟩, qi, false⟩

theorem StW.force_eq (st : StW) : st.force = st := by
  obtain ⟨⟨tn, tt⟩, ⟨fn, ft⟩, ⟨pn, pt⟩, nx, ⟨d⟩, ⟨q⟩, qi, ov⟩ := st
  cases ov <;> simp only [StW.force, seqF_eq, Bool.cond_true, Bool.cond_false]

@[expose] def getF (b : WStore) (i : Nat) : Nat :=
  cond (Nat.blt i b.n) (Nat.mod (Nat.shiftRight b.t (Nat.add 64 (Nat.mul 32 i))) 4294967296) 0

theorem getF_eq (b : WStore) (i : Nat) : getF b i = b.get i := by
  unfold getF WStore.get
  by_cases h : i < b.n
  · rw [show Nat.blt i b.n = true from Nat.blt_eq.mpr h, Bool.cond_true,
      ite_cond_eq_true _ _ (eq_true h)]
    rfl
  · have h2 : Nat.blt i b.n = false := by
      cases e : Nat.blt i b.n
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h
    rw [h2, Bool.cond_false, ite_cond_eq_false _ _ (eq_false h)]

@[expose] def getLF (b : WStore) (c : Nat) : Nat := Nat.xor (getF b c) c

theorem getLF_eq (b : WStore) (c : Nat) : getLF b c = b.getL c := by
  unfold getLF WStore.getL
  rw [getF_eq]
  rfl

@[expose] def walkF (L : Nat) (tab : WStore) : Nat → Nat → Nat → List Nat → Nat × Nat
  | _, k, c, [] => (k, c)
  | 0, k, c, _ :: _ => (k, c)
  | lim + 1, k, c, x :: w =>
    let d := getF tab (Nat.add (Nat.mul c L) x)
    cond (Nat.beq d 0) (k, c) (walkF L tab lim (Nat.succ k) d w)

theorem walkF_eq (L : Nat) (tab : WStore) :
    ∀ lim k c w, walkF L tab lim k c w = walkWS L tab lim k c w := by
  intro lim k c w
  induction w generalizing lim k c with
  | nil => cases lim <;> rfl
  | cons x w ih =>
    cases lim with
    | zero => rfl
    | succ lim =>
      simp only [walkF, walkWS, getF_eq, ih]
      cases h : Nat.beq (tab.get (c * L + x)) 0
      · have h' : (tab.get (c * L + x) == 0) = false := h
        simp only [Bool.cond_false, h', Bool.false_eq_true, ↓reduceIte]
        rfl
      · have h' : (tab.get (c * L + x) == 0) = true := h
        simp only [Bool.cond_true, h', ↓reduceIte]

@[expose] def findF (fwd : WStore) : Nat → Nat → Nat
  | 0, c => c
  | fuel + 1, c =>
    let d := getLF fwd c
    cond (Nat.beq d c) c (findF fwd fuel d)

theorem findF_eq (fwd : WStore) : ∀ fuel c, findF fwd fuel c = findWS fwd fuel c
  | 0, _ => rfl
  | fuel + 1, c => by
    simp only [findF, findWS, getLF_eq, findF_eq fwd fuel]
    cases h : Nat.beq (fwd.getL c) c
    · have h' : (fwd.getL c == c) = false := h
      simp only [Bool.cond_false, h', Bool.false_eq_true, ↓reduceIte]
    · have h' : (fwd.getL c == c) = true := h
      simp only [Bool.cond_true, h', ↓reduceIte]

@[expose] def mergeF (st : StW) (a b : Nat) : StW :=
  let ra := findF st.fwd st.next a
  let rb := findF st.fwd st.next b
  if ra == rb || st.next ≤ ra || st.next ≤ rb then st
  else if ra < rb then
    { st with fwd := st.fwd.setL rb ra, queue := st.queue.push rb }
  else
    { st with fwd := st.fwd.setL ra rb, queue := st.queue.push ra }

theorem mergeF_eq (st : StW) (a b : Nat) : mergeF st a b = mergeW st a b := by
  simp only [mergeF, mergeW, findF_eq]

@[expose] def coincLetterF (P : Params) (st : StW) (g x : Nat) : StW :=
  let d := getF st.tab (g * P.L + x)
  if d == 0 then st else
  let ix := P.inv.getD x 0
  let st := if getF st.tab (d * P.L + ix) == g then
      { st with tab := st.tab.set (d * P.L + ix) 0 } else st
  let mu := findF st.fwd st.next g
  let nu := findF st.fwd st.next d
  let e := getF st.tab (mu * P.L + x)
  if e != 0 then mergeF st nu e
  else
    let e' := getF st.tab (nu * P.L + ix)
    if e' != 0 then mergeF st mu e'
    else { st with tab := (st.tab.set (mu * P.L + x) nu).set (nu * P.L + ix) mu,
                   ded := st.ded.push (mu * P.L + x) }

theorem coincLetterF_eq (P : Params) (st : StW) (g x : Nat) :
    coincLetterF P st g x = coincLetterW P st g x := by
  simp only [coincLetterF, coincLetterW, getF_eq, findF_eq, mergeF_eq]

@[expose] def coincRowF (P : Params) (g : Nat) : Nat → StW → StW
  | 0, st => st
  | n + 1, st => coincRowF P g n (coincLetterF P st g (P.L - (n + 1))).force

theorem coincRowF_eq (P : Params) (g : Nat) : ∀ n st, coincRowF P g n st = coincRowW P g n st
  | 0, _ => rfl
  | n + 1, st => by
    simp only [coincRowF, coincRowW, StW.force_eq, coincLetterF_eq, coincRowF_eq P g n]

@[expose] def coincQueueF (P : Params) : Nat → StW → StW
  | 0, st => st
  | fuel + 1, st =>
    if st.qi < st.queue.size then
      let g := st.queue.getD st.qi 0
      coincQueueF P fuel (coincRowF P g P.L { st with qi := st.qi + 1 })
    else { st with queue := #[], qi := 0 }

theorem coincQueueF_eq (P : Params) : ∀ fuel st, coincQueueF P fuel st = coincQueueW P fuel st
  | 0, _ => rfl
  | fuel + 1, st => by
    simp only [coincQueueF, coincQueueW, coincRowF_eq, coincQueueF_eq P fuel]

@[expose] def coincidenceF (P : Params) (st : StW) (a b : Nat) : StW :=
  coincQueueF P (st.next * (P.L + 1) + 1) (mergeF st a b).force

theorem coincidenceF_eq (P : Params) (st : StW) (a b : Nat) :
    coincidenceF P st a b = coincidenceW P st a b := by
  simp only [coincidenceF, coincidenceW, StW.force_eq, mergeF_eq, coincQueueF_eq]

@[expose] def scanWordF (L : Nat) (tab : WStore) (a : Nat) (w w' : List Nat) : Scan :=
  let r := w.length
  let (i, f) := walkF L tab r 0 a w
  if i == r then (if f == a then .closed else .coinc f a)
  else
    let (j, b) := walkF L tab (r - i) 0 a w'
    if j == r - i then (if f == b then .closed else .coinc f b)
    else if j + 1 == r - i then .deduct f (w.getD i 0) b
    else .gap f (w.getD i 0)

theorem scanWordF_eq (L : Nat) (tab : WStore) (a : Nat) (w w' : List Nat) :
    scanWordF L tab a w w' = scanWordW L tab a w w' := by
  simp only [scanWordF, scanWordW, walkF_eq]

@[expose] def scanF (P : Params) (st : StW) (a : Nat) (w w' : List Nat) : StW :=
  match scanWordF P.L st.tab a w w' with
  | .closed => st
  | .coinc f b => coincidenceF P st f b
  | .deduct f x b => deduceW P st f x b
  | .gap _ _ => st

theorem scanF_eq (P : Params) (st : StW) (a : Nat) (w w' : List Nat) :
    scanF P st a w w' = scanW P st a w w' := by
  simp only [scanF, scanW, scanWordF_eq, coincidenceF_eq]
  generalize scanWordW P.L st.tab a w w' = s
  cases s <;> rfl

@[expose] def scanAllF (P : Params) (a : Nat) : List (List Nat × List Nat) → StW → StW
  | [], st => st
  | p :: ps, st =>
    cond (Nat.beq (getLF st.fwd a) a) (scanAllF P a ps (scanF P st a p.1 p.2)) st

theorem scanAllF_eq (P : Params) (a : Nat) :
    ∀ ps st, scanAllF P a ps st = scanAllW P a ps st
  | [], _ => rfl
  | p :: ps, st => by
    simp only [scanAllF, scanAllW, getLF_eq, scanF_eq, scanAllF_eq P a ps]
    cases h : Nat.beq (st.fwd.getL a) a
    · have h' : (st.fwd.getL a == a) = false := h
      simp only [Bool.cond_false, h', Bool.false_eq_true, ↓reduceIte]
    · have h' : (st.fwd.getL a == a) = true := h
      simp only [Bool.cond_true, h', ↓reduceIte]

@[expose] def processDedF (P : Params) : Nat → StW → StW
  | 0, st => st
  | fuel + 1, st =>
    match st.ded.back? with
    | none => st
    | some e =>
      let st := { st with ded := st.ded.pop }
      let a := e / P.L
      cond (Nat.beq (getLF st.fwd a) a)
        (processDedF P fuel (scanAllF P a (P.scans.getD (e % P.L) []) st).force)
        (processDedF P fuel st)

theorem processDedF_eq (P : Params) : ∀ fuel st, processDedF P fuel st = processDedW P fuel st
  | 0, _ => rfl
  | fuel + 1, st => by
    simp only [processDedF, processDedW, StW.force_eq, processDedF_eq P fuel, getLF_eq,
      scanAllF_eq]
    generalize st.ded.back? = o
    cases o with
    | none => rfl
    | some e =>
      simp only
      cases h : Nat.beq (st.fwd.getL (e / P.L)) (e / P.L)
      · have h' : (st.fwd.getL (e / P.L) == e / P.L) = false := h
        simp only [Bool.cond_false, h', Bool.false_eq_true, ↓reduceIte]
      · have h' : (st.fwd.getL (e / P.L) == e / P.L) = true := h
        simp only [Bool.cond_true, h', ↓reduceIte]

@[expose] def fillWordF (P : Params) (w w' : List Nat) : Nat → StW → StW
  | 0, st => st
  | fuel + 1, st =>
    match scanWordF P.L st.tab 1 w w' with
    | .closed => st
    | .coinc f b => coincidenceF P st f b
    | .deduct f x b => deduceW P st f x b
    | .gap f x =>
      let st := (defineW P st f x).force
      if st.overflow then st else fillWordF P w w' fuel st

theorem fillWordF_eq (P : Params) (w w' : List Nat) :
    ∀ fuel st, fillWordF P w w' fuel st = fillWordW P w w' fuel st
  | 0, _ => rfl
  | fuel + 1, st => by
    simp only [fillWordF, fillWordW, StW.force_eq, fillWordF_eq P w w' fuel, scanWordF_eq,
      coincidenceF_eq]
    generalize scanWordW P.L st.tab 1 w w' = s
    cases s <;> rfl

@[expose] def fillSubsF (P : Params) (fuel : Nat) : List (List Nat × List Nat) → StW → StW
  | [], st => st
  | p :: ps, st =>
    fillSubsF P fuel ps (processDedF P fuel (fillWordF P p.1 p.2 (p.1.length + 1) st)).force

theorem fillSubsF_eq (P : Params) (fuel : Nat) :
    ∀ ps st, fillSubsF P fuel ps st = fillSubsW P fuel ps st
  | [], _ => rfl
  | p :: ps, st => by
    simp only [fillSubsF, fillSubsW, StW.force_eq, processDedF_eq, fillWordF_eq,
      fillSubsF_eq P fuel ps]

@[expose] def fillRowF (P : Params) (fuel c : Nat) : Nat → StW → StW
  | 0, st => st
  | n + 1, st =>
    if st.overflow || getLF st.fwd c != c then st
    else
      let x := P.L - (n + 1)
      if getF st.tab (c * P.L + x) == 0 then
        fillRowF P fuel c n (processDedF P fuel (defineW P st c x)).force
      else fillRowF P fuel c n st

theorem fillRowF_eq (P : Params) (fuel c : Nat) :
    ∀ n st, fillRowF P fuel c n st = fillRowW P fuel c n st
  | 0, _ => rfl
  | n + 1, st => by
    simp only [fillRowF, fillRowW, StW.force_eq, processDedF_eq, fillRowF_eq P fuel c n, getF_eq,
      getLF_eq]

@[expose] def felschF (P : Params) (fuel : Nat) : Nat → Nat → StW → StW
  | 0, _, st => st
  | n + 1, c, st =>
    if c < st.next && !st.overflow then felschF P fuel n (c + 1) (fillRowF P fuel c P.L st).force
    else st

theorem felschF_eq (P : Params) (fuel : Nat) :
    ∀ n c st, felschF P fuel n c st = felschW P fuel n c st
  | 0, _, _ => rfl
  | n + 1, c, st => by
    simp only [felschF, felschW, StW.force_eq, fillRowF_eq, felschF_eq P fuel n]

@[expose] def enumerateF (P : Params) (cap : Nat) : StW :=
  let fuel := 64 * (cap + 1) * (P.L + 1)
  felschF P fuel (cap + 1) 1 (fillSubsF P fuel P.subs (StW.init P.L cap)).force

theorem enumerateF_eq (P : Params) (cap : Nat) : enumerateF P cap = enumerateW P cap := by
  simp only [enumerateF, enumerateW, StW.force_eq, felschF_eq, fillSubsF_eq]

@[expose] def checkF (P : Params) (cap n : Nat) : Bool :=
  let st := (enumerateF P cap).force
  !st.overflow && st.completeW P.L && st.liveCountW == n

theorem checkF_eq (P : Params) (cap n : Nat) : checkF P cap n = checkW P cap n := by
  simp only [checkF, checkW, StW.force_eq, enumerateF_eq]

end CFSG.CosetTable
