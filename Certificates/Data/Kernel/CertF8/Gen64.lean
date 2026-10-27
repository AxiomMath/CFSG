module

public import Certificates.Data.Kernel.CertF8.Pack64
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.GenCheck

public section

namespace CFSG.KC.CertF8.G64

open CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
  (genPool genRW genRules genTW eWord pEntry negW invWord rWord tWord)

@[expose] noncomputable def letV {β : Sort _} (y : Nat) (k : Nat → β) : β :=
  Nat.rec (motive := fun _ => β) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def letQ {β : Sort _} (p : Nat × Nat) (k : Nat × Nat → β) : β :=
  letV p.1 fun a => letV p.2 fun b => k (a, b)

@[expose] def oneK : Nat :=
  615656346818663771867652576299307181162308289002507569908651381683009914384745685243516933280574418891145545252865

@[expose] def letK : List Nat :=
  [615656346818665959118377359311231553664535406630612909744869958789355919956706835303011171656763041148300794265665,
  625275977237705392769087888823756335739619292002379146152506442468240631166367167427082800546689041051561465217025,
  615656346818709704132873019549719003709077759394919306472871730390649513082735429128651037978514049019875547940161,
  817668585618537810797794139312740325152173309304254972625128535256918121190994693785000213783825319725467674083329,
  615656346818740325643019981716660218740257405905314624174850092035489932672060864812535924932413286548464830777537,
  952343411485120503417888514655027243861659581657446210677262871555690775453699249063961297447369385937006170734593,
  615656346818801568663313906050542648802616699451824219588242998278064960461541559993224684459254314928701758771137,
  1221693063218285888658077265339603369064546249370555166232717173233231229910058882101889464491177103093038707638273,
  615656346818775321654616509907450178775891287955000061554346176365370372407071976427296638721107520477145488952513,
  1106257498189786437840853515046213694895502518400009723980789477798944296868236486351558282087312381801420770246657,
  615656346818705329631423453525870258704623524179148546801160535869958024569853123185624290391005809870280018887873,
  798429324780454568994923514263842193897622405286181564026290506409889178809423508685716437185510311694541359415297,
  615656346818663771867652576299428597968072397069440036277827851614675064812186443963595171556184253330475477630977,
  615656346818663772401649335279534701761063715544895598559327512272173106871506087204142467126647474002872879808513,
  615656346818663771867652576300399932414185261604899767231239611067996268231712513724221077761062928845114936655873,
  615656346818663776673623407121354866551107127883999827764736556985478646765589302889146737895231914896691556253697]

@[expose] def oneQ : Nat × Nat := (oneK, 0)

@[expose] def eqQ (p q : Nat × Nat) : Bool := Nat.beq p.1 q.1 && Nat.beq p.2 q.2

@[expose] def symQ (s : Nat) : Nat × Nat := if s < 16 then (letK.getD s oneK, 0) else (oneK, 1)

@[expose] noncomputable def wordQ (w : List Nat) : Nat × Nat :=
  w.foldr (fun s p => mulPr64 (symQ s) p) oneQ

@[expose] noncomputable def powQ (p : Nat × Nat) (n : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) oneQ (fun _ acc => mulPr64 p acc) n

@[expose] noncomputable def prodQ (alph : Nat → Nat × Nat) (w : List Nat) : Nat × Nat :=
  w.foldl (fun acc s => mulPr64 acc (alph s)) oneQ

@[expose] noncomputable def ePTabQ : List (Nat × Nat) :=
  [wordQ (eWord 0 0), wordQ (eWord 0 1), wordQ (eWord 0 2), wordQ (eWord 1 0), wordQ (eWord 1 1),
    wordQ (eWord 1 2), wordQ (eWord 2 0), wordQ (eWord 2 1), wordQ (eWord 2 2), wordQ (eWord 3 0),
    wordQ (eWord 3 1), wordQ (eWord 3 2)]

@[expose] noncomputable def ePQ (c i : Nat) : Nat × Nat := ePTabQ.getD (3 * c + i) oneQ

@[expose] noncomputable def eAlphQ (c s : Nat) : Nat × Nat :=
  if s % 2 = 0 then ePQ c (s / 2) else powQ (ePQ c (s / 2)) 2

@[expose] noncomputable def nTabQ : List (Nat × Nat) :=
  [wordQ (pEntry 0 0).2.2, wordQ (pEntry 0 1).2.2, wordQ (pEntry 0 2).2.2,
    wordQ (pEntry 1 0).2.2, wordQ (pEntry 1 1).2.2, wordQ (pEntry 1 2).2.2,
    wordQ (pEntry 2 0).2.2, wordQ (pEntry 2 1).2.2, wordQ (pEntry 2 2).2.2,
    wordQ (pEntry 3 0).2.2, wordQ (pEntry 3 1).2.2, wordQ (pEntry 3 2).2.2]

@[expose] noncomputable def nInvTabQ : List (Nat × Nat) :=
  [wordQ (invWord (pEntry 0 0).2.2), wordQ (invWord (pEntry 0 1).2.2),
    wordQ (invWord (pEntry 0 2).2.2), wordQ (invWord (pEntry 1 0).2.2),
    wordQ (invWord (pEntry 1 1).2.2), wordQ (invWord (pEntry 1 2).2.2),
    wordQ (invWord (pEntry 2 0).2.2), wordQ (invWord (pEntry 2 1).2.2),
    wordQ (invWord (pEntry 2 2).2.2), wordQ (invWord (pEntry 3 0).2.2),
    wordQ (invWord (pEntry 3 1).2.2), wordQ (invWord (pEntry 3 2).2.2)]

@[expose] noncomputable def nQ (c j : Nat) : Nat × Nat := nTabQ.getD (3 * c + j) oneQ

@[expose] noncomputable def nInvQ (c j : Nat) : Nat × Nat := nInvTabQ.getD (3 * c + j) oneQ

@[expose] noncomputable def pAlphQ (c s : Nat) : Nat × Nat :=
  if s % 2 = 0 then nQ c (s / 2) else nInvQ c (s / 2)

@[expose] noncomputable def rBaseQ (c : Nat) : List (Nat × Nat) :=
  [prodQ (pAlphQ c) (rWord c 0), prodQ (pAlphQ c) (negW (rWord c 0)),
    prodQ (pAlphQ c) (rWord c 1), prodQ (pAlphQ c) (negW (rWord c 1))]

@[expose] noncomputable def slpStepQ (tab : List (Nat × Nat)) (r : Nat × Nat) : List (Nat × Nat) :=
  letQ (mulPr64 (tab.getD r.1 oneQ) (tab.getD r.2 oneQ)) fun x => tab ++ [x]

@[expose] noncomputable def symTabQ (c : Nat) : List (Nat × Nat) :=
  (genRules.getD c []).foldl slpStepQ (rBaseQ c)

@[expose] noncomputable def poolChkQ (e : List Nat × List Nat × List Nat) (u v n ni : Nat × Nat) :
    Bool :=
  e.1.all (· < 6) && e.2.1.all (· < 6) && e.2.2.all (· < 16) &&
    eqQ (powQ u 3) oneQ && eqQ (powQ v 3) oneQ && eqQ (mulPr64 u v) (mulPr64 v u) &&
    (List.range 3).all (fun a => (List.range 3).all fun b =>
      (a == 0 && b == 0) || !eqQ (mulPr64 (powQ u a) (powQ v b)) oneQ) &&
    eqQ (mulPr64 u n) (mulPr64 n u) && eqQ (mulPr64 v n) (mulPr64 n v) &&
    eqQ (mulPr64 n ni) oneQ

@[expose] noncomputable def genPoolChkQ (c j : Nat) : Bool :=
  letQ (prodQ (eAlphQ c) (pEntry c j).1) fun u => letQ (prodQ (eAlphQ c) (pEntry c j).2.1) fun v =>
    letQ (nQ c j) fun n => letQ (nInvQ c j) fun ni => poolChkQ (pEntry c j) u v n ni

@[expose] noncomputable def rChkQ (c : Nat) (b : List (Nat × Nat)) : Bool :=
  (genRW.getD c []).length == 2 && (genRW.getD c []).all (fun w => w.all (· < 6)) &&
    eqQ (mulPr64 (b.getD 0 oneQ) (b.getD 1 oneQ)) oneQ &&
    eqQ (mulPr64 (b.getD 2 oneQ) (b.getD 3 oneQ)) oneQ

@[expose] noncomputable def genRChkQ (c : Nat) : Bool := rChkQ c (rBaseQ c)

@[expose] noncomputable def slpChkQ (c : Nat) (t : List (Nat × Nat)) : Bool :=
  (genTW.getD c []).length == 16 && (List.range 16).all fun k =>
    eqQ (prodQ (fun s => t.getD s oneQ) (tWord c k)) (letK.getD k oneK, 0)

@[expose] noncomputable def genSlpChkQ (c : Nat) : Bool := slpChkQ c (symTabQ c)

@[expose] noncomputable def genCheckClassQ (c : Nat) : Bool :=
  genPool.length == 4 && (genPool.getD c []).length == 3 && (List.range 3).all (genPoolChkQ c) &&
    genRChkQ c && genSlpChkQ c

end CFSG.KC.CertF8.G64

end
