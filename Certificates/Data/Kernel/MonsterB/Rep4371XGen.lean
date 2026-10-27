module

public import Certificates.Data.Kernel.MonsterB.Rep4371XNf

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Rep4371Row CFSG.KC.BM.Pkt

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def f16 (T i : Nat) : Nat := fld(T, Nat.mul (nat_lit 16) i, nat_lit 65535)

@[expose] noncomputable def QA : Nat := nat_lit 11151733894906779702865009608847356688609280

@[expose] noncomputable def QD : Nat :=
  nat_lit 60715814480501360292440757922942356256922977193975988326116187745296417008400728064

@[expose] noncomputable def qsT (i : Nat) : Nat := nIf(Nat.beq i (nat_lit 0), nat_lit 1, nat_lit 0)

@[expose] noncomputable def pauliChk (TH : Nat) (CH : List (Nat × Nat)) (S : List Nat) (i : Nat) : Bool :=
  strictB (qsT i) fun s => strictB (f12 QA i) fun a => strictB (f12 QD i) fun d =>
    lineChk (actPauliT s a d) TH (lineOf CH S i)

@[expose] noncomputable def PP : Nat :=
  nat_lit 15466653098461036300594836623801231701147408391994127258817776893774709261624653037111113488326906131194887862792860948521124905612174809575333168540033929500847022363034462418613440846582302479420226867562511160096149228701020449519766912186867166555774728057998977588205313501543964888894620499437842520453123074722409822381580836699466537362955964798467317634534907803182249778327397394067952307232817724513090423078703749859510304

@[expose] noncomputable def PBT : Nat :=
  nat_lit 4989190185749077304133091501405808445413072519864175769918107535791662241796232034796506322352029001114830549952960848594617287742825441021108683444052745287923729166252099217853776746905346857523396218377596646957708555920169544033875658310499378892361241029032597393631406707037232774436671493649523903925475649130907457461241912202650554900345815245153983914921373853887454820709900165176989459609830532647100610498531636065031989373738539580302086677247381780653983701823537570475192620362393141397912071483601050094

@[expose] noncomputable def PK : Nat := nat_lit 2272

@[expose] noncomputable def pP (r : Nat) : Nat :=
  fld(PP, Nat.mul (nat_lit 120) r, nat_lit 1329227995784915872903807060280344575)

@[expose] noncomputable def pBT (r : Nat) : Nat :=
  fld(PBT, Nat.mul (nat_lit 144) r, nat_lit 22300745198530623141535718272648361505980415)

@[expose] noncomputable def pK (r : Nat) : Nat := bitN PK r

@[expose] noncomputable def permChk (TH : Nat) (CH : List (Nat × Nat)) (S : List Nat) (r : Nat) : Bool :=
  strictB (pP r) fun P => strictB (pBT r) fun BT => strictB (pK r) fun K =>
    lineChk (actPermT TH P BT K) TH (lineOf CH S (Nat.add (nat_lit 23) r))

@[expose] noncomputable def SA : Nat := nat_lit 2722591282936225513394777736534999191555

@[expose] noncomputable def SW : Nat :=
  nat_lit 19761549768059074083996904046714168883864413944211382271760570238198667467030783

@[expose] noncomputable def STT : Nat := nat_lit 79773155456670338437838769678696292412

@[expose] noncomputable def SP : Nat := nat_lit 64

@[expose] noncomputable def sW (r : Nat) : Nat := fld(SW, Nat.mul (nat_lit 24) r, nat_lit 16777215)

@[expose] noncomputable def signChk (TH : Nat) (CH : List (Nat × Nat)) (S : List Nat) (r : Nat) : Bool :=
  strictB (f12 SA r) fun A => strictB (sW r) fun WA => strictB (f12 STT r) fun TA =>
    strictB (bitN SP r) fun PA => lineChk (actSignT TH A WA TA PA) TH (lineOf CH S (Nat.add (nat_lit 35) r))

@[expose] noncomputable def XS : Nat := nat_lit 784015567509866055818352578594300897740329320448

@[expose] noncomputable def XK : Nat := nat_lit 97477957544754592453631546807097193061957173248

@[expose] noncomputable def chunkChk (f : Nat → Terms) (TH : Nat) (CH : List (Nat × Nat)) (S : List Nat)
    (c : Nat) : Bool :=
  chunkOK f TH (lineOf CH S (nat_lit 46)).1 (f16 XS c) (Nat.sub (f16 XS (Nat.succ c)) (f16 XS c))
    (f16 XK c) (f16 XK (Nat.succ c))

@[expose] noncomputable def xiChk (TH : Nat) (CH : List (Nat × Nat)) (S : List Nat) (c : Nat) : Bool :=
  chunkChk (actXiT TH) TH CH S c

@[expose] noncomputable def xiLenChk (CH : List (Nat × Nat)) (S : List Nat) : Bool :=
  Nat.beq (Nat.div (lineOf CH S (nat_lit 46)).2 (nat_lit 3)) (f16 XS (nat_lit 9))

end CFSG.KC.Rep4371X

end
