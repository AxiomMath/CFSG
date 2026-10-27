module

public import Certificates.Data.Kernel.MonsterB.Rep4371Row
public import Certificates.Data.Kernel.KDense.Keys

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Rep4371Row

abbrev Terms : Type := List (Nat × Int)

@[expose] noncomputable def lIf (c : Bool) (t e : Terms) : Terms := Bool.rec (motive := fun _ => Terms) e t c

@[expose] noncomputable def strictL (y : Nat) (k : Nat → Terms) : Terms :=
  Nat.rec (motive := fun _ => Terms) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def buildL (n : Nat) (g : Nat → Nat × Int) : Terms :=
  Nat.rec (motive := fun _ => Terms) List.nil
    (fun i acc => List.cons (g (Nat.sub (Nat.sub n (nat_lit 1)) i)) acc) n

@[expose] noncomputable def kc (t x y : Nat) : Nat :=
  Nat.add t (Nat.add (Nat.mul (nat_lit 4) x) (Nat.mul (nat_lit 16384) y))

@[expose] noncomputable def kt (κ : Nat) : Nat := Nat.land κ (nat_lit 3)

@[expose] noncomputable def kx (κ : Nat) : Nat := Nat.land (Nat.shiftRight κ (nat_lit 2)) (nat_lit 4095)

@[expose] noncomputable def ky (κ : Nat) : Nat := Nat.shiftRight κ (nat_lit 14)

@[expose] noncomputable def sgI (s : Nat) (m : Int) : Int :=
  Bool.rec (motive := fun _ => Int) m (Int.neg m) (Nat.beq s (nat_lit 1))

@[expose] noncomputable def sk (s κ : Nat) : Nat := Nat.add s (Nat.mul (nat_lit 2) κ)

@[expose] noncomputable def one (c : Nat) : Terms :=
  strictL c fun c => List.cons (Nat.shiftRight c (nat_lit 1), sgI (Nat.land c (nat_lit 1)) 64) List.nil

@[expose] noncomputable def nz (e : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 1) (nat_lit 0) (Nat.beq e (nat_lit 0))

@[expose] noncomputable def wk (r e : Nat) : Nat :=
  strictN r fun r => sk (Nat.xor (Nat.land r (nat_lit 1)) e)
    (kc (nat_lit 2) (bitN r (nat_lit 1)) (Nat.shiftRight r (nat_lit 2)))

@[expose] noncomputable def thH (TH a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (thetaT a) (f12 TH a) (Nat.blt a (nat_lit 4096))

@[expose] noncomputable def eYH (TH a η c : Nat) : Nat :=
  strictN (pi0T c) fun p =>
    nIf(Nat.beq η 1, enc (kT a p) 1 p, enc (pairT a (thH TH p)) 0 (shiftT a p))

@[expose] noncomputable def par6 (x : Nat) : Nat := parT (nat_lit 6) x

@[expose] noncomputable def qgT (ν : Nat) : Nat :=
  Nat.land (Nat.shiftRight (popcT (nat_lit 6) ν) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def bgT (μ ν : Nat) : Nat :=
  Nat.xor (Nat.land (par6 μ) (par6 ν)) (par6 (Nat.land μ ν))

@[expose] noncomputable def gamT (x : Nat) : Nat := Nat.xor (Nat.land x (nat_lit 63)) (selB (par6 x) (nat_lit 63))

@[expose] noncomputable def xPauliT (qa qd a d : Nat) : Nat :=
  sk (Nat.xor (pairT a qd) (pairT qa d)) (kc (nat_lit 1) a d)

@[expose] noncomputable def xPermT (TH P BT a d : Nat) : Nat :=
  strictN (permCT P a) fun b =>
    sk (kappaT BT a) (kc (nat_lit 1) b (Nat.xor (thH TH b) (permDT P (Nat.xor (thH TH a) d))))

@[expose] noncomputable def yT (TH A WA TA PA s b d : Nat) : Nat :=
  strictN (thH TH b) fun tb =>
  strictN (Nat.xor b (selB (pairT b TA) (nat_lit 63))) fun ta =>
  strictN (dualT (Nat.land WA (wordT b))) fun td =>
  strictN (pairT (nat_lit 63) d) fun w =>
  strictN (pairT A d) fun ad =>
  strictN (Nat.xor (selB w A) (selB (Nat.xor (Nat.land w PA) ad) (nat_lit 63))) fun da =>
    sk (Nat.xor (Nat.xor (Nat.xor s (pairT A tb)) (Nat.land (Nat.xor w (nat_lit 1)) ad)) (pairT da td))
      (kc (nat_lit 1) (Nat.xor ta da) (Nat.xor td (Nat.xor (selB w TA) d)))

@[expose] noncomputable def W1 : Nat := nat_lit 1118494

@[expose] noncomputable def xXiT (TH a d : Nat) : Nat :=
  strictN (Nat.land a (nat_lit 63)) fun μ =>
  strictN (Nat.land d (nat_lit 63)) fun low =>
  strictN (Nat.xor low (selB (par6 low) (nat_lit 63))) fun ν =>
    yT TH (nat_lit 1) W1 (nat_lit 0) (nat_lit 0) (Nat.xor (qgT ν) (bgT μ ν))
      (Nat.xor ν (Nat.land a (nat_lit 4032))) (Nat.xor (gamT (Nat.xor μ ν)) (Nat.land d (nat_lit 4032)))

@[expose] noncomputable def BM0 : Nat := nat_lit 1118494

@[expose] noncomputable def c4s (r r' : Nat) : Nat :=
  nIf(Nat.beq r (nat_lit 0), nat_lit 1, nIf(Nat.beq r r', nat_lit 0, nIf(Nat.beq r' (nat_lit 0), nat_lit 0, nat_lit 1)))

@[expose] noncomputable def xiA1 (b r r' : Nat) : Nat × Int :=
  (kc (nat_lit 0) (Nat.add b r') (nat_lit 0),
    sgI (Nat.xor (Nat.xor (c4s r r') (bitN BM0 (Nat.add b r'))) (nat_lit 1)) 32)

@[expose] noncomputable def xiAT (j : Nat) : Terms :=
  strictL (Nat.mul (nat_lit 4) (Nat.shiftRight j (nat_lit 2))) fun b =>
  strictL (Nat.land j (nat_lit 3)) fun r =>
    [xiA1 b r (nat_lit 0), xiA1 b r (nat_lit 1), xiA1 b r (nat_lit 2), xiA1 b r (nat_lit 3)]

@[expose] noncomputable def GT : Nat :=
  nat_lit 39500781415248092985854619192296928843944088176505607579940977295698086850642616928238295018382855252657044534197245584854501908183496667170568132548621906667642978176515443940620455809902718611534328326024539866499523919956508259662760730682967453843080734546237151771849501353862948567469863596722967033920

@[expose] noncomputable def gT (x f : Nat) : Int :=
  Int.subNatNat (fld(GT, Nat.mul (nat_lit 8) (Nat.add (Nat.mul (nat_lit 2) x) f), nat_lit 255)) 64

@[expose] noncomputable def strictP (y : Nat) (k : Nat → Nat × Int) : Nat × Int :=
  Nat.rec (motive := fun _ => Nat × Int) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def xiTerm (TH η0 p i : Nat) : Nat × Int :=
  strictP (Nat.shiftRight i (nat_lit 6)) fun f => strictP (Nat.land i (nat_lit 63)) fun ν =>
  strictP (Nat.xor η0 f) fun e' => strictP (eYH TH (nat_lit 1) e' (shiftT ν p)) fun r =>
    (kc (nat_lit 2) (bitN r (nat_lit 1)) (Nat.shiftRight r (nat_lit 2)),
      sgI (Nat.xor (Nat.xor (Nat.xor (qgT ν) (Nat.land e' (bitN ν (nat_lit 0)))) (Nat.land r (nat_lit 1)))
        (nat_lit 1)) (gT (Nat.land p (nat_lit 63)) f))

@[expose] noncomputable def xiWT (TH η0 c : Nat) : Terms :=
  strictL (pi0T c) fun p => buildL (nat_lit 128) (xiTerm TH η0 p)

@[expose] noncomputable def actPauliT (qs qa qd κ : Nat) : Terms :=
  lIf (Nat.beq (kt κ) (nat_lit 0)) (one (sk (nat_lit 0) (kc (nat_lit 0) (kx κ) (nat_lit 0))))
    (lIf (Nat.beq (kt κ) (nat_lit 1)) (one (xPauliT qa qd (kx κ) (ky κ)))
      (one (wk (ePauliT qs qa qd (nz (kx κ)) (ky κ)) (nat_lit 0))))

@[expose] noncomputable def actPermT (TH P BT K κ : Nat) : Terms :=
  lIf (Nat.beq (kt κ) (nat_lit 0)) (one (sk (nz (pe P (nat_lit 0))) (kc (nat_lit 0) (pe P (kx κ)) (nat_lit 0))))
    (lIf (Nat.beq (kt κ) (nat_lit 1)) (one (xPermT TH P BT (kx κ) (ky κ)))
      (one (wk (ePermT P BT K (nz (kx κ)) (ky κ)) (nz (pe P (nat_lit 0))))))

@[expose] noncomputable def actSignT (TH A WA TA PA κ : Nat) : Terms :=
  lIf (Nat.beq (kt κ) (nat_lit 0))
    (one (sk (Nat.xor (bitN WA (nat_lit 0)) (bitN WA (kx κ))) (kc (nat_lit 0) (kx κ) (nat_lit 0))))
    (lIf (Nat.beq (kt κ) (nat_lit 1)) (one (yT TH A WA TA PA (nat_lit 0) (kx κ) (ky κ)))
      (one (wk (eYH TH A (nz (kx κ)) (ky κ)) (bitN WA (nat_lit 0)))))

@[expose] noncomputable def actXiT (TH κ : Nat) : Terms :=
  lIf (Nat.beq (kt κ) (nat_lit 0)) (xiAT (kx κ))
    (lIf (Nat.beq (kt κ) (nat_lit 1)) (one (xXiT TH (kx κ) (ky κ))) (xiWT TH (nz (kx κ)) (ky κ)))

@[expose] noncomputable def appT (L M : Terms) : Terms :=
  List.rec (motive := fun _ => Terms) M (fun f _ ih => List.cons f ih) L

@[expose] noncomputable def scaleT (m : Int) (L : Terms) : Terms :=
  List.rec (motive := fun _ => Terms) List.nil (fun f _ ih => List.cons (f.1, Int.mul m f.2) ih) L

@[expose] noncomputable def actVecT (f : Nat → Terms) (L : Terms) : Terms :=
  List.rec (motive := fun _ => Terms) List.nil (fun e _ ih => appT (scaleT e.2 (f e.1)) ih) L

@[expose] noncomputable def ODDT : Nat :=
  nat_lit 1138886633273799214555955061685116763124436913815497388321450844398029889282640181859581521404889752984663316419400572069178515437413825736151516638229730843288458046073027442312639224910608651271604854698666106984128196675193962022312344633285005525374042252805484515583371853379697432292939971484795398141116896191828999686095667244691119572790318314938174292373618834077946431592469413354663756103189951387406390219082268595431204833704660808994272152402771996035411861791259891344333336087666343422303324197430740430096508620787087026625112016775948259036864214753391169096641803826771669459507396957750892047059361391568922752762803059997360886506449057081402221931916012540819270948203797822955765118105228335414885493618572535170244693383706772716193863927975476171333603215107794661863889535964898302687378602044611815255645451961371470561667327441418097859998858104119016171832698994780537745574198779526221227285840943236778138802390251663530541806758703959849666798935837789392292434678391613377509832977334090478333791305319967836745652656484437347794855058767372858540053853117278096468282240598795300571501712190660544466109374203453025854614339254090656435296518693984262152858762947593234481012443616410013844107524468767049770723456992014533091054340382650536479086862461012853692575492547367047487295813822551100321571167872576746341371568437072480890555302344737057046504225208152016755674350497915908474675482216754082010564371549412514343590697660760009336776777239166077041637398541556543706704803554626827235541494074100401586243913577587465674684301171073099145981467896292147166371963741268352431806684489605804257492969548450455456383853117794263978810988774964284570089724049484931118969743434980011915490936840144572408060528197668809732286974235800713781496084883140569540732905201050825597691324454701506049603888052047115994605953194501231818367886305415629226806287026099640269283214944022003045905594694939339732885139321469206374889897005478529988560377507717646109791654634509466314834831885639500458911354807661950638479381722062370803959548086613504107193071171716105499005637242779370734657647453212750364878806036756831442519907978171529539608555483808963437828022410494057099762670009386414209619886974751822513565518675262178637413454176175602046122005351740236007727593100557125764231867348894820566187803213644816416520672997345897629925650285590144744331829626152958818727105171666391304551217970317748164862383158009317953438443663599092702674952702580425940712899053532306993543864284990699166104313953929317038048147432804923544923012877618021915119729470473031094947420000549153344887011686543302488055845243276262342353352672447494431338882491871107680296163629899318495137574087979818828296246828913092330311561730897277487716260790187739941018021843460907692451115212513122598359428048841447986511575339194354531580061778497869587535273629215353260535108386699513178942341316615544874754676808506934985065299482763358196844509395235228419736236846824448632265612268631138147978135161534765110352605732638284762685630181653969023303002365723514408560479730026053407457147499502211574906310541613899253157823228367187942128791648224135647031326495126781171826046344820265318821505371243290405184115387619714773529947904370718383541864526385798130597380759564168927505540278705561399621272316452695990784309783309964967250783146664240609310598721849622757669148916817319113372503493321776056555833748368656995141984224396638099725638679282474130431481952294293454255682167036154270880628681674228380619297144634169836818279342766147433672852858758608808355727023279282452596226533356354929768609032133679441064765572791496609096266762306225413755527168

@[expose] noncomputable def OCTT : Nat :=
  nat_lit 1145267166122749721533066128391372002546597858672975538719044880830600339532794569601022180372684126694835689094278468690684364041526951904190898776531707204350413638811873375878425488224006821404170343042796293859724147617702536366763124171731976449944440622750892325114761219

@[expose] noncomputable def LPT : Nat :=
  nat_lit 57213064661352832443910704257133847500396145646390789520484393588647854147077

@[expose] noncomputable def MT : Nat :=
  nat_lit 58390305118436492538124018094693818579358026881271157523860382734642248345729

@[expose] noncomputable def oddT (i : Nat) : Nat := f12 ODDT i

@[expose] noncomputable def octT (b : Nat) : Nat := f12 OCTT b

@[expose] noncomputable def lp1 (r : Nat) : Nat := fld(LPT, Nat.mul (nat_lit 16) r, nat_lit 255)

@[expose] noncomputable def lp2 (r : Nat) : Nat :=
  fld(LPT, Nat.add (Nat.mul (nat_lit 16) r) (nat_lit 8), nat_lit 255)

@[expose] noncomputable def oddKT (TH c i : Nat) : Nat :=
  strictN (oddCodeT c i) fun b =>
    kc (nat_lit 1) b (Nat.xor (thH TH b) (dualT (Nat.shiftLeft (nat_lit 1) i)))

@[expose] noncomputable def octKT (TH a m : Nat) : Nat :=
  strictN (octCodeT a m) fun b =>
    kc (nat_lit 1) b (Nat.xor (thH TH b) (dualT (spreadT (wordT a) m)))

@[expose] noncomputable def rawPair (k : Nat) : Terms :=
  strictL (Nat.add (Nat.shiftRight (Nat.sub k (nat_lit 23)) (nat_lit 1)) (nat_lit 2)) fun i =>
  strictL (selB (Nat.land (Nat.sub k (nat_lit 23)) (nat_lit 1)) (nat_lit 63)) fun a =>
    [(kc (nat_lit 1) a (dualT (Nat.lor (nat_lit 1) (Nat.shiftLeft (nat_lit 1) i))), 64),
      (kc (nat_lit 1) a (dualT (Nat.lor (nat_lit 2) (Nat.shiftLeft (nat_lit 1) i))), -64)]

@[expose] noncomputable def octPair (TH k : Nat) : Terms :=
  strictL (octT (Nat.shiftRight (Nat.sub k (nat_lit 1091)) (nat_lit 4))) fun a =>
  strictL (Nat.land (Nat.sub k (nat_lit 1091)) (nat_lit 15)) fun r =>
    [(octKT TH a (lp1 r), 64), (octKT TH a (lp2 r), -64)]

@[expose] noncomputable def rawT (TH k : Nat) : Terms :=
  lIf (Nat.beq k (nat_lit 0)) [(kc (nat_lit 0) (nat_lit 0) (nat_lit 0), 32), (kc (nat_lit 0) (nat_lit 1) (nat_lit 0), 32)]
  (lIf (Nat.ble k (nat_lit 22)) [(kc (nat_lit 0) (Nat.add k (nat_lit 1)) (nat_lit 0), 64)]
  (lIf (Nat.ble k (nat_lit 66)) (rawPair k)
  (lIf (Nat.ble k (nat_lit 1090))
    (strictL (oddT (Nat.sub k (nat_lit 67))) fun c =>
      [(oddKT TH c (nat_lit 0), 64), (oddKT TH c (nat_lit 1), -64)])
  (lIf (Nat.ble k (nat_lit 2322)) (octPair TH k)
    [(kc (nat_lit 2) (nIf(Nat.ble (nat_lit 3347) k, nat_lit 1, nat_lit 0))
      (oddT (Nat.mod (Nat.sub k (nat_lit 2323)) (nat_lit 1024))), 64)]))))

@[expose] noncomputable def mbit (i j : Nat) : Nat := bitN MT (Nat.add (Nat.mul (nat_lit 16) i) j)

@[expose] noncomputable def tauOct (k : Nat) : Terms :=
  strictL (Nat.add (nat_lit 1091) (Nat.mul (nat_lit 16) (Nat.shiftRight (Nat.sub k (nat_lit 1091)) (nat_lit 4))))
    fun base => strictL (Nat.land (Nat.sub k (nat_lit 1091)) (nat_lit 15)) fun r =>
      buildL (nat_lit 16) fun j => (Nat.add base j, sgI (mbit r j) 2)

@[expose] noncomputable def tauT (k : Nat) : Terms :=
  lIf (Nat.beq k (nat_lit 0)) [(nat_lit 0, 8)]
  (lIf (Nat.ble k (nat_lit 22))
    [(Nat.add (nat_lit 23) (Nat.mul (nat_lit 2) (Nat.sub k (nat_lit 1))), 8),
      (Nat.add (nat_lit 24) (Nat.mul (nat_lit 2) (Nat.sub k (nat_lit 1))), -8)]
  (lIf (Nat.ble k (nat_lit 66))
    (lIf (Nat.beq (Nat.land (Nat.sub k (nat_lit 23)) (nat_lit 1)) (nat_lit 0))
      [(Nat.add (Nat.shiftRight (Nat.sub k (nat_lit 23)) (nat_lit 1)) (nat_lit 1), 4), (k, 4),
        (Nat.add k (nat_lit 1), 4)]
      [(Nat.add (Nat.shiftRight (Nat.sub k (nat_lit 23)) (nat_lit 1)) (nat_lit 1), 4),
        (Nat.sub k (nat_lit 1), -4), (k, -4)])
  (lIf (Nat.ble k (nat_lit 1090))
    [(Nat.add (nat_lit 3347) (Nat.sub k (nat_lit 67)),
      sgI (bitN (wordT (oddT (Nat.sub k (nat_lit 67)))) (nat_lit 0)) 8)]
  (lIf (Nat.ble k (nat_lit 2322)) (tauOct k)
  (lIf (Nat.ble k (nat_lit 3346))
    [(Nat.add (nat_lit 67) (Nat.sub k (nat_lit 2323)), sgI (pT (oddT (Nat.sub k (nat_lit 2323)))) 8)]
    [(Nat.add (nat_lit 2323) (Nat.sub k (nat_lit 3347)),
      sgI (Nat.xor (bitN (wordT (oddT (Nat.sub k (nat_lit 3347)))) (nat_lit 0))
        (pT (oddT (Nat.sub k (nat_lit 3347))))) 8)])))))

end CFSG.KC.Rep4371X

end
