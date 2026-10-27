module

public import CFSG.LocalAnalysis.StandardType.GGFrameE78Refl

public section

set_option autoImplicit false

namespace CFSG.StandardType.FrameRoute.WRootsK

open CFSG.StandardType.FrameRoute

@[expose] def lane (T x : ℕ) : ℕ := Nat.land (Nat.shiftRight T (16 * x)) 65535

@[expose] def digits (n c : ℕ) : List ℕ :=
  (List.range n).map fun p => Nat.land (Nat.shiftRight c (2 * p)) 3

@[expose] def ofL (n : ℕ) (l : List ℕ) : FEVec n := fun p => ((l.getD p 0 : ℕ) : ZMod 3)

@[expose] def reflD (n : ℕ) (i : ℕ) (C : List (List ℕ)) (l : List ℕ) : List ℕ :=
  (List.range n).map fun p => (l.getD p 0 + 2 * (l.getD i 0 * (C.getD i []).getD p 0)) % 3

@[expose] def negD (n : ℕ) (l : List ℕ) : List ℕ :=
  (List.range n).map fun p => (2 * l.getD p 0) % 3

@[expose] def bridgeB (n L : ℕ) (R : Fin L → FEVec n) (T : ℕ) : Bool :=
  (List.finRange L).all fun x => (List.ofFn (R x)).map ZMod.val == digits n (lane T x)

@[expose] def colOK (n : ℕ) (C : List (List ℕ)) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun p =>
    decide ((if p = i then 1 else 0) - feS n i p i = (((C.getD i []).getD p 0 : ℕ) : ZMod 3))

@[expose] def chkSucc (n L : ℕ) (T : ℕ) (C : List (List ℕ)) (S : Fin n → Fin L → Fin L) : Bool :=
  (List.finRange n).all fun i => (List.finRange L).all fun k =>
    digits n (lane T (S i k).val) == reflD n i.val C (digits n (lane T k.val))

@[expose] def chkPar (n L : ℕ) (T : ℕ) (C : List (List ℕ)) (P : Fin L → Fin L) (G : Fin L → Fin n) :
    Bool :=
  (List.finRange L).all fun k =>
    digits n (lane T (P k).val) == reflD n (G k).val C (digits n (lane T k.val))

@[expose] def chkNeg (n L : ℕ) (T : ℕ) (N : Fin L → Fin L) : Bool :=
  (List.finRange L).all fun k => digits n (lane T (N k).val) == negD n (digits n (lane T k.val))

@[expose] def chkCol (n L : ℕ) (T : ℕ) (C : List (List ℕ)) (Cl : Fin n → Fin L) : Bool :=
  (List.finRange n).all fun i => digits n (lane T (Cl i).val) == C.getD i []

theorem getD_map_range {n p : ℕ} (f : ℕ → ℕ) (hp : p < n) :
    ((List.range n).map f).getD p 0 = f p := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hp]

theorem sub_eq_add_two_mul (x y : ZMod 3) : x - y = x + 2 * y := by
  revert x y
  decide

theorem two_mul_eq_neg (x : ZMod 3) : 2 * x = -x := by
  revert x
  decide

theorem eq_of_bridgeB {n L : ℕ} {R : Fin L → FEVec n} {T : ℕ} (h : bridgeB n L R T = true)
    (x : Fin L) : R x = ofL n (digits n (lane T x.val)) := by
  simp only [bridgeB, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at h
  funext p
  rw [ofL, ← h x]
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_ofFn]

theorem feCol_eq_ofL {n : ℕ} {C : List (List ℕ)} (h : colOK n C = true) (i : Fin n) :
    feCol n i = ofL n (C.getD i []) := by
  simp only [colOK, List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies] at h
  funext p
  have hrow : feRow n i i = 1 := by
    have h1 := feRow_dot n i (Pi.single i 1)
    simpa using h1
  have he : feCol n i p = (if p = i then 1 else 0) - feS n i p i := by
    rw [feS_eq]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
    rw [hrow]
    ring
  rw [he, h i p]
  rfl

theorem mulVec_ofL {n : ℕ} {C : List (List ℕ)} (hC : colOK n C = true) (i : Fin n)
    (l : List ℕ) : (feS n i).mulVec (ofL n l) = ofL n (reflD n i.val C l) := by
  rw [feS_mulVec, feCol_eq_ofL hC i]
  funext p
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ofL, reflD, getD_map_range _ p.isLt,
    ZMod.natCast_mod]
  push_cast
  exact sub_eq_add_two_mul _ _

theorem succ_of {n L : ℕ} {R : Fin L → FEVec n} {T : ℕ} {C : List (List ℕ)}
    {S : Fin n → Fin L → Fin L} (hB : bridgeB n L R T = true) (hC : colOK n C = true)
    (h : chkSucc n L T C S = true) (i : Fin n) (k : Fin L) :
    R (S i k) = (feS n i).mulVec (R k) := by
  simp only [chkSucc, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at h
  rw [eq_of_bridgeB hB, eq_of_bridgeB hB, mulVec_ofL hC, h i k]

theorem par_of {n L : ℕ} {R : Fin L → FEVec n} {T : ℕ} {C : List (List ℕ)}
    {P : Fin L → Fin L} {G : Fin L → Fin n} (hB : bridgeB n L R T = true)
    (hC : colOK n C = true) (h : chkPar n L T C P G = true) (k : Fin L) :
    R (P k) = (feS n (G k)).mulVec (R k) := by
  simp only [chkPar, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at h
  rw [eq_of_bridgeB hB, eq_of_bridgeB hB, mulVec_ofL hC, h k]

theorem neg_of {n L : ℕ} {R : Fin L → FEVec n} {T : ℕ} {N : Fin L → Fin L}
    (hB : bridgeB n L R T = true) (h : chkNeg n L T N = true) (k : Fin L) :
    R (N k) = -R k := by
  simp only [chkNeg, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at h
  rw [eq_of_bridgeB hB, eq_of_bridgeB hB, h k]
  funext p
  simp only [Pi.neg_apply, ofL, negD, getD_map_range _ p.isLt, ZMod.natCast_mod]
  push_cast
  exact two_mul_eq_neg _

theorem col_of {n L : ℕ} {R : Fin L → FEVec n} {T : ℕ} {C : List (List ℕ)} {Cl : Fin n → Fin L}
    (hB : bridgeB n L R T = true) (hC : colOK n C = true) (h : chkCol n L T C Cl = true)
    (i : Fin n) : R (Cl i) = feCol n i := by
  simp only [chkCol, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at h
  rw [eq_of_bridgeB hB, h i, feCol_eq_ofL hC i]

@[expose] def T7 : ℕ :=
  229627891845423814009949685212121215583516690780726711771239472416970768378308734674632750834948699198997540252460438772995361842268355169099751561867961987304762402899374566818449409976930710040873945500069029965899825667115827310207332188741738588767094479971415064777839305193233216803456066081268170166242778501402143875698931618601326746101291163796504595813968596529967516500112934180752305000745096367825322790570714012915822653258329485763019637129716169436104072492300872699793889436269195202102326899365145894735932298458669639669767225630065458930302023522652021600493699833123317411981885474

@[expose] def T8 : ℕ :=
  4509793615995032303786099205094843701906354322912648890816108724570140518013373641629906938513616484916237874574027682901182288217659390179169594052069715152981588275198710216949193238855053494715614577682070390808518676221042090077350348456086641104776704535459668929448620374412808024475662844896976444773514444059654348739824802002874850871443607508361750752845658003447381138682278646101859360739633476282735784062860112532731882936193910246885708405519473748580403951399770271098814997622132941127178988920161109452433719335907116298585578784540134576094867313833057580889268561487352490300550270424124157894554038053751010654165030141635991407571970004352838416349044970236039958127931573172230743993754665496424945644148066764878755985377552154839379962634924801185710826861301863376670469278070833655345633705632993590130333604188391489051449392108108209335286607697131330987596492719972680847241950833673477552926589280863103585602894070180378152174334408664294952299634439791410172826740253952330278764094084941568203772334218970630145142315859271388855550340071684134653146288766466983778817353420653069375514799035919877284465500362628404412450

@[expose] def C7 : List (List ℕ) :=
  [[2, 0, 2, 0, 0, 0, 0], [0, 2, 0, 2, 0, 0, 0], [2, 0, 2, 2, 0, 0, 0], [0, 2, 2, 2, 2, 0, 0],
    [0, 0, 0, 2, 2, 2, 0], [0, 0, 0, 0, 2, 2, 2], [0, 0, 0, 0, 0, 2, 2]]

@[expose] def C8 : List (List ℕ) :=
  [[2, 0, 2, 0, 0, 0, 0, 0], [0, 2, 0, 2, 0, 0, 0, 0], [2, 0, 2, 2, 0, 0, 0, 0],
    [0, 2, 2, 2, 2, 0, 0, 0], [0, 0, 0, 2, 2, 2, 0, 0], [0, 0, 0, 0, 2, 2, 2, 0],
    [0, 0, 0, 0, 0, 2, 2, 2], [0, 0, 0, 0, 0, 0, 2, 2]]

theorem colOK_seven : colOK 7 C7 = true := by decide +kernel

theorem colOK_eight : colOK 8 C8 = true := by decide +kernel

end CFSG.StandardType.FrameRoute.WRootsK

end
