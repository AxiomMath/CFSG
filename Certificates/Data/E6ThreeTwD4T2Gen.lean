module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
public meta import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
public meta import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
public meta import CFSG.LieType.Chevalley.KernelComponentRoots
public meta import CFSG.Blueprint.ChevalleyRootsInputs
public meta import CFSG.Blueprint.Chevalley

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option maxRecDepth 100000

@[expose] def twD4T2F0 : List ℕ := [1, 1, 1, 0, 0, 0]

@[expose] def twD4T2Sig (_ : Unit := ()) : List ℕ :=
  (List.range e6Certificate.roots.length).filter fun k =>
    decide (triPairing (vec3 (τ := .E6) twD4T2F0) (e6Certificate.root k) = 0)

@[expose] def twD4T2Vecs (_ : Unit := ()) : List (List ℤ) :=
  (List.range e6Certificate.roots.length).map fun m => List.ofFn (e6Certificate.root m)

@[expose] def twD4T2Row (vs : List (List ℤ)) (b : ℕ) : List ℕ :=
  (List.range e6Certificate.roots.length).map fun k =>
    let tv := List.ofFn (e6Certificate.root k -
      corootPair (e6Certificate.root b) (e6Certificate.root k) • e6Certificate.root b)
    (vs.findIdx? fun x => x == tv).getD 0

@[expose] def twD4T2RowOK (b : ℕ) (row : List ℕ) : Bool :=
  (List.range e6Certificate.roots.length).all fun k =>
    decide (row.getD k 0 < e6Certificate.roots.length) &&
      (List.ofFn (e6Certificate.root (row.getD k 0)) == List.ofFn (e6Certificate.root k -
        corootPair (e6Certificate.root b) (e6Certificate.root k) • e6Certificate.root b))

@[expose] def twD4T2Img (row : List ℕ) (t : List ℕ) : List ℕ := t.map fun x => row.getD x 0

@[expose] def twD4T2Closed (keys : List ℕ) (brs : List (ℕ × List ℕ)) (tree : KTree) : Bool :=
  tree.mem (encodeT (List.range Tag.E6.rank)) &&
    decide (decodeT Tag.E6.rank (encodeT (List.range Tag.E6.rank)) = List.range Tag.E6.rank) &&
    keys.all fun k => brs.all fun p =>
      let img := twD4T2Img p.2 (decodeT Tag.E6.rank k)
      decide (decodeT Tag.E6.rank (encodeT img) = img) && tree.mem (encodeT img)

@[expose] def twD4T2Lam (n : ℕ) : Fin Tag.E6.rank → ℤ := fun j => ((n / 3 ^ (j : ℕ) % 3 : ℕ) : ℤ)

@[expose] def twD4T2Moves (t : List ℕ) (n r : ℕ) : Bool :=
  decide (r < e6Certificate.roots.length) && (List.finRange Tag.E6.rank).all fun j =>
    decide ((e6Certificate.tupleVec t (twD4T2Lam n) j - twD4T2Lam n j -
      e6Certificate.root r j) % 3 = 0)

@[expose] def twD4T2WordTuple (word : List ℕ) : List ℕ :=
  (toFinWord3 (τ := .E6) word).foldr (fun i t => e6Certificate.tupleImage i t)
    (List.range Tag.E6.rank)

@[expose] def twD4T2Fixes (b : Fin Tag.E6.rank → ZMod 3) (t : List ℕ) : Bool :=
  (List.finRange Tag.E6.rank).all fun j =>
    decide (triPairing b (e6Certificate.root (t.getD j 0)) = b j)

@[expose] def twIdx3 (v : Fin Tag.E6.rank → ZMod 3) : ℕ :=
  ∑ j : Fin Tag.E6.rank, (v j).val * 3 ^ (j : ℕ)

@[expose] def twD4T2ZTab (sig : List ℕ) : Array (List ℕ) :=
  ((List.range (3 ^ Tag.E6.rank)).map fun k => (List.range sig.length).filter fun i =>
    decide (triPairing (vec3OfIndex (τ := .E6) k) (e6Certificate.root (sig.getD i 0)) = 0)).toArray

@[expose] def twD4T2GTab (ts : List (List ℕ)) : Array Bool :=
  ((List.range (3 ^ Tag.E6.rank)).map fun k =>
    ts.any (twD4T2Fixes (vec3OfIndex (τ := .E6) k))).toArray

@[expose] def twD4T2Coeffs : List (ZMod 3 × ZMod 3) := [(1, 0), (0, 1), (1, 1), (1, 2)]

@[expose] def twD4T2PairsOK (zt : Array (List ℕ)) (gt : Array Bool) : Bool :=
  let ks := List.range (3 ^ Tag.E6.rank)
  ks.all fun k₁ =>
    let z₁ := zt.getD k₁ []
    ks.all fun k₂ =>
      let z₂ := zt.getD k₂ []
      z₁.any (fun i => z₂.contains i) || twD4T2Coeffs.any fun ab =>
        gt.getD (twIdx3 (ab.1 • vec3OfIndex (τ := .E6) k₁ + ab.2 • vec3OfIndex (τ := .E6) k₂))
          false

@[expose] def twD4T2RepsOK (_ : Unit := ()) : Bool :=
  (List.range e6ThreeReps.length).all fun ρ => ρ == 6 ||
    decide (((List.range e6Certificate.roots.length).filter fun k =>
      decide (triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ []))
        (e6Certificate.root k) = 0)).length ≠ 24)

@[expose] def twD4T2Elems : List (ℕ × ℕ × ℕ) :=
  [(3315802255175, 3, 54), (3363231835719, 3, 46), (3401884836096, 3, 25), (3453239104768, 3, 13),
    (3466124013375, 1, 65), (3509259019839, 1, 65), (3526440591646, 1, 37),
    (3556320417054, 1, 37), (4411537694976, 3, 25), (4420129788231, 30, 60),
    (4501548773191, 3, 54), (4510135222528, 27, 15), (4518725168947, 1, 54),
    (4596223451442, 1, 53), (4639170957619, 1, 54), (4677642420530, 1, 53), (5514788471040, 0, 0),
    (5553594763520, 3, 3), (5609433076039, 27, 3), (5652231625543, 3, 37), (5665112333086, 1, 37),
    (5703918620958, 1, 37), (5729692158271, 1, 65), (5755310833983, 1, 65),
    (13250061610823, 3, 54), (13254539813120, 3, 25), (13301786158663, 3, 46),
    (13305894081792, 3, 13), (13391980470558, 1, 37), (13400383369023, 1, 65),
    (13426155263262, 1, 37), (13434928440895, 1, 65), (14315566537543, 3, 37),
    (14345629278464, 3, 25), (14354035978055, 3, 54), (14414162636601, 1, 60),
    (14448522365184, 3, 3), (14504543066937, 1, 60), (14521724969257, 1, 46),
    (14573079300393, 1, 46), (15445125443399, 3, 54), (15449603645696, 3, 25),
    (15458195738951, 30, 60), (15462301827328, 27, 15), (15552685023538, 1, 53),
    (15561086086963, 1, 54), (15651283861810, 1, 53), (15660057039155, 1, 54),
    (16505963484416, 3, 13), (16553022193920, 27, 4), (16561801007431, 30, 53),
    (16613151745577, 1, 46), (16647515350599, 3, 46), (16699237011753, 1, 46),
    (16725009765689, 1, 60), (16772069392697, 1, 60), (17652521374023, 27, 3),
    (17656661016832, 81, 5), (17695319923527, 3, 37), (17699762276608, 3, 3),
    (17789960325439, 1, 65), (17802689911582, 1, 37), (17819873968447, 1, 65),
    (17832906264862, 1, 37), (26401419243335, 3, 54), (26405897445632, 3, 25),
    (26457250924800, 3, 3), (26496093788999, 3, 37), (26547633398057, 1, 46),
    (26594689888057, 1, 60), (26620462565673, 1, 46), (26655005547321, 1, 60),
    (27539566695680, 3, 13), (27556749384519, 3, 37), (27590937741568, 3, 3),
    (27599530960455, 3, 46), (27608117618226, 1, 53), (27655530814258, 1, 53),
    (27745727943987, 1, 54), (27767034677555, 1, 54), (28604889305415, 30, 53),
    (28608995393792, 27, 4), (28639064041031, 3, 46), (28695080670464, 3, 13),
    (28746623227193, 1, 60), (28797973964329, 1, 46), (28815157690681, 1, 60),
    (28853994459433, 1, 46), (30804600430898, 1, 53), (30843255005481, 1, 46),
    (30851845068089, 1, 60), (30894794609971, 1, 54), (30984934403891, 1, 54),
    (31014999764793, 1, 60), (31019294139945, 1, 46), (31045064533554, 1, 53),
    (39595374618183, 3, 46), (39603961268480, 3, 3), (39638492388167, 3, 37),
    (39647079503104, 3, 13), (39741571601715, 1, 54), (39780058204467, 1, 54),
    (39823004608050, 1, 53), (39848942967602, 1, 53), (40743100100403, 1, 54),
    (40786050363193, 1, 60), (40794639705641, 1, 46), (40837589968434, 1, 53),
    (40850528936242, 1, 53), (40889183510825, 1, 46), (40893478606137, 1, 60),
    (40923543246131, 1, 54), (42894849024286, 1, 37), (42903439411519, 1, 65),
    (42942094123314, 1, 53), (42989338298675, 1, 54), (43040806940467, 1, 54),
    (43109527793471, 1, 65), (43113821379358, 1, 37), (43161067395890, 1, 53),
    (50595654414131, 1, 54), (50630015528767, 1, 65), (50647194016542, 1, 37),
    (50698805059890, 1, 53), (50733094738738, 1, 53), (50784703947038, 1, 37),
    (50788999366975, 1, 65), (50844833483059, 1, 54), (52798943265087, 1, 65),
    (52829007716638, 1, 37), (52841892610361, 1, 60), (52880547651881, 1, 46),
    (52936294739769, 1, 60), (52974950231871, 1, 65), (53035078979870, 1, 37),
    (53056554602793, 1, 46), (53889847465246, 1, 37), (53932797135145, 1, 46),
    (53945682889023, 1, 65), (53988632565049, 1, 60), (54035788998185, 1, 46),
    (54074443701022, 1, 37), (54134575408703, 1, 65), (54156050242361, 1, 60),
    (58287824777023, 1, 65), (58330773663545, 1, 60), (58343658557726, 1, 37),
    (58386609017129, 1, 46), (58395285659945, 1, 46), (58442529972510, 1, 37),
    (58515544736063, 1, 65), (58541314212153, 1, 60), (59395908180766, 1, 37),
    (59425975117375, 1, 65), (59438857856553, 1, 46), (59477514722105, 1, 60),
    (59494780638521, 1, 60), (59542025275711, 1, 65), (59615038870814, 1, 37),
    (59640808671529, 1, 46), (61590606381362, 1, 53), (61624966124830, 1, 37),
    (61642146709823, 1, 65), (61728046060851, 1, 54), (61732219987506, 1, 53),
    (61800939458846, 1, 37), (61805236004415, 1, 65), (61852480639283, 1, 54),
    (65984239183423, 1, 65), (65992827539742, 1, 37), (66031483818291, 1, 54),
    (66078726891058, 1, 53), (66091732833587, 1, 54), (66177632174399, 1, 65),
    (66181926425886, 1, 37), (66237760995634, 1, 53), (68230474826034, 1, 53),
    (68273424501033, 1, 46), (68282014826809, 1, 60), (68324964501811, 1, 54),
    (68367760694066, 1, 53), (68397825462569, 1, 46), (68402121218873, 1, 60),
    (68427891020083, 1, 54), (71485907734835, 1, 54), (71524562443065, 1, 60),
    (71533151588649, 1, 46), (71576101264178, 1, 53), (71636384287027, 1, 54),
    (71675038990649, 1, 60), (71679333566761, 1, 46), (71709398335794, 1, 53)]

@[expose] def twD4T2Words : List (List ℕ) :=
  [[2, 3, 4, 5, 0, 2, 1, 3, 4, 2, 1, 3, 2, 1],
    [4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 0, 2, 1, 3, 2, 1],
    [3, 2, 1, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 0, 2, 3, 0, 2],
    [1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 1, 3, 0, 2, 0],
    [5, 4, 3, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2, 0],
    [3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 4, 3, 2, 1, 3, 0, 2, 0],
    [4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 2, 0]]

@[expose] def twD4T2Check (_ : Unit := ()) : Bool :=
  let sig := twD4T2Sig ()
  let vs := twD4T2Vecs ()
  let brs := sig.map fun b => (b, twD4T2Row vs b)
  let keys := twD4T2Elems.map Prod.fst
  let ts := twD4T2Words.map twD4T2WordTuple
  twD4T2RepsOK () &&
    brs.all (fun p => twD4T2RowOK p.1 p.2) &&
    twD4T2Closed keys brs (KTree.ofSorted keys) &&
    twD4T2Elems.all (fun e => decodeT Tag.E6.rank e.1 == List.range Tag.E6.rank ||
      twD4T2Moves (decodeT Tag.E6.rank e.1) e.2.1 e.2.2) &&
    ts.all (fun t => twD4T2Fixes (vec3 (τ := .E6) twD4T2F0) t &&
      e6ScTest e6Certificate twD4T2F0 t) &&
    twD4T2PairsOK (twD4T2ZTab sig) (twD4T2GTab ts)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
