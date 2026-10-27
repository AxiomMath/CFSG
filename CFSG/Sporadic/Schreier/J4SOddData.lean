
module

public import CFSG.Sporadic.Schreier.J4SCommGenBase
public import CFSG.Sporadic.Schreier.J4SPrimes

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native

@[expose] def a276Word : List ℤ :=
  [2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1,
    -2, 1]

@[expose] def wPaths : List (ℕ × List (List ℕ)) := [
  (2, [[], [1], [2], [6], [1, 1], [1, 2], [1, 3], [1, 4], [1, 6], [1, 7], [6, 8]]),
  (72, [[], [1], [2], [3], [4], [5], [6], [7], [8], [1, 2], [1, 3]]),
  (74, [[], [1], [2], [3], [4], [5], [6], [7], [8], [1, 3], [1, 5]]),
  (433, [[], [1], [2], [3], [6], [7], [8], [1, 1], [1, 3], [3, 1], [6, 2]]),
  (435, [[], [1], [2], [3], [6], [7], [8], [1, 1], [1, 2], [1, 4], [1, 5]]),
  (505, [[], [1], [2], [3], [4], [5], [6], [7], [8], [1, 2], [1, 5]]),
  (507, [[], [1], [2], [4], [5], [6], [7], [8], [1, 1], [1, 2], [1, 6]]),
  (1169, [[], [1], [2], [3], [4], [6], [7], [8], [1, 1], [1, 2], [1, 3]]),
  (1171, [[], [1], [2], [3], [4], [6], [7], [8], [1, 1], [1, 2], [2, 4]]),
  (1241, [[], [1], [2], [3], [4], [5], [6], [7], [8], [1, 1], [1, 2]]),
  (1243, [[], [1], [3], [4], [5], [6], [7], [8], [1, 1], [1, 2], [1, 8]]),
  (1312, [[], [1], [2], [3], [4], [6], [7], [8], [1, 1], [1, 2], [1, 3]]),
  (1314, [[], [1], [2], [3], [4], [6], [7], [8], [1, 2], [1, 5], [2, 1]]),
  (1384, [[], [1], [2], [3], [4], [5], [6], [7], [8], [1, 3], [1, 6]]),
  (1386, [[], [1], [2], [3], [4], [5], [6], [7], [8], [1, 1], [1, 6]])]

@[expose] def commPairs : List (ℕ × ℕ) :=
  [(2, 0), (2, 1), (2, 2), (4, 0), (4, 1), (4, 2), (4, 3), (8, 0), (16, 0), (16, 3)]

@[expose] def colSel : Array (ℕ × ℕ) := #[
  (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10),
  (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (0, 17), (0, 18), (0, 19), (0, 20),
  (0, 21), (0, 22), (0, 23), (0, 24), (0, 25), (0, 26), (0, 27), (0, 28), (0, 29), (0, 30),
  (0, 31), (0, 32), (0, 33), (0, 34), (0, 35), (0, 36), (0, 37), (0, 38), (0, 39), (0, 40),
  (0, 41), (0, 42), (0, 43), (0, 44), (0, 45), (0, 46), (0, 47), (0, 50), (0, 51), (1, 0),
  (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11),
  (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (1, 17), (1, 18), (1, 19), (1, 20), (1, 22),
  (1, 23), (1, 25), (1, 26), (1, 27), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6),
  (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 8), (4, 0),
  (4, 1), (4, 2), (4, 3), (4, 4), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (6, 0), (6, 1), (6, 3),
  (7, 0), (8, 0), (9, 0)]

@[expose] def unitCols : ℕ × ℕ := (0, 1)

@[expose] def tInvRows : Array ℕ := #[
  0x718526e651c68ee933e94ba166c0, 0xbd1edda34bc46cfe4714d34689d8, 0x8c3879475661579eea64582c9630,
  0xbddd2a6adfd964f745b10a60a8e8, 0x1cc6ef3ca38817e79bc6b9a3a2a0, 0xa86702b825c42dfe3ef3b9a46498,
  0xd69965c416d29803baac23c65ed4, 0xa09f9f23757b065b9cb917756b74, 0x3432db3ab2067062b0a466df0588,
  0xe519562f6c888ce9d80fd8b6d1dc, 0x819f19068322f2ead0c5db0b67d4, 0x516721042f7602cef34a5aa7b1bc,
  0x107857dd5a32a04637ababdbfa4, 0x25dd3aeffb131723b2c71ffeb900, 0x3e2bbbfea81fc8d52d7058a350b8,
  0xadbc6f922048e710c00bb23d51e4, 0x40329655e52a8a4f980d03a1f73c, 0x6ea206a1a24c1c1ce3da30867728,
  0xe929e5371eb319c94b9125b47098, 0x81d9b8e0c19e3ff099764137afe4, 0x18415ea2adba9ca816685071e02c,
  0xd4fb424debb923e67a0264574870, 0x30db3517aad5916e69a975fbde34, 0x5f5ac3e05400c833f84db5dd87c8,
  0x257f75df6c5cf226c6d2fe99eea0, 0x13fd5caff7c677a1b319678cc2ec, 0x6ecf2cc15c68645871e22d1dc46c,
  0x3a353b03fc634621bac91d5f775c, 0x2d18ccc35655d7945f1fa37cb88c, 0x551c5eb84b929a84c12a7c23a090,
  0x9e4c1312ceda083339c00dec81a8, 0xdc70d817365ac63bdc9066252ce8, 0x3bacd667c2f67e2b828a9edd6890,
  0x10cf291f763dc226d4f2a1a0273c, 0x6b079c97521b5fd2932bf16d409c, 0x1c118a93fa967210ad02e4f19380,
  0xeb2ea89d0fc78cda5949dc40304, 0xdcefd760bcd0b1cb09593dc56c74, 0xfbfce3292b104ea7cd22ca9fe500,
  0x8b84bf39cb17d6a2527ad93c3ac8, 0x216faab198a0669783f141f65a88, 0x2aca1b9d80266b10148d08366828,
  0xe06b3e32bf9c4ffe25a30a3a9bf0, 0x86e4b38cc780c13a0c55958c8fd4, 0xdedd2e9c7a27c4b52b5f1a6688c0,
  0x9b5a92f82667fc488b723fd4e318, 0xb16abe33057f99b9f4fd6a18ae54, 0x79b3b552d3e60681cbe60b0fecc0,
  0xebc386b7ae5dd250f9d6c8c9f5ec, 0x7aac0b0af3196420688ccbe69560, 0x744938bd1c05c0b82093980323a4,
  0x2e60ee061ec492134e51bba4aa9c, 0x2c1b1196f3d9a528b2edce1d840, 0x7663fdf08656d5116880fa114fc0,
  0x75c54e62b7f0b108331b2b4d75e0, 0xf60abbef4d0d05a721c71a05df64, 0xe70f7cb7954aeb9a7b0e24bb26e0,
  0x6967e9fb063e5a2a3c86c82780a4, 0x7529991db722b9a9d1df2c9d8280, 0x89d957b7ef8f2d95891c5095eb68,
  0xb84b663f86a2d5080706dd8dcde4, 0x76e588ef3377565bb822a90788b8, 0xb7dd90ef3634138c3199e6a8c600,
  0x5e4ce86804c238fe773284bbcf40, 0x226322a1a9193e116c2934c13d54, 0xa0df151f6008ce205b81064d414,
  0x61265ae29b1e4025a99cc19ea388, 0x98eea2766106e2316a484a88e6d8, 0xc19e04bb54ad6b7662db8a8fe0bc,
  0xb219b35a7e91d52bfd178e7f5dc, 0x6172d9a6ab38077a17ac180ebf78, 0x5dc16f4de9581bf1dc47b0a974b0,
  0x7f1e91003fc07d1bbdc40e0c0c6c, 0x6a784bf725bfe2c1e897a0d42e74, 0x182be55791a1b2ecc7d053bf8844,
  0xe921f624acbe1a41c769a870ed80, 0x5bd7818415b5d3f24771d2422b0, 0x7ecaffc59b5e13c9f41de3f904c8,
  0xb9d596da8319414b7cb8b025bbac, 0x564c56571bcc913cd66b477bf89c, 0x2e431a47d1eb9cb82e7073cc9f84,
  0xe1c89ac5202e1902ca3a45a219c8, 0xd24fd462e59f57cc6febdedd757c, 0x3abd79abfecf7d4436020dfd2b38,
  0x5771fd62dae10975080fa8646ecc, 0x879979882cd2e3041011e8c493e0, 0x6e6020f003838a48e4471a77a0f0,
  0xb01f1191085b4b909886ef6ca594, 0x60c6990e33a78387d973493cc3b4, 0x55e8fafa130929ec306cf9001018,
  0xb22c1e3ab4597bd3399eeaabf2fc, 0x61d41f4cafce31ba332a248a1134, 0x17d12584c14b2a2690036d0113dc,
  0xa31c6dc7ae5bf7f12e6f46921800, 0x1af70149502bb853cdc665bc9c24, 0x863a83a87cd7417e47cc48bc1f04,
  0xfcda97fb4e4e351a300bef3ffe28, 0x5451573d0f2d187927455aa73aa8, 0xbdc1768f79a6784a1785bcdf38fc,
  0x172dd2994fae7840a2d1e7c25cf4, 0xf5bac9cc67cc09b026af9cade4b8, 0x351a4ba9c9608b0f8257f286eed0,
  0x398baf85fc25df589448843a1934, 0x805ae46f73a4c373fc9788cfa5d8, 0x41112b97d8d0c159dc8ff40deec4,
  0xaa3536f7e55a44e0da8edd9c643c, 0xfd22306d882c508d96f39d62b344, 0x82eb0eec766169b7d02084f5f640,
  0x5988a1b28fce8fec08fdb041cc68, 0x4375f4637b3e8c5f57be6dc96eb0, 0xabb73d9045c31e642701b34c630d,
  0x643cdb0f539af9c44267d4bc5b36]

@[expose] def wSet : List ℕ := 0 :: wPaths.map Prod.fst

@[expose] def pathApp (w : List ℕ) (a : ℕ) : ℕ := w.foldl (fun b m => app11 (sCols m) b) a

@[noinline, expose] def spanOK (vs : List ℕ) : Bool :=
  let combos := (List.range 2048).map (xorSub vs)
  (List.range 2048).all fun c => combos.contains c

@[expose] def pathVecs (p : ℕ × List (List ℕ)) : List ℕ := p.2.map fun w => pathApp w p.1

@[expose] def xorRows (X Y : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 112) fun i => X[i.val]?.getD 0 ^^^ Y[i.val]?.getD 0

@[expose] def selRows (l : ℕ) : Array ℕ :=
  Array.ofFn (n := 112) fun j => (List.range colSel.size).foldl
    (fun acc c => if colSel[c]! = (l, j.val) then acc ||| 2 ^ c else acc) 0

@[expose] def eRows : Array ℕ :=
  Array.ofFn (n := 112) fun r =>
    (if r.val = unitCols.1 then 2 ^ 110 else 0) ||| (if r.val = unitCols.2 then 2 ^ 111 else 0)

@[expose] def commM (p : ℕ × ℕ) : ℕ := p.1 ^^^ app11 generatorColumns[p.2]! p.1

@[expose] def certSum : List (Array ℕ × Array ℕ) → Array ℕ
  | [] => eRows
  | (M, U) :: L => xorRows (xorRows (mulRows 112 M U) U) (certSum L)

@[expose] def certList : List (Array ℕ × Array ℕ) :=
  (List.range 10).map fun l => ((etaP (commM commPairs[l]!)).2, selRows l)

end CFSG.Sporadic.J4Schreier
