module

public import CFSG.Certificates.PresentationLetters

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure.CoxB3

@[expose] noncomputable def edgeBlk0 : ℕ := 0xbc5d7ab6d57dc2fb25f7cb2e55d6aeaa5d74aad14d22da25b6ca2c15542c9d59629eb134c2b96575c9645554a4a54d32a6394d323a04718a225450a29c43089e093cf207e4d347e50fbe25794b2a7a40eba2472492471b51c69b8834d0899914519853aea85890c3188132ca8181040185d3efa5de0b2c1e563cf45548ebb14712aaa7140e38146c26986d28db71269269a6918d35114432c84504c30905c1e785ce8baf0e591e7a58d8b2d0d342aa834c4a288c2e269c2d2471c922c24902ca48a28a401450409882109221e7c208071c081d1a6a1cc038e0c1a1864185459685121454109430c891012481034410830a0e3c082030c02140618141828b01050822040818700010412000008200
@[expose] noncomputable def edgeBlk (_b : ℕ) : ℕ :=
  edgeBlk0
@[expose] noncomputable def edge (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (edgeBlk (Nat.shiftRight i 11))
    (Nat.mul 15 (Nat.land i 2047))) 32767
@[expose] noncomputable def fx (f : ℕ) : ℕ :=
  Nat.land (edge f) 63
@[expose] noncomputable def fc (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (edge f) 6) 7
@[expose] noncomputable def fy (f : ℕ) : ℕ :=
  Nat.shiftRight (edge f) 9

@[expose] noncomputable def justBlk0 : ℕ := 0x8c5eba8b5e2287583285582e845826000000835c227f54327e54260000007d5a2a7b502e7a502600000079582a764e3a754e2200000074562a724a2e714a260000007048220000006f52226b46326a462600000069502a66443a654422000000644e2a62402e614026000000603e260000005f4a2a5c3c3a5b3c220000005a482a58382e57382600000056362200000055442a53322e5232260000005142224d30324c30260000004b402248303647302a000000462e22000000453c2a432a2e422a260000004128260000004038223d28363c282a0000003b362a39242e38242600000037342233223232222600000031222a0000003020220000002f2e2a2d1c2e2c1c260000002b2c22271a32261a26000000251a2a0000002418220000002316260000002224221f16361e162a0000001d14220000001c202a1a122e19122600000018102600000017102a000000160e2200000015182a130c2e120c26000000110a220000001008260000000f12220c08360b082a0000000a062200000009042600000008042a000000070a2a05022e04022600000003022200000002002600000001002200000000002a000000
@[expose] noncomputable def justBlk (_b : ℕ) : ℕ :=
  justBlk0
@[expose] noncomputable def just (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (justBlk (Nat.shiftRight i 11))
    (Nat.mul 24 (Nat.land i 2047))) 16777215
@[expose] noncomputable def kind (f : ℕ) : ℕ := Nat.land (just f) 3
@[expose] noncomputable def wi (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 2) 7
@[expose] noncomputable def ft (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 5) 15
@[expose] noncomputable def fs (f : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (just f) 9) 63
@[expose] noncomputable def fo (f : ℕ) : ℕ :=
  Nat.shiftRight (just f) 15

@[expose] noncomputable def refsBlk0 : ℕ := 0x1127d3b2111a00469f8d8572e9c50600452050e00450011400441e0c44b2799cf600430010c00421ccea00410010400401bcb6643c800fc003f000f86935800f4003d000f0003b180882d1c94cd6003a000e8003917c864630800e00038000dc542c800d80036000d400341446e3a29800cc0033000c84826800c40031000c0002f0f882002e000b8002d0f048150d8c49a002c000b0002b0f04e291f800a8002a000a400280c86a00270009c002600094300e87c6600240009000230a85e00220008800210a02c06048645e002000080001f00078001d08046001c00070001b0781c020284446001a0006800190006000170005818058444200150005400140004c120b8004800120004400100003c000e0301e000d00034000c0002c000a0180003068002400090002000070001800050000a000400010000300008000100000
@[expose] noncomputable def refsBlk (_b : ℕ) : ℕ :=
  refsBlk0
@[expose] noncomputable def refs (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (refsBlk (Nat.shiftRight i 11))
    (Nat.mul 9 (Nat.land i 2047))) 511
@[expose] noncomputable def plBlk0 : ℕ := 0x9c4aa391383bf9f2f072375a8c85facd58a851a5d208c411ecee723317cb6562893490431e0e0662e128803817090381609020080000
@[expose] noncomputable def plBlk (_b : ℕ) : ℕ :=
  plBlk0
@[expose] noncomputable def pl (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (plBlk (Nat.shiftRight i 11))
    (Nat.mul 9 (Nat.land i 2047))) 511
@[expose] noncomputable def ffiBlk0 : ℕ := 0x8ac5a3b1a8fc621b0e89c42331e82c1a371c85c222f147ebfa07007abda23127dbe21f0c78bca030274ba9deec84c2a0f0470b89cee46cb69fefc6fb71aad676bb9f2fa7bbd19ace69b418ac679bc196c875ba182c272b9972ba71b817ebc58ac96eb46eb79b6d857ab152aa6bb514aa668b493a9e67b3146a04ca696ab664b298ec44ba51229244a2986c047a31028243a117abe5dae15aae3e9f966b03c9e956a8389c94ea43b9d0d26a379b142a24fa712a963299936983098926902e9790a8646a3916882d960aa5641a00a2523f9f0924a3d9e09e4c22918da6e3a9d8e6702c9688242359a07a3e339906a363198076382f97062322b9505a2e299409a4e259205628128988e441088886400e8787e3c1c8e86e34148a8321a0884866300b8505e2c068384e240482846200a8583e1c028183618098401e0c008081608038100600
@[expose] noncomputable def ffiBlk (_b : ℕ) : ℕ :=
  ffiBlk0
@[expose] noncomputable def ffi (i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (ffiBlk (Nat.shiftRight i 11))
    (Nat.mul 9 (Nat.land i 2047))) 511
@[expose] noncomputable def liveMask : ℕ := 0xffffffffffff
@[expose] noncomputable def live (x : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight liveMask x) 1) 1

@[expose] noncomputable def words : List (List ℕ) :=
  [[2, 2], [4, 4], [0, 0], [4, 0, 4, 0], [4, 2, 4, 2, 4, 2, 4, 2], [0, 2, 0, 2, 0, 2], [2, 0, 2,
    0, 2, 0]]

open CFSG.Certificates.CosetEnumeration

theorem facts_0 :
    factsOK 48 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 144 =
      true := by
  decide +kernel

theorem facts_all :
    factsOK 48 7 fx fc fy kind wi fs ft fo refs pl (invLetter 3)
      words [] 0 144 =
      true := by
  exact facts_0

theorem cover_0 : coverOK 48 6 144 fx fc fy (invLetter 3) ffi live 0 288 = true := by
  decide +kernel

theorem cover_all : coverOK 48 6 144 fx fc fy (invLetter 3) ffi live 0 288 = true := by
  exact cover_0

theorem live_zero : live 0 = true := by
  decide +kernel

end CFSG.Timmesfeld.Bridge.RootClosure.CoxB3
