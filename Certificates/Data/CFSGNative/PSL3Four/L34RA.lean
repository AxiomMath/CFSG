module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.PSL3Four.Native

@[expose] def raLetterT (j : Nat) : Tab := if j = 0 then g₁T else if j = 1 then g₂T else g₃T

@[expose] def raWordT (w : List Nat) : Tab :=
  w.foldl (fun t j => comp 42 t (raLetterT j)) (idTab 42)

@[expose] def raT0Gens (_ : Unit := ()) : Array Tab :=
  #[raWordT [0, 0, 1, 0, 1, 0, 1], raWordT [0, 1, 0, 0, 2, 0, 1, 0, 0],
    raWordT [0, 1, 0, 0, 1, 0, 1, 0, 0], raWordT [0, 1, 0, 2, 0, 0, 1, 0, 0]]

@[expose] def raGens (_ : Unit := ()) : Array Tab :=
  #[raWordT [0, 0, 1, 0, 1, 0, 1], raWordT [0, 1, 0, 0, 2, 0, 1, 0, 0],
    raWordT [0, 1, 0, 0, 1, 0, 1, 0, 0], raWordT [0, 1, 0, 2, 0, 0, 1, 0, 0], g₅T, g₆T]

@[expose] def raEnum (_ : Unit := ()) : Enum := enumBFS 42 (raGens ()) 256

@[expose] def raMem (T : Array Tab) (x : Tab) : Bool := anyBelow T.size fun k => T[k]! == x

@[expose] def raMulTab (_ : Unit := ()) : Array Nat :=
  let E := raEnum ()
  let idx := indexOf E.tabs
  Array.ofFn (n := 65536) fun k =>
    posOf idx E.tabs (comp 42 E.tabs[k.val / 256]! E.tabs[k.val % 256]!)

@[expose] def raInvTab (_ : Unit := ()) : Array Nat :=
  let E := raEnum ()
  let idx := indexOf E.tabs
  Array.ofFn (n := 256) fun i => posOf idx E.tabs (invTab 42 E.tabs[i.val]!)

@[expose] def labSBits : Nat :=
  115185319018614405845063110084628508767914324550021265537161291679

@[expose] def labT0Bits : Nat :=
  115185319018614405845063110084628508767914324550021265537161291679

@[expose] def labUniBits : Nat :=
  3675041894739040209002281679329246597325836024681920610661309514957149175808

@[expose] def raEnumOK (E : Enum) : Bool :=
  enumOK 42 (raGens ()) E && E.tabs.size == 256 && E.tabs[0]! == idTab 42 &&
    E.tabs[5]! == g₅T && E.tabs[6]! == g₆T && E.tabs[29]! == r₄T

@[expose] def raT0OK (ET : Enum) : Bool := enumOK 42 (raT0Gens ()) ET && ET.tabs.size == 64

@[expose] def raMulOK (E : Enum) (M : Array Nat) : Bool :=
  M.size == 65536 &&
    allBelow 256 fun i => allBelow 256 fun j =>
      M[256 * i + j]! < 256 && E.tabs[M[256 * i + j]!]! == comp 42 E.tabs[i]! E.tabs[j]!

@[expose] def raInvOK (M V : Array Nat) : Bool :=
  V.size == 256 && allBelow 256 fun i => V[i]! < 256 && M[256 * i + V[i]!]! == 0

@[expose] def raLabOK (E : Enum) (ES : Array Tab) (ET O : Enum) : Bool :=
  allBelow 256 fun i =>
    (labSBits.testBit i == raMem ES E.tabs[i]!) &&
      (labT0Bits.testBit i == raMem ET.tabs E.tabs[i]!) &&
      (labUniBits.testBit i == raMem O.tabs E.tabs[i]!) &&
      (!labSBits.testBit i || labT0Bits.testBit i)

@[expose] def l34RACheck (ES : Array Tab) : Bool :=
  let E := raEnum ()
  let ET := enumBFS 42 (raT0Gens ()) 64
  let O := orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₄T 1963
  let M := raMulTab ()
  let V := raInvTab ()
  raEnumOK E && raT0OK ET && raMulOK E M && raInvOK M V && raLabOK E ES ET O

end CFSG.PSL3Four.Native
