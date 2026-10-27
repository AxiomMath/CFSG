module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.PSL3Four.Native

@[expose] def e1T : Tab :=
  #[8, 17, 2, 11, 14, 5, 7, 6, 0, 13, 10, 3, 19, 9, 4, 15, 18, 1, 16, 12, 20, 21, 22, 23, 24, 25,
    36, 37, 34, 35, 40, 41, 38, 39, 28, 29, 26, 27, 32, 33, 30, 31]

@[expose] def e2T : Tab :=
  #[6, 9, 2, 16, 19, 5, 0, 8, 7, 1, 10, 18, 14, 17, 12, 15, 3, 13, 11, 4, 20, 21, 22, 23, 24, 25,
    31, 30, 33, 32, 27, 26, 29, 28, 39, 38, 41, 40, 35, 34, 37, 36]

@[expose] def e3T : Tab :=
  #[1, 0, 2, 4, 3, 5, 9, 13, 17, 6, 10, 14, 18, 7, 11, 15, 19, 8, 12, 16, 20, 22, 21, 23, 25, 24,
    26, 30, 34, 38, 27, 31, 35, 39, 28, 32, 36, 40, 29, 33, 37, 41]

@[expose] def e4T : Tab :=
  #[14, 11, 2, 17, 8, 5, 12, 19, 4, 18, 10, 1, 6, 16, 0, 15, 13, 3, 9, 7, 20, 25, 24, 23, 22, 21,
    36, 30, 39, 29, 27, 41, 32, 34, 33, 35, 26, 40, 38, 28, 37, 31]

@[expose] def e16Gens : Array Tab := #[e1T, e2T, e3T, e4T]

@[expose] def l34E16Check (gT : Array Tab) : Bool :=
  let ET := enumBFS 42 gT 64
  let idxT := indexOf ET.tabs
  let EE := enumBFS 42 e16Gens 16
  enumOK 42 gT ET &&
    (allBelow e16Gens.size fun j => found idxT ET.tabs e16Gens[j]!) &&
    enumOK 42 e16Gens EE && EE.tabs.size == 16 &&
    (allBelow EE.tabs.size fun k =>
      comp 42 EE.tabs[k]! EE.tabs[k]! == idTab 42 &&
        allBelow EE.tabs.size fun l =>
          comp 42 EE.tabs[k]! EE.tabs[l]! == comp 42 EE.tabs[l]! EE.tabs[k]!)

@[expose] def l34RCentCheck (ER : Array Tab) : Bool :=
  let r4 := r₄T ()
  let C := centTabs 42 ER r4
  let c0 := C.map (invTab 42)
  let D₁ := derivedData 42 C c0
  let c1 := D₁.1.map (invTab 42)
  let D₂ := derivedData 42 D₁.1 c1
  let c2 := D₂.1.map (invTab 42)
  let D₃ := derivedData 42 D₂.1 c2
  let c3 := D₃.1.map (invTab 42)
  let D₄ := derivedData 42 D₃.1 c3
  let c4 := D₄.1.map (invTab 42)
  let D₅ := derivedData 42 D₄.1 c4
  C.size == 864 &&
    derivedOK 42 C c0 D₁.1 D₁.2 && D₁.1.size == 216 &&
    derivedOK 42 D₁.1 c1 D₂.1 D₂.2 && D₂.1.size == 72 &&
    derivedOK 42 D₂.1 c2 D₃.1 D₃.2 && D₃.1.size == 18 &&
    derivedOK 42 D₃.1 c3 D₄.1 D₄.2 && D₄.1.size == 9 &&
    derivedOK 42 D₄.1 c4 D₅.1 D₅.2 && D₅.1.size == 1

end CFSG.PSL3Four.Native
