module

public import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.PSL3Four.Native

@[expose] def g₁T : Tab :=
  #[5, 0, 6, 8, 7, 1, 9, 17, 13, 2, 10, 20, 15, 3, 11, 18, 16, 4, 12, 19, 14, 26, 21, 27, 29, 28,
    22, 30, 38, 34, 23, 31, 41, 36, 24, 32, 39, 37, 25, 33, 40, 35]

@[expose] def g₂T : Tab :=
  #[0, 9, 10, 11, 12, 5, 6, 7, 8, 1, 2, 3, 4, 17, 19, 20, 18, 13, 16, 14, 15, 21, 22, 23, 24, 25,
    30, 31, 32, 33, 26, 27, 28, 29, 38, 39, 40, 41, 34, 35, 36, 37]

@[expose] def g₃T : Tab :=
  #[0, 17, 20, 18, 19, 5, 6, 7, 8, 13, 15, 16, 14, 9, 12, 10, 11, 1, 3, 4, 2, 21, 22, 23, 24, 25,
    34, 35, 36, 37, 38, 39, 40, 41, 26, 27, 28, 29, 30, 31, 32, 33]

@[expose] def g₄T : Tab :=
  #[0, 1, 2, 3, 4, 5, 8, 6, 7, 17, 20, 18, 19, 9, 12, 10, 11, 13, 16, 14, 15, 21, 22, 23, 24, 25,
    26, 28, 29, 27, 34, 36, 37, 35, 38, 40, 41, 39, 30, 32, 33, 31]

@[expose] def g₅T : Tab :=
  #[0, 1, 2, 4, 3, 5, 6, 8, 7, 9, 10, 12, 11, 17, 18, 20, 19, 13, 14, 16, 15, 21, 22, 23, 25, 24,
    26, 27, 29, 28, 30, 31, 33, 32, 38, 39, 41, 40, 34, 35, 37, 36]

@[expose] def g₆T : Tab :=
  #[21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 0, 1, 2,
    3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

@[expose] def gTabs : Array Tab := #[g₁T, g₂T, g₃T, g₄T, g₅T, g₆T]

@[expose] def gensS : Array Tab := #[g₁T, g₂T, g₃T]

@[expose] def r₁T (_ : Unit := ()) : Tab := comp 42 (comp 42 (comp 42 g₁T g₁T) g₂T) g₁T

@[expose] def r₂T : Tab := g₅T

@[expose] def r₃T : Tab := g₆T

@[expose] def r₄T (_ : Unit := ()) : Tab := comp 42 g₅T g₆T

@[expose] def rTabs (_ : Unit := ()) : Array Tab := #[r₁T, r₂T, r₃T, r₄T]

@[expose] def sizes₂ : Array Nat := #[1, 21, 42, 56, 24, 24]

@[expose] def sizes₃ : Array Nat := #[1, 15, 20, 12, 12]

@[expose] def certificate (cS cR cO : Nat) : Bool :=
  let ES := enumBFS 42 gensS cS
  let ER := enumBFS 42 gTabs cR
  let gi := gTabs.map (invTab 42)
  let O₁ := orbitBFS 42 gTabs gi r₁T cO
  let O₂ := orbitBFS 42 gTabs gi r₂T cO
  let O₃ := orbitBFS 42 gTabs gi r₃T cO
  let O₄ := orbitBFS 42 gTabs gi r₄T cO
  let C₁ := centTabs 42 ES.tabs r₁T
  let C₂ := centTabs 42 ES.tabs r₂T
  let C₃ := centTabs 42 ES.tabs r₃T
  let C₄ := centTabs 42 ES.tabs r₄T
  let i₂ := C₂.map (invTab 42)
  let i₃ := C₃.map (invTab 42)
  let i₄ := C₄.map (invTab 42)
  let D₁ := derivedData 42 C₄ i₄
  let j₁ := D₁.1.map (invTab 42)
  let D₂ := derivedData 42 D₁.1 j₁
  let j₂ := D₂.1.map (invTab 42)
  let D₃ := derivedData 42 D₂.1 j₂
  enumOK 42 gensS ES && ES.tabs.size == 20160 &&
    enumOK 42 gTabs ER && ER.tabs.size == 241920 &&
    normalOK 42 ES.tabs gTabs gi gensS &&
    centralOK 42 ER.tabs gensS &&
    orbitOK 42 gTabs gi r₁T O₁ && orbitOK 42 gTabs gi r₂T O₂ &&
    orbitOK 42 gTabs gi r₃T O₃ && orbitOK 42 gTabs gi r₄T O₄ &&
    O₁.tabs.size == 315 && O₂.tabs.size == 360 && O₃.tabs.size == 1008 &&
    O₄.tabs.size == 280 &&
    coverOK 42 ER.tabs #[O₁.tabs, O₂.tabs, O₃.tabs, O₄.tabs] &&
    (allBelow 4 fun i => allBelow 4 fun j =>
      i == j || notInOK (#[O₁.tabs, O₂.tabs, O₃.tabs, O₄.tabs])[i]! rTabs[j]!) &&
    (allBelow 4 fun i => comp 42 rTabs[i]! rTabs[i]! == idTab 42 && !(rTabs[i]! == idTab 42)) &&
    notInOK ES.tabs r₂T && notInOK ES.tabs r₃T && notInOK ES.tabs r₄T &&
    C₁.size == 64 && C₂.size == 168 && C₃.size == 60 && C₄.size == 72 &&
    classOK 42 C₂ i₂ (classData 42 C₂ sizes₂) sizes₂ &&
    classOK 42 C₃ i₃ (classData 42 C₃ sizes₃) sizes₃ &&
    derivedOK 42 C₄ i₄ D₁.1 D₁.2 && D₁.1.size == 18 &&
    derivedOK 42 D₁.1 j₁ D₂.1 D₂.2 && D₂.1.size == 9 &&
    derivedOK 42 D₂.1 j₂ D₃.1 D₃.2 && D₃.1.size == 1

end CFSG.PSL3Four.Native
