module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut

public section

namespace CFSG.PSL3Four.Native

@[expose] def pg1T : Tab :=
  #[0, 11, 9, 10, 12, 14, 16, 15, 13, 2, 3, 1, 4, 8, 5, 7, 6, 17, 18, 19, 20, 36, 38, 33, 24, 27,
    30, 25, 39, 29, 26, 31, 41, 23, 34, 37, 21, 35, 22, 28, 40, 32]

@[expose] def pg2T : Tab :=
  #[5, 6, 7, 8, 0, 18, 11, 16, 3, 1, 13, 9, 17, 10, 20, 2, 15, 14, 4, 19, 12, 27, 25, 41, 34, 32,
    22, 39, 35, 31, 21, 29, 26, 28, 24, 36, 33, 38, 23, 30, 40, 37]

@[expose] def pg3T : Tab :=
  #[16, 5, 18, 3, 11, 1, 20, 12, 8, 17, 10, 4, 7, 13, 15, 14, 0, 9, 2, 19, 6, 21, 28, 27, 29, 26,
    25, 23, 22, 24, 37, 34, 36, 35, 31, 33, 32, 30, 38, 39, 40, 41]

@[expose] def pg4T : Tab :=
  #[18, 7, 2, 13, 12, 14, 6, 1, 10, 9, 8, 15, 4, 3, 5, 11, 16, 20, 0, 19, 17, 33, 27, 36, 24, 38,
    41, 22, 37, 29, 32, 31, 30, 21, 34, 39, 23, 28, 25, 35, 40, 26]

@[expose] def fg1T : Tab :=
  #[18, 11, 16, 3, 5, 4, 9, 15, 8, 6, 10, 1, 14, 13, 12, 7, 2, 20, 0, 19, 17, 39, 32, 37, 24, 26,
    25, 30, 36, 29, 27, 31, 22, 35, 34, 33, 28, 23, 41, 21, 40, 38]

@[expose] def fg2T : Tab :=
  #[20, 7, 9, 3, 14, 12, 16, 1, 8, 2, 10, 15, 5, 13, 4, 11, 6, 18, 17, 19, 0, 41, 28, 30, 24, 35,
    33, 37, 22, 29, 23, 31, 36, 26, 34, 25, 32, 27, 39, 38, 40, 21]

@[expose] def fg3T : Tab :=
  #[5, 16, 11, 3, 18, 0, 7, 6, 8, 15, 10, 2, 20, 13, 17, 9, 1, 14, 4, 19, 12, 38, 22, 30, 34, 26,
    25, 37, 28, 31, 23, 29, 32, 35, 24, 33, 36, 27, 21, 41, 40, 39]

@[expose] def fg4T (_ : Unit := ()) : Tab :=
  #[16, 5, 18, 3, 11, 1, 20, 12, 8, 17, 10, 4, 7, 13, 15, 14, 0, 9, 2, 19, 6, 21, 28, 27, 29, 26,
    25, 23, 22, 24, 37, 34, 36, 35, 31, 33, 32, 30, 38, 39, 40, 41]

@[expose] def nT : Tab :=
  #[0, 2, 4, 3, 1, 15, 14, 16, 13, 5, 8, 6, 7, 10, 11, 9, 12, 20, 17, 19, 18, 23, 38, 32, 29, 35,
    26, 36, 41, 31, 22, 24, 21, 25, 34, 33, 39, 28, 30, 27, 40, 37]
@[expose] def pGens : Array Tab := #[pg1T, pg2T, pg3T, pg4T]

@[expose] def fGens (_ : Unit := ()) : Array Tab := #[fg1T, fg2T, fg3T, fg4T]

@[expose] def l34SylCheck (ES : Array Tab) : Bool :=
  let EP := enumBFS 42 pGens 64
  let EPi := EP.tabs.map (invTab 42)
  let idxP := indexOf EP.tabs
  let Et := EP.tabs.filter fun t =>
    allBelow EP.tabs.size fun j => comp 42 t EP.tabs[j]! == comp 42 EP.tabs[j]! t
  let EF := enumBFS 42 fGens 16
  let idxF := indexOf EF.tabs
  let nI := invTab 42 nT
  (allBelow pGens.size fun j => memTab ES pGens[j]!) &&
    enumOK 42 pGens EP && EP.tabs.size == 64 && invsOK 42 EP.tabs EPi &&
    (allBelow EP.tabs.size fun k => powTab 42 EP.tabs[k]! 4 == idTab 42) &&
    (allBelow EP.tabs.size fun k => found idxP EP.tabs (conjTab 42 r₃T r₃T EP.tabs[k]!)) &&
    Et.size == 4 &&
    (allBelow Et.size fun k =>
      comp 42 Et[k]! Et[k]! == idTab 42 && comp 42 r₃T Et[k]! == comp 42 Et[k]! r₃T &&
        anyBelow EP.tabs.size fun a => anyBelow EP.tabs.size fun b =>
          commTab 42 EP.tabs[a]! EP.tabs[b]! EPi[a]! EPi[b]! == Et[k]!) &&
    enumOK 42 fGens EF && EF.tabs.size == 16 &&
    (allBelow EF.tabs.size fun k =>
      found idxP EP.tabs EF.tabs[k]! && comp 42 EF.tabs[k]! EF.tabs[k]! == idTab 42 &&
        allBelow EF.tabs.size fun l => comp 42 EF.tabs[k]! EF.tabs[l]! == comp 42 EF.tabs[l]! EF.tabs[k]!) &&
    (allBelow Et.size fun k => found idxF EF.tabs Et[k]!) &&
    memTab ES nT && invsOK 42 #[nT] #[nI] &&
    (allBelow EP.tabs.size fun k =>
      found idxP EP.tabs (conjTab 42 nT nI EP.tabs[k]!) &&
        found idxP EP.tabs (conjTab 42 nI nT EP.tabs[k]!)) &&
    (allBelow Et.size fun a => allBelow Et.size fun b =>
      Et[a]! == idTab 42 || Et[b]! == idTab 42 || Et[a]! == Et[b]! ||
        conjTab 42 nT nI Et[a]! == Et[b]! || conjTab 42 nI nT Et[a]! == Et[b]!)

end CFSG.PSL3Four.Native
