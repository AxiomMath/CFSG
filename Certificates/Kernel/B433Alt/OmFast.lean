module

public import Certificates.Kernel.B433Alt.OmOK
public import Certificates.Data.Kernel.B433Alt.OmF
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

public section

namespace CFSG.KD.B4AN

open CFSG.KC.B4A

@[expose] noncomputable def segKF (k : Nat) : Bool :=
  segChkF MS CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW CB LIVE RN RL GS XO SJ ST SA SN STL NSEG k

theorem segK_eq (k : Nat) : segK k = segKF k :=
  segChk_eq_F MS CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW CB LIVE RN RL GS XO SJ ST SA SN STL
    NSEG k

@[expose] noncomputable def relPChk (k : Nat) : Bool :=
  relPOK MS (omRels.getD (k / 19) []) (k % 19)

end CFSG.KD.B4AN

open Lean Elab Command in
elab "#b4an_seg_range " lo:num hi:num : command =>
  liftCoreM <| withOptions (Elab.async.set · false) do
    let boolT := mkConst ``Bool
    let tt := mkConst ``Bool.true
    for k in [lo.getNat:hi.getNat] do
      let name := `CFSG.KD.B4AN ++ Name.mkSimple s!"sg{k}"
      let kE := mkRawNatLit k
      let lhs := mkApp (mkConst `CFSG.KD.B4AN.segK) kE
      let mid := mkApp (mkConst `CFSG.KD.B4AN.segKF) kE
      let value := mkAppN (mkConst ``Eq.trans [1])
        #[boolT, lhs, mid, tt, mkApp (mkConst `CFSG.KD.B4AN.segK_eq) kE,
          mkApp2 (mkConst ``Eq.refl [1]) boolT tt]
      let t0 ← IO.monoNanosNow
      CFSG.KC.addThmDecl
        { name, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) boolT lhs tt, value }
      let ms := ((← IO.monoNanosNow) - t0).toFloat / 1e6
      logInfo m!"BMTIME sg{k} {ms} ms"

end
