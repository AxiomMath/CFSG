module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7FLData
public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher.S43

namespace Odd

namespace Gap7

namespace FL

theorem cols_P : ∀ i < 30,
    cols.map (fun x => fld x (4 * i) 2) =
      (List.range 18).map (fun l => pY (enc (basC l (ptRep i) 1))) ∧
    cols.map (fun x => fld x (4 * i + 2) 2) =
      (List.range 18).map (fun l => pY (enc (basC l (ptRep i) S5g))) := by
  decide +kernel

theorem cols_W : ∀ n < 11,
    cols.map (fun x => fld x (OW + 12 * n) 5) =
      (List.range 18).map (fun l => enc ((wit n).map (fun h => basC l h 1)).prod) ∧
    cols.map (fun x => fld x (OW + 12 * n + 5) 5) =
      (List.range 18).map (fun l => enc ((wit n).map (fun h => basC l h S5g)).prod) ∧
    cols.map (fun x => fld x (OW + 12 * n + 10) 2) =
      (List.range 18).map (fun l => pY (enc (qL (basC l) (wit n)))) := by
  decide +kernel

end FL

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
