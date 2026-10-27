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

theorem cols_C : ∀ k : Perm (Fin 5),
    cols.map (fun x => fld x (OC + 4 * pos k) 2) =
      (List.range 18).map (fun l => pY (enc (orth.act k⁻¹ (basC l 1 k * basC l S5g k)))) ∧
    cols.map (fun x => fld x (OC + 4 * pos k + 2) 2) =
      (List.range 18).map (fun l =>
        pY (enc (orth.act k⁻¹ (basC l 1 (k * S5g) * basC l S5g (k * S5g))))) := by
  decide +kernel

end FL

end Gap7

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
