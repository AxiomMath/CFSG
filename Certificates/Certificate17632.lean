
module


public import Certificates.Data.M13L33
import Certificates.Kernel.KDenseP.L33

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Dickson.BMRows.M13L33 in
theorem certificate17632 :
    (∀ r ∈ l33Rels,
        (r.map fun l => cond l.2 (![gw j1W, gw CFSG.HardMathSupport.Dickson.BMRows.M13L33.yW] l.1) (![gw j1W, gw CFSG.HardMathSupport.Dickson.BMRows.M13L33.yW] l.1)⁻¹).prod = 1) ∧
      gw CFSG.HardMathSupport.Dickson.BMRows.M13L33.yW * gw thirteenX = gw thirteenX * gw CFSG.HardMathSupport.Dickson.BMRows.M13L33.yW ∧
      gw j1W * gw thirteenX = gw thirteenX * gw j1W ∧ gw j1W ≠ 1 := KernelKDenseP.L33.facts17632

end Certificates
