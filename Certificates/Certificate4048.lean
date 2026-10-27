module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33DataInputs
import Certificates.Kernel.LocalQT.Small.C4048

public section

namespace Certificates

open CFSG.KD.LQT.C4048 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25L33 in
open CFSG.QuasithinUnique.Unc25K1 in
theorem certificate4048 : (rdet sa = 1 ∧ rdet sb = 1 ∧ rpw sa 8 = rone ∧ rmul sb sb = rone ∧
            rmul sb sa = rmul (rpw sa 3) sb ∧ P0R.Nodup ∧ P0R.length = 16 ∧ rone ∈ P0R ∧ sa ∈ P0R ∧
            sb ∈ P0R ∧ (∀ x ∈ P0R, ∀ y ∈ P0R, rmul x y ∈ P0R) ∧ (∀ x ∈ P0R, rpw x 16 = rone) ∧
            (∀ w ∈ W3, rdet w = 1) ∧
            (∀ t ∈ invsP0, ∀ s ∈ invsP0, t ≠ s → rmul t s = rmul s t →
              ∃ w ∈ W3, rpw w 3 = rone ∧ w ≠ rone ∧
                (∃ u ∈ [rone, t, s, rmul t s], rmul w t = rmul u w) ∧
                (∃ u ∈ [rone, t, s, rmul t s], rmul w s = rmul u w)))
    ∧ (∀ g ∈ rawList, NormProp g)
    ∧ (∀ g ∈ rawList, CentProp g)
    ∧ (∀ g ∈ rawList, FixProp g)
    ∧ (∀ g ∈ rawList,
          ¬ (rmul g (rcof sa) = rmul sa g ∧ rmul g (rcof sb) = rmul sb g)) :=
  CFSG.KC.LQT.R.s4048k _ CFSG.KC.LQT.R.mem_rawList _ _ _ _ ha hb hp hw hk hs

end Certificates
