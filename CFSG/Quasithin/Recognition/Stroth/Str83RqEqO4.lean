module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4
public import CFSG.Quasithin.Recognition.Stroth.Str83RqNorm
import CFSG.Quasithin.Recognition.Stroth.Str83Rq413

public section

namespace CFSG.Quasithin.Stroth.Rq

theorem str83RqEqNorm_of_O4
    (hO4 : Str83RqO4) : Str83RqEqNorm := by
  intro G _ _ L1 L2 S a hF hS hN ha hSz hB hL2
  obtain ⟨f, hfr⟩ := exists_frame hF hS hN ha hSz hB hL2
  by_cases hf : f = 2 * a + 1
  · exact hf ▸ hfr.hL2
  · obtain ⟨t⟩ := hfr.nonempty_track
    exact (t.false_of_GT_eq_K hfr hf (hO4 G L1 L2 S a f hfr hf t)).elim

theorem str83RqEq_of_O4
    (hO4 : Str83RqO4) : Str83RqEq :=
  str83RqEq_of_norm (str83RqEqNorm_of_O4 hO4)

end CFSG.Quasithin.Stroth.Rq

end
