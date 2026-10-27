module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUModel

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  UCoord UModel
open CFSG.SectionRank.OddCover (diagHom)

@[expose] noncomputable def ggTBJSuD {K : Type} [Field K] {n d p : ℕ} {u : Kˣ}
    (h : UnitaryFieldData 2 n K) [NeZero p] (hu : u ^ p = 1) (huq : u ^ (2 ^ n + 1) = 1)
    (hord : orderOf u = p) : ↥(sumZero d p) →* ↥(unitarySU 2 n K d) :=
  ((diagHom d).comp (uvec hu)).codRestrict _ fun f =>
    TableBUE.diagHom_mem_unitarySU h (fun k => uvec_pow_norm hu huq f k) (prod_uvec hu hord f)

theorem ggTBJSuD_coe {K : Type} [Field K] {n d p : ℕ} {u : Kˣ}
    (h : UnitaryFieldData 2 n K) [NeZero p] (hu : u ^ p = 1) (huq : u ^ (2 ^ n + 1) = 1)
    (hord : orderOf u = p) (f : ↥(sumZero d p)) :
    ((ggTBJSuD h hu huq hord f : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
      diagHom d (uvec hu f) :=
  rfl

end CFSG.StandardType

end
