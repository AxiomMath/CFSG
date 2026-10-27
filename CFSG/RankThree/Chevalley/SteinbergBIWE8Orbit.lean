module

public import CFSG.RankThree.Chevalley.SteinbergBIWE8Code

public noncomputable section

namespace CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.WE8.Native

variable {t₀ : W8} {d : OrbitData}

theorem code_conj' {j : ℕ} (hj : j < 8) (w : W8) :
    conjI j (code w) =
      code (simple .E8 ⟨j, hj⟩ * w * simple .E8 ⟨j, hj⟩) :=
  (code_conj ⟨j, hj⟩ w).symm

theorem isConj_conj_simple (i : Fin Tag.E8.rank) (u : W8) :
    IsConj u (simple .E8 i * u * simple .E8 i) := by
  refine isConj_iff.2 ⟨simple .E8 i, ?_⟩
  rw [(coxeterSystem .E8).inv_simple]

end CFSG.RankThree.Chevalley.WeylE8
