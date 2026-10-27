module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Hj
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M3

public section

namespace CFSG.Quasithin.J4Fam

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc
open CFSG.QuasithinUnique.Vol2Native.A312L

@[expose] def J4M2Residual : Prop :=
  ∀ B : Subgroup J, B ∈ lFamily P0 → B ⊔ P0 ≤ Subgroup.centralizer ({z0} : Set J) →
    ¬ B ⊔ P0 ≤ Hj → ¬ B ⊔ P0 ≤ Subgroup.normalizer (V0 : Set J) → J4Shape ↥B

section Main


theorem m2_case_of_residual [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] (h : J4M2Residual) :
    J4Case (Subgroup.centralizer ({z0} : Set J)) := by
  intro B hB hBM
  by_cases h1 : B ⊔ P0 ≤ Hj
  · exact hj_case B hB h1
  by_cases h2 : B ⊔ P0 ≤ Subgroup.normalizer (V0 : Set J)
  · exact m3_case B hB h2
  exact h B hB hBM h1 h2

theorem famJ4_of_binders [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] (hO : J4OvergroupLocal) (hR : J4M2Residual) : FamJ4 :=
  famJ4_of_cases hO hj_case (m2_case_of_residual hR) m3_case

end Main

end CFSG.Quasithin.J4Fam
