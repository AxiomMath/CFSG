module

public import CFSG.Quasithin.Vol2.Ch11SecC37V6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem fsuV_not_le_centralizer (i : Inp37) (hTVS : FactTransvPointSL3)
    (hTVP : FactTransvPointSp4) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ¬ fsuV T I ≤ Subgroup.centralizer (VZ T H : Set G) := by
  intro hV
  obtain ⟨-, -, hO2⟩ := h3228 G T L I s.hyp.fsu
  rw [SecA.fsuL0_eq s.hyp] at hO2
  have hR := s.pCore_le_centralizer_A i hTVS hTVP hVL
  apply s.hAC
  have hVH : VZ T H ≤ pCoreOf 2 (L ⊔ T) := by
    rw [hO2]
    exact le_inf s.VZ_le_T (Subgroup.le_centralizer_iff.mp hV)
  exact Subgroup.le_centralizer_iff.mp (hVH.trans hR)

theorem fsuV_eq_A (i : Inp37) (hTVS : FactTransvPointSL3) (hTVP : FactTransvPointSp4)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    fsuV T I = conjSubgroup (fsuV T I) g ∧
      QuasithinUnique.IsSylowTwoOf (autOn (fsuV T I) (VZ T H)) (autOn (oTwoUpper H) (VZ T H)) := by
  have hV := s.fsuV_not_le_centralizer i hTVS hTVP h3228 hVL
  have h1 : conjSubgroup (fsuV T I) 1 = fsuV T I := by
    ext x
    rw [mem_conjSubgroup_iff, one_mul, inv_one, mul_one]
  have s₁ : Set37 T L I n V₁ H 1 :=
    { hyp := s.hyp, hV₁ := s.hV₁, h31 := s.h31, hnot := s.hnot
      hAT := by rw [h1]; exact SecA.fsuV_le_T s.hyp
      hAC := by rw [h1]; exact hV }
  have heq : fsuV T I = conjSubgroup (fsuV T I) g := by
    rw [s.eq_conj i hTVS hTVP hVL s₁, h1]
  refine ⟨heq, ?_⟩
  have : IsMulCommutative ↥(VZ T H) := s.isElemAbelian_VZ.1
  have hS := s.aStar_sylow i.hAS i.hF i.h1102 i.hKF.2.2.2 i.h1122 i.h1134 i.h1135 i.h1136
  rwa [← heq] at hS

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
