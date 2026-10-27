module

public import CFSG.Quasithin.H13.A6S13821zz

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem not_transv_R_of_solvRad (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hX : oTwoRes (solvRad H) ≠ ⊥) :
    ∀ x ∈ pCoreOf 2 (S.L1 ⊔ T), ¬ InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V) := by
  have hXeq : oTwoRes (solvRad H) = S.X13820 := by
    rcases S.oTwoRes_solvRad_cases h139 h1334 h13 hS hH with h | ⟨hhat, h⟩ | ⟨hhat, h⟩
    · exact absurd h hX
    · rw [h, S.X13820_of_not_hat hhat]
    · rw [h, S.X13820_of_hat hhat]
  have hHX : H ≤ Subgroup.normalizer (S.X13820 : Set G) := by
    rw [← hXeq]
    exact A5.le_normalizer_oTwoRes_of_le_normalizer
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_solvRad H))
  obtain ⟨c, hcX, hc3, -, hfpf, -, hdich⟩ := S.exists_c_13820a' hS hH hHX
  have hcH : c ∈ H := (S.plusData_X13820.le_L1.trans (le_sup_left.trans hH.1.1)) hcX
  intro x hx
  have hxH : x ∈ H := ((pCoreOf_le 2 _).trans hH.1.1) hx
  have h1 := S.comm_c_of_mem_R hS hH hcX hc3 hfpf hdich hx
  have h2 : x * c * x⁻¹ * c⁻¹ ∈ pCoreOf 2 H := by
    have h3 := (pCoreOf 2 H).inv_mem h1
    have e : (c * x * c⁻¹ * x⁻¹)⁻¹ = x * c * x⁻¹ * c⁻¹ := by group
    rwa [e] at h3
  exact S.not_transv_of_comm hS hH hcH hfpf hxH h2

end Setting4

end CFSG.Quasithin.H13.A6
