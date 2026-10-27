module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocLineG

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

namespace Ctx

variable {G : Type} [Group G]
  (C : Ctx G)

theorem Φ1_sY {q : Fin 45} (hq : q ∈ L0S) {e : Y} (he : e ∈ P2) (hee : e * xY * e⁻¹ = sY q) :
    C.Φ1 (sY q) = C.Φ2 e * C.z * (C.Φ2 e)⁻¹ := by
  rw [C.Φ1_eq_Φ2 (T_le_B0 (Vsub_le_T (sY_mem_Vsub hq))), ← hee, C.Φ2_conj he mem_P2_xY,
    C.z_eq]

theorem isPt_of_isConj {a : Y} (haP : a ∈ P1) (ha : IsConj xY a) {g x : G}
    (h : C.Φ1 a = g⁻¹ * x * g) : C.IsPt x := by
  obtain ⟨m, hm, q, hq, rfl⟩ := exists_P1_conj_of_transvection haP ha
  obtain ⟨e, heP, hee⟩ := exists_P2_conj_sY hq
  have hsq : sY q ∈ P1 := Vsub_le_P1 (sY_mem_Vsub hq)
  rw [C.Φ1_conj hm hsq, C.Φ1_sY hq heP hee] at h
  refine ⟨g * C.Φ1 m * C.Φ2 e, ?_⟩
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = g * (C.Φ1 m * (C.Φ2 e * C.z * (C.Φ2 e)⁻¹) * (C.Φ1 m)⁻¹) * g⁻¹ := by rw [← h]
    _ = _ := by group

variable [Finite G]

theorem isConj_of_isPt {a : Y} (haP : a ∈ P1) (ha2 : a * a = 1) (ha1 : a ≠ 1) {g u : G}
    (hu : C.IsPt u) (h : C.Φ1 a = g⁻¹ * u * g) : IsConj xY a := by
  by_contra hx
  obtain ⟨m, hm, hV⟩ := exists_P1_conj_of_involution haP ha2 ha1 hx
  have hvV : m⁻¹ * a * m ∈ Vsub := mem_Vconj.1 hV
  obtain ⟨k, hk⟩ := hu
  have hvP : m⁻¹ * a * m ∈ P1 := P1.mul_mem (P1.mul_mem (P1.inv_mem hm) haP) hm
  have h1 : C.Φ2 (m⁻¹ * a * m) = ((C.Φ1 m)⁻¹ * g⁻¹ * k) * C.z * ((C.Φ1 m)⁻¹ * g⁻¹ * k)⁻¹ := by
    rw [← C.Φ1_eq_Φ2 (T_le_B0 (Vsub_le_T hvV)), C.Φ1_mul (P1.mul_mem (P1.inv_mem hm) haP) hm,
      C.Φ1_mul (P1.inv_mem hm) haP, C.Φ1_inv hm, h, hk]
    group
  have hc := C.isConj_of_conj_z hvV h1
  apply hx
  have hconj : IsConj (m⁻¹ * a * m) a := isConj_iff.2 ⟨m, by group⟩
  exact hc.trans hconj

end Ctx

end CFSG.Quasithin.H13.F431.U42
