module

public import CFSG.Quasithin.H13.L32A53b

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx G T L V V₂ Y)
include C

theorem exists_rot_X : ∃ z a x : G, z ∈ fsuV1 T V ∧ z ≠ 1 ∧ a ∈ V₂ ∧ a ∉ fsuV1 T V ∧
    x ∈ xL L V₂ ∧ x ^ 3 = 1 ∧ x * z * x⁻¹ = a ∧ x * a * x⁻¹ = z * a := by
  have : IsMulCommutative ↥V := C.isMulCommutative_V
  have S := C.set14
  obtain ⟨z, w, b, hz, hz1, hw, hwV, hb, hbV⟩ := S.exists_basis
  have hzV₂ := S.hV2.1 hz
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hwV' : w ∈ V := S.hV2.2.1 hw
  obtain ⟨l, hlL, hl3, -, hlz, hlw⟩ := S.exists_rot hb hzV hwV' hz1
    (fun h => hwV (h ▸ one_mem _)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ hw))
    (fun h => hwV (h ▸ hz)) (fun h => hbV (by
      have := mul_mem hw (inv_mem hzV₂)
      rwa [h, mul_inv_cancel_right] at this))
  have hlN : l ∈ Subgroup.normalizer (V₂ : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    rcases S.mem_V2 hw hwV hv with h | h
    · rcases S.eq_of_mem_V1 hz hz1 h with rfl | rfl
      · rw [mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [hlz]
        exact hw
    · rcases S.eq_of_mem_V1 hz hz1 h with h' | h'
      · rw [eq_inv_of_mul_eq_one_right h',
          show l * w⁻¹ * l⁻¹ = (l * w * l⁻¹)⁻¹ by group, hlw]
        exact inv_mem (mul_mem hzV₂ hw)
      · rw [show v = w⁻¹ * z by rw [← h']; group,
          show l * (w⁻¹ * z) * l⁻¹ = (l * w * l⁻¹)⁻¹ * (l * z * l⁻¹) by group, hlw, hlz]
        exact mul_mem (inv_mem (mul_mem hzV₂ hw)) hw
  exact ⟨z, w, l, hz, hz1, hw, hwV, Subgroup.subset_closure ⟨⟨hlL, hlN⟩, 3, by decide, hl3⟩,
    hl3, hlz, hlw⟩

theorem le_centralizer_V1 : Y ≤ Subgroup.centralizer (fsuV1 T V : Set G) := by
  have : IsMulCommutative ↥V := C.isMulCommutative_V
  have S := C.set14
  rw [← L32A.normalizer_eq_centralizer_of_card_two S.card_V1]
  exact C.hYG1

theorem exists_comm_not_mem :
    ∃ x' ∈ xL L V₂ ⊔ T, Odd (orderOf x') ∧ ∃ y' ∈ Y ⊔ T, Odd (orderOf y') ∧
      ⁅x', y'⁆ ∉ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply C.not_le_normalizer
  have hXH : xL L V₂ ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hYH : Y ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hHW : hY T L V₂ Y ≤ Subgroup.normalizer (vH T L V V₂ Y : Set G) :=
    le_normalizer_conjClosure _ _
  have key : ∀ y' ∈ Y ⊔ T, Odd (orderOf y') →
      y' ∈ Subgroup.normalizer ((xL L V₂ ⊔ cH T L V V₂ Y : Subgroup G) : Set G) := by
    intro y' hy' hy'o
    have hy'H := hYH hy'
    have hle : xL L V₂ ⊔ cH T L V V₂ Y ≤
        (xL L V₂ ⊔ cH T L V V₂ Y).comap (MulAut.conj y').toMonoidHom := by
      refine sup_le ?_ ?_
      · calc xL L V₂ = oTwoUpper (xL L V₂ ⊔ T) := C.oTwoUpper_xT.symm
          _ ≤ _ := by
            refine (Subgroup.closure_le _).mpr fun x' hx' => ?_
            obtain ⟨hx'XT, hx'o⟩ := hx'
            have hx'X : x' ∈ xL L V₂ := by
              rw [← C.oTwoUpper_xT]
              exact Subgroup.subset_closure ⟨hx'XT, hx'o⟩
            have hc : ⁅y', x'⁆ ∈ cH T L V V₂ Y := by
              refine ⟨?_, ?_⟩
              · exact (hY T L V₂ Y).mul_mem ((hY T L V₂ Y).mul_mem ((hY T L V₂ Y).mul_mem
                  hy'H (hXH hx'XT)) ((hY T L V₂ Y).inv_mem hy'H))
                  ((hY T L V₂ Y).inv_mem (hXH hx'XT))
              · rw [← commutatorElement_inv]
                exact Subgroup.inv_mem _ (hcon x' hx'XT hx'o y' hy' hy'o)
            show y' * x' * y'⁻¹ ∈ xL L V₂ ⊔ cH T L V V₂ Y
            have e : y' * x' * y'⁻¹ = ⁅y', x'⁆ * x' := by
              rw [commutatorElement_def]
              group
            rw [e]
            exact mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hx'X)
      · intro c hc
        obtain ⟨hcH, hcC⟩ := hc
        show y' * c * y'⁻¹ ∈ xL L V₂ ⊔ cH T L V V₂ Y
        refine Subgroup.mem_sup_right ⟨(hY T L V₂ Y).mul_mem ((hY T L V₂ Y).mul_mem hy'H hcH)
          ((hY T L V₂ Y).inv_mem hy'H), ?_⟩
        have hN := B2F.normalizer_le_normalizer_centralizer (vH T L V V₂ Y) (hHW hy'H)
        exact (Subgroup.mem_normalizer_iff.mp hN c).mp hcC
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have := hle hn
    simpa [MulAut.conj_apply] using this
  calc Y = oTwoUpper (Y ⊔ T) := C.oTwoUpper_yT.symm
    _ ≤ _ := (Subgroup.closure_le _).mpr fun y' hy' => key y' hy'.1 hy'.2

end Ctx

end CFSG.Quasithin.H13.L32A.T53

end
