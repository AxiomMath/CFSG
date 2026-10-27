module

public import CFSG.Quasithin.H13.GoldschmidtC137H6InvAct
public import CFSG.Quasithin.H13.GoldschmidtC137H6Str3

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem concl_of_c124_b [Finite G] (hC124 : C124StatementSQTK (G := G)) {X T V L P : Subgroup G}
    (h : H6Ctx X T V L P) (hRL : pCoreOf 2 P ≤ L ⊔ (X ⊓ centralizer (V : Set G))) :
    Concl X T V L P := by
  have hcl := hC124 X T V L (pCoreOf 2 P) 6 h.hX h.hSQ h.hred h.hT h.hprod h.hL h.hL2 h.hVL
    h.isAltQuotient h.hQR h.hRT (Or.inr (Or.inr (Or.inl ⟨rfl, hRL⟩)))
  rcases hcl with ⟨C, hC1, hC2, hC3, hC4⟩ | hchi | ⟨-, hA7 | hA6 | hH⟩
  · exact Or.inl ⟨C, hC2, hC1, hC3, hC4⟩
  · exact (not_isChiBlock_of_card hchi (Or.inr (card_of_hatA6 h.hhat))).elim
  · exact (not_isExcA7Block_of_card hA7 (Or.inr (card_of_hatA6 h.hhat))).elim
  · have h1 := card_of_isAltBlockType hA6
    rw [card_of_hatA6 h.hhat] at h1
    omega
  · exact Or.inr (Or.inl (blockPart_of_hatA6 h.hhat (isHatA6Block_of hH)))

theorem concl_caseI [Finite G] (hC124 : C124StatementSQTK (G := G)) {X T V L P : Subgroup G}
    (h : H6Ctx X T V L P) (hDP : A6.o2Z L ≤ P) : Concl X T V L P := by
  obtain ⟨F⟩ := h.nonempty_frame
  obtain ⟨g₀, hg₀X, hN₀, hg₀, w, hw, hwn, hsw⟩ := F.exists_inv_witness
  refine concl_of_c124_b hC124 h ?_
  intro r hr
  by_contra hrn
  have hrP : r ∈ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P hr
  have hrX : r ∈ X := h.hPX.le hrP
  have h1 := F.inv_action hg₀X hN₀ hg₀ hw hsw hrX hrn
  have hwP : w ∈ P := hDP hw
  have hOK : pCoreOf 2 L ≤ pCoreOf 2 P := h.toBaum.hOL_le_Q.trans h.hQR
  have hRn := Subgroup.mem_normalizer_iff.1
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hwP) r⁻¹
  have hR1 : w * r⁻¹ * w⁻¹ ∈ pCoreOf 2 P := (hRn).1 ((pCoreOf 2 P).inv_mem hr)
  have hR2 : r * w * r⁻¹ * w⁻¹ ∈ pCoreOf 2 P := by
    have : r * w * r⁻¹ * w⁻¹ = r * (w * r⁻¹ * w⁻¹) := by group
    rw [this]
    exact (pCoreOf 2 P).mul_mem hr hR1
  have hw2 : w ^ 2 ∈ pCoreOf 2 P := by
    have : w ^ 2 = (r * w * r⁻¹ * w⁻¹)⁻¹ * (r * w * r⁻¹ * w) := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [this]
    exact (pCoreOf 2 P).mul_mem ((pCoreOf 2 P).inv_mem hR2) (hOK h1)
  have hw3 : w ^ 3 ∈ pCoreOf 2 P := hOK (h.pow_three_mem hw)
  have hwR : w ∈ pCoreOf 2 P := by
    have : w = w ^ 3 * (w ^ 2)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [this]
    exact (pCoreOf 2 P).mul_mem hw3 ((pCoreOf 2 P).inv_mem hw2)
  obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) ⟨w, hwR⟩
  exact hwn (h.mem_pCoreOf_of_two_power hw (by simpa using congrArg Subtype.val hj))

end CFSG.Quasithin.H13.U3.GC137
