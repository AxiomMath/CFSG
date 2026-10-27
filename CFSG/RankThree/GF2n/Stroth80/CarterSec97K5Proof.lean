module

public import CFSG.RankThree.GF2n.Stroth80.Sec97FiveDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X Y : Subgroup G} {hc : Ctx M Q Z B} {t nn r g : G}

namespace HS9

theorem pointT_inf_V_le (h13 : Sec97K13 hc t X Y r nn g) :
    pointT hc X Y nn g ⊓ Vt M (LB M Q B) B Z t ≤ Z := by
  intro x hx
  obtain ⟨hxT, hxV⟩ := Subgroup.mem_inf.mp hx
  have hxP : x ∈ planeST M Q Z B X nn g := (Subgroup.mem_inf.mp hxT).1
  have hPle : planeST M Q Z B X nn g ≤ Vt M (LB M Q B) B Z nn := by
    rw [← h13.sup_eq]
    exact le_sup_right
  have hxVn : x ∈ Vt M (LB M Q B) B Z nn := hPle hxP
  have hxU : x ∈ Uline Z (conjSubgroup r B) Y := by
    rw [← h13.inf_eq]
    exact ⟨hxV, hxVn⟩
  have hxZ : x ∈ Z := by
    rw [← h13.inf_Z]
    exact ⟨hxU, hxP⟩
  exact hxZ

theorem pointT_not_le_Z (h13 : Sec97K13 hc t X Y r nn g)
    (hBne : B ≠ Z) :
    ¬ pointT hc X Y nn g ≤ Z := by
  intro hle
  obtain ⟨m, hmM, hpoint⟩ := h13.point
  have hA : conjSubgroup m B ≤ Z := by
    have hAZ : conjSubgroup m B ⊔ Z ≤ Z := by
      rw [← hpoint]
      exact hle
    exact le_sup_left.trans hAZ
  have hBZ : B ≤ Z := by
    intro b hb
    have hbA : m * b * m⁻¹ ∈ conjSubgroup m B := by
      rw [mem_conjSubgroup]
      have e : m⁻¹ * (m * b * m⁻¹) * m = b := by group
      rwa [e]
    have hbZ : m * b * m⁻¹ ∈ Z := hA hbA
    have hnorm := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem hmM))
      (m * b * m⁻¹)).mp hbZ
    have e : m⁻¹ * (m * b * m⁻¹) * m⁻¹⁻¹ = b := by group
    rwa [e] at hnorm
  have hcard : Nat.card Z ≤ Nat.card B := by
    obtain ⟨a, ha⟩ := hc.conj
    rw [ha, card_conjSubgroup]
  exact hBne (Subgroup.eq_of_le_of_card_ge hBZ hcard)

end HS9

end CFSG.RankThree.GF2n.Stroth80
