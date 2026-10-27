module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Zc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Alpha

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open S18 (tilOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s16t_l4_card_barSub_dvd {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil V₀ V) {B : Subgroup G} (hB : B ≤ D.M) :
    Nat.card ↥(barSub V₀ V hV B) ∣ Nat.card ↥B := by
  obtain ⟨φ, hφs, -⟩ := s16t_l4_exists_hom_barSub (hV := hV) hM hB
  exact Subgroup.card_dvd_of_surjective hφs

theorem s16t_l4_isPGroup_of_barSub (hM : D.M ≤ stabTil V₀ V) {Y : Subgroup G}
    (hY : S16tL4Pack D V₀ V L hV Y) {B : Subgroup G} (hBY : B ≤ Y)
    (hB : IsPGroup 2 ↥(barSub V₀ V hV B)) : IsPGroup 2 ↥B := by
  obtain ⟨φ, -, hφk⟩ := s16t_l4_exists_hom_barSub (hV := hV) hM (hBY.trans hY.le)
  have hk2 : IsPGroup 2 ↥φ.ker := by
    rw [hφk]
    refine IsPGroup.of_equiv (G := ↥(B ⊓ F11.CTilde D.M V₀ V)) ?_
      (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
    exact IsPGroup.to_le (s16t_l4_inf_cTilde_isPGroup hY) (inf_le_inf hBY le_rfl)
  have h1 : IsPGroup 2 ↥(⊤ : Subgroup ↥(barSub V₀ V hV B)) := hB.of_equiv Subgroup.topEquiv.symm
  have h2 := IsPGroup.comap_of_ker_isPGroup h1 φ hk2
  rw [Subgroup.comap_top] at h2
  exact h2.of_equiv Subgroup.topEquiv

theorem s16t_l4_normalized_three_prime (hS : S16tL4Setting D V₀ V L hV) {Y : Subgroup G}
    (hY : S16tL4Pack D V₀ V L hV Y) {w : G} (hw : w ∈ V)
    (hpt : Close16PtStab (lBar V₀ V hV L) (tilOf V₀ V hV w hw)) {B : Subgroup G}
    (hBY : B ≤ Y) (h3 : ¬ 3 ∣ Nat.card ↥B)
    (hXB : Opp 3 (Y ⊓ centralizer ({w} : Set G)) ≤ normalizer (B : Set G)) :
    IsPGroup 2 ↥B := by
  have hM := s16t_l4_le_stabTil hS
  have hZM : Y ⊓ centralizer ({w} : Set G) ≤ D.M := inf_le_left.trans hY.le
  have hBs : B ≤ stabTil V₀ V := hBY.trans (hY.le.trans hM)
  have hX : barSub V₀ V hV (Opp 3 (Y ⊓ centralizer ({w} : Set G))) =
      lBar V₀ V hV L ⊓ MulAction.stabilizer (MulAut (Vtil V₀ V hV))
        (tilOf V₀ V hV w hw) := by
    rw [close16_barSub_opp (hZM.trans hM), s16t_l4_barSub_cent_eq hS hY hw hpt, hpt.opp]
  have hnorm : lBar V₀ V hV L ⊓ MulAction.stabilizer (MulAut (Vtil V₀ V hV))
        (tilOf V₀ V hV w hw) ≤
      normalizer ((barSub V₀ V hV B : Subgroup (MulAut (Vtil V₀ V hV))) :
        Set (MulAut (Vtil V₀ V hV))) := by
    rw [← hX]
    exact close16_barSub_le_normalizer hBs hXB
  have hBL : barSub V₀ V hV B ≤ lBar V₀ V hV L :=
    (barSub_mono V₀ V hV hBY).trans hY.bar_eq.le
  have h3' : ¬ 3 ∣ Nat.card ↥(barSub V₀ V hV B) := fun h =>
    h3 (h.trans (s16t_l4_card_barSub_dvd hM (hBY.trans hY.le)))
  exact s16t_l4_isPGroup_of_barSub hM hY hBY
    (close16_threePrime_normalized hpt (s16t_l4_lbar_simple hS) hBL h3' hnorm)

theorem s16t_l4_alpha (hS : S16tL4Setting D V₀ V L hV) {Y : Subgroup G}
    (hY : S16tL4Pack D V₀ V L hV Y) {w : G} (hw : w ∈ V)
    (hpt : Close16PtStab (lBar V₀ V hV L) (tilOf V₀ V hV w hw)) :
    ∀ A ∈ F09.Inv9' D.M (Opp 3 (Y ⊓ centralizer ({w} : Set G))) 3,
      ⁅A, Opp 3 (Y ⊓ centralizer ({w} : Set G))⁆ ≤ pCoreOf 2 A := by
  intro A hA
  obtain ⟨hAM, h3, hXA⟩ := hA
  have hXY : Opp 3 (Y ⊓ centralizer ({w} : Set G)) ≤ Y :=
    (close16_opp_le 3 _).trans inf_le_left
  have hcomm : ⁅A, Opp 3 (Y ⊓ centralizer ({w} : Set G))⁆ ≤ A ⊓ Y := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    have hxY : x ∈ Y := hXY hx
    have hxA : x * a⁻¹ * x⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.1 (hXA hx) a⁻¹).1 (A.inv_mem ha)
    have hax : a * x * a⁻¹ ∈ Y :=
      hY.normal.conj_mem ⟨x, hY.le hxY⟩ hxY ⟨a, hAM ha⟩
    refine ⟨?_, ?_⟩
    · have : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by group
      rw [this]
      exact A.mul_mem ha hxA
    · have : ⁅a, x⁆ = (a * x * a⁻¹) * x⁻¹ := by group
      rw [this]
      exact Y.mul_mem hax (Y.inv_mem hxY)
  have hXB : Opp 3 (Y ⊓ centralizer ({w} : Set G)) ≤ normalizer ((A ⊓ Y : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (hXA hx) y
    have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer (hXY hx)) y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
  have h3B : ¬ 3 ∣ Nat.card ↥(A ⊓ Y) := fun h =>
    h3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have h2 := s16t_l4_normalized_three_prime hS hY hw hpt inf_le_right h3B hXB
  exact hcomm.trans (close16_inf_le_pCoreOf hAM hY.normal h2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
