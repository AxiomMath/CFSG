module

public import CFSG.Quasithin.Background.SmithB57EI
public import CFSG.Quasithin.Background.SmithB57EH

public section

namespace CFSG.Quasithin

namespace SmithB57E

open CFSG.Open CFSG.QuasithinUnique FFC CFSG.Quasithin.S143 Equiv
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

namespace SixData

variable {G L A : Subgroup (MulAut V)} {S : Hyp G L} (D : SixData S A)
include D

theorem case4 : B56Case4 G := by
  obtain ⟨t, htA, htX⟩ := D.exists_t
  have htG : t ∈ G := D.hA.1 htA
  obtain ⟨hsup, hinf⟩ := isDirectSum_commV_fixV S.hV G
  have hG := D.eq_sup htA htX
  have hUW : commV L ≤ fixV (pCoreOf 3 G) := D.U_le_W
  have hsplit := D.split_W
  have hWM : fixV (pCoreOf 3 G) ⊓ fixV (L ⊔ A) ≤ fixV G := by
    intro v hv
    have hv2 : v ∈ fixV L ⊓ fixV A := by rw [← FFC.fixV_sup]; exact hv.2
    have hGv : v ∈ fixV ((L ⊔ pCoreOf 3 G) ⊔ Subgroup.zpowers t) := by
      rw [FFC.fixV_sup, FFC.fixV_sup]
      exact ⟨⟨hv2.1, hv.1⟩, mem_fixV_zpowers_iff.2 (hv2.2 t htA)⟩
    intro g hg
    have hg' : g ∈ (L ⊔ pCoreOf 3 G) ⊔ Subgroup.zpowers t := by rw [← hG]; exact hg
    exact hGv g hg'
  have hGX : fixV G ≤ fixV (pCoreOf 3 G) := B1.fixV_le_fixV (pCore3_le G)
  refine ⟨L, pCoreOf 3 G, t, hG, D.inf_X, fun a ha b hb => (S.commute_X b hb a ha).symm,
    ⟨equivAlternating (by norm_num) D.commutator_eq D.π⟩, D.card_X, ?_, ?_, ?_, ?_,
    by rw [D.card_Y]; norm_num, S.le_normalizer D.hP4 htG, le_normalizer_pCore3 G htG, ?_, ?_⟩
  · rw [eq_top_iff, ← hsup]
    refine sup_le (le_sup_right.trans le_sup_right) ?_
    rw [hsplit]
    exact sup_le (le_sup_left.trans le_sup_right) (hWM.trans le_sup_left)
  · refine le_antisymm ?_ ?_
    · rintro v ⟨hvG, hv⟩
      obtain ⟨u, hu, y, hy, rfl⟩ := Subgroup.mem_sup.1 hv
      have hyW : y ∈ fixV (pCoreOf 3 G) := by
        intro x hx
        have h1 := hGX hvG x hx
        rw [map_mul, hUW hu x hx] at h1
        exact mul_left_cancel h1
      have hy1 : y = 1 := by
        have : y ∈ commV (pCoreOf 3 G) ⊓ fixV (pCoreOf 3 G) := ⟨hy, hyW⟩
        rw [hinf, Subgroup.mem_bot] at this
        exact this
      rw [hy1, mul_one] at hvG ⊢
      exact ⟨B1.fixV_le_fixV S.hLG hvG, hu⟩
    · intro v hv
      exact ⟨fun g hg => D.fix_C hg hv, (le_sup_left : commV L ≤ _) hv.2⟩
  · refine ⟨rfl, eq_bot_iff.2 fun v hv => ?_⟩
    have : v ∈ commV (pCoreOf 3 G) ⊓ fixV (pCoreOf 3 G) := ⟨hv.2, hUW hv.1⟩
    rwa [hinf] at this
  · have h1 := D.card_U
    have h2 := D.card_C_le
    have h3 : 0 < Nat.card ↥(fixV L ⊓ commV L) := Nat.card_pos
    rcases (by omega : Nat.card ↥(fixV L ⊓ commV L) = 1 ∨ Nat.card ↥(fixV L ⊓ commV L) = 2)
      with h | h
    · left
      rw [h1, h]
      norm_num
    · right
      rw [h1, h]
      norm_num
  · rintro ⟨g, hg, hgx⟩
    have hsM : g⁻¹ * t ∈ L ⊔ A :=
      Subgroup.mul_mem _ ((le_sup_left : L ≤ L ⊔ A) (L.inv_mem hg))
        ((le_sup_right : A ≤ L ⊔ A) htA)
    obtain ⟨σ, hσ⟩ := D.f_surj hsM
    have hσ1 : σ = 1 := by
      refine center_alt6 σ fun τ hτ => D.f_injective ?_
      rw [D.f_mul, D.f_mul, hσ]
      have hl : D.f τ ∈ L := (D.mem_L_iff τ).2 hτ
      have h := hgx _ hl
      calc g⁻¹ * t * D.f τ = g⁻¹ * (t * D.f τ * t⁻¹) * t := by group
        _ = g⁻¹ * (g * D.f τ * g⁻¹) * t := by rw [h]
        _ = D.f τ * (g⁻¹ * t) := by group
    rw [hσ1, D.f_one] at hσ
    have htg : t = g := by
      calc t = g * (g⁻¹ * t) := by group
        _ = g := by rw [← hσ, mul_one]
    exact S.not_mem_of_not_mem_centralizer htX (htg ▸ hg)
  · rintro ⟨g, hg, hgx⟩
    apply htX
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hgx x hx
    rw [D.commute_X htA htX g hg x hx, mul_inv_cancel_right] at h
    calc x * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group

end SixData

namespace Hyp

variable {G L : Subgroup (MulAut V)} (S : Hyp G L)
include S

theorem case4 (hP4 : AsB15Part4) (hA21 : AsA21SQTKSection) (hB51 : AsB51) : B56Case4 G := by
  obtain ⟨A, hA, hAX⟩ := S.exists_offender
  obtain ⟨hI, hcase⟩ := S.case1i hP4 hA21 hB51 hA (S.not_le_of_not_le_centralizer hAX)
  rcases hcase with ⟨n, hn5, hn8, hS⟩ | hG
  · obtain ⟨π, hπ, halt⟩ := S.sym_data hP4 hA hn5 hS
    interval_cases n
    · exact (S.false_of_five hP4 hA π).elim
    · exact SixData.case4 (S := S) ⟨hP4, hA21, hB51, hA, hAX, hI, π, hπ, halt⟩
    · exact (S.false_of_seven hP4 hA21 hB51 hA hAX hI hS).elim
    · exact (S.false_of_eight hA hAX π halt).elim
  · exact (S.false_of_g2 hP4 hA21 hB51 hA hAX hI hG).elim

end Hyp

end SmithB57E

namespace FFC

theorem b57Exc_of (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection) : B57Exc := by
  intro V _ _ G hc L hL h3 hlayer hO3
  exact SmithB57E.Hyp.case4 ⟨hc, hL, h3, hlayer, hO3⟩ hP4 hA21 hB51

end FFC

end CFSG.Quasithin
