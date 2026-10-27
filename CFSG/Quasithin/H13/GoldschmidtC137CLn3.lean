module

public import CFSG.Quasithin.EmptyFaithful.S1417Setup
public import CFSG.Quasithin.H13.GoldschmidtC137CBase
public import CFSG.Quasithin.H13.GoldschmidtC137CDict
public import CFSG.Quasithin.H13.GoldschmidtC137Pt2Aux
public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin4
public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin6
public import CFSG.Quasithin.H13.GoldschmidtC137S6Std

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace C137Base

variable [Finite G] {X T V L P : Subgroup G} (h : C137Base X T V L P)
include h

theorem P_le_normalizer_line :
    P ≤ normalizer (((fixV (autI h.hVe (pCoreOf 2 P))).map (S1417.inclMod h.hVe) : Subgroup G) :
      Set G) := by
  have hnorm := autI_le_normalizer_autI_gc h.hVe
    (A := P) (B := pCoreOf 2 P) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
  have key : ∀ p ∈ P, ∀ x ∈ ((fixV (autI h.hVe (pCoreOf 2 P))).map (S1417.inclMod h.hVe) : Subgroup G),
      p * x * p⁻¹ ∈ ((fixV (autI h.hVe (pCoreOf 2 P))).map (S1417.inclMod h.hVe) : Subgroup G) := by
    intro p hp x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hpN : p ∈ normalizer (V : Set G) := h.hXN (h.hPX.le hp)
    have hφ : convI h.hVe ⟨p, hpN⟩ ∈ autI h.hVe P := convI_mem_autI h.hVe hp hpN
    refine ⟨convI h.hVe ⟨p, hpN⟩ u, ?_, ?_⟩
    · intro y hy
      have h1 : (convI h.hVe ⟨p, hpN⟩)⁻¹ * y * convI h.hVe ⟨p, hpN⟩ ∈
          autI h.hVe (pCoreOf 2 P) := by
        have := (Subgroup.mem_normalizer_iff.1 (hnorm ((autI h.hVe P).inv_mem hφ)) y).1 hy
        simpa using this
      have h2 := congrArg (fun z => convI h.hVe ⟨p, hpN⟩ z) (hu _ h1)
      simpa [MulAut.mul_apply] using h2
    · exact (convI_apply_val h.hVe ⟨p, hpN⟩ u).symm
  intro p hp
  exact B6.mem_normalizer_of_forall_mem (fun x hx => key p hp x hx)
    (fun x hx => by simpa using key p⁻¹ (P.inv_mem hp) x hx)

theorem V_inf_centralizer_L :
    V ⊓ centralizer (L : Set G) = (fixV (autI h.hVe L)).map (S1417.inclMod h.hVe) := by
  ext v
  constructor
  · rintro ⟨hvV, hvC⟩
    refine ⟨IntMod.mk h.hVe ⟨v, hvV⟩, ?_, rfl⟩
    intro φ hφ
    obtain ⟨g, hgL, rfl⟩ := (mem_autI h.hVe).1 hφ
    refine IntMod.val_injective ?_
    rw [convI_apply_val]
    have := Subgroup.mem_centralizer_iff.1 hvC g hgL
    show (g : G) * v * (g : G)⁻¹ = v
    rw [this, mul_inv_cancel_right]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.val_mem, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have hgN : g ∈ normalizer (V : Set G) := h.hXN (h.hLX hg)
    have h1 := congrArg IntMod.val (hu (convI h.hVe ⟨g, hgN⟩) (convI_mem_autI h.hVe hg hgN))
    rw [convI_apply_val] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1


end C137Base

namespace C137FrameB

variable [Finite G] {X T V L P : Subgroup G} {h : C137Base X T V L P} (F : C137FrameB h)

include F in
theorem card_fixV_autI_L : Nat.card (fixV (autI h.hVe L)) = cK F.k := by
  rw [← F.hA, F.card_fixV_ρ, fixV_A6, Subgroup.card_bot, mul_one]

include F in
theorem fixV_autI_X_eq_L : fixV (autI h.hVe X) = fixV (autI h.hVe L) := by
  have hle : fixV (autI h.hVe X) ≤ fixV (autI h.hVe L) :=
    B1.fixV_le_fixV (autI_mono h.hVe h.hLX)
  have hc : Nat.card (fixV (autI h.hVe L)) ≤ Nat.card (fixV (autI h.hVe X)) := by
    rw [F.card_fixV_autI_L, ← F.hX, F.card_fixV_ρ]
    have : fixV ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 Mod.ut0)) = ⊥ := by
      rw [eq_bot_iff, ← fixV_A6]
      exact B1.fixV_le_fixV (Subgroup.map_mono le_top)
    rw [this, Subgroup.card_bot, mul_one]
  exact Subgroup.eq_of_le_of_card_ge hle hc

theorem card_fixV_R2 : Nat.card (fixV (R2.map (Mod.act 6 Mod.ut0))) = 4 := by
  have h := card_mul_two_pow_rkIdx (W := Mod.V 6 Mod.ut0) (n := 4) (by rw [card_V6]; norm_num)
    (fixV (R2.map (Mod.act 6 Mod.ut0)))
  rw [rank_R2.2] at h
  omega


end C137FrameB

end CFSG.Quasithin.H13.U3.GC137
