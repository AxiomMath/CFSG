module

public import CFSG.Quasithin.H13.L32A767a
public import CFSG.Quasithin.H13.L32A769b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {x x' y : G}

namespace Sym69

variable (S : Sym69 G T L V x x' y)
include S

theorem cent_W : conjSub x (fsuU T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) =
    conjSub y (V ⊔ u0 T V) := by
  rw [← S.c'.cent.1, conjSub_inf, ← conjSub_centralizer y (conjSub x' (fsuU T V)), S.hU, S.hW]

theorem inf_V1_eq_bot (hV1 : ¬ fsuV1 T V ≤ conjSub x (fsuU T V)) :
    (fsuU T V ⊓ conjSub x (fsuU T V)) ⊓ fsuV1 T V = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  by_contra hv1
  apply hV1
  have hne : fsuV1 T V ⊓ conjSub x (fsuU T V) ≠ ⊥ := by
    intro hb
    have : v ∈ fsuV1 T V ⊓ conjSub x (fsuU T V) := ⟨hv.2, hv.1.2⟩
    rw [hb, Subgroup.mem_bot] at this
    exact hv1 this
  exact le_of_card_eq_two_of_inf_ne_bot S.c.hF.card_V₁ hne

theorem false_of_u0_eq (hV1 : ¬ fsuV1 T V ≤ conjSub x (fsuU T V))
    (hu0 : u0 T V = fsuV1 T V) : False := by
  have C := S.c
  obtain ⟨-, -, hF1⟩ := C.cent
  have hV1V : fsuV1 T V ≤ V := inf_le_left
  have hFV : (fsuU T V ⊓ conjSub x (fsuU T V)) ⊔ fsuV1 T V = V := by
    rw [hF1, hu0, sup_eq_left.mpr hV1V]
  have hFle : fsuU T V ⊓ conjSub x (fsuU T V) ≤ V :=
    le_sup_left.trans (le_of_eq hFV)
  have hF4 : Nat.card ↥(fsuU T V ⊓ conjSub x (fsuU T V)) = 4 := by
    obtain ⟨-, hV8, -, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
    have hUN : fsuU T V ≤ Subgroup.normalizer (fsuV1 T V : Set G) := by
      rw [fsuU_eq_conjClosure_hz C.hMod C.hyp]
      exact C.hF.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 _).trans C.hF.H_normalizes_V₁)
    have hN : fsuU T V ⊓ conjSub x (fsuU T V) ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
      inf_le_left.trans hUN
    have h1 := L32NSet14.card_sup_mul_card_inf hN
    rw [hFV, S.inf_V1_eq_bot hV1, Subgroup.card_bot, hV8, C.hF.card_V₁] at h1
    omega
  have hFW : fsuU T V ⊓ conjSub x (fsuU T V) ≤ conjSub y V := by
    have h1 : fsuU T V ⊓ conjSub x (fsuU T V) ≤
        conjSub x (fsuU T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) := by
      refine le_inf inf_le_right fun f hf => Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      exact F7.isElemAbelian_comm (isElemAbelian_fsuU_of C.hyp C.hMod) hu hf.1
    rw [S.cent_W, hu0, sup_eq_left.mpr hV1V] at h1
    exact h1
  have hVy := conjSub_V_eq C.hyp C.h1222 C.h1332 C.h1334 C.h63 C.hF hFle hF4 hFW
  apply hV1
  have h2 := S.cent_W
  rw [hu0, sup_eq_left.mpr hV1V, hVy] at h2
  have h3 : V ≤ conjSub x (fsuU T V) := (le_of_eq h2.symm).trans inf_le_left
  exact hV1V.trans h3

end Sym69

end CFSG.Quasithin.H13.L32A
