module

public import CFSG.Quasithin.Background.FFC1NonsplitOff
public import CFSG.Quasithin.Background.SmithB51Sp4Bound
public import CFSG.Quasithin.Background.SmithB51Sp4Sec

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.H

namespace Sp4Off

variable {V : Type} [CommGroup V] {W U : Subgroup V}

theorem autSec_le_normalizer {L M : Subgroup (MulAut V)} (hLM : L ≤ M) (hMW : M ≤ stabSub W)
    (hMU : M ≤ stabSub U) (hn : ∀ g ∈ M, ∀ l ∈ L, g * l * g⁻¹ ∈ L) :
    autSec M W U ≤ Subgroup.normalizer (autSec L W U : Set (MulAut (Sec W U))) := by
  have hconj : ∀ g : ↥M, ∀ y ∈ autSec L W U,
      B5.secHom M hMW hMU g * y * (B5.secHom M hMW hMU g)⁻¹ ∈ autSec L W U := by
    intro g y hy
    rw [← B5.map_secHom_eq_autSec M hMW hMU hLM] at hy ⊢
    obtain ⟨l, hl, rfl⟩ := hy
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl
    refine ⟨g * l * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    simpa using hn g g.2 l hl
  intro x hx
  rw [← B5.range_secHom M hMW hMU] at hx
  obtain ⟨g, rfl⟩ := hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hconj g y
  · intro hy
    have := hconj g⁻¹ _ hy
    simpa [mul_assoc] using this

end Sp4Off

theorem asB51NonsplitOffSp4_holds : AsB51NonsplitOffSp4 := by
  intro V _ _ hV G L T hHyp hU hT _ n hn hnat A hA
  obtain ⟨hUC, -, hGU, hGC, hfL, hfM⟩ := B5.secConfig hV hHyp hU hT (C := fixV L ⊓ commV L) rfl
  set W := commV L with hWdef
  set C := fixV L ⊓ commV L with hCdef
  have hLG := B5.le_G hHyp
  have hnL := B5.normal_L hHyp
  have hMG : L ⊔ T ≤ G := sup_le hLG hT.1
  have hMW : L ⊔ T ≤ stabSub W := hMG.trans hGU
  have hMC : L ⊔ T ≤ stabSub C := hMG.trans hGC
  have hLW : L ≤ stabSub W := hLG.trans hGU
  have hLC : L ≤ stabSub C := hLG.trans hGC
  have hAM : A ≤ L ⊔ T := hA.1.trans le_sup_right
  have hAW : A ≤ stabSub W := hAM.trans hMW
  have hAC : A ≤ stabSub C := hAM.trans hMC
  by_contra hAL
  obtain ⟨K, _, _, hK, π, hπ⟩ := hnat
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ n) hK
  have hπ' := Sp4Off.realizesVia_autSec hLW hLC hfL hπ
  obtain ⟨e, he⟩ := exists_mulEquiv_of_realizesVia (StatedSp 2 K) hπ'
  have hLe : (autSec L W C).map (congrHom e) = natImage (StatedSp 2 K) :=
    map_congrHom_eq_natImage (StatedSp 2 K) hπ'.1 e he
  have hMe : (autSec (L ⊔ T) W C).map (congrHom e) ≤ natNorm (StatedSp 2 K) := by
    have h1 : (Subgroup.normalizer (autSec L W C : Set (MulAut (Sec W C)))).map (congrHom e) =
        Subgroup.normalizer (((autSec L W C).map (congrHom e) :
          Subgroup (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))) :
            Set (MulAut (StdMod (Fin 2 ⊕ Fin 2) K))) :=
      Subgroup.map_equiv_normalizer_eq (autSec L W C) (MulAut.congr e)
    rw [natNorm, ← hLe, ← h1]
    exact Subgroup.map_mono (Sp4Off.autSec_le_normalizer le_sup_left hMW hMC
      fun g hg l hl => hnL g (hMG hg) l hl)
  set E := (autSec A W C).map (congrHom e) with hE
  have hEN : E ≤ natNorm (StatedSp 2 K) :=
    (Subgroup.map_mono (autSec_mono hAM W C)).trans hMe
  have hEel : IsElemAbelian2 E :=
    (isElemAbelian2_map_congrHom e).mpr (isElemAbelian2_autSec W C hA.2.2.1)
  have hEnot : ¬ E ≤ natImage (StatedSp 2 K) := by
    intro h
    rw [← hLe, map_congrHom_le_iff] at h
    exact hAL (B5.le_of_autSec_le hMW hMC hfM le_sup_left hAM h)
  have hlt := Sp4Off.card_mul_card_fixV_lt (by omega) hK hEN hEel hEnot
  have hAfaith : A ⊓ centSec W C = ⊥ := by
    rw [eq_bot_iff, ← hfM]
    exact inf_le_inf_right _ hAM
  have hAcard : Nat.card (autSec A W C) = Nat.card A := by
    have := card_autSec_mul hAW hAC
    rwa [hAfaith, Subgroup.card_bot, mul_one] at this
  have hEcard : Nat.card E = Nat.card A := by rw [card_map_congrHom, hAcard]
  have hEfix : Nat.card (fixV E) = Nat.card (fixV (autSec A W C)) := by
    rw [fixV_map_congrHom]
    exact Subgroup.card_map_of_injective e.injective
  have hS : Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) = Nat.card (Sec W C) :=
    (Nat.card_congr e.toEquiv).symm
  have hU0 : Nat.card W ≤ Nat.card A * Nat.card ↥(fixV A ⊓ W) := by
    have := hA.2.2.2 ⊥ bot_le
    rwa [Subgroup.card_bot, one_mul, B1.fixV_bot, top_inf_eq] at this
  have hsec := card_sec_mul (V := V) hUC
  have hfixle := card_inf_fixV_le_autSec (A := A) hUC hAW
  have hCle : Nat.card ↥(C ⊓ fixV A) ≤ Nat.card C := Subgroup.card_le_of_le inf_le_left
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hFF : Nat.card (Sec W C) ≤ Nat.card A * Nat.card (fixV (autSec A W C)) := by
    have h1 : Nat.card (Sec W C) * Nat.card C ≤
        (Nat.card A * Nat.card (fixV (autSec A W C))) * Nat.card C := by
      rw [hsec]
      calc Nat.card W ≤ Nat.card A * Nat.card ↥(fixV A ⊓ W) := hU0
        _ = Nat.card A * Nat.card ↥(W ⊓ fixV A) := by rw [inf_comm]
        _ ≤ Nat.card A * (Nat.card (fixV (autSec A W C)) * Nat.card ↥(C ⊓ fixV A)) :=
          Nat.mul_le_mul_left _ hfixle
        _ ≤ Nat.card A * (Nat.card (fixV (autSec A W C)) * Nat.card C) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hCle)
        _ = (Nat.card A * Nat.card (fixV (autSec A W C))) * Nat.card C := by ring
    exact Nat.le_of_mul_le_mul_right h1 hCpos
  rw [hEcard, hEfix, hS] at hlt
  exact absurd hFF (not_le.mpr hlt)

end FFC

end CFSG.Quasithin
