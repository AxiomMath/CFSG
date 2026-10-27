module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotSwapBLiftLift

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (oddCoreLift HasBLift SwapComponentData)

section Decomposition

variable {H : Type} [Group H] [Finite H]

theorem swapLift_decomposition_of_hasBLift {t : H}
    {Kb Db : Subgroup (H ⧸ oddCore H)}
    (h : SwapComponentData (QuotientGroup.mk' (oddCore H) t) Kb Db)
    (hOut : Group.IsSolvable (Outer Kb)) (hBK : HasBLift Kb)
    (hBsup : HasBLift (Kb ⊔ Kb.map (MulAut.conj (QuotientGroup.mk' (oddCore H) t)).toMonoidHom)) :
    (oddCoreLift Kb).map (MulAut.conj t).toMonoidHom ≤ centralizer (oddCoreLift Kb : Set H) ∧
      oddCoreLift Kb ⊓ (oddCoreLift Kb).map (MulAut.conj t).toMonoidHom ≤ oddCore H ∧
      oddCoreLift Kb ⊔ (oddCoreLift Kb).map (MulAut.conj t).toMonoidHom =
        perfectCore (⊤ : Subgroup H) ∧
      ⁅oddCoreLift Kb, oddCoreLift Kb⁆ = oddCoreLift Kb ∧
      (oddCoreLift Kb).map (QuotientGroup.mk' (oddCore H)) = Kb := by
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set τ := π t with hτ
  set Kh := oddCoreLift Kb with hKh
  have hO := F4Pilot.oddCore_quotient_oddCore_eq_bot_of_finite (H := H)
  have hKp : ⁅Kb, Kb⁆ = Kb := isPerfect_iff.mp h.isComponent.1.1
  have hKτp : ⁅Kb.map (MulAut.conj τ).toMonoidHom, Kb.map (MulAut.conj τ).toMonoidHom⁆ =
      Kb.map (MulAut.conj τ).toMonoidHom := by
    rw [← map_commutator, hKp]
  have hKt : Kh.map (MulAut.conj t).toMonoidHom =
      oddCoreLift (Kb.map (MulAut.conj τ).toMonoidHom) :=
    F4Pilot.map_conj_oddCoreLift Kb t
  have hKhp : ⁅Kh, Kh⁆ = Kh := F4Pilot.commutator_oddCoreLift Kb
  have hπK : Kh.map π = Kb := F4Pilot.map_oddCoreLift hKp
  have hπKt : (Kh.map (MulAut.conj t).toMonoidHom).map π = Kb.map (MulAut.conj τ).toMonoidHom := by
    rw [hKt]
    exact F4Pilot.map_oddCoreLift hKτp
  have hOK : oddCore H ≤ centralizer (Kh : Set H) := le_centralizer_iff.1 hBK
  have hcomm : ⁅Kh, Kh.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
    apply CFSG.LocalCores.perfect_double_commutator (isPerfect_iff.mpr hKhp)
    have h1 : ⁅Kh, Kh.map (MulAut.conj t).toMonoidHom⁆ ≤ oddCore H := by
      have h2 : (⁅Kh, Kh.map (MulAut.conj t).toMonoidHom⁆).map π = ⊥ := by
        rw [map_commutator, hπK, hπKt]
        exact h.commute
      have h3 := (Subgroup.map_eq_bot_iff _).1 h2
      rwa [hπ, QuotientGroup.ker_mk'] at h3
    exact commutator_eq_bot_iff_le_centralizer.2 (h1.trans hOK)
  have hdisj : Kh ⊓ Kh.map (MulAut.conj t).toMonoidHom ≤ oddCore H := by
    rintro x ⟨hx, hxt⟩
    have h1 : π x ∈ Kb ⊓ Kb.map (MulAut.conj τ).toMonoidHom :=
      ⟨hπK ▸ mem_map_of_mem π hx, hπKt ▸ mem_map_of_mem π hxt⟩
    rw [h.inf_eq_bot hO, mem_bot] at h1
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hKhtp : ⁅Kh.map (MulAut.conj t).toMonoidHom, Kh.map (MulAut.conj t).toMonoidHom⁆ =
      Kh.map (MulAut.conj t).toMonoidHom := by
    rw [← map_commutator, hKhp]
  have hle : Kh ⊔ Kh.map (MulAut.conj t).toMonoidHom ≤ perfectCore (⊤ : Subgroup H) :=
    sup_le (CFSG.Quasithin.le_perfectCore_of_perfect le_top hKhp)
      (CFSG.Quasithin.le_perfectCore_of_perfect le_top hKhtp)
  have hsup : Kh ⊔ Kh.map (MulAut.conj t).toMonoidHom = perfectCore (⊤ : Subgroup H) := by
    refine le_antisymm hle ?_
    have hPp := CFSG.Quasithin.perfectCore_perfect (⊤ : Subgroup H)
    have hPmap : (perfectCore (⊤ : Subgroup H)).map π ≤
        Kb ⊔ Kb.map (MulAut.conj τ).toMonoidHom := by
      rw [CFSG.Quasithin.map_perfectCore, map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
      exact h.perfectCore_top_le hO hOut
    have hPO : perfectCore (⊤ : Subgroup H) ≤ centralizer (oddCore H : Set H) :=
      (F4Pilot.le_oddCoreLift_of_perfect hPp hPmap).trans hBsup
    refine F4Pilot.perfect_le_of_forall_exists_commute hPp hle fun a ha => ?_
    have hπa : π a ∈ (Kh ⊔ Kh.map (MulAut.conj t).toMonoidHom).map π := by
      rw [Subgroup.map_sup, hπK, hπKt]
      exact hPmap (mem_map_of_mem π ha)
    obtain ⟨m, hm, hma⟩ := hπa
    refine ⟨m, hm, m⁻¹ * a, by group, fun b hb => ?_⟩
    have hz : m⁻¹ * a ∈ oddCore H := by
      have h2 : π (m⁻¹ * a) = 1 := by rw [map_mul, map_inv, hma, inv_mul_cancel]
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact mem_centralizer_iff.1 (hPO hb) _ hz
  exact ⟨le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm), hdisj, hsup, hKhp,
    hπK⟩

end Decomposition

end CFSG.SeitzReduction.UnitaryPilot
