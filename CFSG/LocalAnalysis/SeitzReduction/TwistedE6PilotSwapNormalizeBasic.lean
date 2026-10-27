module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapBasic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftDecomp

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (SwapComponentData oddCoreLift HasBLift swapDiagHom
  swapDiagHom_apply centralizerPerfectCore)

variable {G : Type} [Group G] [Finite G]

theorem exists_swapFactor_of_swapComponentData {X : Subgroup G} {t : G}
    (htX : t ∈ centralizer (X : Set G))
    {Kb Db : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hdata : SwapComponentData (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      Kb Db) (hOut : Group.IsSolvable (Outer Kb)) (hBK : HasBLift Kb)
    (hBsup : HasBLift (Kb ⊔ Kb.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom)) :
    ∃ Kc : Subgroup G, ⁅Kc, Kc⁆ = Kc ∧
      Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G) ∧
      Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = centralizerPerfectCore X ∧
      ∀ s ∈ centralizer (X : Set G), Odd (orderOf s) → s ∈ normalizer (Kc : Set G) := by
  obtain ⟨hcH, -, hsH, hpH, -⟩ := UnitaryPilot.swapLift_decomposition_of_hasBLift hdata hOut hBK
    hBsup
  have hKct : ((oddCoreLift Kb).map (centralizer (X : Set G)).subtype).map
      (MulAut.conj t).toMonoidHom = ((oddCoreLift Kb).map (MulAut.conj
        (⟨t, htX⟩ : centralizer (X : Set G))).toMonoidHom).map (centralizer (X : Set G)).subtype :=
    (F4Pilot.map_subtype_map_conj (oddCoreLift Kb) ⟨t, htX⟩).symm
  refine ⟨(oddCoreLift Kb).map (centralizer (X : Set G)).subtype, by rw [← map_commutator, hpH],
    ?_, ?_, fun s hs hso => ?_⟩
  · rw [hKct]
    exact F4Pilot.map_le_centralizer_map _ hcH
  · rw [hKct, ← Subgroup.map_sup, hsH, CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  · obtain ⟨σ, hσ⟩ := hdata.exists_sign
    have hs'o : Odd (orderOf (⟨s, hs⟩ : centralizer (X : Set G))) := by
      rw [← Subgroup.orderOf_coe]; exact hso
    have h2 : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
    have hσ1 : σ (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨s, hs⟩) = 1 := by
      obtain ⟨k, hk⟩ := hs'o
      have h1 : σ (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨s, hs⟩) ^ (2 * k + 1) =
          1 := by
        rw [← map_pow, ← map_pow, ← hk, pow_orderOf_eq_one, map_one, map_one]
      rw [pow_succ, pow_mul, h2, one_pow, one_mul] at h1
      exact h1
    have hKs := F4Pilot.mem_normalizer_oddCoreLift Kb (hσ _ hσ1)
    rw [mem_normalizer_iff_map_conj_eq] at hKs ⊢
    calc ((oddCoreLift Kb).map (centralizer (X : Set G)).subtype).map
          (MulAut.conj s).toMonoidHom =
        ((oddCoreLift Kb).map (MulAut.conj (⟨s, hs⟩ : centralizer (X : Set G))).toMonoidHom).map
          (centralizer (X : Set G)).subtype :=
          (F4Pilot.map_subtype_map_conj (oddCoreLift Kb) ⟨s, hs⟩).symm
      _ = (oddCoreLift Kb).map (centralizer (X : Set G)).subtype :=
          congrArg (Subgroup.map (centralizer (X : Set G)).subtype) hKs

omit [Finite G] in
theorem nonempty_swapCover_of_decomposition {X D : Subgroup G} {t : G} (htt : t * t = 1)
    {Kc : Subgroup G} (hperf : ⁅Kc, Kc⁆ = Kc)
    (hc : Kc.map (MulAut.conj t).toMonoidHom ≤ centralizer (Kc : Set G))
    (hsup : Kc ⊔ Kc.map (MulAut.conj t).toMonoidHom = centralizerPerfectCore X)
    (hnorm : ∀ s ∈ centralizer (X : Set G), Odd (orderOf s) → s ∈ normalizer (Kc : Set G))
    (hDp : ⁅D, D⁆ = D) (hDt : D ≤ centralizer ({t} : Set G)) (hDE : D ≤ centralizerPerfectCore X)
    (hPD : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ centralizer ({t} : Set G) →
      P ≤ centralizer (X : Set G) → P ≤ D) :
    Nonempty (SwapCover t X D (centralizerPerfectCore X)) := by
  set δ := swapDiagHom hc with hδ
  have hEX : centralizerPerfectCore X ≤ centralizer (X : Set G) :=
    F4Pilot.centralizerPerfectCore_le_centralizer X
  have htop : ⁅(⊤ : Subgroup Kc), (⊤ : Subgroup Kc)⁆ = (⊤ : Subgroup Kc) := by
    have h1 := CFSG.SeitzReduction.commutator_subgroupOf_eq_self (le_refl Kc) hperf
    rwa [subgroupOf_self] at h1
  have hrp : ⁅δ.range, δ.range⁆ = δ.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, htop]
  have hrt : δ.range ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨k, rfl⟩
    exact E6Pilot.swapDiagHom_mem_centralizer hc htt k
  have hrX : δ.range ≤ centralizer (X : Set G) := by
    rintro _ ⟨k, rfl⟩
    rw [swapDiagHom_apply]
    have h1 : (k : G) ∈ centralizerPerfectCore X := hsup ▸ mem_sup_left k.2
    have h2 : t * (k : G) * t⁻¹ ∈ centralizerPerfectCore X := hsup ▸ mem_sup_right ⟨k, k.2, rfl⟩
    exact mul_mem (hEX h1) (hEX h2)
  have hle : δ.range ≤ D := hPD _ hrp hrt hrX
  have hrange := E6Pilot.swapDiagHom_range_eq hc htt hDp (hsup ▸ hDE) hDt hle
  refine ⟨⟨Kc, hperf, hc, hsup, hnorm, fun k hk => hle ⟨⟨k, hk⟩, rfl⟩, fun d hd => ?_⟩⟩
  rw [← hrange] at hd
  obtain ⟨k, rfl⟩ := hd
  exact ⟨k, k.2, rfl⟩

end CFSG.SeitzReduction.TwistedE6Pilot
