module

public import CFSG.LocalAnalysis.WeakClosure81.W15TenSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem W15Eight1.relIndex_eq_two {M V₀ V U S : Subgroup G} (hW : W15Eight1 G) (hS : Std15 G)
    (h : Cex15 M V₀ V U S) : (v1Sub15 V₀ U).relIndex V₀ = 2 := by
  have hq : E3.mQuot V₀ (v1Sub15 V₀ U) = 1 := hW M V₀ V U S hS h
  have hp : IsPGroup 2 ↥V₀ := h.hyp.isPGroup.to_le h.hyp.h6.le
  have hdvd : (v1Sub15 V₀ U).relIndex V₀ ∣ Nat.card ↥V₀ := Subgroup.index_dvd_card _
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  unfold E3.mQuot at hq
  rw [hk, padicValNat.prime_pow] at hq
  rw [hk, hq]
  norm_num

namespace Hyp1510

variable {M V₀ V U S H P : Subgroup G}

theorem inf_pCoreOf_eq (hW : W15Eight1 G) (hS : Std15 G) (h : Cex15 M V₀ V U S)
    (hP : Hyp1510 V₀ V U S H P) : V₀ ⊓ pCoreOf 2 H = v1Sub15 V₀ U := by
  have hle : v1Sub15 V₀ U ≤ V₀ ⊓ pCoreOf 2 H :=
    le_inf (v1Sub15_le_left V₀ U) (hP.fam.v1_le_pCoreOf h)
  have hlt : ¬ V₀ ≤ pCoreOf 2 H := hP.fam.not_V₀_le_pCoreOf h
  have h2 := hW.relIndex_eq_two hS h
  have hmul := Subgroup.relIndex_mul_relIndex (v1Sub15 V₀ U) (V₀ ⊓ pCoreOf 2 H) V₀ hle inf_le_left
  rw [h2] at hmul
  have hne : (V₀ ⊓ pCoreOf 2 H).relIndex V₀ ≠ 1 := fun h1 =>
    hlt (inf_le_right.trans' (Subgroup.relIndex_eq_one.1 h1))
  have hdvd : (V₀ ⊓ pCoreOf 2 H).relIndex V₀ ∣ 2 := Dvd.intro_left _ hmul
  have h2' : (V₀ ⊓ pCoreOf 2 H).relIndex V₀ = 2 :=
    ((Nat.dvd_prime Nat.prime_two).1 hdvd).resolve_left hne
  rw [h2'] at hmul
  have h3 : (v1Sub15 V₀ U).relIndex (V₀ ⊓ pCoreOf 2 H) = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h3) hle

theorem inf_iHull15_eq (hW : W15Eight1 G) (hS : Std15 G) (h : Cex15 M V₀ V U S)
    (hP : Hyp1510 V₀ V U S H P) : V₀ ⊓ iHull15 V₀ U H = v1Sub15 V₀ U := by
  refine le_antisymm ?_ (le_inf (v1Sub15_le_left V₀ U) (v1Sub15_le_iHull15 V₀ U H))
  rw [← hP.inf_pCoreOf_eq hW hS h]
  exact inf_le_inf_left _ (hP.iHull15_le_pCoreOf h)

theorem not_V₀_le_iHull15 (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) :
    ¬ V₀ ≤ iHull15 V₀ U H := fun hle =>
  hP.fam.not_V₀_le_pCoreOf h (hle.trans (hP.iHull15_le_pCoreOf h))

end Hyp1510

end CFSG.LocalAnalysis.WeakClosure81
