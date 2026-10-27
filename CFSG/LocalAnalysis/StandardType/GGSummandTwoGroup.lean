module

public import CFSG.LocalAnalysis.StandardType.GGSummandStructBasic
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section Frattini

variable {X : Type} [Group X] [Finite X]

theorem ggTwoGroup_le_of_normal_sup {J S P : Subgroup X} (hSJ : S ≤ J) (hPJ : P ≤ J)
    (hS : (S.subgroupOf J).Normal) (hP2 : IsPGroup 2 P) (hsup : S ⊔ P = J)
    (hc : ⁅J, P⁆ = P) : P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Subgroup ↥J := S.subgroupOf J with hS'
  set P' : Subgroup ↥J := P.subgroupOf J with hP'
  let φ : ↥J →* ↥J ⧸ S' := QuotientGroup.mk' S'
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective S'
  have hsup' : S' ⊔ P' = ⊤ := by
    rw [hS', hP', ← Subgroup.subgroupOf_sup hSJ hPJ, hsup, Subgroup.subgroupOf_self]
  have hmapP : P'.map φ = ⊤ := by
    have h1 : (S' ⊔ P').map φ = ⊤ := by rw [hsup', Subgroup.map_top_of_surjective _ hsurj]
    rw [Subgroup.map_sup] at h1
    have h2 : S'.map φ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [h2, bot_sup_eq] at h1
  have hP'2 : IsPGroup 2 ↥P' := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPJ).symm
  have hA2 : IsPGroup 2 ↥(P'.map φ) := hP'2.map φ
  have hsol : Group.IsSolvable ↥(P'.map φ) := by
    have : Group.IsNilpotent ↥(P'.map φ) := hA2.isNilpotent
    infer_instance
  have hcomm : ⁅(⊤ : Subgroup ↥J), P'⁆ = P' := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_commutator]
    have e1 : (⊤ : Subgroup ↥J).map J.subtype = J := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have e2 : P'.map J.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPJ
    rw [e1, e2, hc]
  have htop : ⁅(⊤ : Subgroup (↥J ⧸ S')), (⊤ : Subgroup (↥J ⧸ S'))⁆ = ⊤ := by
    have h1 := congrArg (Subgroup.map φ) hcomm
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj, hmapP] at h1
    exact h1
  have hperf : ⁅P'.map φ, P'.map φ⁆ = P'.map φ := by
    rw [hmapP]; exact htop
  have hbot := CFSG.SeitzReduction.perfect_eq_bot_of_le hsol hperf le_rfl
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hbot (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hPJ hx⟩ : ↥J) ∈ P'))

theorem ggTwoGroup_le_of_subnormal_sup {J S P : Subgroup X} (hsn : IsSubnormal S J)
    (hPJ : P ≤ J) (hP2 : IsPGroup 2 P) (hsup : S ⊔ P = J) (hc : ⁅J, P⁆ = P) : P ≤ S := by
  induction hsn with
  | refl => exact hPJ
  | @step H M K hle hN hMK ih =>
    have hMK' : M ≤ K := isSubnormal_le_of_assembly hMK
    have hM : M ⊔ P = K :=
      le_antisymm (sup_le hMK' hPJ) (hsup ▸ sup_le_sup_right hle P)
    have hPM : P ≤ M := ih hPJ hM hc
    have hMeq : M = K := le_antisymm hMK' (hsup ▸ sup_le hle hPM)
    subst hMeq
    exact ggTwoGroup_le_of_normal_sup hle hPJ hN hP2 hsup hc

end Frattini

end CFSG.StandardType
