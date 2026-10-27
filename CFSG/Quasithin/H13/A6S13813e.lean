module

public import CFSG.Quasithin.H13.A6S1385b

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem V1_le_Uγ_of_solvable (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hsol : Group.IsSolvable ↥H) {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hDH : F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H)
    (hγ : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    (h1 : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1) :
    fsuV1 T V ≤ F8.Uγ S.V3 H (g : G) := by
  have hF := hS.hF H hH
  rcases (S.lemma13_8_10 hF s hγ h1 hDH).2 with h | hcomm
  · exact h
  exfalso
  obtain ⟨δ, δ', k, y, sk, -, -, hUδ, hUγy, hDHk, hDγk⟩ :=
    hF.exists_symmetric_setup s (hF.not_Vγ_le_ballStab_of_lt s hDγ)
  set Uδ := F8.Uγ S.V3 H (k : G) with hUδdef
  set D := F8.DH S.V3 (fsuV1 T V) H (k : G) with hDdef
  set U := conjClosure S.V3 H with hUdef
  set Q := pCoreOf 2 H with hQ
  have hUδH : Uδ ≤ H := hF.Uγ_le_H sk
  have hcommk : ⁅Uδ, D⁆ = ⊥ := by
    rw [hUδ, hDHk, conjSub_commutator, hcomm]
    exact conjSub_bot _
  have hDU : D ≤ U := centralizerMod_le_left _ _ _
  have hidx : D.relIndex U = 2 := by
    have hU2 : IsPGroup 2 ↥(F8.Uγ S.V3 H (g : G)) :=
      isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
    have h2 := HypF98.relIndex_eq_two_pow_mIdx
      (Y := F8.Dγ S.V3 (fsuV1 T V) H (g : G)) hU2
    rw [h1, pow_one] at h2
    rw [hDHk, ← hUγy]
    rw [show (conjSub (y : G) (F8.Dγ S.V3 (fsuV1 T V) H (g : G))).relIndex
        (conjSub (y : G) (F8.Uγ S.V3 H (g : G))) =
        (F8.Dγ S.V3 (fsuV1 T V) H (g : G)).relIndex (F8.Uγ S.V3 H (g : G)) from
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj (y : G)).injective]
    exact h2
  have hDδ : F8.Dγ S.V3 (fsuV1 T V) H (k : G) < Uδ := by
    rw [hDγk, hUδ]
    refine lt_of_le_of_ne (conjSub_mono _ hDH.le) fun he => hDH.ne ?_
    exact (conjSub_inj _).1 he
  have hDδQ := hF.Dγ_eq_inf_pCoreOf sk
  obtain ⟨u, huδ, huQ⟩ : ∃ u ∈ Uδ, u ∉ Q := by
    by_contra hcon
    push Not at hcon
    rw [hDδQ] at hDδ
    exact hDδ.ne (le_antisymm inf_le_left (le_inf le_rfl fun x hx => hcon x hx))
  have huH : u ∈ H := hUδH huδ
  have hUab := hF.F911_3
  have hcommU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUab.1.is_comm.comm (⟨a, ha⟩ : ↥U) ⟨b, hb⟩)
  have huD : ∀ d ∈ D, u * d * u⁻¹ * d⁻¹ = 1 := by
    intro d hd
    have := Subgroup.commutator_mem_commutator huδ hd
    rw [hcommk, Subgroup.mem_bot] at this
    rwa [commutatorElement_def] at this
  have huU : ∀ x ∈ U, u * x * u⁻¹ ∈ U := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H huH) x).mp hx
  obtain ⟨x₀, hx₀U, hx₀D⟩ : ∃ x₀ ∈ U, x₀ ∉ D := by
    by_contra hcon
    push Not at hcon
    have : D.relIndex U = 1 := Subgroup.relIndex_eq_one.mpr fun x hx => hcon x hx
    omega
  have hidx' : (D.subgroupOf U).index = 2 := hidx
  have htr : InducesTransvMod u U (fsuV1 T V) := by
    refine ⟨fun hall => huQ ?_, u * x₀ * u⁻¹ * x₀⁻¹, fun x hx => ?_⟩
    · rw [hQ, hF.toHypF91.pCoreOf_eq_centralizerMod]
      exact ⟨huH, hF.toHypF91.H_normalizes_V₁ huH, hall⟩
    · by_cases hxD : x ∈ D
      · left
        rw [huD x hxD]
        exact (fsuV1 T V).one_mem
      · right
        have hd : x * x₀⁻¹ ∈ D := by
          have h := (Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨x, hx⟩)
            (b := (⟨x₀, hx₀U⟩ : ↥U)⁻¹)).2
          have h' := h ⟨fun h2 => absurd h2 hxD, fun h2 => by
            have h3 : (⟨x₀, hx₀U⟩ : ↥U) ∈ D.subgroupOf U := by
              simpa using (D.subgroupOf U).inv_mem h2
            exact absurd (Subgroup.mem_subgroupOf.1 h3) hx₀D⟩
          exact h'
        set d := x * x₀⁻¹ with hddef
        have hdU : d ∈ U := hDU hd
        have e : x = d * x₀ := by rw [hddef]; group
        have hc : u * x * u⁻¹ * x⁻¹ = u * x₀ * u⁻¹ * x₀⁻¹ := by
          have hud : u * d * u⁻¹ = d := by
            have := huD d hd
            calc u * d * u⁻¹ = u * d * u⁻¹ * d⁻¹ * d := by group
              _ = d := by rw [this, one_mul]
          have hcU : u * x₀ * u⁻¹ * x₀⁻¹ ∈ U :=
            U.mul_mem (huU x₀ hx₀U) (U.inv_mem hx₀U)
          calc u * x * u⁻¹ * x⁻¹ = (u * d * u⁻¹) * (u * x₀ * u⁻¹ * x₀⁻¹) * d⁻¹ := by
                rw [e]; group
            _ = d * (u * x₀ * u⁻¹ * x₀⁻¹) * d⁻¹ := by rw [hud]
            _ = u * x₀ * u⁻¹ * x₀⁻¹ := by
                rw [hcommU d hdU _ hcU]
                group
        rw [hc, mul_inv_cancel]
        exact (fsuV1 T V).one_mem
  exact S.no_transv_of_solvable hS hH hsol u huH htr

end Setting4

end CFSG.Quasithin.H13.A6

