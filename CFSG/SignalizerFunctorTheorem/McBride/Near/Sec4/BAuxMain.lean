module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.BAuxInduct

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.BAux

variable {G : Type*} [Group G]

theorem solvableRadical_top_eq_bot [Finite G] (hsol : CFSG.solvableRadical G = ⊥) :
    CFSG.solvableRadical (⊤ : Subgroup G) = ⊥ := by
  let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  have h := KAPI.comap_solvableRadical_eq (f := e.toMonoidHom) e.surjective
    (by rw [hker]; infer_instance)
  rw [hsol, MonoidHom.comap_bot, hker] at h
  exact h.symm

theorem kOf_top_eq_layer [Finite G] (hsol : CFSG.solvableRadical G = ⊥) :
    kOf (⊤ : Subgroup G) = CFSG.layer G := by
  have hsol' : sol (⊤ : Subgroup G) = ⊥ := (sol_eq_bot_iff _).mpr (solvableRadical_top_eq_bot hsol)
  rw [kOf_eq_map_layer hsol']
  have h := map_layer_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
  exact h

theorem le_layer_of_deg_le [Finite G] (hsol : CFSG.solvableRadical G = ⊥)
    (hB : ∀ J ∈ lcal (⊤ : Subgroup G), HypB ↥J) {X₀ : Subgroup G} (hX : oStar ↥X₀ = ⊤)
    (hperf : Group.IsPerfect X₀) (hdeg : deg ↥(CFSG.layer G) ≤ deg ↥X₀) :
    X₀ ≤ CFSG.layer G := by
  have hsol' : sol (⊤ : Subgroup G) = ⊥ := (sol_eq_bot_iff _).mpr (solvableRadical_top_eq_bot hsol)
  have hKl := kOf_top_eq_layer hsol
  have hK : IsDirectProduct (lcal (⊤ : Subgroup G)) (CFSG.layer G) := by
    rw [← hKl]
    exact isDirectProduct_lcal_kOf hsol'
  have hcent : (⊤ : Subgroup G) ⊓ Subgroup.centralizer (CFSG.layer G : Set G) = ⊥ := by
    rw [← hKl]
    exact centralizer_kOf_eq_bot hsol'
  set 𝓛 := lcal (⊤ : Subgroup G) with h𝓛
  set φ : ↥X₀ →* G := X₀.subtype with hφ
  have hfin : 𝓛.Finite := Set.toFinite _
  have hinv : IsInv φ 𝓛 := by
    intro x J hJ
    refine map_conj_mem_lcal hJ ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp
  have hcomm : ∀ J ∈ 𝓛, ∀ J' ∈ 𝓛, J ≠ J' → ∀ a ∈ J, ∀ b ∈ J', a * b = b * a :=
    fun J hJ J' hJ' hne a ha b hb => (hK.commute J hJ J' hJ' hne a ha b hb).eq
  have hbound := bound_aux (φ := φ) hX hperf hfin hB hcomm 𝓛.ncard 𝓛 subset_rfl hinv rfl
  have hcz : ∀ z : G, (∀ J ∈ 𝓛, ∀ j ∈ J, j * z = z * j) → z = 1 := by
    intro z hz
    have hle : CFSG.layer G ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [← hK.sSup_eq]
      refine sSup_le fun J hJ j hj => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hz J hJ j hj
    have hzc : z ∈ (⊤ : Subgroup G) ⊓ Subgroup.centralizer (CFSG.layer G : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_top z, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
    rw [hcent, Subgroup.mem_bot] at hzc
    exact hzc
  have hcen : cen φ 𝓛 = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have := hcz (x : G) hx
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hdegcen : deg ↥(cen φ 𝓛) = 0 := by
    rw [hcen]
    exact KAPI.deg_eq_zero_of_isSolvable inferInstance
  have hlayerN : (CFSG.layer G).Normal := by
    have : (CFSG.layer G).Characteristic := CFSG.LocalCores.layer_characteristic
    infer_instance
  have hrad : CFSG.solvableRadical ↥(CFSG.layer G) = ⊥ := by
    have h := map_subtype_solvableRadical_eq_inf (hlayerN.isSubnormal)
    rw [hsol, inf_bot_eq] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (CFSG.layer G).subtype_injective).mp h
  have hdegK : deg ↥(CFSG.layer G) = permDeg ↥(CFSG.layer G) :=
    permDeg_congr ((QuotientGroup.quotientMulEquivOfEq hrad).trans QuotientGroup.quotientBot)
  have hkap : kappa 𝓛 ≤ deg ↥(CFSG.layer G) := by
    have : Fintype 𝓛 := hfin.fintype
    have hsimple : ∀ J : 𝓛, IsSimpleGroup ↥(J : Subgroup G) := fun J =>
      (mem_lcal_iff.mp J.2).2.2.1
    have hnc : ∀ J : 𝓛, ¬ IsMulCommutative ↥(J : Subgroup G) := fun J =>
      (mem_lcal_iff.mp J.2).2.2.2
    have h1 : kappa 𝓛 = ∑ J : 𝓛, permDeg ↥(J : Subgroup G) := by
      rw [kappa, ← finsum_subtype_eq_finsum_cond (f := fun J : Subgroup G => deg ↥J)
        (fun J => J ∈ 𝓛), finsum_eq_sum_of_fintype]
      refine Finset.sum_congr rfl fun J _ => ?_
      have := hsimple J
      exact deg_eq_permDeg_of_isSimpleGroup _ (hnc J)
    have h2 := sum_permDeg_le_permDeg_pi (fun J : 𝓛 => (J : Subgroup G)) hnc
    have h3 : permDeg (∀ J : 𝓛, ↥(J : Subgroup G)) = permDeg ↥(CFSG.layer G) :=
      permDeg_congr hK.equiv
    rw [hdegK, ← h3, h1]
    exact h2
  have heq : deg ↥X₀ = deg ↥(cen φ 𝓛) + kappa 𝓛 := by omega
  have hinner := hbound.2 heq
  intro x hx
  obtain ⟨k, hk, hkx⟩ := hinner ⟨x, hx⟩
  have hz : (k⁻¹ * x) = 1 := by
    refine hcz _ fun J hJ j hj => ?_
    have h := hkx J hJ j hj
    simp only [hφ, Subgroup.coe_subtype] at h
    calc j * (k⁻¹ * x) = k⁻¹ * (k * j * k⁻¹) * x := by group
      _ = k⁻¹ * (x * j * x⁻¹) * x := by rw [← h]
      _ = k⁻¹ * x * j := by group
  have : x = k := by
    calc x = k * (k⁻¹ * x) := by group
      _ = k := by rw [hz, mul_one]
  rw [this, ← hK.sSup_eq]
  exact hk

end CFSG.SignalizerFunctorTheorem.McBride.Near.BAux
