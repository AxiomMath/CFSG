module

public import CFSG.LocalAnalysis.StandardType.PhanELocalModels
import CFSG.LocalAnalysis.StandardType.PhanELocalPlane
import CFSG.LocalAnalysis.StandardType.PhanELocalSigma
import CFSG.LocalAnalysis.StandardType.PhanELocalHerm

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

private theorem plpo_exists_span_eq_of_finrank_one {U : Submodule K (Fin 3 → K)}
    (hU : finrank K U = 1) : ∃ v : Fin 3 → K, v ≠ 0 ∧ U = Submodule.span K {v} := by
  have hne : U ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hU
    omega
  obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨v, hv0, eq_span_singleton_of_mem_of_finrank_eq_one hU hvU hv0⟩

private theorem plpo_finrank_sup_eq_two_of_ne {p q : Submodule K (Fin 3 → K)}
    (hp : finrank K p = 1) (hq : finrank K q = 1) (hne : p ≠ q) :
    finrank K ↥(p ⊔ q) = 2 := by
  have hfin : finrank K ↥(p ⊓ q) = 0 := by
    by_contra h
    have hpos : 0 < finrank K ↥(p ⊓ q) := Nat.pos_of_ne_zero h
    have hle1 : finrank K ↥(p ⊓ q) ≤ 1 := by
      calc finrank K ↥(p ⊓ q) ≤ finrank K ↥p := Submodule.finrank_mono inf_le_left
        _ = 1 := hp
    have heq : finrank K ↥(p ⊓ q) = 1 := by omega
    have hpq : p ≤ q := by
      have hpeq : p ⊓ q = p :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [heq, hp])
      rw [← hpeq]
      exact inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hpq (by rw [hp, hq]))
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq p q
  rw [hp, hq, hfin, add_zero] at hsum
  omega

private theorem plpo_mem_genSet_of_aniso_nondeg (hK : Nat.card K = (2 ^ f) ^ 2)
    {p L : Submodule K (Fin 3 → K)}
    (hp : finrank K p = 1) (hL : finrank K L = 2) (hpL : p ≤ L)
    (hpa : p ⊓ perpB K f 3 0 3 p = ⊥) (hLa : L ⊓ perpB K f 3 0 3 L = ⊥) :
    Plane.ofChain p L hp hL hpL ∈ genSet K f 3 [0, 3] [true] := by
  rw [mem_a2pol_iff (K := K) (f := f) hK, Plane.ofChain_E_one, Plane.ofChain_E_two]
  exact ⟨hpa, hLa⟩

private theorem plpo_hermLin_smul_add_self (hK : Nat.card K = (2 ^ f) ^ 2)
    (w u : Fin 3 → K) (s : K)
    (hww : hermLin K f 3 0 3 w w = 0) (hwu : hermLin K f 3 0 3 w u = 1) :
    hermLin K f 3 0 3 (s • w + u) (s • w + u) =
      s + sg K f s + hermLin K f 3 0 3 u u := by
  have huw : hermLin K f 3 0 3 u w = 1 := by
    rw [herm_symm (K := K) (f := f) hK w u, hwu, map_one]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
    hww, hwu, huw, mul_zero, mul_one, zero_add, add_zero]
  ring

theorem a2pol_connected (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) :
    ((flagSys K 2).restrict (genSet K f 3 [0, 3] [true])).Connected := by
  refine Plane.connected_of_common_nbr (genSet K f 3 [0, 3] [true]) ?_
  intro x hx y hy
  have hx' := (mem_a2pol_iff (K := K) (f := f) hK x).mp hx
  have hy' := (mem_a2pol_iff (K := K) (f := f) hK y).mp hy
  obtain ⟨v, hv0, hpv⟩ := plpo_exists_span_eq_of_finrank_one (K := K) (Plane.finrank_E_one x)
  obtain ⟨v', hv0', hpv'⟩ := plpo_exists_span_eq_of_finrank_one (K := K) (Plane.finrank_E_one y)
  have hv : hermLin K f 3 0 3 v v ≠ 0 := by
    refine (span_inf_perpB_eq_bot_iff (K := K) (f := f) hv0).mp ?_
    rw [← hpv]
    exact hx'.1
  have hv' : hermLin K f 3 0 3 v' v' ≠ 0 := by
    refine (span_inf_perpB_eq_bot_iff (K := K) (f := f) hv0').mp ?_
    rw [← hpv']
    exact hy'.1
  by_cases hp_eq : x.E 1 = y.E 1
  · refine ⟨x.E 1, x.E 2, x.E 2, ?_, ?_, ?_, ?_⟩
    · exact ⟨x, hx, rfl, rfl⟩
    · exact ⟨x, hx, rfl, rfl⟩
    · exact ⟨x, hx, rfl, rfl⟩
    · exact ⟨x, hx, hp_eq, rfl⟩
  · have hLfin : finrank K ↥(x.E 1 ⊔ y.E 1) = 2 :=
      plpo_finrank_sup_eq_two_of_ne (K := K) (Plane.finrank_E_one x) (Plane.finrank_E_one y)
        hp_eq
    by_cases hL : (x.E 1 ⊔ y.E 1) ⊓ perpB K f 3 0 3 (x.E 1 ⊔ y.E 1) = ⊥
    ·
      have hp_aniso : Submodule.span K {v} ⊓ perpB K f 3 0 3 (Submodule.span K {v}) = ⊥ :=
        (span_inf_perpB_eq_bot_iff (K := K) (f := f) hv0).mpr hv
      have hp'_aniso : Submodule.span K {v'} ⊓ perpB K f 3 0 3 (Submodule.span K {v'}) = ⊥ :=
        (span_inf_perpB_eq_bot_iff (K := K) (f := f) hv0').mpr hv'
      have hv_fin : finrank K ↥(Submodule.span K {v}) = 1 := finrank_span_singleton hv0
      have hv'_fin : finrank K ↥(Submodule.span K {v'}) = 1 := finrank_span_singleton hv0'
      have hL_nondeg : (Submodule.span K {v} ⊔ Submodule.span K {v'}) ⊓
          perpB K f 3 0 3 (Submodule.span K {v} ⊔ Submodule.span K {v'}) = ⊥ := by
        rw [← hpv, ← hpv']
        exact hL
      have hLfin' : finrank K ↥(Submodule.span K {v} ⊔ Submodule.span K {v'}) = 2 := by
        rw [← hpv, ← hpv']
        exact hLfin
      have hasFl : ∀ (p L : Submodule K (Fin 3 → K)), finrank K p = 1 → finrank K L = 2 →
          p ≤ L → p ⊓ perpB K f 3 0 3 p = ⊥ → L ⊓ perpB K f 3 0 3 L = ⊥ →
          Plane.HasFl (genSet K f 3 [0, 3] [true]) p L :=
        fun p L hp hL hpL hpa hLa => Plane.hasFl_ofChain hp hL hpL
          (plpo_mem_genSet_of_aniso_nondeg (K := K) (f := f) hK hp hL hpL hpa hLa)
      refine ⟨Submodule.span K {v'}, Submodule.span K {v} ⊔ Submodule.span K {v'},
        Submodule.span K {v} ⊔ Submodule.span K {v'}, ?_, ?_, ?_, ?_⟩
      · rw [hpv]
        exact hasFl (Submodule.span K {v}) (Submodule.span K {v} ⊔ Submodule.span K {v'})
          hv_fin hLfin' le_sup_left hp_aniso hL_nondeg
      · exact hasFl (Submodule.span K {v'}) (Submodule.span K {v} ⊔ Submodule.span K {v'})
          hv'_fin hLfin' le_sup_right hp'_aniso hL_nondeg
      · exact hasFl (Submodule.span K {v'}) (Submodule.span K {v} ⊔ Submodule.span K {v'})
          hv'_fin hLfin' le_sup_right hp'_aniso hL_nondeg
      · rw [hpv']
        exact hasFl (Submodule.span K {v'}) (Submodule.span K {v} ⊔ Submodule.span K {v'})
          hv'_fin hLfin' le_sup_right hp'_aniso hL_nondeg
    ·
      obtain ⟨w₀, hw₀_mem, hw₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL
      have hw₀L : w₀ ∈ x.E 1 ⊔ y.E 1 := hw₀_mem.1
      have hperpL : ∀ u ∈ x.E 1 ⊔ y.E 1, hermLin K f 3 0 3 u w₀ = 0 :=
        (mem_perpB_iff (K := K) (f := f) (x.E 1 ⊔ y.E 1) w₀).mp hw₀_mem.2
      have hv_w₀ : hermLin K f 3 0 3 v w₀ = 0 := by
        apply hperpL
        rw [hpv]
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
      have hv'_w₀ : hermLin K f 3 0 3 v' w₀ = 0 := by
        apply hperpL
        rw [hpv']
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v')
      have hw₀_v : hermLin K f 3 0 3 w₀ v = 0 := by
        have h := herm_symm (K := K) (f := f) hK v w₀
        rw [hv_w₀, map_zero] at h
        exact h
      have hw₀_v' : hermLin K f 3 0 3 w₀ v' = 0 := by
        have h := herm_symm (K := K) (f := f) hK v' w₀
        rw [hv'_w₀, map_zero] at h
        exact h
      have hw₀w₀ : hermLin K f 3 0 3 w₀ w₀ = 0 := hperpL w₀ hw₀L
      have hex : ∃ u : Fin 3 → K, hermLin K f 3 0 3 u w₀ ≠ 0 := by
        by_contra h
        exact hw₀_ne (herm_nondeg (K := K) (f := f) (v := w₀)
          (fun u => not_not.mp (not_exists.mp h u)))
      obtain ⟨u, hu_ne⟩ := hex
      have hwu_ne : hermLin K f 3 0 3 w₀ u ≠ 0 := by
        intro h0
        apply hu_ne
        apply (sg K f).injective
        rw [← herm_symm (K := K) (f := f) hK u w₀, h0, map_zero]
      obtain ⟨u₁, hu₁⟩ : ∃ u₁ : Fin 3 → K, hermLin K f 3 0 3 w₀ u₁ = 1 :=
        ⟨(hermLin K f 3 0 3 w₀ u)⁻¹ • u, by
          rw [herm_smul_right]
          exact inv_mul_cancel₀ hwu_ne⟩
      obtain ⟨u₂, hv_u₂, hw₀_u₂⟩ :
          ∃ u₂ : Fin 3 → K, hermLin K f 3 0 3 v u₂ = 0 ∧ hermLin K f 3 0 3 w₀ u₂ = 1 := by
        refine ⟨u₁ + (hermLin K f 3 0 3 v u₁ / hermLin K f 3 0 3 v v) • v, ?_, ?_⟩
        · show hermLin K f 3 0 3 v
            (u₁ + (hermLin K f 3 0 3 v u₁ / hermLin K f 3 0 3 v v) • v) = 0
          rw [herm_add_right, herm_smul_right, div_mul_cancel₀ _ hv]
          exact CharTwo.add_self_eq_zero _
        · show hermLin K f 3 0 3 w₀
            (u₁ + (hermLin K f 3 0 3 v u₁ / hermLin K f 3 0 3 v v) • v) = 1
          rw [herm_add_right, hu₁, herm_smul_right, hw₀_v, mul_zero, add_zero]
      have hu₂_w₀ : hermLin K f 3 0 3 u₂ w₀ = 1 := by
        rw [herm_symm (K := K) (f := f) hK w₀ u₂, hw₀_u₂, map_one]
      obtain ⟨τ, hτ_fixed, hτ_ne0, hτ_ne⟩ :=
        exists_sg_fixed_avoid (K := K) (f := f) hK hq 0
          (hermLin K f 3 0 3 v' u₂ * sg K f (hermLin K f 3 0 3 v' u₂) /
            hermLin K f 3 0 3 v' v')
      have hτκ : τ * hermLin K f 3 0 3 v' v' ≠
          hermLin K f 3 0 3 v' u₂ * sg K f (hermLin K f 3 0 3 v' u₂) := by
        intro h
        apply hτ_ne
        rw [eq_div_iff hv']
        exact h
      have hτc_fixed : sg K f (τ + hermLin K f 3 0 3 u₂ u₂) =
          τ + hermLin K f 3 0 3 u₂ u₂ := by
        rw [map_add, hτ_fixed, herm_self_fixed (K := K) (f := f) hK u₂]
      obtain ⟨s, hs⟩ := exists_sg_trace (K := K) (f := f) hK hτc_fixed
      let z₀ : Fin 3 → K := s • w₀ + u₂
      have hv_z₀ : hermLin K f 3 0 3 v z₀ = 0 := by
        show hermLin K f 3 0 3 v (s • w₀ + u₂) = 0
        rw [herm_add_right, herm_smul_right, hv_w₀, mul_zero, zero_add, hv_u₂]
      have hv'_z₀ : hermLin K f 3 0 3 v' z₀ = hermLin K f 3 0 3 v' u₂ := by
        show hermLin K f 3 0 3 v' (s • w₀ + u₂) = hermLin K f 3 0 3 v' u₂
        rw [herm_add_right, herm_smul_right, hv'_w₀, mul_zero, zero_add]
      have hz₀_z₀ : hermLin K f 3 0 3 z₀ z₀ = τ := by
        show hermLin K f 3 0 3 (s • w₀ + u₂) (s • w₀ + u₂) = τ
        rw [plpo_hermLin_smul_add_self (K := K) (f := f) hK w₀ u₂ s hw₀w₀ hw₀_u₂,
          hs, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      have hgram_v : hermLin K f 3 0 3 v v * hermLin K f 3 0 3 z₀ z₀ ≠
          hermLin K f 3 0 3 v z₀ * hermLin K f 3 0 3 z₀ v := by
        rw [hv_z₀, hz₀_z₀, zero_mul]
        exact mul_ne_zero hv hτ_ne0
      have hgram_v' : hermLin K f 3 0 3 v' v' * hermLin K f 3 0 3 z₀ z₀ ≠
          hermLin K f 3 0 3 v' z₀ * hermLin K f 3 0 3 z₀ v' := by
        rw [hv'_z₀, hz₀_z₀, herm_symm (K := K) (f := f) hK v' z₀, hv'_z₀]
        rw [mul_comm (hermLin K f 3 0 3 v' v') τ]
        exact hτκ
      have hgram_v'_symm : hermLin K f 3 0 3 z₀ z₀ * hermLin K f 3 0 3 v' v' ≠
          hermLin K f 3 0 3 z₀ v' * hermLin K f 3 0 3 v' z₀ := by
        rw [mul_comm (hermLin K f 3 0 3 z₀ z₀) (hermLin K f 3 0 3 v' v'),
          mul_comm (hermLin K f 3 0 3 z₀ v') (hermLin K f 3 0 3 v' z₀)]
        exact hgram_v'
      have hm_nondeg : (Submodule.span K {v} ⊔ Submodule.span K {z₀}) ⊓
          perpB K f 3 0 3 (Submodule.span K {v} ⊔ Submodule.span K {z₀}) = ⊥ :=
        sup_inf_perpB_eq_bot_of_gram (K := K) (f := f) hgram_v
      have hm_fin : finrank K ↥(Submodule.span K {v} ⊔ Submodule.span K {z₀}) = 2 :=
        finrank_span_pair_of_gram (K := K) (f := f) hgram_v
      have hm'_nondeg : (Submodule.span K {z₀} ⊔ Submodule.span K {v'}) ⊓
          perpB K f 3 0 3 (Submodule.span K {z₀} ⊔ Submodule.span K {v'}) = ⊥ :=
        sup_inf_perpB_eq_bot_of_gram (K := K) (f := f) hgram_v'_symm
      have hm'_fin : finrank K ↥(Submodule.span K {z₀} ⊔ Submodule.span K {v'}) = 2 :=
        finrank_span_pair_of_gram (K := K) (f := f) hgram_v'_symm
      have hz0_ne : z₀ ≠ 0 := by
        intro h
        have h0 : hermLin K f 3 0 3 z₀ z₀ = 0 := by
          rw [h]
          exact map_zero (hermLin K f 3 0 3 (0 : Fin 3 → K))
        rw [hz₀_z₀] at h0
        exact hτ_ne0 h0
      have hz_aniso : Submodule.span K {z₀} ⊓ perpB K f 3 0 3 (Submodule.span K {z₀}) = ⊥ :=
        (span_inf_perpB_eq_bot_iff (K := K) (f := f) hz0_ne).mpr (by
          rw [hz₀_z₀]
          exact hτ_ne0)
      have hp_aniso : Submodule.span K {v} ⊓ perpB K f 3 0 3 (Submodule.span K {v}) = ⊥ :=
        (span_inf_perpB_eq_bot_iff (K := K) (f := f) hv0).mpr hv
      have hp'_aniso : Submodule.span K {v'} ⊓ perpB K f 3 0 3 (Submodule.span K {v'}) = ⊥ :=
        (span_inf_perpB_eq_bot_iff (K := K) (f := f) hv0').mpr hv'
      have hv_fin : finrank K ↥(Submodule.span K {v}) = 1 := finrank_span_singleton hv0
      have hv'_fin : finrank K ↥(Submodule.span K {v'}) = 1 := finrank_span_singleton hv0'
      have hz_fin : finrank K ↥(Submodule.span K {z₀}) = 1 := finrank_span_singleton hz0_ne
      have hasFl : ∀ (p L : Submodule K (Fin 3 → K)), finrank K p = 1 → finrank K L = 2 →
          p ≤ L → p ⊓ perpB K f 3 0 3 p = ⊥ → L ⊓ perpB K f 3 0 3 L = ⊥ →
          Plane.HasFl (genSet K f 3 [0, 3] [true]) p L :=
        fun p L hp hL hpL hpa hLa => Plane.hasFl_ofChain hp hL hpL
          (plpo_mem_genSet_of_aniso_nondeg (K := K) (f := f) hK hp hL hpL hpa hLa)
      refine ⟨Submodule.span K {z₀}, Submodule.span K {v} ⊔ Submodule.span K {z₀},
        Submodule.span K {z₀} ⊔ Submodule.span K {v'}, ?_, ?_, ?_, ?_⟩
      · rw [hpv]
        exact hasFl (Submodule.span K {v}) (Submodule.span K {v} ⊔ Submodule.span K {z₀})
          hv_fin hm_fin le_sup_left hp_aniso hm_nondeg
      · exact hasFl (Submodule.span K {z₀}) (Submodule.span K {v} ⊔ Submodule.span K {z₀})
          hz_fin hm_fin le_sup_right hz_aniso hm_nondeg
      · exact hasFl (Submodule.span K {z₀}) (Submodule.span K {z₀} ⊔ Submodule.span K {v'})
          hz_fin hm'_fin le_sup_left hz_aniso hm'_nondeg
      · rw [hpv']
        exact hasFl (Submodule.span K {v'}) (Submodule.span K {z₀} ⊔ Submodule.span K {v'})
          hv'_fin hm'_fin le_sup_right hp'_aniso hm'_nondeg

end CFSG.ClassicalInvolution.Phan.PhanE

end
