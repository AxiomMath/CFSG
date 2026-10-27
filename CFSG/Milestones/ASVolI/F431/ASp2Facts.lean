module

public import CFSG.Milestones.ASVolI.F431.L39Two
public import CFSG.Milestones.ASVolI.F431.ASp2
public import CFSG.Milestones.ASVolI.F431.AInvSpAll
public import CFSG.Milestones.ASVolI.F431.ATopSp

public section

namespace CFSG.ASVolI

section Sp2Facts

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpModel CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Borel252

theorem burnsideF4m_topSp2 : burnsideF4m_TopSp2 :=
  fun _ _ _ _ _ hyp => burnsideF4m_top_Sp4two hyp

theorem burnsideF4m_sp2Facts : burnsideF4m_Sp2Facts := by
  intro E _ M₁ M₂ hyp
  obtain ⟨K, _, _, _, θ, hK, hθinj, hrange, hM₁, hM₂⟩ := burnsideF4m_sp4_model_card hyp
  rw [top_inf_eq] at hM₁ hM₂
  have hK1 : Nat.card K = 2 := by rw [hK, pow_one]
  let Ψ : StatedSp 2 K ≃* E := MulEquiv.ofBijective θ ⟨hθinj, MonoidHom.range_eq_top.1 hrange⟩
  let π : StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
    MulEquiv.ofBijective (proj 2 K)
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
  obtain ⟨θ₂, hθ₂⟩ := burnsideF4gSpOne_exists_iso (K := K) hK
  have hB := burnsideF4gSpOne_borelData θ₂ hθ₂
  let Φ : antiSp K ≃* E := θ₂.trans (π.symm.trans Ψ)
  have hΦmap : ∀ (X : Subgroup (antiSp K)) (Y : Subgroup (StatedSp 2 K)),
      X.map θ₂.toMonoidHom = Y.map (proj 2 K) → X.map Φ.toMonoidHom = Y.map θ := by
    intro X Y hXY
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : θ₂.toMonoidHom x ∈ Y.map (proj 2 K) := by
        rw [← hXY]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hx'
      have hyx' : π y = θ₂ x := hyx
      refine ⟨y, hy, ?_⟩
      show θ y = Ψ (π.symm (θ₂ x))
      rw [← hyx', MulEquiv.symm_apply_apply]
      rfl
    · rintro ⟨y, hy, rfl⟩
      have hy' : proj 2 K y ∈ X.map θ₂.toMonoidHom := by
        rw [hXY]
        exact ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hy'
      have hxy' : θ₂ x = π y := hxy
      refine ⟨x, hx, ?_⟩
      show Ψ (π.symm (θ₂ x)) = θ y
      rw [hxy', MulEquiv.symm_apply_apply]
      rfl
  have hU : (antiUnipotent K).map Φ.toMonoidHom = (unipotent 2 K).map θ :=
    hΦmap _ _ hθ₂
  have hS : pCoreOf 2 (M₁ ⊓ M₂) = (unipotent 2 K).map θ := by
    rw [hM₁, hM₂, ← Subgroup.map_inf_eq _ _ θ hθinj, burnsideF4j_pCoreOf_map θ hθinj,
      burnsideF4gSpInv_Q2_inf_eq_borel, burnsideF4gSpInv_pCoreOf_borel]
  have hZS : ctr (pCoreOf 2 (M₁ ⊓ M₂)) = (ctr (unipotent 2 K)).map θ := by
    rw [hS]
    exact burnsideF4j_ctr_map θ hθinj _
  have hZ1 : ctr (oPPrime 2 M₁) = (ctr (oPPrime 2 (Q2 K 0))).map θ := by
    rw [hM₁, burnsideF4d_oPPrime_map θ hθinj, burnsideF4j_ctr_map θ hθinj]
  have hZ2 : ctr (oPPrime 2 M₂) = (burnsideF4gSpInv_Xs K).map θ := by
    rw [hM₂, burnsideF4d_oPPrime_map θ hθinj, burnsideF4j_ctr_map θ hθinj,
      burnsideF4jb_ctr_oPPrime_Q2_one]
  have hxlZ1 : θ (burnsideF4gSpInv_xl 1) ∈ ctr (oPPrime 2 M₁) := by
    rw [hZ1]
    exact ⟨_, burnsideF4m_xl_mem_ctr_oPPrime one_ne_zero, rfl⟩
  have hxsZ2 : θ (burnsideF4gSpInv_xs 1) ∈ ctr (oPPrime 2 M₂) := by
    rw [hZ2]
    exact ⟨_, burnsideF4gSpInv_mem_Xs.2 ⟨1, rfl⟩, rfl⟩
  have hcore : ∀ (R : Subgroup (antiSp K)) (j : Fin 2),
      pCoreOf 2 (Subgroup.normalizer (R : Set (antiSp K))) = R →
      (Subgroup.normalizer (R : Set (antiSp K))).map θ₂.toMonoidHom = (Q2 K j).map (proj 2 K) →
      pCoreOf 2 ((Q2 K j).map θ) = R.map Φ.toMonoidHom := by
    intro R j hR hN
    rw [← hΦmap _ _ hN, burnsideF4j_pCoreOf_map Φ.toMonoidHom Φ.injective, hR]
  have hsh0 := burnsideF4m_spShape_map Φ (burnsideF4m_shape_antiSp_one hB)
  have hshape : SpShape (pCoreOf 2 (M₁ ⊓ M₂)) ![pCoreOf 2 M₁, pCoreOf 2 M₂] := by
    rw [hS, ← hU]
    rcases burnsideF4gSpOne_parabolic_cases θ₂ hθ₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e : (![pCoreOf 2 M₁, pCoreOf 2 M₂] : Fin 2 → Subgroup E) =
          fun j => (Rrad K j).map Φ.toMonoidHom := by
        rw [hM₁, hM₂, hcore _ 0 hB.core₁ h1, hcore _ 1 hB.core₂ h2]
        funext j
        fin_cases j <;> rfl
      rw [e]
      exact hsh0
    · have e : (![pCoreOf 2 M₁, pCoreOf 2 M₂] : Fin 2 → Subgroup E) =
          ![(Rrad K 1).map Φ.toMonoidHom, (Rrad K 0).map Φ.toMonoidHom] := by
        rw [hM₁, hM₂, hcore _ 1 hB.core₁ h1, hcore _ 0 hB.core₂ h2]
        rfl
      rw [e]
      exact hsh0.swap
  refine ⟨hshape, ?_, ⟨θ (burnsideF4gSpInv_xl 1), hxlZ1, fun h =>
      burnsideF4gSpInv_xl_ne_one one_ne_zero (hθinj (h.trans (map_one θ).symm)), ?_⟩,
    ⟨θ (burnsideF4gSpInv_xs 1), hxsZ2, fun h =>
      burnsideF4gSpInv_xs_ne_one one_ne_zero (hθinj (h.trans (map_one θ).symm)), ?_⟩⟩
  ·
    intro u hu hu1 _ hu₁ hu₂
    have hu' : u ∈ (ctr (unipotent 2 K)).map θ := by
      rw [← hZS]
      exact hu
    obtain ⟨y, hy, rfl⟩ := hu'
    obtain ⟨s, t, rfl⟩ := burnsideF4m_ctr_unipotent hy
    rcases burnsideF4m_eq_zero_or_one_of_card_two hK1 s with rfl | rfl <;>
      rcases burnsideF4m_eq_zero_or_one_of_card_two hK1 t with rfl | rfl
    · exact (hu1 (by rw [burnsideF4gSpInv_xl_zero, burnsideF4gSpInv_xs_zero, one_mul,
        map_one])).elim
    · exact (hu₂ (by rw [burnsideF4gSpInv_xl_zero, one_mul]; exact hxsZ2)).elim
    · exact (hu₁ (by rw [burnsideF4gSpInv_xs_zero, mul_one]; exact hxlZ1)).elim
    · have hc : Subgroup.centralizer
          ({θ (burnsideF4gSpInv_xl 1 * burnsideF4gSpInv_xs 1)} : Set E) =
          (Subgroup.centralizer ({burnsideF4gSpInv_xl (1 : K) * burnsideF4gSpInv_xs 1} :
            Set (StatedSp 2 K))).map θ :=
        burnsideF4gSpInv_centralizer_map Ψ _
      rw [hc, hM₁, hM₂, ← Subgroup.map_inf_eq _ _ θ hθinj]
      exact Subgroup.map_mono (le_inf burnsideF4m_centralizer_mixed_le_Q0
        burnsideF4m_centralizer_mixed_le)
  · show θ (burnsideF4gSpInv_xl 1) ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂))
    rw [hZS]
    exact ⟨_, burnsideF4gSpInv_xl_mem_ctr 1, rfl⟩
  · show θ (burnsideF4gSpInv_xs 1) ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂))
    rw [hZS]
    exact ⟨_, burnsideF4gSpInv_xs_mem_ctr 1, rfl⟩

end Sp2Facts

end CFSG.ASVolI
