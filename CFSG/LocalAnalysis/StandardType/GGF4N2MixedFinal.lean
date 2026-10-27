module

public import CFSG.LocalAnalysis.StandardType.GGF4N2MixedProducer
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOpp
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.LocalAnalysis.StandardType.GGF4N2InternalFive
import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeWeylLift
import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeDict
import CFSG.LocalAnalysis.StandardType.GGF4N2Calibration
import CFSG.LocalAnalysis.StandardType.GGF4N2CalibrationC1
import CFSG.LocalAnalysis.StandardType.GGF4N2MixedPairReceiver
import CFSG.LocalAnalysis.StandardType.GGF4N2MarkedUnits

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.ClassicalInvolution.WeakCT

section Mixed


theorem ggF4N2_mixed_centralImage {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    GGCentralImage .E6 0 2 (ggG0 5 B x L D J) := by
  obtain ⟨ψ₁, ψ₂, g, hgL, v, h₁, hK₁, hJ₁, hgN, hinv, hxg, h₂, hK₂, hblock,
      ⟨rho, hρT, hρker, hρx, hρ5, hρK, hρcard, hρBK⟩, hvDK, hvo, hDyv, hgy, hvM₁, hyM₂, hfin⟩ :=
    ggF4N2_mixed_centralImage_of_marked hR hNbr hL hK hF4
  refine hfin fun hM => ?_
  have ht : orderOf N2KCoordinate.coordA2 = 5 := N2KCoordinate.coordA2_order
  have ht5 : N2KCoordinate.coordA2 ^ 5 = 1 := ht ▸ pow_orderOf_eq_one _
  obtain ⟨Ψ, hΨker, hΨrange, hsl6, -, -, -, ρθ, -, -, -, -, haX, haK, ha5, hIso⟩ :=
    N2InternalFive.exists_internal_five_of_twoSL6Charts_marked_of_t ψ₁ ψ₂ h₁ h₂ hblock.symm hM
      N2KCoordinate.coordA2 ht
  refine ⟨Ψ (ρθ N2KCoordinate.coordA2), haX, hK₁ ▸ haK, ha5, fun c hc hca hBsX _ => ?_⟩
  set t := N2KCoordinate.coordA2 with ht_def
  set φ := N2E6Native.markedRankOne ρθ with hφ_def
  have hφ := N2E6Native.markedRankOne_isogeny ρθ hIso
  set ψ' := (MulAut.conj c).toMonoidHom.comp Ψ with hψ'_def
  obtain ⟨κ, hκ012, hκ3, hC1s, hC1t, h2v, hgm, hg3, hxBs, hx1, hxD⟩ :=
    F4Over.ggF4N2_mixed_native_frame hR hNbr hL hK h₁ hK₁ hinv hxg hρT hρker hρx hρ5 hρK hρBK hvDK
      hvo hDyv hgy hca
  have hκ : ∀ k, ((κ (F4Over.e5 k) : ↥Bs) : G) = ψ' (φ k t) :=
    F4Over.kappa_eq_conj_comp_markedRankOne Ψ ψ₁ hsl6 (by rw [hK₁]; exact hc.2) ρθ t κ hκ012 hκ3
  have h3y : Subgroup.zpowers ((κ (F4Over.e5 3) : ↥Bs) : G) = Subgroup.zpowers y := by
    rw [hκ3]
    exact hca
  obtain ⟨ν, hνX, hν⟩ := N2E6Native.exists_conj_perm_rankOne ψ' φ hφ ht5 (Equiv.swap 2 3)
  obtain ⟨hνN, hνκ⟩ := F4Over.exists_ggConjAut_eq_permAut κ (Equiv.swap 2 3) (ν := ν)
    (fun k => by rw [hκ, hκ]; exact hν k)
  obtain ⟨-, -, hyo, -, -, -⟩ := ggF4N2_x_data hR hNbr
  have h3 : ν * ((κ (F4Over.e5 3) : ↥Bs) : G) * ν⁻¹ = ((κ (F4Over.e5 2) : ↥Bs) : G) := by
    rw [hκ, hκ]
    simpa using hν 3
  have hνy : Subgroup.zpowers (ν * y * ν⁻¹) = Subgroup.zpowers v := by
    have hm : ∀ z : G, Subgroup.zpowers (ν * z * ν⁻¹) =
        (Subgroup.zpowers z).map (MulAut.conj ν).toMonoidHom := fun z =>
      (MonoidHom.map_zpowers (MulAut.conj ν).toMonoidHom z).symm
    rw [hm, ← h3y, ← hm, h3, h2v]
  have hgyo : orderOf (g * y * g⁻¹) = 5 := by
    rw [← SemiconjBy.orderOf_eq g (show SemiconjBy g y (g * y * g⁻¹) by
      rw [SemiconjBy]
      group)]
    exact hyo
  have hgv : Subgroup.zpowers (g * y * g⁻¹) = Subgroup.zpowers v :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgy)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hgyo, hvo])
  have hC4 := ggF4N2_map_conj_K_eq_of_zpowers_eq hR hNbr hL hK hνy hgv
  have hline := F4Over.ggF4_calibration_zpowers hR.1.2.1.2.1 hR.2.2.2.1 hF4 κ hC1s hC1t
    (m := 2) (by decide) hνN hνκ hgL hgN hC4 hgm hg3 hxBs hxD hx1 hxg
  obtain ⟨e, he, hxe⟩ : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ Subgroup.zpowers x =
      Subgroup.zpowers (((κ (F4Over.e5 2) : ↥Bs) : G) * ((κ (F4Over.e5 3) : ↥Bs) : G) ^ e) := by
    rcases hline with h | h
    · exact ⟨1, Or.inl rfl, by rw [zpow_one]; exact h⟩
    · exact ⟨-1, Or.inr rfl, by rw [zpow_neg_one]; exact h⟩
  have hu := N2E6Native.e6Isogeny_prod_rankOne φ hφ t (Pi.single 2 1 + e • Pi.single 3 1)
  have hu' := N2E6Native.e6Isogeny_prod_rankOne φ hφ t (Pi.single 2 1)
  have hprod2 : ((List.finRange 4).map fun k =>
      φ k (t ^ (Pi.single 2 1 + e • Pi.single 3 1 : Fin 4 → ℤ) k)).prod = φ 2 t * φ 3 (t ^ e) := by
    simp [List.finRange_succ, Pi.single_apply]
  have hprod1 : ((List.finRange 4).map fun k => φ k (t ^ (Pi.single 2 1 : Fin 4 → ℤ) k)).prod =
      φ 2 t := by
    simp [List.finRange_succ, Pi.single_apply]
  rw [hprod2] at hu
  rw [hprod1] at hu'
  have hψ'k : ∀ w, ψ' w = c * Ψ w * c⁻¹ := fun _ => rfl
  have hψu : c * Ψ (φ 2 t * φ 3 (t ^ e)) * c⁻¹ =
      ((κ (F4Over.e5 2) : ↥Bs) : G) * ((κ (F4Over.e5 3) : ↥Bs) : G) ^ e := by
    rw [hκ, hκ, hψ'k, hψ'k, map_mul, map_zpow, map_zpow, conj_zpow]
    group
  obtain ⟨-, hpair⟩ := ggF4N2_mixed_dict_components_of_native Ψ hΨker hΨrange c ht (i' := 2)
    (φ 2 t) hu' rfl (by decide : (2 : Fin 4) ≠ 3) he (φ 2 t * φ 3 (t ^ e)) hu (hψu ▸ hxe)
  have hνX' : ν ∈ (ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂).map
      (MulAut.conj c).toMonoidHom := by
    rw [← hΨrange, ← MonoidHom.range_comp]
    exact hνX
  have hKX : K ≤ (ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂).map
      (MulAut.conj c).toMonoidHom := by
    intro k hk
    refine ⟨k, Subgroup.mem_sup_left (hK₁ ▸ hk), ?_⟩
    have hck : k * c = c * k := Subgroup.mem_centralizer_iff.mp hc.2 k hk
    change c * k * c⁻¹ = k
    rw [← hck, mul_inv_cancel_right]
  refine ⟨Or.inl ?_, fun _ => hpair⟩
  rw [← hC4]
  rintro _ ⟨k, hk, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hνX' (hKX hk)) (Subgroup.inv_mem _ hνX')

end Mixed

end CFSG.StandardType

end
