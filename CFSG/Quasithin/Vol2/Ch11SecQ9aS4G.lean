module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4F
public import CFSG.Quasithin.Vol2.Ch11SecSFactsCartan
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartA
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4E

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ClassicalInvolution.ModelFacts.OddCover C11P9A
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.KGNat (charP_two_of_card four_le_card exists_isCoord linModelNat
  exists_sylow_eq_conj_Usp psiSp psiSp_injective exists_eq_pre_of_isFlagW_sp eq_std_of_stable_sp
  map_stabilizer_eq perfectCore_map flag_one_eq flag_two_eq spLine spPlane gmapSp)

theorem factCartanSp4_holds : FactCartanSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₁ U₂ hU₁ hU₂ D hD
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hK4 := exists_finset_card_four (four_le_card hn hK)
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  rw [eq_map_psiSp_of_sylow hg, inf_normalizer_eq_sp hf g] at hD
  obtain ⟨x, hx, hDx⟩ := exists_eq_map_torus_sp hf g hD
  have hg' := sylow_conj_mul_sp hg (Usp_eq_unipotent (K := K) ▸ hx)
  rw [← hK] at hU₁ hU₂
  obtain ⟨S₁, hS₁, hc₁, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg' hU₁
  obtain ⟨S₂, hS₂, hc₂, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg' hU₂
  have e₁ : S₁ = spLine K := (eq_std_of_stable_sp hS₁).1 (by rw [hc₁, pow_one])
  have e₂ : S₂ = spPlane K := (eq_std_of_stable_sp hS₂).2.1 hc₂
  subst e₁ e₂
  set ψ := psiSp π (g * x) with hψdef
  have hψ : Function.Injective ψ := psiSp_injective hf (g * x)
  have hΓ₁ : gammaW H (hf.pre (gmapSp (g * x) (spLine K)).toAddSubgroup) =
      (perfectCore (Q2 K 0)).map ψ := by
    rw [gammaW, ← map_stabilizer_eq hf (g * x) (spLine K), perfectCore_map _ hψ, ← flag_one_eq]
    rfl
  have hΓ₂ : gammaW H (hf.pre (gmapSp (g * x) (spPlane K)).toAddSubgroup) =
      (perfectCore (Q2 K 1)).map ψ := by
    rw [gammaW, ← map_stabilizer_eq hf (g * x) (spPlane K), perfectCore_map _ hψ, ← flag_two_eq]
    rfl
  set Γ₁ := gammaW H (hf.pre (gmapSp (g * x) (spLine K)).toAddSubgroup) with hΓ₁def
  set Γ₂ := gammaW H (hf.pre (gmapSp (g * x) (spPlane K)).toAddSubgroup) with hΓ₂def
  have hA₁ : D ⊓ Γ₁ = ((tSa K).map torusHom).map ψ := by
    rw [hDx, hΓ₁, ← Subgroup.map_inf_eq _ _ _ hψ, torus_inf_N0 hK4]
  have hA₂ : D ⊓ Γ₂ = ((tSc K).map torusHom).map ψ := by
    rw [hDx, hΓ₂, ← Subgroup.map_inf_eq _ _ _ hψ, torus_inf_N1 hK4]
  have hC₁ : centW D Γ₁ = ((tSb K).map torusHom).map ψ := by
    rw [centW, hDx, hΓ₁, pCoreOf_map_of_injective _ hψ, map_inf_sectionCentralizer _ hψ,
      torus_inf_sc0 hK4]
  have hC₂ : centW D Γ₂ = ((tSd K).map torusHom).map ψ := by
    rw [centW, hDx, hΓ₂, pCoreOf_map_of_injective _ hψ, map_inf_sectionCentralizer _ hψ,
      torus_inf_sc1 hK4]
  have hX : D ⊓ Γ₁ ⊓ sectionCentralizer Γ₂ (pCoreOf 2 Γ₂) = ⊥ := by
    rw [hDx, hΓ₁, hΓ₂, pCoreOf_map_of_injective _ hψ, ← Subgroup.map_inf_eq _ _ _ hψ,
      map_inf_sectionCentralizer _ hψ, torus_inf_N0_inf_sc1 hK4, Subgroup.map_bot]
  have hcard : ∀ S : Subgroup (Fin 2 → Kˣ), Nat.card ↥S = Nat.card Kˣ →
      Nat.card ↥((S.map torusHom).map ψ) = 2 ^ n - 1 := fun S hS => by
    rw [Subgroup.card_map_of_injective hψ, Subgroup.card_map_of_injective torusHom_injective, hS,
      Nat.card_units, hK]
  refine ⟨⟨?_, ?_, hX, ?_, ?_, ?_, ?_⟩, fun hn2 => ?_⟩
  · rw [hC₁, hA₁, hDx, ← Subgroup.map_sup]
    exact Subgroup.map_mono torus_le_sup_ba
  · rw [hA₁, hA₂, hDx, ← Subgroup.map_sup]
    exact Subgroup.map_mono torus_le_sup_ac
  · rw [hA₁]
    exact hcard _ card_tSa
  · rw [hC₁]
    exact hcard _ card_tSb
  · rw [hA₂]
    exact hcard _ card_tSc
  · rw [hC₂]
    exact hcard _ card_tSd
  · subst hn2
    have hK' : Nat.card K = 4 := by rw [hK]; norm_num
    set Φ := ψ.comp torusHom with hΦ
    have hΦi : Function.Injective Φ := hψ.comp torusHom_injective
    have hm : ∀ S : Subgroup (Fin 2 → Kˣ), (S.map torusHom).map ψ = S.map Φ := fun S => by
      rw [Subgroup.map_map]
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := tS_pairwise_ne hK'
    have hinj := Subgroup.map_injective hΦi
    unfold FourDiag
    rw [← hΓ₁def, ← hΓ₂def, hA₁, hA₂, hC₁, hC₂, hm, hm, hm, hm]
    refine ⟨fun h => n1 (hinj h), fun h => n2 (hinj h), fun h => n3 (hinj h),
      fun h => n4 (hinj h), fun h => n5 (hinj h), fun h => n6 (hinj h), fun E hE hE3 => ?_⟩
    have hDΦ : D = Φ.range := by
      rw [hDx, torus, MonoidHom.range_eq_map, Subgroup.map_map, ← MonoidHom.range_eq_map]
    have hEm : (E.comap Φ).map Φ = E :=
      Subgroup.map_comap_eq_self (hDΦ ▸ hE)
    have hE3' : Nat.card ↥(E.comap Φ) = 3 := by
      rw [← Subgroup.card_map_of_injective hΦi, hEm, hE3]
    rcases tS_cases hK' hE3' with h | h | h | h
    · left
      rw [← hEm, h]
    · right; left
      rw [← hEm, h]
    · right; right; left
      rw [← hEm, h]
    · right; right; right
      rw [← hEm, h]

end CFSG.Quasithin.Vol2.Ch11.SecS
