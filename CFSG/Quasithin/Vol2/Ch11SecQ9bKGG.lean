module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts12
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartA
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4D
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.Quasithin.Vol2.Ch11.SecS CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.KGNat (charP_two_of_card four_le_card exists_isCoord linModelNat
  exists_sylow_eq_conj_Usp psiSp psiSp_apply psiSp_injective exists_eq_pre_of_isFlagW_sp
  eq_std_of_stable_sp map_stabilizer_eq perfectCore_map flag_one_eq spLine gmapSp mem_gmapSp
  mat_inv_mulVec)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

theorem factCartanPointSp4_holds : FactCartanPointSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₁ hU₁ D hD
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hP
  rw [eq_map_psiSp_of_sylow hg, inf_normalizer_eq_sp hf g] at hD
  obtain ⟨x, hx, hDx⟩ := exists_eq_map_torus_sp hf g hD
  have hg' := sylow_conj_mul_sp hg (Usp_eq_unipotent (K := K) ▸ hx)
  rw [← hK] at hU₁
  obtain ⟨S₁, hS₁, hc₁, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg' hU₁
  have e₁ : S₁ = spLine K := (eq_std_of_stable_sp hS₁).1 (by rw [hc₁, pow_one])
  subst e₁
  set ψ := psiSp π (g * x) with hψdef
  have hψ : Function.Injective ψ := psiSp_injective hf (g * x)
  have hΓ₁ : gammaW H (hf.pre (gmapSp (g * x) (spLine K)).toAddSubgroup) =
      (perfectCore (Q2 K 0)).map ψ := by
    rw [gammaW, ← map_stabilizer_eq hf (g * x) (spLine K), perfectCore_map _ hψ, ← flag_one_eq]
    rfl
  have hC₁ : centW D (gammaW H (hf.pre (gmapSp (g * x) (spLine K)).toAddSubgroup)) =
      ((tSb K).map torusHom).map ψ := by
    rw [centW, hDx, hΓ₁, pCoreOf_map_of_injective _ hψ, map_inf_sectionCentralizer _ hψ,
      torus_inf_sc0 hK4]
  intro d hd htriv
  rw [hC₁] at hd
  obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hd
  obtain ⟨w, hw⟩ := hf.surj (mat 2 K (g * x) *ᵥ Pi.single (Sum.inl 0) 1)
  have hw1 : w ∈ hf.pre (gmapSp (g * x) (spLine K)).toAddSubgroup := by
    show f w ∈ gmapSp (g * x) (spLine K)
    rw [mem_gmapSp, hw, mat_inv_mulVec]
    exact ⟨by simp, by simp, by simp⟩
  have h1 := htriv w hw1
  rw [← hf.ker, hf.map_mul_inv, hψdef, psiSp_apply, hf.act4, hw, sub_eq_zero,
    Matrix.mulVec_mulVec, ← map_mul,
    show g * x * torusHom t * (g * x)⁻¹ * (g * x) = g * x * torusHom t by group, map_mul,
    ← Matrix.mulVec_mulVec] at h1
  have h2 := congrArg (fun v => mat 2 K (g * x)⁻¹ *ᵥ v) h1
  simp only [mat_inv_mulVec] at h2
  have h3 := congrFun h2 (Sum.inl 0)
  rw [show mat 2 K (torusHom t) = spMat (torusHom t) from rfl, spMat_torusHom,
    Matrix.mulVec_diagonal] at h3
  have ht0 : t 0 = 1 := Units.ext (by simpa using h3)
  have ht1 : t 1 = 1 := mem_tSb.mp ht
  rw [show t = 1 from eq_of_fin_two (by rw [ht0]; rfl) (by rw [ht1]; rfl), map_one, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecA
