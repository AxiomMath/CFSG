module

public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharOn
public import CFSG.LocalAnalysis.StandardType.GGLieParabolicCharCoatom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeAut
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.StandardType

open CFSG.AGLEmbedding Subgroup


theorem ggLieParabolicCharInputOn_reeG2 :
    GGLieParabolicCharInputOn fun d => ∃ m, d.1 = .reeG2 m := by
  rintro K _ _ d ⟨m, hm⟩ he - S X hS hSi hNX hX
  have hp : d.1.characteristic = 3 := by
    rw [hm]
    exact TauCeti.LieTypeIndex.characteristic_reeG2 m
  have hd : IsReeGTwoIndex 3 d := ⟨rfl, m, hm⟩
  rw [hp] at hS hSi ⊢
  let U : Sylow 3 K := hS.toSylow hSi
  have hUS : (U : Subgroup K) = S := IsPGroup.toSylow_coe hS hSi
  have hco : IsCoatom (normalizer (S : Set K)) := by
    have h := kFactReeBorelMaximal K d hd he U
    rwa [hUS] at h
  obtain rfl : X = normalizer (S : Set K) := (hco.le_iff.mp hNX).resolve_left hX
  obtain ⟨a, ha, -, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd he
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  have hcen : center K = ⊥ := ReeModel.center_eq_bot_of_equiv hK e
  have hC : centralizer (S : Set K) ≤ S := by
    intro x hx
    obtain ⟨u, hu, hα⟩ := kFactReeCenterCentralizer K d hd he U (MulAut.conj x) fun z hz => by
      have h1 : z * x = x * z := mem_centralizer_iff.1 hx z (hUS ▸ hz.1)
      exact mul_inv_eq_iff_eq_mul.2 h1.symm
    have hcentral : u⁻¹ * x ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h : x * g * x⁻¹ = u * g * u⁻¹ := DFunLike.congr_fun hα g
      calc g * (u⁻¹ * x) = u⁻¹ * (u * g * u⁻¹) * x := by group
        _ = u⁻¹ * (x * g * x⁻¹) * x := by rw [h]
        _ = u⁻¹ * x * g := by group
    rw [hcen, Subgroup.mem_bot, inv_mul_eq_one] at hcentral
    rw [← hcentral]
    exact hUS ▸ hu
  exact isCharacteristicP_of_normalPSubgroup_centralizer_le le_normalizer
    Subgroup.normal_in_normalizer hS fun x hx => hC hx.1

end CFSG.StandardType
