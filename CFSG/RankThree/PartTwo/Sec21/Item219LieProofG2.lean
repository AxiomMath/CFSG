module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensus
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSplit
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Hom
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Sylow
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Torus
import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS219.Tools
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.LayerCentralizer
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.RankThree.Chevalley.SteinbergCAG2ToralPrimePlane
import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofSL3
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofLayer
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import Certificates.Certificate2197
public import Certificates.Certificate3084
public import Certificates.Certificate3169
public import Certificates.Certificate6103
import CFSG.ClassicalInvolution.Balance.PassTwoFinal
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item219LieProof

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.LieType.HighestRoot CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.Steinberg.RankTwo
  CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
open scoped MatrixGroups


theorem g2_exists_model {K : Type} [Field K] [Finite K] (h31 : 3 ∣ Nat.card K - 1)
    {z : adjointGroup .G2 K} (hz1 : z ≠ 1)
    (hz : IsCentral218 (⊤ : Subgroup (adjointGroup .G2 K)) z) :
    ∃ (g : adjointGroup .G2 K) (φ : SL(3, K) →* adjointGroup .G2 K), Function.Injective φ ∧
      g⁻¹ * z * g ∈ φ.range ∧
      φ.range ≤ centralizer ({g⁻¹ * z * g} : Set (adjointGroup .G2 K)) ∧
      ∀ a ∈ centralizer ({g⁻¹ * z * g} : Set (adjointGroup .G2 K)),
        ∀ b ∈ centralizer ({g⁻¹ * z * g} : Set (adjointGroup .G2 K)),
          a * b * a⁻¹ * b⁻¹ ∈ φ.range := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := K)
  obtain ⟨P⟩ : Nonempty (Sylow 3 SL(3, K)) := inferInstance
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨-, hC, -⟩ := exact_G2_finite_order K rfl
  have hS : Nat.card SL(3, K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
    rw [LinearFlag.card_SL_eq (by norm_num), show Finset.Icc 2 3 = {2, 3} by decide,
      Finset.prod_pair (by norm_num)]
  have hP₀ : Nat.card ((P : Subgroup SL(3, K)).map φ) =
      3 ^ (Nat.card (adjointGroup .G2 K)).factorization 3 := by
    rw [Subgroup.card_map_of_injective hφinj, Sylow.card_eq_multiplicity P, hC, hS,
      factorization_three_g2_eq_sl3 h31 hq]
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS219.exists_conj_mem_center_of_isCentral218 hP₀ hz
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨z', -, hz'⟩ := Subgroup.mem_map.mp hg1
  have hz'c : ∀ p ∈ (P : Subgroup SL(3, K)), z' * p = p * z' := by
    intro p hp
    apply hφinj
    rw [map_mul, map_mul, hz']
    exact (Subgroup.mem_centralizer_iff.mp hg2 (φ p) (Subgroup.mem_map_of_mem φ hp)).symm
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq_of_dvd_card_sub_one Nat.prime_three h31
  obtain ⟨-, hω1⟩ := primitive_cube_root_of_orderOf hζ
  have hω3 : (ζ : K) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one ζ
    rw [hζ] at h
    simpa using congrArg Units.val h
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_commute_sylow hω3 hω1 P hz'c
  have hc3 : c ^ 3 = 1 := by
    have h := z'.2
    rw [hc, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  have hcomm' : ∀ A : SL(3, K), z' * A = A * z' := fun A =>
    Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hc]
      exact Matrix.scalar_commute c (fun r => Commute.all _ r) _)
  set w := g⁻¹ * z * g with hw
  refine ⟨g, φ, hφinj, ⟨z', hz'⟩, ?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show φ A * w = w * φ A
    rw [← hz', ← map_mul, ← map_mul, hcomm']
  have hdiag : ∀ i j : Fin 3, i ≠ j → (z' : Matrix (Fin 3) (Fin 3) K) i j = 0 := fun i j hij => by
    rw [hc, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
  have hwT : ((w : adjointGroup .G2 K) : ModGL .G2 K) ∈ torusGroup .G2 K := by
    rw [← hz']
    exact phi_diag_mem_torusGroup φ hφ z' hdiag
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hwT
  have hb0 : b g2ia = 1 := by
    have hT : φ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1) * w =
        w * φ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1) := by
      rw [← hz', ← map_mul, ← map_mul, hcomm']
    rw [phi_T01 φ hφ] at hT
    have hT' := congrArg (fun u : adjointGroup .G2 K => (u : ModGL .G2 K)) hT
    simp only [Subgroup.coe_mul] at hT'
    have hroot : IsRoot .G2 (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .G2)) 1) :=
      isRoot_single .G2 _
    rw [hb, CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hroot] at hT'
    set s := (rootOperatorFamily .G2).pinnedFamilySign
      (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .G2)) 1) with hs
    have h2 := rootDiagUnit_conj_pinnedX b hroot (((s : ℤ) : K) * 1)
    rw [← hT', mul_inv_cancel_right] at h2
    have h3 := pinnedX_injective .G2 K (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .G2)) 1) h2
    have hs0 : ((s : ℤ) : K) ≠ 0 := by
      intro h0
      have := (rootOperatorFamily .G2).pinnedFamilySign_mul_self K
        (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .G2)) 1)
      rw [← hs, h0, zero_mul] at this
      exact zero_ne_one this
    have hχ : (rootChar b (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .G2)) 1) : K) = 1 := by
      have : ((s : ℤ) : K) * 1 * (1 - (rootChar b
          (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .G2)) 1) : K)) = 0 := by
        linear_combination h3
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (by simpa using h) hs0
      · exact (sub_eq_zero.1 h).symm
    have hχ' := Units.ext (by rw [hχ, Units.val_one] :
      ((rootChar b (Pi.single (⟨0, by decide⟩ : Fin (Tag.rank .G2)) 1) : Kˣ) : K) =
        ((1 : Kˣ) : K))
    rwa [rootChar_pi_single] at hχ'
  have hw3 : w ^ 3 = 1 := by
    have hz3 : z' ^ 3 = 1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_pow, hc, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
        hc3, map_one])
    rw [← hz', ← map_pow, hz3, map_one]
  have hb3 : b ^ 3 = 1 := by
    apply rootDiagUnit_injective (τ := .G2) (K := K)
    change rootDiagUnitHom .G2 K (b ^ 3) = rootDiagUnitHom .G2 K 1
    rw [map_pow, map_one]
    change rootDiagUnit .G2 b ^ 3 = 1
    rw [← hb, ← Subgroup.coe_pow, hw3, Subgroup.coe_one]
  have hbs : b = Pi.mulSingle g2ir (b g2ir) := by
    funext j
    rcases fin_G2_cases j with rfl | rfl
    · rw [Pi.mulSingle_eq_of_ne (by decide), hb0]
    · rw [Pi.mulSingle_eq_same]
  have hb1 : b g2ir ≠ 1 := by
    intro h
    apply hz1
    have hb1' : b = 1 := by rw [hbs, h, Pi.mulSingle_one]
    have hw1 : w = 1 := Subtype.ext (by rw [hb, hb1', Subgroup.coe_one]; exact rootDiagUnit_one')
    calc z = g * w * g⁻¹ := by rw [hw]; group
      _ = 1 := by rw [hw1]; group
  have hζ' : orderOf (b g2ir) = 3 := by
    refine orderOf_eq_prime ?_ hb1
    have := congrFun hb3 g2ir
    simpa using this
  have hwb : ((w : adjointGroup .G2 K) : ModGL .G2 K) =
      rootDiagUnit .G2 (Pi.mulSingle g2ir (b g2ir)) := by
    rw [hb, ← hbs]
  intro x hx y hy
  have hx' := (mem_centralizer_iff_toral hwb).mp hx
  have hy' := (mem_centralizer_iff_toral hwb).mp hy
  rw [toralCentralizer_threeA hζ'] at hx' hy'
  have h := commutator_mem_of_mem_sup torus_comm
    (torusGroup_le_normalizer_rootSpan (K := K) fun α hα => isRoot_of_long hα) hx' hy'
  have hle : rootSpan .G2 K {g2a, -g2a, g2b, -g2b, g2c, -g2c} ≤
      φ.range.map (adjointGroup .G2 K).subtype := by
    refine iSup₂_le fun α hα => fun u hu => ?_
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hu
    obtain ⟨γ, hγ, rfl⟩ := exists_a2_root hα
    set s := (rootOperatorFamily .G2).pinnedFamilySign (g2CommRoot (a2pos (γ 0, γ 1)))
    refine ⟨φ (CFSG.LieType.Steinberg.SL.x 2 K γ ((s : K) * c)), ⟨_, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, hφ γ hγ, coe_a2y hγ, ← mul_assoc,
      (rootOperatorFamily .G2).pinnedFamilySign_mul_self K, one_mul]
  obtain ⟨v, hv, hve⟩ := hle h
  have : v = x * y * x⁻¹ * y⁻¹ := Subtype.ext (by
    rw [Subgroup.coe_subtype] at hve
    rw [hve]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv])
  rw [← this]
  exact hv

theorem ks219G2_holds : KS219G2 := by
  intro X _ _ n hn hev hX x hx1 hxc
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hn0 : n ≠ 0 := by omega
  let e₁ : X ≃* adjointGroup .G2 K := e.trans ((QuotientGroup.quotientMulEquivOfEq
    (center_adjointGroup_eq_bot (τ := Tag.G2) (K := K))).trans QuotientGroup.quotientBot)
  have h31 : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    obtain ⟨r, hr⟩ := hev
    have h4 : 2 ^ n % 3 = 1 := by
      rw [hr, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  have hz1 : e₁ x ≠ 1 := fun h => hx1 (e₁.injective (h.trans (map_one e₁).symm))
  have hzc := (CFSG.AGLEmbeddingD2.Wilson.Proving.isCentral218_top_map_iff e₁ x).mp hxc
  obtain ⟨g, φ, hφinj, hwN, hNC, hcomm⟩ := g2_exists_model h31 hz1 hzc
  let e₂ : X ≃* adjointGroup .G2 K := e₁.trans (MulAut.conj g⁻¹)
  have he₂ : e₂ x = g⁻¹ * e₁ x * g := by
    simp only [e₂, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hq : CFSG.IsQuasisimple φ.range := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective hφinj)
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num))
  rw [← he₂] at hwN hNC hcomm
  exact census_of_model e₂ x hwN hNC hcomm hq
    ((MonoidHom.ofInjective hφinj).symm.trans (sl3EquivOfCard hn0 hK))

end CFSG.RankThree.PartTwo.Sec21.Item219LieProof
