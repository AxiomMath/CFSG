module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23cNine.Generic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O6pLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LinePlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusChar
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelSplit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

private lemma single_inl_zero_eq_single_inl_zero {K : Type} [Field K] :
    (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) =
      Pi.single (Sum.inl (⟨0, by omega⟩ : Fin 3)) (1 : K) := by
  rw [show (Sum.inl (0 : Fin 3) : Fin 3 ⊕ Fin 3) = Sum.inl ⟨0, by omega⟩ from
    congrArg Sum.inl (Fin.ext rfl)]

private lemma map_mem_inf_borel {K : Type} [Field K] [Finite K] [CharP K 2]
    {t : ↥(StatedOmega (StatedQuadPlus 3 K))}
    (ht : t ∈ Hinf (omegaPlusQAlpha K) ⊓ omegaPlusQZero K) :
    omegaPlusEmb K t ∈ Hinf (plusFlagStab K 3 ({2, 3} : Finset ℕ)) ⊓
      plusFlagStab K 3 ({1} : Finset ℕ) := by
  haveI : Finite (PlusLin K) :=
    Finite.of_injective
      (fun g : PlusLin K => (g : (Fin 3 ⊕ Fin 3 → K) → (Fin 3 ⊕ Fin 3 → K)))
      DFunLike.coe_injective
  refine ⟨?_, ?_⟩
  · have h1 : omegaPlusEmb K t ∈ (Hinf (omegaPlusQAlpha K)).map (omegaPlusEmb K) :=
      Subgroup.mem_map.mpr ⟨t, ht.1, rfl⟩
    rw [Hinf_map (omegaPlusEmb K) (omegaPlusQAlpha K)] at h1
    exact CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_mono
      (map_omegaPlusQAlpha_le K) h1
  · have h2 : omegaPlusEmb K t ∈ (omegaPlusQZero K).map (omegaPlusEmb K) :=
      Subgroup.mem_map.mpr ⟨t, ht.2, rfl⟩
    rwa [map_omegaPlusQZero K] at h2

private lemma eq_one_of_mem_hinf_plusFlagStab_vecStab {K : Type} [Field K] [Finite K] [CharP K 2]
    {u : PlusLin K}
    (hu : u ∈ Hinf (plusFlagStab K 3 ({2, 3} : Finset ℕ)) ⊓
      plusFlagStab K 3 ({1} : Finset ℕ))
    (hufix : u (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) =
      Pi.single (Sum.inl (0 : Fin 3)) (1 : K))
    (hodd : Odd (orderOf u)) : u = 1 := by
  obtain ⟨e, he, c, hec, -⟩ := exists_conj_torusElt_coroot (K := K) (t := u) hu hodd
  have hefix : e (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) =
      Pi.single (Sum.inl (0 : Fin 3)) (1 : K) := by
    rw [unipotent_eq_posUnip] at he
    exact posUnip_apply_single_inl_zero (K := K) he
  have heinv : e⁻¹ (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) =
      Pi.single (Sum.inl (0 : Fin 3)) (1 : K) := by
    calc e⁻¹ (Pi.single (Sum.inl (0 : Fin 3)) (1 : K)) =
        e⁻¹ (e (Pi.single (Sum.inl (0 : Fin 3)) (1 : K))) := by rw [hefix]
      _ = Pi.single (Sum.inl (0 : Fin 3)) (1 : K) := e.symm_apply_apply _
  have hconjfix : (e * u * e⁻¹)
      (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) =
      Pi.single (Sum.inl (0 : Fin 3)) (1 : K) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, heinv, hufix, hefix]
  have hcorootfix : torusElt 3 K ![c, c⁻¹, 1]
      (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) =
      Pi.single (Sum.inl (0 : Fin 3)) (1 : K) := by
    rw [← hec]
    exact hconjfix
  have hc : c = 1 := by
    have hcoord := congrFun hcorootfix (Sum.inl (0 : Fin 3))
    rw [torusElt_apply] at hcoord
    exact Units.ext (by simpa using hcoord)
  have hvec1 : (![c, c⁻¹, 1] : Fin 3 → Kˣ) = 1 := by
    funext i
    rw [hc]
    fin_cases i <;> simp
  have h2 : e * u * e⁻¹ = 1 := by rw [hec, hvec1, map_one]
  calc u = e⁻¹ * (e * u * e⁻¹) * e := by group
    _ = e⁻¹ * 1 * e := by rw [h2]
    _ = 1 := by group

theorem omegaPlus_eq_one_of_mem_hinf_vecStab {K : Type} [Field K] [Finite K] [CharP K 2]
    {t : ↥(StatedOmega (StatedQuadPlus 3 K))}
    (ht : t ∈ Hinf (omegaPlusQAlpha K) ⊓
      KTabC.vecStab (StatedOmega (StatedQuadPlus 3 K)).subtype
        (Pi.single (Sum.inl (0 : Fin 3)) (1 : K)))
    (hodd : Odd (orderOf t)) : t = 1 := by
  have hvec := single_inl_zero_eq_single_inl_zero (K := K)
  have hzero : t ∈ omegaPlusQZero K := by
    change t ∈ KTabD.lineStab (StatedOmega (StatedQuadPlus 3 K))
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin 3)) (1 : K))
    rw [KTabD.mem_lineStab]
    refine ⟨1, ?_⟩
    rw [one_smul, ← hvec]
    simpa using ht.2
  have hodd' : Odd (orderOf (omegaPlusEmb K t)) := by
    rwa [orderOf_injective (omegaPlusEmb K) (omegaPlusEmb_injective K) t]
  have hufix : omegaPlusEmb K t (Pi.single (Sum.inl (0 : Fin 3)) (1 : K)) =
      Pi.single (Sum.inl (0 : Fin 3)) (1 : K) := by
    rw [omegaPlusEmb_apply]
    exact ht.2
  have hu : omegaPlusEmb K t = 1 :=
    eq_one_of_mem_hinf_plusFlagStab_vecStab
      (map_mem_inf_borel (K := K) ⟨ht.1, hzero⟩) hufix hodd'
  apply omegaPlusEmb_injective K
  rw [hu, map_one]

theorem kTab23cNineAt_of_realizes_omegaPlusSix {W : Type} [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hreal : (FFModel.nat (StatedOmega (StatedQuadPlus 3 K))).Realizes H ⊤ ⊥) :
    KTab23cNineAt W H := by
  let Γ : Subgroup (GL (Fin 3 ⊕ Fin 3) K) := StatedOmega (StatedQuadPlus 3 K)
  let e₀ : Fin 3 ⊕ Fin 3 → K := Pi.single (Sum.inl (0 : Fin 3)) 1
  have he0 : e₀ ≠ 0 := by
    intro h
    have h1 : (1 : K) = 0 := by simpa [e₀] using congrFun h (Sum.inl (0 : Fin 3))
    exact one_ne_zero h1
  obtain ⟨U₀, hU₀, hfix₀⟩ :=
    KTabA.exists_fixedLine_statedOmega_plus_single (K := K) (p := 2) (m := 3) (by norm_num)
  have hline : KTabC.SylowFixedLine Γ e₀ :=
    KTabC.sylowFixedLine_of_isPGroup (Γ := Γ) (K := K) (U := U₀) hU₀ e₀ hfix₀
  obtain ⟨U, hU⟩ := exists_sylow_plusDerivedUnipotent (K := K)
  have hUle : (U : Subgroup ↥Γ) ≤ KTabD.lineStab Γ e₀ := by
    rw [hU]
    exact plusDerivedUnipotent_le_omegaPlusQZero (K := K)
  have hmodel : ∀ S : Sylow 2 ↥H, ∃ φ : ↥Γ ≃* ↥H,
      (plusDerivedUnipotent 3 K).map φ.toMonoidHom = (S : Subgroup ↥H) ∧
        KTabD.pointStab H S = (omegaPlusQZero K).map φ.toMonoidHom ∧
        KSUE.fixSub H S = (KTabC.vecStab Γ.subtype e₀).map φ.toMonoidHom := by
    intro S
    obtain ⟨φ, hφU, hφP, hφF⟩ :=
      exists_mulEquiv_pointStab_fixSub_eq_map_sylow (Γ := Γ) hreal he0 hline U hUle S
    exact ⟨φ, by rw [← hU]; exact hφU, hφP, hφF⟩
  obtain ⟨hpar, hUQ, hnot, hleast⟩ := leastParabolic_omegaPlusQAlpha (K := K)
  exact kTab23cNineAt_of_model H (plusDerivedUnipotent 3 K) (omegaPlusQAlpha K)
    (omegaPlusQZero K) (KTabC.vecStab Γ.subtype e₀) hmodel hpar hUQ hnot hleast
    (fun t ht hodd => omegaPlus_eq_one_of_mem_hinf_vecStab (K := K) ht hodd)

theorem kTab23cNineAt_omegaPlusSix {W : Type} [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 6 n) :
    KTab23cNineAt W H := by
  obtain ⟨-, K, hKf, hKfin, hKcard, hreal⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have hn1 : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hKcard
    have h2 : 2 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  haveI : CharP K 2 := uc22p22d_charP_two hn1 hKcard
  exact kTab23cNineAt_of_realizes_omegaPlusSix H hreal

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTab23cNine
