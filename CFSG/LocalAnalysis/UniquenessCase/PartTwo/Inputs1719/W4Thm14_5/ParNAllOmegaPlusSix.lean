module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllRankThreeBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllResidPlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O6pLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O6pParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.LineTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Adjust
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LinePlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bFinal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreNatural
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  (plusDerivedEquiv plusDerivedUnipotent)

variable {W : Type} [CommGroup W] [Finite W]

theorem nParam_eq_of_natOmegaPlusSix {H S P : Subgroup (MulAut W)} {k n : ℕ}
    (h : IsOmegaPlus ↥H 6 k ∧ NatOmegaPlus H ⊤ ⊥ 6 k) (hk : 2 ≤ k) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) : n = k := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  have hnat : IsNaturalClassicalModule H k :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  obtain ⟨-, -, -, -, -, -, -, -, hO6p, -⟩ :=
    kTab23b_holds W H k hnat hperf hS.toSylow ((hS.toSylow : Subgroup ↥H).map H.subtype)
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer)
      ((hS.toSylow.isPGroup').map H.subtype) le_rfl
  obtain ⟨-, K, _, _, hK, hreal⟩ := h.2
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have : Finite ((Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) := finite_plusAut 3
  rw [show (6 : ℕ) / 2 = 3 by norm_num] at hreal
  set ψ := (plusDerivedEquiv 3 K le_rfl).symm with hψ
  have hmodel : ∀ S' : Sylow 2 ↥H, ∃ φ : ↥(splitE K) ≃* ↥H,
      ((posUnip 3 K).subgroupOf (splitE K)).map φ.toMonoidHom = (S' : Subgroup ↥H) ∧
        KTabD.pointStab H S' =
          ((plusFlagStab K 3 ({1} : Finset ℕ)).subgroupOf (splitE K)).map φ.toMonoidHom := by
    intro S'
    obtain ⟨U, hU⟩ := KAdjE.exists_sylow_plusDerivedUnipotent K
    have : Nonempty (Fin 3 ⊕ Fin 3) := ⟨Sum.inl 0⟩
    obtain ⟨U₀, hU₀, hfix⟩ :=
      KTabA.exists_fixedLine_statedOmega_plus_single (K := K) (p := 2) (m := 3) (by norm_num)
    obtain ⟨φ, h1, h2⟩ := KAdjE.exists_mulEquiv_pointStab_eq_map_sylow hreal
      (KTabC.sylowFixedLine_of_isPGroup U₀ hU₀ _ hfix) U
      (hU ▸ KAdjE.plusDerivedUnipotent_le_omegaPlusQZero K) S'
    refine ⟨ψ.trans φ, ?_, ?_⟩
    · rw [show (ψ.trans φ).toMonoidHom = φ.toMonoidHom.comp ψ.toMonoidHom from rfl,
        ← Subgroup.map_map, hψ, KAdjE.map_symm_posUnip_subgroupOf K, ← hU]
      exact h1
    · rw [show (ψ.trans φ).toMonoidHom = φ.toMonoidHom.comp ψ.toMonoidHom from rfl,
        ← Subgroup.map_map, hψ, KAdjE.map_symm_plusFlagStab_one K]
      exact h2
  obtain ⟨φ, hφU, hφP, Q, hparQ, hUQ, hQnot, hPQ⟩ :=
    exists_model_parabolic hS hmodel hBP hPH hPnot
  have hαQ := KAdjE.plusFlagStab_alpha_le_of_parabolic hparQ hUQ hQnot
  set M := Q.map (splitE K).subtype with hMdef
  have hQM : M.subgroupOf (splitE K) = Q :=
    Subgroup.comap_map_eq_self_of_injective (splitE K).subtype_injective Q
  have hBM : borel 3 K ≤ M := by
    obtain ⟨T, hT⟩ := posUnip_isSylow (K := K) (p := 2) (r := 3) (by norm_num)
      (fun a ha => map_flag_top_ne_Xstar (K := K) (by norm_num) ha)
    have hN : Subgroup.normalizer (((posUnip 3 K).subgroupOf (splitE K) :
        Subgroup ↥(splitE K)) : Set ↥(splitE K)) ≤ Q := by
      have h := hparQ.normalizer_le T (hT ▸ hUQ)
      rw [← hT]
      exact h
    rw [normalizer_posUnip (K := K) (r := 3) (by norm_num)
      (fun a ha => map_flag_top_ne_Xstar (K := K) (by norm_num) ha), flagStab_eq_borel] at hN
    intro b hb
    exact ⟨⟨b, borel_le hb⟩, hN (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
  have hn0 : weylElt 3 K 0 ∈ M := by
    have h0 : (⟨weylElt 3 K 0, weylElt_mem 0⟩ : ↥(splitE K)) ∈
        (plusFlagStab K 3 ({2, 3} : Finset ℕ)).subgroupOf (splitE K) :=
      Subgroup.mem_subgroupOf.mpr
        (KAdjE.rankOneParabolic_le_plusFlagStab_alpha K (UC22.weylElt_mem_rankOneParabolic 3 0))
    exact ⟨_, hαQ h0, rfl⟩
  have hMI : M = plusNodeStab K (le_refl 3) {i : Fin 3 | weylElt 3 K i ∉ M} :=
    eq_plusNodeStab_of_borel_le (le_refl 3) (Subgroup.map_subtype_le Q) hBM
  have hres : Nonempty (Bar2 (Hinf P) ≃* Bar2 (Hinf M)) := by
    obtain ⟨χ₁⟩ := nonempty_bar2_hinf_equiv_of_subgroupOf_eq_map hPH φ hPQ
    obtain ⟨χ₂⟩ := nonempty_bar2_hinf_subgroupOf (Subgroup.map_subtype_le Q)
    rw [hQM] at χ₂
    exact ⟨χ₁.trans χ₂.symm⟩
  by_cases h1 : weylElt 3 K 1 ∈ M <;> by_cases h2 : weylElt 3 K 2 ∈ M
  ·
    exfalso
    have hI : {i : Fin 3 | weylElt 3 K i ∉ M} = ∅ := by
      ext i
      fin_cases i <;> simp [hn0, h1, h2]
    rw [hI, plusNodeStab_empty] at hMI
    have hQtop : Q = ⊤ := by
      rw [← hQM, hMI]
      exact Subgroup.subgroupOf_self _
    rw [hQtop, Subgroup.map_top_of_surjective _ φ.surjective] at hPQ
    have hPeq : P = H := le_antisymm hPH (Subgroup.subgroupOf_eq_top.mp hPQ)
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq hPeq hperf (KOrdNat.kOrd_pCore_eq_bot hnat)
    obtain ⟨he, K', hK'f, hK'fin, hK', ⟨e⟩⟩ := h.1
    exact not_nParam_of_isOmegaPlus_six ⟨he, K', hK'f, hK'fin, hK', ⟨χ.trans e⟩⟩ hk hN
  ·
    have hI : {i : Fin 3 | weylElt 3 K i ∉ M} = {2} := by
      ext i
      fin_cases i <;> simp [hn0, h1, h2]
    rw [hI] at hMI
    obtain ⟨χ⟩ := hres
    rw [hMI] at χ
    obtain ⟨e⟩ := nonempty_bar2_hinf_plusNodeStab_three_two (K := K)
    exact nParam_eq_of_mulEquiv_sl3 hk hK hN (χ.trans e)
  ·
    have hI : {i : Fin 3 | weylElt 3 K i ∉ M} = {1} := by
      ext i
      fin_cases i <;> simp [hn0, h1, h2]
    rw [hI] at hMI
    obtain ⟨χ⟩ := hres
    rw [hMI] at χ
    obtain ⟨e⟩ := nonempty_bar2_hinf_plusNodeStab_three_one (K := K)
    exact nParam_eq_of_mulEquiv_sl3 hk hK hN (χ.trans e)
  ·
    have hI : {i : Fin 3 | weylElt 3 K i ∉ M} = {1, 2} := by
      ext i
      fin_cases i <;> simp [hn0, h1, h2]
    have hc : ({1, 2} : Set (Fin 3))ᶜ = {0} := by
      ext i
      fin_cases i <;> simp
    rw [hI, (plusNodeStab_generation (K := K) (le_refl 3) {1, 2}).1, hc, Set.image_singleton,
      ← UC22.rankOneParabolic, ← KAdjE.plusFlagStab_alpha_eq_rankOneParabolic] at hMI
    have hQα : Q = (plusFlagStab K 3 ({2, 3} : Finset ℕ)).subgroupOf (splitE K) := by
      rw [← hQM, hMI]
    rw [hQα] at hPQ
    obtain ⟨hpar, hSQ, hnot, hleast⟩ := KAdjE.leastParabolic_map φ hφU
      (KAdjE.isParabolicTwo_plusFlagStab_alpha K) (KAdjE.posUnip_subgroupOf_le_plusFlagStab_alpha K)
      (KAdjE.not_plusFlagStab_alpha_le_one K)
      (fun P' hP' hU' hnot' => KAdjE.plusFlagStab_alpha_le_of_parabolic hP' hU' hnot')
    rw [← hPQ] at hpar hSQ hnot hleast
    rw [← hφP] at hnot hleast
    exact nParam_eq_of_least hS hPH hN hk hpar hSQ hnot hleast (hO6p h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
