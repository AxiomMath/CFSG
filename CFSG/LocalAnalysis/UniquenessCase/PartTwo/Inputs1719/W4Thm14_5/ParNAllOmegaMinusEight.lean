module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllRankThreeBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllResidMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O8mLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O8mParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.LineTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Adjust
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bFinal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreNatural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private theorem eq_inf_stabilizer_tailFlag (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (j : Fin 3)
    {M : Subgroup (T3V K ≃ₗ[K] T3V K)} (hMG : M ≤ T3G K b c)
    (hBM : tailBorel 3 (minusTailForm K b c) ≤ M)
    (hW : ∀ i : Fin 3, tailWeylElt 3 (minusTailForm K b c) (t3a0 K) i ∈ M ↔ i ≠ j) :
    M = T3G K b c ⊓ MulAction.stabilizer (T3V K ≃ₗ[K] T3V K)
      (tailFlag K (Fin 2 → K) 3 (j + 1)) := by
  have hani := t3q_anisotropic (K := K) (b := b) (c := c) hirr
  have ha0 := t3a0_ne_zero K
  set F := T3G K b c ⊓ MulAction.stabilizer (T3V K ≃ₗ[K] T3V K)
    (tailFlag K (Fin 2 → K) 3 (j + 1)) with hF
  have hFG : F ≤ T3G K b c := inf_le_left
  have hj := j.isLt
  have hBF : tailBorel 3 (minusTailForm K b c) ≤ F := by
    refine le_inf tailBorel_le fun g hg => ?_
    exact Submodule.mem_stabilizer_submodule_iff_map_eq.2
      ((mem_tailBorel.1 hg).2 (j + 1) (by omega) (by omega))
  have hWF : ∀ i : Fin 3, tailWeylElt 3 (minusTailForm K b c) (t3a0 K) i ∈ F ↔ i ≠ j := by
    intro i
    rw [hF, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      tailWeylElt_smul_tailFlag hani ha0 j i]
    exact ⟨fun h => h.2, fun h => ⟨tailWeylElt_mem _ i, h⟩⟩
  rw [tail_eq_closure_of_borel_le hani ha0 hMG hBM, tail_eq_closure_of_borel_le hani ha0 hFG hBF]
  congr 3
  ext i
  exact (hW i).trans (hWF i).symm

omit [Finite K] [CharP K 2] in
private theorem subgroupOf_inf_stabilizer_eq_orthParab (d : ℕ) :
    (T3G K b c ⊓ MulAction.stabilizer (T3V K ≃ₗ[K] T3V K)
      (tailFlag K (Fin 2 → K) 3 d)).subgroupOf (T3G K b c) =
        orthParab 3 (minusTailForm K b c) ![0, d] := by
  ext x
  rw [mem_orthParab, Fin.forall_fin_two, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Submodule.mem_stabilizer_submodule_iff_map_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, tailFlag_zero,
    Submodule.map_bot, true_and]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

variable {W : Type} [CommGroup W] [Finite W]

theorem nParam_eq_of_natOmegaMinusEight {H S P : Subgroup (MulAut W)} {k n : ℕ}
    (h : IsOmega8m ↥H k ∧ NatOmegaMinus H ⊤ ⊥ 8 k) (hk : 2 ≤ k) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) : n = k := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  have hnat : IsNaturalClassicalModule H k :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hO8m⟩ :=
    kTab23b_holds W H k hnat hperf hS.toSylow ((hS.toSylow : Subgroup ↥H).map H.subtype)
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer)
      ((hS.toSylow.isPGroup').map H.subtype) le_rfl
  obtain ⟨-, K, _, _, b, c, hK, hirr, hreal⟩ := h.2
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [show (8 : ℕ) / 2 = 4 by norm_num] at hreal
  have hani := t3q_anisotropic (K := K) (b := b) (c := c) hirr
  have ha0 := t3a0_ne_zero K
  obtain ⟨φ₀, hφ₀⟩ := KAdjE.exists_mulEquiv_omegaMinusQZero hirr
  have hmodel : ∀ S' : Sylow 2 ↥H, ∃ φ : KAdjE.OmegaMinusE K b c ≃* ↥H,
      (t3U K b c).map φ.toMonoidHom = (S' : Subgroup ↥H) ∧
        KTabD.pointStab H S' = (KAdjE.omegaMinusTailQZero K b c).map φ.toMonoidHom := by
    intro S'
    have hUle : (t3U K b c).map φ₀.symm.toMonoidHom ≤ KAdjE.omegaMinusQZero K b c := by
      rw [← KAdjE.map_symm_omegaMinusTailQZero φ₀ hφ₀]
      exact Subgroup.map_mono (KAdjE.t3U_le_omegaMinusTailQZero hirr)
    obtain ⟨U, hUc⟩ : ∃ U : Sylow 2 ↥(StatedOmega (StatedQuadMinus 4 K b c)),
        (U : Subgroup _) = (t3U K b c).map φ₀.symm.toMonoidHom :=
      ⟨(t3Sylow hirr).mapSurjective (f := φ₀.symm.toMonoidHom) φ₀.symm.surjective, by
        change ((t3Sylow hirr : Subgroup _)).map φ₀.symm.toMonoidHom = _
        rw [t3Sylow_coe]⟩
    obtain ⟨ψ, h1, h2⟩ := KAdjE.exists_mulEquiv_pointStab_eq_map_sylow hreal
      (KTabD.sylowFixedLine_omegaMinus (K := K) (m := 4) (b := b) (c := c) (by norm_num) hirr)
      U (hUc.symm ▸ hUle) S'
    refine ⟨φ₀.symm.trans ψ, ?_, ?_⟩
    · rw [show (φ₀.symm.trans ψ).toMonoidHom = ψ.toMonoidHom.comp φ₀.symm.toMonoidHom from rfl,
        ← Subgroup.map_map, ← hUc]
      exact h1
    · rw [show (φ₀.symm.trans ψ).toMonoidHom = ψ.toMonoidHom.comp φ₀.symm.toMonoidHom from rfl,
        ← Subgroup.map_map, KAdjE.map_symm_omegaMinusTailQZero φ₀ hφ₀]
      exact h2
  obtain ⟨φ, hφU, hφP, Q, hparQ, hUQ, hQnot, hPQ⟩ :=
    exists_model_parabolic hS hmodel hBP hPH hPnot
  have hαQ : t3P0 K b c ≤ Q := by
    rw [← KAdjE.omegaMinusTailQAlpha_eq_t3P0 hirr]
    exact KAdjE.omegaMinusTailQAlpha_le_of_parabolic hirr hparQ hUQ hQnot
  have hB : t3B K b c ≤ Q := by
    have h := hparQ.normalizer_le (t3Sylow hirr) (by rw [t3Sylow_coe]; exact hUQ)
    change Subgroup.normalizer
      (((t3Sylow hirr : Subgroup ↥(T3G K b c)) : Set ↥(T3G K b c))) ≤ Q at h
    rwa [t3Sylow_coe, ← t3B_eq_normalizer hirr] at h
  set M := Q.map (T3G K b c).subtype with hMdef
  have hQM : M.subgroupOf (T3G K b c) = Q :=
    Subgroup.comap_map_eq_self_of_injective (T3G K b c).subtype_injective Q
  have hMG : M ≤ T3G K b c := Subgroup.map_subtype_le Q
  have hBM : tailBorel 3 (minusTailForm K b c) ≤ M := by
    intro x hx
    exact ⟨⟨x, tailBorel_le hx⟩, hB (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hn0 : tailWeylElt 3 (minusTailForm K b c) (t3a0 K) 0 ∈ M := by
    have h0 : (⟨_, tailWeylElt_mem (t3a0 K) 0⟩ : ↥(T3G K b c)) ∈ t3P0 K b c :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (Or.inr rfl))
    exact ⟨_, hαQ h0, rfl⟩
  have hgen : M = Subgroup.closure ((tailBorel 3 (minusTailForm K b c) : Set _) ∪
      tailWeylElt 3 (minusTailForm K b c) (t3a0 K) ''
        {i : Fin 3 | tailWeylElt 3 (minusTailForm K b c) (t3a0 K) i ∈ M}) :=
    tail_eq_closure_of_borel_le hani ha0 hMG hBM
  obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_subgroupOf_eq_map hPH φ hPQ
  by_cases h1 : tailWeylElt 3 (minusTailForm K b c) (t3a0 K) 1 ∈ M <;>
    by_cases h2 : tailWeylElt 3 (minusTailForm K b c) (t3a0 K) 2 ∈ M
  ·
    exfalso
    have hall : ∀ i : Fin 3, tailWeylElt 3 (minusTailForm K b c) (t3a0 K) i ∈ M := by
      intro i
      fin_cases i
      exacts [hn0, h1, h2]
    have hEgen : T3G K b c = Subgroup.closure ((tailBorel 3 (minusTailForm K b c) : Set _) ∪
        tailWeylElt 3 (minusTailForm K b c) (t3a0 K) ''
          {i : Fin 3 | tailWeylElt 3 (minusTailForm K b c) (t3a0 K) i ∈ T3G K b c}) :=
      tail_eq_closure_of_borel_le hani ha0 le_rfl tailBorel_le
    have hME : M = T3G K b c := by
      refine le_antisymm hMG ?_
      rw [hEgen, Subgroup.closure_le]
      rintro _ (hb | ⟨i, -, rfl⟩)
      · exact hBM hb
      · exact hall i
    have hQtop : Q = ⊤ := by
      rw [← hQM, hME]
      exact Subgroup.subgroupOf_self _
    rw [hQtop, Subgroup.map_top_of_surjective _ φ.surjective] at hPQ
    have hPeq : P = H := le_antisymm hPH (Subgroup.subgroupOf_eq_top.mp hPQ)
    obtain ⟨χH⟩ := nonempty_bar2_hinf_equiv_of_eq hPeq hperf (KOrdNat.kOrd_pCore_eq_bot hnat)
    exact not_nParam_of_isOmega8m (CFSG.Blueprint.LieModel.of_mulEquiv χH.symm h.1) hN
  ·
    have hM3 := eq_inf_stabilizer_tailFlag hirr 2 hMG hBM (fun i => by
      fin_cases i <;> simp [hn0, h1, h2])
    have hQ3 : Q = orthParab 3 (minusTailForm K b c) ![0, 3] := by
      rw [← hQM, hM3]
      exact subgroupOf_inf_stabilizer_eq_orthParab 3
    rw [hQ3] at χ
    obtain ⟨e⟩ := nonempty_bar2_hinf_orthParab_minus_three hirr
    exact nParam_eq_of_mulEquiv_sl3 hk hK hN (χ.trans e)
  ·
    exfalso
    have hM2 := eq_inf_stabilizer_tailFlag hirr 1 hMG hBM (fun i => by
      fin_cases i <;> simp [hn0, h1, h2])
    have hQ2 : Q = orthParab 3 (minusTailForm K b c) ![0, 2] := by
      rw [← hQM, hM2]
      exact subgroupOf_inf_stabilizer_eq_orthParab 2
    rw [hQ2] at χ
    obtain ⟨e⟩ := nonempty_bar2_hinf_orthParab_minus_two hirr hK4
    exact not_nParam_of_mulEquiv_sl2_prod_statedOmegaMinus hirr hk hK (χ.trans e) hN
  ·
    have hJ : {i : Fin 3 | tailWeylElt 3 (minusTailForm K b c) (t3a0 K) i ∈ M} = {0} := by
      ext i
      fin_cases i <;> simp [hn0, h1, h2]
    have hQα : Q = KAdjE.omegaMinusTailQAlpha K b c := by
      rw [KAdjE.omegaMinusTailQAlpha_eq_t3P0 hirr, ← hQM, hgen, hJ, Set.image_singleton]
      rfl
    rw [hQα] at hPQ
    obtain ⟨hpar, hSQ, hnot, hleast⟩ := KAdjE.leastParabolic_map φ hφU
      (KAdjE.isParabolicTwo_omegaMinusTailQAlpha hirr) (KAdjE.t3U_le_omegaMinusTailQAlpha hirr)
      (KAdjE.not_omegaMinusTailQAlpha_le_QZero hirr)
      (fun P' hP' hU' hnot' => KAdjE.omegaMinusTailQAlpha_le_of_parabolic hirr hP' hU' hnot')
    rw [← hPQ] at hpar hSQ hnot hleast
    rw [← hφP] at hnot hleast
    exact nParam_eq_of_least hS hPH hN hk hpar hSQ hnot hleast (hO8m h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
