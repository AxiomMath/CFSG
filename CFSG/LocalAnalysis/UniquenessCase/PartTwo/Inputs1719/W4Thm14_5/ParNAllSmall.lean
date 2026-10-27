module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNOmegaPlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bFinal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Dickson
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ProdPCore
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.ProdOvergroups
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.ProdFactors
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.Transport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GroupTheory Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem nParam_eq_of_natL2 {H S P : Subgroup (MulAut W)} {k n : ℕ}
    (h : IsL2 ↥H k ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 2 k) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) : n = k := by
  obtain ⟨hL2, -⟩ :=
    kTab23b_holds W H k (Or.inl h) hperf hS.toSylow ((hS.toSylow : Subgroup ↥H).map H.subtype)
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer)
      ((hS.toSylow.isPGroup').map H.subtype) le_rfl
  exact nParam_eq_of_forall_minimal_eq_top hS hBP hPH hcomm hN (hL2 h)

theorem nParam_eq_two_mul_of_natOmegaMinusFour {H S P : Subgroup (MulAut W)} {k n : ℕ}
    (h : IsOmegaMinus ↥H 4 k ∧ NatOmegaMinus H ⊤ ⊥ 4 k) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) : n = 2 * k := by
  obtain ⟨-, hO4m, -⟩ :=
    kTab23b_holds W H k (Or.inr (Or.inl h)) hperf hS.toSylow
      ((hS.toSylow : Subgroup ↥H).map H.subtype)
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer)
      ((hS.toSylow.isPGroup').map H.subtype) le_rfl
  exact nParam_eq_of_forall_minimal_eq_top hS hBP hPH hcomm hN (hO4m h)

private theorem nParam_eq_of_prodFirstFactor_le {H S P : Subgroup (MulAut W)} {k n : ℕ}
    {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (e : ↥H ≃* A × B)
    (hLA : IsL2 A k) (hLB : IsL2 B k) (hk : 2 ≤ k) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hSP : (hS.toSylow : Subgroup ↥H) ≤ P.subgroupOf H) (hPH : P ≤ H)
    (hN : NParam (Hinf P) n) (hF : prodFirstFactor e ≤ P.subgroupOf H) : n = k := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  set P' : Subgroup ↥H := P.subgroupOf H with hP'
  set π₂ : ↥H →* B := (MonoidHom.snd A B).comp e.toMonoidHom with hπ₂
  have hker : π₂.ker = prodFirstFactor e := by
    ext x
    rw [MonoidHom.mem_ker, mem_prodFirstFactor_iff, Subgroup.mem_prod]
    simp [hπ₂]
  have hπ₂s : Function.Surjective π₂ := fun b => ⟨e.symm (1, b), by simp [hπ₂]⟩
  by_cases hF₂ : prodSecondFactor e ≤ P'
  ·
    have hPeq : P = H := by
      refine le_antisymm hPH ?_
      have htop : P' = ⊤ := by
        rw [eq_top_iff, ← prodFirstFactor_sup_prodSecondFactor e]
        exact sup_le hF hF₂
      exact Subgroup.subgroupOf_eq_top.mp htop
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq hPeq hperf
      (by
        rw [← CFSG.pCore_map_iso 2 e.symm, KTabD.pCore_prod_eq_bot (pCore_eq_bot_of_isL2 hLA)
          (pCore_eq_bot_of_isL2 hLB), Subgroup.map_bot])
    exact kNshape_holds _ _ n k hN (Or.inr ⟨A, B, inferInstance, inferInstance, ⟨χ.trans e⟩,
      hLA, hLB⟩)
  ·
    have hproper : P'.map π₂ ≠ ⊤ := by
      intro htop
      apply hF₂
      intro x _
      obtain ⟨y, hy, hyx⟩ : π₂ x ∈ P'.map π₂ := htop ▸ Subgroup.mem_top _
      have hyinv : y⁻¹ * x ∈ π₂.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      rw [hker] at hyinv
      have := P'.mul_mem hy (hF hyinv)
      rwa [mul_inv_cancel_left] at this
    let T : Sylow 2 B := hS.toSylow.mapSurjective hπ₂s
    have hTP : (T : Subgroup B) ≤ P'.map π₂ := by
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.map_mono hSP
    have hle := l2_sylow_le_normalizer hk hLB T _ hTP hproper
    have hsolv : Group.IsSolvable ↥(P'.map π₂) :=
      haveI := KTabD.isSolvable_normalizer_sylow_of_isL2 hk hLB T
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have hinf_le : Hinf P' ≤ prodFirstFactor e := by
      have h1 : (Hinf P').map π₂ = ⊥ := by
        rw [Hinf_map π₂]
        exact Hinf_eq_bot_of_isSolvable hsolv
      have h2 := (Subgroup.map_eq_bot_iff _).mp h1
      rwa [hker] at h2
    have hperfF₁ : ⁅prodFirstFactor e, prodFirstFactor e⁆ = prodFirstFactor e := by
      have : Group.IsPerfect A := ⟨(NatParMax.isQuasisimple_of_isL2 hLA).1⟩
      have : Group.IsPerfect ↥(prodFirstFactor e) :=
        Group.IsPerfect.ofSurjective (f := (prodFirstFactorMulEquiv e).symm.toMonoidHom)
          (prodFirstFactorMulEquiv e).symm.surjective
      exact Subgroup.commutator_eq_self
    have hinf : Hinf P' = prodFirstFactor e :=
      le_antisymm hinf_le (uc22p21c_le_Hinf hF hperfF₁)
    obtain ⟨χ₁⟩ := nonempty_bar2_hinf_subgroupOf hPH
    rw [← hP', hinf] at χ₁
    obtain ⟨χ₂⟩ := nonempty_bar2_equiv_of_pCore_eq_bot (prodFirstFactorMulEquiv e)
      (pCore_eq_bot_of_isL2 hLA)
    exact kNshape_holds _ _ n k hN (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv
      (χ₁.trans χ₂).symm hLA))

theorem nParam_eq_of_natOmegaPlusFour {H S P : Subgroup (MulAut W)} {k n : ℕ}
    (h : IsOmegaPlus ↥H 4 k ∧ NatOmegaPlus H ⊤ ⊥ 4 k) (hk : 2 ≤ k) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) : n = k := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot : ¬ P ≤ stabSub (fixV S) := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  obtain ⟨A, B, hAg, hBg, ⟨eAB⟩, hLA, hLB⟩ := isL2Square_of_isOmegaPlus hk h.1
  let : Group A := hAg
  let : Group B := hBg
  have : Finite (A × B) := Finite.of_injective (eAB.symm : A × B → ↥H) eAB.symm.injective
  have : Finite A := Finite.of_surjective (MonoidHom.fst A B) (fun a => ⟨(a, 1), rfl⟩)
  have : Finite B := Finite.of_surjective (MonoidHom.snd A B) (fun b => ⟨(1, b), rfl⟩)
  have hA : ∀ (T : Sylow 2 A) (Q : Subgroup A), (T : Subgroup A) ≤ Q → Q ≠ ⊤ →
      Q ≤ normalizer (T : Set A) :=
    fun T Q h1 h2 => l2_sylow_le_normalizer hk hLA T Q h1 h2
  have hB : ∀ (T : Sylow 2 B) (Q : Subgroup B), (T : Subgroup B) ≤ Q → Q ≠ ⊤ →
      Q ≤ normalizer (T : Set B) :=
    fun T Q h1 h2 => l2_sylow_le_normalizer hk hLB T Q h1 h2
  have hcA : ∀ T : Sylow 2 A, ⁅(⊤ : Subgroup A), normalizer (T : Set A)⁆ = ⊤ :=
    fun T => commutator_top_normalizer_eq_top hk hLA T
  have hY : normalizer (((hS.toSylow : Sylow 2 ↥H) : Subgroup ↥H) : Set ↥H) ≤ P.subgroupOf H := by
    intro y hy
    have hy' : y ∈ (normalizer (S : Set (MulAut W))).subgroupOf H := by
      rw [← NatParMax.normalizer_subgroupOf_eq hS.le, ← IsSylowIn.coe_toSylow hS]
      exact hy
    exact Subgroup.mem_subgroupOf.mpr (hBP ⟨y.2, Subgroup.mem_subgroupOf.mp hy'⟩)
  have hSP' : (hS.toSylow : Subgroup ↥H) ≤ P.subgroupOf H :=
    Subgroup.le_normalizer.trans hY
  rcases NatParMax.le_normalizer_or_prodFactor_le eAB hA hB hcA hS.toSylow hY with
    hYle | hF1 | hF2
  · exfalso
    apply hPnot
    have hPN : P ≤ normalizer (S : Set (MulAut W)) := by
      refine NatParMax.le_normalizer_of_subgroupOf_le hS.le hPH ?_
      rw [← IsSylowIn.coe_toSylow hS]
      exact hYle
    exact (le_inf hPH hPN).trans (NatParMax.inf_normalizer_le_inf_stabSub H S) |>.trans inf_le_right
  · exact nParam_eq_of_prodFirstFactor_le eAB hLA hLB hk hperf hS hSP' hPH hN hF1
  · refine nParam_eq_of_prodFirstFactor_le (eAB.trans MulEquiv.prodComm) hLB hLA hk hperf hS hSP'
      hPH hN ?_
    rw [prodFirstFactor_trans_prodComm]
    exact hF2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
