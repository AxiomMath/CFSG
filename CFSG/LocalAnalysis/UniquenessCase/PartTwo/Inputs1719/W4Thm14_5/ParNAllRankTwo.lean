module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpBorel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNMinimal
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Adjust
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.LineTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bFinal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreNatural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLFlagMat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem sl_eq_map_flagStabilizer_of_parabolic {k : ℕ} [NeZero k] (hk : 2 ≤ k) {K : Type}
    [Field K] [Finite K] [CharP K 2] {P : Subgroup ↥(StatedSL k K)}
    (hP : IsParabolicTwo ↥(StatedSL k K) P) (hU : KAdjE.slU k K ≤ P)
    (hnot : ¬ P ≤ KAdjE.slQZero k K) :
    ∃ I ⊆ KAdjE.slAlphaCuts k,
      P = (LinearFlag.flagStabilizer k K I).map
        (specialLinearGroupEquivStatedSL k K).toMonoidHom := by
  have hk1 : 1 ≤ k := by omega
  set e := specialLinearGroupEquivStatedSL k K with he
  obtain ⟨U, hUcoe⟩ := KAdjE.exists_sylow_slU hk1 (K := K)
  have hBle : (LinearFlag.upperTriangular k K).map e.toMonoidHom ≤ P := by
    rw [he, ← KAdjE.normalizer_slU k K, ← hUcoe]
    exact hP.normalizer_le U (by rw [hUcoe]; exact hU)
  set P' := P.comap e.toMonoidHom with hP'def
  have hBle' : LinearFlag.upperTriangular k K ≤ P' := by
    rw [hP'def, ← Subgroup.map_le_iff_le_comap]
    exact hBle
  obtain ⟨hP'I, -⟩ := LinearFlag.borel_overgroups P' hBle'
  have hPmap : P'.map e.toMonoidHom = P := Subgroup.map_comap_eq_self_of_surjective e.surjective P
  have hPeq : P = (LinearFlag.flagStabilizer k K (LinearFlag.borelOvergroupCuts P')).map
      e.toMonoidHom :=
    hPmap.symm.trans (congrArg (fun Q => Q.map e.toMonoidHom) hP'I)
  have h1I : 1 ∉ LinearFlag.borelOvergroupCuts P' := by
    intro h1mem
    apply hnot
    rw [hPeq, KAdjE.slQZero_eq_map_flagStabilizer k K]
    exact Subgroup.map_mono (KAdjE.flagStabilizer_anti_G11 (Set.singleton_subset_iff.mpr h1mem))
  exact ⟨_, KAdjE.borelOvergroupCuts_subset_slAlphaCuts_G11 h1I, hPeq⟩

theorem sl3_eq_slQAlpha_or_eq_top {K : Type} [Field K] [Finite K] [CharP K 2]
    {P : Subgroup ↥(StatedSL 3 K)} (hP : IsParabolicTwo ↥(StatedSL 3 K) P)
    (hU : KAdjE.slU 3 K ≤ P) (hnot : ¬ P ≤ KAdjE.slQZero 3 K) :
    P = KAdjE.slQAlpha 3 K ∨ P = ⊤ := by
  obtain ⟨I, hI, rfl⟩ := sl_eq_map_flagStabilizer_of_parabolic (by norm_num) hP hU hnot
  have hcuts : KAdjE.slAlphaCuts 3 = {2} := by
    ext i
    simp only [KAdjE.slAlphaCuts, Set.mem_setOf_eq, Set.mem_singleton_iff]
    omega
  rw [hcuts] at hI
  rcases Set.subset_singleton_iff_eq.mp hI with rfl | rfl
  · right
    rw [eq_top_iff]
    rintro x -
    refine ⟨(specialLinearGroupEquivStatedSL 3 K).symm x,
      LinearFlag.mem_flagStabilizer.mpr fun i hi => absurd hi (Set.notMem_empty i), by simp⟩
  · left
    unfold KAdjE.slQAlpha
    rw [hcuts]

theorem sp_eq_flagStabilizer_of_parabolic (m : ℕ) {K : Type} [Field K] [Finite K] [CharP K 2]
    {P : Subgroup ↥(StatedSp (m + 2) K)} (hP : IsParabolicTwo ↥(StatedSp (m + 2) K) P)
    (hU : SymplecticFlag.unipotent (m + 2) K ≤ P)
    (hnot : ¬ P ≤ KTabD.lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)) :
    ∃ I ⊆ Set.Icc 2 (m + 2), P = SymplecticHigher.flagStabilizer (m + 2) K I := by
  obtain ⟨S, hS⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 (m + 2)
  have hSset : (S : Set ↥(StatedSp (m + 2) K)) =
      (SymplecticFlag.unipotent (m + 2) K : Set (StatedSp (m + 2) K)) := congrArg SetLike.coe hS
  have hSP : (S : Subgroup ↥(StatedSp (m + 2) K)) ≤ P := by
    intro x hx
    have hx' : x ∈ (SymplecticFlag.unipotent (m + 2) K : Set (StatedSp (m + 2) K)) := by
      rw [← hSset]
      exact hx
    exact hU hx'
  have hB : SymplecticFlag.borelSubgroup (m + 2) K ≤ P := by
    rw [← SymplecticHigher.normalizer_unipotent]
    have h := hP.normalizer_le S hSP
    rwa [hSset] at h
  obtain ⟨hPcut, -⟩ := SymplecticHigher.borel_overgroups (K := K) P hB
  refine ⟨SymplecticHigher.borelCuts K P, fun i hi => ?_, hPcut⟩
  obtain ⟨h1i, h2i⟩ := SymplecticHigher.borelCuts_le P i hi
  have hne : i ≠ 1 := by
    rintro rfl
    apply hnot
    rw [hPcut, KAdjE.lineStab_statedSp_eq_flagStabilizer]
    intro g hg
    rw [SymplecticHigher.mem_flagStabilizer] at hg
    rw [SymplecticHigher.mem_flagStabilizer]
    intro j hj
    rw [Set.mem_singleton_iff] at hj
    subst hj
    exact hg 1 hi
  exact Set.mem_Icc.mpr ⟨by omega, h2i⟩

variable {W : Type} [CommGroup W] [Finite W]

theorem nParam_eq_of_natSL3 {H S P : Subgroup (MulAut W)} {k n : ℕ}
    (h : IsSLn ↥H 3 k ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 3 k) (hk : 2 ≤ k)
    (hperf : ⁅H, H⁆ = H) (hS : IsSylowIn 2 S H)
    (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) : n = k := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  have hnat : IsNaturalClassicalModule H k := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  obtain ⟨-, -, -, -, hSL3, -⟩ :=
    kTab23b_holds W H k hnat hperf hS.toSylow ((hS.toSylow : Subgroup ↥H).map H.subtype)
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer)
      ((hS.toSylow.isPGroup').map H.subtype) le_rfl
  obtain ⟨K, _, _, hK, hreal⟩ := h.2
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hmodel : ∀ S' : Sylow 2 ↥H, ∃ φ : ↥(StatedSL 3 K) ≃* ↥H,
      (KAdjE.slU 3 K).map φ.toMonoidHom = (S' : Subgroup ↥H) ∧
        KTabD.pointStab H S' = (KAdjE.slQZero 3 K).map φ.toMonoidHom := by
    intro S'
    obtain ⟨U, hU⟩ := KAdjE.exists_sylow_slU (k := 3) (K := K) (by norm_num)
    obtain ⟨φ, h1, h2⟩ := KAdjE.exists_mulEquiv_pointStab_eq_map_sylow hreal
      (KTabD.sylowFixedLine_statedSL (K := K) (d := 3) (by norm_num)) U
      (hU ▸ KAdjE.slU_le_slQZero) S'
    exact ⟨φ, hU ▸ h1, h2⟩
  obtain ⟨φ, hφU, hφP, Q, hparQ, hUQ, hQnot, hPQ⟩ :=
    exists_model_parabolic hS hmodel hBP hPH hPnot
  rcases sl3_eq_slQAlpha_or_eq_top hparQ hUQ hQnot with rfl | rfl
  · obtain ⟨hpar, hSQ, hnot, hleast⟩ := KAdjE.leastParabolic_map φ hφU
      (KAdjE.isParabolicTwo_slQAlpha (by norm_num)) (KAdjE.slU_le_slQAlpha 3 K)
      (KAdjE.not_slQAlpha_le_slQZero (by norm_num))
      (fun P' hP' hU' hnot' => KAdjE.slQAlpha_le_of_parabolic (by norm_num) hP' hU' hnot')
    rw [← hPQ] at hpar hSQ hnot hleast
    rw [← hφP] at hnot hleast
    exact nParam_eq_of_least hS hPH hN hk hpar hSQ hnot hleast (hSL3 h)
  · have hPeq : P = H := by
      refine le_antisymm hPH ?_
      rw [Subgroup.map_top_of_surjective _ φ.surjective] at hPQ
      exact Subgroup.subgroupOf_eq_top.mp hPQ
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq hPeq hperf (KOrdNat.kOrd_pCore_eq_bot hnat)
    obtain ⟨K', hK'f, hK'fin, hK', ⟨e⟩⟩ := h.1
    exact nParam_eq_of_isSL3 hN (isSL3_of_isSLn_three ⟨K', hK'f, hK'fin, hK', ⟨χ.trans e⟩⟩ hk)

theorem nParam_eq_of_natSp4 {H S P : Subgroup (MulAut W)} {k n : ℕ}
    (h : IsSp4 ↥H k ∧ NatSpn H ⊤ ⊥ 4 k) (hk : 2 ≤ k) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hBP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hcomm : commSub (fixV S) (Hinf P) ≠ ⊥) (hN : NParam (Hinf P) n) : n = k := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hSP : S ≤ P := fun s hs => hBP ⟨hS.le hs, Subgroup.le_normalizer hs⟩
  have hPnot := not_le_stabSub_of_commSub_ne_bot hS hSP hPH hcomm
  have hnat : IsNaturalClassicalModule H k := Or.inr (Or.inr (Or.inr (Or.inl h)))
  obtain ⟨-, -, -, hSp4, -⟩ :=
    kTab23b_holds W H k hnat hperf hS.toSylow ((hS.toSylow : Subgroup ↥H).map H.subtype)
      ((Subgroup.map_subtype_le _).trans Subgroup.le_normalizer)
      ((hS.toSylow.isPGroup').map H.subtype) le_rfl
  obtain ⟨-, K, _, _, hK, hreal⟩ := h.2
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hmodel : ∀ S' : Sylow 2 ↥H, ∃ φ : ↥(StatedSp 2 K) ≃* ↥H,
      (SymplecticFlag.unipotent 2 K).map φ.toMonoidHom = (S' : Subgroup ↥H) ∧
        KTabD.pointStab H S' =
          (KTabD.lineStab (StatedSp 2 K) (Pi.single (Sum.inl 0) 1)).map φ.toMonoidHom := by
    intro S'
    obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 2
    have hUle : (U : Subgroup ↥(StatedSp 2 K)) ≤
        KTabD.lineStab (StatedSp 2 K) (Pi.single (Sum.inl 0) 1) := by
      rw [hU]
      exact KAdjE.unipotent_le_lineStab 0 K
    obtain ⟨φ, h1, h2⟩ := KAdjE.exists_mulEquiv_pointStab_eq_map_sylow hreal
      (KTabD.sylowFixedLine_statedSp (K := K) 2) U hUle S'
    exact ⟨φ, hU ▸ h1, h2⟩
  obtain ⟨φ, hφU, hφP, Q, hparQ, hUQ, hQnot, hPQ⟩ :=
    exists_model_parabolic hS hmodel hBP hPH hPnot
  obtain ⟨I, hI, rfl⟩ := sp_eq_flagStabilizer_of_parabolic 0 hparQ hUQ hQnot
  have hI2 : Set.Icc 2 2 = ({2} : Set ℕ) := by
    ext i
    simp only [Set.mem_Icc, Set.mem_singleton_iff]
    omega
  rw [hI2] at hI
  rcases Set.subset_singleton_iff_eq.mp hI with rfl | rfl
  ·
    have htop : SymplecticHigher.flagStabilizer 2 K ∅ = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      rw [SymplecticHigher.mem_flagStabilizer]
      intro i hi
      exact absurd hi (Set.notMem_empty i)
    have hPeq : P = H := by
      refine le_antisymm hPH ?_
      rw [htop, Subgroup.map_top_of_surjective _ φ.surjective] at hPQ
      exact Subgroup.subgroupOf_eq_top.mp hPQ
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq hPeq hperf (KOrdNat.kOrd_pCore_eq_bot hnat)
    exact nParam_eq_of_isSp4 hN (CFSG.Blueprint.LieModel.of_mulEquiv χ.symm h.1) hk
  ·
    have hα : SymplecticHigher.flagStabilizer 2 K {2} =
        SymplecticHigher.flagStabilizer (0 + 2) K (Set.Icc 2 (0 + 2)) := by
      rw [hI2]
    obtain ⟨hpar, hSQ, hnot, hleast⟩ := KAdjE.leastParabolic_map φ hφU
      (KAdjE.isParabolicTwo_flagStabilizer_alpha 0 K) (KAdjE.unipotent_le_flagStabilizer_alpha 0 K)
      (KAdjE.not_flagStabilizer_alpha_le_lineStab 0 K)
      (fun P' hP' hU' hnot' => KAdjE.flagStabilizer_alpha_le_of_parabolic 0 hP' hU' hnot')
    rw [← hα, ← hPQ] at hpar hSQ hnot hleast
    rw [← hφP] at hnot hleast
    exact nParam_eq_of_least hS hPH hN hk hpar hSQ hnot hleast (hSp4 h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
