module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1RLevel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Transfer
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaSec
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso
public import CFSG.RankThree.GF2n.Stroth80.Sec1110CMLmConsumer
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerReduce
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldFixed
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldMark
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.GroupTheory.ConjKerCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.LieType.Universal.Spin

theorem largeEvenMarking_action_mulEquiv {H R : Type} [Group H] [Group R] (e : H ≃* R)
    {A : Subgroup (MulAut H)} {C : Subgroup H}
    (hmark : (∀ a ∈ A, ∀ c ∈ C, a c ∈ C) ∧
      LargeEvenMarking ↥C (fun _ _ _ I _ θ => GGAutsInduceOn A C θ I)) :
    (∀ a ∈ A.map (MulAut.congr e).toMonoidHom,
        ∀ c ∈ C.map e.toMonoidHom, a c ∈ C.map e.toMonoidHom) ∧
      LargeEvenMarking ↥(C.map e.toMonoidHom)
        (fun _ _ _ I _ θ => GGAutsInduceOn (A.map (MulAut.congr e).toMonoidHom)
          (C.map e.toMonoidHom) θ I) := by
  classical
  let eC : ↥C ≃* ↥(C.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective C e.toMonoidHom e.injective
  have hN : ∀ a ∈ A.map (MulAut.congr e).toMonoidHom,
      ∀ c ∈ C.map e.toMonoidHom, a c ∈ C.map e.toMonoidHom := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    change MulAut.congr e a (e c) ∈ C.map e.toMonoidHom
    rw [show MulAut.congr e a (e c) = e (a c) from by simp [MulAut.congr_apply]]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (hmark.1 a ha c hc)
  have hJperf : ⁅C, C⁆ = C :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hmark.2.1)
  have hJperfR : ⁅C.map e.toMonoidHom, C.map e.toMonoidHom⁆ = C.map e.toMonoidHom := by
    rw [← Subgroup.map_commutator, hJperf]
  have hCperfR : commutator ↥(C.map e.toMonoidHom) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hJperfR)
  refine ⟨hN, ?_⟩
  obtain ⟨-, lab, hlab, hraw⟩ := hmark.2
  refine ⟨hCperfR, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R' _ I F ⟨hs, hna, θC, hθC⟩
  refine ⟨hs, hna, (centerQuotCongr eC).symm.trans θC, ?_⟩
  refine ggAutsInduceOn_map_of e ((centerQuotCongr eC).symm.trans θC) I ?_
  have hθeq : (centerQuotCongr eC).trans ((centerQuotCongr eC).symm.trans θC) = θC := by
    ext q
    change θC ((centerQuotCongr eC).symm ((centerQuotCongr eC) q)) = θC q
    rw [MulEquiv.symm_apply_apply]
  rwa [hθeq]

theorem q1OmegaQuotient_component_action
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
    (Q : (ι → K) → K) (Φ : QuadraticForm K (ι → K)) (hΦfun : ⇑Φ = Q)
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι)
    (hscal : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥)
    (hconj : Function.Injective
      (MulAut.conj : ↥(LargeEvenOmega Q) →* MulAut ↥(LargeEvenOmega Q)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (A : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega Q))))
    (hA : CFSG.Open.IsElemAbelian p A)
    (hAI : ∀ a ∈ A, a ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega Q)))
    (u : MulAut (LargeEvenProj (LargeEvenOmega Q)))
    (hu : u ∈ A) (huord : orderOf u = p)
    (J : Subgroup (LargeEvenProj (LargeEvenOmega Q)))
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u)) :
    LargeEvenMarking J (fun _ _ _ IJ _ θJ =>
      True ∧ (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧ GGAutsInduceOn A J θJ IJ) := by
  classical
  subst Q
  let e : ↥(LargeEvenOmega ⇑Φ) ≃* LargeEvenProj (LargeEvenOmega ⇑Φ) :=
    TableBOrth.projMkEquiv hscal
  let AH : Subgroup (MulAut ↥(LargeEvenOmega ⇑Φ)) :=
    A.map (MulAut.congr e.symm).toMonoidHom
  let uH : MulAut ↥(LargeEvenOmega ⇑Φ) := MulAut.congr e.symm u
  let CH : Subgroup ↥(LargeEvenOmega ⇑Φ) := J.map e.symm.toMonoidHom
  have hAH : CFSG.Open.IsElemAbelian p AH :=
    TableB.isElemAbelian_map hA (MulAut.congr e.symm).toMonoidHom
  have hAHI : ∀ a ∈ AH, a ∈ LargeEvenInnSet ↥(LargeEvenOmega ⇑Φ) := by
    rintro _ ⟨a, ha, h1⟩
    obtain ⟨r, h2⟩ := hAI a ha
    refine ⟨e.symm r, ?_⟩
    rw [← h1, ← h2]
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have huH : uH ∈ AH := ⟨u, hu, rfl⟩
  have huHord : orderOf uH = p := by
    rw [show uH = MulAut.congr e.symm u from rfl, gdf_orderOf_congr e.symm u, huord]
  have huHodd : Odd (orderOf uH) := by
    rw [huHord]
    exact hp.odd_of_ne_two hp2
  have hcommA : ∀ a ∈ A, Commute a u := by
    intro a ha
    let : IsMulCommutative ↥A := hA.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥A) (⟨u, hu⟩ : ↥A))
  have hcommH : ∀ a ∈ AH, Commute a uH := by
    rintro _ ⟨a, ha, h1⟩
    rw [← h1]
    exact (hcommA a ha).map (MulAut.congr e.symm)
  have hCH : CFSG.Assembly.IsComponentOf CH (ggAutFixedSubgroup uH) := by
    have h := isComponentOf_map_mulEquiv e.symm (CFSG.Assembly.isComponentOf_iff_open.mpr hJ)
    change CFSG.Assembly.IsComponentOf (J.map e.symm.toMonoidHom)
      ((ggAutFixedSubgroup u).map e.symm.toMonoidHom) at h
    rw [← gdf_fixed_congr e.symm u] at h
    exact h
  obtain ⟨hNH, hmarkH⟩ :=
    ggAutFixedSubgroup_inner_actor_statedOmega Φ hΦ h8 hconj hAHI huH huHodd hcommH hCH
  have hCJ : CH.map e.toMonoidHom = J := by
    ext x
    constructor
    · rintro ⟨cH, hcH, rfl⟩
      obtain ⟨j, hj, hjc⟩ := hcH
      rw [← hjc]
      simpa using hj
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, by simp⟩
  have hAJ : AH.map (MulAut.congr e).toMonoidHom = A := by
    ext a
    constructor
    · rintro ⟨aH, ⟨a', ha', h1⟩, h2⟩
      rw [← h2, ← h1]
      have hcongr : MulAut.congr e (MulAut.congr e.symm a') = a' := by
        ext x; simp [MulAut.congr_apply]
      change MulAut.congr e (MulAut.congr e.symm a') ∈ A
      rw [hcongr]
      exact ha'
    · intro ha
      exact ⟨MulAut.congr e.symm a, ⟨a, ha, rfl⟩, by ext x; simp [MulAut.congr_apply]⟩
  have htrans := largeEvenMarking_action_mulEquiv e ⟨hNH, hmarkH⟩
  rw [hAJ, hCJ] at htrans
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ hθ => ⟨trivial, htrans.1, hθ⟩) htrans.2

theorem q2OmegaQuotient_commutingLift
    {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : (ι → K) → K)
    (hscal : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥)
    (hconj : Function.Injective
      (MulAut.conj : ↥(LargeEvenOmega Q) →* MulAut ↥(LargeEvenOmega Q)))
    (A : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega Q))))
    (hA : IsMulCommutative ↥A)
    (hAI : ∀ a ∈ A, a ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega Q))) :
    ∃ σ : ↥A →* ↥(LargeEvenOmega Q), IsMulCommutative ↥σ.range ∧
      ∀ (a : ↥A) (z : ↥(LargeEvenOmega Q)),
        TableBOrth.projMkEquiv hscal (σ a * z * (σ a)⁻¹) =
          (a : MulAut (LargeEvenProj (LargeEvenOmega Q)))
            (TableBOrth.projMkEquiv hscal z) := by
  classical
  let e : ↥(LargeEvenOmega Q) ≃* LargeEvenProj (LargeEvenOmega Q) :=
    TableBOrth.projMkEquiv hscal
  let f : ↥A →* MulAut ↥(LargeEvenOmega Q) :=
    (MulAut.congr e.symm).toMonoidHom.comp A.subtype
  have hf : ∀ a : ↥A,
      f a ∈ (MulAut.conj : ↥(LargeEvenOmega Q) →* MulAut ↥(LargeEvenOmega Q)).range := by
    intro a
    obtain ⟨r, hr⟩ := hAI a a.2
    refine ⟨e.symm r, ?_⟩
    ext z
    simp [f, MulAut.congr_apply, ← hr, MulAut.conj_apply]
  let f' : ↥A →* ↥(MulAut.conj :
      ↥(LargeEvenOmega Q) →* MulAut ↥(LargeEvenOmega Q)).range :=
    f.codRestrict _ hf
  let σ : ↥A →* ↥(LargeEvenOmega Q) :=
    (MonoidHom.ofInjective hconj).symm.toMonoidHom.comp f'
  have hσ : ∀ a : ↥A, MulAut.conj (σ a) = f a := by
    intro a
    exact MonoidHom.apply_ofInjective_symm hconj (f' a)
  haveI : IsMulCommutative ↥A := hA
  refine ⟨σ, inferInstance, ?_⟩
  intro a z
  have h := DFunLike.congr_fun (hσ a) z
  change σ a * z * (σ a)⁻¹ =
    e.symm ((a : MulAut (LargeEvenProj (LargeEvenOmega Q))) (e z)) at h
  change e (σ a * z * (σ a)⁻¹) =
    (a : MulAut (LargeEvenProj (LargeEvenOmega Q))) (e z)
  rw [h, MulEquiv.apply_symm_apply]

end CFSG.StandardType

public section
namespace CFSG.StandardType.S2MathAs51642Interfaces
open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType

theorem q1RToralTransfer_DTwD_high :
    Q1RToralTransfer (fun _ _ _ => True)
      (fun p lab => CenterPrimeTo p lab ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank)
      (fun _ _ _ => True) := by
  intro p hp hp2 lab hlab hS
  obtain ⟨-, htag, hrank⟩ := hS
  rcases lab with ⟨tag, rank, n⟩
  dsimp only at htag hrank ⊢
  intro Q hQ
  rcases htag with rfl | rfl
  ·
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    rw [if_neg (by omega : rank ≠ 3)] at hQ ⊢
    obtain ⟨K, fieldK, finiteK, hK, hQK⟩ := hQ
    let : Field K := fieldK
    let : Finite K := finiteK
    have hK2 : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    let : CharP K 2 := hK2
    let Φ : QuadraticForm K (Fin rank ⊕ Fin rank → K) := TableBOrth.qPlusForm K rank
    have hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate :=
      TableBOrth.nondegenerate_qPlusForm rank
    have h8 : 8 ≤ Fintype.card (Fin rank ⊕ Fin rank) := by
      simp
      omega
    have hscal : (LargeEvenScalars (Fin rank ⊕ Fin rank) K).subgroupOf
        (LargeEvenOmega (LargeEvenQPlus K rank)) = ⊥ :=
      TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := K) (m := rank) (by omega)
    have hZraw : Subgroup.center ↥(LargeEvenOmega (LargeEvenQPlus K rank)) = ⊥ :=
      CFSG.RankThree.GF2n.Stroth80.center_statedOmega_quadPlus_eq_bot
        (m := rank) (by omega)
    have hconj : Function.Injective
        (MulAut.conj : ↥(LargeEvenOmega (LargeEvenQPlus K rank)) →*
          MulAut ↥(LargeEvenOmega (LargeEvenQPlus K rank))) :=
      (MonoidHom.ker_eq_bot_iff _).mp (CFSG.GroupTheory.ker_conj_eq_center.trans hZraw)
    refine ⟨K, fieldK, finiteK, hK, ?_⟩
    refine ⟨hQK, ?_⟩
    intro A hA hAI hToral u hu huord J hJ
    exact q1OmegaQuotient_component_action (LargeEvenQPlus K rank) Φ
      (TableBOrth.coe_qPlusForm rank) hΦ h8 hscal hconj
      hp hp2 A hA hAI u hu huord J hJ
  ·
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    rw [if_neg (by omega : rank ≠ 2), if_neg (by omega : rank ≠ 3)] at hQ ⊢
    obtain ⟨K, fieldK, finiteK, hK, b, c, hbc, hQK⟩ := hQ
    let : Field K := fieldK
    let : Finite K := finiteK
    have hK2 : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    let : CharP K 2 := hK2
    let Φ : QuadraticForm K (LargeEvenMinusIdx (rank - 1) → K) :=
      TableBOrth.qMinusForm K (rank - 1) b c
    have hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate :=
      TableBOrth.nondegenerate_qMinusForm (rank - 1) hbc
    have h8 : 8 ≤ Fintype.card (LargeEvenMinusIdx (rank - 1)) := by
      simp [LargeEvenMinusIdx]
      omega
    have hscal : (LargeEvenScalars (LargeEvenMinusIdx (rank - 1)) K).subgroupOf
        (LargeEvenOmega (LargeEvenQMinus (rank - 1) b c)) = ⊥ :=
      TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := rank - 1) b c
    have hZstd : Subgroup.center (StatedOmega (StatedQuadMinus rank K b c)) = ⊥ :=
      CFSG.StandardType.center_statedOmega_quadMinus_eq_bot (n := rank) (by omega) hbc
    have hZraw : Subgroup.center
        (LargeEvenOmega (LargeEvenQMinus (rank - 1) b c)) = ⊥ := by
      have hsub : rank - 1 + 1 = rank := Nat.sub_add_cancel (by omega)
      have eM : LargeEvenOmega (LargeEvenQMinus (rank - 1) b c) ≃*
          StatedOmega (StatedQuadMinus rank K b c) :=
        hsub ▸ CFSG.StandardType.LayerCyc.largeEvenOmegaMinusEquiv (rank - 1) K b c
      rw [← Subgroup.map_center_eq eM.symm, hZstd, Subgroup.map_bot]
    have hconj : Function.Injective
        (MulAut.conj : ↥(LargeEvenOmega (LargeEvenQMinus (rank - 1) b c)) →*
          MulAut ↥(LargeEvenOmega (LargeEvenQMinus (rank - 1) b c))) :=
      (MonoidHom.ker_eq_bot_iff _).mp (CFSG.GroupTheory.ker_conj_eq_center.trans hZraw)
    refine ⟨K, fieldK, finiteK, hK, b, c, hbc, hQK, ?_⟩
    intro A hA hAI hToral u hu huord J hJ
    exact q1OmegaQuotient_component_action (LargeEvenQMinus (rank - 1) b c) Φ
      (TableBOrth.coe_qMinusForm (rank - 1) b c) hΦ h8 hscal hconj
      hp hp2 A hA hAI u hu huord J hJ

end CFSG.StandardType.S2MathAs51642Interfaces
