module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.HardMathSupport.Lang.Proving.SLTwoThreePrime
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PermJordan
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_index_coprime_six (hblk : CFSG.AGLEmbedding.AschbacherLocalCGTBlock)
    {M H S X : Subgroup G} (hH : CFSG.QuasithinUnique.CharTwo H) (hS2 : IsPGroup 2 S)
    (hSH : S ≤ H) (hQS : CFSG.Open.pCoreOf 2 H ≤ S)
    (hSM : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ M)
    (hK : CFSG.Open.IsKGroup ↥(X ⊔ S)) (hQX : CFSG.Open.pCoreOf 2 H ≤ X) (hXH : X ≤ H)
    (hSX : S ≤ Subgroup.normalizer (X : Set G))
    (h2 : ¬ 2 ∣ ((CFSG.Open.pCoreOf 2 H).subgroupOf X).index)
    (h3 : ¬ 3 ∣ ((CFSG.Open.pCoreOf 2 H).subgroupOf X).index) : X ≤ M := by
  classical
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 H
  let H₀ : Subgroup G := X ⊔ S
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype
  have hQnormH : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hXH₀ : X ≤ H₀ := le_sup_left
  have hSH₀ : S ≤ H₀ := le_sup_right
  have hH₀H : H₀ ≤ H := sup_le hXH hSH
  have hH₀X : H₀ ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer hSX
  have hQleXS : Q ≤ X ⊓ S := le_inf hQX hQS
  have hrel1 : S.relIndex (X ⊔ S) = (X ⊓ S).relIndex X := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := S) (K := X) hSX).1
    rw [← sup_comm S X, ← inf_comm S X]
    exact h
  have hdvd1 : (S.subgroupOf (X ⊔ S)).index ∣ (Q.subgroupOf X).index := by
    have hle : Q.subgroupOf X ≤ (X ⊓ S).subgroupOf X := Subgroup.subgroupOf_mono X hQleXS
    have h := Subgroup.index_dvd_of_le hle
    have e1 : (S.subgroupOf (X ⊔ S)).index = ((X ⊓ S).subgroupOf X).index := hrel1
    rwa [e1]
  have hodd : ¬ 2 ∣ (S.subgroupOf H₀).index := fun h => h2 (h.trans hdvd1)
  have hSylow : CFSG.QuasithinUnique.IsSylowTwoOf S H₀ := ⟨hSH₀, hS2, hodd⟩
  have hQH₀ : Q ≤ H₀ := hQX.trans hXH₀
  have hQnormH₀ : H₀ ≤ Subgroup.normalizer (Q : Set G) := hH₀H.trans hQnormH
  have hQO : Q ≤ CFSG.Open.pCoreOf 2 H₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQH₀ hQnormH₀ hQ2
  have hchar₀ : CFSG.QuasithinUnique.CharTwo H₀ := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxH : x ∈ H := hH₀H hx.1
    have hxcQ : x ∈ Subgroup.centralizer (Q : Set G) :=
      Subgroup.centralizer_le (s := (Q : Set G)) (t := (CFSG.Open.pCoreOf 2 H₀ : Set G))
        (fun y hy => hQO hy) hx.2
    exact hQO (hH (Subgroup.mem_inf.mpr ⟨hxH, hxcQ⟩))
  have hcgs : CFSG.Quasithin.cgsIn H₀ S ≤ M := by
    refine iSup_le fun C => iSup_le fun hCS => iSup_le fun hC1 => iSup_le fun hCc => ?_
    exact inf_le_right.trans (hSM C hCS hC1 hCc)
  by_contra hnotX
  have hcgsne : CFSG.Quasithin.cgsIn H₀ S ≠ H₀ := by
    intro hEq
    exact hnotX ((hXH₀.trans (le_of_eq hEq.symm)).trans hcgs)
  obtain ⟨Y, hYH₀, _hYsub, hYclass, _hYnot⟩ := hblk G H₀ S hK hchar₀ hSylow hcgsne
  have hYshort : CFSG.QuasithinUnique.IsShort2 Y := hYclass.1
  haveI hXnH₀ : (X.subgroupOf H₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH₀).mpr hH₀X
  have hsupH : (X.subgroupOf H₀) ⊔ (S.subgroupOf H₀) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hXH₀ hSH₀, Subgroup.subgroupOf_self]
  have hmem : ∀ h : ↥H₀, ∃ n ∈ X.subgroupOf H₀, ∃ s ∈ S.subgroupOf H₀, n * s = h := by
    intro h
    have hh : h ∈ (X.subgroupOf H₀) ⊔ (S.subgroupOf H₀) := by
      rw [hsupH]
      exact Subgroup.mem_top h
    exact (Subgroup.mem_sup_of_normal_left (x := h)).mp hh
  let ψ : ↥S →* ↥H₀ ⧸ X.subgroupOf H₀ :=
    (QuotientGroup.mk' (X.subgroupOf H₀)).comp (Subgroup.inclusion hSH₀)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn, s, hs, hns⟩ := hmem h
    refine ⟨⟨s, hs⟩, ?_⟩
    have hm : s⁻¹ * n⁻¹ * s ∈ X.subgroupOf H₀ := by
      simpa using hXnH₀.conj_mem n⁻¹ ((X.subgroupOf H₀).inv_mem hn) s⁻¹
    have heq : (↑(n * s) : ↥H₀ ⧸ X.subgroupOf H₀) = ↑s := by
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hm
    rw [show ψ ⟨s, hs⟩ = (↑s : ↥H₀ ⧸ X.subgroupOf H₀) from rfl, ← hns]
    exact heq.symm
  have hHq : IsPGroup 2 (↥H₀ ⧸ X.subgroupOf H₀) := hS2.of_surjective ψ hψ
  let φ : ↥Y →* ↥H₀ ⧸ X.subgroupOf H₀ :=
    (QuotientGroup.mk' (X.subgroupOf H₀)).comp (Subgroup.inclusion hYH₀)
  have hker : φ.ker = (X ⊓ Y).subgroupOf Y := by
    ext y
    simp [φ, Subgroup.mem_subgroupOf]
  haveI hNYnorm : ((X ⊓ Y).subgroupOf Y).Normal := by
    rw [← hker]
    infer_instance
  have hNY2 : IsPGroup 2 (↥Y ⧸ (X ⊓ Y).subgroupOf Y) :=
    (hHq.of_injective (QuotientGroup.kerLift φ) (QuotientGroup.kerLift_injective φ)).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hker)
  have hYtop : (X ⊓ Y).subgroupOf Y = ⊤ := hYshort.1 ((X ⊓ Y).subgroupOf Y) hNY2
  have hYX : Y ≤ X := (Subgroup.subgroupOf_eq_top.mp hYtop).trans inf_le_left
  have h3Y : 3 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rcases hYclass.2 with ⟨n, hn, hLin⟩ | ⟨n, hn, hAlt⟩
    · obtain ⟨F, hF, hFfin, _hFcard, α, hα, hker, -⟩ := hLin
      letI : Field F := hF
      letI : Fintype F := hFfin
      have e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hα)
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.HardMathSupport.Lang.Proving.three_dvd_card_specialLinearGroup_two
    · obtain ⟨α, hα, hker, -⟩ := hAlt
      have hm : 3 ≤ 2 * n + 1 := by omega
      have e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* alternatingGroup (Fin (2 * n + 1)) :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hα)
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.three_dvd_card_alternatingGroup
        (α := Fin (2 * n + 1)) (by simpa using hm)
  have hYnormQ : Y ≤ Subgroup.normalizer (Q : Set G) := hYH₀.trans (hH₀H.trans hQnormH)
  have hYQ2 : IsPGroup 2 ↥(Y ⊓ Q) :=
    IsPGroup.to_le (H := Y ⊓ Q) (K := Q) hQ2 inf_le_right
  have hYQnormal : ((Y ⊓ Q).subgroupOf Y).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨hzY, hzQ⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) z).mp hzY,
        (Subgroup.mem_normalizer_iff.mp (hYnormQ hy) z).mp hzQ⟩
    · rintro ⟨hzY, hzQ⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) z).mpr hzY,
        (Subgroup.mem_normalizer_iff.mp (hYnormQ hy) z).mpr hzQ⟩
  have hYQpcore : (Y ⊓ Q).subgroupOf Y ≤ CFSG.pCore 2 ↥Y := by
    rw [CFSG.pCore_eq_iSup]
    refine le_iSup_of_le ((Y ⊓ Q).subgroupOf Y) (le_iSup_of_le hYQnormal
      (le_iSup_of_le ?_ le_rfl))
    exact hYQ2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hdvdO2 : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ∣
      Nat.card (↥Y ⧸ (Y ⊓ Q).subgroupOf Y) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_of_le hYQpcore
  have hdvdYQX : Nat.card (↥Y ⧸ (Y ⊓ Q).subgroupOf Y) ∣ (Q.subgroupOf X).index := by
    have hrelY : Q.relIndex (Y ⊔ Q) = (Y ⊓ Q).relIndex Y :=
      (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer (H := Y) (K := Q) hYnormQ).2
    have hYQindex : ((Y ⊓ Q).subgroupOf Y).index = Q.relIndex (Y ⊔ Q) := hrelY.symm
    have hYQX : Y ⊔ Q ≤ X := sup_le hYX hQX
    have hmul := Subgroup.relIndex_mul_relIndex (H := Q) (K := Y ⊔ Q) (L := X) le_sup_right
      hYQX
    have hdvd : Q.relIndex (Y ⊔ Q) ∣ Q.relIndex X :=
      ⟨(Y ⊔ Q).relIndex X, hmul.symm⟩
    rw [show Nat.card (↥Y ⧸ (Y ⊓ Q).subgroupOf Y) = ((Y ⊓ Q).subgroupOf Y).index from
      (Subgroup.index_eq_card _).symm, hYQindex]
    exact hdvd
  exact h3 (h3Y.trans (hdvdO2.trans hdvdYQX))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
