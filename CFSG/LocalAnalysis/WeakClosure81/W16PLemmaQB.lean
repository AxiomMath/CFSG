module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQBA
public import CFSG.Goldschmidt.Steps.Red2Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CfgLemmaQ

variable {M V₀ V C : Subgroup G} {h : G}

private theorem exists_mem_mul_inv_mem_centralizer_of_coboundary
    (q : CfgLemmaQ M V₀ V h C) {τ y : G} (hτ : τ ∈ V)
    (hy : y ∈ nVSub V₀ h ⊔ bSub V₀ h)
    (hyc : ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h,
      x * τ * x⁻¹ * τ⁻¹ = x * y * x⁻¹ * y⁻¹) :
    ∃ y' ∈ V₀, τ * y'⁻¹ ∈ centralizer ((V₀ ⊔ conjSubgroup V₀ h : Subgroup G) : Set G) := by
  classical
  have hgne : conjSubgroup V₀ h ≠ V₀ := by
    intro heq
    apply q.not_isPGroup
    rw [heq, sup_idem]
    exact CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian q.hyp.elemAbelian₀
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (q.hyp.h6.elemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hτV₀ : ∀ v ∈ V₀, v * τ = τ * v := fun v hv =>
    hVcomm v (q.hyp.h6.le hv) τ hτ
  have hycent : ∀ v ∈ V₀, v * y = y * v := by
    intro v hv
    have hvX : v ∈ V₀ ⊔ conjSubgroup V₀ h := Subgroup.mem_sup_left hv
    have h1 : v * τ * v⁻¹ * τ⁻¹ = 1 := by
      rw [hτV₀ v hv]; group
    have h2 : v * y * v⁻¹ * y⁻¹ = 1 := by rw [← hyc v hvX, h1]
    have h3 : v * y * v⁻¹ = y := mul_inv_eq_one.mp h2
    calc v * y = v * y * v⁻¹ * v := by group
      _ = y * v := by rw [h3]
  obtain ⟨u, hu, b, hb, hy_eq⟩ :=
    exists_mul_of_mem_sup_nVSub_bSub q.hyp.elemAbelian₀ q.hyp.isTI hgne hy
  have huV₀ : u ∈ V₀ := (mem_nVSub.mp hu).1
  have hbCent : ∀ v ∈ V₀, v * b = b * v := by
    intro v hv
    have hyv := hycent v hv
    have huv : v * u = u * v :=
      congrArg Subtype.val (q.hyp.elemAbelian₀.1.is_comm.comm ⟨v, hv⟩ ⟨u, huV₀⟩)
    have hkey : u * (v * b) = u * (b * v) := by
      calc u * (v * b) = (u * v) * b := by group
        _ = (v * u) * b := by rw [huv]
        _ = v * (u * b) := by group
        _ = v * y := by rw [← hy_eq]
        _ = y * v := hyv
        _ = (u * b) * v := by rw [hy_eq]
        _ = u * (b * v) := by group
    exact mul_left_cancel hkey
  have hb1 : b = 1 := by
    by_contra hbne
    have hbT : b ∈ conjSubgroup V₀ h := (mem_bSub.mp hb).1
    have hTI : CFSG.CGT.Timmesfeld75.IsTI (conjSubgroup V₀ h) :=
      isTI_conj q.hyp.isTI h
    have hle : V₀ ≤ Subgroup.normalizer ((conjSubgroup V₀ h : Subgroup G) : Set G) := by
      intro v hv
      exact CFSG.RankThree.GF2n.Tim77.mem_normalizer_of_commute_of_isTI hTI hbT hbne
        (hbCent v hv)
    have hnV : nVSub V₀ h = V₀ := by
      rw [nVSub]
      exact le_antisymm inf_le_left (le_inf le_rfl hle)
    exact q.prop24Setup.ne hnV
  have hyV₀ : y ∈ V₀ := by
    rw [hy_eq, hb1, mul_one]
    exact huV₀
  refine ⟨y, hyV₀, ?_⟩
  have hconj_all : ∀ z ∈ V₀ ⊔ conjSubgroup V₀ h, τ * z * τ⁻¹ = y * z * y⁻¹ := by
    intro z hz
    have h := hyc z hz
    have h' : τ * z * τ⁻¹ * z⁻¹ = y * z * y⁻¹ * z⁻¹ := by
      have hinv := congrArg Inv.inv h
      simpa [mul_inv_rev, inv_inv, mul_assoc] using hinv
    exact mul_right_cancel h'
  have hτ2 : τ * τ = 1 := by
    simpa [pow_two] using q.hyp.h6.elemAbelian.2 τ hτ
  have hy2 : y * y = 1 := by
    simpa [pow_two] using q.hyp.elemAbelian₀.2 y hyV₀
  have hconj_inv : ∀ z ∈ V₀ ⊔ conjSubgroup V₀ h, τ⁻¹ * z * τ = y⁻¹ * z * y := by
    intro z hz
    simpa [inv_eq_of_mul_eq_one_right hτ2, inv_eq_of_mul_eq_one_right hy2]
      using hconj_all z hz
  exact CFSG.Goldschmidt.Red2.mul_inv_mem_centralizer_of_conj_eq hconj_inv

section Certified


theorem exists_mem_mul_inv_mem_centralizer (q : CfgLemmaQ M V₀ V h C) {τ : G} (hτ : τ ∈ V)
    (hτY : τ ∈ centralizer ((nVSub V₀ h ⊔ bSub V₀ h : Subgroup G) : Set G))
    (hτX : ∀ x ∈ V₀ ⊔ conjSubgroup V₀ h, x * τ * x⁻¹ * τ⁻¹ ∈ nVSub V₀ h ⊔ bSub V₀ h) :
    ∃ y ∈ V₀, τ * y⁻¹ ∈ centralizer ((V₀ ⊔ conjSubgroup V₀ h : Subgroup G) : Set G) := by
  obtain ⟨y, hy, hyc⟩ := exists_mem_mul_inv_mem_centralizer_core q hτ hτY hτX
  exact exists_mem_mul_inv_mem_centralizer_of_coboundary q hτ hy hyc

end Certified

end CfgLemmaQ

end CFSG.LocalAnalysis.WeakClosure81

end
