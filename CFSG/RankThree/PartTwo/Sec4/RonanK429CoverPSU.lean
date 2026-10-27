module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429CoverLift
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof429
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Cfg
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open Matrix


theorem coverNormalForm_of_psu {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (hZodd : Odd (Nat.card (Subgroup.center L))) (hZ : Subgroup.center L ≠ ⊥)
    {α : MulAut L} (hα3 : α ^ 3 = 1) {f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 f F) (hq2 : 2 < 2 ^ f) (e' : L ⧸ Subgroup.center L ≃* unitaryPSU h 3)
    (hk : (stdPinnedPSU3 h).HasKind (MulAut.congr e' (centerDescend L α)) .field) :
    Nat.card (Subgroup.center L) = 3 ∧ CoverNormalForm L α := by
  set τ := MulAut.congr e' (centerDescend L α) with hτ
  have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, ← map_pow, hα3, map_one, map_one]
  have hD : τ ∉ (psuConj h).range :=
    (stdPinnedPSU3_separated h).not_mem_inndiag_of_hasKind hk (by decide) (by decide)
  obtain ⟨ρ, hρ3, H, hτH⟩ := unitary_order_three_field_descent hq2 τ hτ3 hD
  have := h.finite
  haveI : CharP F 2 := h.charP
  have hf2 : 2 ≤ f := by
    by_contra hlt
    interval_cases f <;> simp at hq2
  have hcard : Nat.card F = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* unitarySU 2 f F 3),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : unitarySU 2 f F 3 →* E, ∀ g, π (s g) = g := by
    intro E _ _ π hπ hc hodd
    obtain ⟨s, hs, -⟩ :=
      CFSG.SectionRank.EvenCover.even_unitary_three_central_odd_extension_splitting hcard hf2 hπ
        hc hodd
    exact ⟨s, hs⟩
  have hD3 : Nat.card (unitaryScalars h 3) ∣ 3 := by
    rw [card_unitaryScalars h (by norm_num)]
    exact Nat.gcd_dvd_left _ _
  obtain ⟨Ψ, hΨ, hZ3, hDcard⟩ := exists_compatible_cover hZodd hZ e' hD3 hsplit
  have hq : ModThree false (2 ^ f) := by
    rw [card_unitaryScalars h (by norm_num)] at hDcard
    have h3 : 3 ∣ 2 ^ f + 1 := hDcard ▸ Nat.gcd_dvd_right 3 _
    change 2 ^ f % 3 = 2
    omega
  set β : MulAut (unitarySU 2 f F 3) := MulAut.congr Ψ.symm α with hβ
  have : Group.IsPerfect (unitarySU 2 f F 3) :=
    Group.IsPerfect.ofSurjective (f := Ψ.symm.toMonoidHom) Ψ.symm.surjective
  have hΨβ : ∀ s, Ψ (β s) = α (Ψ s) := fun s => by
    show Ψ (Ψ.symm (α (Ψ s))) = α (Ψ s)
    exact Ψ.apply_symm_apply _
  have hdesc : MulAut.congr (suCenterEquiv h hq2) (centerDescend _ β) = τ := by
    ext x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    show suCenterEquiv h hq2 (centerDescend _ β ((suCenterEquiv h hq2).symm
        (s : unitaryPSU h 3))) = e' (centerDescend L α (e'.symm (s : unitaryPSU h 3)))
    have h1 : (suCenterEquiv h hq2).symm (s : unitaryPSU h 3) =
        (s : unitarySU 2 f F 3 ⧸ Subgroup.center (unitarySU 2 f F 3)) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have hs : e'.symm (s : unitaryPSU h 3) = (Ψ s : L ⧸ Subgroup.center L) := by
      rw [MulEquiv.symm_apply_eq]
      exact (hΨ s).symm
    rw [h1, centerDescend_mk, hs, centerDescend_mk, ← hΨβ, hΨ (β s)]
    rfl
  have hlift : ∀ γ : MulAut (unitarySU 2 f F 3),
      MulAut.congr (suCenterEquiv h hq2) (centerDescend _ γ) = τ → β = γ := by
    intro γ hγ
    have hγ' : centerDescend _ γ = centerDescend _ β :=
      (MulAut.congr _).injective (hγ.trans hdesc.symm)
    apply mulAut_eq_of_inv_mul_mem_center
    intro g
    have h1 := congrArg (fun σ : MulAut (unitarySU 2 f F 3 ⧸ Subgroup.center _) =>
      σ (g : unitarySU 2 f F 3 ⧸ Subgroup.center _)) hγ'
    simp only [centerDescend_mk] at h1
    exact QuotientGroup.eq.mp h1
  have hβγ := hlift (suConj h H * suField h ρ * (suConj h H)⁻¹) (by
    rw [hτH, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, congr_centerDescend_suConj,
      congr_centerDescend_suField])
  obtain ⟨h3f, hρc⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) h.card hρ3
  obtain ⟨f₀, rfl⟩ : 3 ∣ f := by
    have hc : Nat.Coprime 3 2 := by norm_num
    exact hc.dvd_of_dvd_mul_left h3f
  have hH : (H : GL (Fin 3) F) * frobGL ρ (H : GL (Fin 3) F)⁻¹ ∈
      glPi false 3 (2 ^ (3 * f₀)) F := by
    refine (mem_glPi_false h).mpr ?_
    rw [← mem_unitaryIsom3]
    exact mul_mem H.2 (glAut_mem_unitaryIsom3 ρ (inv_mem H.2))
  have hPi : PiField false 2 (3 * f₀) F := ⟨Nat.prime_two, h.one_le, by
    rw [h.card]
    change 2 ^ (2 * (3 * f₀)) = (2 ^ (3 * f₀)) ^ 2
    ring⟩
  refine ⟨hZ3, false, 2, 3 * f₀, F, inferInstance, hPi, hq, f₀, rfl, ρ, ?_, _, hH,
    Ψ.symm.trans (slPiFalseEquiv 2 (3 * f₀) F).symm, fun l => ?_⟩
  · rcases hρc with hc | hc
    · refine Or.inl fun c => ?_
      rw [hc, show 2 * (3 * f₀) / 3 = 2 * f₀ by omega]
      change c ^ 2 ^ (2 * f₀) = c ^ (2 ^ f₀) ^ 2
      rw [← pow_mul, mul_comm]
    · refine Or.inr fun c => ?_
      rw [hc, show 2 * (2 * (3 * f₀)) / 3 = 4 * f₀ by omega]
      change c ^ 2 ^ (4 * f₀) = c ^ ((2 ^ f₀) ^ 2) ^ 2
      rw [← pow_mul, ← pow_mul]
      ring_nf
  · have hβl : Ψ.symm (α l) = β (Ψ.symm l) := by
      apply Ψ.injective
      rw [hΨβ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    show ((Ψ.symm (α l) : unitarySU 2 (3 * f₀) F 3) : GL (Fin 3) F) =
      _ * frobGL ρ ((Ψ.symm l : unitarySU 2 (3 * f₀) F 3) : GL (Fin 3) F) * _
    rw [← conj_frobGL_conj, hβl, hβγ, MulAut.mul_apply, MulAut.mul_apply, coe_suConj,
      coe_suField, ← map_inv, coe_suConj, glAut_eq_frobGL]
    simp only [Subgroup.coe_inv, inv_inv]

end CFSG.RankThree.PartTwo.Sec4.RonanK429
