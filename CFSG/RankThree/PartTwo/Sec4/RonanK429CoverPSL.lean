module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429CoverLift
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBHigherLinearAction
open Matrix

theorem coverNormalForm_of_psl {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (hZodd : Odd (Nat.card (Subgroup.center L))) (hZ : Subgroup.center L ≠ ⊥)
    {α : MulAut L} (hα3 : α ^ 3 = 1) {F : Type} [Field F] [Finite F]
    (e' : L ⧸ Subgroup.center L ≃* projectiveSL 3 F)
    (hk : (stdPinnedPSL 3 F).HasKind (MulAut.congr e' (centerDescend L α)) .field) :
    Nat.card (Subgroup.center L) = 3 ∧ CoverNormalForm L α := by
  set τ := MulAut.congr e' (centerDescend L α) with hτ
  have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, ← map_pow, hα3, map_one, map_one]
  have hD : τ ∉ linearAutGroup 3 F :=
    (stdPinnedPSL_separated (n := 3) (K := F) le_rfl).not_mem_inndiag_of_hasKind hk
      (by decide) (by decide)
  obtain ⟨ρ, hρ3, H, hτH⟩ := linear_order_three_field_descent le_rfl τ hτ3 hD
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  set p := ringChar F with hpdef
  have hcardF : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨⟨f₀, hf₀⟩, hρc⟩ := eq_frobenius_pow_of_orderOf_eq_three hp n.pos hcardF hρ3
  have hF5 : 5 ≤ Nat.card F := by
    have h1 : 1 ≤ f₀ := by have := n.pos; omega
    rw [hcardF, hf₀]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp.two_le 3
      _ ≤ p ^ (3 * f₀) := Nat.pow_le_pow_right hp.pos (by omega)
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SpecialLinearGroup (Fin 3) F),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : SpecialLinearGroup (Fin 3) F →* E, ∀ g, π (s g) = g :=
    fun E _ _ π hπ hc _ =>
      CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central (m := 2) le_rfl hF5
        hπ hc
  have hD3 : Nat.card (scalars 3 F) ∣ 3 := by
    rw [card_scalars_eq_gcd F (by norm_num)]
    exact Nat.gcd_dvd_left _ _
  obtain ⟨Ψ, hΨ, hZ3, hDcard⟩ := exists_compatible_cover hZodd hZ e' hD3 hsplit
  have hq : ModThree true (p ^ (n : ℕ)) := by
    rw [card_scalars_eq_gcd F (by norm_num)] at hDcard
    have h3 : 3 ∣ Nat.card F - 1 := hDcard ▸ Nat.gcd_dvd_right 3 _
    have hpos : 1 ≤ Nat.card F := Nat.card_pos
    change p ^ (n : ℕ) % 3 = 1
    rw [← hcardF]
    omega
  set β : MulAut (SpecialLinearGroup (Fin 3) F) := MulAut.congr Ψ.symm α with hβ
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
    Group.IsPerfect.ofSurjective (f := Ψ.symm.toMonoidHom) Ψ.symm.surjective
  have hΨβ : ∀ s, Ψ (β s) = α (Ψ s) := fun s => by
    show Ψ (Ψ.symm (α (Ψ s))) = α (Ψ s)
    exact Ψ.apply_symm_apply _
  have hdesc : descendAut 3 F β = τ := by
    ext x
    obtain ⟨s, rfl⟩ := proj_surjective 3 F x
    rw [descendAut_proj]
    show proj 3 F (β s) = e' (centerDescend L α (e'.symm (proj 3 F s)))
    have hs : e'.symm (proj 3 F s) = (Ψ s : L ⧸ Subgroup.center L) := by
      rw [MulEquiv.symm_apply_eq]
      exact (hΨ s).symm
    rw [hs, centerDescend_mk, ← hΨβ]
    exact (hΨ (β s)).symm
  have hβH : β = slConjugation 3 F H * CatalogueBHigherLinearField.slFieldAut (Fin 3) F ρ *
      (slConjugation 3 F H)⁻¹ := by
    apply mulAut_eq_of_inv_mul_mem_center
    intro s
    have hγ : descendAut 3 F (slConjugation 3 F H *
        CatalogueBHigherLinearField.slFieldAut (Fin 3) F ρ * (slConjugation 3 F H)⁻¹) =
        descendAut 3 F β := by
      rw [hdesc, hτH, map_mul, map_mul, map_inv]
      rfl
    rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one,
      ← descendAut_proj, ← descendAut_proj, hγ]
  have hcoe : ∀ s : SpecialLinearGroup (Fin 3) F,
      (((slPiTrueEquiv (p ^ (n : ℕ)) F).symm s : slPi true 3 (p ^ (n : ℕ)) F) :
        GL (Fin 3) F) = Matrix.SpecialLinearGroup.toGL s := by
    intro s
    rw [← toGL_slPiTrueEquiv, MulEquiv.apply_symm_apply]
  refine ⟨hZ3, true, p, n, F, inferInstance, ⟨hp, n.pos, hcardF⟩, hq, f₀, hf₀, ρ, ?_,
    H * frobGL ρ H⁻¹, mem_glPi_true _ _, Ψ.symm.trans (slPiTrueEquiv (p ^ (n : ℕ)) F).symm,
    fun l => ?_⟩
  · rcases hρc with hc | hc
    · refine Or.inl fun c => ?_
      rw [hc, hf₀, Nat.mul_div_cancel_left _ (by norm_num)]
      rfl
    · refine Or.inr fun c => ?_
      rw [hc, hf₀, show 2 * (3 * f₀) / 3 = 2 * f₀ by omega]
      change c ^ p ^ (2 * f₀) = c ^ (p ^ f₀) ^ 2
      rw [← pow_mul, mul_comm]
  · have hβl : Ψ.symm (α l) = β (Ψ.symm l) := by
      apply Ψ.injective
      rw [hΨβ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    simp only [MulEquiv.trans_apply]
    rw [hcoe, hcoe, hβl, hβH, ← conj_frobGL_conj, MulAut.mul_apply, MulAut.mul_apply,
      toGL_slConjugation, toGL_slFieldAut, ← map_inv, toGL_slConjugation, inv_inv]

end CFSG.RankThree.PartTwo.Sec4.RonanK429
