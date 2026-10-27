module

public import CFSG.RankThree.PartTwo.KFacts.K71InnerSp4
public import CFSG.RankThree.PartTwo.KFacts.K71Lift
public import CFSG.RankThree.PartTwo.Sec8.Steps
import CFSG.RankThree.PartTwo.Sec8.Outer
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Adapters.RankTwoModelTransports (statedProjEquivMapMk)

variable {G : Type} [Group G] [Finite G]

theorem fieldAut_proj_planeSp_ordThreeSL {F : Type} [Field F] [CharP F 2] (σ : F ≃+* F)
    (i : Fin 2) :
    fieldAut 2 F σ (proj 2 F (planeSp i (ordThreeSL F))) = proj 2 F (planeSp i (ordThreeSL F)) :=
  (mem_range_proj_spIncl_iff σ _).mp ⟨planeSp i (ordThreeSL _), by
    rw [MonoidHom.comp_apply, spIncl_planeSp_ordThreeSL]⟩

theorem exists_data83_of_sp4 {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
    (h : Sec8.Hyp81 G A c L a) {n : ℕ} (hn : Odd n)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 (3 * n)))) :
    ∃ (A₀ : Subgroup G) (d : G), Sec8.Data83 G c L a A₀ d n := by
  obtain ⟨eL⟩ := id hL
  set F := GaloisField 2 (3 * n) with hFdef
  have hn0 : n ≠ 0 := by
    obtain ⟨k, rfl⟩ := hn
    omega
  have hF : Nat.card F = 2 ^ (3 * n) := GaloisField.card 2 (3 * n) (by omega)
  have hf : 2 ≤ 3 * n := by omega
  set e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 F) :=
    eL.trans (statedProjEquivMapMk (StatedSp 2 F)).symm with he
  have ha : a ∈ Subgroup.normalizer (L : Set G) := h.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hca : c * a = a * c :=
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨c, h.mem_A⟩ ⟨a, h.a_mem⟩)
  have hout : InducesOuterTheta a L := h.inducesOuterTheta
  have hout' := h.not_isInnerAut_induced
  have hcL : L ≤ Subgroup.centralizer {c} := by
    obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
    exact Subgroup.map_subtype_le _
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    by_contra hz1
    exact false_of_center_eq_bot_of_mulEquiv e
      (CFSG.QuasithinUnique.Lin2.Five.center_statedProj_eq_bot F) hz hz1
  set α := inducedAutHom L e ⟨a, ha⟩ with hαdef
  have hα3 : α ^ 3 = 1 := inducedAutHom_pow_eq_one L e ha ha3
  have hnotin : α ∉ (conjAut 2 F).range := by
    rintro ⟨B, hB⟩
    apply (not_isInnerAut_inducedAutHom_iff L e ha).mpr hout
    rw [← hαdef, ← hB]
    exact conjAut_mem_inner_of_charTwo B
  obtain ⟨σ, -, H, hαH⟩ := sp4_even_order_three_field_descent α hα3 hnotin
  set φ : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
    (MulEquiv.ofBijective (proj 2 F) ⟨proj_injective_of_charTwo, proj_surjective⟩).trans
      (conjAut 2 F H) with hφ
  have hφapp : ∀ g, φ g = conjAut 2 F H (proj 2 F g) := fun g => rfl
  have hfixα : ∀ i : Fin 2, α (φ (planeSp i (ordThreeSL F))) = φ (planeSp i (ordThreeSL F)) := by
    intro i
    have hcc : ∀ y, (conjAut 2 F H)⁻¹ (conjAut 2 F H y) = y := fun y => by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [hαH, hφapp, MulAut.mul_apply, MulAut.mul_apply, hcc, fieldAut_proj_planeSp_ordThreeSL]
  set y₁ := e.symm (φ (sp4T F)) with hy₁def
  set y₂ := e.symm (φ (sp4T' F)) with hy₂def
  have hmemC : ∀ i : Fin 2, e.symm (φ (planeSp i (ordThreeSL F))) ∈
      Sec8.barCentralizer (Subgroup.zpowers a) L := by
    intro i
    rw [mem_barCentralizer_zpowers_iff ha]
    apply e.injective
    have h1 : e (thetaQuotMulAut L (compAction L ⟨a, ha⟩) (e.symm (φ (planeSp i (ordThreeSL F))))) =
        α (φ (planeSp i (ordThreeSL F))) := rfl
    rw [h1, hfixα, MulEquiv.apply_symm_apply]
  have hinjφ : Function.Injective fun g => e.symm (φ g) := e.symm.injective.comp φ.injective
  have hy₁3 : y₁ ^ 3 = 1 := by rw [hy₁def, ← map_pow, ← map_pow, sp4T_pow_three, map_one, map_one]
  have hy₂3 : y₂ ^ 3 = 1 := by rw [hy₂def, ← map_pow, ← map_pow, sp4T'_pow_three, map_one, map_one]
  have hy : y₁ * y₂ = y₂ * y₁ := by
    rw [hy₁def, hy₂def, ← map_mul, ← map_mul, ← map_mul, ← map_mul, sp4T_commute]
  have hy₁1 : y₁ ≠ 1 := by
    intro h1
    apply sp4T_ne_one F
    apply hinjφ
    change e.symm (φ (sp4T F)) = e.symm (φ 1)
    rw [← hy₁def, h1, map_one, map_one]
  have hy₂₁ : y₂ ∉ Subgroup.zpowers y₁ := by
    rintro ⟨k, hk⟩
    apply sp4T'_not_mem_zpowers F
    refine ⟨k, hinjφ ?_⟩
    change e.symm (φ (sp4T F ^ k)) = e.symm (φ (sp4T' F))
    rw [map_zpow, map_zpow, ← hy₁def, ← hy₂def]
    exact hk
  obtain ⟨A₀, d, hdL, hdy, hdA, hcA, haA, hA₀, hcard, hnorm, hsec⟩ :=
    exists_E81 hcL ha hca hc3 h.ne_one ha3 hout' hZ (hmemC 0) (hmemC 1) hy₁3 hy₂3 hy hy₁1 hy₂₁
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1 := ⟨1, by rw [pow_one]; exact hA₀.2 d hdA⟩
  have hdt : inducedAutHom L e ⟨d, hdN⟩ = MulAut.conj (φ (sp4T F)) := by
    rw [inducedAutHom_eq_conj_of_mem e hdL hdN, hdy, MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨hK, hKne⟩ := imageModTheta_mulEquiv_projSL_of_sp4 hF hf e φ hdN hd3 hdt
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply hy₁1
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨1, hdL⟩ = 1 := map_one _
    rw [hy₁def]
    exact hdy.symm.trans h1
  refine ⟨A₀, d, ⟨fun x hx => hnorm hx, hcA, haA, hA₀, hcard, hsec, hdA, hd1, ?_, hn, hKne, ?_⟩⟩
  · exact Or.inl (InducesStdKind.psp4even F
      (inducesKindPSp4Even_inner_of_conj e hdN (φ (sp4T F)) hdt))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hL,
      (barCentralizer_mulEquiv_projSp hn0 ha3 hout hL).2, hK⟩)))

end CFSG.RankThree.PartTwo.KFacts
