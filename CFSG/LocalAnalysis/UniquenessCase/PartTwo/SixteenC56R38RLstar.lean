module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RLstarY
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RLayerKer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Norm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_Lstar_of_case1633 (D : Data G) (h119 : F11.R119 D) (h127 : R127 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {m : ℕ}
    (hm : Case1633 D V₀ V hV L m) :
    ∃ Lst : Subgroup G, Lst ≤ D.M ∧ D.M ≤ normalizer (Lst : Set G) ∧
      ¬ (2 ^ m - 1) ∣ Nat.card ↥(Lst ⊓ F11.CTilde D.M V₀ V) ∧
        barSub V₀ V hV Lst = lBar V₀ V hV L := by
  classical
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_case1633 hm
  have hm23 : m = 2 ∨ m = 3 := by
    rcases hm with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hq : (2 ^ m - 1).Prime := by rcases hm23 with rfl | rfl <;> norm_num
  have hq2 : 2 ^ m - 1 ≠ 2 := by rcases hm23 with rfl | rfl <;> norm_num
  have hΩ : IsOmegaPlus ↥(lBar V₀ V hV L) 4 m := by
    rcases hm with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
    · exact hc.1
    · exact hc.1
  have hcard : Nat.card S.omega = (Nat.card S.K * (Nat.card S.K ^ 2 - 1)) ^ 2 := by
    have h1 := Om8Excl.card_isOmegaPlus_four (by omega) hΩ
    rw [hSω, h1, hSK]
    rcases hm23 with rfl | rfl <;> norm_num
  have hΩ0 : S.omega = S.omega0 := S.omega_eq_omega0_of_card hcard
  have hsup2 : (⨆ j, S.factor j) = S.factor 0 ⊔ S.factor 1 := by
    apply le_antisymm
    · exact iSup_le fun j => by fin_cases j <;> simp
    · exact sup_le (le_iSup S.factor 0) (le_iSup S.factor 1)
  have hsup : (⨆ j, S.factor j) = lBar V₀ V hV L := by
    rw [hsup2, S.factor_sup, ← hΩ0, hSω]
  have h125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hS.setting.hyp151.le
  have hdvd := fun j => S.dvd_card_factor hSK hm23 j
  obtain ⟨Y, hYM, hYn, hperf, hlayer, hsolv, hR, hbarY⟩ :=
    exists_Y_of_factors D h127 h119 h125 hV S.factor
      (fun j => (le_iSup S.factor j).trans (hsup.le.trans hLM))
      S.isSimpleGroup_factor S.center_factor (fun j => (hdvd j).1)
      (fun j l hjl => S.factor_commute hjl)
      (by rw [hsup, ← hSω]; exact Mbar_le_normalizer_lBar hS S hSω)
  refine ⟨Y, hYM, hYn, ?_, hbarY.trans hsup⟩
  have hYs : Y ≤ stabTil V₀ V := hYM.trans hMs
  let f : ↥Y →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hYs)
  have hfrange : f.range = barSub V₀ V hV Y := by
    show ((actTil V₀ V hV).comp (Subgroup.inclusion hYs)).range = _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hfker : ∀ y : ↥Y, y ∈ f.ker ↔ (y : G) ∈ F11.CTilde D.M V₀ V := by
    intro y
    rw [mem_cTilde_iff hV h125.pairFacts.le_normalizer]
    exact ⟨fun h => ⟨hYM y.2, hYs y.2, h⟩, fun h => h.2.2⟩
  have hfkerEq : f.ker.map Y.subtype = Y ⊓ F11.CTilde D.M V₀ V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hfker y).1 hy⟩
    · rintro ⟨hxY, hxC⟩
      exact ⟨⟨x, hxY⟩, (hfker ⟨x, hxY⟩).2 hxC, rfl⟩
  have hsolvf : Group.IsSolvable ↥f.ker := by
    have hle : f.ker.map Y.subtype ≤ Y ⊓ F11.CTilde D.M V₀ V := hfkerEq.le
    haveI := hsolv
    exact solvable_of_solvable_injective (f := (Subgroup.inclusion hle).comp
      (f.ker.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
      ((Subgroup.inclusion_injective hle).comp (MulEquiv.injective _))
  have hR' : CFSG.pCore 2 ↥Y ≤ f.ker := fun y hy => (hfker y).2 (hR y hy)
  have hcardker : Nat.card ↥f.ker = Nat.card ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
    rw [← hfkerEq]
    exact Nat.card_congr (f.ker.equivMapOfInjective Y.subtype Y.subtype_injective).toEquiv
  have hrange : f.range = S.factor 0 ⊔ S.factor 1 := by
    rw [hfrange, hbarY, hsup2]
  have key := not_dvd_card_ker_of_layer_prod (Subgroup.isPerfect_iff.2 hperf) hlayer f
    (T₀ := S.factor 0) (T₁ := S.factor 1) (S.factor_commute (by decide))
    S.factor_inf_factor hrange hsolvf hR' hq hq2 (hdvd 0).2.1 (hdvd 0).2.2 (hdvd 1).2.1
    (hdvd 1).2.2
  rwa [hcardker] at key

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
