module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Seven
public import CFSG.GroupTheory.SLThreeEightCoverRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Prod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace C163

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem four_le_pRank_of_sl3_eight_pair (D : Data G) (h127 : R127 D) (h119 : F11.R119 D)
    {V₀ V : Subgroup G} (h125 : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V)
    (N : Fin 2 → Subgroup (MulAut (Vtil V₀ V hV)))
    (hNcomp : ∀ j, IsComponentOf (N j) (Mbar D.M V₀ V hV))
    (hNSL : ∀ j, IsSLn ↥(N j) 3 3)
    (hNcomm : ∀ j l, j ≠ l → ∀ x ∈ N j, ∀ y ∈ N l, x * y = y * x) :
    4 ≤ CFSG.Open.pRank 7 D.M := by
  classical
  have hdata : ∀ j, ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 8 ∧
      Nonempty (↥(N j) ≃* Matrix.SpecialLinearGroup (Fin 3) K) := by
    intro j
    obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hNSL j
    refine ⟨K, hKf, hKfin, ?_, ?_⟩
    · rw [hKcard]; norm_num
    · exact ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm⟩
  obtain ⟨K₀, hK₀f, hK₀fin, hK₀card, ⟨e₀⟩⟩ := hdata 0
  obtain ⟨K₁, hK₁f, hK₁fin, hK₁card, ⟨e₁⟩⟩ := hdata 1
  let : Field K₀ := hK₀f
  let : Finite K₀ := hK₀fin
  let : Field K₁ := hK₁f
  let : Finite K₁ := hK₁fin
  have hZ : ∀ j, Subgroup.center ↥(N j) = ⊥ := by
    intro j
    obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hdata j
    let : Field K := hKf
    let : Finite K := hKfin
    have hdiv := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd
      (n := 3) (by norm_num) K
    rw [hKcard] at hdiv
    have hcard1 : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) = 1 := by
      have hgcd : Nat.gcd 3 (8 - 1) = 1 := by norm_num
      rw [hgcd] at hdiv
      exact Nat.dvd_one.mp hdiv
    have hZK : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ hcard1
    have hmap : (Subgroup.center ↥(N j)).map e.toMonoidHom = ⊥ := by
      rw [show (Subgroup.center ↥(N j)).map e.toMonoidHom =
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) from
          Subgroup.map_center_eq e]
      exact hZK
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥(N j))
      e.injective).mp hmap
  have hNS : ∀ j, IsSimpleGroup ↥(N j) := by
    intro j
    have hq := (hNcomp j).2.2
    have hsimple : IsSimpleGroup (↥(N j) ⧸ Subgroup.center ↥(N j)) := hq.2
    exact ((QuotientGroup.quotientMulEquivOfEq (hZ j)).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hN3 : ∀ j, 3 ∣ Nat.card ↥(N j) := by
    intro j
    fin_cases j
    · change 3 ∣ Nat.card ↥(N 0)
      rw [Nat.card_congr e₀.toEquiv,
        Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K₀).toEquiv,
        CFSG.Open.StatedAPI.card_statedSL_three, hK₀card]
      norm_num
    · change 3 ∣ Nat.card ↥(N 1)
      rw [Nat.card_congr e₁.toEquiv,
        Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K₁).toEquiv,
        CFSG.Open.StatedAPI.card_statedSL_three, hK₁card]
      norm_num
  have hNM : ∀ j, N j ≤ Mbar D.M V₀ V hV := fun j => (hNcomp j).1
  obtain ⟨Y, hYM, hYperf, f, hfrange, hlayer, hsolv, hR⟩ :=
    exists_perfect_cover_of_factors D h127 h119 h125 hV N hNM hNS hZ hN3 hNcomm
  have hdisj : N 0 ⊓ N 1 = ⊥ := by
    have hcentral : N 1 ≤ Subgroup.centralizer (N 0 : Set (MulAut (Vtil V₀ V hV))) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hNcomm 0 1 (by decide) x hx y hy
    simpa only [disjoint_iff] using
      CFSG.ComponentClassification.CenterlessCommutingFamily.disjoint_of_centralizes
        (N 0) (N 1) (hZ 0) hcentral
  have hprod : Nonempty (↥(N 0 ⊔ N 1) ≃* ↥(N 0) × ↥(N 1)) :=
    CFSG.EvenSporadicStandard.HSStd.InvCent.nonempty_mulEquiv_sup_prod
      (hNcomm 0 1 (by decide)) hdisj
  have hsup : (⨆ j : Fin 2, N j) = N 0 ⊔ N 1 := by
    refine le_antisymm (iSup_le ?_) (sup_le (le_iSup (fun j : Fin 2 => N j) 0)
      (le_iSup (fun j : Fin 2 => N j) 1))
    intro j
    fin_cases j
    · exact le_sup_left
    · exact le_sup_right
  let eProd : ↥(⨆ j : Fin 2, N j) ≃* (Matrix.SpecialLinearGroup (Fin 3) K₀ ×
      Matrix.SpecialLinearGroup (Fin 3) K₁) :=
    (MulEquiv.subgroupCongr hsup).trans (hprod.some.trans (MulEquiv.prodCongr e₀ e₁))
  let fR : ↥Y →* ↥(⨆ j : Fin 2, N j) :=
    (MulEquiv.subgroupCongr hfrange).toMonoidHom.comp
      (f.codRestrict f.range (fun y => MonoidHom.mem_range.mpr ⟨y, rfl⟩))
  let F : ↥Y →* (Matrix.SpecialLinearGroup (Fin 3) K₀ ×
      Matrix.SpecialLinearGroup (Fin 3) K₁) := eProd.toMonoidHom.comp fR
  have hFsurj : Function.Surjective F := by
    intro x
    obtain ⟨z, hz⟩ := eProd.surjective x
    obtain ⟨w, hw⟩ := (MulEquiv.subgroupCongr hfrange).surjective z
    obtain ⟨y, hy⟩ := w.2
    refine ⟨y, ?_⟩
    have hw' : w = (⟨f y, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩ : ↥f.range) :=
      (Subtype.ext hy).symm
    have h1 : (MulEquiv.subgroupCongr hfrange)
        ⟨f y, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩ = z := by
      rw [← hw, hw']
    calc F y = eProd ((MulEquiv.subgroupCongr hfrange)
          ⟨f y, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩) := rfl
      _ = eProd z := by rw [h1]
      _ = x := hz
  have hFker : F.ker = f.ker := by
    rw [show F = eProd.toMonoidHom.comp fR from rfl,
      MonoidHom.ker_comp_of_injective _ _ eProd.injective,
      show fR = (MulEquiv.subgroupCongr hfrange).toMonoidHom.comp
        (f.codRestrict f.range (fun y => MonoidHom.mem_range.mpr ⟨y, rfl⟩)) from rfl,
      MonoidHom.ker_comp_of_injective _ _
        (MulEquiv.subgroupCongr hfrange).injective,
      MonoidHom.ker_codRestrict]
  have hsolvF : Group.IsSolvable ↥F.ker := by
    rw [hFker]
    exact hsolv
  have hRF : CFSG.pCore 2 ↥Y ≤ F.ker := by
    rw [hFker]
    exact hR
  have : Group.IsPerfect ↥Y := hYperf
  have hT1 := CFSG.GroupTheory.four_le_pRank_of_sl3_eight_product_cover
    (Y := ↥Y) hK₀card hK₁card F hFsurj hlayer hsolvF hRF
  have hYrank : 4 ≤ CFSG.Open.pRank 7 Y := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hT1
  exact hYrank.trans (CFSG.SectionRank.pRank_mono (p := 7) Nat.prime_seven.one_lt hYM)

end C163

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
