module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Unitary
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoSmall
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoG2
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoFamCl
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SylowOver
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54BorelRank
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2a
import CFSG.LocalAnalysis.UniquenessCase.UC22ListB
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)


private theorem blueprintLieModel_tits_of_models {X : Type} [Group X] {n f : ℕ}
    (hm : CFSG.Models.LieModel X .Tits n 2 f) : CFSG.Blueprint.LieModel X .Tits 0 2 1 := by
  obtain ⟨-, hcl | ⟨-, d, hnames, ⟨e⟩⟩⟩ := hm
  · exact hcl.2.elim
  · obtain ⟨⟨idx, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d :=
      ⟨d, rfl⟩
    have hidx : idx = .tits := by
      cases idx <;> simp_all only [CFSG.Models.NamesTag]
    subst hidx
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide,
      CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_tits_of_index hv e⟩))

private theorem exists_blueprint_lieModel_of_smallParabolic {X : Type} [Group X]
    {t : StatedLieTag} {n f : ℕ} (hm : CFSG.Models.LieModel X t n 2 f)
    (hs : Asch58SmallParabolic t n f) :
    ∃ t n f, CFSG.Blueprint.LieModel X t n 2 f ∧ Asch58SmallParabolic t n f := by
  by_cases ht : t = .Tits
  · subst t
    exact ⟨.Tits, 0, 1, blueprintLieModel_tits_of_models hm,
      by simp [Asch58SmallParabolic]⟩
  · exact ⟨t, n, f, blueprintLieModel_of_models_of_ne_tits hm ht, hs⟩

theorem asch54Case_parabolic (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    Asch54Case fun X _ => ∃ t n f, CFSG.Models.LieModel X t n 2 f ∧ Asch58Parabolic t n f := by
  intro Q _ _ L T hKQ hLn hLs hLnab hC hP hLL0 hT hnu
  obtain ⟨t, n, f, hm, hpar⟩ := hP
  have hO : LieOrderFormulasInput :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hL0f : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧
        ∃ a b : L, a * b ≠ b * a :=
    fun X _ hX => CFSG.LocalAnalysis.UniquenessCase.UC22.uc22lb_listB_facts
      CFSG.LocalAnalysis.UniquenessCase.UC22.listBExceptionalFacts
      ((isCalL0_iff_asc1930ListB X).1 hX)
  have hL0' : ∀ (X : Type) [Group X], IsCalL0 X → ∃ a b : X, a * b ≠ b * a :=
    fun X _ hX => (hL0f X hX).2.2
  have hcat : CFSG.Open.IsCatalogGroup ↥L :=
    (hKQ.of_injective L.subtype L.subtype_injective).isCatalogGroup_of_surjective ⊤ hLnab
      (Subgroup.subtype ⊤) (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hq : Group.IsSolvable (Q ⧸ L) :=
    isSolvable_quotient_of_outSolvable L (by rw [hC]; exact bot_le)
      (CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer
        (hS _ hLs hLnab hcat))
  have hSmall : ∀ (X : Type) [Group X] [Finite X],
      (IsSimpleGroup X ∧ ∃ t n f, CFSG.Blueprint.LieModel X t n 2 f ∧
        Asch58SmallParabolic t n f) →
      ∀ (S : Sylow 2 X) (Y : Subgroup X), (S : Subgroup X) ≤ Y → Y < ⊤ →
        ¬ HasCompFactor Y IsCalL0 := by
    rintro X _ _ ⟨hXs, t, n, f, hbm, hsp⟩ S Y hSY hY
    have hinst : IsSimpleGroup X := hXs
    exact not_hasCompFactor_of_sylow_le_small hO hbm hsp S hSY hY
  have hLarge : ∀ (X : Type) [Group X] [Finite X],
      ((∃ t n f, CFSG.Models.LieModel X t n 2 f ∧ f = 2 ∧ t ≠ .Tits ∧
          4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t n) ∧
        IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < CFSG.Open.pRank p (⊤ : Subgroup X) ∧
        ∀ S : Sylow 2 X, 1 < CFSG.Open.pRank p
          (Subgroup.normalizer ((S : Subgroup X) : Set X)) := by
    rintro X _ _ ⟨⟨t, n, f, hmX, hf, ht, hr⟩, hXs, hnabX⟩
    subst hf
    have hinst : IsSimpleGroup X := hXs
    have h := pRank_three_normalizer_of_rank hnabX hmX ht hr
    exact ⟨3, Nat.prime_three, by norm_num, h.1,
      fun S => lt_trans (by norm_num : 1 < 3) (h.2 S)⟩
  have hsmallCase : Asch54Case (fun X _ => IsSimpleGroup X ∧
      ∃ t n f, CFSG.Blueprint.LieModel X t n 2 f ∧ Asch58SmallParabolic t n f) :=
    asch54Case_of_sylowOvergroups hS hL0f hSmall
  have hlargeCase : Asch54Case (fun X _ =>
      (∃ t n f, CFSG.Models.LieModel X t n 2 f ∧ f = 2 ∧ t ≠ .Tits ∧
        4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t n) ∧
        IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) :=
    asch54Case_of_pRank_normalizer hS hL0f hLarge
  rcases hpar with ⟨rfl, htD4⟩ | ⟨rfl, hcases⟩
  ·
    cases t
    case PSL =>
      have h2 : 2 ≤ n := hm.1.2.2.1
      have hn2 : n ≠ 2 := by
        intro hn
        exact hm.1.2.2.2.1 (by rw [hn]; norm_num)
      by_cases hn3 : n = 3
      · subst n
        refine hsmallCase Q L T hKQ hLn hLs hLnab hC ⟨hLs, ?_⟩ hLL0 hT hnu
        exact exists_blueprint_lieModel_of_smallParabolic hm
          (by simp [Asch58SmallParabolic])
      · have h4 : 4 ≤ n := by omega
        exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
          (Chev2Orbit.hasBQSmall_psl hO hm (Or.inl ⟨rfl, h4⟩)))
    case PSU =>
      have h3 : 3 ≤ n := hm.1.2.2.1
      have hn3 : n ≠ 3 := by
        intro hn
        exact hm.1.2.2.2 (by rw [hn]; norm_num)
      have h4 : 4 ≤ n := by omega
      exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
        (Chev2Orbit.hasBQSmall_psu hO hm h4))
    case PSp =>
      have h2 : 2 ≤ n := hm.1.2.2.1
      have hn2 : n ≠ 2 := by
        intro hn
        exact hm.1.2.2.2 (by rw [hn]; norm_num)
      have h3 : 3 ≤ n := by omega
      exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
        (Chev2Orbit.hasBQSmall_psp hO hm (Or.inl ⟨rfl, h3⟩)))
    case POmegaOdd => exact absurd rfl hm.1.2.2.2
    case POmegaPlus =>
      exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
        (Chev2Orbit.hasBQSmall_pomegaPlus hO hm))
    case POmegaMinus =>
      exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
        (Chev2Orbit.hasBQSmall_pomegaMinus hO hm))
    case G2 => exact absurd hm.1.2.2.2 (by norm_num)
    case F4 =>
      exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
        (Chev2Orbit.hasBQSmall_f4 hO hm))
    case E6 =>
      exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
        (Chev2Orbit.hasBQSmall_e6 hO hm))
    case E7 =>
      exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
        (Chev2Orbit.hasBQSmall_e7 hO hm))
    case E8 =>
      exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
        (Chev2Orbit.hasBQSmall_e8 hO hm))
    case twistedE6 =>
      exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
        (Chev2Orbit.hasBQSmall_twistedE6 hO hm))
    case trialityD4 => exact absurd rfl htD4
    case twistedB2 => exact absurd hm.1.2.2.2.2.2 (by norm_num)
    case twistedG2 => exact absurd hm.1.2.2.2.1 (by norm_num)
    case twistedF4 => exact absurd hm.1.2.2.2.2.2 (by norm_num)
    case Tits =>
      refine hsmallCase Q L T hKQ hLn hLs hLnab hC ⟨hLs, ?_⟩ hLL0 hT hnu
      exact exists_blueprint_lieModel_of_smallParabolic hm
        (by simp [Asch58SmallParabolic])
  ·
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨rfl, rfl⟩
    ·
      have h2 : 2 ≤ n := hm.1.2.2.1
      by_cases hn2 : n = 2
      · subst n
        refine hsmallCase Q L T hKQ hLn hLs hLnab hC ⟨hLs, ?_⟩ hLL0 hT hnu
        exact exists_blueprint_lieModel_of_smallParabolic hm
          (by simp [Asch58SmallParabolic])
      · by_cases hn3 : n = 3
        · subst n
          refine hsmallCase Q L T hKQ hLn hLs hLnab hC ⟨hLs, ?_⟩ hLL0 hT hnu
          exact exists_blueprint_lieModel_of_smallParabolic hm
            (by simp [Asch58SmallParabolic])
        · have h4 : 4 ≤ n := by omega
          by_cases hn4 : n = 4
          · subst n
            exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
              (Chev2Orbit.hasBQSmall_psl hO hm (Or.inr ⟨rfl, rfl⟩)))
          · have h5 : 5 ≤ n := by omega
            refine hlargeCase Q L T hKQ hLn hLs hLnab hC ⟨⟨.PSL, n, 2, hm, rfl,
              by decide, ?_⟩, hLs, hLnab⟩ hLL0 hT hnu
            simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank]
            omega
    ·
      have h2 : 2 ≤ n := hm.1.2.2.1
      by_cases hn2 : n = 2
      · subst n
        refine hsmallCase Q L T hKQ hLn hLs hLnab hC ⟨hLs, ?_⟩ hLL0 hT hnu
        exact exists_blueprint_lieModel_of_smallParabolic hm
          (by simp [Asch58SmallParabolic])
      · by_cases hn3 : n = 3
        · subst n
          exact Or.inl (Chev2Orbit.lGen_eq_top_of_hasBQSmall hLs hLnab hq hT hL0'
            (Chev2Orbit.hasBQSmall_psp hO hm (Or.inr ⟨rfl, rfl⟩)))
        · have h4 : 4 ≤ n := by omega
          refine hlargeCase Q L T hKQ hLn hLs hLnab hC ⟨⟨.PSp, n, 2, hm, rfl,
            by decide, ?_⟩, hLs, hLnab⟩ hLL0 hT hnu
          simp only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank]
          omega
    ·
      have h4 : 4 ≤ n := hm.1.2.2
      refine hlargeCase Q L T hKQ hLn hLs hLnab hC ⟨⟨.POmegaPlus, n, 2, hm, rfl,
        by decide, ?_⟩, hLs, hLnab⟩ hLL0 hT hnu
      simpa only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] using h4
    ·
      have hn0 : n = 0 := hm.1.2.2.1
      subst n
      exact Or.inl (Chev2Orbit.lGen_eq_top_of_lieModel_g2 hLs hLnab hq hT hL0' hO hm)
    ·
      refine hlargeCase Q L T hKQ hLn hLs hLnab hC ⟨⟨.F4, n, 2, hm, rfl,
        by decide, ?_⟩, hLs, hLnab⟩ hLL0 hT hnu
      norm_num [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank]
    ·
      refine hlargeCase Q L T hKQ hLn hLs hLnab hC ⟨⟨.E6, n, 2, hm, rfl,
        by decide, ?_⟩, hLs, hLnab⟩ hLL0 hT hnu
      norm_num [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank]
    ·
      refine hlargeCase Q L T hKQ hLn hLs hLnab hC ⟨⟨.E7, n, 2, hm, rfl,
        by decide, ?_⟩, hLs, hLnab⟩ hLL0 hT hnu
      norm_num [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank]
    ·
      refine hlargeCase Q L T hKQ hLn hLs hLnab hC ⟨⟨.E8, n, 2, hm, rfl,
        by decide, ?_⟩, hLs, hLnab⟩ hLL0 hT hnu
      norm_num [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank]
    ·
      refine hsmallCase Q L T hKQ hLn hLs hLnab hC ⟨hLs, ?_⟩ hLL0 hT hnu
      exact exists_blueprint_lieModel_of_smallParabolic hm
        (by simp [Asch58SmallParabolic])

theorem asch54Chev2 (hS : CFSG.AGLEmbedding.KFactCatalogSchreier) : Asch54Chev2 :=
  asch54Chev2_of hS (asch54Case_parabolic hS) asch58UnitaryFive_holds

end CFSG.LocalAnalysis.WeakClosure81
