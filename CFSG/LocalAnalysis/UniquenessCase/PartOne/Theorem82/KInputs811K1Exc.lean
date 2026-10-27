module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeExc

import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3Rank
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharSmall
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3Models
import CFSG.HardMathSupport.Timmesfeld.LieRank.G2Spec
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaPRank
import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TitsP3NoElemAbelian
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharXfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup TauCeti
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

section Certificates

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3 (four_le_pRank_three_of_isExcBig)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
  (pRank_le_two_statedSL_three_prime pRank_le_two_statedSU_three_prime)


theorem k34odd_lie_char3_or_exceptional
    (X : Type) [Group X] [Finite X] (d : ValidLieTypeIndex)
    (e : X ≃* (CFSGIndex.lie d).Group) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3)
    (hd : d.1.characteristic = 3 ∨
      ¬ ((∃ r q, d.1 = .A r q) ∨ (∃ r q, d.1 = .twistedA r q) ∨ (∃ r q, d.1 = .B r q) ∨
        (∃ r q, d.1 = .C r q) ∨ (∃ r q, d.1 = .D r q) ∨ (∃ r q, d.1 = .twistedD r q))) :
    LieModel X .PSL 2 3 3 := by
  by_cases hcl : (∃ r q, d.1 = .A r q) ∨ (∃ r q, d.1 = .twistedA r q) ∨
      (∃ r q, d.1 = .B r q) ∨ (∃ r q, d.1 = .C r q) ∨ (∃ r q, d.1 = .D r q) ∨
      (∃ r q, d.1 = .twistedD r q)
  ·
    have hch : d.1.characteristic = 3 := by
      rcases hd with h | h
      · exact h
      · exact absurd hcl h
    rcases CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3.rank_dichotomy_classical
        d hch hcl e with h4 | ⟨q, hA1, h27, -⟩ | ⟨q, hA2, hcard⟩ | ⟨q, hA2, hcard⟩
    · exfalso
      omega
    ·
      obtain ⟨dd, hv⟩ := d
      have hdd : dd = .A 1 q := hA1
      subst hdd
      have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
      have hpe : q.p ^ q.exponent = 3 ^ 3 := by
        rw [← PrimePower.card_def, h27]
        norm_num
      obtain ⟨hp, he⟩ :=
        Nat.Prime.pow_inj' q.prime_p Nat.prime_three q.exponent_pos.ne' (by norm_num) hpe
      rw [hp, he] at hm
      exact Or.inl ⟨by decide, hm⟩
    ·
      obtain ⟨dd, hv⟩ := d
      have hdd : dd = .A 2 q := hA2
      subst hdd
      have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
      have hpe : q.p ^ q.exponent = 3 ^ 1 := by
        rw [← PrimePower.card_def, hcard]
        norm_num
      obtain ⟨hp, he⟩ :=
        Nat.Prime.pow_inj' q.prime_p Nat.prime_three q.exponent_pos.ne' (by norm_num) hpe
      rw [hp, he] at hm
      obtain ⟨-, K, _, _, hK, ⟨f⟩⟩ := hm
      exfalso
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h2 := pRank_le_two_statedSL_three_prime (p := 3) (by simpa using hK) f
      omega
    ·
      obtain ⟨dd, hv⟩ := d
      have hdd : dd = .twistedA 2 q := hA2
      subst hdd
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hpe : q.p ^ q.exponent = 3 ^ 1 := by
        rw [← PrimePower.card_def, hcard]
        norm_num
      obtain ⟨hp, he⟩ :=
        Nat.Prime.pow_inj' q.prime_p Nat.prime_three q.exponent_pos.ne' (by norm_num) hpe
      rw [hp, he] at hm
      obtain ⟨-, K, _, _, hK, ⟨f⟩⟩ := hm
      exfalso
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h2 := pRank_le_two_statedSU_three_prime (p := 3) (by norm_num) (by simpa using hK) f
      omega
  ·
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q => exact absurd (Or.inl ⟨r, q, rfl⟩) hcl
    | twistedA r q => exact absurd (Or.inr (Or.inl ⟨r, q, rfl⟩)) hcl
    | B r q => exact absurd (Or.inr (Or.inr (Or.inl ⟨r, q, rfl⟩))) hcl
    | C r q => exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, rfl⟩)))) hcl
    | D r q => exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, q, rfl⟩))))) hcl
    | twistedD r q =>
        exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, q, rfl⟩))))) hcl
    | E6 q =>
        exfalso
        have h4 := four_le_pRank_three_of_isExcBig ⟨.E6 q, hv⟩ trivial e
        omega
    | E7 q =>
        exfalso
        have h4 := four_le_pRank_three_of_isExcBig ⟨.E7 q, hv⟩ trivial e
        omega
    | E8 q =>
        exfalso
        have h4 := four_le_pRank_three_of_isExcBig ⟨.E8 q, hv⟩ trivial e
        omega
    | F4 q =>
        exfalso
        have h4 := four_le_pRank_three_of_isExcBig ⟨.F4 q, hv⟩ trivial e
        omega
    | twistedE6 q =>
        exfalso
        have h4 := four_le_pRank_three_of_isExcBig ⟨.twistedE6 q, hv⟩ trivial e
        omega
    | G2 q =>
        by_cases hp : q.p = 3
        · haveI : Fact q.p.Prime := ⟨q.prime_p⟩
          have hU := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
            CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 e
          by_cases hf : 2 ≤ q.exponent
          · exfalso
            have h3 := CFSG.SectionRank.three_mul_le_pRank_of_G2Model hU
            rw [hp] at h3
            omega
          · have he1 : q.exponent = 1 := by
              have := q.exponent_pos
              omega
            rw [hp, he1] at hU
            exfalso
            have hL : LieModel X .G2 0 3 1 :=
              Or.inr (Or.inl ⟨rfl, by decide,
                ⟨⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩, hU⟩⟩)
            obtain ⟨φ⟩ :=
              CFSG.HardMathSupport.Timmesfeld.LieRank.nonempty_mulEquiv_adjointGroup_G2_of_lieModel
                hL
            obtain ⟨e', -⟩ : ∃ e' : X ≃* CFSG.HardMathSupport.Timmesfeld.LieRank.RG, True :=
              ⟨φ.trans (Subgroup.equivMapOfInjective
                (CFSG.Blueprint.Chevalley.adjointGroup .G2 (ZMod 3))
                (CFSG.Quasithin.G2U.glHom (RingEquiv.refl (ZMod 3)))
                (CFSG.Quasithin.G2U.glHom_injective _)), trivial⟩
            have heq : CFSG.Open.pRank 3 (⊤ : Subgroup X) =
                CFSG.Open.pRank 3
                  (⊤ : Subgroup CFSG.HardMathSupport.Timmesfeld.LieRank.RG) :=
              CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e'
            have h4 := CFSG.AGLEmbedding.ModuleSpec.n_le_pRank Nat.prime_three
              CFSG.HardMathSupport.Timmesfeld.LieRank.specA
            have hn : CFSG.HardMathSupport.Timmesfeld.LieRank.specA.n = 4 := rfl
            omega
        · exfalso
          have h := CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_cat_G2
            q hv (Ne.symm hp)
          have h' := CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm h
          obtain ⟨E, -, hE, hc⟩ :=
            CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
          have h2 := h' E hE
          rw [hc, hrk] at h2
          norm_num at h2
    | trialityD4 q =>
        by_cases hp : q.p = 3
        · haveI : Fact q.p.Prime := ⟨q.prime_p⟩
          exfalso
          have hT := CFSG.HardMathSupport.Timmesfeld.Tables.Census.twistedChevalleyModel_of_bridge
            CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 e
          have h4 := CFSG.SectionRank.four_le_pRank_of_trialityD4Model q.exponent_pos hT
          rw [hp] at h4
          omega
        · exfalso
          have h := CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4
            q hv hp
          have h' := CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm h
          obtain ⟨E, -, hE, hc⟩ :=
            CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
          have h2 := h' E hE
          rw [hc, hrk] at h2
          norm_num at h2
    | suzuki m =>
        exfalso
        have hS := CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie (S := X) m ⟨hv, ⟨e⟩⟩
        have h3 := CFSG.RankThree.PartTwo.KFacts.KP7.three_not_dvd_card hS
        obtain ⟨E, -, -, hc⟩ :=
          CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
        rw [hrk] at hc
        exact (h3 ((dvd_pow_self 3 (by norm_num : 3 ≠ 0)).trans
          (hc ▸ Subgroup.card_subgroup_dvd_card E))).elim
    | reeG2 m =>
        exfalso
        have hR := CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 (S := X) m ⟨hv, ⟨e⟩⟩
        obtain ⟨-, hf, h2⟩ := CFSG.SectionRank.smallReeModel_rank hR
        have ha : 1 ≤ m := by
          have h := ((LieTypeIndex.valid_iff _).1 hv).1
          simpa [LieTypeIndex.inStandardRange_iff] using h
        rw [hrk] at h2
        omega
    | reeF4 m =>
        exfalso
        have h := CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv
        have h' := CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm h
        obtain ⟨E, -, hE, hc⟩ :=
          CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
        have h2 := h' E hE
        rw [hc, hrk] at h2
        norm_num at h2
    | tits =>
        exfalso
        obtain ⟨E, -, hE, hc⟩ :=
          CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
        rw [hrk] at hc
        exact (CFSG.HardMathSupport.Timmesfeld.CrossChar.no_elemAbelian27_cat_tits hv
          (E := E.map e.toMonoidHom)
          (CFSG.SectionRank.isElemAbelian_map hE _)
          (by rw [Subgroup.card_map_of_injective e.injective, hc]; norm_num)).elim

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
