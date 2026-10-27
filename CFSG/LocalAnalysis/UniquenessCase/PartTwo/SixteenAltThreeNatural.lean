module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltThreeRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltThreeHeart
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTripleA6Rank
public import CFSG.Quasithin.H13.KGFactHatA6
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvFactHatSeven
public import CFSG.LocalAnalysis.AGLEmbeddingD2.RealThreeRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Loc
public import CFSG.Quasithin.Background.SmithD321Ext
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Rank
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvFactSixSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23ATwoConj
public import CFSG.Quasithin.Background.ConjugateSectionAction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase
public import CFSG.Quasithin.Background.F918V3QB1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSectionTransport
public import CFSG.GroupTheory.SubgroupOfQuotientMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.FiveCentralB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Cent
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_common_center_of_two_components
    {B : Type} [Group B] [Finite B] {C₁ C₂ : Subgroup B}
    (hC₁ : CFSG.IsComponent C₁) (hC₂ : CFSG.IsComponent C₂) (hne : C₁ ≠ C₂)
    (hrk₁ : 2 ≤ CFSG.Open.pRank 3 C₁) (hrk₂ : 2 ≤ CFSG.Open.pRank 3 C₂)
    (hupper : CFSG.Open.pRank 3 (⊤ : Subgroup B) ≤ 3)
    (hodd₁ : Odd (Nat.card (Subgroup.center C₁)))
    (hodd₂ : Odd (Nat.card (Subgroup.center C₂)))
    (hdvd₁ : Nat.card (Subgroup.center C₁) ∣ 6)
    (hdvd₂ : Nat.card (Subgroup.center C₂) ∣ 6) :
    (Subgroup.center C₁).map C₁.subtype = C₁ ⊓ C₂ ∧
      (Subgroup.center C₂).map C₂.subtype = C₁ ⊓ C₂ ∧
      Nat.card ↥(C₁ ⊓ C₂) = 3 ∧
      Nat.card (Subgroup.center C₁) = 3 ∧
      Nat.card (Subgroup.center C₂) = 3 := by
  have hcomm : ⁅C₁, C₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hC₁ hC₂).resolve_left hne
  have hcomm' : ⁅C₂, C₁⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm] at hcomm
  have hC₂_le_cent : C₂ ≤ Subgroup.centralizer (C₁ : Set B) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
  have hC₁_le_cent : C₁ ≤ Subgroup.centralizer (C₂ : Set B) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcommute : ∀ x ∈ C₁, ∀ y ∈ C₂, x * y = y * x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (hC₂_le_cent hy) x hx
  have hinf_le_center₁ : C₁ ⊓ C₂ ≤ (Subgroup.center C₁).map C₁.subtype := by
    intro x hx
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (by
      show (y : B) * x = x * (y : B)
      exact hcommute (y : B) y.2 x hx.2)
  have hinf_le_center₂ : C₁ ⊓ C₂ ≤ (Subgroup.center C₂).map C₂.subtype := by
    intro x hx
    rw [Subgroup.mem_map]
    refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (by
      show (y : B) * x = x * (y : B)
      exact (hcommute x hx.1 (y : B) y.2).symm)
  have hinf_ne_bot : C₁ ⊓ C₂ ≠ ⊥ := by
    intro hbot
    have hcop : Nat.Coprime 3 (Nat.card ↥(C₁ ⊓ C₂)) := by
      rw [hbot, Subgroup.card_bot]
      exact Nat.coprime_one_right 3
    have hadd := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime
      (q := 3) Nat.prime_three hcommute hcop
    have hle : CFSG.Open.pRank 3 (C₁ ⊔ C₂) ≤ 3 :=
      (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3)
        (le_top : C₁ ⊔ C₂ ≤ ⊤)).trans hupper
    omega
  have hcard_inf_ne_one : Nat.card ↥(C₁ ⊓ C₂) ≠ 1 := fun h1 =>
    hinf_ne_bot (Subgroup.eq_bot_of_card_eq _ h1)
  have hcenter₁ : Nat.card (Subgroup.center C₁) = 3 := by
    have hdvd3 : Nat.card (Subgroup.center C₁) ∣ 3 := by
      have hcop : Nat.Coprime (Nat.card (Subgroup.center C₁)) 2 :=
        hodd₁.coprime_two_right
      have h6 : (6 : ℕ) = 3 * 2 := by norm_num
      exact hcop.dvd_of_dvd_mul_right (h6 ▸ hdvd₁)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
    · exfalso
      have hbot : Subgroup.center C₁ = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      have hle_bot : C₁ ⊓ C₂ ≤ (⊥ : Subgroup B) := by
        simpa only [hbot, Subgroup.map_bot] using hinf_le_center₁
      exact hinf_ne_bot (le_bot_iff.mp hle_bot)
    · exact h3
  have hcenter₂ : Nat.card (Subgroup.center C₂) = 3 := by
    have hdvd3 : Nat.card (Subgroup.center C₂) ∣ 3 := by
      have hcop : Nat.Coprime (Nat.card (Subgroup.center C₂)) 2 :=
        hodd₂.coprime_two_right
      have h6 : (6 : ℕ) = 3 * 2 := by norm_num
      exact hcop.dvd_of_dvd_mul_right (h6 ▸ hdvd₂)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
    · exfalso
      have hbot : Subgroup.center C₂ = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      have hle_bot : C₁ ⊓ C₂ ≤ (⊥ : Subgroup B) := by
        simpa only [hbot, Subgroup.map_bot] using hinf_le_center₂
      exact hinf_ne_bot (le_bot_iff.mp hle_bot)
    · exact h3
  have hinf_card : Nat.card ↥(C₁ ⊓ C₂) = 3 := by
    have hdvd : Nat.card ↥(C₁ ⊓ C₂) ∣ 3 := by
      have hcard : Nat.card ↥(C₁ ⊓ C₂) ∣
          Nat.card ↥((Subgroup.center C₁).map C₁.subtype) :=
        Subgroup.card_dvd_of_le hinf_le_center₁
      rwa [Subgroup.card_map_of_injective C₁.subtype_injective, hcenter₁] at hcard
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 hcard_inf_ne_one
    · exact h3
  have hmap₁ : (Subgroup.center C₁).map C₁.subtype = C₁ ⊓ C₂ := by
    refine (Subgroup.eq_of_le_of_card_ge hinf_le_center₁ ?_).symm
    rw [Subgroup.card_map_of_injective C₁.subtype_injective, hcenter₁, hinf_card]
  have hmap₂ : (Subgroup.center C₂).map C₂.subtype = C₁ ⊓ C₂ := by
    refine (Subgroup.eq_of_le_of_card_ge hinf_le_center₂ ?_).symm
    rw [Subgroup.card_map_of_injective C₂.subtype_injective, hcenter₂, hinf_card]
  exact ⟨hmap₁, hmap₂, hinf_card, hcenter₁, hcenter₂⟩

private structure S168e3ActualCover
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
    (H : Subgroup (MulAut (Vtil V₀ V hV))) : Type where
  K : Subgroup G
  hK : K ∈ calC D.M
  hbarK : barSub V₀ V hV K = H
  C : Subgroup (Bar2 D.M)
  C_eq : C = UC22.barImage D.M K
  isComp : CFSG.IsComponent C
  map_eq : C.map ψ = H
  η : C →* H
  η_surj : Function.Surjective η
  η_val : ∀ y : C, (η y : MulAut (Vtil V₀ V hV)) = ψ y
  ker_eq : η.ker = Subgroup.center C
  q : C ⧸ Subgroup.center C ≃* H
  q_eq : ∀ y : C, q (QuotientGroup.mk y) = η y
  oddCenter : Odd (Nat.card (Subgroup.center C))
  center_dvd : Nat.card (Subgroup.center C) ∣ 6
  pRank3 : 2 ≤ CFSG.Open.pRank 3 C

private noncomputable def s168e3_actualCoverData
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    {ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV)}
    (hψ : ∀ m : D.M, ψ (QuotientGroup.mk m) =
      actTil V₀ V hV ⟨m, le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
        c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ m.2⟩)
    {H : Subgroup (MulAut (Vtil V₀ V hV))}
    (hcomp : IsComponentOf H (Mbar D.M V₀ V hV))
    {n : ℕ} (hn : n = 6 ∨ n = 7) (hA : UC22.IsAlt H n) :
    S168e3ActualCover ψ H := by
  have h125 : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  let hExists : ∃ K : Subgroup G, K ∈ calC D.M ∧ barSub V₀ V hV K = H :=
    exists_calC_cover_of_component h125 c.std.h127 c.std.h119 hcomp
  let K : Subgroup G := Classical.choose hExists
  have hK : K ∈ calC D.M := (Classical.choose_spec hExists).1
  have hbarK : barSub V₀ V hV K = H := (Classical.choose_spec hExists).2
  let C : Subgroup (Bar2 D.M) := UC22.barImage D.M K
  have hCcomp : CFSG.IsComponent C := by
    dsimp only [C]
    exact uc22p22l_barImage_isComponent hK
  have hmap : C.map ψ = H := by
    dsimp only [C]
    exact barImage_map_eq_of_mem_calC h125 hK hbarK ψ hψ
  have hsimple : IsSimpleGroup ↥H := by
    obtain ⟨eA⟩ := hA
    have hAltSimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rcases hn with rfl | rfl <;> norm_num)
    exact eA.isSimpleGroup_congr.mpr hAltSimple
  let eC : ↥(C.map ψ) ≃* ↥H := MulEquiv.subgroupCongr hmap
  let η : C →* H := eC.toMonoidHom.comp (ψ.subgroupMap C)
  have hηsurj : Function.Surjective η :=
    eC.surjective.comp (ψ.subgroupMap_surjective C)
  have hηval : ∀ y : C, (η y : MulAut (Vtil V₀ V hV)) = ψ y := by
    intro y
    rfl
  have hker_sub : (ψ.comp C.subtype).ker = Subgroup.center C :=
    ker_comp_subtype_eq_center_of_mem_calC h125 hK hbarK hsimple ψ hψ
  have hker_comp : (ψ.comp C.subtype).ker = ψ.ker.subgroupOf C := by
    ext x
    simp [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have hker_map : (ψ.subgroupMap C).ker = (ψ.comp C.subtype).ker := by
    rw [Subgroup.ker_subgroupMap]
    exact hker_comp.symm
  have hkerη : η.ker = (ψ.subgroupMap C).ker :=
    MonoidHom.ker_comp_of_injective _ _ eC.injective
  have hker : η.ker = Subgroup.center C := hkerη.trans (hker_map.trans hker_sub)
  let q : C ⧸ Subgroup.center C ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective η hηsurj)
  have hqeq : ∀ y : C, q (QuotientGroup.mk y) = η y := by
    intro y
    rfl
  let eBar : Bar2 K ≃* C :=
    Classical.choose (uc22p22l_barImage_equiv (L := D.M) hK)
  have hoddBar : Odd (Nat.card (Subgroup.center (Bar2 K))) := by
    simpa only [Bar2] using uc22p22l_odd_center_quotient (Λ := K)
  have hodd : Odd (Nat.card (Subgroup.center C)) := by
    rw [← Nat.card_congr (Subgroup.centerCongr eBar).toEquiv]
    exact hoddBar
  have hperf : commutator C = ⊤ := Group.isPerfect_def.mp hCcomp.1.1
  have hqAlt : Nonempty (C ⧸ Subgroup.center C ≃* alternatingGroup (Fin n)) := by
    obtain ⟨eA⟩ := hA
    exact ⟨q.trans eA⟩
  have hcenter_dvd : Nat.card (Subgroup.center C) ∣ 6 :=
    CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.altSixSevenCentre_holds (n := n) hn C hperf hqAlt
  have hrankA : 2 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (alternatingGroup (Fin n))) := by
    rcases hn with rfl | rfl
    · exact CFSG.Quasithin.H13.Rank8.two_le_pRank_alternating_six
    · exact CFSG.Quasithin.H13.Rank8.two_le_pRank_alternating_seven
  let eA : ↥H ≃* ↥(alternatingGroup (Fin n)) := Classical.choice hA
  have hrankH : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eA]
    exact hrankA
  have hpRank3 : 2 ≤ CFSG.Open.pRank 3 C :=
    uc22p2214_two_le_pRank_of_surj (K := C) (Y := H) η hηsurj
      Nat.prime_three (by norm_num) hrankH
  exact
    { K := K
      hK := hK
      hbarK := hbarK
      C := C
      C_eq := rfl
      isComp := hCcomp
      map_eq := hmap
      η := η
      η_surj := hηsurj
      η_val := hηval
      ker_eq := hker
      q := q
      q_eq := hqeq
      oddCenter := hodd
      center_dvd := hcenter_dvd
      pRank3 := hpRank3 }

private theorem s168e3_exists_other_conjugate
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hs : s15 D.M V₀ V hV L = 2) {n : ℕ}
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n) :
    ∃ (H₂ : Subgroup (MulAut (Vtil V₀ V hV)))
      (φ : MulAut (Vtil V₀ V hV)),
      φ ∈ Mbar D.M V₀ V hV ∧
        H₂ = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∧
        H₂ ≠ lBar V₀ V hV L ∧ IsComponentOf H₂ (Mbar D.M V₀ V hV) ∧
        UC22.IsAlt ↥H₂ n := by
  let H₁ : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let S : Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
    {X | ∃ φ ∈ Mbar D.M V₀ V hV,
      X = H₁.map (MulAut.conj φ).toMonoidHom}
  have hS : S.ncard = 2 := by
    simpa only [S, H₁, s15, lBar] using hs
  have hlt : 1 < S.ncard := by rw [hS]; norm_num
  obtain ⟨H₂, hH₂S, hH₂ne⟩ := Set.exists_ne_of_one_lt_ncard hlt H₁
  obtain ⟨φ, hφ, hH₂eq⟩ := hH₂S
  have hcomp₂ : IsComponentOf H₂ (Mbar D.M V₀ V hV) := by
    rw [hH₂eq]
    exact CFSG.LocalAnalysis.RankThreeTheoremC.IsComponentOf.map_conj hcomp hφ
  have hA₂ : UC22.IsAlt ↥H₂ n := by
    obtain ⟨eA⟩ := hA
    rw [hH₂eq]
    exact ⟨(H₁.equivMapOfInjective (MulAut.conj φ).toMonoidHom
      (MulAut.conj φ).injective).symm.trans eA⟩
  exact ⟨H₂, φ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂⟩

private theorem s168e3_pRank_bar2_top_le_three
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M)) ≤ 3 := by
  have hbar : CFSG.AGLEmbedding.barM D.M D.M = ⊤ := by
    rw [CFSG.AGLEmbedding.barM, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  calc
    CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 D.M))
        = CFSG.Open.pRank 3 (CFSG.AGLEmbedding.barM D.M D.M) := by rw [hbar]
    _ = CFSG.Open.pRank 3 D.M :=
      CFSG.AGLEmbedding.pRank_barM_eq Nat.prime_three (by norm_num) D.M D.M le_rfl
    _ ≤ CFSG.Open.evenRank G :=
      CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3
        Nat.prime_three (by norm_num) D.M D.maxLocal.1
    _ = 3 := c.std.h3

private theorem s168e3_actualCover_common_center
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 2)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n) :
    ∃ (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
      (H₂ : Subgroup (MulAut (Vtil V₀ V hV)))
      (A₁ : S168e3ActualCover ψ (lBar V₀ V hV L))
      (A₂ : S168e3ActualCover ψ H₂),
      (∀ m : D.M, ψ (QuotientGroup.mk m) =
        actTil V₀ V hV ⟨m, le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
          c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ m.2⟩) ∧
      (∃ (φ : MulAut (Vtil V₀ V hV)), φ ∈ Mbar D.M V₀ V hV ∧
        H₂ = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom) ∧
      H₂ ≠ lBar V₀ V hV L ∧ IsComponentOf H₂ (Mbar D.M V₀ V hV) ∧
      UC22.IsAlt ↥H₂ n ∧ A₁.C ≠ A₂.C ∧
        (Subgroup.center A₁.C).map A₁.C.subtype = A₁.C ⊓ A₂.C ∧
        (Subgroup.center A₂.C).map A₂.C.subtype = A₁.C ⊓ A₂.C ∧
        Nat.card ↥(A₁.C ⊓ A₂.C) = 3 ∧
        Nat.card (Subgroup.center A₁.C) = 3 ∧
        Nat.card (Subgroup.center A₂.C) = 3 := by
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 c.setting.hyp16.hyp125
  let H₁ : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  have hA₁ : UC22.IsAlt ↥H₁ n := hA
  obtain ⟨H₂, φ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂⟩ :=
    s168e3_exists_other_conjugate hs hcomp hA
  let A₁ : S168e3ActualCover ψ H₁ :=
    s168e3_actualCoverData c hψ hcomp hn hA₁
  let A₂ : S168e3ActualCover ψ H₂ :=
    s168e3_actualCoverData c hψ hcomp₂ hn hA₂
  have hCne : A₁.C ≠ A₂.C := by
    intro hC
    have hH : H₁ = H₂ := by
      rw [← A₁.map_eq, ← A₂.map_eq, hC]
    exact hH₂ne hH.symm
  have hcommon := s168e3_common_center_of_two_components
    A₁.isComp A₂.isComp hCne A₁.pRank3 A₂.pRank3
    (s168e3_pRank_bar2_top_le_three c) A₁.oddCenter A₂.oddCenter
    A₁.center_dvd A₂.center_dvd
  exact ⟨ψ, H₂, A₁, A₂, hψ, ⟨φ, hφ, hH₂eq⟩, hH₂ne, hcomp₂, hA₂, hCne, hcommon.1,
    hcommon.2.1, hcommon.2.2.1, hcommon.2.2.2.1, hcommon.2.2.2.2⟩

private theorem s168e3_commSub_self
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥H) :
    commSub (commSub (⊤ : Subgroup W) H) H = commSub (⊤ : Subgroup W) H :=
  s16jp_commSub_commSub hperf (Y := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)

private theorem s168e3_U_inf_Z_left
    {W : Type} [CommGroup W] {H₁ : Subgroup (MulAut W)}
    {U₁ Z₁ Z₂ Z : Subgroup W}
    (hZ₁ : Z₁ = U₁ ⊓ fixV H₁) (hZ : Z = Z₁ ⊔ Z₂) (hfixZ : Z ≤ fixV H₁) :
    U₁ ⊓ Z = Z₁ := by
  apply le_antisymm
  · intro x hx
    rw [hZ₁]
    exact ⟨hx.1, hfixZ hx.2⟩
  · intro x hx
    have hxU₁ : x ∈ U₁ := ((hZ₁ ▸ hx) : x ∈ U₁ ⊓ fixV H₁).1
    have hxZ : x ∈ Z := by rw [hZ]; exact Subgroup.mem_sup_left hx
    exact ⟨hxU₁, hxZ⟩

private theorem s168e3_U_inf_Z_right
    {W : Type} [CommGroup W] {H₂ : Subgroup (MulAut W)}
    {U₂ Z₁ Z₂ Z : Subgroup W}
    (hZ₂ : Z₂ = U₂ ⊓ fixV H₂)
    (hZ : Z = Z₁ ⊔ Z₂) (hfixZ : Z ≤ fixV H₂) :
    U₂ ⊓ Z = Z₂ := by
  have hZ' : Z = Z₂ ⊔ Z₁ := by rw [hZ, sup_comm]
  exact s168e3_U_inf_Z_left (H₁ := H₂) (U₁ := U₂) (Z₁ := Z₂) (Z₂ := Z₁)
    hZ₂ hZ' hfixZ

private theorem s168e3_quotient_inf_eq_bot
    {W : Type} [CommGroup W] {U₁ U₂ Z₁ Z₂ Z : Subgroup W}
    (hZ : Z = Z₁ ⊔ Z₂) (hZ₁U₁ : Z₁ ≤ U₁) (hZ₂U₂ : Z₂ ≤ U₂)
    (hinfZ₁ : U₁ ⊓ U₂ ≤ Z₁) :
    U₁.map (QuotientGroup.mk' Z) ⊓ U₂.map (QuotientGroup.mk' Z) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨u₁, hu₁, hq₁⟩ := Subgroup.mem_map.mp hq.1
  obtain ⟨u₂, hu₂, hq₂⟩ := Subgroup.mem_map.mp hq.2
  have hqeq : (QuotientGroup.mk' Z) u₂ = (QuotientGroup.mk' Z) u₁ := by rw [hq₂, hq₁]
  have hz : u₁ * u₂⁻¹ ∈ Z := by
    have h1 : (QuotientGroup.mk' Z) (u₁ * u₂⁻¹) = 1 := by
      rw [map_mul, map_inv, hqeq, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (u₁ * u₂⁻¹)).mp h1
  obtain ⟨z₁, hz₁, z₂, hz₂, hzz⟩ :=
    Subgroup.mem_sup.mp (by rw [← hZ]; exact hz)
  have hz₁U₁ : z₁ ∈ U₁ := hZ₁U₁ hz₁
  have hz₂U₂ : z₂ ∈ U₂ := hZ₂U₂ hz₂
  have hmem : u₁ * z₁⁻¹ ∈ U₁ ⊓ U₂ := by
    constructor
    · exact U₁.mul_mem hu₁ (U₁.inv_mem hz₁U₁)
    · have h' : u₁ * z₁⁻¹ = z₂ * u₂ := by
        calc u₁ * z₁⁻¹ = (u₁ * u₂⁻¹) * u₂ * z₁⁻¹ := by group
          _ = (z₁ * z₂) * u₂ * z₁⁻¹ := by rw [← hzz]
          _ = z₂ * u₂ := by simp [mul_assoc, mul_comm]
      rw [h']
      exact U₂.mul_mem hz₂U₂ hu₂
  have hu₁Z₁ : u₁ ∈ Z₁ := by
    have h := Z₁.mul_mem (hinfZ₁ hmem) hz₁
    rwa [show (u₁ * z₁⁻¹) * z₁ = u₁ by group] at h
  have hZ₁Z : Z₁ ≤ Z := by rw [hZ]; exact le_sup_left
  rw [← hq₁]
  exact (QuotientGroup.eq_one_iff u₁).mpr (hZ₁Z hu₁Z₁)

private theorem s168e3_quotient_sup_eq_top
    {W : Type} [CommGroup W] {U₁ U₂ Z : Subgroup W} (hsup : U₁ ⊔ U₂ = ⊤) :
    U₁.map (QuotientGroup.mk' Z) ⊔ U₂.map (QuotientGroup.mk' Z) = ⊤ := by
  rw [← Subgroup.map_sup, hsup,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

private theorem s168e3_concrete_two_block
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 2)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n) :
    ∃ (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
      (H₂ : Subgroup (MulAut (Vtil V₀ V hV)))
      (A₁ : S168e3ActualCover ψ (lBar V₀ V hV L))
      (A₂ : S168e3ActualCover ψ H₂)
      (φ : MulAut (Vtil V₀ V hV))
      (U₁ U₂ Z₁ Z₂ Z : Subgroup (Vtil V₀ V hV))
      (Q₁ Q₂ : Subgroup (Vtil V₀ V hV ⧸ Z)),
      (∀ m : D.M, ψ (QuotientGroup.mk m) =
        actTil V₀ V hV ⟨m, le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
          c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ m.2⟩) ∧
      φ ∈ Mbar D.M V₀ V hV ∧
      H₂ = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∧
      H₂ ≠ lBar V₀ V hV L ∧ IsComponentOf H₂ (Mbar D.M V₀ V hV) ∧
      UC22.IsAlt ↥H₂ n ∧
      A₁.C ≠ A₂.C ∧
      (Subgroup.center A₁.C).map A₁.C.subtype = A₁.C ⊓ A₂.C ∧
      (Subgroup.center A₂.C).map A₂.C.subtype = A₁.C ⊓ A₂.C ∧
      Nat.card ↥(A₁.C ⊓ A₂.C) = 3 ∧
      Nat.card (Subgroup.center A₁.C) = 3 ∧
      Nat.card (Subgroup.center A₂.C) = 3 ∧
      U₁ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∧
      U₂ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) H₂ ∧
      Z₁ = U₁ ⊓ fixV (lBar V₀ V hV L) ∧
      Z₂ = U₂ ⊓ fixV H₂ ∧
      Z = Z₁ ⊔ Z₂ ∧ U₂ = U₁.map φ.toMonoidHom ∧
      Z₂ = Z₁.map φ.toMonoidHom ∧ U₁ ⊔ U₂ = ⊤ ∧
      commSub U₁ H₂ = ⊥ ∧ commSub U₂ (lBar V₀ V hV L) = ⊥ ∧
      commSub U₁ (lBar V₀ V hV L) = U₁ ∧ commSub U₂ H₂ = U₂ ∧
      U₁ ⊓ U₂ ≤ Z₁ ∧ U₁ ⊓ U₂ ≤ Z₂ ∧
      Z ≤ fixV (lBar V₀ V hV L) ∧ Z ≤ fixV H₂ ∧
      U₁ ⊓ Z = Z₁ ∧ U₂ ⊓ Z = Z₂ ∧
      Q₁ = U₁.map (QuotientGroup.mk' Z) ∧ Q₂ = U₂.map (QuotientGroup.mk' Z) ∧
      Q₁ ⊔ Q₂ = ⊤ ∧ Q₁ ⊓ Q₂ = ⊥ := by
  obtain ⟨ψ, H₂, A₁, A₂, hψ, hconj, hH₂ne, hcomp₂, hA₂, hCne,
    hcent₁, hcent₂, hcentcard, hcent₁card, hcent₂card⟩ :=
    s168e3_actualCover_common_center c hcomp hs hn hA
  obtain ⟨φ, hφ, hH₂eq⟩ := hconj
  let H₁ : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  have h_two : Set.ncard
      {X : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ m ∈ Mbar D.M V₀ V hV, X = H₁.map (MulAut.conj m).toMonoidHom} = 2 := by
    simpa only [H₁, lBar, s15] using hs
  obtain ⟨-, huniv⟩ := c23a_two_conj h_two
  have hφmap : H₁.map (MulAut.conj φ).toMonoidHom ≠ H₁ := by
    intro h
    apply hH₂ne
    rw [hH₂eq, h]
  have hφn : φ ∉ Subgroup.normalizer (H₁ : Set (MulAut (Vtil V₀ V hV))) := by
    intro hN
    exact hφmap (Subgroup.mem_normalizer_iff_map_conj_eq.mp hN)
  have huniv' := huniv φ hφ hφmap
  let U₁ : Subgroup (Vtil V₀ V hV) := commSub (⊤ : Subgroup _) H₁
  let U₂ : Subgroup (Vtil V₀ V hV) := commSub (⊤ : Subgroup _) H₂
  let Z₁ : Subgroup (Vtil V₀ V hV) := U₁ ⊓ fixV H₁
  let Z₂ : Subgroup (Vtil V₀ V hV) := U₂ ⊓ fixV H₂
  let Z : Subgroup (Vtil V₀ V hV) := Z₁ ⊔ Z₂
  have hU₂φ : U₂ = U₁.map φ.toMonoidHom := by
    dsimp only [U₁, U₂]
    rw [show H₂ = H₁.map (MulAut.conj φ).toMonoidHom from hH₂eq,
      s15_Infra_commSub_top_map_conj]
  have hZ₂φ : Z₂ = Z₁.map φ.toMonoidHom := by
    have hfixφ : fixV H₂ = (fixV H₁).map φ.toMonoidHom := by
      rw [hH₂eq, fixV_map_conj_eq]
    dsimp only [Z₁, Z₂]
    rw [hU₂φ, hfixφ, ← Subgroup.map_inf_eq _ _ _ φ.injective]
  obtain ⟨t, htA, ht2, ht1, htrk, hW⟩ := c.conc
  have hcrossHyp : ∀ g ∈ Mbar D.M V₀ V hV,
      g ∉ Subgroup.normalizer (H₁ : Set (MulAut (Vtil V₀ V hV))) →
      commSub (commSub (⊤ : Subgroup _) H₁) (H₁.map (MulAut.conj g).toMonoidHom) = ⊥ :=
    fun g hg hgn => (hW.2.1 g hg hgn).2
  have hone : H₁.map (MulAut.conj (1 : MulAut (Vtil V₀ V hV))).toMonoidHom = H₁ := by
    ext x
    simp
  have hne1φ : H₁.map (MulAut.conj (1 : MulAut (Vtil V₀ V hV))).toMonoidHom ≠
      H₁.map (MulAut.conj φ).toMonoidHom := by
    rw [hone]
    exact hφmap.symm
  have hfixes := CFSG.Quasithin.ConjugateSection.commSub_le_fixV_of_conj_ne
    (A := Mbar D.M V₀ V hV) (H := H₁) hcrossHyp
    (a := 1) (b := φ) (Mbar D.M V₀ V hV).one_mem hφ hne1φ
  have hfixes1 := hfixes.1
  have hfixes2 := hfixes.2
  rw [hone] at hfixes1
  rw [hone] at hfixes2
  have hfixU₁ : U₁ ≤ fixV H₂ := by
    dsimp only [U₁]
    rw [hH₂eq]
    exact hfixes1
  have hfixU₂ : U₂ ≤ fixV H₁ := by
    dsimp only [U₂]
    rw [hH₂eq]
    exact hfixes2
  have hcross12 : commSub U₁ H₂ = ⊥ := by
    rw [hH₂eq]
    exact hcrossHyp φ hφ hφn
  have hcross21 : commSub U₂ H₁ = ⊥ := commSub_eq_bot_iff.mpr hfixU₂
  have hsup : U₁ ⊔ U₂ = ⊤ := by
    apply le_antisymm le_top
    rw [← hW.1]
    refine iSup_le fun X => iSup_le fun hX => ?_
    obtain ⟨m, hm, rfl⟩ := hX
    rcases huniv'.1 m hm with hfix | hswap
    · have hmap : (commSub (⊤ : Subgroup _) H₁).map m.toMonoidHom = U₁ := by
        dsimp only [U₁]
        rw [← s15_Infra_commSub_top_map_conj H₁ m, hfix]
      rw [hmap]
      exact le_sup_left
    · have hmap : (commSub (⊤ : Subgroup _) H₁).map m.toMonoidHom = U₂ := by
        dsimp only [U₂]
        rw [← s15_Infra_commSub_top_map_conj H₁ m, hswap, ← hH₂eq]
      rw [hmap]
      exact le_sup_right
  have hperf₁ : Group.IsPerfect ↥H₁ := Group.isPerfect_def.mpr hcomp.2.2.1
  have hperf₂ : Group.IsPerfect ↥H₂ := Group.isPerfect_def.mpr hcomp₂.2.2.1
  have hself₁ : commSub U₁ H₁ = U₁ := by
    dsimp only [U₁]
    exact s168e3_commSub_self hperf₁
  have hself₂ : commSub U₂ H₂ = U₂ := by
    dsimp only [U₂]
    exact s168e3_commSub_self hperf₂
  have hinfZ₁ : U₁ ⊓ U₂ ≤ Z₁ := by
    intro x hx
    dsimp only [Z₁]
    exact ⟨hx.1, hfixU₂ hx.2⟩
  have hinfZ₂ : U₁ ⊓ U₂ ≤ Z₂ := by
    intro x hx
    dsimp only [Z₂]
    exact ⟨hx.2, hfixU₁ hx.1⟩
  have hZ₁fix : Z₁ ≤ fixV H₁ := by dsimp only [Z₁]; exact inf_le_right
  have hZ₂fix₁ : Z₂ ≤ fixV H₁ := by
    dsimp only [Z₂]
    exact inf_le_left.trans hfixU₂
  have hZ₂fix : Z₂ ≤ fixV H₂ := by dsimp only [Z₂]; exact inf_le_right
  have hZ₁fix₂ : Z₁ ≤ fixV H₂ := by
    dsimp only [Z₁]
    exact inf_le_left.trans hfixU₁
  have hfixZ₁ : Z ≤ fixV H₁ := by
    dsimp only [Z]
    exact sup_le hZ₁fix hZ₂fix₁
  have hfixZ₂ : Z ≤ fixV H₂ := by
    dsimp only [Z]
    exact sup_le hZ₁fix₂ hZ₂fix
  have hUZ₁ : U₁ ⊓ Z = Z₁ :=
    s168e3_U_inf_Z_left (H₁ := H₁) (U₁ := U₁) (Z₁ := Z₁) (Z₂ := Z₂) rfl rfl hfixZ₁
  have hUZ₂ : U₂ ⊓ Z = Z₂ :=
    s168e3_U_inf_Z_right (H₂ := H₂) (U₂ := U₂)
      (Z₁ := Z₁) (Z₂ := Z₂) rfl rfl hfixZ₂
  let Q₁ : Subgroup (Vtil V₀ V hV ⧸ Z) := U₁.map (QuotientGroup.mk' Z)
  let Q₂ : Subgroup (Vtil V₀ V hV ⧸ Z) := U₂.map (QuotientGroup.mk' Z)
  have hQsup : Q₁ ⊔ Q₂ = ⊤ := s168e3_quotient_sup_eq_top hsup
  have hQinf : Q₁ ⊓ Q₂ = ⊥ :=
    s168e3_quotient_inf_eq_bot rfl inf_le_left inf_le_left hinfZ₁
  exact ⟨ψ, H₂, A₁, A₂, φ, U₁, U₂, Z₁, Z₂, Z, Q₁, Q₂,
    hψ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂, hCne,
    hcent₁, hcent₂, hcentcard, hcent₁card, hcent₂card,
    rfl, rfl, rfl, rfl, rfl, hU₂φ, hZ₂φ, hsup, hcross12, hcross21,
    hself₁, hself₂, hinfZ₁, hinfZ₂, hfixZ₁, hfixZ₂, hUZ₁, hUZ₂,
    rfl, rfl, hQsup, hQinf⟩

private theorem s168e3_quotHomOn_rangeRestrict_apply
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {C : Subgroup W}
    (hH : H ≤ stabSub C) (h : H) (w : W) :
    QuotientGroup.mk' C ((h : MulAut W) w) =
      ((v3qb_quotHomOn C hH).rangeRestrict h : MulAut (W ⧸ C))
        (QuotientGroup.mk' C w) := by
  rfl

private theorem s168e3_quotHomOn_rangeRestrict_injective_of_realizes
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {C I Z₀ : Subgroup W}
    (hH : H ≤ stabSub C) {D : FFModel} (hD : D.Faithful)
    {π : D.Gam →* ↥H} (hReal : D.RealizesVia H I Z₀ π)
    (hIC : I ⊓ C ≤ Z₀) :
    Function.Injective (v3qb_quotHomOn C hH).rangeRestrict := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxmul : (x : MulAut W) = 1 := by
    refine CFSG.Quasithin.G64.RealizesVia.eq_one_of_trivial hD hReal x.2 ?_
    intro u hu
    have hxI : (x : MulAut W) u ∈ I := hReal.2.2.2.1 x u hu
    have hq1 : ((v3qb_quotHomOn C hH).rangeRestrict x : MulAut (W ⧸ C))
        (QuotientGroup.mk' C u) = QuotientGroup.mk' C u := by
      rw [hx]
      rfl
    have heq : QuotientGroup.mk' C ((x : MulAut W) u) = QuotientGroup.mk' C u := by
      rw [s168e3_quotHomOn_rangeRestrict_apply hH x u, hq1]
    have hdiv : (x : MulAut W) u * u⁻¹ ∈ C := (mk_eq_mk_iff _ _).mp heq
    exact hIC ⟨I.mul_mem hxI (I.inv_mem hu), hdiv⟩
  exact Subtype.ext hxmul

private theorem s168e3_concrete_two_block_left_action
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 2)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    ∃ (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
      (H₂ : Subgroup (MulAut (Vtil V₀ V hV)))
      (A₁ : S168e3ActualCover ψ (lBar V₀ V hV L))
      (A₂ : S168e3ActualCover ψ H₂)
      (φ : MulAut (Vtil V₀ V hV))
      (U₁ U₂ Z₁ Z₂ Z : Subgroup (Vtil V₀ V hV))
      (Q₁ Q₂ : Subgroup (Vtil V₀ V hV ⧸ Z)),
      (∀ m : D.M, ψ (QuotientGroup.mk m) =
        actTil V₀ V hV ⟨m, le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
          c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ m.2⟩) ∧
      φ ∈ Mbar D.M V₀ V hV ∧
      H₂ = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∧
      H₂ ≠ lBar V₀ V hV L ∧ IsComponentOf H₂ (Mbar D.M V₀ V hV) ∧
      UC22.IsAlt ↥H₂ n ∧
      A₁.C ≠ A₂.C ∧
      (Subgroup.center A₁.C).map A₁.C.subtype = A₁.C ⊓ A₂.C ∧
      (Subgroup.center A₂.C).map A₂.C.subtype = A₁.C ⊓ A₂.C ∧
      Nat.card ↥(A₁.C ⊓ A₂.C) = 3 ∧
      Nat.card (Subgroup.center A₁.C) = 3 ∧
      Nat.card (Subgroup.center A₂.C) = 3 ∧
      U₁ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∧
      U₂ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) H₂ ∧
      Z₁ = U₁ ⊓ fixV (lBar V₀ V hV L) ∧
      Z₂ = U₂ ⊓ fixV H₂ ∧
      Z = Z₁ ⊔ Z₂ ∧ U₂ = U₁.map φ.toMonoidHom ∧
      Z₂ = Z₁.map φ.toMonoidHom ∧ U₁ ⊔ U₂ = ⊤ ∧
      commSub U₁ H₂ = ⊥ ∧ commSub U₂ (lBar V₀ V hV L) = ⊥ ∧
      commSub U₁ (lBar V₀ V hV L) = U₁ ∧ commSub U₂ H₂ = U₂ ∧
      U₁ ⊓ U₂ ≤ Z₁ ∧ U₁ ⊓ U₂ ≤ Z₂ ∧
      Z ≤ fixV (lBar V₀ V hV L) ∧ Z ≤ fixV H₂ ∧
      U₁ ⊓ Z = Z₁ ∧ U₂ ⊓ Z = Z₂ ∧
      Q₁ = U₁.map (QuotientGroup.mk' Z) ∧ Q₂ = U₂.map (QuotientGroup.mk' Z) ∧
      Q₁ ⊔ Q₂ = ⊤ ∧ Q₁ ⊓ Q₂ = ⊥ ∧
      ∃ (Hq : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z)))
        (theta : (lBar V₀ V hV L) →* Hq),
        (∃ (hZ : Z ≤ fixV (lBar V₀ V hV L)),
          Hq = (v3qb_quotHomOn Z (le_stabSub_of_le_fixV hZ)).range ∧
          (∀ h : lBar V₀ V hV L,
            (theta h : MulAut (Vtil V₀ V hV ⧸ Z)) =
              ((v3qb_quotHomOn Z (le_stabSub_of_le_fixV hZ)).rangeRestrict h :
                MulAut (Vtil V₀ V hV ⧸ Z))) ∧
          Function.Surjective theta ∧ Function.Injective theta ∧
          ∀ (h : lBar V₀ V hV L) (w : Vtil V₀ V hV),
            QuotientGroup.mk' Z ((h : MulAut (Vtil V₀ V hV)) w) =
              ((theta h : MulAut (Vtil V₀ V hV ⧸ Z)) (QuotientGroup.mk' Z w))) := by
  obtain ⟨ψ, H₂, A₁, A₂, φ, U₁, U₂, Z₁, Z₂, Z, Q₁, Q₂,
    hψ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂, hCne,
    hcent₁, hcent₂, hcentcard, hcent₁card, hcent₂card,
    hU₁eq, hU₂eq, hZ₁eq, hZ₂eq, hZeq, hU₂φ, hZ₂φ, hsup,
    hcross12, hcross21, hself₁, hself₂, hinfZ₁, hinfZ₂, hfixZ₁, hfixZ₂,
    hUZ₁, hUZ₂, hQ₁eq, hQ₂eq, hQsup, hQinf⟩ :=
    s168e3_concrete_two_block c hcomp hs hn hA
  have hU₁eq' : U₁ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L) := by
    simpa only [lBar] using hU₁eq
  have hsum0 : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 3 := by
    simpa only [wTil] using hsum
  have hZ₁eq' : Z₁ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L) ⊓
      fixV (lBar V₀ V hV L) := by
    rw [hZ₁eq, hU₁eq']
  have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) U₁ Z₁ 3 := by
    rw [hU₁eq', hZ₁eq']
    exact hsum0
  obtain ⟨I, hZI, hind, hsupI, hN⟩ := hsum'
  have hI0U : I 0 ≤ U₁ := by
    calc I 0 ≤ ⨆ i : Fin 3, I i := le_iSup (fun i : Fin 3 => I i) 0
      _ ≤ Z₁ ⊔ ⨆ i : Fin 3, I i := le_sup_right
      _ = U₁ := hsupI
  have hIC : I 0 ⊓ Z ≤ Z₁ := by
    rw [← hUZ₁]
    exact inf_le_inf hI0U le_rfl
  have hH : lBar V₀ V hV L ≤ stabSub Z := le_stabSub_of_le_fixV hfixZ₁
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hN0 : (FFModel.altDn n).Realizes (lBar V₀ V hV L) (I 0) Z₁ := hN 0
  obtain ⟨π, hReal⟩ := hN0
  have hD : (FFModel.altDn n).Faithful := FFC.altDn_faithful hn5
  have hinj : Function.Injective (v3qb_quotHomOn Z hH).rangeRestrict :=
    s168e3_quotHomOn_rangeRestrict_injective_of_realizes hH hD hReal hIC
  have hsurj : Function.Surjective (v3qb_quotHomOn Z hH).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have hrepr : ∀ (h : lBar V₀ V hV L) (w : Vtil V₀ V hV),
      QuotientGroup.mk' Z ((h : MulAut (Vtil V₀ V hV)) w) =
        ((v3qb_quotHomOn Z hH).rangeRestrict h : MulAut (Vtil V₀ V hV ⧸ Z))
          (QuotientGroup.mk' Z w) :=
    fun h w => s168e3_quotHomOn_rangeRestrict_apply hH h w
  exact ⟨ψ, H₂, A₁, A₂, φ, U₁, U₂, Z₁, Z₂, Z, Q₁, Q₂,
    hψ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂, hCne,
    hcent₁, hcent₂, hcentcard, hcent₁card, hcent₂card,
    hU₁eq, hU₂eq, hZ₁eq, hZ₂eq, hZeq, hU₂φ, hZ₂φ, hsup,
    hcross12, hcross21, hself₁, hself₂, hinfZ₁, hinfZ₂, hfixZ₁, hfixZ₂,
    hUZ₁, hUZ₂, hQ₁eq, hQ₂eq, hQsup, hQinf,
    ⟨(v3qb_quotHomOn Z hH).range, (v3qb_quotHomOn Z hH).rangeRestrict,
      hfixZ₁, rfl, (fun h => rfl), hsurj, hinj, hrepr⟩⟩

private def S168e3QuotAction
    {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) (Z : Subgroup W)
    (hZ : Z ≤ fixV H) (Hq : Subgroup (MulAut (W ⧸ Z))) (theta : H →* Hq) : Prop :=
  Hq = (v3qb_quotHomOn Z (le_stabSub_of_le_fixV hZ)).range ∧
    (∀ h : H, (theta h : MulAut (W ⧸ Z)) =
      ((v3qb_quotHomOn Z (le_stabSub_of_le_fixV hZ)).rangeRestrict h :
        MulAut (W ⧸ Z))) ∧
    Function.Surjective theta ∧ Function.Injective theta ∧
    ∀ (h : H) (w : W),
      QuotientGroup.mk' Z ((h : MulAut W) w) =
        ((theta h : MulAut (W ⧸ Z)) (QuotientGroup.mk' Z w))

private theorem s168e3_named_family_independence
    {W : Type} [CommGroup W] {U Z₀ Z : Subgroup W} (ρ : W →* W ⧸ Z)
    (hρker : U ⊓ ρ.ker ≤ Z₀) (hZ₀U : Z₀ ≤ U) (hZ₀map : Z₀.map ρ = ⊥)
    {I : Fin 3 → Subgroup W} (hIU : ∀ i, I i ≤ U) (_hZI : ∀ i, Z₀ ≤ I i)
    (hind : ∀ i, I i ⊓ (Z₀ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ Z₀) :
    ∀ i : Fin 3, (I i).map ρ ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), (I j).map ρ) = ⊥ := by
  intro i
  let f : ↥U →* W ⧸ Z := ρ.comp U.subtype
  have hZ₀ker : Z₀ ≤ ρ.ker := (Subgroup.map_eq_bot_iff Z₀).mp hZ₀map
  have hkerf : f.ker = Z₀.subgroupOf U := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact hρker ⟨x.2, hx⟩
    · intro hx
      exact hZ₀ker hx
  let K : Subgroup W := I i
  let B : Subgroup W := Z₀ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j
  have hKU : K ≤ U := hIU i
  have hBU : B ≤ U := by
    dsimp only [B]
    exact sup_le hZ₀U (iSup_le fun j => iSup_le fun _ => hIU j)
  have hKB : K ⊓ B ≤ Z₀ := by
    simpa only [K, B] using hind i
  have hmap := CFSG.GroupTheory.map_subgroupOf_inf (X := U) (D := Z₀) (ψ := f) hkerf
    K (K' := B) (le_sup_left : Z₀ ≤ B)
  have hleftbot : ((K ⊓ B).subgroupOf U).map f = ⊥ := by
    rw [show f = ρ.comp U.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le (hKB.trans hZ₀U)]
    have hle : (K ⊓ B).map ρ ≤ Z₀.map ρ := Subgroup.map_mono hKB
    rw [hZ₀map] at hle
    exact le_bot_iff.mp hle
  have hKmap : (K.subgroupOf U).map f = K.map ρ := by
    rw [show f = ρ.comp U.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hKU]
  have hBmap : (B.subgroupOf U).map f = B.map ρ := by
    rw [show f = ρ.comp U.subtype from rfl, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hBU]
  have hBmap' : B.map ρ = ⨆ (j : Fin 3) (_ : j ≠ i), (I j).map ρ := by
    dsimp only [B]
    rw [Subgroup.map_sup, Subgroup.map_iSup, hZ₀map, bot_sup_eq]
    simp only [Subgroup.map_iSup]
  rw [hleftbot, hKmap, hBmap, hBmap'] at hmap
  simpa only [K] using hmap.symm

private theorem s168e3_concrete_two_block_three_family
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 2)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    ∃ (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
      (H₂ : Subgroup (MulAut (Vtil V₀ V hV)))
      (A₁ : S168e3ActualCover ψ (lBar V₀ V hV L))
      (A₂ : S168e3ActualCover ψ H₂)
      (φ : MulAut (Vtil V₀ V hV))
      (U₁ U₂ Z₁ Z₂ Z : Subgroup (Vtil V₀ V hV))
      (Q₁ Q₂ : Subgroup (Vtil V₀ V hV ⧸ Z)),
      (∀ m : D.M, ψ (QuotientGroup.mk m) =
        actTil V₀ V hV ⟨m, le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
          c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ m.2⟩) ∧
      φ ∈ Mbar D.M V₀ V hV ∧
      H₂ = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∧
      H₂ ≠ lBar V₀ V hV L ∧ IsComponentOf H₂ (Mbar D.M V₀ V hV) ∧
      UC22.IsAlt ↥H₂ n ∧
      A₁.C ≠ A₂.C ∧
      (Subgroup.center A₁.C).map A₁.C.subtype = A₁.C ⊓ A₂.C ∧
      (Subgroup.center A₂.C).map A₂.C.subtype = A₁.C ⊓ A₂.C ∧
      Nat.card ↥(A₁.C ⊓ A₂.C) = 3 ∧
      Nat.card (Subgroup.center A₁.C) = 3 ∧
      Nat.card (Subgroup.center A₂.C) = 3 ∧
      U₁ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∧
      U₂ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) H₂ ∧
      Z₁ = U₁ ⊓ fixV (lBar V₀ V hV L) ∧
      Z₂ = U₂ ⊓ fixV H₂ ∧
      Z = Z₁ ⊔ Z₂ ∧ U₂ = U₁.map φ.toMonoidHom ∧
      Z₂ = Z₁.map φ.toMonoidHom ∧ U₁ ⊔ U₂ = ⊤ ∧
      commSub U₁ H₂ = ⊥ ∧ commSub U₂ (lBar V₀ V hV L) = ⊥ ∧
      commSub U₁ (lBar V₀ V hV L) = U₁ ∧ commSub U₂ H₂ = U₂ ∧
      U₁ ⊓ U₂ ≤ Z₁ ∧ U₁ ⊓ U₂ ≤ Z₂ ∧
      Z ≤ fixV (lBar V₀ V hV L) ∧ Z ≤ fixV H₂ ∧
      U₁ ⊓ Z = Z₁ ∧ U₂ ⊓ Z = Z₂ ∧
      Q₁ = U₁.map (QuotientGroup.mk' Z) ∧ Q₂ = U₂.map (QuotientGroup.mk' Z) ∧
      Q₁ ⊔ Q₂ = ⊤ ∧ Q₁ ⊓ Q₂ = ⊥ ∧
      ∃ (Hq₁ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z)))
        (theta₁ : (lBar V₀ V hV L) →* Hq₁)
        (hZ₁ : Z ≤ fixV (lBar V₀ V hV L)),
        S168e3QuotAction (lBar V₀ V hV L) Z hZ₁ Hq₁ theta₁ ∧
      ∃ (I : Fin 3 → Subgroup (Vtil V₀ V hV))
        (_hZI : ∀ i, Z₁ ≤ I i)
        (_hind : ∀ i, I i ⊓ (Z₁ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ Z₁)
        (_hsupI : Z₁ ⊔ ⨆ i : Fin 3, I i = U₁)
        (_hsumU : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
          (lBar V₀ V hV L) U₁ Z₁ 3)
        (_hN : ∀ i : Fin 3, AlternatingNatural (lBar V₀ V hV L) (I i) Z₁ n)
        (I₂ : Fin 3 → Subgroup (Vtil V₀ V hV))
        (_hI₂ : ∀ i, I₂ i = (I i).map φ.toMonoidHom)
        (Hq₂ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z)))
        (theta₂ : H₂ →* Hq₂)
        (hZ₂ : Z ≤ fixV H₂),
        S168e3QuotAction H₂ Z hZ₂ Hq₂ theta₂ ∧
      ∃ (S₁ S₂ : Fin 3 → Subgroup (Vtil V₀ V hV ⧸ Z)),
        (∀ i, S₁ i = (I i).map (QuotientGroup.mk' Z)) ∧
        (∀ i, S₂ i = (I₂ i).map (QuotientGroup.mk' Z)) ∧
        (∀ i, S₂ i = (I i).map ((QuotientGroup.mk' Z).comp φ.toMonoidHom)) ∧
        (∀ i, AlternatingNatural Hq₁ (S₁ i) ⊥ n) ∧
        (∀ i, AlternatingNatural Hq₂ (S₂ i) ⊥ n) ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z n) Hq₁ Q₁ ⊥ 3 ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z n) Hq₂ Q₂ ⊥ 3 ∧
        (⨆ i : Fin 3, S₁ i) = Q₁ ∧
        (⨆ i : Fin 3, S₂ i) = Q₂ ∧
        (∀ i : Fin 3,
          S₁ i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S₁ j) = ⊥) ∧
        (∀ i : Fin 3,
          S₂ i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S₂ j) = ⊥) := by
  obtain ⟨ψ, H₂, A₁, A₂, φ, U₁, U₂, Z₁, Z₂, Z, Q₁, Q₂,
    hψ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂, hCne,
    hcent₁, hcent₂, hcentcard, hcent₁card, hcent₂card,
    hU₁eq, hU₂eq, hZ₁eq, hZ₂eq, hZeq, hU₂φ, hZ₂φ, hsup,
    hcross12, hcross21, hself₁, hself₂, hinfZ₁, hinfZ₂, hfixZ₁, hfixZ₂,
    hUZ₁, hUZ₂, hQ₁eq, hQ₂eq, hQsup, hQinf,
    Hq₁, theta₁, hleftZ, hleftHqEq, hleftThetaVal, hleftSurj, hleftInj, hleftRepr⟩ :=
    s168e3_concrete_two_block_left_action c hcomp hs hn hA hsum
  have hU₁eq' : U₁ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L) := by
    simpa only [lBar] using hU₁eq
  have hsum0 : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) 3 := by
    simpa only [wTil] using hsum
  have hZ₁eq' : Z₁ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV L) ⊓
      fixV (lBar V₀ V hV L) := by
    rw [hZ₁eq, hU₁eq']
  have hsumU : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) U₁ Z₁ 3 := by
    rw [hU₁eq', hZ₁eq']
    exact hsum0
  have hsumU' : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) U₁ Z₁ 3 := hsumU
  obtain ⟨I, hZI, hind, hsupI, hN⟩ := hsumU'
  let ρ : Vtil V₀ V hV →* (Vtil V₀ V hV ⧸ Z) := QuotientGroup.mk' Z
  let I₂ : Fin 3 → Subgroup (Vtil V₀ V hV) := fun i => (I i).map φ.toMonoidHom
  let S₁ : Fin 3 → Subgroup (Vtil V₀ V hV ⧸ Z) := fun i => (I i).map ρ
  let S₂ : Fin 3 → Subgroup (Vtil V₀ V hV ⧸ Z) := fun i => (I₂ i).map ρ
  have hρker : ρ.ker = Z := QuotientGroup.ker_mk' Z
  have hIU₁ : ∀ i : Fin 3, I i ≤ U₁ := by
    intro i
    rw [← hsupI]
    exact le_sup_of_le_right (le_iSup (fun i : Fin 3 => I i) i)
  have hZ₁U : Z₁ ≤ U₁ := by
    rw [← hsupI]
    exact le_sup_left
  have hU₁ker : U₁ ⊓ ρ.ker ≤ Z₁ := by
    rw [hρker, hUZ₁]
  have hZ₁map : Z₁.map ρ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hρker, hZeq]
    exact le_sup_left
  have hH₁ : lBar V₀ V hV L ≤ stabSub Z := le_stabSub_of_le_fixV hleftZ
  have htheta₁_repr_all : ∀ (h : lBar V₀ V hV L) (w : Vtil V₀ V hV),
      ρ ((h : MulAut (Vtil V₀ V hV)) w) =
        ((theta₁ h : MulAut (Vtil V₀ V hV ⧸ Z)) (ρ w)) := by
    intro h w
    rw [hleftThetaVal h]
    exact s168e3_quotHomOn_rangeRestrict_apply hH₁ h w
  have hNat₁ : ∀ j : Fin 3, AlternatingNatural Hq₁ (S₁ j) ⊥ n := by
    intro j
    have hR : (FFModel.altDn n).Realizes (lBar V₀ V hV L) (I j) Z₁ := by
      simpa only [AlternatingNatural] using hN j
    have hkerj : I j ⊓ ρ.ker ≤ Z₁ := by
      rw [hρker]
      exact (inf_le_inf (hIU₁ j) le_rfl).trans_eq hUZ₁
    have hres := realizes_map_of_surjective_of_inf_ker_le (hR := hR) (ρ := ρ)
      (hρ := QuotientGroup.mk'_surjective Z) (hker := hkerj)
      (θ := theta₁) (hθ := hleftSurj) (he := htheta₁_repr_all)
    rw [hZ₁map] at hres
    simpa only [S₁, AlternatingNatural] using hres
  have hSum₁ : SumOfNat (fun H U Z => AlternatingNatural H U Z n) Hq₁ Q₁ ⊥ 3 := by
    have h := sumOfNat_map_of_inf_ker_le (hS := hsumU) (ρ := ρ)
      (N := fun H U Z => AlternatingNatural H U Z n)
      (N' := fun H U Z => AlternatingNatural H U Z n)
      (H := lBar V₀ V hV L) (H' := Hq₁) (U := U₁) (Z := Z₁) (k := 3)
      hU₁ker
      (fun I' _ hI'U hNI' => by
        have hR : (FFModel.altDn n).Realizes (lBar V₀ V hV L) I' Z₁ := by
          simpa only [AlternatingNatural] using hNI'
        have hker' : I' ⊓ ρ.ker ≤ Z₁ := by
          rw [hρker]
          exact (inf_le_inf hI'U le_rfl).trans_eq hUZ₁
        have hres := realizes_map_of_surjective_of_inf_ker_le (hR := hR) (ρ := ρ)
          (hρ := QuotientGroup.mk'_surjective Z) (hker := hker')
          (θ := theta₁) (hθ := hleftSurj) (he := htheta₁_repr_all)
        simpa only [AlternatingNatural] using hres)
    rwa [hZ₁map, ← hQ₁eq] at h
  have hθker : φ.toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff φ.toMonoidHom).mpr φ.injective
  have hkerφ : φ.toMonoidHom.ker ≤ Z₁ := by
    rw [hθker]
    exact bot_le
  have hH₂eq' : H₂ = (lBar V₀ V hV L).map (↑(MulAut.conj φ)) := by
    rw [hH₂eq]
    rfl
  let eφ : ↥(lBar V₀ V hV L) ≃* ↥H₂ :=
    (MulEquiv.subgroupMap (MulAut.conj φ) (lBar V₀ V hV L)).trans
      (MulEquiv.subgroupCongr hH₂eq'.symm)
  have heφ : ∀ (h : lBar V₀ V hV L) (w : Vtil V₀ V hV),
      φ ((h : MulAut (Vtil V₀ V hV)) w) =
        ((eφ h : ↥H₂) : MulAut (Vtil V₀ V hV)) (φ w) := by
    intro h w
    simp only [eφ, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply,
      MulAut.conj_apply]
    simp
  have hsupI₂ : Z₂ ⊔ ⨆ i : Fin 3, I₂ i = U₂ := by
    have h := congrArg (fun K : Subgroup (Vtil V₀ V hV) => K.map φ.toMonoidHom) hsupI
    rw [Subgroup.map_sup, Subgroup.map_iSup, ← hZ₂φ, ← hU₂φ] at h
    simpa only [I₂] using h
  have hIU₂ : ∀ i : Fin 3, I₂ i ≤ U₂ := by
    intro i
    change (I i).map φ.toMonoidHom ≤ U₂
    rw [hU₂φ]
    exact Subgroup.map_mono (hIU₁ i)
  have hZI₂ : ∀ i : Fin 3, Z₂ ≤ I₂ i := by
    intro i
    change Z₂ ≤ (I i).map φ.toMonoidHom
    rw [hZ₂φ]
    exact Subgroup.map_mono (hZI i)
  have hind₂ : ∀ i : Fin 3,
      I₂ i ⊓ (Z₂ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I₂ j) ≤ Z₂ := by
    intro i
    have h := Subgroup.map_mono (f := φ.toMonoidHom) (hind i)
    rw [Subgroup.map_inf_eq (I i) (Z₁ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j)
      φ.toMonoidHom φ.injective, Subgroup.map_sup, Subgroup.map_iSup] at h
    simpa only [Subgroup.map_iSup, ← hZ₂φ, I₂] using h
  have hNatI₂ : ∀ j : Fin 3, AlternatingNatural H₂ (I₂ j) Z₂ n := by
    intro j
    have hR : (FFModel.altDn n).Realizes (lBar V₀ V hV L) (I j) Z₁ := by
      simpa only [AlternatingNatural] using hN j
    have hres := s16k_realizes_map (hR := hR) (ρ := φ.toMonoidHom) hkerφ
      eφ.toMonoidHom eφ.surjective heφ
    simpa only [I₂, ← hZ₂φ, AlternatingNatural] using hres
  have hZ₂U : Z₂ ≤ U₂ := by
    rw [← hsupI₂]
    exact le_sup_left
  have hU₂ker : U₂ ⊓ ρ.ker ≤ Z₂ := by
    rw [hρker, hUZ₂]
  have hZ₂map : Z₂.map ρ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hρker, hZeq]
    exact le_sup_right
  have hH₂Z : H₂ ≤ stabSub Z := le_stabSub_of_le_fixV hfixZ₂
  let q₂ : H₂ →* MulAut (Vtil V₀ V hV ⧸ Z) := v3qb_quotHomOn Z hH₂Z
  have htheta₂_surj : Function.Surjective q₂.rangeRestrict :=
    MonoidHom.rangeRestrict_surjective q₂
  have htheta₂_repr : ∀ (h : H₂) (w : Vtil V₀ V hV),
      ρ ((h : MulAut (Vtil V₀ V hV)) w) =
        ((q₂.rangeRestrict h : MulAut (Vtil V₀ V hV ⧸ Z)) (ρ w)) :=
    fun h w => s168e3_quotHomOn_rangeRestrict_apply hH₂Z h w
  have hR₂0 : (FFModel.altDn n).Realizes H₂ (I₂ 0) Z₂ := by
    simpa only [AlternatingNatural] using hNatI₂ 0
  obtain ⟨π₂, hReal₂⟩ := hR₂0
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hD : (FFModel.altDn n).Faithful := FFC.altDn_faithful hn5
  have hIC₂ : I₂ 0 ⊓ Z ≤ Z₂ := by
    rw [← hUZ₂]
    exact inf_le_inf (hIU₂ 0) le_rfl
  have htheta₂_inj : Function.Injective q₂.rangeRestrict :=
    s168e3_quotHomOn_rangeRestrict_injective_of_realizes hH₂Z hD hReal₂ hIC₂
  have hNat₂ : ∀ j : Fin 3, AlternatingNatural q₂.range (S₂ j) ⊥ n := by
    intro j
    have hR : (FFModel.altDn n).Realizes H₂ (I₂ j) Z₂ := by
      simpa only [AlternatingNatural] using hNatI₂ j
    have hkerj : I₂ j ⊓ ρ.ker ≤ Z₂ := by
      rw [hρker]
      exact (inf_le_inf (hIU₂ j) le_rfl).trans_eq hUZ₂
    have hres := realizes_map_of_surjective_of_inf_ker_le (hR := hR) (ρ := ρ)
      (hρ := QuotientGroup.mk'_surjective Z) (hker := hkerj)
      (θ := q₂.rangeRestrict) (hθ := htheta₂_surj) (he := htheta₂_repr)
    rw [hZ₂map] at hres
    simpa only [S₂, AlternatingNatural] using hres
  have hSum₂' : SumOfNat (fun H U Z => AlternatingNatural H U Z n) H₂ U₂ Z₂ 3 := by
    have h := s16k_sumOfNat_map (hS := hsumU) (ρ := φ.toMonoidHom) hkerφ
      (N := fun H U Z => AlternatingNatural H U Z n)
      (N' := fun H U Z => AlternatingNatural H U Z n)
      (H := lBar V₀ V hV L) (H' := H₂) (U := U₁) (Z := Z₁) (k := 3)
      (fun I' _ hNI' => by
        have hR : (FFModel.altDn n).Realizes (lBar V₀ V hV L) I' Z₁ := by
          simpa only [AlternatingNatural] using hNI'
        have hres := s16k_realizes_map (hR := hR) (ρ := φ.toMonoidHom) hkerφ
          eφ.toMonoidHom eφ.surjective heφ
        simpa only [AlternatingNatural] using hres)
    rwa [← hU₂φ, ← hZ₂φ] at h
  have hSum₂ : SumOfNat (fun H U Z => AlternatingNatural H U Z n) q₂.range Q₂ ⊥ 3 := by
    have h := sumOfNat_map_of_inf_ker_le (hS := hSum₂') (ρ := ρ)
      (N := fun H U Z => AlternatingNatural H U Z n)
      (N' := fun H U Z => AlternatingNatural H U Z n)
      (H := H₂) (H' := q₂.range) (U := U₂) (Z := Z₂) (k := 3)
      hU₂ker
      (fun I' _ hI'U hNI' => by
        have hR : (FFModel.altDn n).Realizes H₂ I' Z₂ := by
          simpa only [AlternatingNatural] using hNI'
        have hker' : I' ⊓ ρ.ker ≤ Z₂ := by
          rw [hρker]
          exact (inf_le_inf hI'U le_rfl).trans_eq hUZ₂
        have hres := realizes_map_of_surjective_of_inf_ker_le (hR := hR) (ρ := ρ)
          (hρ := QuotientGroup.mk'_surjective Z) (hker := hker')
          (θ := q₂.rangeRestrict) (hθ := htheta₂_surj) (he := htheta₂_repr)
        simpa only [AlternatingNatural] using hres)
    rwa [hZ₂map, ← hQ₂eq] at h
  have hJoin₁ : (⨆ i : Fin 3, S₁ i) = Q₁ := by
    rw [hQ₁eq, ← hsupI, Subgroup.map_sup, Subgroup.map_iSup, hZ₁map, bot_sup_eq]
  have hJoin₂ : (⨆ i : Fin 3, S₂ i) = Q₂ := by
    rw [hQ₂eq, ← hsupI₂, Subgroup.map_sup, Subgroup.map_iSup, hZ₂map, bot_sup_eq]
  have hInd₁ : ∀ i : Fin 3,
      S₁ i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S₁ j) = ⊥ := by
    have h := s168e3_named_family_independence (ρ := ρ) hU₁ker hZ₁U hZ₁map hIU₁ hZI hind
    simpa only [S₁] using h
  have hInd₂ : ∀ i : Fin 3,
      S₂ i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S₂ j) = ⊥ := by
    have h := s168e3_named_family_independence (ρ := ρ) hU₂ker hZ₂U hZ₂map hIU₂ hZI₂ hind₂
    simpa only [S₂] using h
  have hS₂_comp : ∀ i : Fin 3,
      S₂ i = (I i).map (ρ.comp φ.toMonoidHom) := by
    intro i
    dsimp only [S₂, I₂]
    rw [Subgroup.map_map]
  refine ⟨ψ, H₂, A₁, A₂, φ, U₁, U₂, Z₁, Z₂, Z, Q₁, Q₂,
    hψ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂, hCne,
    hcent₁, hcent₂, hcentcard, hcent₁card, hcent₂card,
    hU₁eq, hU₂eq, hZ₁eq, hZ₂eq, hZeq, hU₂φ, hZ₂φ, hsup,
    hcross12, hcross21, hself₁, hself₂, hinfZ₁, hinfZ₂, hfixZ₁, hfixZ₂,
    hUZ₁, hUZ₂, hQ₁eq, hQ₂eq, hQsup, hQinf, ?_⟩
  refine ⟨Hq₁, theta₁, hleftZ, ?_, ?_⟩
  · exact ⟨hleftHqEq, hleftThetaVal, hleftSurj, hleftInj, hleftRepr⟩
  · refine ⟨I, hZI, hind, hsupI, hsumU, hN, I₂, (fun i => rfl),
      q₂.range, q₂.rangeRestrict, hfixZ₂, ?_, ?_⟩
    · exact ⟨rfl, (fun h => rfl), htheta₂_surj, htheta₂_inj, htheta₂_repr⟩
    · exact ⟨S₁, S₂, (fun i => rfl), (fun i => rfl), hS₂_comp,
        hNat₁, hNat₂, hSum₁, hSum₂, hJoin₁, hJoin₂, hInd₁, hInd₂⟩

private theorem s168e3_conj_theta_compat
    {W Q : Type} [CommGroup W] [Group Q]
    {H : Subgroup (MulAut W)}
    {Hq : Subgroup (MulAut Q)} {rho : W →* Q} {theta : H →* Hq}
    {t : MulAut W} {tau : MulAut Q} {delta : H →* H}
    (hrho : Function.Surjective rho)
    (htau : ∀ w : W, tau (rho w) = rho (t w))
    (htheta : ∀ (h : H) (w : W), rho ((h : MulAut W) w) = (theta h : MulAut Q) (rho w))
    (hdelta : ∀ h : H, (delta h : MulAut W) = t * (h : MulAut W) * t⁻¹) :
    ∀ h : H, (theta (delta h) : MulAut Q) = tau * (theta h : MulAut Q) * tau⁻¹ := by
  intro h
  refine MulEquiv.ext fun q => ?_
  obtain ⟨w, rfl⟩ := hrho q
  have htau_inv : tau⁻¹ (rho w) = rho (t⁻¹ w) := by
    have h := htau (t⁻¹ w)
    have h' : tau (rho (t⁻¹ w)) = rho w := by simpa using h
    calc tau⁻¹ (rho w) = tau⁻¹ (tau (rho (t⁻¹ w))) := by rw [h']
      _ = rho (t⁻¹ w) := by simp
  calc
    (theta (delta h) : MulAut Q) (rho w)
        = rho ((delta h : MulAut W) w) := (htheta (delta h) w).symm
    _ = rho ((t * (h : MulAut W) * t⁻¹) w) := by rw [hdelta h]
    _ = rho (t ((h : MulAut W) (t⁻¹ w))) := by simp [MulAut.mul_apply]
    _ = tau (rho ((h : MulAut W) (t⁻¹ w))) := (htau _).symm
    _ = tau ((theta h : MulAut Q) (rho (t⁻¹ w))) := by rw [htheta h (t⁻¹ w)]
    _ = tau ((theta h : MulAut Q) (tau⁻¹ (rho w))) := by rw [← htau_inv]
    _ = (tau * (theta h : MulAut Q) * tau⁻¹) (rho w) := by simp [MulAut.mul_apply]

private theorem s168e3_rk_altNatural_ge_four
    {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {S : Subgroup W} {n : ℕ}
    (hV : ∀ w : W, w ^ 2 = 1) (hn : n = 6 ∨ n = 7)
    (h : AlternatingNatural H S ⊥ n) : 4 ≤ rk ↥S := by
  have hn0 : 0 < n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨π, ψ, hπsurj, hψeq⟩ := s16c167_altNatural_equiv hn0 h
  have hcard : Nat.card ↥S = Nat.card (CFSG.RankThree.PartTwo.altHeart n) := by
    rw [Nat.card_congr ψ.toEquiv,
      Nat.card_congr (Multiplicative.toAdd (α := CFSG.RankThree.PartTwo.altHeart n))]
  have halt16 : 16 ≤ Nat.card (CFSG.RankThree.PartTwo.altHeart n) := by
    rcases hn with rfl | rfl
    · rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_altHeart_even
        (by norm_num) (by norm_num)]
      norm_num
    · rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_altHeart_odd (by norm_num)]
      norm_num
  have hcardS : Nat.card ↥S = 2 ^ rk ↥S := card_eq_two_pow hV S
  have hge : 2 ^ 4 ≤ 2 ^ rk ↥S := by
    rw [← hcardS, hcard]
    simpa using halt16
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hge

private def S168e3SelectedInvolution
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (H₂ : Subgroup (MulAut (Vtil V₀ V hV)))
    (U₁ U₂ Z₁ Z₂ Z : Subgroup (Vtil V₀ V hV))
    (Q₁ Q₂ : Subgroup (Vtil V₀ V hV ⧸ Z))
    (Hq₁ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z)))
    (theta₁ : (lBar V₀ V hV L) →* Hq₁)
    (Hq₂ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z)))
    (theta₂ : H₂ →* Hq₂) : Prop :=
  ∃ (t : MulAut (Vtil V₀ V hV)) (htZ : t ∈ stabSub Z)
    (τ : MulAut (Vtil V₀ V hV ⧸ Z)),
    t ∈ Mbar D.M V₀ V hV ∧ t ^ 2 = 1 ∧ t ≠ 1 ∧
    rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (Subgroup.zpowers t)) ≤ 3 ∧
    τ = quotHom Z ⟨t, htZ⟩ ∧
    (∀ w : Vtil V₀ V hV,
      τ (QuotientGroup.mk' Z w) = QuotientGroup.mk' Z (t w)) ∧
    τ ^ 2 = 1 ∧
    rkIdx (fixV (Subgroup.zpowers τ)) ≤ 3 ∧
    (lBar V₀ V hV L).map (MulAut.conj t).toMonoidHom = lBar V₀ V hV L ∧
    H₂.map (MulAut.conj t).toMonoidHom = H₂ ∧
    U₁.map t.toMonoidHom = U₁ ∧ U₂.map t.toMonoidHom = U₂ ∧
    Z₁.map t.toMonoidHom = Z₁ ∧ Z₂.map t.toMonoidHom = Z₂ ∧
    Q₁.map τ.toMonoidHom = Q₁ ∧ Q₂.map τ.toMonoidHom = Q₂ ∧
    ∃ (δ₁ : ↥(lBar V₀ V hV L) →* ↥(lBar V₀ V hV L))
      (δ₂ : ↥H₂ →* ↥H₂),
      (∀ h : ↥(lBar V₀ V hV L),
        (δ₁ h : MulAut (Vtil V₀ V hV)) =
          t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹) ∧
      (∀ h : ↥H₂,
        (δ₂ h : MulAut (Vtil V₀ V hV)) =
          t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹) ∧
      (∀ h : ↥(lBar V₀ V hV L),
        (theta₁ (δ₁ h) : MulAut (Vtil V₀ V hV ⧸ Z)) =
          τ * (theta₁ h : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹) ∧
      (∀ h : ↥H₂,
        (theta₂ (δ₂ h) : MulAut (Vtil V₀ V hV ⧸ Z)) =
          τ * (theta₂ h : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹) ∧
      τ ∈ Subgroup.normalizer (Hq₁ : Set (MulAut (Vtil V₀ V hV ⧸ Z))) ∧
      τ ∈ Subgroup.normalizer (Hq₂ : Set (MulAut (Vtil V₀ V hV ⧸ Z))) ∧
      ((∀ y ∈ Hq₁, τ * y = y * τ) →
        ∀ h ∈ lBar V₀ V hV L,
          t * (h : MulAut (Vtil V₀ V hV)) = (h : MulAut (Vtil V₀ V hV)) * t) ∧
      ((∀ y ∈ Hq₂, τ * y = y * τ) →
        ∀ h ∈ H₂, t * (h : MulAut (Vtil V₀ V hV)) =
          (h : MulAut (Vtil V₀ V hV)) * t) ∧
      τ ≠ 1

private theorem s168e3_selected_involution
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 2)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    {H₂ : Subgroup (MulAut (Vtil V₀ V hV))}
    {φ : MulAut (Vtil V₀ V hV)}
    (hφ : φ ∈ Mbar D.M V₀ V hV)
    {U₁ U₂ Z₁ Z₂ Z : Subgroup (Vtil V₀ V hV)}
    {Q₁ Q₂ : Subgroup (Vtil V₀ V hV ⧸ Z)}
    {Hq₁ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z))}
    {theta₁ : (lBar V₀ V hV L) →* Hq₁}
    {Hq₂ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z))}
    {theta₂ : H₂ →* Hq₂}
    {S₁ : Fin 3 → Subgroup (Vtil V₀ V hV ⧸ Z)}
    (hH₂eq : H₂ = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom)
    (hH₂ne : H₂ ≠ lBar V₀ V hV L)
    (hU₁eq : U₁ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
    (hU₂eq : U₂ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) H₂)
    (hZ₁eq : Z₁ = U₁ ⊓ fixV (lBar V₀ V hV L))
    (hZ₂eq : Z₂ = U₂ ⊓ fixV H₂)
    (hZeq : Z = Z₁ ⊔ Z₂)
    (hsup : U₁ ⊔ U₂ = ⊤)
    (hfixZ₁ : Z ≤ fixV (lBar V₀ V hV L))
    (hfixZ₂ : Z ≤ fixV H₂)
    (_hUZ₁ : U₁ ⊓ Z = Z₁) (_hUZ₂ : U₂ ⊓ Z = Z₂)
    (hQ₁eq : Q₁ = U₁.map (QuotientGroup.mk' Z))
    (hQ₂eq : Q₂ = U₂.map (QuotientGroup.mk' Z))
    (hQinf : Q₁ ⊓ Q₂ = ⊥)
    (hJoin₁ : (⨆ i : Fin 3, S₁ i) = Q₁)
    (hNat₁ : ∀ i : Fin 3, AlternatingNatural Hq₁ (S₁ i) ⊥ n)
    (htheta₁_surj : Function.Surjective theta₁)
    (htheta₁_inj : Function.Injective theta₁)
    (htheta₁_repr : ∀ (h : lBar V₀ V hV L) (w : Vtil V₀ V hV),
      QuotientGroup.mk' Z ((h : MulAut (Vtil V₀ V hV)) w) =
        ((theta₁ h : MulAut (Vtil V₀ V hV ⧸ Z)) (QuotientGroup.mk' Z w)))
    (htheta₂_surj : Function.Surjective theta₂)
    (htheta₂_inj : Function.Injective theta₂)
    (htheta₂_repr : ∀ (h : H₂) (w : Vtil V₀ V hV),
      QuotientGroup.mk' Z ((h : MulAut (Vtil V₀ V hV)) w) =
        ((theta₂ h : MulAut (Vtil V₀ V hV ⧸ Z)) (QuotientGroup.mk' Z w))) :
    S168e3SelectedInvolution (D := D) H₂ U₁ U₂ Z₁ Z₂ Z Q₁ Q₂ Hq₁ theta₁ Hq₂ theta₂ := by
  classical
  let H₁ : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let ρ : Vtil V₀ V hV →* (Vtil V₀ V hV ⧸ Z) := QuotientGroup.mk' Z
  obtain ⟨t, htA, ht2, ht1, htr, hconc⟩ := c.conc
  have h_two : Set.ncard
      {X : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ m ∈ Mbar D.M V₀ V hV, X = H₁.map (MulAut.conj m).toMonoidHom} = 2 := by
    simpa only [H₁, lBar, s15] using hs
  obtain ⟨-, huniv⟩ := c23a_two_conj h_two
  have hφmap : H₁.map (MulAut.conj φ).toMonoidHom ≠ H₁ := by
    intro h
    exact hH₂ne (by rw [hH₂eq, h])
  have hcases := (huniv φ hφ hφmap).2 t htA
  have hZmap : Z.map t.toMonoidHom = Z := by
    rcases hcases with ⟨hH₁t, hH₂t⟩ | ⟨hH₁t, hH₂t⟩
    · have hH₂t' : H₂.map (MulAut.conj t).toMonoidHom = H₂ := by
        rw [hH₂eq, hH₂t]
      have hconj₁ : conjBy t H₁ = H₁ := hH₁t
      have hconj₂ : conjBy t H₂ = H₂ := hH₂t'
      have hU₁t : U₁.map t.toMonoidHom = U₁ := by
        rw [hU₁eq, ← commSub_conjBy t (⊤ : Subgroup (Vtil V₀ V hV)) H₁,
          hconj₁, map_top_toMonoidHom]
      have hU₂t : U₂.map t.toMonoidHom = U₂ := by
        rw [hU₂eq, ← commSub_conjBy t (⊤ : Subgroup (Vtil V₀ V hV)) H₂,
          hconj₂, map_top_toMonoidHom]
      have hfix₁t : (fixV H₁).map t.toMonoidHom = fixV H₁ := by
        rw [← fixV_conjBy t H₁, hconj₁]
      have hfix₂t : (fixV H₂).map t.toMonoidHom = fixV H₂ := by
        rw [← fixV_conjBy t H₂, hconj₂]
      have hZ₁t : Z₁.map t.toMonoidHom = Z₁ := by
        rw [hZ₁eq, Subgroup.map_inf_eq U₁ (fixV H₁) t.toMonoidHom t.injective,
          hU₁t, hfix₁t]
      have hZ₂t : Z₂.map t.toMonoidHom = Z₂ := by
        rw [hZ₂eq, Subgroup.map_inf_eq U₂ (fixV H₂) t.toMonoidHom t.injective,
          hU₂t, hfix₂t]
      rw [hZeq, Subgroup.map_sup, hZ₁t, hZ₂t]
    · have hH₂t' : H₂.map (MulAut.conj t).toMonoidHom = H₁ := by
        rw [hH₂eq, hH₂t]
      have hconj₁ : conjBy t H₁ = H₂ := by
        rw [hH₂eq]
        exact hH₁t
      have hconj₂ : conjBy t H₂ = H₁ := hH₂t'
      have hU₁t : U₁.map t.toMonoidHom = U₂ := by
        rw [hU₁eq, hU₂eq, ← commSub_conjBy t (⊤ : Subgroup (Vtil V₀ V hV)) H₁,
          hconj₁, map_top_toMonoidHom]
      have hU₂t : U₂.map t.toMonoidHom = U₁ := by
        rw [hU₂eq, hU₁eq, ← commSub_conjBy t (⊤ : Subgroup (Vtil V₀ V hV)) H₂,
          hconj₂, map_top_toMonoidHom]
      have hfix₁t : (fixV H₁).map t.toMonoidHom = fixV H₂ := by
        rw [← fixV_conjBy t H₁, hconj₁]
      have hfix₂t : (fixV H₂).map t.toMonoidHom = fixV H₁ := by
        rw [← fixV_conjBy t H₂, hconj₂]
      have hZ₁t : Z₁.map t.toMonoidHom = Z₂ := by
        rw [hZ₁eq, hZ₂eq, Subgroup.map_inf_eq U₁ (fixV H₁) t.toMonoidHom t.injective,
          hU₁t, hfix₁t]
      have hZ₂t : Z₂.map t.toMonoidHom = Z₁ := by
        rw [hZ₂eq, hZ₁eq, Subgroup.map_inf_eq U₂ (fixV H₂) t.toMonoidHom t.injective,
          hU₂t, hfix₂t]
      rw [hZeq, Subgroup.map_sup, hZ₁t, hZ₂t, sup_comm]
  have htZ : t ∈ stabSub Z := CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq hZmap
  let τ : MulAut (Vtil V₀ V hV ⧸ Z) := quotHom Z ⟨t, htZ⟩
  have htau_repr : ∀ w : Vtil V₀ V hV,
      τ (QuotientGroup.mk' Z w) = QuotientGroup.mk' Z (t w) :=
    fun w => quotHom_mk Z ⟨t, htZ⟩ w
  have htau_sq : τ ^ 2 = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Z q
    rw [pow_two, MulAut.mul_apply, htau_repr, htau_repr]
    rw [← MulAut.mul_apply, show t * t = 1 by simpa [pow_two] using ht2, MulAut.one_apply]
    rfl
  have hrkτ : rkIdx (fixV (Subgroup.zpowers τ)) ≤ 3 := by
    have h1 := Inputs1719.Thm13_10.rkIdx_fixV_zpowers_quotHom_le (W := Vtil V₀ V hV)
      (C := Z) (t := t) htZ
    have h2 : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3 := by
      rw [CFSG.Quasithin.rkIdx_fixV_zpowers, CFSG.Quasithin.commV_eq_commSub]
      exact htr
    exact h1.trans h2
  have hnotswap : ¬ ((lBar V₀ V hV L).map (MulAut.conj t).toMonoidHom = H₂ ∧
      H₂.map (MulAut.conj t).toMonoidHom = lBar V₀ V hV L) := by
    rintro ⟨hH₁t, hH₂t⟩
    have hconj₁ : conjBy t H₁ = H₂ := hH₁t
    have hU₁t : U₁.map t.toMonoidHom = U₂ := by
      rw [hU₁eq, hU₂eq, ← commSub_conjBy t (⊤ : Subgroup (Vtil V₀ V hV)) H₁,
        hconj₁, map_top_toMonoidHom]
    have hcompτρ : τ.toMonoidHom.comp ρ = ρ.comp t.toMonoidHom :=
      MonoidHom.ext htau_repr
    have hQ₁t : Q₁.map τ.toMonoidHom = Q₂ := by
      rw [hQ₁eq, hQ₂eq, Subgroup.map_map, hcompτρ, ← Subgroup.map_map, hU₁t]
    have hinf : Q₁ ⊓ Q₁.map τ.toMonoidHom = ⊥ := by
      rw [hQ₁t, hQinf]
    have hrkQ : rk ↥Q₁ ≤ rkIdx (fixV (Subgroup.zpowers τ)) :=
      s16c167_rk_le_rkIdx_of_inf_map_eq_bot τ hinf
    have hrkQ3 : rk ↥Q₁ ≤ 3 := hrkQ.trans hrkτ
    have hSle : S₁ 0 ≤ Q₁ := by
      rw [← hJoin₁]
      exact le_iSup (fun i : Fin 3 => S₁ i) 0
    have hQ2 : ∀ q : Vtil V₀ V hV ⧸ Z, q ^ 2 = 1 := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H w =>
        simpa using congrArg (QuotientGroup.mk' Z)
          (s15_Infra_vtil_sq_eq_one V₀ V hV w)
    have hrkS : 4 ≤ rk ↥(S₁ 0) :=
      s168e3_rk_altNatural_ge_four (hV := hQ2) hn (hNat₁ 0)
    have hle : rk ↥(S₁ 0) ≤ rk ↥Q₁ := rk_mono hSle
    omega
  have hfixed : (lBar V₀ V hV L).map (MulAut.conj t).toMonoidHom = lBar V₀ V hV L ∧
      H₂.map (MulAut.conj t).toMonoidHom = H₂ := by
    rcases hcases with h | h
    · refine ⟨h.1, ?_⟩
      rw [hH₂eq, h.2]
    · have hswap : (lBar V₀ V hV L).map (MulAut.conj t).toMonoidHom = H₂ ∧
          H₂.map (MulAut.conj t).toMonoidHom = lBar V₀ V hV L := by
        constructor
        · rw [hH₂eq]
          exact h.1
        · rw [hH₂eq]
          exact h.2
      exact absurd hswap hnotswap
  have hconj₁ : conjBy t H₁ = H₁ := hfixed.1
  have hconj₂ : conjBy t H₂ = H₂ := hfixed.2
  have hU₁t : U₁.map t.toMonoidHom = U₁ := by
    rw [hU₁eq, ← commSub_conjBy t (⊤ : Subgroup (Vtil V₀ V hV)) H₁,
      hconj₁, map_top_toMonoidHom]
  have hU₂t : U₂.map t.toMonoidHom = U₂ := by
    rw [hU₂eq, ← commSub_conjBy t (⊤ : Subgroup (Vtil V₀ V hV)) H₂,
      hconj₂, map_top_toMonoidHom]
  have hfix₁t : (fixV H₁).map t.toMonoidHom = fixV H₁ := by
    rw [← fixV_conjBy t H₁, hconj₁]
  have hfix₂t : (fixV H₂).map t.toMonoidHom = fixV H₂ := by
    rw [← fixV_conjBy t H₂, hconj₂]
  have hZ₁t : Z₁.map t.toMonoidHom = Z₁ := by
    rw [hZ₁eq, Subgroup.map_inf_eq U₁ (fixV H₁) t.toMonoidHom t.injective,
      hU₁t, hfix₁t]
  have hZ₂t : Z₂.map t.toMonoidHom = Z₂ := by
    rw [hZ₂eq, Subgroup.map_inf_eq U₂ (fixV H₂) t.toMonoidHom t.injective,
      hU₂t, hfix₂t]
  have hcompτρ : τ.toMonoidHom.comp ρ = ρ.comp t.toMonoidHom :=
    MonoidHom.ext htau_repr
  have hQ₁t : Q₁.map τ.toMonoidHom = Q₁ := by
    rw [hQ₁eq, Subgroup.map_map, hcompτρ, ← Subgroup.map_map, hU₁t]
  have hQ₂t : Q₂.map τ.toMonoidHom = Q₂ := by
    rw [hQ₂eq, Subgroup.map_map, hcompτρ, ← Subgroup.map_map, hU₂t]
  have hH₁t' : H₁.map (↑(MulAut.conj t)) = H₁ := by
    change H₁.map (MulAut.conj t).toMonoidHom = H₁
    exact hfixed.1
  have hH₂t' : H₂.map (↑(MulAut.conj t)) = H₂ := by
    change H₂.map (MulAut.conj t).toMonoidHom = H₂
    exact hfixed.2
  let δ₁e : ↥H₁ ≃* ↥H₁ :=
    (MulEquiv.subgroupMap (MulAut.conj t) H₁).trans (MulEquiv.subgroupCongr hH₁t')
  let δ₂e : ↥H₂ ≃* ↥H₂ :=
    (MulEquiv.subgroupMap (MulAut.conj t) H₂).trans (MulEquiv.subgroupCongr hH₂t')
  let δ₁ : ↥H₁ →* ↥H₁ := δ₁e.toMonoidHom
  let δ₂ : ↥H₂ →* ↥H₂ := δ₂e.toMonoidHom
  have hδ₁e_ambient : ∀ h : ↥H₁,
      (δ₁e h : MulAut (Vtil V₀ V hV)) =
        t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹ := by
    intro h
    simp only [δ₁e, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  have hδ₂e_ambient : ∀ h : ↥H₂,
      (δ₂e h : MulAut (Vtil V₀ V hV)) =
        t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹ := by
    intro h
    simp only [δ₂e, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  have hδ₁_ambient : ∀ h : ↥H₁,
      (δ₁ h : MulAut (Vtil V₀ V hV)) =
        t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹ := fun h => hδ₁e_ambient h
  have hδ₂_ambient : ∀ h : ↥H₂,
      (δ₂ h : MulAut (Vtil V₀ V hV)) =
        t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹ := fun h => hδ₂e_ambient h
  have htheta₁_compat : ∀ h : ↥H₁,
      (theta₁ (δ₁ h) : MulAut (Vtil V₀ V hV ⧸ Z)) =
        τ * (theta₁ h : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹ :=
    s168e3_conj_theta_compat (H := H₁) (rho := ρ) (theta := theta₁) (delta := δ₁)
      (QuotientGroup.mk'_surjective Z) htau_repr htheta₁_repr hδ₁_ambient
  have htheta₂_compat : ∀ h : ↥H₂,
      (theta₂ (δ₂ h) : MulAut (Vtil V₀ V hV ⧸ Z)) =
        τ * (theta₂ h : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹ :=
    s168e3_conj_theta_compat (H := H₂) (rho := ρ) (theta := theta₂) (delta := δ₂)
      (QuotientGroup.mk'_surjective Z) htau_repr htheta₂_repr hδ₂_ambient
  have hτNorm₁ : τ ∈ Subgroup.normalizer (Hq₁ : Set (MulAut (Vtil V₀ V hV ⧸ Z))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨h, hh⟩ := htheta₁_surj ⟨y, hy⟩
      have hy' : (theta₁ h : MulAut (Vtil V₀ V hV ⧸ Z)) = y :=
        congrArg Subtype.val hh
      rw [← hy']
      change τ * (theta₁ h : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹ ∈ Hq₁
      rw [← htheta₁_compat h]
      exact (theta₁ (δ₁ h)).2
    · rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective]
  have hτNorm₂ : τ ∈ Subgroup.normalizer (Hq₂ : Set (MulAut (Vtil V₀ V hV ⧸ Z))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨h, hh⟩ := htheta₂_surj ⟨y, hy⟩
      have hy' : (theta₂ h : MulAut (Vtil V₀ V hV ⧸ Z)) = y :=
        congrArg Subtype.val hh
      rw [← hy']
      change τ * (theta₂ h : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹ ∈ Hq₂
      rw [← htheta₂_compat h]
      exact (theta₂ (δ₂ h)).2
    · rw [Subgroup.card_map_of_injective (MulAut.conj τ).injective]
  have hCentToOriginal₁ : (∀ y ∈ Hq₁, τ * y = y * τ) →
      ∀ h ∈ H₁, t * (h : MulAut (Vtil V₀ V hV)) =
        (h : MulAut (Vtil V₀ V hV)) * t := by
    intro hc h hh
    let h' : ↥H₁ := ⟨h, hh⟩
    have hθeq : theta₁ (δ₁ h') = theta₁ h' := by
      apply Subtype.ext
      have hcomp : (theta₁ (δ₁ h') : MulAut (Vtil V₀ V hV ⧸ Z)) =
          τ * (theta₁ h' : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹ := htheta₁_compat h'
      have hcy := hc (theta₁ h') (theta₁ h').2
      calc (theta₁ (δ₁ h') : MulAut (Vtil V₀ V hV ⧸ Z)) =
          τ * (theta₁ h' : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹ := hcomp
        _ = (theta₁ h' : MulAut (Vtil V₀ V hV ⧸ Z)) := by rw [hcy]; group
    have hδeq : δ₁ h' = h' := htheta₁_inj hθeq
    have hamb := hδ₁_ambient h'
    have hconj : t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹ =
        (h : MulAut (Vtil V₀ V hV)) := by
      rw [← hamb, hδeq]
    calc t * (h : MulAut (Vtil V₀ V hV)) =
        (t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹) * t := by group
      _ = (h : MulAut (Vtil V₀ V hV)) * t := by rw [hconj]
  have hCentToOriginal₂ : (∀ y ∈ Hq₂, τ * y = y * τ) →
      ∀ h ∈ H₂, t * (h : MulAut (Vtil V₀ V hV)) =
        (h : MulAut (Vtil V₀ V hV)) * t := by
    intro hc h hh
    let h' : ↥H₂ := ⟨h, hh⟩
    have hθeq : theta₂ (δ₂ h') = theta₂ h' := by
      apply Subtype.ext
      have hcomp : (theta₂ (δ₂ h') : MulAut (Vtil V₀ V hV ⧸ Z)) =
          τ * (theta₂ h' : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹ := htheta₂_compat h'
      have hcy := hc (theta₂ h') (theta₂ h').2
      calc (theta₂ (δ₂ h') : MulAut (Vtil V₀ V hV ⧸ Z)) =
          τ * (theta₂ h' : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹ := hcomp
        _ = (theta₂ h' : MulAut (Vtil V₀ V hV ⧸ Z)) := by rw [hcy]; group
    have hδeq : δ₂ h' = h' := htheta₂_inj hθeq
    have hamb := hδ₂_ambient h'
    have hconj : t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹ =
        (h : MulAut (Vtil V₀ V hV)) := by
      rw [← hamb, hδeq]
    calc t * (h : MulAut (Vtil V₀ V hV)) =
        (t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹) * t := by group
      _ = (h : MulAut (Vtil V₀ V hV)) * t := by rw [hconj]
  have hτne : τ ≠ 1 := by
    intro hτ1
    have hcent₁ : ∀ y ∈ Hq₁, τ * y = y * τ := by
      intro y hy
      simp [hτ1]
    have hcent₂ : ∀ y ∈ Hq₂, τ * y = y * τ := by
      intro y hy
      simp [hτ1]
    have hHorig₁ : ∀ h ∈ H₁, t * (h : MulAut (Vtil V₀ V hV)) =
        (h : MulAut (Vtil V₀ V hV)) * t := hCentToOriginal₁ hcent₁
    have hHorig₂ : ∀ h ∈ H₂, t * (h : MulAut (Vtil V₀ V hV)) =
        (h : MulAut (Vtil V₀ V hV)) * t := hCentToOriginal₂ hcent₂
    let H : Subgroup (MulAut (Vtil V₀ V hV)) := H₁ ⊔ H₂
    have hcommTop : commSub (⊤ : Subgroup (Vtil V₀ V hV)) H = ⊤ := by
      refine le_antisymm le_top ?_
      have hU₁le : U₁ ≤ commSub (⊤ : Subgroup (Vtil V₀ V hV)) H := by
        rw [hU₁eq]
        exact commSub_mono le_rfl le_sup_left
      have hU₂le : U₂ ≤ commSub (⊤ : Subgroup (Vtil V₀ V hV)) H := by
        rw [hU₂eq]
        exact commSub_mono le_rfl le_sup_right
      calc (⊤ : Subgroup (Vtil V₀ V hV)) = U₁ ⊔ U₂ := hsup.symm
        _ ≤ commSub (⊤ : Subgroup (Vtil V₀ V hV)) H := sup_le hU₁le hU₂le
    have hfixH : Z ≤ fixV H := by
      change Z ≤ fixV (H₁ ⊔ H₂)
      rw [fixV_sup]
      exact le_inf hfixZ₁ hfixZ₂
    have hZmem : ∀ w : Vtil V₀ V hV, t w * w⁻¹ ∈ Z := by
      intro w
      have h1 : QuotientGroup.mk' Z (t w) = QuotientGroup.mk' Z w := by
        have h := htau_repr w
        rw [hτ1] at h
        simpa using h.symm
      exact (mk_eq_mk_iff (t w) w).mp h1
    have hHcent : H ≤ Subgroup.centralizer ({t} : Set (MulAut (Vtil V₀ V hV))) := by
      change H₁ ⊔ H₂ ≤ Subgroup.centralizer ({t} : Set (MulAut (Vtil V₀ V hV)))
      refine sup_le ?_ ?_
      · intro h hh
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact hHorig₁ h hh
      · intro h hh
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact hHorig₂ h hh
    have hac : ∀ h ∈ H, t * h = h * t := by
      intro h hh
      exact Subgroup.mem_centralizer_iff.mp (hHcent hh) t (Set.mem_singleton t)
    have hfix : ∀ w : Vtil V₀ V hV, t w * w⁻¹ ∈ fixV H :=
      fun w => hfixH (hZmem w)
    have ht1' : t = 1 := s16g_eq_one_of_commSub hcommTop hac hfix
    exact ht1 ht1'
  unfold S168e3SelectedInvolution
  refine ⟨t, htZ, τ, htA, ht2, ht1, htr, rfl, htau_repr, htau_sq, hrkτ,
    hfixed.1, hfixed.2, hU₁t, hU₂t, hZ₁t, hZ₂t, hQ₁t, hQ₂t, ?_⟩
  exact ⟨δ₁, δ₂, hδ₁_ambient, hδ₂_ambient, htheta₁_compat, htheta₂_compat,
    hτNorm₁, hτNorm₂, hCentToOriginal₁, hCentToOriginal₂, hτne⟩

private theorem s168e3_concrete_two_block_selected_involution
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 2)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    ∃ (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
      (H₂ : Subgroup (MulAut (Vtil V₀ V hV)))
      (A₁ : S168e3ActualCover ψ (lBar V₀ V hV L))
      (A₂ : S168e3ActualCover ψ H₂)
      (φ : MulAut (Vtil V₀ V hV))
      (U₁ U₂ Z₁ Z₂ Z : Subgroup (Vtil V₀ V hV))
      (Q₁ Q₂ : Subgroup (Vtil V₀ V hV ⧸ Z)),
      (∀ m : D.M, ψ (QuotientGroup.mk m) =
        actTil V₀ V hV ⟨m, le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
          c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ m.2⟩) ∧
      φ ∈ Mbar D.M V₀ V hV ∧
      H₂ = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∧
      H₂ ≠ lBar V₀ V hV L ∧ IsComponentOf H₂ (Mbar D.M V₀ V hV) ∧
      UC22.IsAlt ↥H₂ n ∧
      A₁.C ≠ A₂.C ∧
      (Subgroup.center A₁.C).map A₁.C.subtype = A₁.C ⊓ A₂.C ∧
      (Subgroup.center A₂.C).map A₂.C.subtype = A₁.C ⊓ A₂.C ∧
      Nat.card ↥(A₁.C ⊓ A₂.C) = 3 ∧
      Nat.card (Subgroup.center A₁.C) = 3 ∧
      Nat.card (Subgroup.center A₂.C) = 3 ∧
      U₁ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∧
      U₂ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) H₂ ∧
      Z₁ = U₁ ⊓ fixV (lBar V₀ V hV L) ∧
      Z₂ = U₂ ⊓ fixV H₂ ∧
      Z = Z₁ ⊔ Z₂ ∧ U₂ = U₁.map φ.toMonoidHom ∧
      Z₂ = Z₁.map φ.toMonoidHom ∧ U₁ ⊔ U₂ = ⊤ ∧
      commSub U₁ H₂ = ⊥ ∧ commSub U₂ (lBar V₀ V hV L) = ⊥ ∧
      commSub U₁ (lBar V₀ V hV L) = U₁ ∧ commSub U₂ H₂ = U₂ ∧
      U₁ ⊓ U₂ ≤ Z₁ ∧ U₁ ⊓ U₂ ≤ Z₂ ∧
      Z ≤ fixV (lBar V₀ V hV L) ∧ Z ≤ fixV H₂ ∧
      U₁ ⊓ Z = Z₁ ∧ U₂ ⊓ Z = Z₂ ∧
      Q₁ = U₁.map (QuotientGroup.mk' Z) ∧ Q₂ = U₂.map (QuotientGroup.mk' Z) ∧
      Q₁ ⊔ Q₂ = ⊤ ∧ Q₁ ⊓ Q₂ = ⊥ ∧
      ∃ (Hq₁ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z)))
        (theta₁ : (lBar V₀ V hV L) →* Hq₁)
        (hZ₁ : Z ≤ fixV (lBar V₀ V hV L)),
        S168e3QuotAction (lBar V₀ V hV L) Z hZ₁ Hq₁ theta₁ ∧
      ∃ (I : Fin 3 → Subgroup (Vtil V₀ V hV))
        (_hZI : ∀ i, Z₁ ≤ I i)
        (_hind : ∀ i, I i ⊓ (Z₁ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ Z₁)
        (_hsupI : Z₁ ⊔ ⨆ i : Fin 3, I i = U₁)
        (_hsumU : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
          (lBar V₀ V hV L) U₁ Z₁ 3)
        (_hN : ∀ i : Fin 3, AlternatingNatural (lBar V₀ V hV L) (I i) Z₁ n)
        (I₂ : Fin 3 → Subgroup (Vtil V₀ V hV))
        (_hI₂ : ∀ i, I₂ i = (I i).map φ.toMonoidHom)
        (Hq₂ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z)))
        (theta₂ : H₂ →* Hq₂)
        (hZ₂ : Z ≤ fixV H₂),
        S168e3QuotAction H₂ Z hZ₂ Hq₂ theta₂ ∧
      ∃ (S₁ S₂ : Fin 3 → Subgroup (Vtil V₀ V hV ⧸ Z)),
        (∀ i, S₁ i = (I i).map (QuotientGroup.mk' Z)) ∧
        (∀ i, S₂ i = (I₂ i).map (QuotientGroup.mk' Z)) ∧
        (∀ i, S₂ i = (I i).map ((QuotientGroup.mk' Z).comp φ.toMonoidHom)) ∧
        (∀ i, AlternatingNatural Hq₁ (S₁ i) ⊥ n) ∧
        (∀ i, AlternatingNatural Hq₂ (S₂ i) ⊥ n) ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z n) Hq₁ Q₁ ⊥ 3 ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z n) Hq₂ Q₂ ⊥ 3 ∧
        (⨆ i : Fin 3, S₁ i) = Q₁ ∧
        (⨆ i : Fin 3, S₂ i) = Q₂ ∧
        (∀ i : Fin 3,
          S₁ i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S₁ j) = ⊥) ∧
        (∀ i : Fin 3,
          S₂ i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S₂ j) = ⊥) ∧
        S168e3SelectedInvolution (D := D) H₂ U₁ U₂ Z₁ Z₂ Z Q₁ Q₂ Hq₁ theta₁ Hq₂ theta₂:= by
  obtain ⟨ψ, H₂, A₁, A₂, φ, U₁, U₂, Z₁, Z₂, Z, Q₁, Q₂,
    hψ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂, hCne,
    hcent₁, hcent₂, hcentcard, hcent₁card, hcent₂card,
    hU₁eq, hU₂eq, hZ₁eq, hZ₂eq, hZeq, hU₂φ, hZ₂φ, hsup,
    hcross12, hcross21, hself₁, hself₂, hinfZ₁, hinfZ₂, hfixZ₁, hfixZ₂,
    hUZ₁, hUZ₂, hQ₁eq, hQ₂eq, hQsup, hQinf, hblock₁⟩ :=
    s168e3_concrete_two_block_three_family c hcomp hs hn hA hsum
  obtain ⟨Hq₁, theta₁, hZ₁, hq₁act, hblock₂⟩ := hblock₁
  obtain ⟨I, _hZI, _hind, _hsupI, _hsumU, _hN, I₂, _hI₂, Hq₂, theta₂, hZ₂,
    hq₂act, hblock₃⟩ := hblock₂
  obtain ⟨S₁, S₂, hS₁, hS₂, hS₂comp, hNat₁, hNat₂, hSum₁, hSum₂, hJoin₁, hJoin₂,
    hInd₁, hInd₂⟩ := hblock₃
  have hq₁act' := hq₁act
  have hq₂act' := hq₂act
  obtain ⟨hHq₁eq, htheta₁_val, htheta₁_surj, htheta₁_inj, htheta₁_repr⟩ := hq₁act
  obtain ⟨hHq₂eq, htheta₂_val, htheta₂_surj, htheta₂_inj, htheta₂_repr⟩ := hq₂act
  have hselected : S168e3SelectedInvolution (D := D) H₂ U₁ U₂ Z₁ Z₂ Z Q₁ Q₂
      Hq₁ theta₁ Hq₂ theta₂ :=
    s168e3_selected_involution c hs hn hφ hH₂eq hH₂ne hU₁eq hU₂eq hZ₁eq hZ₂eq hZeq hsup
      hfixZ₁ hfixZ₂ hUZ₁ hUZ₂ hQ₁eq hQ₂eq hQinf hJoin₁ hNat₁
      htheta₁_surj htheta₁_inj htheta₁_repr htheta₂_surj htheta₂_inj htheta₂_repr
  refine ⟨ψ, H₂, A₁, A₂, φ, U₁, U₂, Z₁, Z₂, Z, Q₁, Q₂,
    hψ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂, hCne,
    hcent₁, hcent₂, hcentcard, hcent₁card, hcent₂card,
    hU₁eq, hU₂eq, hZ₁eq, hZ₂eq, hZeq, hU₂φ, hZ₂φ, hsup,
    hcross12, hcross21, hself₁, hself₂, hinfZ₁, hinfZ₂, hfixZ₁, hfixZ₂,
    hUZ₁, hUZ₂, hQ₁eq, hQ₂eq, hQsup, hQinf, ?_⟩
  refine ⟨Hq₁, theta₁, hZ₁, hq₁act', ?_⟩
  refine ⟨I, _hZI, _hind, _hsupI, _hsumU, _hN, I₂, _hI₂, Hq₂, theta₂, hZ₂,
    hq₂act', ?_⟩
  exact ⟨S₁, S₂, hS₁, hS₂, hS₂comp, hNat₁, hNat₂, hSum₁, hSum₂, hJoin₁, hJoin₂,
    hInd₁, hInd₂, hselected⟩

private theorem s168e3_altNatural_stable_of_small_rank
    {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {S : Subgroup W} {n : ℕ}
    (hW : ∀ w : W, w ^ 2 = 1) (hn : n = 6 ∨ n = 7)
    (hNat : AlternatingNatural H S ⊥ n) (tau : MulAut W)
    (htauN : tau ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hrank : rkIdx (fixV (Subgroup.zpowers tau)) ≤ 3) :
    S.map tau.toMonoidHom = S := by
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hirr := s16c167_mem_irrSet_alt hn5 hNat
  have hfix : S ⊓ fixV H = ⊥ := s16c167_cfg2_fix_alt hn5 hNat
  obtain ⟨-, hlt0, hstab, -, hminimal0⟩ := hirr
  have hlt : (⊥ : Subgroup W) < S := by
    rw [← hfix]
    exact hlt0
  have hminimal : ∀ J : Subgroup W, StableUnder H J → J ≤ S → J = ⊥ ∨ J = S := by
    intro J hJ hJS
    simpa only [hfix] using hminimal0 J hJ (by rw [hfix]; exact bot_le) hJS
  have hSne : S ≠ ⊥ := hlt.ne'
  have hmin : S ∈ CFSG.LocalAnalysis.WeakClosure81.minStab H S :=
    ⟨le_rfl, hstab, hSne, hminimal⟩
  have hrk : 4 ≤ rk ↥S := s168e3_rk_altNatural_ge_four hW hn hNat
  have hτB : ∀ b ∈ H, tau⁻¹ * b * tau ∈ H := by
    intro b hb
    have hτinv : tau⁻¹ ∈ Subgroup.normalizer (H : Set (MulAut W)) :=
      (Subgroup.normalizer (H : Set (MulAut W))).inv_mem htauN
    simpa [inv_inv] using (Subgroup.mem_normalizer_iff.mp hτinv b).1 hb
  have hτ : tau ∈ stabSub S :=
    CFSG.LocalAnalysis.WeakClosure81.mem_stabSub_of_rkIdx_lt hτB hmin (by omega)
  exact CFSG.Quasithin.StabLat.mem_stabSub_iff_map.mp hτ

private theorem s168e3_altNatural_uniform_of_fixed_member
    {Q : Type} [CommGroup Q] [Finite Q]
    {ι : Type*} {H : Subgroup (MulAut Q)}
    (S : ι → Subgroup Q) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (τ : MulAut Q)
    (hτN : τ ∈ Subgroup.normalizer (H : Set (MulAut Q)))
    (hNat : ∀ i : ι, AlternatingNatural H (S i) ⊥ n)
    (hτS : ∀ i : ι, (S i).map τ.toMonoidHom = S i)
    (j : ι) (hfix : ∀ w ∈ S j, τ w = w) :
    (∀ g ∈ H, τ * g = g * τ) ∧
      ∀ i : ι, ∀ w ∈ S i, τ w = w := by
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨π, hReal⟩ := hNat j
  have hHS : ∀ g ∈ H, ∀ w ∈ S j, g w ∈ S j :=
    fun g hg w hw => hReal.2.2.2.1 ⟨g, hg⟩ w hw
  have hfaith : ∀ g ∈ H, (∀ w ∈ S j, g w = w) → g = 1 := by
    intro g hg htriv
    apply CFSG.Quasithin.G64.RealizesVia.eq_one_of_trivial
      (FFC.altDn_faithful hn5) hReal hg
    intro w hw
    rw [htriv w hw, mul_inv_cancel]
    exact (⊥ : Subgroup Q).one_mem
  have hτj : τ ∈ stabSub (S j) :=
    CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq (hτS j)
  have hτj' : τ⁻¹ ∈ stabSub (S j) := (stabSub (S j)).inv_mem hτj
  have hcomm : ∀ g ∈ H, τ * g = g * τ :=
    CFSG.Quasithin.SmithD321.comm_of_trivial_on hτN hHS hfaith hfix
      (fun w hw => (mem_stabSub.mp hτj' w).mpr hw)
  refine ⟨hcomm, fun i w hw => ?_⟩
  let e : ↥(S i) ≃* ↥(S i) :=
    (MulEquiv.subgroupMap τ (S i)).trans (MulEquiv.subgroupCongr (hτS i))
  have heval : ∀ x : ↥(S i), ((e x : ↥(S i)) : Q) = τ (x : Q) := fun x => rfl
  have he : e = MulEquiv.refl _ :=
    s16c167_endUnits_alt hn5 (hNat i) e (by
      intro g x y hxy
      show (g : MulAut Q) ((e x : ↥(S i)) : Q) = ((e y : ↥(S i)) : Q)
      rw [heval x, heval y]
      have h1 := congrArg (fun f : MulAut Q => f (x : Q))
        (hcomm (g : MulAut Q) g.2).symm
      simp only [MulAut.mul_apply] at h1
      calc (g : MulAut Q) (τ (x : Q)) = τ ((g : MulAut Q) (x : Q)) := h1
        _ = τ (y : Q) := by rw [show (g : MulAut Q) (x : Q) = (y : Q) from hxy])
  have h2 : e ⟨w, hw⟩ = ⟨w, hw⟩ := by
    have := congrArg (fun ψ : ↥(S i) ≃* ↥(S i) => ψ ⟨w, hw⟩) he
    simpa using this
  have h3 := congrArg (fun y : ↥(S i) => (y : Q)) h2
  rw [heval ⟨w, hw⟩] at h3
  simpa using h3

private def S168e3NamedActivity
    {W Q : Type} [CommGroup W] [CommGroup Q] [Finite Q]
    (H₁ H₂ : Subgroup (MulAut W)) (Hq₁ Hq₂ : Subgroup (MulAut Q))
    (Q₁ Q₂ : Subgroup Q) (S₁ S₂ : Fin 3 → Subgroup Q)
    (t : MulAut W) (τ : MulAut Q) : Prop :=
  let F := fixV (Subgroup.zpowers τ)
  (∀ i : Fin 3, (S₁ i).map τ.toMonoidHom = S₁ i) ∧
  (∀ i : Fin 3, (S₂ i).map τ.toMonoidHom = S₂ i) ∧
  rkIdx F = 3 ∧
  (((¬ Q₁ ≤ F) ∧ E3.mQuot Q₁ (Q₁ ⊓ F) = 3 ∧
      (∀ i : Fin 3, (¬ S₁ i ≤ F) ∧ E3.mQuot (S₁ i) (S₁ i ⊓ F) = 1) ∧
      Q₂ ≤ F ∧ E3.mQuot Q₂ (Q₂ ⊓ F) = 0 ∧
      (∀ y ∈ Hq₂, τ * y = y * τ) ∧ (∀ h ∈ H₂, t * h = h * t)) ∨
   ((¬ Q₂ ≤ F) ∧ E3.mQuot Q₂ (Q₂ ⊓ F) = 3 ∧
      (∀ i : Fin 3, (¬ S₂ i ≤ F) ∧ E3.mQuot (S₂ i) (S₂ i ⊓ F) = 1) ∧
      Q₁ ≤ F ∧ E3.mQuot Q₁ (Q₁ ⊓ F) = 0 ∧
      (∀ y ∈ Hq₁, τ * y = y * τ) ∧ (∀ h ∈ H₁, t * h = h * t)))

private theorem s168e3_activity_of_witness
    {W Q : Type} [CommGroup W] [CommGroup Q] [Finite Q]
    {H₁ H₂ : Subgroup (MulAut W)} {Hq₁ Hq₂ : Subgroup (MulAut Q)}
    {Q₁ Q₂ : Subgroup Q} (S₁ S₂ : Fin 3 → Subgroup Q)
    (t : MulAut W) (τ : MulAut Q) (hQ : ∀ q : Q, q ^ 2 = 1)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hNat₁ : ∀ i, AlternatingNatural Hq₁ (S₁ i) ⊥ n)
    (hNat₂ : ∀ i, AlternatingNatural Hq₂ (S₂ i) ⊥ n)
    (hN₁ : τ ∈ Subgroup.normalizer (Hq₁ : Set (MulAut Q)))
    (hN₂ : τ ∈ Subgroup.normalizer (Hq₂ : Set (MulAut Q)))
    (hQinf : Q₁ ⊓ Q₂ = ⊥) (hQsup : Q₁ ⊔ Q₂ = ⊤)
    (hQ₁ : Q₁.map τ.toMonoidHom = Q₁) (hQ₂ : Q₂.map τ.toMonoidHom = Q₂)
    (hJoin₁ : (⨆ i : Fin 3, S₁ i) = Q₁) (hJoin₂ : (⨆ i : Fin 3, S₂ i) = Q₂)
    (hInd₁ : ∀ i : Fin 3, S₁ i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S₁ j) = ⊥)
    (hInd₂ : ∀ i : Fin 3, S₂ i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S₂ j) = ⊥)
    (hRank : rkIdx (fixV (Subgroup.zpowers τ)) ≤ 3) (hτne : τ ≠ 1)
    (hReflect₁ : (∀ y ∈ Hq₁, τ * y = y * τ) → ∀ h ∈ H₁, t * h = h * t)
    (hReflect₂ : (∀ y ∈ Hq₂, τ * y = y * τ) → ∀ h ∈ H₂, t * h = h * t) :
    S168e3NamedActivity H₁ H₂ Hq₁ Hq₂ Q₁ Q₂ S₁ S₂ t τ := by
  have hS₁ : ∀ i : Fin 3, (S₁ i).map τ.toMonoidHom = S₁ i :=
    fun i => s168e3_altNatural_stable_of_small_rank hQ hn (hNat₁ i) τ hN₁ hRank
  have hS₂ : ∀ i : Fin 3, (S₂ i).map τ.toMonoidHom = S₂ i :=
    fun i => s168e3_altNatural_stable_of_small_rank hQ hn (hNat₂ i) τ hN₂ hRank
  let F := fixV (Subgroup.zpowers τ)
  have hUniform₁ : ∀ i : Fin 3, S₁ i ≤ F → Q₁ ≤ F := by
    intro i hi
    have hfixi : ∀ w ∈ S₁ i, τ w = w :=
      fun w hw => mem_fixV_zpowers_iff_apply.mp (hi hw)
    have huni := s168e3_altNatural_uniform_of_fixed_member S₁ hn τ hN₁ hNat₁ hS₁ i hfixi
    rw [← hJoin₁]
    exact iSup_le fun j w hw => mem_fixV_zpowers_iff_apply.mpr (huni.2 j w hw)
  have hUniform₂ : ∀ i : Fin 3, S₂ i ≤ F → Q₂ ≤ F := by
    intro i hi
    have hfixi : ∀ w ∈ S₂ i, τ w = w :=
      fun w hw => mem_fixV_zpowers_iff_apply.mp (hi hw)
    have huni := s168e3_altNatural_uniform_of_fixed_member S₂ hn τ hN₂ hNat₂ hS₂ i hfixi
    rw [← hJoin₂]
    exact iSup_le fun j w hw => mem_fixV_zpowers_iff_apply.mpr (huni.2 j w hw)
  have hrk := s168e3_two_block_three_rank_allocation hQ τ hτne S₁ S₂ hQinf hQsup hQ₁ hQ₂
    hJoin₁ hJoin₂ hInd₁ hInd₂ hS₁ hS₂ hUniform₁ hUniform₂ hRank
  dsimp only at hrk
  obtain ⟨hRankEq, hLeftOrRight⟩ := hrk
  rcases hLeftOrRight with hL | hR
  · obtain ⟨hQ1ne, hmQ1, hS1act, hQ2le, hmQ2⟩ := hL
    have hS20le : S₂ 0 ≤ Q₂ := by
      rw [← hJoin₂]
      exact le_iSup (fun i : Fin 3 => S₂ i) 0
    have hfix20 : ∀ w ∈ S₂ 0, τ w = w :=
      fun w hw => mem_fixV_zpowers_iff_apply.mp (hQ2le (hS20le hw))
    have huni₂ := s168e3_altNatural_uniform_of_fixed_member S₂ hn τ hN₂ hNat₂ hS₂ 0 hfix20
    have hComm₂ : ∀ y ∈ Hq₂, τ * y = y * τ := huni₂.1
    have hCommOrig₂ : ∀ h ∈ H₂, t * h = h * t := hReflect₂ hComm₂
    exact ⟨hS₁, hS₂, hRankEq,
      Or.inl ⟨hQ1ne, hmQ1, hS1act, hQ2le, hmQ2, hComm₂, hCommOrig₂⟩⟩
  · obtain ⟨hQ2ne, hmQ2, hS2act, hQ1le, hmQ1⟩ := hR
    have hS10le : S₁ 0 ≤ Q₁ := by
      rw [← hJoin₁]
      exact le_iSup (fun i : Fin 3 => S₁ i) 0
    have hfix10 : ∀ w ∈ S₁ 0, τ w = w :=
      fun w hw => mem_fixV_zpowers_iff_apply.mp (hQ1le (hS10le hw))
    have huni₁ := s168e3_altNatural_uniform_of_fixed_member S₁ hn τ hN₁ hNat₁ hS₁ 0 hfix10
    have hComm₁ : ∀ y ∈ Hq₁, τ * y = y * τ := huni₁.1
    have hCommOrig₁ : ∀ h ∈ H₁, t * h = h * t := hReflect₁ hComm₁
    exact ⟨hS₁, hS₂, hRankEq,
      Or.inr ⟨hQ2ne, hmQ2, hS2act, hQ1le, hmQ1, hComm₁, hCommOrig₁⟩⟩

private def S168e3SelectedActivity
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (H₂ : Subgroup (MulAut (Vtil V₀ V hV)))
    (U₁ U₂ Z₁ Z₂ Z : Subgroup (Vtil V₀ V hV))
    (Q₁ Q₂ : Subgroup (Vtil V₀ V hV ⧸ Z))
    (Hq₁ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z)))
    (theta₁ : (lBar V₀ V hV L) →* Hq₁)
    (Hq₂ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z)))
    (theta₂ : H₂ →* Hq₂)
    (S₁ S₂ : Fin 3 → Subgroup (Vtil V₀ V hV ⧸ Z)) : Prop :=
  ∃ (t : MulAut (Vtil V₀ V hV)) (htZ : t ∈ stabSub Z)
    (τ : MulAut (Vtil V₀ V hV ⧸ Z)),
    t ∈ Mbar D.M V₀ V hV ∧ t ^ 2 = 1 ∧ t ≠ 1 ∧
    rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (Subgroup.zpowers t)) ≤ 3 ∧
    τ = quotHom Z ⟨t, htZ⟩ ∧
    (∀ w : Vtil V₀ V hV,
      τ (QuotientGroup.mk' Z w) = QuotientGroup.mk' Z (t w)) ∧
    τ ^ 2 = 1 ∧
    rkIdx (fixV (Subgroup.zpowers τ)) ≤ 3 ∧
    (lBar V₀ V hV L).map (MulAut.conj t).toMonoidHom = lBar V₀ V hV L ∧
    H₂.map (MulAut.conj t).toMonoidHom = H₂ ∧
    U₁.map t.toMonoidHom = U₁ ∧ U₂.map t.toMonoidHom = U₂ ∧
    Z₁.map t.toMonoidHom = Z₁ ∧ Z₂.map t.toMonoidHom = Z₂ ∧
    Q₁.map τ.toMonoidHom = Q₁ ∧ Q₂.map τ.toMonoidHom = Q₂ ∧
    ∃ (δ₁ : ↥(lBar V₀ V hV L) →* ↥(lBar V₀ V hV L))
      (δ₂ : ↥H₂ →* ↥H₂),
      (∀ h : ↥(lBar V₀ V hV L),
        (δ₁ h : MulAut (Vtil V₀ V hV)) =
          t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹) ∧
      (∀ h : ↥H₂,
        (δ₂ h : MulAut (Vtil V₀ V hV)) =
          t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹) ∧
      (∀ h : ↥(lBar V₀ V hV L),
        (theta₁ (δ₁ h) : MulAut (Vtil V₀ V hV ⧸ Z)) =
          τ * (theta₁ h : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹) ∧
      (∀ h : ↥H₂,
        (theta₂ (δ₂ h) : MulAut (Vtil V₀ V hV ⧸ Z)) =
          τ * (theta₂ h : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹) ∧
      τ ∈ Subgroup.normalizer (Hq₁ : Set (MulAut (Vtil V₀ V hV ⧸ Z))) ∧
      τ ∈ Subgroup.normalizer (Hq₂ : Set (MulAut (Vtil V₀ V hV ⧸ Z))) ∧
      ((∀ y ∈ Hq₁, τ * y = y * τ) →
        ∀ h ∈ lBar V₀ V hV L,
          t * (h : MulAut (Vtil V₀ V hV)) = (h : MulAut (Vtil V₀ V hV)) * t) ∧
      ((∀ y ∈ Hq₂, τ * y = y * τ) →
        ∀ h ∈ H₂, t * (h : MulAut (Vtil V₀ V hV)) =
          (h : MulAut (Vtil V₀ V hV)) * t) ∧
      τ ≠ 1 ∧
      S168e3NamedActivity (lBar V₀ V hV L) H₂ Hq₁ Hq₂ Q₁ Q₂ S₁ S₂ t τ

private theorem s168e3_concrete_two_block_selected_activity
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 2)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    ∃ (ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV))
      (H₂ : Subgroup (MulAut (Vtil V₀ V hV)))
      (A₁ : S168e3ActualCover ψ (lBar V₀ V hV L))
      (A₂ : S168e3ActualCover ψ H₂)
      (φ : MulAut (Vtil V₀ V hV))
      (U₁ U₂ Z₁ Z₂ Z : Subgroup (Vtil V₀ V hV))
      (Q₁ Q₂ : Subgroup (Vtil V₀ V hV ⧸ Z)),
      (∀ m : D.M, ψ (QuotientGroup.mk m) =
        actTil V₀ V hV ⟨m, le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
          c.setting.hyp16.hyp125.pairFacts.le_normalizer₀ m.2⟩) ∧
      φ ∈ Mbar D.M V₀ V hV ∧
      H₂ = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∧
      H₂ ≠ lBar V₀ V hV L ∧ IsComponentOf H₂ (Mbar D.M V₀ V hV) ∧
      UC22.IsAlt ↥H₂ n ∧
      A₁.C ≠ A₂.C ∧
      (Subgroup.center A₁.C).map A₁.C.subtype = A₁.C ⊓ A₂.C ∧
      (Subgroup.center A₂.C).map A₂.C.subtype = A₁.C ⊓ A₂.C ∧
      Nat.card ↥(A₁.C ⊓ A₂.C) = 3 ∧
      Nat.card (Subgroup.center A₁.C) = 3 ∧
      Nat.card (Subgroup.center A₂.C) = 3 ∧
      U₁ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∧
      U₂ = commSub (⊤ : Subgroup (Vtil V₀ V hV)) H₂ ∧
      Z₁ = U₁ ⊓ fixV (lBar V₀ V hV L) ∧
      Z₂ = U₂ ⊓ fixV H₂ ∧
      Z = Z₁ ⊔ Z₂ ∧ U₂ = U₁.map φ.toMonoidHom ∧
      Z₂ = Z₁.map φ.toMonoidHom ∧ U₁ ⊔ U₂ = ⊤ ∧
      commSub U₁ H₂ = ⊥ ∧ commSub U₂ (lBar V₀ V hV L) = ⊥ ∧
      commSub U₁ (lBar V₀ V hV L) = U₁ ∧ commSub U₂ H₂ = U₂ ∧
      U₁ ⊓ U₂ ≤ Z₁ ∧ U₁ ⊓ U₂ ≤ Z₂ ∧
      Z ≤ fixV (lBar V₀ V hV L) ∧ Z ≤ fixV H₂ ∧
      U₁ ⊓ Z = Z₁ ∧ U₂ ⊓ Z = Z₂ ∧
      Q₁ = U₁.map (QuotientGroup.mk' Z) ∧ Q₂ = U₂.map (QuotientGroup.mk' Z) ∧
      Q₁ ⊔ Q₂ = ⊤ ∧ Q₁ ⊓ Q₂ = ⊥ ∧
      ∃ (Hq₁ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z)))
        (theta₁ : (lBar V₀ V hV L) →* Hq₁)
        (hZ₁ : Z ≤ fixV (lBar V₀ V hV L)),
        S168e3QuotAction (lBar V₀ V hV L) Z hZ₁ Hq₁ theta₁ ∧
      ∃ (I : Fin 3 → Subgroup (Vtil V₀ V hV))
        (_hZI : ∀ i, Z₁ ≤ I i)
        (_hind : ∀ i, I i ⊓ (Z₁ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ Z₁)
        (_hsupI : Z₁ ⊔ ⨆ i : Fin 3, I i = U₁)
        (_hsumU : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
          (lBar V₀ V hV L) U₁ Z₁ 3)
        (_hN : ∀ i : Fin 3, AlternatingNatural (lBar V₀ V hV L) (I i) Z₁ n)
        (I₂ : Fin 3 → Subgroup (Vtil V₀ V hV))
        (_hI₂ : ∀ i, I₂ i = (I i).map φ.toMonoidHom)
        (Hq₂ : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z)))
        (theta₂ : H₂ →* Hq₂)
        (hZ₂ : Z ≤ fixV H₂),
        S168e3QuotAction H₂ Z hZ₂ Hq₂ theta₂ ∧
      ∃ (S₁ S₂ : Fin 3 → Subgroup (Vtil V₀ V hV ⧸ Z)),
        (∀ i, S₁ i = (I i).map (QuotientGroup.mk' Z)) ∧
        (∀ i, S₂ i = (I₂ i).map (QuotientGroup.mk' Z)) ∧
        (∀ i, S₂ i = (I i).map ((QuotientGroup.mk' Z).comp φ.toMonoidHom)) ∧
        (∀ i, AlternatingNatural Hq₁ (S₁ i) ⊥ n) ∧
        (∀ i, AlternatingNatural Hq₂ (S₂ i) ⊥ n) ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z n) Hq₁ Q₁ ⊥ 3 ∧
        SumOfNat (fun H U Z => AlternatingNatural H U Z n) Hq₂ Q₂ ⊥ 3 ∧
        (⨆ i : Fin 3, S₁ i) = Q₁ ∧
        (⨆ i : Fin 3, S₂ i) = Q₂ ∧
        (∀ i : Fin 3,
          S₁ i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S₁ j) = ⊥) ∧
        (∀ i : Fin 3,
          S₂ i ⊓ (⨆ (j : Fin 3) (_ : j ≠ i), S₂ j) = ⊥) ∧
        S168e3SelectedActivity (D := D) H₂ U₁ U₂ Z₁ Z₂ Z Q₁ Q₂ Hq₁ theta₁ Hq₂ theta₂ S₁ S₂ := by

  obtain ⟨ψ, H₂, A₁, A₂, φ, U₁, U₂, Z₁, Z₂, Z, Q₁, Q₂,
    hψ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂, hCne,
    hcent₁, hcent₂, hcentcard, hcent₁card, hcent₂card,
    hU₁eq, hU₂eq, hZ₁eq, hZ₂eq, hZeq, hU₂φ, hZ₂φ, hsup,
    hcross12, hcross21, hself₁, hself₂, hinfZ₁, hinfZ₂, hfixZ₁, hfixZ₂,
    hUZ₁, hUZ₂, hQ₁eq, hQ₂eq, hQsup, hQinf, hblock₁⟩ :=
    s168e3_concrete_two_block_selected_involution c hcomp hs hn hA hsum
  obtain ⟨Hq₁, theta₁, hZ₁, hq₁act, hblock₂⟩ := hblock₁
  obtain ⟨I, _hZI, _hind, _hsupI, _hsumU, _hN, I₂, _hI₂, Hq₂, theta₂, hZ₂,
    hq₂act, hblock₃⟩ := hblock₂
  obtain ⟨S₁, S₂, hS₁, hS₂, hS₂comp, hNat₁, hNat₂, hSum₁, hSum₂, hJoin₁, hJoin₂,
    hInd₁, hInd₂, hselectedI⟩ := hblock₃
  obtain ⟨t, htZ, τ, htA, ht2, ht1, htr, hτeq, htau_repr, htau_sq, hrkτ,
    hfixed₁, hfixed₂, hU₁t, hU₂t, hZ₁t, hZ₂t, hQ₁t, hQ₂t, hδblock⟩ := hselectedI
  obtain ⟨δ₁, δ₂, hδ₁, hδ₂, hθcomp₁, hθcomp₂, hnorm₁, hnorm₂, hrefl₁, hrefl₂, hτne⟩ :=
    hδblock
  have hQ : ∀ q : Vtil V₀ V hV ⧸ Z, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      simpa using congrArg (QuotientGroup.mk' Z)
        (s15_Infra_vtil_sq_eq_one V₀ V hV w)
  have hact : S168e3NamedActivity (lBar V₀ V hV L) H₂ Hq₁ Hq₂ Q₁ Q₂ S₁ S₂ t τ :=
    s168e3_activity_of_witness (H₁ := lBar V₀ V hV L) (H₂ := H₂)
      (Hq₁ := Hq₁) (Hq₂ := Hq₂) (Q₁ := Q₁) (Q₂ := Q₂)
      S₁ S₂ t τ hQ hn hNat₁ hNat₂ hnorm₁ hnorm₂ hQinf hQsup hQ₁t hQ₂t
      hJoin₁ hJoin₂ hInd₁ hInd₂ hrkτ hτne hrefl₁ hrefl₂
  have hselected : S168e3SelectedActivity (D := D) H₂ U₁ U₂ Z₁ Z₂ Z Q₁ Q₂
      Hq₁ theta₁ Hq₂ theta₂ S₁ S₂ := by
    refine ⟨t, htZ, τ, htA, ht2, ht1, htr, hτeq, htau_repr, htau_sq, hrkτ,
      hfixed₁, hfixed₂, hU₁t, hU₂t, hZ₁t, hZ₂t, hQ₁t, hQ₂t, ?_⟩
    exact ⟨δ₁, δ₂, hδ₁, hδ₂, hθcomp₁, hθcomp₂, hnorm₁, hnorm₂, hrefl₁, hrefl₂,
      hτne, hact⟩
  refine ⟨ψ, H₂, A₁, A₂, φ, U₁, U₂, Z₁, Z₂, Z, Q₁, Q₂,
    hψ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂, hCne,
    hcent₁, hcent₂, hcentcard, hcent₁card, hcent₂card,
    hU₁eq, hU₂eq, hZ₁eq, hZ₂eq, hZeq, hU₂φ, hZ₂φ, hsup,
    hcross12, hcross21, hself₁, hself₂, hinfZ₁, hinfZ₂, hfixZ₁, hfixZ₂,
    hUZ₁, hUZ₂, hQ₁eq, hQ₂eq, hQsup, hQinf, ?_⟩
  refine ⟨Hq₁, theta₁, hZ₁, hq₁act, ?_⟩
  refine ⟨I, _hZI, _hind, _hsupI, _hsumU, _hN, I₂, _hI₂, Hq₂, theta₂, hZ₂,
    hq₂act, ?_⟩
  exact ⟨S₁, S₂, hS₁, hS₂, hS₂comp, hNat₁, hNat₂, hSum₁, hSum₂, hJoin₁, hJoin₂,
    hInd₁, hInd₂, hselected⟩

private theorem s168e3_actual_cover_induces_of_original_conjugation
    {B Y : Type} [Group B] [Group Y]
    {C : Subgroup B} {H : Subgroup Y} {n : ℕ}
    (ψ : B →* Y) (η : ↥C →* ↥H)
    (hηval : ∀ y : ↥C, (η y : Y) = ψ (y : B))
    (q : (↥C ⧸ Subgroup.center ↥C) ≃* ↥H)
    (hq : ∀ y : ↥C, q (QuotientGroup.mk y) = η y)
    (t : Y) (δ : ↥H →* ↥H)
    (hδval : ∀ h : ↥H, (δ h : Y) = t * (h : Y) * t⁻¹)
    (x : B) (hx : ψ x = t) (α : MulAut ↥C)
    (hαval : ∀ y : ↥C, ((α y : ↥C) : B) = x * (y : B) * x⁻¹)
    (p : alternatingGroup (Fin n) ≃* ↥H) (σ : Equiv.Perm (Fin n))
    (hp : ∀ γ : alternatingGroup (Fin n),
      δ (p γ) = p (MulAut.conjNormal (H := alternatingGroup (Fin n)) σ γ)) :
    ∀ y : ↥C,
      (q.trans p.symm) (QuotientGroup.mk (α y)) =
        MulAut.conjNormal (H := alternatingGroup (Fin n)) σ
          ((q.trans p.symm) (QuotientGroup.mk y)) := by
  have hηδ : ∀ y : ↥C, η (α y) = δ (η y) := by
    intro y
    apply Subtype.ext
    calc (η (α y) : Y) = ψ ((α y : ↥C) : B) := hηval (α y)
      _ = ψ (x * (y : B) * x⁻¹) := by rw [hαval y]
      _ = ψ x * ψ (y : B) * (ψ x)⁻¹ := by simp only [map_mul, map_inv]
      _ = t * (η y : Y) * t⁻¹ := by rw [hx, hηval y]
      _ = (δ (η y) : Y) := (hδval (η y)).symm
  have hκ : ∀ h : ↥H,
      p.symm (δ h) =
        MulAut.conjNormal (H := alternatingGroup (Fin n)) σ (p.symm h) := by
    intro h
    have h1 := hp (p.symm h)
    rw [MulEquiv.apply_symm_apply] at h1
    simpa using congrArg p.symm h1
  intro y
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hq, hq, hηδ y, hκ (η y)]

private theorem s168e3_odd_cover_inverts_center
    {X : Type} [Group X] [Finite X]
    (hperf : Group.IsPerfect X) (hcenter : Nat.card (Subgroup.center X) = 3)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : (X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin n))
    (α : MulAut X) (σ : Equiv.Perm (Fin n)) (hσ : Equiv.Perm.sign σ = -1)
    (hind : ∀ y : X,
      e (QuotientGroup.mk (α y)) =
        MulAut.conjNormal (H := alternatingGroup (Fin n)) σ
          (e (QuotientGroup.mk y))) :
    ∀ z ∈ Subgroup.center X, α z = z⁻¹ := by
  rcases hn with rfl | rfl
  · intro z hz
    refine CFSG.Quasithin.H13.KGHatA6.hatA6OddInverts_holds X hperf hcenter e α σ hσ ?_ z hz
    intro y
    have h := congrArg (fun w : ↥(alternatingGroup (Fin 6)) => (w : Equiv.Perm (Fin 6)))
      (hind y)
    simpa [MulAut.conjNormal_apply] using h
  · intro z hz
    have hHat : CFSG.LocalAnalysis.GLTheoremB.IsHatSeven X :=
      ⟨Group.isPerfect_def.mp hperf, hcenter, ⟨e⟩⟩
    exact CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.hatSevenOddInverts_holds X hHat e α σ hσ hind z hz

private theorem s168e3_actual_cover_branch_false
    {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {ψ : Bar2 D.M →* MulAut (Vtil V₀ V hV)}
    {H H' : Subgroup (MulAut (Vtil V₀ V hV))}
    (A : S168e3ActualCover ψ H) (A' : S168e3ActualCover ψ H')
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    {Z : Subgroup (Vtil V₀ V hV)}
    (hQ : ∀ q : Vtil V₀ V hV ⧸ Z, q ^ 2 = 1)
    {Hq : Subgroup (MulAut (Vtil V₀ V hV ⧸ Z))}
    (theta : H →* Hq) (htheta : Function.Bijective theta)
    {t : MulAut (Vtil V₀ V hV)} {τ : MulAut (Vtil V₀ V hV ⧸ Z)}
    (δ : H →* H)
    (hδval : ∀ h : ↥H,
      (δ h : MulAut (Vtil V₀ V hV)) =
        t * (h : MulAut (Vtil V₀ V hV)) * t⁻¹)
    (hTheta : ∀ h : ↥H,
      (theta (δ h) : MulAut (Vtil V₀ V hV ⧸ Z)) =
        τ * (theta h : MulAut (Vtil V₀ V hV ⧸ Z)) * τ⁻¹)
    (hN : Hq.map (MulAut.conj τ).toMonoidHom = Hq)
    {S : Subgroup (Vtil V₀ V hV ⧸ Z)}
    (hNat : AlternatingNatural Hq S ⊥ n)
    (hτS : S.map τ.toMonoidHom = S)
    (hRankS : E3.mQuot S (S ⊓ fixV (Subgroup.zpowers τ)) = 1)
    {x : Bar2 D.M} (hx : ψ x = t)
    (hxC : x ∈ Subgroup.normalizer (A.C : Set (Bar2 D.M)))
    (hxC' : x ∈ Subgroup.centralizer (A'.C : Set (Bar2 D.M)))
    (hcenterA : Nat.card ↥(Subgroup.center ↥A.C) = 3)
    (hmapA : (Subgroup.center ↥A.C).map A.C.subtype = A.C ⊓ A'.C) :
    False := by
  classical
  have hperf : Group.IsPerfect ↥A.C := A.isComp.1.1
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hnpos : 0 < n := by omega
  obtain ⟨π, β, hπsurj, hβ⟩ := s16c167_altNatural_equiv hnpos hNat
  obtain ⟨_π₀, hReal⟩ := hNat
  have hHS : ∀ g : ↥Hq, ∀ u ∈ S,
      (g : MulAut (Vtil V₀ V hV ⧸ Z)) u ∈ S :=
    fun g u hu => hReal.2.2.2.1 g u hu
  obtain ⟨σ, p, _hσswap, hσsign, _hβact, _hp, hδp⟩ :=
    s168e3_rank_one_heart_conjugation hn5 hQ π hπsurj β hHS hβ theta htheta δ τ
      hTheta hN hτS hRankS
  let α : MulAut ↥A.C := A.C.normalizerMonoidHom ⟨x, hxC⟩
  have hαval : ∀ y : ↥A.C,
      ((α y : ↥A.C) : Bar2 D.M) = x * (y : Bar2 D.M) * x⁻¹ :=
    fun y => Subgroup.normalizerMonoidHom_apply_apply_coe A.C ⟨x, hxC⟩ y
  let e : (↥A.C ⧸ Subgroup.center ↥A.C) ≃* alternatingGroup (Fin n) := A.q.trans p.symm
  have hind : ∀ y : ↥A.C,
      e (QuotientGroup.mk (α y)) =
        MulAut.conjNormal (H := alternatingGroup (Fin n)) σ
          (e (QuotientGroup.mk y)) :=
    s168e3_actual_cover_induces_of_original_conjugation
      (B := Bar2 D.M) (Y := MulAut (Vtil V₀ V hV)) (C := A.C) (H := H) (n := n)
      ψ A.η A.η_val A.q A.q_eq t δ hδval x hx α hαval p σ hδp
  have hinv : ∀ z ∈ Subgroup.center ↥A.C, α z = z⁻¹ :=
    s168e3_odd_cover_inverts_center hperf hcenterA hn e α σ hσsign hind
  have hne : Subgroup.center ↥A.C ≠ ⊥ := by
    have hgt : 1 < Nat.card ↥(Subgroup.center ↥A.C) := by rw [hcenterA]; norm_num
    exact (Subgroup.one_lt_card_iff_ne_bot (Subgroup.center ↥A.C)).1 hgt
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let zB : Bar2 D.M := ((z : ↥A.C) : Bar2 D.M)
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := z)
    rwa [hcenterA] at h
  have hzB3 : zB ^ 3 = 1 := by
    have h := congrArg (fun y : ↥(Subgroup.center ↥A.C) => ((y : ↥A.C) : Bar2 D.M)) hz3
    simpa [zB] using h
  have hαinv : x * zB * x⁻¹ = zB⁻¹ := by
    have h := congrArg (fun y : ↥A.C => (y : Bar2 D.M)) (hinv z z.property)
    rw [hαval z] at h
    simpa [zB] using h
  have hzB_inf : zB ∈ A.C ⊓ A'.C := by
    have hmem : zB ∈ (Subgroup.center ↥A.C).map A.C.subtype :=
      Subgroup.mem_map.mpr ⟨z, z.property, rfl⟩
    rwa [hmapA] at hmem
  have hzB' : zB ∈ A'.C := (Subgroup.mem_inf.mp hzB_inf).2
  have hcomm : zB * x = x * zB :=
    (Subgroup.mem_centralizer_iff.mp hxC') zB hzB'
  have hfix : x * zB * x⁻¹ = zB := by
    calc x * zB * x⁻¹ = (zB * x) * x⁻¹ := by rw [← hcomm]
      _ = zB := by group
  have hzB1 : zB = 1 :=
    CFSG.AGLEmbeddingD2.RealThreeRank.eq_one_of_conj_eq_inv_of_conj_eq hzB3 hαinv hfix
  have hzAC : (z : ↥A.C) = 1 := by
    apply Subtype.ext
    simpa [zB] using hzB1
  exact hzne (Subtype.ext hzAC)

theorem s168e3_false_of_alt_six_seven_sum_three_s_two
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 2)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓
        normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom) : False := by
  let H₁ : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  have _htrans := htrans
  have h125 : Hyp125 D V₀ V := c.setting.hyp16.hyp125
  obtain ⟨ψ, H₂, A₁, A₂, φ, U₁, U₂, Z₁, Z₂, Z, Q₁, Q₂,
    hψ, hφ, hH₂eq, hH₂ne, hcomp₂, hA₂, hCne,
    hcent₁, hcent₂, hcentcard, hcent₁card, hcent₂card,
    hU₁eq, hU₂eq, hZ₁eq, hZ₂eq, hZeq, hU₂φ, hZ₂φ, hsup,
    hcross12, hcross21, hself₁, hself₂, hinfZ₁, hinfZ₂, hfixZ₁, hfixZ₂,
    hUZ₁, hUZ₂, hQ₁eq, hQ₂eq, hQsup, hQinf, hblock₁⟩ :=
    s168e3_concrete_two_block_selected_activity c hcomp hs hn hA hsum
  obtain ⟨Hq₁, theta₁, hZ₁, hq₁act, hblock₂⟩ := hblock₁
  obtain ⟨I, _hZI, _hind, _hsupI, _hsumU, _hN, I₂, _hI₂, Hq₂, theta₂, hZ₂, hq₂act, hblock₃⟩ :=
    hblock₂
  obtain ⟨S₁, S₂, hS₁, hS₂, hS₂comp, hNat₁, hNat₂, hSum₁, hSum₂, hJoin₁, hJoin₂,
    hInd₁, hInd₂, hselectedI⟩ := hblock₃
  obtain ⟨t, htZ, τ, htA, ht2, ht1, htr, hτeq, htau_repr, htau_sq, hrkτ,
    hfixed₁, hfixed₂, hU₁t, hU₂t, hZ₁t, hZ₂t, hQ₁t, hQ₂t, hδblock⟩ := hselectedI
  obtain ⟨δ₁, δ₂, hδ₁, hδ₂, hθcomp₁, hθcomp₂, hnorm₁, hnorm₂, hrefl₁, hrefl₂, hτne, hact⟩ :=
    hδblock
  obtain ⟨hHq₁eq, _htheta₁_val, htheta₁_surj, htheta₁_inj, _htheta₁_repr⟩ := hq₁act
  obtain ⟨hHq₂eq, _htheta₂_val, htheta₂_surj, htheta₂_inj, _htheta₂_repr⟩ := hq₂act
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hsimple₁ : IsSimpleGroup ↥H₁ := by
    obtain ⟨eA⟩ := hA
    exact eA.isSimpleGroup_congr.mpr (alternatingGroup.isSimpleGroup (by simpa using hn5))
  have hsimple₂ : IsSimpleGroup ↥H₂ := by
    obtain ⟨eA⟩ := hA₂
    exact eA.isSimpleGroup_congr.mpr (alternatingGroup.isSimpleGroup (by simpa using hn5))
  have hxmem : t ∈ ψ.range := by
    rw [range_eq_mbar ψ hψ]
    exact htA
  obtain ⟨x, hx⟩ := hxmem
  have hxN₁ : ψ x ∈ Subgroup.normalizer (H₁ : Set (MulAut (Vtil V₀ V hV))) := by
    rw [hx]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfixed₁
  have hxN₂ : ψ x ∈ Subgroup.normalizer (H₂ : Set (MulAut (Vtil V₀ V hV))) := by
    rw [hx]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfixed₂
  have hxC₁ : x ∈ Subgroup.normalizer (A₁.C : Set (Bar2 D.M)) := by
    rw [A₁.C_eq]
    exact mem_normalizer_barImage_of_map_mem_normalizer h125 A₁.hK A₁.hbarK hsimple₁ ψ hψ hxN₁
  have hxC₂ : x ∈ Subgroup.normalizer (A₂.C : Set (Bar2 D.M)) := by
    rw [A₂.C_eq]
    exact mem_normalizer_barImage_of_map_mem_normalizer h125 A₂.hK A₂.hbarK hsimple₂ ψ hψ hxN₂
  have hQ : ∀ q : Vtil V₀ V hV ⧸ Z, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      simpa using congrArg (QuotientGroup.mk' Z)
        (s15_Infra_vtil_sq_eq_one V₀ V hV w)
  unfold S168e3NamedActivity at hact
  dsimp only at hact
  obtain ⟨hActS₁, hActS₂, hRankEq, hLR⟩ := hact
  rcases hLR with hL | hR
  · obtain ⟨_hQ1ne, _hmQ1, hS1act, _hQ2le, _hmQ2, _hCommQ₂, hCommH₂⟩ := hL
    have hxCent₂ : ψ x ∈ Subgroup.centralizer (H₂ : Set (MulAut (Vtil V₀ V hV))) := by
      rw [hx, Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hCommH₂ h hh).symm
    have hxC₂cent : x ∈ Subgroup.centralizer (A₂.C : Set (Bar2 D.M)) := by
      rw [A₂.C_eq]
      exact mem_centralizer_barImage_of_map_mem_centralizer h125 A₂.hK A₂.hbarK hsimple₂ ψ hψ
        hxCent₂
    exact s168e3_actual_cover_branch_false (D := D) A₁ A₂ hn hQ theta₁
      ⟨htheta₁_inj, htheta₁_surj⟩ δ₁ hδ₁ hθcomp₁
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm₁) (hNat₁ 0) (hActS₁ 0) (hS1act 0).2
      hx hxC₁ hxC₂cent hcent₁card hcent₁
  · obtain ⟨_hQ2ne, _hmQ2, hS2act, _hQ1le, _hmQ1, _hCommQ₁, hCommH₁⟩ := hR
    have hxCent₁ : ψ x ∈ Subgroup.centralizer (H₁ : Set (MulAut (Vtil V₀ V hV))) := by
      rw [hx, Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hCommH₁ h hh).symm
    have hxC₁cent : x ∈ Subgroup.centralizer (A₁.C : Set (Bar2 D.M)) := by
      rw [A₁.C_eq]
      exact mem_centralizer_barImage_of_map_mem_centralizer h125 A₁.hK A₁.hbarK hsimple₁ ψ hψ
        hxCent₁
    exact s168e3_actual_cover_branch_false (D := D) A₂ A₁ hn hQ theta₂
      ⟨htheta₂_inj, htheta₂_surj⟩ δ₂ hδ₂ hθcomp₂
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm₂) (hNat₂ 0) (hActS₂ 0) (hS2act 0).2
      hx hxC₂ hxC₁cent hcent₂card (by rw [inf_comm]; exact hcent₂)

theorem s168e3_concl163F_of_alt_six_seven_sum_three_s_two
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 2)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓
        normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom) :
    Concl163F D V₀ V hV L :=
  (s168e3_false_of_alt_six_seven_sum_three_s_two c hcomp hs hn hA hsum htrans).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
