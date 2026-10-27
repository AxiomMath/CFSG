module

public import CFSG.RankThree.GF2n.Tim79a34Sp42Cover

public import CFSG.RankThree.GF2n.Tim79aCitedSp
public import CFSG.Holt.H78.Schur
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUnique
public import CFSG.Alternating.Multipliers.Small
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.SL2Alt5
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherSLTwo

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open Matrix Subgroup
open CFSG.RankThree.PerfectCover

theorem card_ker_le_two_of_hopfMultiplier
    {X Γ : Type*} [Group X] [Finite X] [Group Γ] [Finite Γ]
    (hX : commutator X = ⊤)
    (hM : Nat.card (hopfMultiplier X) ≤ 2)
    (φ : Γ →* X) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcom : φ.ker ≤ commutator Γ) :
    Nat.card φ.ker ≤ 2 := by
  haveI : Group.IsPerfect X := Group.isPerfect_def.2 hX
  haveI : Group.IsPerfect Γ := CFSG.Holt.H78.isPerfect_of_ker_le_commutator φ hφ hcom
  haveI : Finite (hopfMultiplier X) := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
  have hsurj : Function.Surjective (hopfMultiplierToKer φ hφ hcen) :=
    hopfMultiplierToKer_surjective φ hφ hcen
  exact (Nat.card_le_card_of_surjective _ hsurj).trans hM

theorem statedSp_three_two_one_lieModel :
    CFSG.Blueprint.LieModel (StatedSp 3 (GaloisField 2 1)) .PSp 3 2 1 := by
  refine Or.inl ⟨by decide, ?_⟩
  refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩,
    GaloisField 2 1, inferInstance, inferInstance, ?_, ?_⟩
  · rw [GaloisField.card 2 1 (by norm_num), pow_one]
  · exact ⟨((QuotientGroup.quotientMulEquivOfEq
      (StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := 3)
        (K := GaloisField 2 1))).trans QuotientGroup.quotientBot).symm⟩

theorem card_ker_le_two_statedSp_three_two_one
    {Γ : Type} [Group Γ] [Finite Γ]
    (φ : Γ →* StatedSp 3 (GaloisField 2 1)) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcom : φ.ker ≤ commutator Γ) :
    Nat.card φ.ker ≤ 2 := by
  let X := StatedSp 3 (GaloisField 2 1)
  obtain ⟨hX, ⟨eM⟩⟩ :=
    CFSG.EvenSmallLie.SympSix.multiplier_PSp_three_two_one X statedSp_three_two_one_lieModel
  have hM : Nat.card (hopfMultiplier X) ≤ 2 := by
    rw [← Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv,
      Nat.card_congr eM.toEquiv]
    simp [Nat.card_eq_fintype_card]
  exact card_ker_le_two_of_hopfMultiplier hX hM φ hφ hcen hcom

theorem card_ker_le_two_alternatingGroup_five
    {Γ : Type} [Group Γ] [Finite Γ]
    (φ : Γ →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcom : φ.ker ≤ commutator Γ) :
    Nat.card φ.ker ≤ 2 := by
  have hperf : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    CFSG.Holt.H78.isPerfect_alternatingGroup (by norm_num)
  have hM : Nat.card (hopfMultiplier (alternatingGroup (Fin 5))) ≤ 2 := by
    rw [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five).2]
  exact card_ker_le_two_of_hopfMultiplier hperf.commutator_eq_top hM φ hφ hcen hcom

noncomputable def statedSp_one_two_equiv_alternatingGroup_five :
    StatedSp 1 (GaloisField 2 2) ≃* alternatingGroup (Fin 5) :=
  let hsc : (StatedScalars (Fin 1 ⊕ Fin 1) (GaloisField 2 2)).subgroupOf
      (StatedSp 1 (GaloisField 2 2)) = ⊥ :=
    StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
  let eProj : StatedSp 1 (GaloisField 2 2) ≃*
      StatedProj (StatedSp 1 (GaloisField 2 2)) :=
    ((QuotientGroup.quotientMulEquivOfEq hsc).trans QuotientGroup.quotientBot).symm
  eProj.trans ((CFSG.SeitzReduction.OmegaPilot.spOneEquiv (GaloisField 2 2)).trans
    (CFSG.CGT.PushingUpLit.CGT6.sl2_four_equiv_alt5.some))

theorem card_ker_le_two_statedSp_one_two
    {Γ : Type} [Group Γ] [Finite Γ]
    (φ : Γ →* StatedSp 1 (GaloisField 2 2)) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center Γ) (hcom : φ.ker ≤ commutator Γ) :
    Nat.card φ.ker ≤ 2 := by
  let e := statedSp_one_two_equiv_alternatingGroup_five
  let ψ : Γ →* alternatingGroup (Fin 5) := e.toMonoidHom.comp φ
  have hψ : Function.Surjective ψ := e.surjective.comp hφ
  have hker : ψ.ker = φ.ker := by
    ext x
    simp only [ψ, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact e.map_eq_one_iff
  have hcen' : ψ.ker ≤ Subgroup.center Γ := hker ▸ hcen
  have hcom' : ψ.ker ≤ commutator Γ := hker ▸ hcom
  have := card_ker_le_two_alternatingGroup_five ψ hψ hcen' hcom'
  rwa [hker] at this

theorem exists_cover_statedSp_one_two :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ)
      (φ : Γ →* StatedSp 1 (GaloisField 2 2)),
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center Γ ∧
        φ.ker ≤ commutator Γ ∧ Nat.card φ.ker = 2 := by
  classical
  let S : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcardS : Nat.card S = 120 := CFSG.CGT.PushingUpLit.CGT6.card_sl2_five'
  have hcen : Nat.card (Subgroup.center S) = 2 :=
    CFSG.ClassicalInvolution.sl2_natCard_center (by rw [Nat.card_zmod]; norm_num)
  have hcardQ : Nat.card (S ⧸ Subgroup.center S) = 60 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
    rw [hcardS, hcen] at h
    omega
  have hsimple : IsSimpleGroup (S ⧸ Subgroup.center S) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
      (by rw [Nat.card_zmod]; norm_num)
  obtain ⟨eA⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (G := S ⧸ Subgroup.center S) hcardQ
  let ψ : S →* alternatingGroup (Fin 5) :=
    eA.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center S))
  have hψ : Function.Surjective ψ := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker = Subgroup.center S := by
    ext x
    simp only [ψ, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact eA.map_eq_one_iff.trans (QuotientGroup.eq_one_iff x)
  have hperf : Group.IsPerfect S :=
    CFSG.ClassicalInvolution.sl2_isPerfect (by rw [Nat.card_zmod]; norm_num)
  let e := statedSp_one_two_equiv_alternatingGroup_five
  let φ : S →* StatedSp 1 (GaloisField 2 2) := e.symm.toMonoidHom.comp ψ
  have hφ : Function.Surjective φ := e.symm.surjective.comp hψ
  have hkerφ : φ.ker = ψ.ker := by
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact e.symm.map_eq_one_iff
  refine ⟨S, inferInstance, inferInstance, φ, hφ, ?_, ?_, ?_⟩
  · simpa [hkerφ, hker]
  · rw [hkerφ, hker, hperf.commutator_eq_top]
    exact le_top
  · rw [hkerφ, hker]
    exact hcen

theorem exists_cover_statedSp_three_two_one :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ)
      (φ : Γ →* StatedSp 3 (GaloisField 2 1)),
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center Γ ∧
        φ.ker ≤ commutator Γ ∧ Nat.card φ.ker = 2 := by
  obtain ⟨e⟩ := CFSG.EvenSmallLie.Sp6.nonempty_mulEquiv_co3X36
    statedSp_three_two_one_lieModel
  let φ := CFSG.EvenSmallLie.SympSix.co3MQuotHom e
  have hsurj := CFSG.EvenSmallLie.SympSix.co3MQuotHom_surjective e
  have hker := CFSG.EvenSmallLie.SympSix.co3MQuotHom_ker e
  refine ⟨CFSG.Sporadic.Schreier.Co3.co3M, inferInstance, inferInstance, φ, hsurj, ?_, ?_, ?_⟩
  · rw [hker]
  · rw [hker]
    haveI : Group.IsPerfect CFSG.Sporadic.Schreier.Co3.co3M :=
      CFSG.Sporadic.Schreier.Co3.co3M_isPerfect
    rw [Group.IsPerfect.commutator_eq_top]
    exact le_top
  · rw [hker, CFSG.Sporadic.Schreier.Co3.card_co3M_center]

theorem griessSpMultiplierExceptionStatement_of_s6_upper
    (hSp42 : ∀ (Γ : Type) [Group Γ] [Finite Γ]
      (φ : Γ →* StatedSp 2 (GaloisField 2 1)),
      Function.Surjective φ → φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ →
        Nat.card φ.ker ≤ 2)
    :
    CFSG.RankThree.GF2n.Tim79a.GriessSpMultiplierExceptionStatement := by
  intro n f hcases
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨fun Γ _ _ φ hφ hcen hcom =>
      card_ker_le_two_statedSp_one_two φ hφ hcen hcom, exists_cover_statedSp_one_two⟩
  · exact ⟨fun Γ _ _ φ hφ hcen hcom => hSp42 Γ φ hφ hcen hcom, exists_cover_statedSp_two_one⟩
  · exact ⟨fun Γ _ _ φ hφ hcen hcom =>
      card_ker_le_two_statedSp_three_two_one φ hφ hcen hcom,
      exists_cover_statedSp_three_two_one⟩

end CFSG.RankThree.GF2n.Tim79a
