module

public import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofCent
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.Quasithin.Background.FFC2G2
import CFSG.Quasithin.Background.GoldschmidtListedSolv
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofG2Two
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.Assembly.RankThreeEven (projImage projSU projSp)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace Item8KFacts2Proof

section Residuals

noncomputable def perfectResidualEquivOfMulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    perfectResidual X ≃* perfectResidual Y :=
  ((perfectResidual X).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (KFacts.perfectResidual_map_mulEquiv e))

theorem perfectResidual_eq_bot_or_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : perfectResidual Y = ⊥ ∨ IsQuasisimple (perfectResidual Y)) :
    perfectResidual X = ⊥ ∨ IsQuasisimple (perfectResidual X) := by
  rcases h with h | h
  · left
    rw [← Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective,
      KFacts.perfectResidual_map_mulEquiv, h]
  · exact Or.inr (LocalCores.isQuasisimple_of_mulEquiv (perfectResidualEquivOfMulEquiv e).symm h)

theorem isQuasisimple_perfectResidual_of_isQuasisimple {X : Type*} [Group X]
    (h : IsQuasisimple X) : IsQuasisimple (perfectResidual X) := by
  rw [KFacts.perfectResidual_eq_top_of_isPerfect h.1]
  exact LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h

theorem perfectResidual_eq_bot_or_of_isoPGUThree {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (h : IsoPGUThree X (2 ^ m)) : perfectResidual X = ⊥ ∨ IsQuasisimple (perfectResidual X) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hPi : Sec4.PiField false 2 m K := ⟨Nat.prime_two, hm, hK⟩
  exact perfectResidual_eq_bot_or_of_mulEquiv e
    (perfectResidual_projImage_glPi_eq_bot_or_isQuasisimple hPi (fun h => absurd h (by decide)))

theorem perfectResidual_eq_bot_or_of_isoSUThree {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (h : IsoSUThree X (2 ^ m)) : perfectResidual X = ⊥ ∨ IsQuasisimple (perfectResidual X) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  refine perfectResidual_eq_bot_or_of_mulEquiv e ?_
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    left
    have : Finite (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K) := Subtype.finite
    exact (perfect_residual_characterization.2.2.2.2.2).mpr
      (CFSG.Quasithin.isSolvable_statedSU_one hK)
  · exact Or.inr (isQuasisimple_perfectResidual_of_isQuasisimple
      (Item87Proof.isQuasisimple_statedSU_three hK hm2).1)

theorem isQuasisimple_perfectResidual_reeGamma
    {b : ℕ} {k : Type} [Field k]
    [Finite k] [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    IsQuasisimple (perfectResidual (ReeTag.F4.reeGamma k b)) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hk2 : Nat.card k = 2 := by simpa using hk
    set R := reeFixed ReeTag.F4 k 0 with hR
    have hT := CFSG.LieType.Simplicity.titsData k hk2
    have hperf : Group.IsPerfect (commutator R) := hT.isPerfect hk2
    have hq : IsQuasisimple (commutator R) := hT.isQuasisimple hk2
    have heq : perfectResidual R = commutator R := by
      refine le_antisymm ?_ (Item87Res2Proof.le_perfectResidual_of_isPerfect hperf)
      rw [← derivedSeries_one]
      exact iInf_le _ 1
    have hqR : IsQuasisimple (perfectResidual R) := by
      rw [heq]
      exact hq
    exact LocalCores.isQuasisimple_of_mulEquiv
      (perfectResidualEquivOfMulEquiv (ReeTag.reeFixedEquivReeGamma k 0)) hqR
  · have hperf : Group.IsPerfect (ReeTag.F4.reeGamma k b) :=
      ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk⟩
    have hs : IsSimpleGroup (ReeTag.F4.reeGamma k b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hk
    have h4096 := Item812Res2.card_reeGamma_ge hk
    have : Nontrivial (ReeTag.F4.reeGamma k b) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact isQuasisimple_perfectResidual_of_isQuasisimple
      (LocalCores.isQuasisimple_of_isSimpleGroup (exists_ne_comm_of_isPerfect hperf)).1

theorem isQuasisimple_perfectResidual_of_isoGTwoEven
    {X : Type} [Group X] {m : ℕ}
    (hm : 1 ≤ m) (h : IsoGTwoEven X m) : IsQuasisimple (perfectResidual X) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hG : IsQuasisimple (perfectResidual (adjointGroup .G2 K)) := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
      set H := adjointGroup .G2 K
      obtain ⟨E⟩ := Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hK2
      obtain ⟨hs, hnc, -⟩ := CFSG.Quasithin.FFC.commutator_data_g2 hK2 (Subgroup.topEquiv.trans E)
      have hP : Group.IsPerfect ↥⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ :=
        Item812Res6.isPerfect_of_isSimpleGroup_of_not_comm hnc
      have heq : perfectResidual H = ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ := by
        refine le_antisymm ?_ (Item87Res2Proof.le_perfectResidual_of_isPerfect hP)
        rw [← commutator_def, ← derivedSeries_one]
        exact iInf_le _ 1
      rw [heq]
      exact (LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
    · have hK3 : 3 ≤ Nat.card K := by
        rw [hK]
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      exact isQuasisimple_perfectResidual_of_isQuasisimple
        (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK3)
  exact LocalCores.isQuasisimple_of_mulEquiv (perfectResidualEquivOfMulEquiv e).symm hG

end Residuals


section Cases


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}

theorem perfectResidual_eq_bot_or_of_projSU {m : ℕ} (hm : 1 ≤ m)
    (e₁ : L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * m)) (hx3 : x ^ 3 = 1)
    (hk : KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) :
    perfectResidual (barCentralizer (Subgroup.zpowers x) L) = ⊥ ∨
      IsQuasisimple (perfectResidual (barCentralizer (Subgroup.zpowers x) L)) := by
  have hout : InducesOuterTheta x L := by
    rcases hk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
  have h3m : 1 ≤ 3 * m := by omega
  have hU := unitaryFieldData_galoisField 2 (3 * m) h3m
  have hq2 : 2 < 2 ^ (3 * m) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * m))
  rcases Nat.even_or_odd m with hme | hmo
  · have hme3 : Even (3 * m) := hme.mul_left 3
    have hq := Item82OneProof.two_pow_mod_three_of_even hme3
    set E := e₁.trans (projSUEquivUnitaryPSU 2 (3 * m) hU)
    rcases KFacts.inducesKindPSU3_diagonal_or_field (h := hU) L hq2 hx3 hout E with hd | hf
    · exact (false_of_inducesKind_diagonal (psu3_inndiag_cube (by omega)) hd hx3).elim
    · obtain ⟨f₀, hf₀, hC⟩ := KFacts.isoPGUThree_barCentralizer_of_field hq2 hx3 ⟨E, hf⟩
      obtain rfl : f₀ = m := by omega
      exact perfectResidual_eq_bot_or_of_isoPGUThree hm hC
  · have hmo3 : Odd (3 * m) := Nat.odd_mul.mpr ⟨by decide, hmo⟩
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      KFacts.center_eq_bot_of_mulEquiv_fwd (e₁.trans (projSUEquivUnitaryPSU 2 (3 * m) hU)).symm
        (KFacts.center_unitaryPSU_three_eq_bot hU hq2)
    have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
        CFSG.Open.ordTwistedA 2 (2 ^ (3 * m)) :=
      (Nat.card_congr e₁.toEquiv).trans (KFacts.card_projSU_three_two h3m)
    have hodd := KFacts.not_oddCharStdModel_of_mulEquiv_projSU (by omega : 2 ≤ 3 * m) e₁
    rcases hk with hk | hk
    · rcases KFacts.inducesKindPSU3_or_oddCharStdModel hmo3 hcard hZ hk with
        ⟨K, _, hK, hq, hkK⟩ | hO
      · obtain ⟨f₀, hf₀, hC⟩ := KFacts.isoPGUThree_barCentralizer_of_field hq hx3 hkK
        obtain rfl : f₀ = m := by omega
        exact perfectResidual_eq_bot_or_of_isoPGUThree hm hC
      · exact (hodd hO).elim
    · rcases KFacts.inducesKindPSU3_or_oddCharStdModel hmo3 hcard hZ hk with
        ⟨K, _, hK, -, hkK⟩ | hO
      · exact (KFacts.not_inducesKindPSU3_graphField hK hkK).elim
      · exact (hodd hO).elim

theorem perfectResidual_eq_bot_or_of_isoSUThree_quot {m : ℕ} (hm : 1 ≤ m)
    (hL : IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * m))) (hx3 : x ^ 3 = 1)
    (hk : KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) :
    perfectResidual (barCentralizer (Subgroup.zpowers x) L) = ⊥ ∨
      IsQuasisimple (perfectResidual (barCentralizer (Subgroup.zpowers x) L)) := by
  rcases Nat.even_or_odd m with hme | hmo
  · obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := hL
    obtain ⟨e₂⟩ := Item82OneProof.nonempty_statedSU_mulEquiv_projSU (by omega : 1 ≤ 3 * m)
      (Item82OneProof.two_pow_mod_three_of_even (hme.mul_left 3)) hK
    exact perfectResidual_eq_bot_or_of_projSU hm (e₁.trans e₂) hx3 hk
  · rcases hk with hk | hk
    · exact perfectResidual_eq_bot_or_of_isoSUThree hm
        (KFacts.isoSUThree_barCentralizer_of_inducesStdKind hmo hL hx3 hk)
    · exact (KFacts.not_inducesStdKind_graphField_of_isoSUThree (by omega)
        (KFacts.three_dvd_two_pow_three_mul_add_one hmo) hL hk).elim

theorem isQuasisimple_perfectResidual_of_isoGTwoEven_quot
    {m : ℕ} (hm : 1 ≤ m)
    (hL : IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * m)) (hx3 : x ^ 3 = 1)
    (hout : InducesOuterTheta x L) :
    IsQuasisimple (perfectResidual (barCentralizer (Subgroup.zpowers x) L)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
  obtain ⟨-, k, _, _, hk, ⟨φ⟩⟩ := KFacts.barCentralizer_mulEquiv_g2 (by omega) hK hx3 hout e
  exact isQuasisimple_perfectResidual_of_isoGTwoEven hm ⟨k, inferInstance, inferInstance, hk, ⟨φ⟩⟩

theorem perfectResidual_barCentralizer_trialityD4
    (hE : KF82D4SecondCentY0Even) {m : ℕ}
    (hX : IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) m) (hx3 : x ^ 3 = 1)
    (hout : InducesOuterTheta x L) :
    perfectResidual (barCentralizer (Subgroup.zpowers x) L) = ⊥ ∨
      IsQuasisimple (perfectResidual (barCentralizer (Subgroup.zpowers x) L)) := by
  classical
  obtain ⟨q, hq, hq2, hqm, ⟨e₀⟩⟩ := hX
  have hCEM := (Sec4.Census.bridgeExceptional46).trialityD4 q hq hq2
  have hf : 1 ≤ q.exponent := q.exponent_pos
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf hCEM.2
  set e := e₀.trans e₁ with he
  obtain ⟨hN, -⟩ := id hout
  set α := KFacts.inducedAutHom L e ⟨x, hN⟩ with hαdef
  have hα3 : α ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one L e hN hx3
  have hαout : ¬ KFacts.IsInnerAut α := (KFacts.not_isInnerAut_inducedAutHom_iff L e hN).mpr hout
  have hfix := KFacts.map_barCentralizer_eq hN e (Sec4.autFix α) (fun z => Iff.rfl)
  set C := barCentralizer (Subgroup.zpowers x) L with hC
  set φ : C ≃* Sec4.autFix α := (e.subgroupMap C).trans (MulEquiv.subgroupCongr hfix) with hφ
  rcases isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK hσ hα3 hαout with ⟨β, hβ⟩ | he₂
  · exact Or.inr (isQuasisimple_perfectResidual_of_isoGTwoEven hf
      (KFacts.isoGTwoEven_barCentralizer_of_conj_fieldActor hf hK hσ e hN β hβ))
  · obtain ⟨e₂⟩ := he₂
    rcases Nat.even_or_odd q.exponent with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := hE _ hfe hf K σ hK hσ
      have hPi : Sec4.PiField true 2 q.exponent F := ⟨Nat.prime_two, hf, hF⟩
      have hf2 : 2 ≤ q.exponent := by
        obtain ⟨k, hk⟩ := hfe
        omega
      have h2 : 2 < 2 ^ q.exponent :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      exact perfectResidual_eq_bot_or_of_mulEquiv (φ.trans (e₂.trans e₃))
        (perfectResidual_projImage_glPi_eq_bot_or_isQuasisimple hPi (fun _ => h2))
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0_holds _ hfo K σ hK hσ
      have hPi : Sec4.PiField false 2 q.exponent F := ⟨Nat.prime_two, hf, hF⟩
      exact perfectResidual_eq_bot_or_of_mulEquiv (φ.trans (e₂.trans e₃))
        (perfectResidual_projImage_glPi_eq_bot_or_isQuasisimple hPi
          (fun h => absurd h (by decide)))

end Cases

end Item8KFacts2Proof



open Item8KFacts2Proof in
theorem kF87CentRest_of
    (hE : KF82D4SecondCentY0Even) :
    KF87CentRest := by
  intro G _ _ L x m hm htype hSp hx3 hk
  have hout : InducesOuterTheta x L := by
    rcases hk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L h (by decide)
  apply inSubgroup_perfectResidual_eq_bot_or_of_mulEquiv (MulEquiv.refl _)
  rcases htype with ⟨k, hk', hkm, ⟨e₀⟩⟩ | hD | ⟨q, hq2, hqe, hGq⟩ | hU | hS | hSp'
  ·
    have hR := (Sec4.Census.bridgeExceptional46).reeF4 k hk'
    obtain ⟨-, k', hk'1, -, K, _, _, _, hK, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
    obtain ⟨b, k₀, _, _, _, hk₀, ⟨φ⟩⟩ :=
      Item812Res2.exists_barCentralizer_mulEquiv_reeGamma hk'1 hK (e₀.trans e₁) hx3 hout
    exact perfectResidual_eq_bot_or_of_mulEquiv φ
      (Or.inr (isQuasisimple_perfectResidual_reeGamma hk₀))
  ·
    exact perfectResidual_barCentralizer_trialityD4 hE hD hx3 hout
  ·
    exact Or.inr (isQuasisimple_perfectResidual_of_isoGTwoEven_quot hm
      (Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hGq) hx3 hout)
  ·
    obtain ⟨e₁⟩ := hU
    exact perfectResidual_eq_bot_or_of_projSU hm e₁ hx3 hk
  ·
    exact perfectResidual_eq_bot_or_of_isoSUThree_quot hm hS hx3 hk
  · exact (hSp hSp').elim

end CFSG.RankThree.PartTwo.Sec8
