module

public import CFSG.Timmesfeld.ARS.ExclNSDefs
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.Blueprint.Catalog
import CFSG.Timmesfeld.RankTwo.LevisMinusN
import CFSG.Timmesfeld.RankTwo.Presentation
import CFSG.Timmesfeld.ARS.CaseOANSLSp
import CFSG.LieType.CurtisTits.Symplectic
import CFSG.LieType.CurtisTits.Spin
import CFSG.LieType.CurtisTits.Exceptional
import CFSG.LieType.Steinberg.G2.Perfect
import CFSG.LieType.Steinberg.Adjoint.Perfect
import CFSG.LieType.Steinberg.TwistedD4.RankOne
import CFSG.LieType.Steinberg.TwistedE6.Local
import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
import CFSG.Quasithin.Recognition.CertG2Two
import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixField
import CFSG.Timmesfeld.Final.PSU33
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFourAlg
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate19953
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.ARS.Sec5Maximal
public import CFSG.Timmesfeld.ARS.Sec5Ten
public import CFSG.Timmesfeld.RankOne
public import Certificates.Certificate43
import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Blueprint
open CFSG.Blueprint.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedSp)
open CFSG.Open (StatedLieAdmissible)
open CFSG.AGLEmbedding.KlingenSpFour (card_eq_of_mem_iff_range)

theorem card_adjDatum_rootGroup {τ : Tag} {K₀ : Type} [Field K₀] (i₀ : Fin τ.rank) :
    Nat.card ((Adjoint.adjDatum (CFSG.LieType.Chevalley.rootOperatorFamily τ) K₀).rootGroup
      (Pi.single i₀ 1)) = Nat.card K₀ :=
  card_eq_of_mem_iff_range _ _ (Adjoint.xPar_injective (IsRoot.basis i₀)) fun g =>
    (Adjoint.mem_rootGroup_iff (IsRoot.basis i₀) g).trans
      ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem quasisimple_lieModel_symplecticDatum {n : ℕ} {F₀ : Type} [Field F₀] (hn : 3 ≤ n)
    (i₀ : Fin n) {f : ℕ} (hf : 1 ≤ f)
    (hX : Nat.card ((Symplectic.rootDatum n F₀).rootGroup (Pi.single i₀ 1)) = 2 ^ f) :
    CFSG.IsQuasisimple ↥(StatedSp n F₀) ∧
      LieModel (↥(StatedSp n F₀) ⧸ Subgroup.center ↥(StatedSp n F₀)) .PSp n 2 f := by
  have hp := Sp.isParametrization (n := n) (F := F₀) (Pi.single i₀ 1)
    (CaseOANSL.mem_roots_single i₀)
  have hF : Nat.card F₀ = 2 ^ f := (card_eq_of_mem_iff_range _ _ hp.2.2 fun g =>
    (hp.1 g).trans ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩).symm.trans hX
  have : Finite F₀ := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have hadm : StatedLieAdmissible .PSp n 2 f :=
    ⟨Nat.prime_two, hf, by omega, fun e => absurd (congrArg Prod.fst e) (by omega)⟩
  obtain ⟨⟨-, hK, hm⟩, -⟩ :=
    CurtisTits.curtisTitsConclusion_symplectic.{0} (n := n) (F := F₀) hadm hF hn
  exact ⟨hK, hm⟩

theorem quasisimple_lieModel_minusDatum {n : ℕ} {K' : Type} [Field K'] {b c : K'}
    (hirr : ∀ s : K', s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) (i₀ : Fin (n - 1))
    (hi : i₀.val + 2 < n) {f : ℕ} (hf : 1 ≤ f)
    (hX : Nat.card ((Spin.Twisted.minusDatum n hirr).rootGroup (Pi.single i₀ 1)) = 2 ^ f) :
    CFSG.IsQuasisimple ↥(spinGroup (Spin.quadMinus n K' b c)) ∧
      LieModel (↥(spinGroup (Spin.quadMinus n K' b c)) ⧸
        Subgroup.center ↥(spinGroup (Spin.quadMinus n K' b c))) .POmegaMinus n 2 f := by
  have hL := RankTwo.minusLong_single (n := n) hi
  have hF : Nat.card K' = 2 ^ f := (card_eq_of_mem_iff_range _
    (RankTwo.minusXL n b c (Pi.single i₀ 1)) (RankTwo.minusXL_injective hL) fun g =>
      ⟨fun hg => (RankTwo.exists_minusXL_eq hirr hL hg).imp fun _ ha => ha.symm,
        fun ⟨a, ha⟩ => ha ▸ RankTwo.minusXL_mem hirr hL a⟩).symm.trans hX
  have : Finite K' := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have hadm : StatedLieAdmissible .POmegaMinus n 2 f := ⟨Nat.prime_two, hf, hn⟩
  obtain ⟨⟨-, hK, hm⟩, -⟩ := CurtisTits.curtisTitsConclusion_spinMinus.{0} hirr hadm hF
  exact ⟨hK, hm⟩

theorem quasisimple_lieModel_g2Datum {K₀ : Type} [Field K₀] (i₀ : Fin (Tag.rank .G2)) {f : ℕ}
    (hf : 2 ≤ f) (hX : Nat.card ((Adjoint.g2Datum K₀).rootGroup (Pi.single i₀ 1)) = 2 ^ f) :
    CFSG.IsQuasisimple ↥(adjointGroup .G2 K₀) ∧ LieModel (AdjointQuotient .G2 K₀) .G2 0 2 f := by
  have hF : Nat.card K₀ = 2 ^ f := (card_adjDatum_rootGroup (τ := .G2) i₀).symm.trans hX
  have : Finite K₀ := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have h3 : 3 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  refine ⟨Adjoint.isQuasisimple_g2_of_three_le_card K₀ (by rw [hF]; exact h3), ?_⟩
  exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, by omega, rfl, h3⟩,
    K₀, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩)

theorem quasisimple_lieModel_f4Datum {K₀ : Type} [Field K₀] (i₀ : Fin (Tag.rank .F4)) {f : ℕ}
    (hf : 1 ≤ f) (hX : Nat.card ((Adjoint.f4Datum K₀).rootGroup (Pi.single i₀ 1)) = 2 ^ f) :
    CFSG.IsQuasisimple ↥(adjointGroup .F4 K₀) ∧ LieModel (AdjointQuotient .F4 K₀) .F4 0 2 f := by
  have hF : Nat.card K₀ = 2 ^ f := (card_adjDatum_rootGroup (τ := .F4) i₀).symm.trans hX
  have : Finite K₀ := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  refine ⟨Adjoint.isQuasisimple_f4 K₀, ?_⟩
  exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hf, rfl⟩,
    K₀, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩)

theorem quasisimple_lieModel_twistedD4Datum (e : ℕ) [Fact (1 ≤ e)] (i₀ : Fin (Tag.rank .G2))
    (hi : i₀.val = 0) {f : ℕ} (hX : Nat.card ((TwistedD4.twistedDatum
      (iterateFrobenius (GaloisField 2 (3 * e)) 2 e)).rootGroup (Pi.single i₀ 1)) = 2 ^ f) :
    f = e ∧ CFSG.IsQuasisimple ↥(TwistedD4.twistedGroup
        (iterateFrobenius (GaloisField 2 (3 * e)) 2 e)) ∧
      LieModel (↥(TwistedD4.twistedGroup (iterateFrobenius (GaloisField 2 (3 * e)) 2 e)) ⧸
        Subgroup.center ↥(TwistedD4.twistedGroup
          (iterateFrobenius (GaloisField 2 (3 * e)) 2 e))) .trialityD4 0 2 e := by
  have he : 1 ≤ e := Fact.out
  set K := GaloisField 2 (3 * e)
  set σ := iterateFrobenius K 2 e
  have hK : Nat.card K = 2 ^ (3 * e) := GaloisField.card 2 (3 * e) (by omega)
  have hK3 : Nat.card K = (2 ^ e) ^ 3 := by rw [hK, ← pow_mul, mul_comm]
  have hσ : ∀ c, σ c = c ^ 2 ^ e := fun c => iterateFrobenius_def 2 e c
  have hσ3 := TwistedD4.sigma_three_of_card hK3 hσ
  obtain rfl : i₀ = TwistedD4.ng 0 := Fin.ext hi
  have hα : IsRoot TwistedD4.d4 (Pi.single (TwistedD4.nd 2) 1) := .basis _
  have hle := TwistedD4.twistedRootSubgroupD4_le_twistedGroup σ
    (IsRoot.basis (τ := .G2) (TwistedD4.ng 0))
  have h1 : Nat.card ((TwistedD4.twistedDatum σ).rootGroup (Pi.single (TwistedD4.ng 0) 1)) =
      Nat.card (TwistedD4.twistedRootSubgroupD4 σ (Pi.single (TwistedD4.ng 0) 1)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h2 : Nat.card (TwistedD4.twistedRootSubgroupD4 σ (Pi.single (TwistedD4.ng 0) 1)) =
      Nat.card {c : K // σ c = c} := by
    refine card_eq_of_mem_iff_range _ (fun c : {c : K // σ c = c} =>
      Adjoint.xPar (CFSG.LieType.Chevalley.rootOperatorFamily TwistedD4.d4)
        (Pi.single (TwistedD4.nd 2) 1) c.1)
      (fun a b hab => Subtype.ext (Adjoint.xPar_injective hα hab)) fun g => ?_
    rw [TwistedD4.mem_twistedRootSubgroupD4_iff_of_fixed hσ3 hα TwistedD4.proj_single_two
      TwistedD4.rho_single_two]
    exact ⟨fun ⟨c, hc, hg⟩ => ⟨⟨c, hc⟩, hg⟩, fun ⟨c, hg⟩ => ⟨c.1, c.2, hg⟩⟩
  have h3 : Nat.card {c : K // σ c = c} = 2 ^ e := by
    rw [← CFSG.Quasithin.H13.F431.D4q.Out.card_pow_fixed (by omega) he (dvd_mul_left e 3) hK]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => by rw [hσ])
  refine ⟨Nat.pow_right_injective le_rfl (hX.symm.trans (h1.trans (h2.trans h3))), ?_, ?_⟩
  · exact TwistedD4.twistedGroup_isQuasisimple_of_card
      (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) he)) hK3 hσ
  · exact lieModel_twistedD4_quotient Nat.prime_two he hK3 σ hσ

theorem quasisimple_lieModel_twistedE6Datum (e : ℕ) [Fact (1 ≤ e)] (i₀ : Fin (Tag.rank .F4))
    (hi : i₀.val < 2) {f : ℕ}
    (hX : Nat.card ((Exceptional.twistedE6Datum 2 e).rootGroup (Pi.single i₀ 1)) = 2 ^ f) :
    f = e ∧ CFSG.IsQuasisimple (Exceptional.twistedE6Group 2 e) ∧
      LieModel (Exceptional.twistedE6Group 2 e ⧸ Subgroup.center (Exceptional.twistedE6Group 2 e))
        .twistedE6 0 2 e := by
  have he : 1 ≤ e := Fact.out
  have hk : Nat.card (GaloisField 2 (2 * e)) = 2 ^ (2 * e) := GaloisField.card 2 (2 * e) (by omega)
  have hθ : ∀ c, Exceptional.frobQ 2 e c = c ^ 2 ^ e := Exceptional.frobQ_apply 2 e
  obtain ⟨a, ha, hρ⟩ : ∃ a : Fin (Tag.rank .E6), TwistedE6.orbitMap a = i₀ ∧
      TwistedE6.rhoPerm a = a := by
    obtain ⟨v, hv⟩ := i₀
    obtain rfl | rfl : v = 0 ∨ v = 1 := by simp only at hi; omega
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
  have hα : IsRoot .E6 (Pi.single a 1) := .basis a
  have hp : TwistedE6.proj (Pi.single a 1) = Pi.single i₀ 1 := by
    rw [TwistedE6.proj_single, ha]
  have hfix : TwistedE6.rho (Pi.single a 1) = Pi.single a 1 := by
    rw [TwistedE6.rho_single, hρ]
  have hmem : ∀ c : {c : GaloisField 2 (2 * e) // Exceptional.frobQ 2 e c = c},
      Minuscule.e6Data_valid.xm (GaloisField 2 (2 * e)) (Pi.single a 1) c.1 ∈
        TwistedE6.fixedGroup (GaloisField 2 (2 * e)) (Exceptional.frobQ 2 e) := by
    intro c
    rw [TwistedE6.mem_fixedGroup, TwistedE6.sigma_xm (Exceptional.frobQ 2 e) hα, hfix,
      TwistedE6.twistSign_of_rho_eq hα hfix, Int.cast_one, one_mul, c.2]
  have h2 : Nat.card ((Exceptional.twistedE6Datum 2 e).rootGroup (Pi.single i₀ 1)) =
      Nat.card {c : GaloisField 2 (2 * e) // Exceptional.frobQ 2 e c = c} := by
    refine card_eq_of_mem_iff_range _ (fun c => (⟨_, hmem c⟩ :
        TwistedE6.fixedGroup (GaloisField 2 (2 * e)) (Exceptional.frobQ 2 e)))
      (fun c d hcd => Subtype.ext (Minuscule.e6Data_valid.xm_injective (GaloisField 2 (2 * e)) hα
        (congrArg Subtype.val hcd))) fun g => ?_
    change g ∈ TwistedE6.twistedRootGroup (GaloisField 2 (2 * e)) (Exceptional.frobQ 2 e)
      (Pi.single i₀ 1) ↔ _
    rw [TwistedE6.mem_twistedRootGroup_iff_of_fixed (Exceptional.frobQ 2 e) hα hp hfix]
    exact ⟨fun ⟨c, hc, hg⟩ => ⟨⟨c, hc⟩, Subtype.ext hg⟩,
      fun ⟨c, hg⟩ => ⟨c.1, c.2, congrArg Subtype.val hg⟩⟩
  have h3 : Nat.card {c : GaloisField 2 (2 * e) // Exceptional.frobQ 2 e c = c} = 2 ^ e := by
    rw [← CFSG.Quasithin.H13.F431.D4q.Out.card_pow_fixed (by omega) he (dvd_mul_left e 2) hk]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c => by rw [hθ])
  have hadm : StatedLieAdmissible .twistedE6 0 2 e := ⟨Nat.prime_two, he, rfl⟩
  obtain ⟨⟨-, hK, hm⟩, -⟩ := CurtisTits.curtisTitsConclusion_twistedE6.{0} 2 e hadm
  exact ⟨Nat.pow_right_injective le_rfl (hX.symm.trans (h2.trans h3)), hK, hm⟩

theorem lieModel_PSU_of_g2Datum_two {G : Type} [Group G] [Group.IsPerfect G] {K₀ : Type}
    [Field K₀] (hK : Nat.card K₀ = 2) (Ψ : ↥(adjointGroup .G2 K₀) →* G)
    (hsurj : Function.Surjective Ψ) (hker : Ψ.ker ≤ Subgroup.center ↥(adjointGroup .G2 K₀)) :
    LieModel G .PSU 3 3 1 := by
  have : Finite K₀ := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot_field .G2 K₀] at hker
  have hinj : Function.Injective Ψ := (MonoidHom.ker_eq_bot_iff Ψ).1 (le_bot_iff.1 hker)
  let e : ↥(adjointGroup .G2 K₀) ≃* G := MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  have : Group.IsPerfect ↥(adjointGroup .G2 K₀) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hAA : ⁅adjointGroup .G2 K₀, adjointGroup .G2 K₀⁆ = adjointGroup .G2 K₀ :=
    Subgroup.commutator_eq_self
  obtain ⟨e'⟩ := CFSG.Quasithin.g2_derived_mulEquiv_PSU3 K₀ hK
  obtain ⟨e''⟩ := CFSG.Timmesfeld.Final.nonempty_statedProj_statedSU_equiv_PSU3
  exact Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, GaloisField 3 (2 * 1),
    inferInstance, inferInstance, by rw [GaloisField.card 3 (2 * 1) (by norm_num)]; norm_num,
    ⟨((e.symm.trans (MulEquiv.subgroupCongr hAA.symm)).trans e').trans e''.symm⟩⟩

end CFSG.Timmesfeld.ARS
