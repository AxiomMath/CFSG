module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGField
public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1Labels
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
public import Certificates.Certificate3951

import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.MarkingChevalley
import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangChev
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcFixTwE6
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcFixE6All
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcOrd
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09Field
import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
import CFSG.LieType.Simplicity.Exceptional
import CFSG.LieType.BorelTits.DerivedQuotient
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem kgFieldCompContExcAux_nonabelian {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

private noncomputable def kgFieldCompContExcAux_fixEquiv {R : Type} [Group R]
    (φ u f : MulAut R) (hφ : φ = u * f * u⁻¹) :
    MonoidHom.eqLocus (φ : R →* R) (MonoidHom.id R) ≃* ↥(ggFixSub f) where
  toFun x := ⟨u⁻¹ (x : R), by
    rw [mem_ggFixSub]
    have hx : (u * f * u⁻¹) (x : R) = (x : R) := by
      rw [← hφ]
      exact x.2
    have h2 := congrArg (fun z => u⁻¹ z) hx
    simpa [MulAut.mul_apply] using h2⟩
  invFun y := ⟨u (y : R), by
    change φ (u (y : R)) = u (y : R)
    rw [hφ]
    have hy : f (y : R) = (y : R) := y.2
    simp [MulAut.mul_apply, hy]⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem kgFieldCompCont_E6Three {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6) (h3 : 3 ∣ lab.n) :
    LargeEvenLabelAll lab (KGFieldCompCont 3 lab) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hl : l = 0 := hlab.2
  have hconjAll : LargeEvenRawDatum ⟨.E6, l, n⟩
      (fun R _ I F => Q R I F ∧ GGRawFieldConj 3 R I F) :=
    ggRawFieldConjOn_chev 3 Nat.prime_three (by norm_num) ⟨.E6, l, n⟩ hlab
      (Or.inr (Or.inr (Or.inl rfl))) Q hQ
  unfold CFSG.StandardType.LargeEvenRawDatum at hconjAll
  obtain ⟨K, hKfield, hKfin, hK, hQK, hconj⟩ := hconjAll
  refine ⟨K, hKfield, hKfin, hK, hQK, ?_⟩
  intro φ hφ hφI hφp J₀ hJ₀
  obtain ⟨u, hu, f, hf, hφeq⟩ := hφ
  have hufI : u * f ∉ LargeEvenChevIDImage (LargeEvenCartanE 6) K
      (LargeEvenChevH (LargeEvenCartanE 6) K false) := by
    rw [← hφeq]
    exact hφI
  have hufp : (u * f) ^ 3 = 1 := by
    rw [← hφeq]
    exact hφp
  have hq : CFSG.IsQuasisimple ↥(CFSG.Blueprint.Chevalley.adjointGroup .E6 K) :=
    CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K
  obtain ⟨eQ⟩ := centerQuot_chevGroup_equiv K .E6
  have hRsimple :
      IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) := by
    haveI : IsSimpleGroup (CFSG.Blueprint.AdjointQuotient .E6 K) := hq.2.1
    exact eQ.isSimpleGroup
  have hRnab : ∃ a b : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false),
      a * b ≠ b * a :=
    kgFieldCompContExcAux_nonabelian eQ.symm hq.2.2
  obtain ⟨f', hf'F, u', hu'I, hord', heq⟩ :=
    hconj hRsimple hRnab u hu f hf hufI hufp
  have hφu' : φ = u' * f' * u'⁻¹ := hφeq.trans heq
  obtain ⟨_, k, hkF, hkFin, hkCard, ⟨eDer⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.fixE6all_fixGroup hn hK (p := 3)
      Nat.prime_three hf'F hord'
  have hq₀ : CFSG.IsQuasisimple ↥(CFSG.Blueprint.Chevalley.adjointGroup .E6 k) :=
    CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 k
  obtain ⟨eQ₀⟩ := centerQuot_chevGroup_equiv k .E6
  have hR₀simple :
      IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) k false)) := by
    haveI : IsSimpleGroup (CFSG.Blueprint.AdjointQuotient .E6 k) := hq₀.2.1
    exact eQ₀.isSimpleGroup
  haveI : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) k false)) :=
    hR₀simple
  have eDerR : ↥(ggFixDer f') ≃*
      LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) k false) :=
    eDer.trans (TableBExc.recipeEquiv .E6 k).symm
  have hDerSimple : IsSimpleGroup ↥(ggFixDer f') := eDerR.isSimpleGroup
  have hR₀nab : ∃ a b : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) k false),
      a * b ≠ b * a :=
    kgFieldCompContExcAux_nonabelian eQ₀.symm hq₀.2.2
  have hDerNab : ∃ a b : ↥(ggFixDer f'), a * b ≠ b * a :=
    kgFieldCompContExcAux_nonabelian eDerR.symm hR₀nab
  let C : Subgroup (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) :=
    MonoidHom.eqLocus (φ : LargeEvenCenterQuot
        (LargeEvenChevH (LargeEvenCartanE 6) K false) →*
        LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
      (MonoidHom.id (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)))
  have eC : C ≃* ↥(ggFixSub f') := kgFieldCompContExcAux_fixEquiv φ u' f' hφu'
  let eJiso : ↥⁅C, C⁆ ≃* ↥(ggFixDer f') :=
    (CFSG.LieType.BorelTits.commutatorSubgroupEquiv C).trans
      ((CFSG.LieType.BorelTits.commutatorEquiv eC).trans
        (CFSG.LieType.BorelTits.commutatorSubgroupEquiv (ggFixSub f')).symm)
  haveI : IsSimpleGroup ↥(ggFixDer f') := hDerSimple
  haveI : IsSimpleGroup ↥⁅C, C⁆ := eJiso.isSimpleGroup
  have hJ₀eq : J₀ = ⁅C, C⁆ :=
    CFSG.ComponentClassification.ExcSelector.eq_of_isComponentOf_of_commutator_eq
      (K := J₀) (J := ⁅C, C⁆) (F := C) rfl hJ₀
  let eJ₀ : ↥J₀ ≃* ↥⁅C, C⁆ := MulEquiv.subgroupCongr hJ₀eq
  haveI : IsSimpleGroup ↥J₀ := eJ₀.isSimpleGroup
  have hnabJ : ∃ a b : ↥J₀, a * b ≠ b * a :=
    kgFieldCompContExcAux_nonabelian eJ₀.symm
      (kgFieldCompContExcAux_nonabelian eJiso.symm hDerNab)
  have hcenterJ : Subgroup.center ↥J₀ = ⊥ :=
    CFSG.ComponentClassification.ExcSelector.center_eq_bot_of_isSimpleGroup' hnabJ
  let eCent : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥J₀ :=
    (QuotientGroup.quotientMulEquivOfEq hcenterJ).trans QuotientGroup.quotientBot
  let eFull : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃*
      LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) k false) :=
    eCent.trans (eJ₀.trans (eJiso.trans eDerR))
  have hm : 1 ≤ n / 3 := Nat.div_pos (Nat.le_of_dvd hn h3) (by norm_num)
  refine ⟨⟨.E6, l, n / 3⟩, ⟨hm, hl⟩, ?_, ?_, ?_⟩
  · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
    exact ⟨k, hkF, hkFin, hkCard, ⟨eFull⟩⟩
  · exact Nat.div_mul_cancel h3
  · exact Or.inl ⟨rfl, rfl⟩

theorem kgFieldCompCont_twE6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .twE6) :
    LargeEvenLabelAll lab (KGFieldCompCont p lab) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hl : l = 0 := hlab.2
  have hconjAll : LargeEvenRawDatum ⟨.twE6, l, n⟩
      (fun R _ I F => Q R I F ∧ GGRawFieldConj p R I F) :=
    ggRawFieldConjOn_twE6 p hp hp2 ⟨.twE6, l, n⟩ hlab rfl Q hQ
  unfold CFSG.StandardType.LargeEvenRawDatum at hconjAll
  obtain ⟨K, hKfield, hKfin, hK, hQK, hconj⟩ := hconjAll
  refine ⟨K, hKfield, hKfin, hK, hQK, ?_⟩
  have hchar : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, ← pow_mul])
  set σ : K ≃+* K := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨hperfG, hnaG, hHG, -, -⟩ :=
    CFSG.LieType.Chevalley.finite_fixed_root_group_perfect
      CFSG.Blueprint.Chevalley.TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ
  have hnaSub : ∃ a b : ↥(CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.E6 K σ.toRingHom), a * b ≠ b * a := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnaG
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  haveI : IsSimpleGroup (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.E6 K σ.toRingHom) :=
    (CFSG.LieType.Chevalley.isSimpleGroup_graphFixedRootGroup_of_perfect
      CFSG.Blueprint.Chevalley.TwistTag.E6 K σ hperfG).1
  have hcenterG : Subgroup.center (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.E6 K σ.toRingHom) = ⊥ :=
    CFSG.ComponentClassification.ExcSelector.center_eq_bot_of_isSimpleGroup' hnaSub
  have eSub : ↥⁅CFSG.Blueprint.twistedFixedGroup CFSG.Blueprint.Chevalley.TwistTag.E6 K
      σ.toRingHom, CFSG.Blueprint.twistedFixedGroup CFSG.Blueprint.Chevalley.TwistTag.E6 K
      σ.toRingHom⁆ ≃* ↥(CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.E6 K σ.toRingHom) :=
    MulEquiv.subgroupCongr hHG
  have eD : CFSG.Blueprint.DerivedCentralQuotient (CFSG.Blueprint.twistedFixedGroup
      CFSG.Blueprint.Chevalley.TwistTag.E6 K σ.toRingHom) ≃*
      ↥(CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.E6 K
        σ.toRingHom) :=
    (QuotientGroup.congr _ _ eSub (Subgroup.map_center_eq eSub)).trans
      ((QuotientGroup.quotientMulEquivOfEq hcenterG).trans QuotientGroup.quotientBot)
  haveI : IsSimpleGroup (CFSG.Blueprint.DerivedCentralQuotient (CFSG.Blueprint.twistedFixedGroup
      CFSG.Blueprint.Chevalley.TwistTag.E6 K σ.toRingHom)) := eD.isSimpleGroup
  obtain ⟨eR⟩ := centerQuot_twistedH_equiv (K := K) CFSG.Blueprint.Chevalley.TwistTag.E6 n
    σ.toRingHom hσ
  have hRsimple : IsSimpleGroup (LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) := eR.isSimpleGroup
  have hRnab : ∃ a b : LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n), a * b ≠ b * a :=
    kgFieldCompContExcAux_nonabelian (eR.trans eD).symm hnaSub
  intro φ hφ hφI hφp J₀ hJ₀
  obtain ⟨u, hu, f, hf, hφeq⟩ := hφ
  have hufI : u * f ∉ LargeEvenChevIDImage (LargeEvenCartanE 6) K
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) := by
    rw [← hφeq]
    exact hφI
  have hufp : (u * f) ^ p = 1 := by
    rw [← hφeq]
    exact hφp
  obtain ⟨f', hf'F, u', hu'I, hord', heq⟩ :=
    hconj hRsimple hRnab u hu f hf hufI hufp
  have hφu' : φ = u' * f' * u'⁻¹ := hφeq.trans heq
  have hK2 : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hp2n : p ∣ 2 * n :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.dvd_of_chevField_order (n := 2 * n)
      (by omega) hK2 hp
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)
      (fun δ h hh => CFSG.LocalAnalysis.GLTheoremA.YS09Field.twisted_map_mem
        (A := LargeEvenCartanE 6) (K := K) LargeEvenRhoE6 n δ h hh)
      hf'F hord'
  have hpn : p ∣ n :=
    ((Nat.coprime_primes hp Nat.prime_two).2 hp2).dvd_of_dvd_mul_left hp2n
  obtain ⟨k, hkF, hkFin, hkCard, hR₀simple, hR₀nab, θ₀, -⟩ :=
    twE6Fix_fixStd hn hK hp hp2 hf'F hord'
  haveI : IsSimpleGroup (LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) k LargeEvenRhoE6 (n / p))) := hR₀simple
  let C : Subgroup (LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) :=
    MonoidHom.eqLocus (φ : LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K
        LargeEvenRhoE6 n) →* LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K
        LargeEvenRhoE6 n))
      (MonoidHom.id (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K
        LargeEvenRhoE6 n)))
  have eC : C ≃* ↥(ggFixSub f') := kgFieldCompContExcAux_fixEquiv φ u' f' hφu'
  let eJiso : ↥⁅C, C⁆ ≃* ↥(ggFixDer f') :=
    (CFSG.LieType.BorelTits.commutatorSubgroupEquiv C).trans
      ((CFSG.LieType.BorelTits.commutatorEquiv eC).trans
        (CFSG.LieType.BorelTits.commutatorSubgroupEquiv (ggFixSub f')).symm)
  haveI : IsSimpleGroup ↥(ggFixDer f') := θ₀.isSimpleGroup
  haveI : IsSimpleGroup ↥⁅C, C⁆ := eJiso.isSimpleGroup
  have hJ₀eq : J₀ = ⁅C, C⁆ :=
    CFSG.ComponentClassification.ExcSelector.eq_of_isComponentOf_of_commutator_eq
      (K := J₀) (J := ⁅C, C⁆) (F := C) rfl hJ₀
  let eJ₀ : ↥J₀ ≃* ↥⁅C, C⁆ := MulEquiv.subgroupCongr hJ₀eq
  haveI : IsSimpleGroup ↥J₀ := eJ₀.isSimpleGroup
  have hnabJ : ∃ a b : ↥J₀, a * b ≠ b * a :=
    kgFieldCompContExcAux_nonabelian eJ₀.symm
      (kgFieldCompContExcAux_nonabelian eJiso.symm
        (kgFieldCompContExcAux_nonabelian θ₀.symm hR₀nab))
  have hcenterJ : Subgroup.center ↥J₀ = ⊥ :=
    CFSG.ComponentClassification.ExcSelector.center_eq_bot_of_isSimpleGroup' hnabJ
  let eCent : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥J₀ :=
    (QuotientGroup.quotientMulEquivOfEq hcenterJ).trans QuotientGroup.quotientBot
  let eFull : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* LargeEvenCenterQuot
      (LargeEvenTwistedH (LargeEvenCartanE 6) k LargeEvenRhoE6 (n / p)) :=
    eCent.trans (eJ₀.trans (eJiso.trans θ₀))
  have hm : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  refine ⟨⟨.twE6, l, n / p⟩, ⟨hm, hl⟩, ?_, ?_, ?_⟩
  · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
    exact ⟨k, hkF, hkFin, hkCard, ⟨eFull⟩⟩
  · exact Nat.div_mul_cancel hpn
  · exact Or.inl ⟨rfl, rfl⟩

theorem kgFieldCompCont_excE {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hS : GGNbrLangS1ExcELabel p lab) :
    LargeEvenLabelAll lab (KGFieldCompCont p lab) := by
  obtain ⟨hcase, hp3, h3⟩ := hS
  subst hp3
  rcases hcase with hE6 | hTwE6 | hE7
  · exact kgFieldCompCont_E6Three hlab hE6 h3
  · exact kgFieldCompCont_twE6 hp hp2 hlab hTwE6
  · exact kgFieldCompCont_E7 hp hp2 hlab hE7

end CFSG.StandardType
