module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate3951
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangChev
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevModel
import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcOrd
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcCore
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def KGFieldCompCont (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I F =>
  ∀ φ : MulAut R, (∃ u ∈ I, ∃ f ∈ Subgroup.closure F, φ = u * f) → φ ∉ I → φ ^ p = 1 →
    ∀ J₀ : Subgroup R, IsComponentOf J₀ (MonoidHom.eqLocus (φ : R →* R) (MonoidHom.id R)) →
      ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
        GGHasLabel labJ (↥J₀ ⧸ Subgroup.center ↥J₀) ∧ labJ.n * p = lab.n ∧
        ((labJ.tag = lab.tag ∧ labJ.rank = lab.rank) ∨ (lab.tag = .twF4 ∧ labJ.tag = .twF4der))

private theorem kgFieldCompContE7Aux_nonabelian {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨e a, e b, fun h' => hab (e.injective (by rw [map_mul, map_mul, h']))⟩

private noncomputable def kgFieldCompContE7Aux_fixEquiv {R : Type} [Group R]
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

theorem kgFieldCompCont_E7 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E7) :
    LargeEvenLabelAll lab (KGFieldCompCont p lab) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hl : l = 0 := hlab.2
  have hconjAll : CFSG.StandardType.LargeEvenRawDatum ⟨.E7, l, n⟩
      (fun R _ I F => Q R I F ∧ GGRawFieldConj p R I F) :=
    ggRawFieldConjOn_chev p hp hp2 ⟨.E7, l, n⟩ hlab
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) Q hQ
  unfold CFSG.StandardType.LargeEvenRawDatum at hconjAll
  obtain ⟨K, hKfield, hKfin, hK, hQK, hconj⟩ := hconjAll
  refine ⟨K, hKfield, hKfin, hK, hQK, ?_⟩
  intro φ hφ hφI hφp J₀ hJ₀
  obtain ⟨u, hu, f, hf, hφeq⟩ := hφ
  have hufI : u * f ∉ LargeEvenChevIDImage (LargeEvenCartanE 7) K
      (LargeEvenChevH (LargeEvenCartanE 7) K false) := by
    rw [← hφeq]
    exact hφI
  have hufp : (u * f) ^ p = 1 := by
    rw [← hφeq]
    exact hφp
  have hq : CFSG.IsQuasisimple ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 K) :=
    chev_isQuasisimple (τ := .E7) (Or.inr (Or.inl rfl)) K
  obtain ⟨eQ⟩ := centerQuot_chevGroup_equiv K .E7
  have hRsimple :
      IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false)) := by
    haveI : IsSimpleGroup (CFSG.Blueprint.AdjointQuotient .E7 K) := hq.2.1
    exact eQ.isSimpleGroup
  have hRnab : ∃ a b : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false),
      a * b ≠ b * a :=
    kgFieldCompContE7Aux_nonabelian eQ.symm hq.2.2
  obtain ⟨f', hf'F, u', hu'I, hord', heq⟩ :=
    hconj hRsimple hRnab u hu f hf hufI hufp
  have hφu' : φ = u' * f' * u'⁻¹ := hφeq.trans heq
  obtain ⟨k, hkF, hkFin, hkCard, ⟨E⟩⟩ :=
    chevFixGroup_recipe (τ := .E7) (Or.inr (Or.inl rfl)) hn hK hp.pos hf'F hord'
  have e₀ : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) k false) ≃*
      ↥(ggFixSub f') := (TableBExc.recipeEquiv .E7 k).trans E
  let C : Subgroup (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false)) :=
    MonoidHom.eqLocus
      (φ : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false) →*
        LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false))
      (MonoidHom.id (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false)))
  have eC : C ≃* ↥(ggFixSub f') := kgFieldCompContE7Aux_fixEquiv φ u' f' hφu'
  let eR₀ : C ≃* LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) k false) :=
    eC.trans e₀.symm
  have hq₀ : CFSG.IsQuasisimple ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 k) :=
    chev_isQuasisimple (τ := .E7) (Or.inr (Or.inl rfl)) k
  obtain ⟨eQ₀⟩ := centerQuot_chevGroup_equiv k .E7
  have hR₀simple :
      IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) k false)) := by
    haveI : IsSimpleGroup (CFSG.Blueprint.AdjointQuotient .E7 k) := hq₀.2.1
    exact eQ₀.isSimpleGroup
  have hR₀nab : ∃ a b : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) k false),
      a * b ≠ b * a :=
    kgFieldCompContE7Aux_nonabelian eQ₀.symm hq₀.2.2
  haveI : IsSimpleGroup (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) k false)) :=
    hR₀simple
  have hCsimple : IsSimpleGroup C := eR₀.isSimpleGroup
  haveI : IsSimpleGroup C := hCsimple
  have hCnab : ∃ a b : C, a * b ≠ b * a :=
    kgFieldCompContE7Aux_nonabelian eR₀.symm hR₀nab
  have hcenterC : Subgroup.center C = ⊥ := center_eq_bot_of_simple_nonabelian hCnab
  have hJ₀eqC : J₀ = C :=
    CFSG.ComponentClassification.ExcSelector.eq_of_isComponentOf_of_isSimpleGroup (J := C) hJ₀
  have hcenterJ₀ : Subgroup.center ↥J₀ = ⊥ := by
    rw [hJ₀eqC]
    exact hcenterC
  let eJ : ↥J₀ ≃* ↥C := MulEquiv.subgroupCongr hJ₀eqC
  let eCent : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃* ↥J₀ :=
    (QuotientGroup.quotientMulEquivOfEq hcenterJ₀).trans QuotientGroup.quotientBot
  let eFull : (↥J₀ ⧸ Subgroup.center ↥J₀) ≃*
      LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) k false) :=
    eCent.trans (eJ.trans eR₀)
  have hpn : p ∣ n :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.dvd_of_chevField_order hn hK hp
      (LargeEvenChevH (LargeEvenCartanE 7) K false)
      (fun σ h hh => CFSG.LocalAnalysis.GLTheoremA.YS09Field.chevH_stable
        (LargeEvenCartanE 7) K false σ h hh)
      hf'F hord'
  have hm : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  refine ⟨⟨.E7, l, n / p⟩, ⟨hm, hl⟩, ?_, ?_, ?_⟩
  · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
    exact ⟨k, hkF, hkFin, hkCard, ⟨eFull⟩⟩
  · exact Nat.div_mul_cancel hpn
  · exact Or.inl ⟨rfl, rfl⟩

end CFSG.StandardType
