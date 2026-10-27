module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreM6Defs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralEmbed
public import CFSG.LocalAnalysis.StandardType.GGLieM6cConj
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourToral
public import CFSG.LocalAnalysis.StandardType.GGLieM6cFrobE6
public import CFSG.LocalAnalysis.StandardType.GGLieM6cFrobTwE6
public import CFSG.LocalAnalysis.StandardType.GGLieM6cRegular
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
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.StandardType.LieCore.M6c

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.LieCore
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open CFSG.StandardType.SCFourCover (E6AdToral)
open CFSG.Open (StatedLieTag)

private theorem m6c_toral_of_ker
    (A : Subgroup (ModGL Tag.E6 GGL)) (g : ModGL Tag.E6 GGL)
    (hg : g ∈ adjointGroup Tag.E6 GGL)
    (hEM : A.map (MulAut.conj g).toMonoidHom ≤ monomialSubgroup Tag.E6 GGL)
    (hker : ∀ e (he : e ∈ A.map (MulAut.conj g).toMonoidHom),
      weylQuotientHom Tag.E6 GGL ⟨e, hEM he⟩ = 1) :
    IsToralSubgroup Tag.E6 GGL A := by
  refine ⟨g⁻¹, inv_mem hg, fun x hx => ?_⟩
  have hxE : (MulAut.conj g).toMonoidHom x ∈ A.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hmaps : MapsRootLines ((MulAut.conj g).toMonoidHom x) 1 := by
    have h := mapsRootLines_weylQuotientHom (τ := Tag.E6) (R := GGL)
      (⟨(MulAut.conj g).toMonoidHom x, hEM hxE⟩ : monomialSubgroup Tag.E6 GGL)
    rwa [hker _ hxE] at h
  have htor := mem_torusGroup_of_mapsRootLines_one (hEM hxE) hmaps
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using htor

private theorem m6c_notAbelian_of_ne_bot
    (A : Subgroup (ModGL Tag.E6 GGL)) (hEa : A ≤ adjointGroup Tag.E6 GGL)
    (hAab : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ 4)
    (hab : GGLieAbelianPreimageE6 A)
    (g : ModGL Tag.E6 GGL) (hg : g ∈ adjointGroup Tag.E6 GGL)
    (hEM : A.map (MulAut.conj g).toMonoidHom ≤ monomialSubgroup Tag.E6 GGL)
    (A_W : Subgroup (WeylGroup Tag.E6))
    (hEA : ∀ w, w ∈ A_W ↔ ∃ e, ∃ he : e ∈ A.map (MulAut.conj g).toMonoidHom,
      weylQuotientHom Tag.E6 GGL ⟨e, hEM he⟩ = w)
    (hAS : A_W ≤ modelHomE6.range) (hA1 : A_W ≠ ⊥) (hAg : ∀ i, gE6 i ∉ A_W) :
    False := by
  have hEa' : A.map (MulAut.conj g).toMonoidHom ≤ adjointGroup Tag.E6 GGL :=
    hEM.trans monomialSubgroup_le_adjointGroup'
  have hEab' : IsElemAbelian 3 (A.map (MulAut.conj g).toMonoidHom) :=
    hAab.map (MulAut.conj g).toMonoidHom
  have hcard' : 3 ^ 4 ≤ Nat.card (A.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hAcard]
  have hab' : GGLieAbelianPreimageE6 (A.map (MulAut.conj g).toMonoidHom) :=
    abelianPreimage_map_conj hab hg
  exact not_abelianPreimage_of_regular (A.map (MulAut.conj g).toMonoidHom) hEa' hEM hEab'
    hcard' A_W hEA hAS hA1 hAg hab'

theorem isToral_of_abelianPreimage
    (A : Subgroup (ModGL Tag.E6 GGL)) (hEa : A ≤ adjointGroup Tag.E6 GGL)
    (hEfin : (A : Set (ModGL Tag.E6 GGL)).Finite)
    (hAab : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ 4)
    (hab : GGLieAbelianPreimageE6 A) :
    IsToralSubgroup Tag.E6 GGL A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, hEM, hS4⟩ :=
    CFSG.StandardType.E6NonToralThree.exists_conj_regular (L := GGL) (ℓ := 2)
      (by norm_num : (2 : ℕ) ≠ 3)
      (CFSG.LieType.AlgebraicGroups.isAlgebraic_zmod_of_isAlgClosure 2 (ZMod 2) GGL)
      hEa hEfin hAab
  let A_W : Subgroup (WeylGroup Tag.E6) :=
    ((weylQuotientHom Tag.E6 GGL).comp (Subgroup.inclusion hEM)).range
  have hEA : ∀ w, w ∈ A_W ↔ ∃ e, ∃ he : e ∈ A.map (MulAut.conj g).toMonoidHom,
      weylQuotientHom Tag.E6 GGL ⟨e, hEM he⟩ = w := by
    intro w
    show w ∈ ((weylQuotientHom Tag.E6 GGL).comp (Subgroup.inclusion hEM)).range ↔ _
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.1, x.2, hx⟩
    · rintro ⟨e, he, hwe⟩
      exact ⟨⟨e, he⟩, hwe⟩
  by_cases hbot : A_W = ⊥
  · exact m6c_toral_of_ker A g hg hEM (fun e he => by
      have hmem : weylQuotientHom Tag.E6 GGL ⟨e, hEM he⟩ ∈ A_W :=
        (hEA _).mpr ⟨e, he, rfl⟩
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem)
  · exfalso
    exact m6c_notAbelian_of_ne_bot A hEa hAab hAcard hab g hg hEM A_W hEA
      (fun w hw => by
        obtain ⟨e, he, hwe⟩ := (hEA w).mp hw
        rw [← hwe]
        exact (hS4 e he).1)
      hbot
      (fun i hgi => by
        obtain ⟨e, he, hwe⟩ := (hEA _).mp hgi
        exact (hS4 e he).2 i hwe)

theorem e6AdToral_of_abelianPreimage_GGL
    (A : Subgroup (ModGL Tag.E6 GGL)) (hEa : A ≤ adjointGroup Tag.E6 GGL)
    (hEfin : (A : Set (ModGL Tag.E6 GGL)).Finite)
    (hAab : IsElemAbelian 3 A) (hAcard : Nat.card A = 3 ^ 4)
    (hab : GGLieAbelianPreimageE6 A) :
    E6AdToral A := by
  obtain ⟨g, hg, hgt⟩ := isToral_of_abelianPreimage A hEa hEfin hAab hAcard hab
  exact ⟨g⁻¹, inv_mem hg, fun x hx => by simpa using hgt x hx⟩

theorem ggLieNonToralRankFour_holds
    : GGLieNonToralRankFour := by
  classical
  rw [GGLieNonToralRankFour]
  intro f hf t ht A hA hAab hAcard
  rcases ht with ⟨rfl, hfodd⟩ | ⟨rfl, hfeven⟩
  · have hEa : A ≤ adjointGroup Tag.E6 GGL := fun x hx => (hA hx).1
    have hcardne : Nat.card A ≠ 0 := by rw [hAcard]; norm_num
    have hEfin : (A : Set (ModGL (langTag .E6) GGL)).Finite :=
      Set.finite_coe_iff.mpr (Nat.finite_of_card_ne_zero hcardne)
    have hab : GGLieAbelianPreimageE6 A :=
      abelianPreimage_of_ratPoints_E6 hfodd hA
        (fun x hx y hy => CFSG.Open.IsElemAbelian.comm hAab hx hy)
    exact isToral_of_abelianPreimage A hEa hEfin hAab hAcard hab
  · have hEa : A ≤ adjointGroup Tag.E6 GGL := fun x hx => (hA hx).1
    have hcardne : Nat.card A ≠ 0 := by rw [hAcard]; norm_num
    have hEfin : (A : Set (ModGL (langTag .twistedE6) GGL)).Finite :=
      Set.finite_coe_iff.mpr (Nat.finite_of_card_ne_zero hcardne)
    have hab : GGLieAbelianPreimageE6 A :=
      abelianPreimage_of_ratPoints_twistedE6 hfeven hA
        (fun x hx y hy => CFSG.Open.IsElemAbelian.comm hAab hx hy)
    exact isToral_of_abelianPreimage A hEa hEfin hAab hAcard hab

end CFSG.StandardType.LieCore.M6c
