module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitRAssembly
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6PlaceNTConfig
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6ThetaModel
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTThreeUnitary
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6BigElemAbelian
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcCaseV
import CFSG.LocalAnalysis.StandardType.GGLieBridgeTheta
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.RCKRP CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)


theorem twE6PlaceNT_holds : TwE6PlaceNT := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos hres A hA hf θ hθψ hθker hθrange Θ hΘR hΘone hpart hΘinj hnt
  obtain ⟨hp3, h3, h9⟩ := hres
  subst hp3
  obtain ⟨hcore, -, hV⟩ :=
    twE6_caseVData_of_nontoral hpos hA hθker hθrange Θ hΘR hpart hΘinj hnt
  have hVcfg := hV
  unfold RCKExcCaseVData at hV
  obtain ⟨-, -, -, -, hcardA, hBA, hAG, hZ⟩ := hV
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, hθker, hZ]
  have ht : GGExcFive .twistedE6 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨θ₀, -, -, hθ₀range, hθ₀cent⟩ := ggLieBridge_theta ht hf hcore.1
  have hcent : ∀ z ∈ ggFixGp .twistedE6 f, (∀ x : ↥G₀, z * θ x = θ x * z) → z = 1 := by
    intro z hz hc
    refine hθ₀cent z hz (fun x => ?_)
    have hx : θ₀ x ∈ θ.range := by
      rw [hθrange, ← hθ₀range]
      exact MonoidHom.mem_range.2 ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hx
    rw [← hy]
    exact hc y
  have hΘθ : ∀ a : ↥A, Θ a = θ ⟨(a : X), hAG a.2⟩ := by
    intro a
    have hdN : (a : X) ∈ Subgroup.normalizer (G₀ : Set X) := G₀.le_normalizer (hAG a.2)
    have hθΦ : θ ⟨(a : X), hAG a.2⟩ ∈ ggFixGp .twistedE6 f := by
      have hmem : θ ⟨(a : X), hAG a.2⟩ ∈ θ.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
      rw [hθrange] at hmem
      exact Subgroup.commutator_le_self (ggFixGp .twistedE6 f) hmem
    exact GGLiePartner.unique hcent hdN (hΘR a) hθΦ (hpart a)
      (GGLiePartner.of_mem (⟨(a : X), hAG a.2⟩ : ↥G₀))
  obtain ⟨K, hKfield, hKfin, σ, κ, hKcard, hσ, eF, heF⟩ :=
    exists_twE6_model_of_theta hf hθinj hθrange
  letI : Field K := hKfield
  letI : Finite K := hKfin
  let k : Type := ↥(CFSG.LieType.Chevalley.fixSubfield σ)
  letI : Field k := (CFSG.LieType.Chevalley.fixSubfield σ).toField
  letI : Algebra k K := (CFSG.LieType.Chevalley.fixSubfield σ).toAlgebra
  obtain ⟨x₀, hdata⟩ := rckExcCaseV_model_data_core hcore hVcfg hKcard hσ eF
  dsimp only at hdata
  obtain ⟨hk, hxD, hx0A0, hxord0, hWeq, hxcomp, hLf, c, Q, m, hQord, hQm1, hcx, hLimage, -, -⟩ :=
    hdata
  unfold RCKCompCore at hcore
  obtain ⟨-, -, -, -, hAel, -, hDB1, hDcard, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hDnotc, -,
    -⟩ := hcore
  have hDA : D ≤ A := hBA ▸ hDB1
  have hx1 : (x₀ : X) ≠ 1 := by
    intro h1
    have h1' : x₀ = 1 := Subtype.ext h1
    rw [h1', orderOf_one] at hxord0
    omega
  have hDex : ∃ d, d ∈ D ∧ d ∉ Subgroup.centralizer (L : Set X) := by
    by_contra hcon
    apply hDnotc
    intro d hd
    by_contra hdc
    exact hcon ⟨d, hd, hdc⟩
  obtain ⟨d, hdD, hdC⟩ := hDex
  have hxinf : (x₀ : X) ∈ A ⊓ Subgroup.centralizer (L : Set X) := by
    rw [hWeq]
    exact Subgroup.mem_zpowers _
  have hzxC : Subgroup.zpowers (x₀ : X) ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hxinf).2
  have hdx : d ∉ Subgroup.zpowers (x₀ : X) := fun hd => hdC (hzxC hd)
  have hDelem : IsElemAbelian 3 D := hAel.mono hDA
  have hsup : D = Subgroup.zpowers (x₀ : X) ⊔ Subgroup.zpowers d :=
    CFSG.StandardType.eq_sup_zpowers_of_card Nat.prime_three hDelem hDcard hxD hx1 hdD hdx
  have hdG0 : d ∈ G₀ := hAG (hDA hdD)
  let d₀ : ↥G₀ := ⟨d, hdG0⟩
  have hd3 : d₀ ^ 3 = 1 := Subtype.ext (by simpa using hAel.2 d (hDA hdD))
  have hdx0 : d₀ * x₀ = x₀ * d₀ := Subtype.ext (hAel.comm (hDA hdD) (hDA hxD))
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hKcard
  let ι₀ : ↥G₀ →* ModGL TwistTag.E6.tag K := (twistedE6RootGroup K σ).subtype.comp eF.toMonoidHom
  let ι : ↥G₀ →* ModGL TwistTag.E6.tag K :=
    (MulAut.conj (c : ModGL TwistTag.E6.tag K)).toMonoidHom.comp ι₀
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective.comp eF.injective
  have hι : Function.Injective ι := (MulAut.conj (c : ModGL TwistTag.E6.tag K)).injective.comp hι₀
  have hroot : ∀ g, ι g ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    intro g
    have h1 : ((twistedE6InndiagConj K σ c (eF g) : twistedE6RootGroup K σ) :
        ModGL TwistTag.E6.tag K) = ι g := by
      exact twistedE6InndiagConj_apply c (eF g)
    rw [← h1]
    exact (twistedE6InndiagConj K σ c (eF g)).2
  have hx₀ : ι x₀ = (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (Q ^ m) := by
    have h1 : ι x₀ = (c : ModGL TwistTag.E6.tag K) * ι₀ x₀ * (c : ModGL TwistTag.E6.tag K)⁻¹ :=
      rfl
    rw [h1]
    exact hcx
  have hρinj : Function.Injective
      ((thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K))) :=
    injective_thetaSL2_comp_map hK2 (algebraMap k K)
  have hm3 : orderOf (Q ^ m) = 3 := by
    rw [← orderOf_injective _ hρinj (Q ^ m), ← hcx]
    have h1 : orderOf ((c : ModGL TwistTag.E6.tag K) * ι₀ x₀ * (c : ModGL TwistTag.E6.tag K)⁻¹) =
        orderOf (ι₀ x₀) := by
      exact (MulAut.conj (c : ModGL TwistTag.E6.tag K)).orderOf_eq (ι₀ x₀)
    rw [h1, orderOf_injective ι₀ hι₀ x₀, hxord0]
  have hL : su6Levi σ.toRingHom ≤ ι.range := by
    rw [← hLimage]
    exact Subgroup.map_le_range _ _
  obtain ⟨E, hEel, hx₀E, hd₀E, hEcard⟩ :=
    exists_big_elemAbelian_of_model (f := f) (k := k) (K := K) hf hk hKcard
      (σ := σ.toRingHom) hσ h3 h9 hQord hm3 ι hι hroot hx₀ hd3 hdx0 hL
  have hDE : ∀ a : X, a ∈ D → ∃ h : a ∈ G₀, (⟨a, h⟩ : ↥G₀) ∈ E := by
    intro a ha
    have hE' : D ≤ E.map G₀.subtype := by
      rw [hsup]
      exact sup_le (Subgroup.zpowers_le.2 ⟨x₀, hx₀E, rfl⟩)
        (Subgroup.zpowers_le.2 ⟨d₀, hd₀E, rfl⟩)
    obtain ⟨e, he, hea⟩ := Subgroup.mem_map.1 (hE' ha)
    have hmem : a ∈ G₀ := hAG (hDA ha)
    refine ⟨hmem, ?_⟩
    have he' : e = ⟨a, hmem⟩ := Subtype.ext hea
    rw [← he']
    exact he
  let Eθ : Subgroup (ModGL (langTag .twistedE6) GGL) := E.map θ
  have hEθcard : 3 ^ 5 ≤ Nat.card Eθ := by
    rw [Subgroup.card_map_of_injective hθinj]
    exact hEcard
  have hEθel : IsElemAbelian 3 Eθ := hEel.map θ
  have hEθR : Eθ ≤ ggFixGp .twistedE6 f := by
    intro y hy
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.1 hy
    have hmem : θ e ∈ θ.range := MonoidHom.mem_range.2 ⟨e, rfl⟩
    rw [hθrange] at hmem
    exact Subgroup.commutator_le_self (ggFixGp .twistedE6 f) hmem
  have hXt : NoOffTwE6Three.IsToralE6 GGL Eθ :=
    ExcFramesHalf.bigElemAbelianToralBar_E6_three (ZMod 2) (by rw [Nat.card_zmod]; norm_num) Eθ
      (fun y hy => (Subgroup.mem_inf.1 (hEθR hy)).1)
      (fun y hy z hz => congrArg Subtype.val (hEθel.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)) hEθel.2
      (by
        have h5 : (3 : ℕ) ^ (Tag.E6.rank - 1) = 3 ^ 5 := rfl
        rw [h5]
        exact hEθcard)
  refine ⟨Eθ, ?_, twE6LawPos_three_of_toral hf h3 hEθR hEθel
    (le_trans (by norm_num) hEθcard) hXt⟩
  intro a ha
  obtain ⟨hmem, hE⟩ := hDE (a : X) ha
  rw [hΘθ a]
  exact Subgroup.mem_map_of_mem θ hE

end CFSG.StandardType.LieKnownR2.ExcPos
