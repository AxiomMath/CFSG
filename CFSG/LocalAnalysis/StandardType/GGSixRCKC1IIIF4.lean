module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA
import CFSG.LocalAnalysis.StandardType.GGPsiInnerDiagOfMarking
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientActionPart2
import CFSG.LocalAnalysis.StandardType.GGSixA6F4ClsThree
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCyclicKernel
import CFSG.LocalAnalysis.StandardType.GGRootDetectCore
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureExcF4
import CFSG.LocalAnalysis.RankThreeUC.Assembly

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.RCKRP
open CFSG.StandardType.F4ExplicitPos.AmbientAction
open CFSG.StandardType.A6Red

section Certificates


theorem rckF4_p_eq_three_of_injective
    {H : Type} [Group H] [Finite H]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hHp : IsPGroup p H) (hcard : p ^ 4 ≤ Nat.card H)
    (β : H →* ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 1)))
    (hβ : Function.Injective β) : p = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
  have hk4 : 4 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  have hp4H : p ^ 4 ∣ Nat.card H := by
    rw [hk]
    exact Nat.pow_dvd_pow p hk4
  have hβcard : Nat.card H = Nat.card β.range :=
    Nat.card_congr (Equiv.ofInjective β hβ)
  have hdvdU : Nat.card H ∣
      Nat.card ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 1)) := by
    rw [hβcard]
    exact Subgroup.card_subgroup_dvd_card β.range
  have hcardU : Nat.card ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4
      (GaloisField 2 1)) = CFSG.Open.ordF4 2 := by
    have hF2card : Nat.card (GaloisField 2 1) = 2 := by
      rw [GaloisField.card 2 1 (by norm_num)]
      norm_num
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hF2card]
  have hp4U : p ^ 4 ∣ CFSG.Open.ordF4 2 := by
    rw [← hcardU]
    exact hp4H.trans hdvdU
  by_cases hp3 : p = 3
  · exact hp3
  · exfalso
    have hpge3 : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    have hpge4 : 4 ≤ p := lt_of_le_of_ne hpge3 (Ne.symm hp3)
    have hpne4 : p ≠ 4 := by
      intro h
      subst p
      norm_num at hp
    have h5 : 5 ≤ p := lt_of_le_of_ne hpge4 (Ne.symm hpne4)
    have hp3dvd : p ^ 3 ∣ CFSG.Open.ordF4 2 :=
      (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 4)).trans hp4U
    exact CFSG.LocalAnalysis.RankThreeUC.not_pow_three_dvd_ordF4_two hp h5 hp3dvd


theorem rckF4_component_mulEquiv_statedSp
    {X : Type} [Group X] [Finite X] (n : ℕ) (ψ : (ggU .F4 n 1).K →* X)
    (p : ℕ) (G₀ A B₁ D J L K : Subgroup X) (e : X)
    (hcfg : RCKRP.RCKCompConfig .F4 n 1 ψ p G₀ A B₁ D J L K e) :
    Nonempty (↥K ≃* ↥(CFSG.Open.StatedSp 3 (GaloisField 2 1))) := by
  obtain ⟨hpres, hOddCent, hp, hp2, hA, hB1A, hDB1, hDcard, hAnormG0, hMarkG,
    hB1normJ, hB1cap, hB1card, hApow, hAcap, hAcapBot, hB1normL, hMarkL, hJcompD,
    hOddCenJ, hLG0, hExists, hNotCent, hCompL, hNoA6, heD, hene, hKcomp, hJK,
    hOddK⟩ := hcfg
  have hpres' := hpres
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, hperfG, hmodel⟩ := hpres'
  let F₂ := GaloisField 2 1
  let ψA : ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 F₂) →* X := ψ
  have hF2card : Nat.card F₂ = 2 := by
    dsimp [F₂]
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hrangeA : ψA.range = G₀ := by
    change ψ.range = G₀
    exact hrange
  have hkerA : ψA.ker ≤ Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 F₂) := by
    change ψ.ker ≤ Subgroup.center (ggU .F4 n 1).K
    exact hker
  have hcenterU : Subgroup.center (ggU .F4 n 1).K = ⊥ := by
    change Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 F₂) = ⊥
    exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hdiagA : ∀ a ∈ A, GGPsiInnerDiag (ggU .F4 n 1).D ψ a :=
    ggPsiInnerDiag_of_marking hpres hMarkG hAnormG0
  have hdiagA' : ∀ a ∈ A,
      GGPsiInnerDiag (CFSG.LieType.Steinberg.Adjoint.f4Datum F₂) ψA a := by
    intro a ha
    change GGPsiInnerDiag (ggU .F4 n 1).D ψ a
    exact hdiagA a ha
  have hinnerB1 : ∀ b ∈ B₁, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X) := by
    intro b hb
    exact f4_hinner (K := F₂) (ψ := ψA) hrangeA hkerA
      (fun b hb => hdiagA' b (hB1A hb)) b hb
  have hB1N : B₁ ≤ Subgroup.normalizer (G₀ : Set X) := hB1A.trans hAnormG0
  let β : ↥B₁ →* ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 F₂) :=
    betaF4 ψA G₀ B₁ hrangeA hkerA hcenterU hB1N hinnerB1
  have hβker : β.ker = (Subgroup.centralizer (G₀ : Set X)).subgroupOf B₁ :=
    betaF4_ker ψA G₀ B₁ hrangeA hkerA hcenterU hB1N hinnerB1
  have hβkerbot : β.ker = ⊥ := by
    rw [hβker, Subgroup.subgroupOf_eq_bot]
    exact ((disjoint_iff.mpr hAcapBot).mono_left hB1A).symm
  have hβinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).mp hβkerbot
  have : Fact p.Prime := ⟨hp⟩
  have hB1p : IsPGroup p ↥B₁ :=
    (CFSG.Open.IsElemAbelian.isPGroup hA).to_le hB1A
  have hp3 : p = 3 :=
    rckF4_p_eq_three_of_injective p hp hp2 hB1p hB1card β hβinj
  let e0 : (ggU .F4 n 1).K ≃* ↥G₀ :=
    eF4 ψA G₀ hrangeA hkerA hcenterU
  let zA : ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 F₂) :=
    β ⟨e, hDB1 heD⟩
  let z : (ggU .F4 n 1).K := (zA : (ggU .F4 n 1).K)
  let x : ↥G₀ := e0 z
  have hepow : e ^ p = 1 := hA.2 e (hB1A (hDB1 heD))
  have heord : orderOf e = 3 := by
    rw [hp3] at hepow
    exact orderOf_eq_prime hepow hene
  have hzord : orderOf z = 3 := by
    change orderOf zA = 3
    rw [show zA = β (⟨e, hDB1 heD⟩ : ↥B₁) from rfl]
    rw [orderOf_injective β hβinj]
    rw [← Subgroup.orderOf_coe (⟨e, hDB1 heD⟩ : ↥B₁)]
    exact heord
  have hxord : orderOf x = 3 := by
    dsimp [x]
    rw [MulEquiv.orderOf_eq]
    exact hzord
  have hxψ : (x : X) = ψA zA := by
    dsimp [x, e0, eF4]
    exact psiEquiv_apply ψA G₀ hrangeA hkerA hcenterU zA
  have hact : ∀ u : ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 F₂),
      (e : X) * ψA u * (e : X)⁻¹ = (x : X) * ψA u * (x : X)⁻¹ := by
    intro u
    have h := psi_betaF4_action ψA G₀ B₁ hrangeA hkerA hcenterU hB1N hinnerB1
      (⟨e, hDB1 heD⟩ : ↥B₁) u
    have h' : ψA (zA * u * zA⁻¹) = (e : X) * ψA u * (e : X)⁻¹ := h
    calc (e : X) * ψA u * (e : X)⁻¹
        = ψA (zA * u * zA⁻¹) := h'.symm
      _ = ψA zA * ψA u * (ψA zA)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = (x : X) * ψA u * (x : X)⁻¹ := by rw [hxψ]
  have hcent_eq : (Subgroup.centralizer ({e} : Set X)).subgroupOf G₀ =
      (Subgroup.centralizer ({(x : X)} : Set X)).subgroupOf G₀ := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    have hψy : ψA (e0.symm y : ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 F₂)) =
        (y : X) := by
      have h := psiEquiv_apply ψA G₀ hrangeA hkerA hcenterU (e0.symm y)
      change ((e0 (e0.symm y) : G₀) : X) =
        ψA (e0.symm y : ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 F₂)) at h
      rw [MulEquiv.apply_symm_apply] at h
      exact h.symm
    have ha := hact (e0.symm y : ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 F₂))
    rw [hψy] at ha
    constructor
    · intro hy
      have heq : (e : X) * (y : X) * (e : X)⁻¹ = (y : X) := by
        rw [← hy]
        group
      rw [heq] at ha
      calc (y : X) * (x : X)
          = ((x : X) * (y : X) * (x : X)⁻¹) * (x : X) := by
            conv_lhs => rw [ha]
        _ = (x : X) * (y : X) := by group
    · intro hy
      have hgx : (x : X) * (y : X) * (x : X)⁻¹ = (y : X) := by
        calc (x : X) * (y : X) * (x : X)⁻¹
            = ((y : X) * (x : X)) * (x : X)⁻¹ := by rw [← hy]
          _ = (y : X) := by group
      rw [hgx] at ha
      have heq : (e : X) * (y : X) = (y : X) * (e : X) := by
        calc (e : X) * (y : X)
            = ((e : X) * (y : X) * (e : X)⁻¹) * (e : X) := by group
          _ = (y : X) * (e : X) := by rw [ha]
      exact heq.symm
  have hKleG0 : K ≤ G₀ := hKcomp.1.trans inf_le_left
  have hKGcompH : CFSG.Assembly.IsComponentOf (K.subgroupOf G₀) ((G₀ ⊓
      Subgroup.centralizer ({e} : Set X)).subgroupOf G₀) :=
    ggIsComponentOf_subgroupOf hKcomp inf_le_left
  have hKGcomp : CFSG.Assembly.IsComponentOf (K.subgroupOf G₀)
      (Subgroup.centralizer ({x} : Set ↥G₀)) := by
    have h := hKGcompH
    rw [Subgroup.inf_subgroupOf_left, hcent_eq,
      CFSG.GroupTheory.centralizer_subgroupOf_singleton x.2] at h
    exact h
  obtain ⟨eC3⟩ :=
    CFSG.StandardType.A6Red.ggA6F4_three (K := F₂) hF2card (G := ↥G₀)
      (e := e0.symm) x hxord (K.subgroupOf G₀) hKGcomp
  let eSp : ↥(K.subgroupOf G₀) ≃* ↥(CFSG.Open.StatedSp 3 F₂) :=
    eC3.trans (CFSG.SeitzReduction.F4Pilot.c3LeviEquiv F₂).symm
  exact ⟨(Subgroup.subgroupOfEquivOfLe hKleG0).symm.trans eSp⟩


theorem rckF4_exists_native_PSp_three
    {X : Type} [Group X] [Finite X] (n : ℕ) (ψ : (ggU .F4 n 1).K →* X)
    (p : ℕ) (G₀ A B₁ D J L K : Subgroup X) (e : X)
    (hcfg : RCKRP.RCKCompConfig .F4 n 1 ψ p G₀ A B₁ D J L K e) :
    ∃ φ : (ggU .PSp 3 1).K →* X, φ.range = K ∧
      φ.ker ≤ Subgroup.center (ggU .PSp 3 1).K ∧
      ∀ b ∈ B₁, GGPsiInnerDiag (ggU .PSp 3 1).D φ b := by
  obtain ⟨η⟩ := rckF4_component_mulEquiv_statedSp n ψ p G₀ A B₁ D J L K e hcfg
  obtain ⟨-, -, hp, hp2, hA, hB1A, hDB1, hDcard, hAnormG0, -, hB1normJ, -, -, -,
    -, -, -, -, hJcompD, -, -, -, -, -, -, heD, hene, hKcomp, hJK, -⟩ := hcfg
  have hB1K : B₁ ≤ Subgroup.normalizer (K : Set X) :=
    (le_normalizer_and_exists_isComponentOf_of_plane hp hA hB1A hDB1 hDcard hAnormG0
      hB1normJ hJcompD heD hene hKcomp hJK).1
  let F₂ := GaloisField 2 1
  have hF2card : Nat.card F₂ = 2 := by
    dsimp [F₂]
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  have hSCM : CFSG.Open.StatedClassicalModel (↥(CFSG.Open.StatedSp 3 F₂)) .PSp 3 2 1 := by
    refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by norm_num⟩, ?_⟩
    refine ⟨F₂, inferInstance, inferInstance, ?_,
      ⟨CFSG.SeitzReduction.F4Pilot.spProjEquiv 3 F₂⟩⟩
    simpa using hF2card
  have hLMsp : CFSG.Blueprint.LieModel (↥(CFSG.Open.StatedSp 3 F₂)) .PSp 3 2 1 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hSCM⟩
  have hLMK : CFSG.Blueprint.LieModel ↥K .PSp 3 2 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv η.symm hLMsp
  let eKsp : (ggU .PSp 3 1).K ≃* ↥K := η.symm
  let φ : (ggU .PSp 3 1).K →* X := K.subtype.comp eKsp.toMonoidHom
  have hφrange : φ.range = K := by
    dsimp [φ]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eKsp.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  have hφker : φ.ker ≤ Subgroup.center (ggU .PSp 3 1).K := by
    dsimp [φ]
    change (K.subtype.comp eKsp.toMonoidHom).ker ≤ Subgroup.center (ggU .PSp 3 1).K
    rw [MonoidHom.ker_comp_of_injective eKsp.toMonoidHom K.subtype K.subtype_injective]
    rw [show eKsp.toMonoidHom.ker = (⊥ : Subgroup (ggU .PSp 3 1).K) from
      (MonoidHom.ker_eq_bot_iff eKsp.toMonoidHom).mpr eKsp.injective]
    exact bot_le
  refine ⟨φ, hφrange, hφker, ?_⟩
  intro b hb
  let α : MulAut ↥K := K.normalizerMonoidHom ⟨b, hB1K hb⟩
  obtain ⟨u, hu⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.exists_eq_conj_of_lieModel hLMK α
  have hbconj : ∀ x : ↥K,
      (b : X) * (x : X) * (b : X)⁻¹ = (u : X) * (x : X) * (u : X)⁻¹ := by
    intro x
    have hα : ((α x : ↥K) : X) = (b : X) * (x : X) * (b : X)⁻¹ := by
      dsimp [α]
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have h := congrArg (fun φ : MulAut ↥K => ((φ x : ↥K) : X)) hu
    rw [hα] at h
    simpa [MulAut.conj_apply] using h
  have hcentral : (b : X) * (u : X)⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxH : (u : X)⁻¹ * x * (u : X) ∈ K :=
      Subgroup.mul_mem K (Subgroup.mul_mem K (Subgroup.inv_mem K u.2) hx) u.2
    have hh := hbconj ⟨(u : X)⁻¹ * x * (u : X), hxH⟩
    have hconj : ((b : X) * (u : X)⁻¹) * x * ((b : X) * (u : X)⁻¹)⁻¹ = x := by
      calc ((b : X) * (u : X)⁻¹) * x * ((b : X) * (u : X)⁻¹)⁻¹
          = (b : X) * ((u : X)⁻¹ * x * (u : X)) * (b : X)⁻¹ := by group
        _ = (u : X) * ((u : X)⁻¹ * x * (u : X)) * (u : X)⁻¹ := hh
        _ = x := by group
    calc x * ((b : X) * (u : X)⁻¹)
        = (((b : X) * (u : X)⁻¹) * x * ((b : X) * (u : X)⁻¹)⁻¹) *
            ((b : X) * (u : X)⁻¹) := by rw [hconj]
      _ = ((b : X) * (u : X)⁻¹) * x := by group
  let a : (ggU .PSp 3 1).K := eKsp.symm (u⁻¹)
  refine CFSG.StandardType.RootDetect.ggPsiInnerDiag_of_centralizes (ggU .PSp 3 1).D
    (ψ := φ) (c := b) (a := a) ?_
  intro y
  have hφa : φ a = ((u⁻¹ : ↥K) : X) := by
    dsimp [φ, a]
    rw [eKsp.apply_symm_apply]
    rfl
  have hyK : φ y ∈ K := by
    rw [← hφrange]
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  rw [hφa]
  have hc := (Subgroup.mem_centralizer_iff.mp hcentral) (φ y) hyK
  calc (((b : X) * (u : X)⁻¹)⁻¹) * φ y * ((b : X) * (u : X)⁻¹)
      = ((b : X) * (u : X)⁻¹)⁻¹ * (φ y * ((b : X) * (u : X)⁻¹)) := by group
    _ = ((b : X) * (u : X)⁻¹)⁻¹ * (((b : X) * (u : X)⁻¹) * φ y) := by rw [hc]
    _ = φ y := by group


end Certificates

end CFSG.StandardType.RCKC1
