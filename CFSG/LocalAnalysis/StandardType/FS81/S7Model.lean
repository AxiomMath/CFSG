module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoExcStep
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBFull
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct
public import CFSG.LocalAnalysis.StandardType.GGExcFrameLang
public import CFSG.LocalAnalysis.StandardType.FS81.S7ModelHirr

import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R16ExcLabel
import CFSG.CGT.PushingUpLit.SolK.Basics
import CFSG.LieType.Chevalley.E6GraphInvolutionForms
import CFSG.LieType.Chevalley.E6GraphRootSL2Basic
import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
import CFSG.LieType.Steinberg.CentralExt.FieldTwoMultiplier
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.CGT.PushingUpLit.BHS.Offender
import CFSG.CGT.PushingUpLit.SolK.ModData

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction

section Transport

variable {M G : Type} [Group M] [Group G] (ι : M →* G)

theorem centralizer_singleton_inf_range_eq_map (hι : Function.Injective ι) (x : M) :
    Subgroup.centralizer ({ι x} : Set G) ⊓ ι.range =
      (Subgroup.centralizer ({x} : Set M)).map ι := by
  ext y
  constructor
  · rintro ⟨hy, m, rfl⟩
    refine ⟨m, Subgroup.mem_centralizer_iff.2 fun h hh => ?_, rfl⟩
    rw [Set.mem_singleton_iff.1 hh]
    exact hι (by simpa only [map_mul] using
      Subgroup.mem_centralizer_iff.1 hy (ι x) (Set.mem_singleton _))
  · rintro ⟨m, hm, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.2 fun h hh => ?_, m, rfl⟩
    rw [Set.mem_singleton_iff.1 hh]
    simpa only [map_mul] using
      congrArg ι (Subgroup.mem_centralizer_iff.1 hm x (Set.mem_singleton _))

theorem centralizer_range_inf_range_eq_map_center (hι : Function.Injective ι) :
    Subgroup.centralizer (ι.range : Set G) ⊓ ι.range = (Subgroup.center M).map ι := by
  ext y
  constructor
  · rintro ⟨hy, m, rfl⟩
    refine ⟨m, Subgroup.mem_center_iff.2 fun n => ?_, rfl⟩
    exact hι (by simpa only [map_mul] using
      Subgroup.mem_centralizer_iff.1 hy (ι n) ⟨n, rfl⟩)
  · rintro ⟨m, hm, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.2 ?_, m, rfl⟩
    rintro _ ⟨n, rfl⟩
    simpa only [map_mul] using congrArg ι (Subgroup.mem_center_iff.1 hm n)

theorem isPGroup_map_iff (hι : Function.Injective ι) (p : ℕ) (P : Subgroup M) :
    IsPGroup p (P.map ι) ↔ IsPGroup p P := by
  constructor
  · intro h x
    obtain ⟨k, hk⟩ := h ⟨ι x, x, x.2, rfl⟩
    refine ⟨k, Subtype.ext (hι ?_)⟩
    have := congrArg Subtype.val hk
    simpa [map_pow] using this
  · intro h x
    obtain ⟨y, hy, hyx⟩ := x.2
    obtain ⟨k, hk⟩ := h ⟨y, hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥P => ι z.1) hk
    simpa [map_pow, hyx] using this

theorem hUmax_map (hι : Function.Injective ι) {C Q : Subgroup M}
    (h : ∀ P : Subgroup M, IsPGroup 2 P → P ≤ C → C ≤ Subgroup.normalizer (P : Set M) → P ≤ Q) :
    ∀ P : Subgroup G, IsPGroup 2 P → P ≤ C.map ι →
      C.map ι ≤ Subgroup.normalizer (P : Set G) → P ≤ Q.map ι := by
  intro P hP hPC hN
  have hPr : P ≤ ι.range := hPC.trans (Subgroup.map_le_range ι C)
  have hPP : (P.comap ι).map ι = P := Subgroup.map_comap_eq_self hPr
  have hP₀ : IsPGroup 2 (P.comap ι) := by
    rw [← isPGroup_map_iff ι hι, hPP]
    exact hP
  have hC₀ : P.comap ι ≤ C := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hPC hx
    rwa [← hι hyx]
  have hN₀ : C ≤ Subgroup.normalizer ((P.comap ι : Subgroup M) : Set M) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have := Subgroup.mem_normalizer_iff.1 (hN ⟨c, hc, rfl⟩) (ι n)
    simpa [Subgroup.mem_comap, map_mul, map_inv] using this
  calc P = (P.comap ι).map ι := hPP.symm
    _ ≤ Q.map ι := Subgroup.map_mono (h _ hP₀ hC₀ hN₀)

theorem hirr_map (hι : Function.Injective ι) {t : M} {D Q : Subgroup M} {L : Subgroup G}
    (h : ∀ V : Subgroup M, Subgroup.zpowers t ≤ V → V ≤ Q →
      D ≤ Subgroup.normalizer (V : Set M) → V = Subgroup.zpowers t ∨ V = Q)
    (hL : D.map ι ≤ L) :
    ∀ V : Subgroup G, Subgroup.zpowers (ι t) ≤ V → V ≤ Q.map ι →
      L ≤ Subgroup.normalizer (V : Set G) → V = Subgroup.zpowers (ι t) ∨ V = Q.map ι := by
  intro V hV1 hV2 hN
  have hVr : V ≤ ι.range := hV2.trans (Subgroup.map_le_range ι Q)
  have hVV : (V.comap ι).map ι = V := Subgroup.map_comap_eq_self hVr
  have h1 : Subgroup.zpowers t ≤ V.comap ι := by
    rw [Subgroup.zpowers_le]
    exact hV1 (Subgroup.mem_zpowers (ι t))
  have h2 : V.comap ι ≤ Q := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hV2 hx
    rwa [← hι hyx]
  have h3 : D ≤ Subgroup.normalizer ((V.comap ι : Subgroup M) : Set M) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have := Subgroup.mem_normalizer_iff.1 (hN (hL ⟨d, hd, rfl⟩)) (ι n)
    simpa [Subgroup.mem_comap, map_mul, map_inv] using this
  rcases h _ h1 h2 h3 with h4 | h4
  · left
    rw [← hVV, h4, MonoidHom.map_zpowers]
  · right
    rw [← hVV, h4]

theorem isSylow2In_map (hι : Function.Injective ι) (S : Sylow 2 M) :
    IsSylow2In ((S : Subgroup M).map ι) ι.range := by
  refine ⟨Subgroup.map_le_range ι _, (isPGroup_map_iff ι hι 2 _).2 S.isPGroup', ?_⟩
  intro T hT hTp hST
  have hTT : (T.comap ι).map ι = T := Subgroup.map_comap_eq_self hT
  have hT₀ : IsPGroup 2 (T.comap ι) := by
    rw [← isPGroup_map_iff ι hι, hTT]
    exact hTp
  have hS₀ : (S : Subgroup M) ≤ T.comap ι := by
    intro x hx
    exact hST ⟨x, hx, rfl⟩
  rw [← hTT, S.is_maximal' hT₀ hS₀]

end Transport

section M0Iso

theorem exists_mulEquiv_adjointGroup_E8_of_isEm {G : Type} [Group G] [Finite G]
    {Y : Subgroup G} (hY : IsEm 8 Y) (hZ : Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥) :
    Nonempty (↥Y ≃* adjointGroup .E8 (GaloisField 2 1)) := by
  have hZ' : Subgroup.center ↥Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzG : (z : G) ∈ Subgroup.centralizer (Y : Set G) ⊓ Y :=
      ⟨Subgroup.mem_centralizer_iff.2 fun y hy => by
        have := Subgroup.mem_center_iff.1 hz ⟨y, hy⟩
        exact congrArg Subtype.val this, z.2⟩
    rw [hZ] at hzG
    exact Subtype.ext (Subgroup.mem_bot.1 hzG)
  obtain ⟨⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_glaLabel hY
  dsimp only at hmt hn
  subst hn
  have ht : t = .E8 := by rcases hmt with ⟨h, -⟩ | ⟨-, h⟩ <;> [omega; exact h]
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.exists_mulEquiv_adjointGroup_of_isLabel_E8
    (lab := ⟨t, r, 1⟩) hlab ht hZ'

end M0Iso

section M0Center

theorem centralizer_inf_eq_bot_of_isEm_eight {G : Type} [Group G] [Finite G]
    {Y : Subgroup G} (hY : IsEm 8 Y) : Subgroup.centralizer (Y : Set G) ⊓ Y = ⊥ := by
  obtain ⟨⟨t, r, n⟩, ⟨hmt, -, hn⟩, hlab⟩ := exists_glaLabel hY
  dsimp only at hmt hn
  subst hn
  have ht : t = .E8 := by rcases hmt with ⟨h, -⟩ | ⟨-, h⟩ <;> [omega; exact h]
  have hK : CFSG.LocalAnalysis.GLTheoremA.Rk2IsLabel ↥Y (⟨t, r, 1⟩ : GLALabel) := hlab
  obtain ⟨hQ, -, hM⟩ := CFSG.LocalAnalysis.GLTheoremA.quasisimple_markedModel_of_isLabel hK
  have hL : LieModel (↥Y ⧸ Subgroup.center ↥Y) .E8 0 2 1 :=
    CFSG.LocalAnalysis.GLTheoremA.lieModel_of_markedModel_E8 ht hM
  have hCEM : ChevalleyExceptionalModel (↥Y ⧸ Subgroup.center ↥Y) .E8 2 1 :=
    hL.chevalleyExceptionalModel (by decide)
  obtain ⟨F, hF, hFin, hcard, ⟨iso⟩⟩ := hCEM.2
  let : Field F := hF
  let : Finite F := hFin
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two le_rfl (by rw [pow_one]; exact hF2)
  have hZ : Subgroup.center ↥Y = ⊥ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_eq_bot_of_hopf_subsingleton hQ iso
      (CFSG.LieType.Steinberg.CentralExt.FieldTwo.e8_two_hopfMultiplier hF2).2
  rw [eq_bot_iff]
  intro g hg
  have hgc : (⟨g, hg.2⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 hg.1 y y.2
  rw [hZ, Subgroup.mem_bot] at hgc
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hgc)

theorem exists_injective_hom_range_eq_of_isEm_eight {G : Type} [Group G] [Finite G]
    {Y : Subgroup G} (hY : IsEm 8 Y) :
    ∃ ι : adjointGroup .E8 (GaloisField 2 1) →* G, Function.Injective ι ∧ ι.range = Y := by
  obtain ⟨e⟩ := exists_mulEquiv_adjointGroup_E8_of_isEm hY (centralizer_inf_eq_bot_of_isEm_eight hY)
  refine ⟨Y.subtype.comp e.symm.toMonoidHom, Subtype.val_injective.comp e.symm.injective, ?_⟩
  ext g
  constructor
  · rintro ⟨m, rfl⟩
    exact (e.symm m).2
  · intro hg
    exact ⟨e ⟨g, hg⟩, by simp⟩

end M0Center

theorem natCard_galoisField_two_one : Nat.card (GaloisField 2 1) = 2 := by
  rw [GaloisField.card 2 1 one_ne_zero, pow_one]

section RootThreeDef

@[expose] noncomputable def rootThree (τ : Tag) (K : Type) [Field K] (α : Fin τ.rank → ℤ) :
    adjointGroup τ K :=
  EPilot.pinnedElt τ α (1 : K) * EPilot.pinnedElt τ (-α) (1 : K)

end RootThreeDef

section SL2Facts

variable {K : Type} [Field K]

theorem uSL_one_mul_self_of_two (h2 : (2 : K) = 0) : (uSL 1 : SL2 K) * uSL 1 = 1 := by
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [uSL, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals linear_combination h2

theorem uSL_one_ne_one : (uSL 1 : SL2 K) ≠ 1 := fun h => by
  have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp [uSL] at this

theorem uSL_one_mul_vSL_one_ne_one : (uSL 1 * vSL 1 : SL2 K) ≠ 1 := fun h => by
  have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
  simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem uSL_mul_uSL_mul_vSL_mul_inv_of_two (h2 : (2 : K) = 0) :
    (uSL 1 : SL2 K) * (uSL 1 * vSL 1) * (uSL 1)⁻¹ = (uSL 1 * vSL 1)⁻¹ := by
  have hu := uSL_one_mul_self_of_two h2
  have hv := CFSG.LieType.Chevalley.E6GraphRootSL2.vSL_mul_self_of_two h2
  have hui : (uSL 1 : SL2 K)⁻¹ = uSL 1 := inv_eq_of_mul_eq_one_right hu
  have hvi : (vSL 1 : SL2 K)⁻¹ = vSL 1 := inv_eq_of_mul_eq_one_right hv
  rw [mul_inv_rev, hui, hvi]
  calc (uSL 1 : SL2 K) * (uSL 1 * vSL 1) * uSL 1 = (uSL 1 * uSL 1) * vSL 1 * uSL 1 := by
        simp only [mul_assoc]
    _ = vSL 1 * uSL 1 := by rw [hu, one_mul]

end SL2Facts

section M1

variable {τ : Tag} {K : Type} [Field K]

theorem orderOf_pinnedElt_one [CharP K 2] (α : Fin τ.rank → ℤ) :
    orderOf (EPilot.pinnedElt τ α (1 : K)) = 2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hx : ((EPilot.pinnedElt τ α (1 : K) : adjointGroup τ K) : ModGL τ K) =
      rootSL2 τ K α (uSL 1) :=
    (CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two h2 α 1).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [Subgroup.coe_pow, hx, ← map_pow, pow_two, uSL_one_mul_self_of_two h2, map_one]
    try rfl
  · intro h
    have h1 : rootSL2 τ K α (uSL 1) = rootSL2 τ K α 1 := by
      rw [map_one, ← hx, h]
      try rfl
    exact uSL_one_ne_one
      (CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_injective_of_two h2 α h1)

theorem coe_rootThree [CharP K 2] {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ((rootThree τ K α : adjointGroup τ K) : ModGL τ K) = rootSL2 τ K α (uSL 1 * vSL 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [map_mul, CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two h2,
    CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_vSL_of_two h2 hα]
  rfl

theorem orderOf_rootThree [CharP K 2] {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    orderOf (rootThree τ K α) = 3 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs := coe_rootThree (K := K) hα
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [Subgroup.coe_pow, hs, ← map_pow,
      CFSG.LieType.Chevalley.E6GraphRootSL2.uSL_mul_vSL_pow_three h2, map_one]
    try rfl
  · intro h
    have h1 : rootSL2 τ K α (uSL 1 * vSL 1) = rootSL2 τ K α 1 := by
      rw [map_one, ← hs, h]
      try rfl
    exact uSL_one_mul_vSL_one_ne_one
      (CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_injective_of_two h2 α h1)

theorem pinnedElt_mul_rootThree_mul_inv [CharP K 2] {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    EPilot.pinnedElt τ α (1 : K) * rootThree τ K α * (EPilot.pinnedElt τ α (1 : K))⁻¹ =
      (rootThree τ K α)⁻¹ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h := congrArg (rootSL2 τ K α) (uSL_mul_uSL_mul_vSL_mul_inv_of_two (K := K) h2)
  simp only [map_mul, map_inv] at h
  rw [CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two h2,
    CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_vSL_of_two h2 hα] at h
  exact Subtype.ext h

theorem exists_conj_rootThree_eq [CharP K 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) :
    ∃ g : adjointGroup τ K, g * rootThree τ K α * g⁻¹ = rootThree τ K β := by
  have key : ∀ (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∀ w : WeylGroup τ,
      (canonicalRep (coxeterSystem τ) K w : ModGL τ K) * pinnedX τ K γ 1 *
        (canonicalRep (coxeterSystem τ) K w : ModGL τ K)⁻¹ = pinnedX τ K (w • γ) 1 := by
    intro γ hγ w
    obtain ⟨ε, hε, h⟩ := CFSG.LieType.Chevalley.exists_canonicalRep_mul_pinnedX_mul_inv K w hγ
    have hε1 : ε = 1 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
      exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
    rw [h 1, hε1, one_mul]
  obtain ⟨w₁, hw₁⟩ := EPilot.exists_smul_highRoot_eq hτ hα
  obtain ⟨w₂, hw₂⟩ := EPilot.exists_smul_highRoot_eq hτ hβ
  have hw : (w₂ * w₁⁻¹) • α = β := by
    rw [← hw₁, ← hw₂, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  refine ⟨⟨canonicalRep (coxeterSystem τ) K (w₂ * w₁⁻¹),
    canonicalRep_mem_adjointGroup _ K _⟩, Subtype.ext ?_⟩
  have e1 := key α hα (w₂ * w₁⁻¹)
  have e2 := key (-α) (IsRoot.neg hα) (w₂ * w₁⁻¹)
  rw [hw] at e1
  rw [smul_neg, hw] at e2
  show (canonicalRep (coxeterSystem τ) K (w₂ * w₁⁻¹) : ModGL τ K) *
      (pinnedX τ K α 1 * pinnedX τ K (-α) 1) *
      (canonicalRep (coxeterSystem τ) K (w₂ * w₁⁻¹) : ModGL τ K)⁻¹ =
    pinnedX τ K β 1 * pinnedX τ K (-β) 1
  rw [← e1, ← e2]
  group

end M1

section Abstract

variable {G : Type} [Group G]

theorem eq_bot_of_isPGroup_of_normalized_of_eq_sup_zpowers [Finite G] {b : G} (hb : orderOf b = 3)
    {K C : Subgroup G} (hKb : K ≤ Subgroup.centralizer ({b} : Set G))
    (hC : C = Subgroup.zpowers b ⊔ K) (hK : IsSimpleGroup K) (hZ : Subgroup.center K = ⊥)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPC : P ≤ C)
    (hN : C ≤ Subgroup.normalizer (P : Set G)) : P = ⊥ := by
  have hbK : ∀ k ∈ K, b * k = k * b := fun k hk =>
    Subgroup.mem_centralizer_iff.1 (hKb hk) b (Set.mem_singleton b)
  have hbN : Subgroup.zpowers b ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    have hconj : ∀ k ∈ K, b * k * b⁻¹ = k := fun k hk => by rw [hbK k hk]; group
    refine ⟨fun hh => by rwa [hconj h hh], fun hh => ?_⟩
    have h3 : b * h * b⁻¹ = h := by
      have e := hconj _ hh
      calc b * h * b⁻¹ = b⁻¹ * (b * (b * h * b⁻¹) * b⁻¹) * b := by group
        _ = b⁻¹ * (b * h * b⁻¹) * b := by rw [e]
        _ = h := by group
    rwa [h3] at hh
  have hCN : C ≤ Subgroup.normalizer (K : Set G) := by
    rw [hC]; exact sup_le hbN Subgroup.le_normalizer
  have hKC : K ≤ C := by rw [hC]; exact le_sup_right
  have hdec : ∀ p ∈ P, ∃ i : ℤ, ∃ k ∈ K, p = b ^ i * k := by
    intro p hp
    have hp' : p ∈ ((Subgroup.zpowers b ⊔ K : Subgroup G) : Set G) := by
      rw [← hC]; exact hPC hp
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hbN] at hp'
    obtain ⟨x, hx, k, hk, rfl⟩ := hp'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ⟨i, k, hk, rfl⟩
  have hPK : P ⊓ K = ⊥ := by
    have hnorm : ((P ⊓ K).subgroupOf K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (n : G) ∈ P ⊓ K := Subgroup.mem_subgroupOf.1 hn
      refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, (g * n * g⁻¹).2⟩)
      have hg : (g : G) ∈ Subgroup.normalizer (P : Set G) := hN (hKC g.2)
      exact (Subgroup.mem_normalizer_iff.1 hg n).1 (Subgroup.mem_inf.1 hn').1
    rcases hK.eq_bot_or_eq_top_of_normal ((P ⊓ K).subgroupOf K) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : K) ∈ (P ⊓ K).subgroupOf K := Subgroup.mem_subgroupOf.2 hx
      rw [h, Subgroup.mem_bot] at this
      have h1 : x = 1 := congrArg Subtype.val this
      rw [h1]; exact Subgroup.one_mem _
    · exfalso
      have hKP : K ≤ P := fun x hx => by
        have hx' : (⟨x, hx⟩ : K) ∈ (P ⊓ K).subgroupOf K := by rw [h]; trivial
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx')).1
      have hKp : IsPGroup 2 K := hP.to_le hKP
      have hKnt : Nontrivial K := hK.toNontrivial
      have hcnt : Nontrivial (Subgroup.center K) := hKp.center_nontrivial
      rw [hZ] at hcnt
      exact (Subgroup.nontrivial_iff_ne_bot _).1 hcnt rfl
  have hcomm : ∀ p ∈ P, ∀ k ∈ K, p * k = k * p := by
    intro p hp k hk
    have hpC : p ∈ C := hPC hp
    have h1 : p * k * p⁻¹ * k⁻¹ ∈ K := by
      have : p * k * p⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hCN hpC) k).1 hk
      exact K.mul_mem this (K.inv_mem hk)
    have h2 : p * k * p⁻¹ * k⁻¹ ∈ P := by
      have : k * p⁻¹ * k⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.1 (hN (hKC hk)) p⁻¹).1 (P.inv_mem hp)
      have h3 := P.mul_mem hp this
      simpa only [mul_assoc] using h3
    have h4 : p * k * p⁻¹ * k⁻¹ = 1 := by
      have : p * k * p⁻¹ * k⁻¹ ∈ P ⊓ K := ⟨h2, h1⟩
      rw [hPK, Subgroup.mem_bot] at this
      exact this
    calc p * k = (p * k * p⁻¹ * k⁻¹) * (k * p) := by group
      _ = k * p := by rw [h4, one_mul]
  rw [eq_bot_iff]
  intro p hp
  obtain ⟨i, k, hk, rfl⟩ := hdec p hp
  have hkc : (⟨k, hk⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := z.2
    have e1 := hcomm _ hp z hz
    have e2 : b ^ i * (z : G) = z * b ^ i :=
      (Commute.zpow_left (hbK z hz : Commute b z) i).eq
    apply Subtype.ext
    show (z : G) * k = k * z
    have : b ^ i * (k * z) = b ^ i * (z * k) := by
      calc b ^ i * (k * z) = (b ^ i * k) * z := by rw [mul_assoc]
        _ = z * (b ^ i * k) := e1
        _ = (z * b ^ i) * k := by rw [mul_assoc]
        _ = (b ^ i * z) * k := by rw [e2]
        _ = b ^ i * (z * k) := by rw [mul_assoc]
    exact (mul_left_cancel this).symm
  have hk1 : k = 1 := by
    have : (⟨k, hk⟩ : K) ∈ (⊥ : Subgroup K) := by rw [← hZ]; exact hkc
    exact congrArg Subtype.val ((Subgroup.mem_bot).1 this)
  subst hk1
  rw [mul_one] at hp ⊢
  obtain ⟨n, hn⟩ := hP ⟨_, hp⟩
  have h2n : (b ^ i) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hb3 : b ^ 3 = 1 := by have := pow_orderOf_eq_one b; rwa [hb] at this
  have h3 : (b ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hd : orderOf (b ^ i) ∣ Nat.gcd 3 (2 ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2n)
  have hcop : Nat.gcd 3 (2 ^ n) = 1 := Nat.Coprime.pow_right n (by norm_num)
  rw [hcop] at hd
  have : b ^ i = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  rw [this]; exact Subgroup.one_mem _

theorem eq_of_le_sup_zpowers_of_card_eq [Finite G] {b : G} {K D : Subgroup G}
    (hKb : K ≤ Subgroup.centralizer ({b} : Set G)) (hD : D ≤ Subgroup.zpowers b ⊔ K)
    (hDperf : ⁅D, D⁆ = D) (hcard : Nat.card D = Nat.card K) : D = K := by
  have hbK : ∀ k ∈ K, Commute b k := fun k hk =>
    Subgroup.mem_centralizer_iff.1 (hKb hk) b (Set.mem_singleton b)
  have hbN : Subgroup.zpowers b ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    have hconj : ∀ k ∈ K, b * k * b⁻¹ = k := fun k hk => (hbK k hk).mul_inv_cancel
    refine ⟨fun hh => by rwa [hconj h hh], fun hh => ?_⟩
    have h3 : b * h * b⁻¹ = h := by
      have e := hconj _ hh
      calc b * h * b⁻¹ = b⁻¹ * (b * (b * h * b⁻¹) * b⁻¹) * b := by group
        _ = b⁻¹ * (b * h * b⁻¹) * b := by rw [e]
        _ = h := by group
    rwa [h3] at hh
  have hdec : ∀ x ∈ Subgroup.zpowers b ⊔ K, ∃ i : ℤ, ∃ k ∈ K, x = b ^ i * k := by
    intro x hx
    have hx' : x ∈ ((Subgroup.zpowers b ⊔ K : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hbN] at hx'
    obtain ⟨y, hy, k, hk, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨i, k, hk, rfl⟩
  have hcomm : ⁅D, D⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨i, k, hk, rfl⟩ := hdec x (hD hx)
    obtain ⟨j, k', hk', rfl⟩ := hdec y (hD hy)
    rw [commutatorElement_def]
    have huk : Commute (b ^ i) k := (hbK k hk).zpow_left i
    have huk' : Commute (b ^ i) k' := (hbK k' hk').zpow_left i
    have hvk : Commute (b ^ j) k := (hbK k hk).zpow_left j
    have hvk' : Commute (b ^ j) k' := (hbK k' hk').zpow_left j
    have huv : Commute (b ^ j) (b ^ i) := (Commute.refl b).zpow_zpow j i
    have h1 : Commute (b ^ j) (k' * k⁻¹ * (b ^ i)⁻¹ * k'⁻¹) :=
      ((hvk'.mul_right hvk.inv_right).mul_right huv.inv_right).mul_right hvk'.inv_right
    have h2 : Commute (b ^ i) (k * k' * k⁻¹) := (huk.mul_right huk').mul_right huk.inv_right
    have key : b ^ i * k * (b ^ j * k') * (b ^ i * k)⁻¹ * (b ^ j * k')⁻¹ =
        k * k' * k⁻¹ * k'⁻¹ := by
      calc b ^ i * k * (b ^ j * k') * (b ^ i * k)⁻¹ * (b ^ j * k')⁻¹
          = b ^ i * k * (b ^ j * (k' * k⁻¹ * (b ^ i)⁻¹ * k'⁻¹) * (b ^ j)⁻¹) := by group
        _ = b ^ i * k * (k' * k⁻¹ * (b ^ i)⁻¹ * k'⁻¹) := by rw [h1.mul_inv_cancel]
        _ = (b ^ i * (k * k' * k⁻¹) * (b ^ i)⁻¹) * k'⁻¹ := by group
        _ = (k * k' * k⁻¹) * k'⁻¹ := by rw [h2.mul_inv_cancel]
        _ = k * k' * k⁻¹ * k'⁻¹ := rfl
    rw [key]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')
  have hDK : D ≤ K := by rw [← hDperf]; exact hcomm
  have : Finite K := inferInstance
  exact Subgroup.eq_of_le_of_card_ge hDK (le_of_eq hcard.symm)

@[expose] def normalizerLines (H E : Subgroup G) (b : G) : Set (Subgroup G) :=
  {Z | ∃ g ∈ H ⊓ Subgroup.normalizer (E : Set G), Z = Subgroup.zpowers (g * b * g⁻¹)}

theorem mem_normalizer_inf_centralizer {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (Q : Set G), ∀ h ∈ Q ⊓ Subgroup.centralizer (Q : Set G),
      g * h * g⁻¹ ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    intro g hg h hh
    refine ⟨(Subgroup.mem_normalizer_iff.1 hg h).1 hh.1,
      Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) q).1 hq
      simpa using this
    have hc : g⁻¹ * q * g * h = h * (g⁻¹ * q * g) := Subgroup.mem_centralizer_iff.1 hh.2 _ hq'
    calc q * (g * h * g⁻¹) = g * (g⁻¹ * q * g * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
      _ = g * h * g⁻¹ * q := by group
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

end Abstract

section TransportLines

variable {M G : Type} [Group M] [Group G] (ι : M →* G)

theorem ncard_normalizerLines_map (hι : Function.Injective ι) (E : Subgroup M) (b : M) :
    (normalizerLines ι.range (E.map ι) (ι b)).ncard = (normalizerLines ⊤ E b).ncard := by
  have hnorm := Subgroup.comap_normalizer_eq_of_le_range (H := E.map ι) (f := ι)
    (Subgroup.map_le_range ι E)
  rw [Subgroup.comap_map_eq_self_of_injective hι] at hnorm
  have hmem : ∀ g : M, ι g ∈ Subgroup.normalizer ((E.map ι : Subgroup G) : Set G) ↔
      g ∈ Subgroup.normalizer (E : Set M) := fun g =>
    Iff.of_eq (congrArg (fun S : Subgroup M => g ∈ S) hnorm)
  have himg : normalizerLines ι.range (E.map ι) (ι b) =
      (Subgroup.map ι) '' (normalizerLines ⊤ E b) := by
    ext Z
    constructor
    · rintro ⟨g', hg', rfl⟩
      obtain ⟨g, rfl⟩ := (Subgroup.mem_inf.1 hg').1
      refine ⟨Subgroup.zpowers (g * b * g⁻¹),
        ⟨g, Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, (hmem g).1 (Subgroup.mem_inf.1 hg').2⟩, rfl⟩,
        ?_⟩
      rw [MonoidHom.map_zpowers, map_mul, map_mul, map_inv]
    · rintro ⟨Z₀, ⟨g, hg, rfl⟩, rfl⟩
      refine ⟨ι g, Subgroup.mem_inf.2 ⟨⟨g, rfl⟩, (hmem g).2 (Subgroup.mem_inf.1 hg).2⟩, ?_⟩
      rw [MonoidHom.map_zpowers, map_mul, map_mul, map_inv]
  rw [himg]
  exact Set.ncard_image_of_injective _ (Subgroup.map_injective hι)

theorem natCard_ggAutomizer_map (hι : Function.Injective ι) (E : Subgroup M) :
    Nat.card (ggAutomizer ι.range (E.map ι)) = Nat.card (ggAutomizer (⊤ : Subgroup M) E) := by
  have hnorm := Subgroup.comap_normalizer_eq_of_le_range (H := E.map ι) (f := ι)
    (Subgroup.map_le_range ι E)
  rw [Subgroup.comap_map_eq_self_of_injective hι] at hnorm
  have hmem : ∀ g : M, ι g ∈ Subgroup.normalizer ((E.map ι : Subgroup G) : Set G) ↔
      g ∈ Subgroup.normalizer (E : Set M) := fun g =>
    Iff.of_eq (congrArg (fun S : Subgroup M => g ∈ S) hnorm)
  let e : ↥E ≃* ↥(E.map ι) := Subgroup.equivMapOfInjective E ι hι
  let Φ : MulAut ↥E ≃* MulAut ↥(E.map ι) := MulAut.congr e
  have hind : ggInduced ι.range (E.map ι) =
      (Φ.toMonoidHom : MulAut ↥E →* MulAut ↥(E.map ι)) '' ggInduced (⊤ : Subgroup M) E := by
    ext ψ
    constructor
    · rintro ⟨g', hg', hgn, hψ⟩
      obtain ⟨g, rfl⟩ := hg'
      have hgE : g ∈ Subgroup.normalizer (E : Set M) := (hmem g).1 hgn
      refine ⟨Φ.symm ψ, ⟨g, Subgroup.mem_top _, hgE, fun x => ?_⟩, Φ.apply_symm_apply ψ⟩
      apply hι
      have h1 : ι (((Φ.symm ψ) x : ↥E) : M) = ((ψ (e x) : ↥(E.map ι)) : G) := by
        have : e ((Φ.symm ψ) x) = ψ (e x) := by
          show e (e.symm (ψ (e x))) = ψ (e x)
          exact e.apply_symm_apply _
        exact congrArg Subtype.val this
      rw [h1, hψ (e x), map_mul, map_mul, map_inv]
      rfl
    · rintro ⟨φ, ⟨g, -, hgn, hφ⟩, rfl⟩
      refine ⟨ι g, ⟨g, rfl⟩, (hmem g).2 hgn, fun b' => ?_⟩
      have hb' : ι ((e.symm b' : ↥E) : M) = (b' : G) := by
        have : e (e.symm b') = b' := e.apply_symm_apply b'
        exact congrArg Subtype.val this
      show ((e (φ (e.symm b')) : ↥(E.map ι)) : G) = ι g * b' * (ι g)⁻¹
      have h2 : ((e (φ (e.symm b')) : ↥(E.map ι)) : G) = ι (((φ (e.symm b') : ↥E)) : M) := rfl
      rw [h2, hφ, map_mul, map_mul, map_inv, hb']
  have hmap : ggAutomizer ι.range (E.map ι) =
      (ggAutomizer (⊤ : Subgroup M) E).map Φ.toMonoidHom := by
    rw [ggAutomizer, ggAutomizer, MonoidHom.map_closure]
    exact congrArg Subgroup.closure hind
  rw [hmap]
  exact Subgroup.card_map_of_injective Φ.injective

theorem isElemAbelian_comap (hι : Function.Injective ι) {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.comap ι) := by
  refine ⟨isMulCommutative_iff.2 fun a b => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hι
    have := isMulCommutative_iff.1 hE.1 ⟨ι a, a.2⟩ ⟨ι b, b.2⟩
    simpa using congrArg Subtype.val this
  · apply hι
    simpa using hE.2 (ι x) hx

end TransportLines

section M2M3

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem centralizer_pinnedElt_highRoot_E8 :
    Subgroup.centralizer
        ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} : Set (adjointGroup .E8 K)) =
        EPilot.highRadical .E8 K ⊔ EPilot.perpLevi .E8 K ∧
      EPilot.perpLevi .E8 K ≤
        Subgroup.normalizer (EPilot.highRadical .E8 K : Set (adjointGroup .E8 K)) ∧
      Disjoint (EPilot.highRadical .E8 K) (EPilot.perpLevi .E8 K) ∧
      IsPGroup 2 (EPilot.highRadical .E8 K) ∧
      pCoreOf 2 (Subgroup.centralizer
        ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} : Set (adjointGroup .E8 K))) =
        EPilot.highRadical .E8 K := by
  obtain ⟨hC, hLQ, hdisj, hQ⟩ := KGExc.centralizer_decomp_highRoot (K := K)
    (Or.inr (Or.inr rfl)) E8Pilot.isQuasisimple_e7Levi E8Pilot.center_e7Levi_eq_bot
  exact ⟨hC, hLQ, hdisj,
    (EPilot.isTwoRadicalDecomp_highRoot (K := K) (Or.inr (Or.inr rfl)) one_ne_zero).1, hQ⟩

theorem le_highRadical_of_isPGroup_of_normalized {P : Subgroup (adjointGroup .E8 K)}
    (hP : IsPGroup 2 P)
    (hPC : P ≤ Subgroup.centralizer
      ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} : Set (adjointGroup .E8 K)))
    (hN : Subgroup.centralizer
        ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} : Set (adjointGroup .E8 K)) ≤
      Subgroup.normalizer (P : Set (adjointGroup .E8 K))) :
    P ≤ EPilot.highRadical .E8 K := by
  obtain ⟨-, -, -, -, hcore⟩ := centralizer_pinnedElt_highRoot_E8 (K := K)
  rw [← hcore]
  refine CFSG.CGT.PushingUpLit.SolK.le_pCoreOf_of_normalized hPC (fun h hh x hx => ?_) hP
  exact (Subgroup.mem_normalizer_iff.1 (hN hh) x).1 hx

omit
  [Finite K] [CharP K 2] in
theorem pinnedElt_highRoot_mem_highRadical :
    EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) ∈ EPilot.highRadical .E8 K := by
  have hθ : highRoot .E8 ∈ parabolicRadicalRoots .E8 (EPilot.perpNodes .E8) :=
    (EPilot.mem_parabolicRadicalRoots_perpNodes_iff_iform (Or.inr (Or.inr rfl))).2
      ⟨isRoot_highRoot _, iform_self_pos_of_isRoot (isRoot_highRoot _)⟩
  exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan hθ 1)

omit
  [Finite K] [CharP K 2] in
theorem perpLevi_le_centralizer_pinnedElt_neg_highRoot :
    EPilot.perpLevi .E8 K ≤ Subgroup.centralizer
      ({EPilot.pinnedElt .E8 (-highRoot .E8) (1 : K)} : Set (adjointGroup .E8 K)) := by
  intro d hd
  have hdS : (d : ModGL .E8 K) ∈ rootSpan .E8 K (EPilot.perpRoots .E8) :=
    Subgroup.mem_subgroupOf.1 hd
  have h := EPilot.rootSpan_perpRoots_le_centralizer_highRootSL2 (K := K)
    (Or.inr (Or.inr rfl)) hdS
  have hmem : pinnedX .E8 K (-highRoot .E8) 1 ∈ EPilot.highRootSL2 .E8 K :=
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨1, rfl⟩)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h _ hmem).symm

theorem perpLevi_le_centralizer_rootThree :
    EPilot.perpLevi .E8 K ≤
      Subgroup.centralizer ({rootThree .E8 K (highRoot .E8)} : Set (adjointGroup .E8 K)) := by
  intro d hd
  obtain ⟨hC, -⟩ := centralizer_pinnedElt_highRoot_E8 (K := K)
  have h1 : d ∈ Subgroup.centralizer
      ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} : Set (adjointGroup .E8 K)) := by
    rw [hC]
    exact Subgroup.mem_sup_right hd
  have h2 := perpLevi_le_centralizer_pinnedElt_neg_highRoot (K := K) hd
  have c1 : Commute d (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)) :=
    Subgroup.mem_centralizer_singleton_iff.1 h1
  have c2 : Commute d (EPilot.pinnedElt .E8 (-highRoot .E8) (1 : K)) :=
    Subgroup.mem_centralizer_singleton_iff.1 h2
  exact Subgroup.mem_centralizer_singleton_iff.2 (c1.mul_right c2)

theorem nonempty_mulEquiv_perpLevi_E8 :
    Nonempty (EPilot.perpLevi .E8 K ≃* adjointGroup .E7 K) :=
  ⟨E8Pilot.e7LeviEquiv K⟩

theorem commutator_perpLevi_E8_eq_top : commutator ↥(EPilot.perpLevi .E8 K) = ⊤ :=
  (E8Pilot.isQuasisimple_e7Levi (K := K)).1.commutator_eq_top

theorem hUmax_E8_range {G : Type} [Group G] (ι : adjointGroup .E8 K →* G)
    (hι : Function.Injective ι) :
    ∀ P : Subgroup G, IsPGroup 2 P →
      P ≤ Subgroup.centralizer ({ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K))} : Set G) ⊓
        ι.range →
      Subgroup.centralizer ({ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K))} : Set G) ⊓
          ι.range ≤ Subgroup.normalizer (P : Set G) →
      P ≤ (EPilot.highRadical .E8 K).map ι := by
  rw [centralizer_singleton_inf_range_eq_map ι hι]
  exact hUmax_map ι hι fun P hP hPC hN => le_highRadical_of_isPGroup_of_normalized hP hPC hN

omit
  [Finite K] in
theorem hirr_E8_range (hK : Nat.card K = 2) {G : Type} [Group G] (ι : adjointGroup .E8 K →* G)
    (hι : Function.Injective ι) {L : Subgroup G} (hL : (EPilot.perpLevi .E8 K).map ι ≤ L) :
    ∀ V : Subgroup G, Subgroup.zpowers (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K))) ≤ V →
      V ≤ (EPilot.highRadical .E8 K).map ι → L ≤ Subgroup.normalizer (V : Set G) →
      V = Subgroup.zpowers (ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K))) ∨
        V = (EPilot.highRadical .E8 K).map ι :=
  hirr_map ι hι (fun _ h1 h2 hN => eq_zpowers_or_eq_highRadical hK h1 h2 hN) hL

theorem map_le_centralizer_map_pinnedElt_highRoot {G : Type} [Group G]
    (ι : adjointGroup .E8 K →* G) :
    (EPilot.highRadical .E8 K).map ι ≤
        Subgroup.centralizer ({ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K))} : Set G) ∧
      (EPilot.perpLevi .E8 K).map ι ≤
        Subgroup.centralizer ({ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K))} : Set G) := by
  obtain ⟨hC, -⟩ := centralizer_pinnedElt_highRoot_E8 (K := K)
  have key : ∀ x : adjointGroup .E8 K,
      x ∈ Subgroup.centralizer ({EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)} :
        Set (adjointGroup .E8 K)) →
      ι x ∈ Subgroup.centralizer ({ι (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K))} : Set G) :=
    fun x hx => by
      have hc : Commute x (EPilot.pinnedElt .E8 (highRoot .E8) (1 : K)) :=
        Subgroup.mem_centralizer_singleton_iff.1 hx
      exact Subgroup.mem_centralizer_singleton_iff.2 (hc.map ι)
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact key x (by rw [hC]; exact Subgroup.mem_sup_left hx)
  · rintro _ ⟨x, hx, rfl⟩
    exact key x (by rw [hC]; exact Subgroup.mem_sup_right hx)

end M2M3

section M4M5

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem commute_pinnedX_one_mul_of_iform_eq_zero {γ β : Fin Tag.E8.rank → ℤ}
    (hγ : IsRoot .E8 γ) (hβ : IsRoot .E8 β) (h0 : CFSG.LieType.Steinberg.Adjoint.iform γ β = 0) :
    Commute (pinnedX .E8 K γ 1) (pinnedX .E8 K β 1 * pinnedX .E8 K (-β) 1) := by
  have h1 : Commute (pinnedX .E8 K γ 1) (pinnedX .E8 K β 1) :=
    EPilot.commute_of_iform_eq_zero (Or.inr (Or.inr rfl)) hγ hβ h0
      (Subgroup.subset_closure ⟨1, rfl⟩) (Subgroup.subset_closure ⟨1, rfl⟩)
  have h2 : Commute (pinnedX .E8 K γ 1) (pinnedX .E8 K (-β) 1) :=
    EPilot.commute_of_iform_eq_zero (Or.inr (Or.inr rfl)) hγ (IsRoot.neg hβ)
      (by rw [CFSG.LieType.Chevalley.iform_neg_right, h0, neg_zero])
      (Subgroup.subset_closure ⟨1, rfl⟩) (Subgroup.subset_closure ⟨1, rfl⟩)
  exact h1.mul_right h2

omit [Finite K] [CharP K 2] in
theorem commute_framePart_rootThree {L : List (Fin Tag.E8.rank → ℤ)} {β : Fin Tag.E8.rank → ℤ}
    (hL : ∀ σ ∈ L, IsRoot .E8 σ) (hβ : IsRoot .E8 β)
    (hperp : ∀ σ ∈ L, CFSG.LieType.Steinberg.Adjoint.iform σ β = 0) :
    Commute (⟨(L.map fun σ => pinnedX .E8 K σ 1).prod, list_prod_map_pinnedX_mem_adjointGroup L⟩ :
        adjointGroup .E8 K) (rootThree .E8 K β) := by
  apply Subtype.ext
  refine (Commute.list_prod_left _ _ fun x hx => ?_).eq
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hx
  exact commute_pinnedX_one_mul_of_iform_eq_zero (hL σ hσ) hβ (hperp σ hσ)

theorem oddDerivE8YFrame_mem : ∀ σ ∈ oddDerivE8YFrame, σ ∈ rootFinset .E8 := by decide +kernel

theorem oddDerivE8ZFrame_mem : ∀ σ ∈ oddDerivE8ZFrame, σ ∈ rootFinset .E8 := by decide +kernel

theorem oddDerivE8UFrame_mem : ∀ σ ∈ oddDerivE8UFrame, σ ∈ rootFinset .E8 := by decide +kernel

omit [Finite K] [CharP K 2] in
theorem exists_commute_rootThree_of_mem_innerRepsE8 {r : adjointGroup .E8 K}
    (hr : r ∈ innerRepsE8 K) :
    ∃ β : Fin Tag.E8.rank → ℤ, IsRoot .E8 β ∧ Commute r (rootThree .E8 K β) := by
  have hY : ∀ σ ∈ oddDerivE8YFrame, IsRoot .E8 σ := fun σ hσ =>
    mem_rootFinset.1 (oddDerivE8YFrame_mem σ hσ)
  have hZ : ∀ σ ∈ oddDerivE8ZFrame, IsRoot .E8 σ := fun σ hσ =>
    mem_rootFinset.1 (oddDerivE8ZFrame_mem σ hσ)
  have hU : ∀ σ ∈ oddDerivE8UFrame, IsRoot .E8 σ := fun σ hσ =>
    mem_rootFinset.1 (oddDerivE8UFrame_mem σ hσ)
  simp only [innerRepsE8, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · refine ⟨Pi.single 0 1, isRoot_single _ _, ?_⟩
    apply Subtype.ext
    exact (commute_pinnedX_one_mul_of_iform_eq_zero (isRoot_highRoot _) (isRoot_single _ _)
      (by decide +kernel)).eq
  · exact ⟨Pi.single 7 1, isRoot_single _ _,
      commute_framePart_rootThree hY (isRoot_single _ _) (by decide +kernel)⟩
  · exact ⟨Pi.single 7 1, isRoot_single _ _,
      commute_framePart_rootThree hZ (isRoot_single _ _) (by decide +kernel)⟩
  · exact ⟨Pi.single 4 1, isRoot_single _ _,
      commute_framePart_rootThree hU (isRoot_single _ _) (by decide +kernel)⟩

theorem exists_commute_conj_rootThree_highRoot {t : adjointGroup .E8 K} (ht : t ^ 2 = 1) :
    ∃ g : adjointGroup .E8 K,
      Commute t (g * rootThree .E8 K (highRoot .E8) * g⁻¹) := by
  by_cases ht1 : t = 1
  · exact ⟨1, by rw [ht1]; exact Commute.one_left _⟩
  obtain ⟨g, hg⟩ := classListE8_exists_conj_mem_innerRepsE8 ht ht1
  obtain ⟨β, hβ, hc⟩ := exists_commute_rootThree_of_mem_innerRepsE8 hg
  obtain ⟨h, hh⟩ := exists_conj_rootThree_eq (K := K) (Or.inr (Or.inr rfl))
    (isRoot_highRoot .E8) hβ
  refine ⟨g⁻¹ * h, ?_⟩
  have e : (g⁻¹ * h) * rootThree .E8 K (highRoot .E8) * (g⁻¹ * h)⁻¹ =
      g⁻¹ * rootThree .E8 K β * g := by
    rw [← hh]; group
  rw [e]
  have hc' : g * t * g⁻¹ * rootThree .E8 K β = rootThree .E8 K β * (g * t * g⁻¹) := hc.eq
  show t * (g⁻¹ * rootThree .E8 K β * g) = (g⁻¹ * rootThree .E8 K β * g) * t
  calc t * (g⁻¹ * rootThree .E8 K β * g)
      = g⁻¹ * (g * t * g⁻¹ * rootThree .E8 K β) * g := by group
    _ = g⁻¹ * (rootThree .E8 K β * (g * t * g⁻¹)) * g := by rw [hc']
    _ = (g⁻¹ * rootThree .E8 K β * g) * t := by group

theorem exists_sylow_two_mem_centralizer_pinnedElt_highRoot :
    ∃ S : Sylow 2 (adjointGroup .E8 K),
      EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) ∈ (S : Subgroup (adjointGroup .E8 K)) ∧
        EPilot.pinnedElt .E8 (highRoot .E8) (1 : K) ∈
          Subgroup.centralizer ((S : Subgroup (adjointGroup .E8 K)) : Set (adjointGroup .E8 K)) := by
  refine ⟨E8Pilot.posUnipotentSylowE .E8 K, ?_, ?_⟩
  · rw [E8Pilot.mem_posUnipotentSylowE]
    exact pinnedX_mem_posUnipotent_annih (isRoot_highRoot _) (height_highRoot_pos _) 1
  · rw [Subgroup.mem_centralizer_iff]
    intro u hu
    refine Subtype.ext ?_
    have h := E8Pilot.posUnipotent_le_centralizer_pinnedX_highRoot (τ := .E8) (1 : K)
      (E8Pilot.mem_posUnipotentSylowE.1 hu)
    exact Subgroup.mem_centralizer_singleton_iff.1 h

end M4M5

section M6

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def frameTorusE8 (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (adjointGroup .E8 K) :=
  (TableBExcTwoTB.tE K TableBExcTwo.frameE8).range

theorem isElemAbelian_frameTorusE8 : IsElemAbelian 3 (frameTorusE8 K) := by
  unfold frameTorusE8
  refine ⟨isMulCommutative_iff.2 fun a b => ?_, fun x hx => ?_⟩
  · obtain ⟨a, u, rfl⟩ := a
    obtain ⟨b, v, rfl⟩ := b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, mul_comm]
  · obtain ⟨u, rfl⟩ := hx
    have hu : u ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      have h3 : ((3 : ℕ) : ZMod 3) = 0 := CharP.cast_eq_zero (ZMod 3) 3
      calc (3 : ℕ) • Multiplicative.toAdd u
          = ((3 : ℕ) : ZMod 3) • Multiplicative.toAdd u :=
            (Nat.cast_smul_eq_nsmul (ZMod 3) 3 _).symm
        _ = 0 := by rw [h3, zero_smul]
    rw [← map_pow, hu, map_one]

theorem natCard_frameTorusE8 : Nat.card (frameTorusE8 K) = 3 ^ 8 := by
  let e := MonoidHom.ofInjective
    (TableBExcTwoTB.tE_injective (K := K) (F := TableBExcTwo.frameE8))
  unfold frameTorusE8
  rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  simp [ZMod.card]

omit [Finite K] in
theorem exists_conj_tE_single_eq_rootThree :
    ∃ g : adjointGroup .E8 K,
      g * TableBExcTwoTB.tE K TableBExcTwo.frameE8
          (Multiplicative.ofAdd (Pi.single 0 1 : Fin (7 + 1) → ZMod 3)) * g⁻¹ =
        rootThree .E8 K (highRoot .E8) := by
  have hE : TableBExcTwoTB.tE K TableBExcTwo.frameE8
      (Multiplicative.ofAdd (Pi.single 0 1 : Fin (7 + 1) → ZMod 3)) =
        rootThree .E8 K (TableBExcTwo.frameE8.root 0) := by
    rw [TableBExcTwoTB.tE_apply]
    have hf : (fun j => Multiplicative.ofAdd ((Pi.single 0 1 : Fin (7 + 1) → ZMod 3) j)) =
        Pi.mulSingle (M := fun _ : Fin (7 + 1) => Multiplicative (ZMod 3)) 0
          (Multiplicative.ofAdd (1 : ZMod 3)) := by
      funext j
      by_cases h : j = 0
      · subst h; simp
      · simp [h]
    rw [hf]
    unfold TableBExcTwoTB.tD
    rw [MonoidHom.noncommPiCoprod_mulSingle, TableBExcTwoTB.tC_one]
    apply Subtype.ext
    rw [coe_rootThree (TableBExcTwo.frameE8.isRoot 0)]
    rfl
  obtain ⟨g, hg⟩ := exists_conj_rootThree_eq (K := K) (Or.inr (Or.inr rfl))
    (TableBExcTwo.frameE8.isRoot 0) (isRoot_highRoot .E8)
  exact ⟨g, by rw [hE]; exact hg⟩

end M6

end CFSG.StandardType.FrameRoute.FS81
