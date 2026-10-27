module

public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalBorel

import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalIndec
import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalCompl
import CFSG.Quasithin.Recognition.St84.Gen.D4qVertexOneModule
import CFSG.Quasithin.Recognition.St84.Gen.TriModule
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecSec
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
import CFSG.RankThree.GF2n.Smith81.TiD3Model
import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LMod
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
import CFSG.CGT.Timmesfeld75.L2Defs
import CFSG.LieType.BorelTits.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.Quasithin.Recognition.St84.Gen.CoprimeComplement
public import CFSG.Quasithin.Recognition.St84.Gen.SL2TorusAut
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Timmesfeld.RankOne.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Core
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxSL2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCentralQuotient
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinDS
import CFSG.Quasithin.Background.C1PackS15212C
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F7TwoFix
import CFSG.Quasithin.Background.F918H5
import CFSG.Quasithin.Background.FFC4Tr2
import CFSG.Quasithin.Background.FLc3Out
import CFSG.Quasithin.Background.FLcP0Mat
import CFSG.Quasithin.Background.GoldschmidtS146RBend1
import CFSG.Quasithin.Background.HPairBridge
import CFSG.Quasithin.Background.JonesParshallSmallSL
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S146zClaim
import CFSG.Quasithin.EmptyFaithful.S152Y15
import CFSG.Quasithin.EmptyFaithful.S152Y19
import CFSG.Quasithin.EmptyFaithful.S153E59A
import CFSG.Quasithin.EmptyFaithful.SzN15Top
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.H13.QRCBenderPairModel
import CFSG.Quasithin.Vol2.Ch11SecCB51Trans
import CFSG.Quasithin.Vol2.Ch1EightFourChar2
import CFSG.Quasithin.Vol2.Ch3Sec3L2qCore
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313B
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Defs
import CFSG.Quasithin.Vol2.Ch3T325D
import CFSG.Quasithin.Vol2.Ch3T325J
import CFSG.RankThree.CentralLiftU.UnitaryTriRoots
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.KS.PKit
import CFSG.RankThree.PartOne.KS.PKitLines
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S8.Statements
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.Sporadic.J4.QT2LocMain
import CFSG.Sporadic.J4.QT2LocRadMain
import CFSG.Sporadic.Schreier.MathieuOddCore
import CFSG.Sporadic.Schreier.TitsOuterTwo

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.CGT.Timmesfeld75 CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.NFa2 CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.D3
open scoped MatrixGroups commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem d4qIR_finrank_le {T W : Type} [Group T] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) T W) (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ t x y, B (ρ t x) (ρ t y) = B x y) (hsep : ∀ x, (∀ y, B x y = 0) → x = 0) :
    Module.finrank (ZMod 2) W ≤
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v | ∃ t w, v = ρ t w - w}) +
        Module.finrank (ZMod 2) ρ.invariants := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hnd : LinearMap.BilinForm.Nondegenerate B :=
    LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep
  set X := Submodule.span (ZMod 2) {v | ∃ t w, v = ρ t w - w} with hX
  have hle : LinearMap.BilinForm.orthogonal B X ≤ ρ.invariants := by
    intro v hv
    rw [Representation.mem_invariants]
    intro t
    have key : ∀ w, B w (ρ t⁻¹ v - v) = 0 := by
      intro w
      have h1 : B w (ρ t⁻¹ v) = B (ρ t w) v := by
        rw [← hB t w (ρ t⁻¹ v), Representation.self_inv_apply]
      have h2 : B (ρ t w - w) v = 0 :=
        LinearMap.BilinForm.isOrtho_def.mp
          (LinearMap.BilinForm.mem_orthogonal_iff.mp hv _
            (Submodule.subset_span ⟨t, w, rfl⟩))
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h2
      rw [map_sub, h1, h2, sub_self]
    have h3 : ρ t⁻¹ v = v := sub_eq_zero.mp (hnd.2 _ key)
    calc ρ t v = ρ t (ρ t⁻¹ v) := by rw [h3]
      _ = v := Representation.self_inv_apply ρ t v
  have h1 := LinearMap.BilinForm.finrank_orthogonal hnd X
  have h2 := Submodule.finrank_mono hle
  have h3 : Module.finrank (ZMod 2) X ≤ Module.finrank (ZMod 2) W := Submodule.finrank_le X
  omega

private theorem d4qIR_zmod_two (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

private theorem d4qIR_card_invariants_le (hf : 2 ≤ f) {K H : Subgroup G}
    (hd : D4qVertexOneData (pCoreOf 2 L1) (centerOf (pCoreOf 2 L1)) K H f) {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : SecRep (K ⊔ H) (centerOf (pCoreOf 2 L1)) (pCoreOf 2 L1) W) (c1 : D4qCoordLeft L1 S f)
    (hKL : K ≤ L1) (hQK : pCoreOf 2 L1 ⊔ K = L1) (hQinfK : pCoreOf 2 L1 ⊓ K = ⊥) :
    Nat.card (Representation.invariants
      ((leviRep le_sup_left s).comp (S.subgroupOf K).subtype)) ≤ 2 ^ f := by
  classical
  letI := c1.field
  letI := c1.fintype
  haveI : CharP c1.F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c1.card])
  have hF : Fintype.card c1.F = 2 ^ (3 * f) := by rw [← Nat.card_eq_fintype_card, c1.card]
  let α' : ↥K →* SL(2, c1.F) := c1.α.comp (Subgroup.inclusion hKL)
  have hα'inj : Function.Injective α' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have hkQ : (k : G) ∈ pCoreOf 2 L1 := (c1.ker _).mp hk
    have hk' : (k : G) ∈ pCoreOf 2 L1 ⊓ K := ⟨hkQ, k.2⟩
    rw [hQinfK] at hk'
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hk'))
  have hα'surj : Function.Surjective α' := by
    intro g
    obtain ⟨l, hl⟩ := c1.surj g
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right K (pCoreOf 2 L1)
      (hKL.trans (le_normalizer_pCoreOf 2 L1))
    have hlKQ : (l : G) ∈ (K : Set G) * (pCoreOf 2 L1 : Set G) := by
      rw [← hmul, sup_comm, hQK]
      exact l.2
    obtain ⟨k, hk, y, hy, hky⟩ := hlKQ
    refine ⟨⟨k, hk⟩, ?_⟩
    have hyL : y ∈ L1 := pCoreOf_le 2 L1 hy
    have hαy : c1.α ⟨y, hyL⟩ = 1 := (c1.ker _).mpr hy
    have hl' : l = ⟨k, hKL hk⟩ * ⟨y, hyL⟩ := Subtype.ext hky.symm
    show c1.α ⟨k, hKL hk⟩ = g
    rw [← hl, hl', map_mul, hαy, mul_one]
  let e : ↥K ≃* SL(2, c1.F) := MulEquiv.ofBijective α' ⟨hα'inj, hα'surj⟩
  let ρ' : Representation (ZMod 2) SL(2, c1.F) W :=
    (leviRep le_sup_left s).comp e.symm.toMonoidHom
  have hρ' : ∀ k : ↥K, ρ' (e k) = leviRep le_sup_left s k := by
    intro k
    simp [ρ']
  haveI : Fact ρ'.IsIrreducible := by
    refine ⟨?_⟩
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
    obtain ⟨hnt, hinv⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff
      (leviRep le_sup_left s)).mp (hd.isIrreducible_leviRep hf s)
    refine ⟨hnt, fun U hU => hinv U ?_⟩
    intro k u hu
    rw [← hρ' k]
    exact hU (e k) u hu
  have hnt : ∃ g, ρ' g ≠ 1 := by
    obtain ⟨k, hk⟩ := hd.exists_leviRep_ne_one hf s
    exact ⟨e k, by rwa [hρ' k]⟩
  have hW : Nat.card W = 2 ^ (8 * f) := hd.card_secRep s
  obtain ⟨K', hK'field, hK'fin, hK'alg, hK'card, σ, β, hβ⟩ :=
    exists_kForm_model hf hF ρ' hnt hW
  letI : Field K' := hK'field
  letI : Fintype K' := hK'fin
  letI : Algebra K' c1.F := hK'alg
  have hτ : ∀ a, FiniteField.frobeniusAlgHom K' c1.F a = a ^ 2 ^ f := by
    intro a
    rw [FiniteField.frobeniusAlgHom_apply, hK'card]
  have hline : ∀ w ∈ Representation.invariants
      ((leviRep le_sup_left s).comp (S.subgroupOf K).subtype),
      ∃ c : K', ((β w : ↥(kForm (FiniteField.frobeniusAlgHom K' c1.F))) : Hyp c1.F) =
        algebraMap K' c1.F c • e0 c1.F := by
    intro w hw
    rw [Representation.mem_invariants] at hw
    refine fix_U_line hK'card (Nat.le_self_pow (by omega) 2) (by rw [hF]; ring)
      (FiniteField.frobeniusAlgHom K' c1.F) hτ (β w).2 fun a => ?_
    have hgS : ((e.symm (D2.uSL (σ.symm a)) : ↥K) : G) ∈ S := by
      have he : c1.α (Subgroup.inclusion hKL (e.symm (D2.uSL (σ.symm a)))) =
          D2.uSL (σ.symm a) := e.apply_symm_apply _
      have hmem := (c1.memS (Subgroup.inclusion hKL (e.symm (D2.uSL (σ.symm a))))).mpr
        (by rw [he]; exact mem_utri_entries.mpr ⟨by simp [D2.uSL], by simp [D2.uSL]⟩)
      simpa using hmem
    have hfix : ρ' (D2.uSL (σ.symm a)) w = w :=
      hw ⟨e.symm (D2.uSL (σ.symm a)), Subgroup.mem_subgroupOf.mpr hgS⟩
    have h := hβ (D2.uSL (σ.symm a)) w
    rw [D2.slMap_uSL, RingEquiv.apply_symm_apply, hfix] at h
    exact h.symm
  have hinj : Function.Injective
      (fun w : Representation.invariants ((leviRep le_sup_left s).comp (S.subgroupOf K).subtype) =>
        (hline w.1 w.2).choose) := by
    intro w₁ w₂ h
    have e₁ := (hline w₁.1 w₁.2).choose_spec
    have e₂ := (hline w₂.1 w₂.2).choose_spec
    simp only at h
    rw [h] at e₁
    exact Subtype.ext (β.injective (Subtype.ext (e₁.trans e₂.symm)))
  calc Nat.card (Representation.invariants ((leviRep le_sup_left s).comp (S.subgroupOf K).subtype))
      ≤ Nat.card K' := Nat.card_le_card_of_injective _ hinj
    _ = 2 ^ f := by rw [Nat.card_eq_fintype_card, hK'card]

private theorem d4qIR_centerOf_left_le_commutator (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) :
    centerOf (pCoreOf 2 L1) ≤ ⁅pCoreOf 2 L2, L2⁆ := by
  obtain ⟨c⟩ := hD.exists_coordRight hH
  letI := c.field
  obtain ⟨β, hβs, hβker, hβeq⟩ := c.nat
  refine (hD.centerOf_pCoreOf_left_le_right hH h1).trans fun z hz => ?_
  obtain ⟨y, hyc, hyZ, hy⟩ := exists_commutator_natSecVec_eq c.surj hβs hβeq
    (le_normalizer_centerOf_of_le_normalizer (le_normalizer_pCoreOf 2 L2)) z
  have hyz : y⁻¹ * z ∈ (⊥ : Subgroup G) := (natSecVec_eq_iff hβker hyZ hz).mp hy
  rw [Subgroup.mem_bot, inv_mul_eq_one] at hyz
  rw [← hyz, Subgroup.commutator_comm]
  exact Subgroup.commutator_mono le_rfl
    (show centerOf (pCoreOf 2 L2) ≤ pCoreOf 2 L2 from inf_le_left) hyc

private theorem d4qIR_commutator_mem (hH : Hyp111 L1 L2 S) (hD : D4qLocalData L1 L2 S f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1))
    (hcomm1 : ∀ x ∈ pCoreOf 2 L1, ∀ y ∈ pCoreOf 2 L1,
      x * y * x⁻¹ * y⁻¹ ∈ centerOf (pCoreOf 2 L1))
    {t x : G} (ht : t ∈ S) (hx : x ∈ pCoreOf 2 L1) :
    t * x * t⁻¹ * x⁻¹ ∈ ⁅pCoreOf 2 L2, L2⁆ := by
  have hS1 : S ≤ L1 := hD.le_left hH h1
  have hS2 : S ≤ L2 := hD.le_right hH
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (pCoreOf 2 L2) (pCoreOf 2 L1)
    ((hH.pCoreOf_le_right.trans hS1).trans (le_normalizer_pCoreOf 2 L1))
  have htQ : t ∈ (pCoreOf 2 L2 : Set G) * (pCoreOf 2 L1 : Set G) := by
    rw [← hmul, sup_comm, hD.sup_pCoreOf hH h1]
    exact ht
  obtain ⟨b, hb, a, ha, rfl⟩ := htQ
  have hxS : x ∈ S := hH.pCoreOf_le_left hx
  have hax : a * x * a⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L1) := hcomm1 a ha x hx
  have hcen : a * x * a⁻¹ * x⁻¹ ∈ centerOf L1 := hD.center_left ▸ hax
  have hbL : b ∈ L1 := hS1 (hH.pCoreOf_le_right hb)
  have hbz : b * (a * x * a⁻¹ * x⁻¹) * b⁻¹ = a * x * a⁻¹ * x⁻¹ := by
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcen).2 b hbL
    rw [hc, mul_inv_cancel_right]
  have hbx : b * x * b⁻¹ * x⁻¹ ∈ ⁅pCoreOf 2 L2, L2⁆ :=
    Subgroup.commutator_mem_commutator hb (hS2 hxS)
  have heq : b * a * x * (b * a)⁻¹ * x⁻¹ =
      (b * (a * x * a⁻¹ * x⁻¹) * b⁻¹) * (b * x * b⁻¹ * x⁻¹) := by group
  rw [heq, hbz]
  exact mul_mem (d4qIR_centerOf_left_le_commutator hH hD h1 hax) hbx

private theorem d4qIR_card_subgroupOf_ge (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {M : Subgroup G}
    (hZM : centerOf (pCoreOf 2 L1) ≤ M)
    (hcommM : ∀ t ∈ S, ∀ x ∈ pCoreOf 2 L1, t * x * t⁻¹ * x⁻¹ ∈ M) :
    2 ^ (8 * f) ≤ Nat.card (M.subgroupOf (pCoreOf 2 L1)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hHB, hSH, hSinfH, hHcard, hHcomm⟩ := hD.exists_hall_bigB hH h1
  obtain ⟨hd, hQK, hQinfK, -, -⟩ := hD.vertexOne_left hf hH h1 hHB hSH hSinfH hHcard hHcomm
  generalize hKdef : L1 ⊓ Subgroup.centralizer ((H ⊓ trivOTwoQuot L1 : Subgroup G) : Set G) = K
    at hd hQK hQinfK
  have hKL : K ≤ L1 := hKdef ▸ inf_le_left
  obtain ⟨W, hW1, hW2, hW3, ⟨s⟩⟩ := exists_secRep hd.secHyp
  obtain ⟨c1⟩ := hD.exists_coordLeft hH h1
  obtain ⟨B, hBinv, hBsep⟩ := hd.exists_invariant_form hf s
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hfin := d4qIR_finrank_le ((leviRep le_sup_left s).comp (S.subgroupOf K).subtype) B
    (fun t x y => hBinv (t : ↥K) x y) hBsep
  have hinv := d4qIR_card_invariants_le hf hd s c1 hKL hQK hQinfK
  set ρT : Representation (ZMod 2) ↥(S.subgroupOf K) W :=
    (leviRep le_sup_left s).comp (S.subgroupOf K).subtype with hρT
  set X := Submodule.span (ZMod 2) {v | ∃ t w, v = ρT t w - w} with hX
  have h2 : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hWdim : Module.finrank (ZMod 2) W = 8 * f := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hd.card_secRep s, h2] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hCdim : Module.finrank (ZMod 2) ρT.invariants ≤ f := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ρT.invariants)
    rw [h2] at h
    rw [h] at hinv
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hinv
  have hXcard : 2 ^ (7 * f) ≤ Nat.card X := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := X), h2]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  set Y : Subgroup ↥(pCoreOf 2 L1) := M.subgroupOf (pCoreOf 2 L1) with hY
  have hXY : ∀ v ∈ X, Multiplicative.ofAdd v ∈ Y.map s.cls := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨t, w, rfl⟩ := hv
      obtain ⟨n, hn⟩ := s.surj (Multiplicative.ofAdd w)
      have htK : ((t : ↥K) : G) ∈ K := (t : ↥K).2
      have htS : ((t : ↥K) : G) ∈ S := Subgroup.mem_subgroupOf.mp t.2
      have htN : ((t : ↥K) : G) ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
        le_normalizer_pCoreOf 2 L1 (hKL htK)
      let m : ↥(pCoreOf 2 L1) := ⟨((t : ↥K) : G) * n * ((t : ↥K) : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp htN n).mp n.2⟩
      have hact := s.act (Subgroup.inclusion le_sup_left (t : ↥K)) n m rfl
      have hw : w = Multiplicative.toAdd (s.cls n) := by rw [hn]; rfl
      refine ⟨m * n⁻¹, ?_, ?_⟩
      · show m * n⁻¹ ∈ Y
        rw [hY, Subgroup.mem_subgroupOf]
        exact hcommM _ htS _ n.2
      · rw [map_mul, map_inv]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, hw]
        change Multiplicative.toAdd (s.cls m) + -Multiplicative.toAdd (s.cls n) =
          (leviRep le_sup_left s (t : ↥K)) (Multiplicative.toAdd (s.cls n)) -
            Multiplicative.toAdd (s.cls n)
        rw [leviRep_apply, hact, sub_eq_add_neg]
    | zero => exact ⟨1, Y.one_mem, by simp⟩
    | add x y _ _ hx hy =>
      rw [ofAdd_add]
      exact mul_mem hx hy
    | smul c x _ hx =>
      rcases d4qIR_zmod_two c with rfl | rfl
      · simp
      · simpa using hx
  have hYcard : 2 ^ (8 * f) ≤ Nat.card Y := by
    have hker := Subgroup.card_ker_mul_card_range (s.cls.comp Y.subtype)
    have hrange : (s.cls.comp Y.subtype).range = Y.map s.cls := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h1' : Nat.card X ≤ Nat.card (s.cls.comp Y.subtype).range := by
      rw [hrange]
      refine Nat.card_le_card_of_injective
        (fun v : X => (⟨Multiplicative.ofAdd v.1, hXY v.1 v.2⟩ : ↥(Y.map s.cls))) ?_
      intro v₁ v₂ h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Multiplicative.ofAdd.injective h)
    have h2' : 2 ^ f ≤ Nat.card (s.cls.comp Y.subtype).ker := by
      rw [← hd.card_center]
      refine Nat.card_le_card_of_injective
        (fun z : ↥(centerOf (pCoreOf 2 L1)) =>
          (⟨⟨⟨z, (inf_le_left : centerOf (pCoreOf 2 L1) ≤ _) z.2⟩,
            Subgroup.mem_subgroupOf.mpr (hZM z.2)⟩,
            (s.ker _).mpr z.2⟩ : ↥(s.cls.comp Y.subtype).ker)) ?_
      intro z₁ z₂ h
      exact Subtype.ext (congrArg (fun u : ↥(s.cls.comp Y.subtype).ker => u.1.1.1) h)
    calc 2 ^ (8 * f) = 2 ^ f * 2 ^ (7 * f) := by rw [← pow_add]; ring_nf
      _ ≤ Nat.card (s.cls.comp Y.subtype).ker * Nat.card (s.cls.comp Y.subtype).range :=
        Nat.mul_le_mul h2' (hXcard.trans h1')
      _ = Nat.card Y := hker
  exact hYcard

private theorem d4qIR_comm_mem_center (hD : D4qLocalData L1 L2 S f) :
    ∀ x ∈ pCoreOf 2 L1, ∀ y ∈ pCoreOf 2 L1, x * y * x⁻¹ * y⁻¹ ∈ centerOf (pCoreOf 2 L1) := by
  have hf : 1 ≤ f := hD.one_le
  have hcomm := (CFSG.Quasithin.H13.commutator_eq_centerOf_of_isSpecialPow (p := 2) (q := 2 ^ f)
    (w := 4) (by norm_num) (Nat.le_self_pow (by omega) 2) hD.special_left).1
  intro x hx y hy
  have hmem : ⁅x, y⁆ ∈ ⁅pCoreOf 2 L1, pCoreOf 2 L1⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [hcomm] at hmem
  simpa [commutatorElement_def] using hmem

private theorem d4qIR_card_centerOf_right (hD : D4qLocalData L1 L2 S f) :
    Nat.card (centerOf (pCoreOf 2 L2)) = 2 ^ (2 * f) := by
  obtain ⟨F, hField, hFintype, hFcard, α, -, -, β, hβ, hker, -⟩ := hD.nat_right
  letI := hField
  letI := hFintype
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  rw [Nat.card_eq_of_bijective β ⟨hinj, hβ⟩, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_fin, Nat.card_eq_fintype_card, hFcard]
  ring

private theorem d4qIR_inf_le_commutator (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) :
    pCoreOf 2 L1 ⊓ pCoreOf 2 L2 ≤ ⁅pCoreOf 2 L2, L2⁆ := by
  have hYcard := d4qIR_card_subgroupOf_ge hf hH hD h1 (M := ⁅pCoreOf 2 L2, L2⁆)
    (d4qIR_centerOf_left_le_commutator hH hD h1)
    fun t ht x hx => d4qIR_commutator_mem hH hD h1 (d4qIR_comm_mem_center hD) ht hx
  set Y : Subgroup ↥(pCoreOf 2 L1) := (⁅pCoreOf 2 L2, L2⁆).subgroupOf (pCoreOf 2 L1) with hY
  have hYle : Y ≤ (pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1) := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (commutator_pCoreOf_le_pCoreOf L2 (Subgroup.mem_subgroupOf.mp hy))
  have hJcard : Nat.card ((pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1)) ≤ 2 ^ (8 * f) := by
    rw [← hD.card_inf_pCoreOf hH h1]
    exact Nat.card_le_card_of_injective
      (fun y : ↥((pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1)) =>
        (⟨((y : ↥(pCoreOf 2 L1)) : G), (y : ↥(pCoreOf 2 L1)).2,
          Subgroup.mem_subgroupOf.mp y.2⟩ : ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2)))
      fun y₁ y₂ h => Subtype.ext (Subtype.ext
        (congrArg (fun u : ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) => (u : G)) h))
  have hYeq : Y = (pCoreOf 2 L2).subgroupOf (pCoreOf 2 L1) :=
    Subgroup.eq_of_le_of_card_ge hYle (hJcard.trans hYcard)
  intro j hj
  have hjY : (⟨j, hj.1⟩ : ↥(pCoreOf 2 L1)) ∈ Y := by
    rw [hYeq, Subgroup.mem_subgroupOf]
    exact hj.2
  exact Subgroup.mem_subgroupOf.mp hjY

theorem D4qLocalData.le_pCoreOf_left_of_commutator_le (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {W : Subgroup G}
    (hWS : W ≤ S) (hWL : ⁅W, L2⁆ ≤ centerOf (pCoreOf 2 L2)) : W ≤ pCoreOf 2 L1 := by
  have hS1 : S ≤ L1 := hD.le_left hH h1
  have hS2 : S ≤ L2 := hD.le_right hH
  have hQ1S : pCoreOf 2 L1 ≤ S := hH.pCoreOf_le_left
  have hZ2N : L2 ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L2) : Set G) :=
    le_normalizer_centerOf_of_le_normalizer (le_normalizer_pCoreOf 2 L2)
  have hcomm1 := d4qIR_comm_mem_center hD
  have hZ12 := hD.centerOf_pCoreOf_left_le_right hH h1
  let Kc : Subgroup G :=
    { carrier := {κ | κ ∈ S ∧ ∀ x ∈ pCoreOf 2 L1, κ * x * κ⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L2)}
      one_mem' := ⟨S.one_mem, fun x _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haS, ha⟩ ⟨hbS, hb⟩
        refine ⟨S.mul_mem haS hbS, fun x hx => ?_⟩
        have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
            a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hZ2N (hS2 haS)) _).mp (hb x hx))
          (ha x hx)
      inv_mem' := by
        rintro a ⟨haS, ha⟩
        refine ⟨S.inv_mem haS, fun x hx => ?_⟩
        have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hZ2N (hS2 (S.inv_mem haS))) _).mp
          (inv_mem (ha x hx)) }
  have hmemKc : ∀ κ, κ ∈ Kc ↔
      κ ∈ S ∧ ∀ x ∈ pCoreOf 2 L1, κ * x * κ⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L2) :=
    fun κ => Iff.rfl
  have hKcS : Kc ≤ S := fun κ hκ => ((hmemKc κ).mp hκ).1
  have hWKc : W ≤ Kc := fun w hw => (hmemKc w).mpr
    ⟨hWS hw, fun x hx => hWL (Subgroup.commutator_mem_commutator hw (hS2 (hQ1S hx)))⟩
  have hNB := hD.bigB_le_normalizer hH h1
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  have hBKc : borelOf L1 S ≤ Subgroup.normalizer (Kc : Set G) := by
    refine le_normalizer_of_forall_conj_mem_of_mem fun b hb κ hκ => ?_
    obtain ⟨hκS, hκ⟩ := (hmemKc κ).mp hκ
    have hbB := hB1B hb
    have hbS : b ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_inf.mp (hNB hbB)).2
    have hbQ1 : b ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
      hH.bigB_le_normalizer_pCoreOf_left hbB
    have hbZ2 : b ∈ Subgroup.normalizer (centerOf (pCoreOf 2 L2) : Set G) :=
      le_normalizer_centerOf_of_le_normalizer hH.bigB_le_normalizer_pCoreOf_right hbB
    refine (hmemKc _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hbS κ).mp hκS, fun x hx => ?_⟩
    have hx' : b⁻¹ * x * b⁻¹⁻¹ ∈ pCoreOf 2 L1 :=
      (Subgroup.mem_normalizer_iff.mp (inv_mem hbQ1) x).mp hx
    have e : b * κ * b⁻¹ * x * (b * κ * b⁻¹)⁻¹ * x⁻¹ =
        b * (κ * (b⁻¹ * x * b⁻¹⁻¹) * κ⁻¹ * (b⁻¹ * x * b⁻¹⁻¹)⁻¹) * b⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hbZ2 _).mp (hκ _ hx')
  rcases le_pCoreOf_or_le_sup_of_borelOf_le_normalizer (n := 3 * f) (by omega) hH.h1.sylow h1 hS1
    hKcS hBKc with h | h
  · exact hWKc.trans h
  · exfalso
    have hQ1Kc : pCoreOf 2 L1 ≤ Kc := fun y hy =>
      (hmemKc y).mpr ⟨hQ1S hy, fun x hx => hZ12 (hcomm1 y hy x hx)⟩
    have hSKc : S ≤ Kc := h.trans (sup_le le_rfl hQ1Kc)
    have hcard := d4qIR_card_subgroupOf_ge hf hH hD h1 (M := centerOf (pCoreOf 2 L2)) hZ12
      fun t ht x hx => ((hmemKc t).mp (hSKc ht)).2 x hx
    have hle : Nat.card ((centerOf (pCoreOf 2 L2)).subgroupOf (pCoreOf 2 L1)) ≤ 2 ^ (2 * f) := by
      rw [← d4qIR_card_centerOf_right hD]
      exact Nat.card_le_card_of_injective
        (fun y : ↥((centerOf (pCoreOf 2 L2)).subgroupOf (pCoreOf 2 L1)) =>
          (⟨((y : ↥(pCoreOf 2 L1)) : G), Subgroup.mem_subgroupOf.mp y.2⟩ :
            ↥(centerOf (pCoreOf 2 L2))))
        fun y₁ y₂ h => Subtype.ext (Subtype.ext
          (congrArg (fun u : ↥(centerOf (pCoreOf 2 L2)) => (u : G)) h))
    have hlt : 2 ^ (2 * f) < 2 ^ (8 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

theorem D4qLocalData.eq_one_of_mem_trivOTwoQuot (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {k : G}
    (hkL : k ∈ L2) (hkodd : Odd (orderOf k)) (hk : k ∈ trivOTwoQuot L1) : k = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS1 : S ≤ L1 := hD.le_left hH h1
  have hS2 : S ≤ L2 := hD.le_right hH
  have hQ1S : pCoreOf 2 L1 ≤ S := hH.pCoreOf_le_left
  have hQ2S : pCoreOf 2 L2 ≤ S := hH.pCoreOf_le_right
  have hcomm1 := d4qIR_comm_mem_center hD
  have hZ12 := hD.centerOf_pCoreOf_left_le_right hH h1
  have hkN1 : k ∈ Subgroup.normalizer (L1 : Set G) := (mem_trivOTwoQuot.mp hk).1
  have hkQ1 : k ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L1 hkN1
  have hkZ1 : k ∈ Subgroup.normalizer (centerOf (pCoreOf 2 L1) : Set G) :=
    le_normalizer_centerOf_of_le_normalizer le_rfl hkQ1
  have hL1Z1 : L1 ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L1) : Set G) :=
    le_normalizer_centerOf_of_le_normalizer (le_normalizer_pCoreOf 2 L1)
  have hS_one : ∀ g ∈ S, Odd (orderOf g) → g = 1 := by
    intro g hg hodd
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hH.h1.pgroup ⟨g, hg⟩
    rw [Subgroup.orderOf_mk] at hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero] at hm
      exact orderOf_eq_one_iff.mp hm
    · rw [hm] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr ((Nat.even_pow' hpos.ne').mpr even_two))
  let D : Subgroup G :=
    { carrier := {x | x ∈ pCoreOf 2 L1 ∧ k * x * k⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L1)}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haQ, ha⟩ ⟨hbQ, hb⟩
        refine ⟨mul_mem haQ hbQ, ?_⟩
        have e : k * (a * b) * k⁻¹ * (a * b)⁻¹ =
            (k * a * k⁻¹ * a⁻¹) * (a * (k * b * k⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem ha (mem_centerOf_conj_of_mem_normalizer
          (le_normalizer_pCoreOf 2 L1 (pCoreOf_le 2 L1 haQ)) hb)
      inv_mem' := by
        rintro a ⟨haQ, ha⟩
        refine ⟨inv_mem haQ, ?_⟩
        have e : k * a⁻¹ * k⁻¹ * a⁻¹⁻¹ = a⁻¹ * (k * a * k⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact mem_centerOf_conj_of_mem_normalizer
          (le_normalizer_pCoreOf 2 L1 (pCoreOf_le 2 L1 (inv_mem haQ))) (inv_mem ha) }
  have hmemD : ∀ x, x ∈ D ↔
      x ∈ pCoreOf 2 L1 ∧ k * x * k⁻¹ * x⁻¹ ∈ centerOf (pCoreOf 2 L1) := fun x => Iff.rfl
  have hZD : centerOf (pCoreOf 2 L1) ≤ D := fun z hz =>
    (hmemD z).mpr ⟨(inf_le_left : centerOf (pCoreOf 2 L1) ≤ _) hz,
      mul_mem ((Subgroup.mem_normalizer_iff.mp hkZ1 z).mp hz) (inv_mem hz)⟩
  have hDQ : D ≤ pCoreOf 2 L1 := fun x hx => ((hmemD x).mp hx).1
  have hLD : L1 ≤ Subgroup.normalizer (D : Set G) := by
    refine le_normalizer_of_forall_conj_mem_of_mem fun l hl x hx => ?_
    obtain ⟨hxQ, hxz⟩ := (hmemD x).mp hx
    have ha : k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 L1 := (mem_trivOTwoQuot.mp hk).2 l hl
    have hx' : l * x * l⁻¹ ∈ pCoreOf 2 L1 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L1 hl) x).mp hxQ
    have hal : k * l * k⁻¹ * l⁻¹ * l ∈ L1 := mul_mem (pCoreOf_le 2 L1 ha) hl
    have h1' : (k * l * k⁻¹ * l⁻¹ * l) * (k * x * k⁻¹ * x⁻¹) * (k * l * k⁻¹ * l⁻¹ * l)⁻¹ ∈
        centerOf (pCoreOf 2 L1) := (Subgroup.mem_normalizer_iff.mp (hL1Z1 hal) _).mp hxz
    have h2' := hcomm1 _ ha _ hx'
    refine (hmemD _).mpr ⟨hx', ?_⟩
    have e : k * (l * x * l⁻¹) * k⁻¹ * (l * x * l⁻¹)⁻¹ =
        ((k * l * k⁻¹ * l⁻¹ * l) * (k * x * k⁻¹ * x⁻¹) * (k * l * k⁻¹ * l⁻¹ * l)⁻¹) *
          ((k * l * k⁻¹ * l⁻¹) * (l * x * l⁻¹) * (k * l * k⁻¹ * l⁻¹)⁻¹ * (l * x * l⁻¹)⁻¹) := by
      group
    rw [e]
    exact mul_mem h1' h2'
  rcases hD.irred_left D hZD hDQ hLD with hDZ | hDQ1
  ·
    obtain ⟨W, hZW, hWQ, hWcard, hWL⟩ := hD.mid_right
    have hWQ1 : W ≤ pCoreOf 2 L1 :=
      hD.le_pCoreOf_left_of_commutator_le hf hH h1 (hWQ.trans hQ2S) hWL
    have hZ2N : L2 ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L2) : Set G) :=
      le_normalizer_centerOf_of_le_normalizer (le_normalizer_pCoreOf 2 L2)
    have hkZ2 : Subgroup.zpowers k ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L2) : Set G) :=
      (Subgroup.zpowers_le.mpr hkL).trans hZ2N
    have hWN : W ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L2) : Set G) :=
      ((hWQ.trans hQ2S).trans hS2).trans hZ2N
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers k))
        (Nat.card (centerOf (pCoreOf 2 L2))) := by
      rw [Nat.card_zpowers, d4qIR_card_centerOf_right hD]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hkodd)
    have hcommW : ∀ h ∈ Subgroup.zpowers k, ∀ l ∈ W,
        h * l * h⁻¹ * l⁻¹ ∈ centerOf (pCoreOf 2 L2) := by
      intro h hh l hl
      have hmem : ⁅h, l⁆ ∈ ⁅L2, W⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.zpowers_le.mpr hkL hh) hl
      rw [Subgroup.commutator_comm] at hmem
      exact hWL hmem
    have hWZ2 : W ≤ centerOf (pCoreOf 2 L2) := by
      intro w hw
      obtain ⟨z, hz, c, hc, rfl⟩ :=
        exists_mul_mem_inf_centralizer_of_coprime hZW hWN hkZ2 hcop hcommW hw
      have hcW : c ∈ W := (Subgroup.mem_inf.mp hc).1
      have hck : k * c = c * k :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 k (Subgroup.mem_zpowers k)
      have hcD : c ∈ D := (hmemD c).mpr ⟨hWQ1 hcW, by
        rw [hck, mul_inv_cancel_right, mul_inv_cancel]
        exact one_mem _⟩
      rw [hDZ] at hcD
      exact mul_mem hz (hZ12 hcD)
    have hcard := Subgroup.card_le_of_le hWZ2
    rw [hWcard, d4qIR_card_centerOf_right hD] at hcard
    have hlt : 2 ^ (2 * f) < 2 ^ (5 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  ·
    obtain ⟨c2⟩ := hD.exists_coordRight hH
    letI := c2.field
    letI := c2.fintype
    haveI : CharP c2.F 2 :=
      charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c2.card])
    obtain ⟨s, hs⟩ := c2.surj (utriElt 1)
    have hsS : (s : G) ∈ S := (c2.memS s).mpr (by rw [hs]; exact utriElt_mem_utri 1)
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (pCoreOf 2 L2) (pCoreOf 2 L1)
      ((hQ2S.trans hS1).trans (le_normalizer_pCoreOf 2 L1))
    have hs' : (s : G) ∈ (pCoreOf 2 L2 : Set G) * (pCoreOf 2 L1 : Set G) := by
      rw [← hmul, sup_comm, hD.sup_pCoreOf hH h1]
      exact hsS
    obtain ⟨b, hb, y, hy, hby⟩ := hs'
    have hyL2 : y ∈ L2 := hS2 (hQ1S hy)
    have hbL2 : b ∈ L2 := pCoreOf_le 2 L2 hb
    have hαb : c2.α ⟨b, hbL2⟩ = 1 := (c2.ker _).mpr hb
    have hαy : c2.α ⟨y, hyL2⟩ = utriElt 1 := by
      have hs'' : s = ⟨b, hbL2⟩ * ⟨y, hyL2⟩ := Subtype.ext hby.symm
      rw [← hs, hs'', map_mul, hαb, one_mul]
    have hky : k * y * k⁻¹ * y⁻¹ ∈ centerOf (pCoreOf 2 L1) := by
      have hyD : y ∈ D := by
        rw [hDQ1]
        exact hy
      exact ((hmemD y).mp hyD).2
    have hkyQ2 : k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 L2 :=
      (inf_le_left : centerOf (pCoreOf 2 L2) ≤ _) (hZ12 hky)
    have hα : c2.α (⟨k, hkL⟩ * ⟨y, hyL2⟩ * (⟨k, hkL⟩ : ↥L2)⁻¹ * (⟨y, hyL2⟩ : ↥L2)⁻¹) = 1 :=
      (c2.ker _).mpr hkyQ2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hαy] at hα
    have hkS : k ∈ S :=
      (c2.memS ⟨k, hkL⟩).mpr (mem_utri_of_conj_utriElt_one_eq (mul_inv_eq_one.mp hα))
    exact hS_one k hkS hkodd

theorem D4qLocalData.commutator_pCoreOf_right (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) {H : Subgroup G}
    (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ (3 * f) - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (htriv : H ⊓ L2 ⊓ trivOTwoQuot L1 = ⊥) :
    ⁅pCoreOf 2 L2, L2⁆ = pCoreOf 2 L2 := by
  have hJ := d4qIR_inf_le_commutator hf hH hD h1
  have hsup := hD.pCoreOf_right_le_commutator_sup hf hH h1 hHB hSH hSinfH hHcard hHcomm htriv
  have hRQ : ⁅pCoreOf 2 L2, L2⁆ ≤ pCoreOf 2 L2 := commutator_pCoreOf_le_pCoreOf L2
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right ⁅pCoreOf 2 L2, L2⁆ (pCoreOf 2 L1)
    (((hRQ.trans hH.pCoreOf_le_right).trans (hD.le_left hH h1)).trans
      (le_normalizer_pCoreOf 2 L1))
  refine le_antisymm hRQ fun x hx => ?_
  have hx' : x ∈ ((⁅pCoreOf 2 L2, L2⁆ : Subgroup G) : Set G) * (pCoreOf 2 L1 : Set G) := by
    rw [← hmul]
    exact hsup hx
  obtain ⟨r, hr, y, hy, rfl⟩ := hx'
  have hyQ2 : y ∈ pCoreOf 2 L2 := by
    have h := (pCoreOf 2 L2).mul_mem ((pCoreOf 2 L2).inv_mem (hRQ hr)) hx
    rwa [inv_mul_cancel_left] at h
  exact mul_mem hr (hJ ⟨hy, hyQ2⟩)

theorem D4qLocalData.indec_right (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : D4qLocalData L1 L2 S f) (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) :
    ⁅pCoreOf 2 L2, L2⁆ = pCoreOf 2 L2 := by
  obtain ⟨H, hHB, hSH, hSinfH, hHcard, hHcomm⟩ := hD.exists_hall_bigB hH h1
  refine hD.commutator_pCoreOf_right hf hH h1 hHB hSH hSinfH hHcard hHcomm ?_
  rw [eq_bot_iff]
  intro t ht
  obtain ⟨htHL, httriv⟩ := Subgroup.mem_inf.mp ht
  obtain ⟨htH, htL2⟩ := Subgroup.mem_inf.mp htHL
  have hHodd : Odd (Nat.card H) := by
    have hf1 : f ≠ 0 := by omega
    rw [hHcard]
    exact (Nat.Even.sub_odd Nat.one_le_two_pow
      ((show Even 2 by norm_num).pow_of_ne_zero (by omega : 3 * f ≠ 0)) odd_one).mul
      (Nat.Even.sub_odd Nat.one_le_two_pow ((show Even 2 by norm_num).pow_of_ne_zero hf1) odd_one)
  have hodd : Odd (orderOf t) := Odd.of_dvd_nat hHodd (Subgroup.orderOf_dvd_natCard H htH)
  exact Subgroup.mem_bot.mpr (hD.eq_one_of_mem_trivOTwoQuot hf hH h1 htL2 hodd httriv)

end CFSG.Quasithin.F112R.St84

end
