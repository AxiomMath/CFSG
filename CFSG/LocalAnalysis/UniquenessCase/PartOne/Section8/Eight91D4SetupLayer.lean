module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Model
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4SU32
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Bridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.K148InnerCentA
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint.Chevalley (TwistTag ModGL)
open CFSG.LieType.Chevalley (graphFixedRootGroup)
open CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Opp)
open CFSG.LocalAnalysis.GLTheoremA.S10 (twoPart)
open CFSG.LocalAnalysis.GLTheoremA.K148Inner
  (twoPart_mul_odd twoPart_two_pow k148InnerCentFact_holds)

private lemma r891_conj_mem_of_commutator_mem {X : Type} [Group X] {C R : Subgroup X}
    (hRC : R ≤ C) (hc : ∀ a ∈ C, ∀ b ∈ C, a * b * a⁻¹ * b⁻¹ ∈ R) :
    ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
  intro c hcC r hr
  have h := hc c hcC r (hRC hr)
  have heq : c * r * c⁻¹ = (c * r * c⁻¹ * r⁻¹) * r := by group
  rw [heq]
  exact R.mul_mem h hr

private theorem r891_opp_eq_of_su32_model {X : Type} [Group X] [Finite X] {z : X}
    {R : Subgroup X} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : ↥R ≃* ↥(StatedSU 3 2 F))
    (hRC : R ≤ Subgroup.centralizer ({z} : Set X))
    (hcomm : ∀ a ∈ Subgroup.centralizer ({z} : Set X),
      ∀ b ∈ Subgroup.centralizer ({z} : Set X), a * b * a⁻¹ * b⁻¹ ∈ R)
    (hInner : twoPart (Nat.card (Subgroup.centralizer ({z} : Set X))) = 8) :
    Opp 2 (Subgroup.centralizer ({z} : Set X)) = R := by
  classical
  let C : Subgroup X := Subgroup.centralizer ({z} : Set X)
  have hRcard : Nat.card R = 216 := by
    rw [Nat.card_congr e.toEquiv]
    simpa using CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two
      (F := F) (f := 1) (by simpa using hF)
  have htwoR : twoPart (Nat.card R) = 8 := by
    rw [hRcard, show (216 : ℕ) = 8 * 27 by norm_num,
      twoPart_mul_odd (m := 8) (n := 27) (by norm_num) (by norm_num),
      show (8 : ℕ) = 2 ^ 3 by norm_num, twoPart_two_pow]
  have hRnormal : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R :=
    r891_conj_mem_of_commutator_mem hRC hcomm
  have hOppR : Opp 2 R = R := by
    obtain ⟨E, hcore, -⟩ := exists_oddCore_statedSU_two (F := F) hF
    have h := R891OddCore.comap_map (F := R) (e := e)
      (R₀ := (⊤ : Subgroup ↥(StatedSU 3 2 F))) (E₀ := E) hcore
    have hmap : ((⊤ : Subgroup ↥(StatedSU 3 2 F)).comap e.toMonoidHom).map R.subtype = R := by
      rw [Subgroup.comap_top, Subgroup.map_top, Subgroup.range_subtype]
    rw [hmap] at h
    exact h.1
  have hRleOppC : R ≤ Opp 2 C := by
    rw [← hOppR, Opp]
    apply Subgroup.closure_mono
    rintro x ⟨hxR, k, hk⟩
    exact ⟨hRC hxR, k, hk⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁, hT₁⟩ := CFSG.ABGLocalTools.exists_isSylowOf (G := X) 2 R
  have hT₁leC : T₁ ≤ C := fun x hx => hRC (hT₁.le hx)
  have hT₁card : Nat.card T₁ = 8 := by
    have h : Nat.card T₁ = twoPart (Nat.card R) := hT₁.card_eq
    rw [h, htwoR]
  have hT₁C : CFSG.ABGLocalTools.IsSylowOf 2 T₁ C := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hT₁leC ?_
    rw [hT₁card, ← hInner]
    rfl
  have hOppC_le_R : Opp 2 C ≤ R := by
    rw [Opp]
    apply (Subgroup.closure_le R).mpr
    rintro x ⟨hxC, k, hk⟩
    have hxP : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hxPC : IsPGroup 2 ((Subgroup.zpowers x).subgroupOf C) := hxP.comap_subtype (K := C)
    obtain ⟨T, hxT⟩ := hxPC.exists_le_sylow
    let TX : Subgroup X := (T : Subgroup ↥C).map C.subtype
    have hTXC : CFSG.ABGLocalTools.IsSylowOf 2 TX C := ⟨T, rfl⟩
    obtain ⟨c, hcC, hconj⟩ := hT₁C.exists_mem_conj hTXC
    have hxZC : (⟨x, hxC⟩ : ↥C) ∈ (Subgroup.zpowers x).subgroupOf C :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x)
    have hxTX : x ∈ TX := by
      change x ∈ (T : Subgroup ↥C).map C.subtype
      exact Subgroup.mem_map_of_mem C.subtype (hxT hxZC)
    have hcxR : c⁻¹ * x * c ∈ R := hT₁.le ((hconj x).mp hxTX)
    have h := hRnormal c hcC (c⁻¹ * x * c) hcxR
    rwa [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at h
  exact le_antisymm hOppC_le_R hRleOppC



theorem exists_r891D4Layer_d4ShortSL2 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hz : z ∈ CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), R891D4Layer n z R := by
  classical
  have : Finite (ModGL TwistTag.D4.tag K) := CFSG.LieType.Chevalley.finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  obtain ⟨R, hzR, hRC, hcomm, hmodel⟩ :=
    r891_threeA_model_of_conj_short hn hK σ hσ
      (MulEquiv.refl (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) hz3 hz1
      (1 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (by
        exact hz)
  rcases hmodel with ⟨hev, hq, F, hFfield, hFfin, hFcard, ⟨eR⟩⟩ |
    ⟨hod, Ω, hΩfield, hΩclosed, hΩchar, U, hU, eRU, hRq⟩
  ·
    let : Field F := hFfield
    let : Finite F := hFfin
    have hn2 : 2 ≤ n := by
      obtain ⟨k, hk⟩ := hev
      omega
    have hqmod : 2 ^ n % 3 = 1 := CFSG.two_pow_mod_three_of_even hev
    have hSL : R891SL3Two ↥R n :=
      Or.inr (Or.inl ⟨hn2, hev, threeCover_psl3_of_mulEquiv hn2 hev hFcard hq eR⟩)
    have hPi : Sec4.IsSLThreePiAt ↥R (2 ^ n) :=
      ⟨F, hFfield, hFfin,
        Or.inl ⟨hFcard, hqmod,
          ⟨eR.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F)⟩⟩⟩
    refine ⟨R, hzR, hRC, hcomm, hSL, hPi, fun hn1 => ?_⟩
    obtain ⟨k, hk⟩ := hev
    omega
  ·
    let : Field Ω := hΩfield
    let : IsAlgClosed Ω := hΩclosed
    let : CharP Ω 2 := hΩchar
    by_cases hn1 : n = 1
    ·
      subst n
      obtain ⟨F, hFfield', hFfin', hF4, ⟨eUS⟩⟩ :=
        exists_mulEquiv_statedSU_two (Ω := Ω) hU
      let : Field F := hFfield'
      let : Finite F := hFfin'
      have eRUS : ↥R ≃* ↥(StatedSU 3 2 F) := eRU.trans eUS
      have hSU : R891SU32 ↥R :=
        R891SU32.of_mulEquiv eRUS.symm (r891SU32_statedSU_two (F := F) hF4)
      have hInner : twoPart (Nat.card (Subgroup.centralizer
          ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) = 8 := by
        have h := k148InnerCentFact_holds 1 le_rfl K σ hK hσ z hz3 hz1
        simpa using h
      have hPi : Sec4.IsSLThreePiAt ↥R (2 ^ 1) :=
        ⟨F, hFfield', hFfin',
          Or.inr ⟨by simpa using hF4, by norm_num, ⟨eRUS⟩⟩⟩
      exact ⟨R, hzR, hRC, hcomm, Or.inl ⟨rfl, hSU⟩, hPi, fun _ =>
        r891_opp_eq_of_su32_model hF4 eRUS hRC hcomm hInner⟩
    ·
      have hn2 : 2 ≤ n := by
        obtain ⟨k, hk⟩ := hod
        omega
      have hqmod : 2 ^ n % 3 = 2 := CFSG.two_pow_mod_three_of_odd hod
      obtain ⟨F, hFfield', hFfin', hFcard', ⟨eUS⟩⟩ :=
        CFSG.OddStandard.GH71.S55.nonempty_statedSU_mulEquiv (Ω := Ω) (ℓ := 2) (f := n) hn hU
      let : Field F := hFfield'
      let : Finite F := hFfin'
      have hSL : R891SL3Two ↥R n :=
        Or.inr (Or.inr ⟨hn2, hod,
          threeCover_psu3_of_mulEquiv hn2 hod hU (hRq hn2).1 eRU⟩)
      have hPi : Sec4.IsSLThreePiAt ↥R (2 ^ n) :=
        ⟨F, hFfield', hFfin', Or.inr ⟨hFcard', hqmod, ⟨eRU.trans eUS.symm⟩⟩⟩
      refine ⟨R, hzR, hRC, hcomm, hSL, hPi, fun hn1' => ?_⟩
      exact absurd hn1' hn1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
