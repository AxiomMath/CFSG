module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Defs
import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13PGL
import CFSG.RankThree.PartTwo.Sec16.KS16ProofMeet
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec15.HypS

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1614Trans

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169
  CFSG.RankThree.PartTwo.Sec16.Proof1613 CFSG.RankThree.PartTwo.Sec16.Proof1614 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)

variable {G : Type} [Group G] [Finite G]

theorem card_inf_eq_three_of_pgl {A L : Subgroup G} {c : G} (h13 : Sec13Data G A c L)
    (hPGL : Sec8.IsZ3PGLThreePi ↥(lBarA c L A)) : Nat.card (A ⊓ L : Subgroup G) = 3 := by
  obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := hPGL
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    fun hπ => by subst hπ; exact hK.unitary
  have hq2 : 2 < p ^ f := by
    by_contra hle
    have h2 : p ^ f = 2 := by
      have hf : f ≠ 0 := by have := hK.one_le; omega
      have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
      omega
    cases π
    · exact false_of_isSolvable h13 (isSolvable_projImage_glPi_two hK h2) φ
    · change p ^ f % 3 = 1 at hq
      omega
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  set ψ := aBarHom h13 with hψ
  have := lBar_normal h13
  have hR : Nat.card ψ.range = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (aBarHom_injective h13)).toEquiv, h13.card_eq]
  have hcomap : Λ.comap ψ = (A ⊓ L).subgroupOf A := by
    ext a
    show ((ψ a : lBarA c L A) : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ∈
        Sec12.lBar c L ↔ (a : G) ∈ A ⊓ L
    constructor
    · intro ha
      refine ⟨a.2, ?_⟩
      have h3 : (⟨(a : G), h13.A_le_normalizer_zpowers a.2⟩ :
          Subgroup.normalizer (Subgroup.zpowers c : Set G)) ^ 3 ^ 1 = 1 :=
        Subtype.ext (by simpa using h13.isElemAbelian.2 _ a.2)
      exact mem_of_mk_mem_lBar h13.mem_thetaComponentsAt h3 ha
    · rintro ⟨-, haL⟩
      exact ⟨⟨(a : G), le_normalizer_zpowers_of_mem h13.mem_thetaComponentsAt haL⟩,
        Subgroup.mem_subgroupOf.mpr haL, rfl⟩
  have hinf : Nat.card (Λ ⊓ ψ.range : Subgroup (lBarA c L A)) =
      Nat.card (A ⊓ L : Subgroup G) := by
    have hmap : (Λ.comap ψ).map ψ = ψ.range ⊓ Λ := Subgroup.map_comap_eq ψ Λ
    have h1 : Nat.card ((Λ.comap ψ).map ψ) = Nat.card (Λ.comap ψ) :=
      Subgroup.card_map_of_injective (aBarHom_injective h13)
    rw [hmap, inf_comm, hcomap] at h1
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrel : Λ.relIndex ψ.range = Λ.index := by
    rw [← Subgroup.relIndex_sup_right, sup_comm, lBar_sup_range_aBarHom h13,
      Subgroup.relIndex_top_right]
  have hidx : Λ.index = 3 * (commutator (projImage (glPi π 3 (p ^ f) K))).index := by
    rw [← Subgroup.index_map_equiv _ φ]
    change (Λ.map φ.toMonoidHom).index = _
    rw [map_lBar_eq_commutator h13 φ, Subgroup.index_prod, Subgroup.index_bot,
      Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)), Nat.card_zmod]
  have hle := KS1615MeetProof.index_commutator_le_three hK hq2
  have hne1 : (commutator (projImage (glPi π 3 (p ^ f) K))).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    have hcomm := commutator_projImage_glPi hK hq2
    rw [h1] at hcomm
    apply kSPGLProper π p f K hK hq
    refine le_antisymm (Subgroup.map_mono (Sec4.slPi_le_glPi hπ)) fun x hx => ?_
    have hx' : (⟨x, hx⟩ : projImage (glPi π 3 (p ^ f) K)) ∈
        (projImage (slPi π 3 (p ^ f) K)).subgroupOf (projImage (glPi π 3 (p ^ f) K)) :=
      hcomm ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hx'
  have key := Subgroup.relIndex_mul_card Λ ψ.range
  rw [hrel, hR, hinf, hidx] at key
  set i := (commutator (projImage (glPi π 3 (p ^ f) K))).index with hi
  have hi0 : i ≠ 0 := by
    intro h0
    rw [h0] at key
    omega
  interval_cases i <;> omega

theorem exists_three_element_of_autIn {A L : Subgroup G}
    (φ : Sec4.autIn L A ≃* Multiplicative (ZMod 3)) :
    ∃ w ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, w ^ 3 ^ k = 1) ∧
      ∃ a ∈ A, w * a * w⁻¹ ≠ a := by
  set x : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1 with hx
  set σ : Sec4.autIn L A := φ.symm x with hσ
  obtain ⟨l, hN, hlL, hlσ⟩ := Sec4.mem_autIn_iff.mp σ.2
  have hn : orderOf l ≠ 0 := (orderOf_pos l).ne'
  obtain ⟨k, m, hm3, hlm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  refine ⟨l ^ m, Subgroup.mem_inf.mpr ⟨L.pow_mem hlL m, Subgroup.pow_mem _ hN m⟩, ⟨k, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hlm, pow_orderOf_eq_one]
  ·
    have hσm : σ ^ m ≠ 1 := by
      intro h1
      have h2 : φ (σ ^ m) = 1 := by rw [h1, map_one]
      rw [map_pow, hσ, MulEquiv.apply_symm_apply, hx, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]
        at h2
      have h3 : ((m : ℕ) : ZMod 3) = 0 := by
        have := congrArg Multiplicative.toAdd h2
        simpa using this
      rw [ZMod.natCast_eq_zero_iff] at h3
      exact hm3 h3
    have hσm' : ((σ : MulAut A) ^ m) ≠ 1 := by
      intro h1
      apply hσm
      apply Subtype.ext
      rw [Subgroup.coe_pow, h1, Subgroup.coe_one]
    have hact : A.normalizerMonoidHom ⟨l ^ m, Subgroup.pow_mem _ hN m⟩ = (σ : MulAut A) ^ m := by
      have : (⟨l ^ m, Subgroup.pow_mem _ hN m⟩ : Subgroup.normalizer (A : Set G)) =
          ⟨l, hN⟩ ^ m := rfl
      rw [this, map_pow, hlσ]
    by_contra hall
    push Not at hall
    apply hσm'
    ext a
    have h1 := Sec4.normalizerMonoidHom_apply_coe (Subgroup.pow_mem _ hN m) a
    rw [hact] at h1
    rw [h1, MulAut.one_apply]
    exact hall a a.2

omit [Finite G] in
theorem commutator_mem_inf {A L : Subgroup G} (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {w : G} (hw : w ∈ L ⊓ Subgroup.normalizer (A : Set G)) :
    ∀ a ∈ A, w * a * w⁻¹ * a⁻¹ ∈ A ⊓ L := by
  intro a ha
  obtain ⟨hwL, hwA⟩ := Subgroup.mem_inf.mp hw
  refine Subgroup.mem_inf.mpr ⟨A.mul_mem ((Subgroup.mem_normalizer_iff.mp hwA a).mp ha)
    (A.inv_mem ha), ?_⟩
  have h1 : a * w⁻¹ * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hAL ha) w⁻¹).mp (L.inv_mem hwL)
  have h2 : w * a * w⁻¹ * a⁻¹ = w * (a * w⁻¹ * a⁻¹) := by group
  rw [h2]
  exact L.mul_mem hwL h1

end CFSG.RankThree.PartTwo.Sec16.Proof1614Trans

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.RankThree.PartTwo.Sec16.Proof1613
  CFSG.RankThree.PartTwo.Sec16.Proof1614 CFSG.RankThree.PartTwo.Sec16.Proof1614Trans CFSG.GH74.GLS

theorem ks1614Trans_of
    (h131 : Item131) : KS1614Trans := by
  intro G _ _ A c L h hPGL
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨-, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  obtain ⟨hL3, -, -⟩ := facts_of_isZ3PGLThreePi h.toSec13Data hPGL
  obtain ⟨p, e, hp, -, hiso⟩ := hL3
  rcases cases131 h131 sporadicModels131 slTwoCenter h.toSec13Data with
      ⟨-, -, ⟨ψ⟩, -⟩ | ⟨-, -, hMJ, -⟩ | ⟨-, -, ⟨φ⟩, -⟩ | ⟨hcL', -⟩
  · exact (false_of_pgl_of_prod kSPGLProper h.toSec13Data hPGL ψ).elim
  · exfalso
    rcases hMJ with ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
    · obtain ⟨-, -, -, ⟨χ'⟩⟩ := facts_of_prod h.toSec13Data hM12p hM12z χ
      exact KFacts.KS14.not_isoLThreePi_M12 p e (isoLThreePi_of_mulEquiv χ' hiso)
    · obtain ⟨-, -, -, ⟨χ'⟩⟩ := facts_of_prod h.toSec13Data hJ2p hJ2z χ
      exact KFacts.KS14.ks17J2NotList.1 p e (isoLThreePi_of_mulEquiv χ' hiso)
  · obtain ⟨w, hw, hw3, a, haA, hwa⟩ := exists_three_element_of_autIn φ
    obtain ⟨d, hdL, hd1, hdeq⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
      (card_inf_eq_three_of_pgl h.toSec13Data hPGL)
    refine ⟨w, hw, hw3, d, (Subgroup.mem_inf.mp hdL).1, hd1, fun b hb => ?_, a, haA, hwa⟩
    rw [← hdeq]
    exact commutator_mem_inf h.le_normalizer hw b hb
  · exact (hcL hcL').elim

end CFSG.RankThree.PartTwo.Sec16
