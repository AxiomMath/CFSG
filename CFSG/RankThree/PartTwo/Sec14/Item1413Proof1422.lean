module

public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item1413Proof1421
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Mathieu
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_centralizer_pair {c d w : G} (hwd : w * d = d * w)
    (hwc : w * c * w⁻¹ = c * d) :
    w ∈ Subgroup.normalizer (Subgroup.centralizer ({c, d} : Set G) : Set G) := by
  have hcl : (Subgroup.closure ({c, d} : Set G)).map (MulAut.conj w).toMonoidHom =
      Subgroup.closure ({c, d} : Set G) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hwc, show w * d * w⁻¹ = d by rw [hwd, mul_inv_cancel_right]]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact mul_mem (mem_closure_left _ _) (mem_closure_right _ _)
      · exact mem_closure_right _ _
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · have h1 : x * d * d⁻¹ ∈ Subgroup.closure ({x * d, d} : Set G) :=
          mul_mem (mem_closure_left _ _) (inv_mem (mem_closure_right _ _))
        simpa using h1
      · exact mem_closure_right _ _
  rw [← Subgroup.centralizer_closure]
  refine mem_normalizer_of_map_conj_eq ?_
  rw [map_conj_centralizer, hcl]

theorem false_of_m22 (hTr : Step1422TransvR)
    (hCe : Step1422CentR) (hSR : Step1422SR) (h146 : Item146S14) (hbot : Item145BotS14)
    {A : Subgroup G} {c₀ : G} {L₀ : Subgroup G} (hR : Sec15R G A c₀ L₀)
    (hfail : Fail1411 A (lB A)) {c : G} (hcΓ : Subgroup.zpowers c ∈ gammaA A (lB A))
    {L : Subgroup G} (hL : L ∈ lA A c)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) : False := by
  have hS : Sec14Std G A c L := sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hcA : c ∈ A := hD.mem_A
  have hM22s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22 :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hM22p : ¬ (Nat.card CFSG.Blueprint.NativeSporadic.M22).Prime := by
    rw [Sec4.Census.card_m22_eq]
    norm_num
  have hcL : c ∉ L := not_mem_of_mulEquiv_simple hD hM22p φ
  obtain ⟨R, hR', d, hdAL, hd1, hU0, hUR⟩ := hCe G A c₀ L₀ hR hfail c hcΓ L hL ⟨φ⟩
  obtain ⟨S, hS', hRS, hNS⟩ := hSR G A c₀ L₀ hR hfail c hcΓ L hL ⟨φ⟩ R hR'
  obtain ⟨w, hw, hwd, hwc⟩ := hTr G A c₀ L₀ hR hfail c hcΓ L hL ⟨φ⟩ d hdAL
  set U := CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c, d} : Set G)) with hUdef
  have hwU : w ∈ Subgroup.normalizer (U : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (mem_normalizer_centralizer_pair hwd hwc)
  have hnat := isNaturalFamily_lB A
  have hSw : S.map (MulAut.conj w).toMonoidHom ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) :=
    maximal_map_conj (W := Subgroup.normalizer (A : Set G))
      (fun Q hQ x hx => map_conj_mem_scriptQPi_top hnat hx hQ) hS' hw
  have hUS : U ≤ S := hUR.trans hRS
  have hUSw : U ≤ S.map (MulAut.conj w).toMonoidHom := by
    rw [← Late.map_conj_eq_of_mem_normalizer hwU]
    exact Subgroup.map_mono hUS
  have hconj : IsConjIn (xA A) S (S.map (MulAut.conj w).toMonoidHom) := by
    by_contra hc
    have h0 := rank3II_14_15_std hS (h146 G A c L hS) (hbot G A c L hS) hfail.2 hS' hSw hc
    exact hU0 (le_bot_iff.mp (h0 ▸ le_inf hUS hUSw))
  obtain ⟨x, hx, hxS⟩ := hconj
  have hXA : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  have hg : x⁻¹ * w ∈ Subgroup.normalizer (S : Set G) := by
    refine mem_normalizer_of_map_conj_eq ?_
    rw [← map_conj_map_conj, hxS, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have hgA : x⁻¹ * w ∈ Subgroup.normalizer (A : Set G) := mul_mem (inv_mem (hXA hx)) hw
  have hgc := hNS (Subgroup.mem_inf.mpr ⟨hg, hgA⟩)
  have hxc : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_singleton_le_normalizer_zpowers c
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA) (pPrimeCoreOf_le 3 _ hx))
  have hwc' : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    have h1 := mul_mem hxc hgc
    rwa [mul_inv_cancel_left] at h1
  have hcd : c * d ∈ Subgroup.zpowers c := by
    rw [← hwc]
    exact (Subgroup.mem_normalizer_iff.mp hwc' c).mp (Subgroup.mem_zpowers c)
  have hdc : d ∈ Subgroup.zpowers c := by
    have h1 := mul_mem (inv_mem (Subgroup.mem_zpowers c)) hcd
    rwa [inv_mul_cancel_left] at h1
  have hbot' := Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD.orderOf_eq hcL
  have hd0 : d ∈ L ⊓ Subgroup.zpowers c := ⟨hdAL.2, hdc⟩
  rw [hbot', Subgroup.mem_bot] at hd0
  exact hd1 hd0

end Proof1413

theorem step1422R_of (hTr : Step1422TransvR)
    (hCe : Step1422CentR) (hSR : Step1422SR) (h146 : Item146S14) (hbot : Item145BotS14) :
    Step1422R := by
  intro G _ _ A c L hR hfail c' hc' L' hL'
  exact ⟨fun φ => Proof1413.false_of_m22 hTr hCe hSR h146 hbot hR hfail hc' hL' φ⟩

end CFSG.RankThree.PartTwo.Sec14
