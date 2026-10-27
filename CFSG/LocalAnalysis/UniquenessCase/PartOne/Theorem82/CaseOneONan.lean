module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KeyLemma
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
import CFSG.GroupTheory.Commutator.PowMem
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Counterexample4

theorem forall_pow_three_eq_one_mem_L_of_threeCover (c : Counterexample4 G) (hK3 : K3Exp)
    (hOut : ∀ α : MulAut (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L), IsPGroup 3 (Subgroup.zpowers α) →
      α ∈ innAut (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L))
    (hON : CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
      (fun Y _ => CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor Y .ONan)
      (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) :
    ∀ x ∈ P, x ^ 3 = 1 → x ∈ c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set Lbar := ↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L with hLbar
  set φ := CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L with hφ
  set C : Subgroup G := φ.ker.map c.S.M.subtype with hC
  intro x hxP hx3
  have hxM : x ∈ c.S.M := hP.le hxP
  let xm : ↥c.S.M := ⟨x, hxM⟩
  have hxm3 : xm ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hφx3 : φ xm ^ 3 = 1 := by rw [← map_pow, hxm3, map_one]
  have hαp : IsPGroup 3 (Subgroup.zpowers (φ xm)) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    obtain ⟨n, hn⟩ : ∃ n, orderOf (φ xm) = 3 ^ n := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hφx3) with h | h
      · exact ⟨0, by rw [h]; norm_num⟩
      · exact ⟨1, by rw [h]; norm_num⟩
    exact ⟨n, hn⟩
  obtain ⟨lbar, hlbar⟩ := MonoidHom.mem_range.mp (hOut (φ xm) hαp)
  have hlbar_center : lbar ^ 3 ∈ Subgroup.center Lbar := by
    have h3 : MulAut.conj (lbar ^ 3) = 1 := by rw [map_pow, hlbar, hφx3]
    rw [Subgroup.mem_center_iff]
    intro w
    have h := congrArg (fun f : MulAut Lbar => f w) h3
    simp only [MulAut.one_apply, MulAut.conj_apply] at h
    calc w * lbar ^ 3 = (lbar ^ 3 * w * (lbar ^ 3)⁻¹) * lbar ^ 3 := by rw [h]
      _ = lbar ^ 3 * w := by group
  have hlbar9 : lbar ^ 9 = 1 := by
    let z : ↥(Subgroup.center Lbar) := ⟨lbar ^ 3, hlbar_center⟩
    have hdvd : orderOf z ∣ Nat.card ↥(Subgroup.center Lbar) := orderOf_dvd_natCard z
    rw [hON.2.1] at hdvd
    have hz3 : z ^ 3 = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · rw [orderOf_eq_one_iff.mp h]; exact one_pow 3
      · rw [← h]; exact pow_orderOf_eq_one z
    have h := congrArg (fun w : ↥(Subgroup.center Lbar) => (w : Lbar)) hz3
    have h' : (lbar ^ 3) ^ 3 = 1 := by simpa [z] using h
    rw [← pow_mul] at h'
    simpa using h'
  have hlbar_p : IsPGroup 3 (Subgroup.zpowers lbar) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have hdvd : orderOf lbar ∣ 3 ^ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa using hlbar9
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact ⟨n, hn⟩
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (p := 3) (P := Subgroup.zpowers lbar) hlbar_p
  have hlbar3 : lbar ^ 3 = 1 :=
    hK3 Lbar hON Q lbar (hQ (Subgroup.mem_zpowers lbar))
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥c.L) lbar
  have hlM : (l : G) ∈ c.S.M := c.hyp81.1 l.2
  have hφl : φ ⟨(l : G), hlM⟩ = MulAut.conj lbar := by
    rw [CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L c.S.M c.le_normalizer_L hlM l.2]
    exact congrArg MulAut.conj hl
  let c0 : G := (l : G)⁻¹ * x
  have hc0M : c0 ∈ c.S.M := c.S.M.mul_mem (c.S.M.inv_mem hlM) hxM
  have hφc0 : φ ⟨c0, hc0M⟩ = 1 := by
    have hsplit : (⟨c0, hc0M⟩ : ↥c.S.M) = (⟨(l : G), hlM⟩ : ↥c.S.M)⁻¹ * xm := by
      ext
      simp [c0, xm]
    rw [hsplit, map_mul, map_inv, hφl, hlbar, inv_mul_cancel]
  have hc0C : c0 ∈ C :=
    Subgroup.mem_map.mpr ⟨⟨c0, hc0M⟩, MonoidHom.mem_ker.mpr hφc0, rfl⟩
  have hN_le : CFSG.Open.pCoreOf 2 c.L ≤ c.S.M :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L).trans c.hyp81.1
  have hl3N : (l : G) ^ 3 ∈ CFSG.Open.pCoreOf 2 c.L := by
    have hmem : (l ^ 3 : ↥c.L) ∈ CFSG.Open.pCore 2 ↥c.L := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, hl, hlbar3]
    rw [CFSG.Open.pCoreOf, Subgroup.mem_map]
    exact ⟨l ^ 3, hmem, rfl⟩
  have hcommLC : ⁅c.L, C⁆ ≤ CFSG.Open.pCoreOf 2 c.L :=
    (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 c.L c.S.M C
      c.le_normalizer_L (Subgroup.map_subtype_le φ.ker)).mp (le_refl C)
  have hc0_3N : c0 ^ 3 ∈ CFSG.Open.pCoreOf 2 c.L := by
    haveI : ((CFSG.Open.pCoreOf 2 c.L).subgroupOf c.S.M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN_le).mpr
        (c.le_normalizer_L.trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L))
    have hab : ⁅(⟨(l : G), hlM⟩ : ↥c.S.M), ⟨c0, hc0M⟩⁆ ∈
        (CFSG.Open.pCoreOf 2 c.L).subgroupOf c.S.M := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.commutator_le.mp hcommLC (l : G) l.2 c0 hc0C
    have ha : (⟨(l : G), hlM⟩ : ↥c.S.M) ^ 3 ∈
        (CFSG.Open.pCoreOf 2 c.L).subgroupOf c.S.M := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hl3N
    have habn : ((⟨(l : G), hlM⟩ : ↥c.S.M) * ⟨c0, hc0M⟩) ^ 3 ∈
        (CFSG.Open.pCoreOf 2 c.L).subgroupOf c.S.M := by
      rw [Subgroup.mem_subgroupOf]
      have hxe : ((⟨(l : G), hlM⟩ : ↥c.S.M) * ⟨c0, hc0M⟩ : ↥c.S.M) = xm := by
        ext
        simp [c0, xm]
      rw [hxe, hxm3]
      exact (CFSG.Open.pCoreOf 2 c.L).one_mem
    have h := CFSG.GroupTheory.pow_mem_of_commutator_mem hab ha habn
    rwa [Subgroup.mem_subgroupOf] at h
  obtain ⟨k, hk⟩ : ∃ k, (c0 ^ 3) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L) ⟨c0 ^ 3, hc0_3N⟩
    exact ⟨k, by simpa using congrArg (fun z : ↥(CFSG.Open.pCoreOf 2 c.L) => (z : G)) hk⟩
  have hc1_3 : (c0 ^ (2 ^ k)) ^ 3 = 1 := by
    rw [← pow_mul, show 2 ^ k * 3 = 3 * 2 ^ k by ring, pow_mul, hk]
  have hc1C : c0 ^ (2 ^ k) ∈ C := Subgroup.pow_mem C hc0C _
  have hc1L : c0 ^ (2 ^ k) ∈ c.L := mem_L_of_mem_ker_of_pow_three_eq_one c hc1C hc1_3
  have hc0_3L : c0 ^ 3 ∈ c.L := (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L) hc0_3N
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 2 ^ k * b = 3 * a + 1 := by
    have hlt : 2 ^ k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hne : 2 ^ k % 3 ≠ 0 := by
      intro h0
      have h3 : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h0
      have h23 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    rcases (by omega : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2) with h | h
    · exact ⟨2 ^ k / 3, 1, by
        have := Nat.div_add_mod (2 ^ k) 3
        omega⟩
    · refine ⟨2 ^ (k + 1) / 3, 2, ?_⟩
      have hmod : 2 ^ (k + 1) % 3 = 1 := by
        rw [pow_succ, Nat.mul_mod, h]
      have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
      have := Nat.div_add_mod (2 ^ (k + 1)) 3
      omega
  have hc0L : c0 ∈ c.L := by
    have h1 : (c0 ^ 3) ^ a ∈ c.L := Subgroup.pow_mem c.L hc0_3L a
    have h2 : (c0 ^ (2 ^ k)) ^ b ∈ c.L := Subgroup.pow_mem c.L hc1L b
    have heq : c0 = ((c0 ^ 3) ^ a)⁻¹ * (c0 ^ (2 ^ k)) ^ b := by
      have h1 : c0 ^ (2 ^ k * b) = c0 ^ (3 * a + 1) := by rw [hab]
      rw [pow_add, pow_mul, pow_mul, pow_one] at h1
      rw [h1]
      group
    rw [heq]
    exact c.L.mul_mem (c.L.inv_mem h1) h2
  have hxeq : x = (l : G) * c0 := by simp [c0]
  rw [hxeq]
  exact c.L.mul_mem l.2 hc0L

theorem false_of_threeCover_ONan (c : Counterexample4 G) (hK3 : K3Exp) (hK5 : K5)
    (hOut : ∀ α : MulAut (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L), IsPGroup 3 (Subgroup.zpowers α) →
      α ∈ innAut (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L))
    (hON : CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
      (fun Y _ => CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor Y .ONan)
      (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L))
    {p : ℕ} (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p) : False := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 c.S.M
  have hΩ : ∀ x ∈ P, x ^ 3 = 1 → x ∈ c.L :=
    forall_pow_three_eq_one_mem_L_of_threeCover c hK3 hOut hON hP
  have h3 := three_le_pRank_range_of_forall_pow_eq_one c hp h76 hP hΩ
  have hp' : p.Prime := hp.1.1
  have hle : CFSG.Open.pRank p
      (CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).range ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L))) :=
    CFSG.SectionRank.pRank_mono hp'.one_lt le_top
  have h2 : CFSG.Open.pRank p
      (⊤ : Subgroup (MulAut (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L))) ≤ 2 := by
    have h := hK5.2.2.2.2.1 (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) hON p hp'
      (c.five_le_of_mem_sigma hp)
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h
  omega

end Counterexample4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
