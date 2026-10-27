module

public import CFSG.RankThree.GF2n.Smith81.InspLocal
public import CFSG.RankThree.GF2n.Smith81.LinStmt
import CFSG.RankThree.GF2n.Smith81.InspLinLocal
import CFSG.RankThree.GF2n.Smith81.Smith219Step1
import CFSG.RankThree.GF2n.Smith81.InspLinCore

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld
open CFSG.SeitzReduction.F4Pilot (ordSL)

variable {G : Type} [Group G]

theorem two_pow_dvd_card_normalClosure_lin [Finite G]
    {M Q Z B V₁ V₂ : Subgroup G} {n : ℕ} (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 1 ≤ n) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    {f : ℕ} (hf : Nat.card Z = 2 ^ f) :
    2 ^ (f * (2 * n + 1) + f * (n * (n - 1) / 2)) ∣
      Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) := by
  set X := Subgroup.normalClosure ({z} : Set G) with hXdef
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hS.width hc.hyp
  have hP : (2 ^ f) ^ (2 * n + 1) * ordSL n (2 ^ f) ∣
      Nat.card (Subgroup.centralizer ({selfIn z} : Set ↥X)) := by
    have h1 := card_Lgen_dvd_centralizer hc hz hz1
    rwa [card_Lgen_eq hS hn, hw, hf] at h1
  have hP' : (2 ^ f) ^ (2 * n + 1) * (2 ^ f) ^ (n * (n - 1) / 2) ∣
      Nat.card (Subgroup.centralizer ({selfIn z} : Set ↥X)) :=
    (mul_dvd_mul_left _ (pow_dvd_ordSL n (2 ^ f))).trans hP
  have hcard : (2 ^ f) ^ (2 * n + 1) * (2 ^ f) ^ (n * (n - 1) / 2) =
      2 ^ (f * (2 * n + 1) + f * (n * (n - 1) / 2)) := by
    rw [← pow_add, ← pow_mul, mul_add]
  rw [hcard] at hP'
  exact hP'.trans (Subgroup.card_subgroup_dvd_card _)

theorem linInspect_data [Finite G]
    {M Q Z B V₁ V₂ : Subgroup G} {n : ℕ}
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 1 ≤ n)
    (h3 : Lin3Facts M Q Z B n V₁ V₂) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hroot : Timmesfeld.IsRootInvolutionSet {g : G | IsConj z g})
    (hconj : ∀ w : G, IsConj z w →
      ∃ x ∈ Subgroup.normalClosure ({z} : Set G), w = x * z * x⁻¹) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ 2 ≤ f ∧
      Hyp ↥(Subgroup.normalClosure ({z} : Set G)) (classIn z) ∧
      (∃ d ∈ classIn z, ∃ e ∈ rootSet (classIn z) d, e ≠ d) ∧
      Nat.card (rootGroup (classIn z) (selfIn z)) = 2 ^ f ∧
      2 ^ (f * (2 * n + 1) + f * (n * (n - 1) / 2)) ∣
        Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) ∧
      2 ^ (f * (2 * n + 1)) ∣ Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) ∧
      (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 ≤
        (Nat.card G).factorization 2 := by
  classical
  have H := hc.hyp
  obtain ⟨f, k₀, hf, hcp⟩ := H.cp
  have hf2 : 2 ≤ f := by
    have h4 := H.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  have hodd : pPrimeCore 2 G = ⊥ := H.toTim81Hyp.pPrimeCore_eq_bot H.q4
  have hnd : ∃ d e : G, IsConj z d ∧ IsConj z e ∧ orderOf (d * e) = 4 := by
    obtain ⟨d, hd, e, he, h4⟩ := exists_orderOf_mul_eq_four H hz hz1
    exact ⟨d, e, hd, he, h4⟩
  have hHyp := hyp_classIn hroot hconj hodd H.o2 hnd
  have hrootZ : rootGroup {g : G | IsConj z g} z = Z :=
    Smith219Step1.rootGroup_eq_Z_lin H h3.h212 hz hz1
  have hcardroot : Nat.card (rootGroup (classIn z) (selfIn z)) = 2 ^ f := by
    rw [card_rootGroup_classIn]
    show Nat.card (rootGroup {g : G | IsConj z g} z) = 2 ^ f
    rw [hrootZ, hf]
  have hl : ∃ d ∈ classIn z, ∃ e ∈ rootSet (classIn z) d, e ≠ d := by
    refine ⟨selfIn z, IsConj.refl z, ?_⟩
    by_contra hcon
    push Not at hcon
    have hle : rootGroup (classIn z) (selfIn z) ≤ Subgroup.zpowers (selfIn z) := by
      rw [rootGroup, Subgroup.closure_le]
      intro e he
      rw [hcon e he]
      exact Subgroup.mem_zpowers _
    have h1 := Subgroup.card_le_of_le hle
    have hz2 : (selfIn z) ^ 2 = 1 := Subtype.ext (by simpa using sq_eq_one_of_cp hcp z hz)
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) hz2
    rw [hcardroot, Nat.card_zpowers] at h1
    have h3 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    omega
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hS.width H
  have hQdvd : Nat.card Q ∣ Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) :=
    Subgroup.card_dvd_of_le (Q_le_normalClosure H hz hz1)
  have hlow : 2 ^ (f * (2 * n + 1) + f * (n * (n - 1) / 2)) ∣
      Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) :=
    two_pow_dvd_card_normalClosure_lin hc hS hn hz hz1 hf
  have hpow : 2 ^ (f * (2 * n + 1)) ∣
      Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) := by
    rw [pow_mul, ← hf, ← hw]
    exact hQdvd
  have hv : (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 ≤
      (Nat.card G).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card (Subgroup.normalClosure ({z} : Set G))) 2
  exact ⟨f, hf, hf2, hHyp, hl, hcardroot, hlow, hpow, hv⟩

end CFSG.RankThree.GF2n.Smith81.Insp
