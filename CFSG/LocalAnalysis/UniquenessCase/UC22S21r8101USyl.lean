module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XD
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UBar
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XI
import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u81_dvd_card_centralizer {M B : Subgroup G} (hBM : B ≤ M) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hB : IsPGroup r B) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : Bar2 M}
    (hz : orderOf z = p)
    (hzB : z ∈ centralizer ((barImage M B : Subgroup (Bar2 M)) : Set (Bar2 M))) :
    p ∣ Nat.card (centralizer (B : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hker : IsPGroup 2 (uc22p21cPi M).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hzp : IsPGroup p (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨Q, hQp, hQmap, hQdisj⟩ := UC6S846.exists_lift_pGroup (uc22p21cPi M)
    (uc22p21c_pi_surjective M) hker hp hp2 (zpowers z) hzp
  have hMO : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf M)
  have hcomm : ∀ e ∈ B, ∀ a ∈ Q.map M.subtype, e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 M := by
    intro e he a ha
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 ha
    have hqC : uc22p21cPi M q ∈ centralizer ((barImage M B : Subgroup (Bar2 M)) : Set (Bar2 M)) :=
      zpowers_le.2 hzB (hQmap ▸ Subgroup.mem_map_of_mem _ hq)
    set m : ↥M := ⟨e, hBM he⟩
    have hmB : uc22p21cPi M m ∈ barImage M B := uc22p21c_mem_barImage.2 ⟨m, he, rfl⟩
    have h1 : uc22p21cPi M (m * q * m⁻¹ * q⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [mem_centralizer_iff.1 hqC _ hmB]
      group
    exact ⟨m * q * m⁻¹ * q⁻¹, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  obtain ⟨A', hA'C, -, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hr hr2 hp hp2 (pCoreOf 2 M)
    (Q.map M.subtype) B (UC6S846.isPGroup_pCoreOf M) ((map_subtype_le Q).trans hMO)
    (hBM.trans hMO) (hQp.map _) hB hcomm
  have hA'c : Nat.card A' = p := by
    rw [Nat.card_congr eA.toEquiv, Subgroup.card_map_of_injective M.subtype_injective,
      ← UC6S846.card_map_of_disjoint_ker _ Q hQdisj, hQmap, Nat.card_zpowers, hz]
  rw [← hA'c]
  exact Subgroup.card_dvd_of_le hA'C

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem u81_exists_omega (u : U4X D L K n)
    (hr3 : CFSG.Open.pRank (2 ^ n - 1) D.M ≤ 3) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) :
    ∃ B : Subgroup G, B ≤ R ∧ R ≤ centralizer (B : Set G) ∧ IsElemAbelian (2 ^ n - 1) B ∧
      ∀ x ∈ R, x ^ (2 ^ n - 1) = 1 → x ∈ B := by
  have hc := u.u81_comm hr3 hR
  have hBR : closure {x | x ∈ R ∧ x ^ (2 ^ n - 1) = 1} ≤ R := (closure_le _).2 fun x hx => hx.1
  refine ⟨_, hBR, fun y hy => mem_centralizer_iff.2 fun x hx => hc x (hBR hx) y hy, ?_,
    fun x hx hx1 => subset_closure ⟨hx, hx1⟩⟩
  exact IsElemAbelian.closure_of_commute (fun a ha b hb => hc a ha.1 b hb.1) fun a ha => ha.2

theorem u81_omega_decomp (u : U4X D L K n) {R B : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf (2 ^ n - 1) R D.M) (hBR : B ≤ R)
    (hΩ : ∀ x ∈ R, x ^ (2 ^ n - 1) = 1 → x ∈ B) {β : Bar2 D.M} (hβ : β ∈ barImage D.M B) :
    ∃ x₀ ∈ barImage D.M B ⊓ barImage D.M L, ∃ x₁ ∈ barImage D.M B ⊓ barImage D.M K,
      ∃ c ∈ barImage D.M B ⊓ centralizer
        ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)),
        β = x₀ * x₁ * c := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (2 ^ n - 1).Prime := ⟨u.prime_r⟩
  have hmem : ∀ {H : Subgroup (Bar2 D.M)}, Nat.card ↥(barImage D.M R ⊓ H) = 2 ^ n - 1 →
      ∀ x ∈ barImage D.M R ⊓ H, x ∈ barImage D.M B := by
    intro H hH x hx
    have hx1 : x ^ (2 ^ n - 1) = 1 := by
      have h := pow_card_eq_one' (x := (⟨x, hx⟩ : ↥(barImage D.M R ⊓ H)))
      rw [hH] at h
      exact congrArg Subtype.val h
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hx.1
    have hmR : m ^ (2 ^ n - 1) ∈ R.subgroupOf D.M := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact R.pow_mem hm _
    have hπ : uc22p21cPi D.M (m ^ (2 ^ n - 1)) = 1 := by rw [map_pow]; exact hx1
    have h1 := Subgroup.disjoint_def.1 (IsPGroup.disjoint_of_ne _ _ u.r_ne_two _ _
      hR.isPGroup.comap_subtype CFSG.pCore_isPGroup) hmR ((QuotientGroup.eq_one_iff _).1 hπ)
    refine uc22p21c_mem_barImage.2 ⟨m, hΩ _ hm ?_, rfl⟩
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  obtain ⟨x₀, hx₀, x₁, hx₁, c, hc, rfl⟩ := u.u81_decomp hR (barImage_mono hBR hβ)
  have hx₀B := hmem (u.u81_card_inf hR) x₀ hx₀
  have hx₁B := hmem (u.symm.u81_card_inf hR) x₁ hx₁
  refine ⟨x₀, ⟨hx₀B, hx₀.2⟩, x₁, ⟨hx₁B, hx₁.2⟩, c, ⟨?_, hc.2⟩, rfl⟩
  rw [show c = (x₀ * x₁)⁻¹ * (x₀ * x₁ * c) by group]
  exact (barImage D.M B).mul_mem ((barImage D.M B).inv_mem ((barImage D.M B).mul_mem hx₀B hx₁B)) hβ

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
