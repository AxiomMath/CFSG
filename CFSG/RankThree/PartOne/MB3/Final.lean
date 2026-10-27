module

public import CFSG.RankThree.PartOne.MB3.Inner
public import CFSG.RankThree.PartOne.MB3.NoSeven
public import CFSG.RankThree.PartOne.MB3.FixedPoint
public import CFSG.RankThree.PartOne.MB3.Defs
public import CFSG.RankThree.PartOne.S11d.Facts

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G]

theorem eq_of_commute_of_pow_eq_one {y₀ y₁ : G} (hc : Commute y₀ y₁) {m : ℕ}
    (hcop : Nat.Coprime 7 m) (h0 : y₀ ^ m = 1) (h1 : y₁ ^ m = 1) (hz : (y₀ * y₁⁻¹) ^ 7 = 1) :
    y₀ = y₁ := by
  have hzm : (y₀ * y₁⁻¹) ^ m = 1 := by
    rw [hc.inv_right.mul_pow, h0, inv_pow, h1, inv_one, one_mul]
  have h2 := pow_gcd_eq_one.mpr ⟨hz, hzm⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h2
  exact mul_inv_eq_one.mp h2

namespace Branch

variable [Finite G] {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ} {b : G}
  {S K K' : Subgroup G} {a' : G} {x : G} {lam : ℤ}

theorem false_of_centralizes_c (H : Branch 7 A c L B n b S K K' a') (X : Xdata A c L B x lam)
    (hqL : CFSG.IsQuasisimple L) (hKq : CFSG.IsQuasisimple K) (h7K : ¬ 7 ∣ Nat.card K) {y : G}
    (hyK : y ∈ K) (hyc : y * c = c * y) (hyZ : ¬ ∀ k ∈ K, y * k = k * y) : False := by
  have hyA : ∀ a ∈ A, y * a = a * y := H.commute_A_of_mem_K hKq hyK hyc
  have hyzp : y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute c y from hyc.symm) j).eq
  have hyL : y ∈ Subgroup.normalizer (L : Set G) :=
    H.config.mem_normalizer_L hqL H.witness.b_mem H.witness.b_ne_one hyzp
      (H.commute_b_of_mem_K hyK)
  have hxA : x ∈ Subgroup.normalizer (A : Set G) := X.mem_normalizer_A
  have hy₁K : x * y * x⁻¹ ∈ conjBy x K := conj_mem_conjBy hyK x
  have hy₁A : ∀ a ∈ A, x * y * x⁻¹ * a = a * (x * y * x⁻¹) := by
    intro a ha
    have ha' : x⁻¹ * a * x ∈ A := by
      refine (Subgroup.mem_normalizer_iff.mp hxA (x⁻¹ * a * x)).mpr ?_
      have : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
      rw [this]
      exact ha
    have h1 := hyA _ ha'
    calc x * y * x⁻¹ * a = x * (y * (x⁻¹ * a * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * a * x) * y) * x⁻¹ := by rw [h1]
      _ = a * (x * y * x⁻¹) := by group
  have hzL : y * x * y⁻¹ * x⁻¹ ∈ L := by
    have h1 : y * x * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL x).mp X.mem_L
    exact L.mul_mem h1 (L.inv_mem X.mem_L)
  have hzy : y * x * y⁻¹ * x⁻¹ = y * (x * y * x⁻¹)⁻¹ := by group
  have hzcomm : ∀ β ∈ A, β * (y * x * y⁻¹ * x⁻¹) = (y * x * y⁻¹ * x⁻¹) * β := by
    intro β hβ
    have c1 : Commute β y := (hyA β hβ).symm
    have c2 : Commute β (x * y * x⁻¹) := (hy₁A β hβ).symm
    rw [hzy]
    exact (c1.mul_right c2.inv_right).eq
  have hzB : y * x * y⁻¹ * x⁻¹ ∈ B := by
    rw [← H.config.centralizer_inf_L]
    exact ⟨Subgroup.mem_centralizer_iff.mpr fun β hβ => hzcomm β (H.config.B_le_A hβ), hzL⟩
  have hz7 : (y * x * y⁻¹ * x⁻¹) ^ 7 = 1 := H.config.pow_p_eq_one (H.config.B_le_A hzB)
  have hmcop : Nat.Coprime 7 (orderOf y) := by
    refine (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr fun h => h7K (h.trans ?_)
    have := orderOf_dvd_natCard (⟨y, hyK⟩ : K)
    simpa using this
  have hy0 : y ^ orderOf y = 1 := pow_orderOf_eq_one y
  have hy1 : (x * y * x⁻¹) ^ orderOf y = 1 := conj_pow_eq_one hy0 x
  have hc01 : Commute y (x * y * x⁻¹) := H.comm₀₁ X hKq y hyK _ hy₁K
  have heq : y = x * y * x⁻¹ :=
    eq_of_commute_of_pow_eq_one hc01 hmcop hy0 hy1 (by rw [← hzy]; exact hz7)
  have hyK₁ : y ∈ conjBy x K := by
    rw [heq]
    exact hy₁K
  exact hyZ fun k hk => (H.comm₀₁ X hKq k hk y hyK₁).symm

end Branch

open CFSG.Blueprint in
theorem maximalBranchThree_of (hS : SchreierFor InCatalog)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (h68 : Sec6EightMultipliers) (hQ7 : MovingQuasisimpleSeven) : MaximalBranchThree := by
  intro G _ _ p A c L B n cfg b S K K' a' hW hK hSK hK' ha'A ha'B hrel
  obtain rfl : p = 7 := cfg.p_eq
  have H : Branch 7 A c L B n b S K K' a' := ⟨cfg, hW, hK, hSK, hK', ha'A, ha'B, hrel⟩
  obtain ⟨x, lam, X⟩ := exists_xdata cfg
  have hsetup := cfg.setup
  have hKq : CFSG.IsQuasisimple K := hQ7 hS twoActionInputs_of_S9 G A hsetup K hK.1
  have hqL : CFSG.IsQuasisimple ↥L :=
    (moving_maximal_data_at hS hsetup cfg.L_mem.1 cfg.c_mem cfg.c_ne_one cfg.L_mem.2).1
  have hr7 : localRank 7 G ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank (by norm_num) (by norm_num)).trans H.hev
  have hZ : ¬ 7 ∣ Nat.card (Subgroup.center K) := by
    intro h7
    have := hsetup.1
    have hcat : Catalog (K ⧸ Subgroup.center K) :=
      catalog_quotient_center_of_quasisimple hsetup.2.2.1 hbridge hsetup.2.1 hW.b_ne_one
        H.K_le_centralizer hKq
    have hG3 : CFSG.twoLocalOddRank G ≤ 3 := hsetup.2.2.2.2.1.le
    obtain ⟨h75, -⟩ := h68 G hG3 K 7 (by norm_num) (by norm_num) hKq hcat h7
    omega
  have hout : c ∉ K ⊔ Subgroup.centralizer (K : Set G) :=
    H.c_notMem_sup_centralizer X hKq hZ hr7
  have h7K : ¬ 7 ∣ Nat.card K := H.not_dvd_card_K hKq hZ hout
  obtain ⟨k, hkc, hkZ⟩ := exists_fixed_noncentral hKq hZ (H.A_le_normalizer_K cfg.c_mem)
    (cfg.pow_p_eq_one cfg.c_mem)
  exact H.false_of_centralizes_c X hqL hKq h7K k.2 hkc fun hall =>
    hkZ (Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hall g g.2).symm)

end CFSG.RankThree.PartOne.MB3
