module

public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Quot
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Act

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

open CFSG CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

theorem normal_subgroupOf_of_le_normalizer {Y C : Subgroup G}
    (hYC : Y ≤ Subgroup.normalizer (C : Set G)) : (C.subgroupOf Y).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hYC g.2) (n : G)).mp hn⟩

theorem rho_eq_one_of_mem {Y C : Subgroup G} (hY3 : Y = oPrimeResidualOf 3 Y)
    (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) (hCY : C ≤ Subgroup.normalizer (Y : Set G))
    (hYC : Y ≤ Subgroup.normalizer (C : Set G)) (hnot : ¬ Y ≤ C)
    (c : ↥(Subgroup.normalizer (Y : Set G))) (hc : (c : G) ∈ C) : rho Y c = 1 := by
  haveI : (C.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hYC
  haveI : (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (C.subgroupOf Y)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases quasi_normal_le_center_or_eq_top hq
      (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (C.subgroupOf Y)) with hle | htop
  · refine mulAut_eq_one_of_central hq (rho Y c) ?_
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [rho_mk]
    have hYc : (c : G) * (y : G) * (c : G)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp c.2 (y : G)).mp y.2
    have hCmem : (c : G) * (y : G) * (c : G)⁻¹ * (y : G)⁻¹ ∈ C := by
      have hy : (y : G) * (c : G)⁻¹ * (y : G)⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hYC y.2) (c : G)⁻¹).mp (inv_mem hc)
      rw [show (c : G) * (y : G) * (c : G)⁻¹ * (y : G)⁻¹
          = (c : G) * ((y : G) * (c : G)⁻¹ * (y : G)⁻¹) by group]
      exact mul_mem hc hy
    have hmem : (⟨(c : G) * (y : G) * (c : G)⁻¹, hYc⟩ * y⁻¹ : ↥Y) ∈ C.subgroupOf Y :=
      Subgroup.mem_subgroupOf.mpr hCmem
    have hmapmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) hmem
    have hval : QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
          (⟨(c : G) * (y : G) * (c : G)⁻¹, hYc⟩ * y⁻¹ : ↥Y)
        = QuotientGroup.mk (⟨(c : G) * (y : G) * (c : G)⁻¹, hYc⟩ : ↥Y) * (QuotientGroup.mk y)⁻¹ := by
      rw [map_mul, map_inv]
      rfl
    have key := hle hmapmem
    rw [hval] at key
    exact key
  · exfalso
    apply hnot
    have h3 : ∀ x : ↥Y, (∃ k : ℕ, x ^ (3 ^ k) = 1) → x ∈ C.subgroupOf Y := by
      rintro x ⟨k, hk⟩
      have hx : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) x ∈
          Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (C.subgroupOf Y) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hx
      have hmx' : m⁻¹ * x ∈ CFSG.pCore 2 ↥Y := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hmx
        exact QuotientGroup.eq.mp hmx
      obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨m⁻¹ * x, hmx'⟩
      have ho : (m⁻¹ * x) ^ (2 ^ j) = 1 := by
        have := congrArg Subtype.val hj
        simpa using this
      have hπm : QuotientGroup.mk' (C.subgroupOf Y) m = 1 :=
        (QuotientGroup.eq_one_iff m).mpr hm
      have hxo : QuotientGroup.mk' (C.subgroupOf Y) x
          = QuotientGroup.mk' (C.subgroupOf Y) (m⁻¹ * x) := by
        rw [map_mul, map_inv, hπm, inv_one, one_mul]
      have h1 : (QuotientGroup.mk' (C.subgroupOf Y) x) ^ (3 ^ k) = 1 := by
        rw [← map_pow, hk, map_one]
      have h2 : (QuotientGroup.mk' (C.subgroupOf Y) x) ^ (2 ^ j) = 1 := by
        rw [hxo, ← map_pow, ho, map_one]
      have hcop : Nat.Coprime (3 ^ k) (2 ^ j) := Nat.Coprime.pow k j (by norm_num)
      have hg : (QuotientGroup.mk' (C.subgroupOf Y) x) ^ (Nat.gcd (3 ^ k) (2 ^ j)) = 1 :=
        pow_gcd_eq_one.mpr ⟨h1, h2⟩
      rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
      exact (QuotientGroup.eq_one_iff x).mp hg
    have hsub : CFSG.GH74.GLS.oPrimeResidual 3 ↥Y ≤ C.subgroupOf Y :=
      (Subgroup.closure_le _).mpr fun x hx => h3 x hx
    have hmap : oPrimeResidualOf 3 Y ≤ C := Subgroup.map_le_iff_le_comap.mpr hsub
    exact hY3.trans_le hmap

private theorem glue_pow_mul_mem {C : Subgroup G} {y c : G}
    (hy : y ∈ Subgroup.normalizer (C : Set G)) (hc : c ∈ C) (j : ℕ) :
    ∃ d ∈ C, (y * c) ^ j = y ^ j * d := by
  induction j with
  | zero => exact ⟨1, C.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨d, hd, hdk⟩ := ih
    refine ⟨y⁻¹ * d * y * c, C.mul_mem ?_ hc, ?_⟩
    · refine (Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * d * y)).mpr ?_
      have e : y * (y⁻¹ * d * y) * y⁻¹ = d := by group
      rw [e]
      exact hd
    · rw [pow_succ (y * c) k, hdk, pow_succ y k]
      simp only [mul_assoc, mul_inv_cancel_left]

private theorem glue_pow_mem_pCoreOf {Y : Subgroup G} {y : G} (hyY : y ∈ Y)
    (hcen : (QuotientGroup.mk (⟨y, hyY⟩ : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    y ^ Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∈ CFSG.Open.pCoreOf 2 Y := by
  have hpow : (QuotientGroup.mk (⟨y, hyY⟩ : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y) ^
      Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) = 1 := by
    have h : (⟨_, hcen⟩ : ↥(Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))) ^
        Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h
  have hq1 : ((⟨y, hyY⟩ : ↥Y) ^ Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))) ∈
      CFSG.pCore 2 ↥Y :=
    (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact hpow)
  exact Subgroup.mem_map_of_mem Y.subtype hq1

private theorem glue_mem_of_pow_mem {C : Subgroup G} {s : G} {m k : ℕ}
    (hcop : Nat.Coprime m (2 ^ k)) (hk : s ^ 2 ^ k = 1) (hsm : s ^ m ∈ C) : s ∈ C := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have h1 : s ^ (u * (m : ℤ) + v * ((2 ^ k : ℕ) : ℤ)) = s := by
    rw [huv, zpow_one]
  rw [zpow_add, zpow_mul', zpow_mul', zpow_natCast, zpow_natCast, hk, one_zpow, mul_one] at h1
  rw [← h1]
  exact zpow_mem hsm u

theorem glue_G {Y S C : Subgroup G} (hSY : S ≤ Subgroup.normalizer (Y : Set G)) (hS2 : IsPGroup 2 S)
    (hY3 : Y = oPrimeResidualOf 3 Y) (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hCY : C ≤ Subgroup.normalizer (Y : Set G)) (hYC : Y ≤ Subgroup.normalizer (C : Set G))
    (hSC : S ≤ Subgroup.normalizer (C : Set G)) (hnot : ¬ Y ≤ C)
    (hO2 : CFSG.Open.pCoreOf 2 Y ≤ C)
    (hInn : ∀ n : ↥(Subgroup.normalizer (Y : Set G)), (n : G) ∈ S → rho Y n ∈ innQ Y →
      rho Y n = 1) :
    ∀ s ∈ S, ∀ y ∈ Y, ∀ c ∈ C, s = y * c → s ∈ C := by
  intro s hsS y hyY c hcC hsyc
  have hyC : y ∈ Subgroup.normalizer (C : Set G) := hYC hyY
  have hsN : s ∈ Subgroup.normalizer (Y : Set G) := hSY hsS
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := hCY hcC
  have hyN : y ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hyY
  have hfac : (⟨s, hsN⟩ : ↥(Subgroup.normalizer (Y : Set G))) = ⟨y, hyN⟩ * ⟨c, hcN⟩ :=
    Subtype.ext hsyc
  have hrho_c : rho Y ⟨c, hcN⟩ = 1 := rho_eq_one_of_mem hY3 hq hCY hYC hnot ⟨c, hcN⟩ hcC
  have hrho_s : rho Y ⟨s, hsN⟩ =
      MulAut.conj (QuotientGroup.mk (⟨y, hyY⟩ : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rw [hfac, map_mul, hrho_c, mul_one]
    exact rho_inner Y ⟨y, hyY⟩
  have hmem : rho Y ⟨s, hsN⟩ ∈ innQ Y := by
    rw [hrho_s]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hconj : MulAut.conj (QuotientGroup.mk (⟨y, hyY⟩ : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y) = 1 := by
    rw [← hrho_s]
    exact hInn ⟨s, hsN⟩ hsS hmem
  have hcen := (conj_eq_one_iff _).mp hconj
  have hymC : y ^ Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∈ C :=
    hO2 (glue_pow_mem_pCoreOf hyY hcen)
  obtain ⟨d, hd, hdk⟩ :=
    glue_pow_mul_mem hyC hcC (Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)))
  rw [← hsyc] at hdk
  have hsm : s ^ Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∈ C := by
    rw [hdk]
    exact C.mul_mem hymC hd
  obtain ⟨k, hk⟩ := hS2 ⟨s, hsS⟩
  have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (odd_card_center_quot Y))
  exact glue_mem_of_pow_mem hcop hk' hsm


end CFSG.RankThree.PartTwo.Sec15.F153L3C2
