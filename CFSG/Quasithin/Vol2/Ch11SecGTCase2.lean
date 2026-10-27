module

public import CFSG.Quasithin.Vol2.Ch11SecGTL1
public import CFSG.Quasithin.Vol2.Ch11SecGFacts2
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem not_dvd_180_mul {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (j : ℕ) : ¬ p ∣ 180 * 2 ^ j := by
  intro h
  have h180 : (180 : ℕ) = 2 ^ 2 * 3 ^ 2 * 5 := by norm_num
  rw [h180] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
        omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega

theorem exists_orderOf_eq_of_isPSL {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (h : IsPSL 2 p 1 X) : ∃ x : X, orderOf x = p := by
  obtain ⟨-, Kf, _, _, hKf, ⟨eX⟩⟩ := h
  obtain ⟨y, hy⟩ := SL2.exists_orderOf_eq hp (by rw [hKf, pow_one])
  let e' : X ≃* PSL(2, Kf) :=
    eX.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 Kf).symm
  exact ⟨e'.symm y, by rw [MulEquiv.orderOf_eq, hy]⟩

theorem cBar_eq_bot_of_isPSL [Finite G] {K L₁ Y : Subgroup G} (hKK : ⁅K, K⁆ = K)
    (hL : L₁ ≤ K) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* SL(2, F)) (hcl : CFSG.Quasithin.conjClosure L₁ K = K)
    (hKY : K ≤ Subgroup.normalizer (Y : Set G))
    (hCL : K ⊓ Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (L₁ : Set G))
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (hPSL : IsPSL 2 p 1 (Bar.KBar K)) :
    Bar.cBar K Y = ⊥ := by
  have hs : IsSimpleGroup (Bar.KBar K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hPSL).2
  have : (Bar.cBar K Y).Normal := Bar.cBar_normal hKY
  rcases hs.eq_bot_or_eq_top_of_normal (Bar.cBar K Y) with h | h
  · exact h
  exfalso
  have hLn : ((Bar.rhoL hL).range).Normal := ⟨fun n hn g => by
    obtain ⟨l, rfl⟩ := hn
    exact Bar.mem_range_of_mem_cBar hL hCL (by rw [h]; exact Subgroup.mem_top g) l⟩
  rcases hs.eq_bot_or_eq_top_of_normal (Bar.rhoL hL).range with hL1 | hL1
  · have htop : (⊤ : Subgroup (Bar.KBar K)) ≤ Subgroup.center (Bar.KBar K) := by
      refine Bar.le_center_of_commute hL hcl (fun n _ l hl => ?_)
      have h1 : Bar.rhoL hL ⟨l, hl⟩ = 1 := by
        rw [← Subgroup.mem_bot, ← hL1]
        exact ⟨⟨l, hl⟩, rfl⟩
      change n * Bar.rhoL hL ⟨l, hl⟩ = Bar.rhoL hL ⟨l, hl⟩ * n
      rw [h1, mul_one, one_mul]
    have hcomm : ⁅(⊤ : Subgroup (Bar.KBar K)), (⊤ : Subgroup (Bar.KBar K))⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact (Subgroup.mem_center_iff.mp (htop (Subgroup.mem_top x)) y)
    rw [Bar.commutator_top_eq_top hKK] at hcomm
    obtain ⟨x, hx⟩ := exists_ne (1 : Bar.KBar K)
    exact hx (by
      have : x ∈ (⊥ : Subgroup (Bar.KBar K)) := hcomm ▸ Subgroup.mem_top x
      exact Subgroup.mem_bot.mp this)
  · obtain ⟨x₀, hx₀⟩ := exists_orderOf_eq_of_isPSL hp hPSL
    obtain ⟨l, hl⟩ : x₀ ∈ (Bar.rhoL hL).range := by
      rw [hL1]
      exact Subgroup.mem_top x₀
    have hs180 := SL2.pow_180_eq_one hF (e (QuotientGroup.mk' (CFSG.pCore 2 ↥L₁) l))
    have hlP : l ^ 180 ∈ CFSG.pCore 2 ↥L₁ := by
      rw [← map_pow, ← map_pow] at hs180
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L₁) (l ^ 180) = 1 :=
        e.injective (hs180.trans (map_one e).symm)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup ⟨_, hlP⟩
    have hl1 : l ^ (180 * 2 ^ j) = 1 := by
      rw [pow_mul]
      simpa using congrArg Subtype.val hj
    have hx1 : x₀ ^ (180 * 2 ^ j) = 1 := by
      rw [← hl, ← map_pow, hl1, map_one]
    have hdvd := orderOf_dvd_of_pow_eq_one hx1
    rw [hx₀] at hdvd
    exact not_dvd_180_mul hp (by omega) j hdvd

theorem mem_pCoreOf_of_case2 [Finite G] {H K T L₁ Y : Subgroup G} {a y₀ : G}
    (hInv : FactL2pInvol) (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hT : QuasithinUnique.IsSylowTwoOf T H) (hKT : K ⊔ T = H) (hKK : ⁅K, K⁆ = K)
    (hL : L₁ ≤ K) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* SL(2, F)) (hcl : CFSG.Quasithin.conjClosure L₁ K = K)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G)) (hY : IsElemAbelian 2 Y)
    (hCL : K ⊓ Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (L₁ : Set G))
    (ha : a ∈ H) {n : ℕ} (han : a ^ 2 ^ n = 1) (hy₀ : y₀ ∈ Y)
    (htr : ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ = 1 ∨ a * y * a⁻¹ * y⁻¹ = y₀)
    (ha2 : a ^ 2 ∈ Subgroup.centralizer (Y : Set G)) {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (hp17 : p ≠ 17) (hPSL : IsPSL 2 p 1 (Bar.KBar K)) : a ∈ pCoreOf 2 H := by
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) := hKH.trans hHY
  have haK : a ∈ Subgroup.normalizer (K : Set G) := hHK ha
  have haY : a ∈ Subgroup.normalizer (Y : Set G) := hHY ha
  have hC := cBar_eq_bot_of_isPSL hKK hL hF e hcl hKY hCL hp hp11 hPSL
  have hα2 : (Bar.aut K ⟨a, haK⟩) ^ 2 = 1 := by
    have ha2K : a ^ 2 ∈ Subgroup.normalizer (K : Set G) := pow_mem haK 2
    have h1 : (Bar.aut K ⟨a, haK⟩) ^ 2 = Bar.aut K ⟨a ^ 2, ha2K⟩ := by
      rw [← map_pow]
      rfl
    rw [h1]
    ext x
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.one_apply]
    have hmem : ((⟨a ^ 2 * z * (a ^ 2)⁻¹ * z⁻¹, Bar.commK_mem ha2K hz⟩ : ↥K) : Bar.KBar K) ∈
        Bar.cBar K Y := by
      apply Bar.mk_mem_cBar
      have e1 : a ^ 2 * z * (a ^ 2)⁻¹ * z⁻¹ = a ^ 2 * (z * (a ^ 2)⁻¹ * z⁻¹) := by group
      change a ^ 2 * z * (a ^ 2)⁻¹ * z⁻¹ ∈ Subgroup.centralizer (Y : Set G)
      rw [e1]
      exact mul_mem ha2 (conj_mem_centralizer (hKY hz) (inv_mem ha2))
    rw [hC, Subgroup.mem_bot, Bar.mk_commK ha2K hz] at hmem
    exact mul_inv_eq_one.mp hmem
  by_cases hα1 : Bar.aut K ⟨a, haK⟩ = 1
  · exact mem_pCoreOf_of_comm_mem hKH hHK hT hKT ha han (Bar.comm_mem_of_aut_eq_one hα1)
  exfalso
  obtain ⟨x, hx1, hαx, r, hr, hr5, hxr⟩ :=
    hInv (Bar.KBar K) p hp hp11 hp17 hPSL (Bar.aut K ⟨a, haK⟩) hα1 hα2
  obtain ⟨m, hm⟩ := hr.odd_of_ne_two (by omega)
  obtain ⟨⟨z, hz⟩, hzx⟩ := QuotientGroup.mk_surjective (x ^ (m + 1))
  have hval : ((⟨a * z * a⁻¹ * z⁻¹, Bar.commK_mem haK hz⟩ : ↥K) : Bar.KBar K) = x⁻¹ := by
    rw [Bar.mk_commK haK hz, hzx, map_pow, hαx, inv_pow, ← mul_inv_rev, ← pow_add,
      show m + 1 + (m + 1) = r + 1 by omega, pow_succ, hxr, one_mul]
  have hxr' : ((⟨a * z * a⁻¹ * z⁻¹, Bar.commK_mem haK hz⟩ : ↥K) : Bar.KBar K) ^ r = 1 := by
    rw [hval, inv_pow, hxr, inv_one]
  have hprimes : ∀ s : ℕ, s.Prime → s ∣ r → 5 ≤ s := fun s hs hsr => by
    rw [(Nat.prime_dvd_prime_iff_eq hs hr).mp hsr]
    exact hr5
  have hxC := Bar.commK_mem_cBar hY hKY haY haK hy₀ htr ha2 hz hr.pos hprimes hxr'
  rw [hC, Subgroup.mem_bot, hval, inv_eq_one] at hxC
  exact hx1 hxC

end CFSG.Quasithin.Vol2.Ch11.SecG
