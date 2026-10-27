module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Holt.General.NoRelevantBasic
public import CFSG.GroupTheory.CoprimeCovering

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Ctx23L.withB0 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) : Ctx23L D Ch :=
  { c with B := c.B0, hB := c.hB0, hle := le_rfl }

@[simp]
theorem Ctx23L.withB0_B {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch) :
    c.withB0.B = c.B0 :=
  rfl

theorem Ctx23L.B0_le_normalizer_of_mem_calC {D : Data G} {Ch : Choice2011 G}
    (h215 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M) :
    c.B0 ≤ Subgroup.normalizer (K : Set G) := by
  let c₀ : Ctx21 D Ch :=
    { c.toCtx23.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl }
  exact h215 h1930 c₀ K hK

theorem Ctx23L.exists_mem_B0_not_mem_centralizer_Z {D : Data G} {Ch : Choice2011 G}
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch)
    (h53 : S23_5_3 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    2 ≤ CFSG.Open.pRank 2 D.Z ∧
      ∀ r : ℕ, r.Prime → r ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1 →
        ∃ b ∈ c.B0, orderOf b = r ∧
          b ∉ Subgroup.centralizer (D.Z : Set G) := by
  classical
  set m := CFSG.Open.pRank 2 D.Z with hm
  have hn3 : 3 ≤ c.n := uc22p20g_hn3_of hE D Ch h207 h1930 c.toCtx23.toCtx21
  have hcase : c.n = m ∨
      (c.L = c.L0 ∧ CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsOmegaMinus (Bar2 c.L) 4 m ∧
        c.n = 2 * m) := by
    simpa [hm] using h52 h1930 c
  obtain ⟨hm2, hmdvd⟩ : 2 ≤ m ∧ m ∣ c.n := by
    rcases hcase with h | ⟨-, -, h⟩
    · exact ⟨by omega, h ▸ dvd_rfl⟩
    · exact ⟨by omega, h ▸ dvd_mul_left _ 2⟩
  refine ⟨hm2, ?_⟩
  intro r hr hrdvd
  have hr_pi : r ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hr, hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) hmdvd)⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨b, hbo⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) r hr_pi.2
  have hboG : orderOf (b : G) = r := by rw [Subgroup.orderOf_coe, hbo]
  refine ⟨(b : G), b.2, hboG, ?_⟩
  rintro hbC
  have hbZ : (b : G) ∈ c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) := ⟨b.2, hbC⟩
  let c₀ : Ctx23L D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  rcases h53 h1930 c₀ c₀.hpi with hbot | ⟨-, hpiZ⟩
  · have hb1 : (b : G) = 1 := by
      have hmem : (b : G) ∈ (⊥ : Subgroup G) := hbot ▸ hbZ
      simpa using hmem
    exact hr.ne_one (by rw [← hboG, hb1, orderOf_one])
  · have hr_Z : r ∈ piSet (c₀.B ⊓ Subgroup.centralizer (D.Z : Set G)) :=
      ⟨hr, by rw [← hboG]; exact Subgroup.orderOf_dvd_natCard _ hbZ⟩
    have hplus : r ∣ 2 ^ m + 1 := (hpiZ ▸ hr_Z).2
    have htwo : r ∣ 2 := by
      have hsub := Nat.dvd_sub hplus hrdvd
      rwa [show (2 ^ m + 1) - (2 ^ m - 1) = 2 by
        have := Nat.one_le_two_pow (n := m); omega] at hsub
    exact (CFSG.GroupTheory.SuzukiTwoGroup.odd_two_pow_sub_one (by omega)).not_two_dvd_nat
      ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp htwo ▸ hrdvd)

theorem mem_uniqueSet_of_isStronglyPEmbedded {M : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) {X : Subgroup G}
    (hX : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q ↥X) : X ∈ uniqueSet M := by
  haveI : Fact q.Prime := ⟨hq⟩
  refine ⟨hX, ?_⟩
  intro g hXg
  by_contra hMg
  have hgM : g ∉ M := by
    intro hg
    apply hMg
    have hmap : M.map (MulAut.conj g).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)
    simpa using hmap
  obtain ⟨k, hk⟩ := hXq.exists_card_eq
  have hk0 : k ≠ 0 := by
    intro hk0
    apply hXne
    exact Subgroup.eq_bot_of_card_eq X (by simpa [hk0] using hk)
  have hqX : q ∣ Nat.card X := by
    rw [hk]
    exact dvd_pow_self q hk0
  let Mg : Subgroup G := M.map (MulAut.conj g).toMonoidHom
  have hXinf : X ≤ M ⊓ Mg := le_inf hX (by simpa [Mg] using hXg)
  have hqinf : q ∣ Nat.card ↥(M ⊓ Mg) :=
    hqX.trans (Subgroup.card_dvd_of_le hXinf)
  exact hstrong.2.2 g hgM (by simpa [Mg] using hqinf)

theorem isSylowOf_map_piBarInf {D : Data G} {K : Subgroup G} (hK : K ∈ calC D.M) :
    CFSG.ABGLocalTools.IsSylowOf 2
      (((D.T ⊓ K).subgroupOf K).map (piBarInf K)) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    uc22p2214_isSylowOf_inf (Q := G) D.sylowM hK.1
  have hTK' : CFSG.ABGLocalTools.IsSylowOf 2 ((D.T ⊓ K).subgroupOf K) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff K]
    rw [Subgroup.map_subgroupOf_eq_of_le hTK.le]
    rw [show (⊤ : Subgroup ↥K).map K.subtype = K from by ext x; simp]
    exact hTK
  have hsurj : Function.Surjective (piBarInf K) := by
    simpa [piBarInf] using
      (QuotientGroup.mk'_surjective (Subgroup.center (BarInf K))).comp
        (QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥K))
  have hmap := CFSG.Holt.General.NoRelevant.isSylowOf_map hTK' (piBarInf K)
  rwa [Subgroup.map_top_of_surjective _ hsurj] at hmap

private theorem pow_conj_mem_of_conj_mem {N : Subgroup G} {x b : G}
    (hbN : b ∈ Subgroup.normalizer (N : Set G))
    (hfix : b * x * b⁻¹ * x⁻¹ ∈ N) :
    ∀ n : ℕ, ∃ n' ∈ N, b ^ n * x * (b ^ n)⁻¹ = n' * x := by
  intro n
  induction n with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨n', hn', hconj⟩ := ih
    refine ⟨(b * n' * b⁻¹) * (b * x * b⁻¹ * x⁻¹), ?_, ?_⟩
    · exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp hbN n').mp hn') hfix
    · calc b ^ (n + 1) * x * (b ^ (n + 1))⁻¹
          = b * (b ^ n * x * (b ^ n)⁻¹) * b⁻¹ := by group
        _ = b * (n' * x) * b⁻¹ := by rw [hconj]
        _ = ((b * n' * b⁻¹) * (b * x * b⁻¹ * x⁻¹)) * x := by group

theorem commutator_zpowers_mem_of_conj_mem {N : Subgroup G} {x b : G}
    (hbN : b ∈ Subgroup.normalizer (N : Set G))
    (hfix : b * x * b⁻¹ * x⁻¹ ∈ N) :
    ∀ r ∈ Subgroup.zpowers b, ⁅x, r⁆ ∈ N := by
  have hbInvN : b⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normalizer (N : Set G)).inv_mem hbN
  have hfixInv : b⁻¹ * x * (b⁻¹)⁻¹ * x⁻¹ ∈ N := by
    have h := (Subgroup.mem_normalizer_iff.mp hbInvN (b * x * b⁻¹ * x⁻¹)⁻¹).mp
      (N.inv_mem hfix)
    simpa [mul_assoc] using h
  intro r hr
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · obtain ⟨n', hn', hconj⟩ := pow_conj_mem_of_conj_mem hbN hfix n
    have hcomm : b ^ (n : ℤ) * x * (b ^ (n : ℤ))⁻¹ * x⁻¹ ∈ N := by
      rw [zpow_natCast, hconj]
      simpa using hn'
    have heq : ⁅x, b ^ (n : ℤ)⁆ =
        (b ^ (n : ℤ) * x * (b ^ (n : ℤ))⁻¹ * x⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact N.inv_mem hcomm
  · obtain ⟨n', hn', hconj⟩ := pow_conj_mem_of_conj_mem hbInvN hfixInv n
    have hcomm : b ^ (-(n : ℤ)) * x * (b ^ (-(n : ℤ)))⁻¹ * x⁻¹ ∈ N := by
      rw [zpow_neg, zpow_natCast, ← inv_pow, hconj]
      simpa using hn'
    have heq : ⁅x, b ^ (-(n : ℤ))⁆ =
        (b ^ (-(n : ℤ)) * x * (b ^ (-(n : ℤ)))⁻¹ * x⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact N.inv_mem hcomm

theorem exists_pow_orderOf_eq_of_coprime_map {H Q : Type} [Group H] [Finite H] [Group Q]
    (φ : H →* Q) {x : H} {r m : ℕ} (hr : r.Prime)
    (hφ : orderOf (φ x) = r) (hm : (x ^ r) ^ m = 1) (hcop : Nat.Coprime m r) :
    ∃ k : ℕ, φ (x ^ k) = φ x ∧ orderOf (x ^ k) = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  set o := orderOf x
  set d := orderOf (x ^ r)
  have hdvd : d ∣ m := orderOf_dvd_of_pow_eq_one hm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm0 | h
    · rw [hm0, Nat.coprime_zero_left] at hcop
      exact (hr.ne_one hcop).elim
    · exact h
  have hd_cop : Nat.Coprime d r := hcop.coprime_dvd_left hdvd
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hd_cop hr.one_lt
  have hrdvd : r ∣ o := by
    have := orderOf_map_dvd φ x
    rwa [hφ] at this
  have hxpow : x ^ (r * m) = 1 := by
    rw [pow_mul]
    exact hm
  have hx0 : o ≠ 0 := by
    have hpos : 0 < o :=
      Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hxpow) (Nat.mul_pos hr.pos hmpos)
    exact hpos.ne'
  have hd_eq : d = o / r := by
    change orderOf (x ^ r) = orderOf x / r
    rw [orderOf_pow, Nat.gcd_eq_right hrdvd]
  have hdord : orderOf (x ^ d) = r := by
    rw [hd_eq]
    exact orderOf_pow_orderOf_div hx0 hrdvd
  have hrj : Nat.Coprime r j := by
    refine (hr.coprime_iff_not_dvd).mpr fun hrj => ?_
    have h0 : d * j % r = 0 := Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left hrj d)
    omega
  refine ⟨d * j, ?_, ?_⟩
  · rw [map_pow, ← pow_mod_orderOf, hφ, hj, pow_one]
  · have hdj : Nat.Coprime (orderOf (x ^ d)) j := hdord.symm ▸ hrj
    rw [pow_mul, hdj.orderOf_pow, hdord]

private theorem exists_mul_mem_inf_centralizer_of_pCore {K : Subgroup G} {b x : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b))
    (hxK : x ∈ K) (hfix : b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    ∃ y : ↥K, (y : G) ∈ Subgroup.centralizer ({b} : Set G) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) y =
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨x, hxK⟩ : ↥K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  let N : Subgroup G := CFSG.Open.pCoreOf 2 K
  let R : Subgroup G := Subgroup.zpowers b
  have hNX : N ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  haveI hchar : (CFSG.pCore 2 ↥K).Characteristic :=
    CFSG.LieType.BorelTits.pCore_characteristic 2
  have hNnormal : (N.subgroupOf K).Normal := by
    rw [show N = CFSG.Open.pCoreOf 2 K from rfl, CFSG.openPCoreOf_subgroupOf]
    infer_instance
  have hRnorm : R ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.zpowers_le]
    exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 ↥K)) hbN
  have hN2 : IsPGroup 2 N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  haveI : Group.IsNilpotent ↥N := hN2.isNilpotent
  have hsolv : Group.IsSolvable ↥N := inferInstance
  have hcop : Nat.Coprime (Nat.card N) (Nat.card R) := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk, Nat.card_zpowers]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hbodd)
  have hxR : ∀ r ∈ R, ⁅x, r⁆ ∈ N := by
    refine commutator_zpowers_mem_of_conj_mem (N := N) ?_ ?_
    · exact hRnorm (Subgroup.mem_zpowers b)
    · simpa [N] using hfix
  obtain ⟨n, hnN, hyinf⟩ :=
    CFSG.GroupTheory.exists_mul_mem_inf_centralizer_of_commutator_mem
      (X := K) (N := N) (R := R) hNX hNnormal hRnorm hsolv hcop hxK hxR
  have hncore : (⟨n, hNX hnN⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
    (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) ⟨n, hNX hnN⟩).mp (by simpa [N] using hnN)
  let y0 : ↥K := ⟨x * n, (Subgroup.mem_inf.mp hyinf).1⟩
  refine ⟨y0, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyinf).2) b
      (Subgroup.mem_zpowers b)).symm
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    have hconj : (⟨x, hxK⟩ : ↥K) * ⟨n, hNX hnN⟩ * (⟨x, hxK⟩ : ↥K)⁻¹ ∈
        CFSG.pCore 2 ↥K :=
      (CFSG.pCore_normal (G := ↥K)).conj_mem _ hncore _
    convert hconj using 1
    ext
    simp [y0, div_eq_mul_inv, mul_assoc]

theorem exists_mem_inf_centralizer_of_bar_fixed {K : Subgroup G} {b x : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hbodd : Odd (orderOf b))
    (hxK : x ∈ K) (hfix : b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hxr : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨x, hxK⟩ : ↥K)) = r) :
    ∃ y : ↥K, (y : G) ∈ Subgroup.centralizer ({b} : Set G) ∧
      orderOf (y : G) = r ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥K) y =
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨x, hxK⟩ : ↥K) := by
  obtain ⟨y0, hy0C, hy0image⟩ :=
    exists_mul_mem_inf_centralizer_of_pCore hbN hbodd hxK hfix
  have hy0bar : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥K) y0) = r := by
    rw [hy0image, hxr]
  have hy0r_mem : y0 ^ r ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (y0 ^ r) = 1
    rw [map_pow, ← hy0bar, pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).exists_card_eq
  have hkill : (y0 ^ r) ^ (2 ^ k) = 1 := by
    have h := pow_card_eq_one' (x := (⟨y0 ^ r, hy0r_mem⟩ : ↥(CFSG.pCore 2 ↥K)))
    rw [hk] at h
    simpa using congrArg Subtype.val h
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hcop2 : Nat.Coprime (2 ^ k) r :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hrodd)
  obtain ⟨j, hjmap, hjord⟩ :=
    exists_pow_orderOf_eq_of_coprime_map
      (φ := QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (x := y0) hr hy0bar hkill hcop2
  refine ⟨y0 ^ j, ?_, ?_, ?_⟩
  · simpa using (Subgroup.centralizer ({b} : Set G)).pow_mem hy0C j
  · rw [Subgroup.orderOf_coe, hjord]
  · rw [hjmap, hy0image]





end CFSG.LocalAnalysis.UniquenessCase.UC22
