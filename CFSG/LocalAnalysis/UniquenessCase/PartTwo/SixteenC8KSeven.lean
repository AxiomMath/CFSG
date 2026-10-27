module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KE64
import CFSG.Assembly.OrderReductions.InvariantSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem c8k_sylow7_le_c0 {Γ : Type} [Group Γ] [Finite Γ] {B C₀ O : Subgroup Γ}
    (hP : C8P0 B C₀) (hO : O.Normal) (hOB : O ≤ B)
    (h7 : ∀ x ∈ O, ∃ n : ℕ, x ^ 7 ^ n ∈ CFSG.pCore 2 Γ)
    {R : Subgroup Γ} (hRO : R ≤ O) (hR : IsPGroup 7 R) : R ≤ C₀ := by
  obtain ⟨P, _, φ, hφs, hφk, hE64, _⟩ := hP
  obtain ⟨N, hNn, hN64, hL3⟩ := hE64
  haveI := hNn
  haveI : Finite P := Finite.of_surjective φ hφs
  let O' : Subgroup ↥B := O.subgroupOf B
  have hO'n : O'.Normal := hO.subgroupOf B
  let M : Subgroup P := O'.map φ
  have hMn : M.Normal := hO'n.map φ hφs
  have h3 : ∀ m ∈ M, ¬ 3 ∣ orderOf m := by
    intro m hm
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hm
    have hbO : (b : Γ) ∈ O := Subgroup.mem_subgroupOf.mp hb
    obtain ⟨n, hn⟩ := h7 (b : Γ) hbO
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQp : IsPGroup 2 (CFSG.pCore 2 Γ) := CFSG.pCore_isPGroup (p := 2) (G := Γ)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
    have hord : orderOf ((b : Γ) ^ 7 ^ n) ∣ 2 ^ k := by
      rw [← hk]
      exact Subgroup.orderOf_dvd_natCard (CFSG.pCore 2 Γ) hn
    have hy : ((b : Γ) ^ 7 ^ n) ^ 2 ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
    have hbpow : (b : Γ) ^ (7 ^ n * 2 ^ k) = 1 := by
      rw [pow_mul]
      exact hy
    have hbdvd : orderOf (b : Γ) ∣ 7 ^ n * 2 ^ k := orderOf_dvd_of_pow_eq_one hbpow
    have hcop : Nat.Coprime 3 (7 ^ n * 2 ^ k) :=
      ((by norm_num : Nat.Coprime 3 7).pow_right n).mul_right
        ((by norm_num : Nat.Coprime 3 2).pow_right k)
    have hnot3 : ¬ 3 ∣ 7 ^ n * 2 ^ k :=
      fun h => absurd (hcop.eq_one_of_dvd h) (by norm_num)
    have hmvd : orderOf (φ b) ∣ orderOf (b : Γ) := by
      have h := orderOf_map_dvd φ b
      rwa [← Subgroup.orderOf_coe b] at h
    exact fun h3dvd => hnot3 ((h3dvd.trans hmvd).trans hbdvd)
  have hMle : M ≤ N := c8_e64_le_of_no_three hL3 hMn h3
  intro x hxR
  have hxO : x ∈ O := hRO hxR
  have hxB : x ∈ B := hOB hxO
  let b : ↥B := ⟨x, hxB⟩
  have hbO' : b ∈ O' := Subgroup.mem_subgroupOf.mpr hxO
  have hMb : φ b ∈ M := Subgroup.mem_map.mpr ⟨b, hbO', rfl⟩
  have hNb : φ b ∈ N := hMle hMb
  have hsq : (φ b) ^ 2 = 1 := by
    have hN2 : (⟨φ b, hNb⟩ : ↥N) ^ 2 = 1 := by
      obtain ⟨e⟩ := hN64
      apply e.injective
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      rw [nsmul_eq_mul, Pi.mul_apply, Pi.zero_apply]
      simp only [Pi.natCast_apply]
      rw [show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_mul]
    have h := congrArg (Subtype.val) hN2
    simpa using h
  have h2dvd : orderOf (φ b) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  obtain ⟨k, hk⟩ := hR ⟨x, hxR⟩
  have hx7 : x ^ 7 ^ k = 1 := by
    have h := congrArg (Subtype.val) hk
    simpa using h
  have hb7 : b ^ 7 ^ k = 1 := by
    apply Subtype.ext
    simpa using hx7
  have hpow : (φ b) ^ 7 ^ k = 1 := by
    rw [← map_pow, hb7, map_one]
  have h7dvd : orderOf (φ b) ∣ 7 ^ k := orderOf_dvd_of_pow_eq_one hpow
  have hcop : Nat.Coprime (orderOf (φ b)) (7 ^ k) := by
    have h7not : ¬ 7 ∣ orderOf (φ b) := by
      intro h
      have h72 : 7 ∣ 2 := h.trans h2dvd
      norm_num at h72
    exact ((Nat.prime_seven).coprime_iff_not_dvd.mpr h7not).symm.pow_right k
  have h1 : orderOf (φ b) = 1 := hcop.eq_one_of_dvd h7dvd
  have hker : b ∈ φ.ker := MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h1)
  have hbc : b ∈ C₀.subgroupOf B := by
    rw [← hφk]
    exact hker
  exact Subgroup.mem_subgroupOf.mp hbc

theorem c8k_exists_inv_sylow7 {Γ : Type} [Group Γ] [Finite Γ] {O : Subgroup Γ} {d : Γ}
    (hO : O.Normal) (hd : orderOf d = 3) (hQO : CFSG.pCore 2 Γ ≤ O)
    (h7 : ∀ x ∈ O, ∃ n : ℕ, x ^ 7 ^ n ∈ CFSG.pCore 2 Γ) :
    ∃ R : Subgroup Γ, R ≤ O ∧ IsPGroup 7 R ∧ R ⊔ CFSG.pCore 2 Γ = O ∧
      ∀ x ∈ R, d * x * d⁻¹ ∈ R := by
  haveI := hO
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : ¬ 3 ∣ Nat.card ↥O := by
    intro hdiv
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdiv
    obtain ⟨n, hn⟩ := h7 (x : Γ) x.2
    have hord : orderOf ((x : Γ) ^ 7 ^ n) = 3 := by
      have hcop : Nat.Coprime (orderOf (x : Γ)) (7 ^ n) := by
        rw [Subgroup.orderOf_coe x, hx]
        exact (by norm_num : Nat.Coprime 3 7).pow_right n
      rw [hcop.orderOf_pow, Subgroup.orderOf_coe x, hx]
    have hdvd : 3 ∣ Nat.card (CFSG.pCore 2 Γ) := by
      have h := Subgroup.orderOf_dvd_natCard (CFSG.pCore 2 Γ) hn
      rwa [hord] at h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := Γ))
    have h32 : 3 ∣ 2 ^ k := by rwa [hk] at hdvd
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h32) (by norm_num)
  have hA : IsPGroup 3 ↥(Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd]; norm_num)
  obtain ⟨S, hS⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime
    (actor := ↥(Subgroup.zpowers d)) (group := ↥O) 3 7 hA h3
    ((MulAut.conjNormal (H := O)).comp (Subgroup.zpowers d).subtype)
  let R : Subgroup Γ := (S : Subgroup ↥O).map O.subtype
  have hRle : R ≤ O := Subgroup.map_subtype_le (S : Subgroup ↥O)
  have hR7 : IsPGroup 7 R := S.isPGroup'.map O.subtype
  have hRQ : R ⊔ CFSG.pCore 2 Γ = O := by
    apply le_antisymm (sup_le hRle hQO)
    rw [← Subgroup.relIndex_eq_one]
    let m := (R ⊔ CFSG.pCore 2 Γ).relIndex O
    have hdivR : m ∣ R.relIndex O :=
      Subgroup.relIndex_dvd_of_le_left (H := R) (K := R ⊔ CFSG.pCore 2 Γ) (L := O) le_sup_left
    have hdivQ : m ∣ (CFSG.pCore 2 Γ).relIndex O :=
      Subgroup.relIndex_dvd_of_le_left (H := CFSG.pCore 2 Γ) (K := R ⊔ CFSG.pCore 2 Γ)
        (L := O) le_sup_right
    have hRrel : R.relIndex O = S.index := by
      have htop : (⊤ : Subgroup ↥O).map O.subtype = O := by ext y; simp
      have hcomap : Subgroup.comap O.subtype R = (S : Subgroup ↥O) := by
        simp only [R]
        exact Subgroup.comap_map_eq_self_of_injective O.subtype_injective (S : Subgroup ↥O)
      have hstep : (Subgroup.comap O.subtype R).relIndex ⊤ =
          R.relIndex ((⊤ : Subgroup ↥O).map O.subtype) :=
        Subgroup.relIndex_comap (f := O.subtype) (K := (⊤ : Subgroup ↥O)) (H := R)
      rw [htop] at hstep
      rw [hcomap] at hstep
      exact hstep.symm.trans (Subgroup.relIndex_top_right (H := (S : Subgroup ↥O)))
    have hQpow : ∃ k, (CFSG.pCore 2 Γ).relIndex O = 7 ^ k := by
      haveI : ((CFSG.pCore 2 Γ).subgroupOf O).Normal :=
        (CFSG.pCore_normal (p := 2) (G := Γ)).subgroupOf O
      have hquot : IsPGroup 7 (↥O ⧸ (CFSG.pCore 2 Γ).subgroupOf O) := by
        intro q
        obtain ⟨o, rfl⟩ := QuotientGroup.mk'_surjective ((CFSG.pCore 2 Γ).subgroupOf O) q
        obtain ⟨n, hn⟩ := h7 (o : Γ) o.2
        refine ⟨n, ?_⟩
        rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr (by simpa using hn)
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hquot
      exact ⟨k, by simpa [Subgroup.relIndex, Subgroup.index] using hk⟩
    obtain ⟨k, hk⟩ := hQpow
    have h7not : ¬ 7 ∣ m := by
      intro h7m
      apply S.not_dvd_index
      rw [← hRrel]
      exact h7m.trans hdivR
    have hdvd : m ∣ 7 ^ k := by rw [hk] at hdivQ; exact hdivQ
    exact (((Nat.prime_seven).coprime_iff_not_dvd.mpr h7not).symm.pow_right k).eq_one_of_dvd hdvd
  refine ⟨R, hRle, hR7, hRQ, ?_⟩
  intro x hx
  obtain ⟨y, hyS, rfl⟩ := Subgroup.mem_map.mp (show x ∈ (S : Subgroup ↥O).map O.subtype from hx)
  refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal (H := O) d y, ?_, ?_⟩
  · have h := hS ⟨d, Subgroup.mem_zpowers d⟩
    rw [← h]
    exact Subgroup.mem_map.mpr ⟨y, hyS, rfl⟩
  · exact MulAut.conjNormal_apply d y

theorem c8k_not_o_le_b {Γ : Type} [Group Γ] [Finite Γ] {B S C₀ : Subgroup Γ} {d : Γ}
    {ρ : Γ →* ↥(StatedSL 2 (ZMod 7))} {O Z : Subgroup Γ} (conf : C8KConf Γ B S C₀ d)
    (nat : C8KNat Γ d ρ O Z) : ¬ O ≤ B := by
  intro hOB
  haveI : Z.Normal := nat.z_normal
  obtain ⟨R, hRO, hR7, hRQ, hRinv⟩ :=
    c8k_exists_inv_sylow7 nat.normal conf.ctx.d_order (nat.q_le.trans nat.z_le) nat.seven
  have hRC : R ≤ C₀ := c8k_sylow7_le_c0 conf.p0 nat.normal hOB nat.seven hRO hR7
  have hcomm : ∀ x ∈ R, d * x = x * d := conf.c0_cent R hRC hR7 hRinv
  have hH : R ⊔ CFSG.pCore 2 Γ ≤
      (centralizer ({(d : Γ ⧸ Z)} : Set (Γ ⧸ Z))).comap (QuotientGroup.mk' Z) := by
    refine sup_le (fun x hx => ?_) (fun q hq => ?_)
    · rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      show (d : Γ ⧸ Z) * (x : Γ ⧸ Z) = (x : Γ ⧸ Z) * (d : Γ ⧸ Z)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm x hx]
    · have hqZ : q ∈ Z := nat.q_le hq
      have h1 : QuotientGroup.mk' Z q = 1 := (QuotientGroup.eq_one_iff q).mpr hqZ
      rw [Subgroup.mem_comap, h1]
      exact Subgroup.one_mem _
  have hact : ∀ x ∈ O, d * x * d⁻¹ * x⁻¹ ∈ Z := by
    intro x hx
    have hx' := hH (hRQ ▸ hx)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hx'
    have h1 := hx' (d : Γ ⧸ Z) rfl
    rw [← QuotientGroup.eq_one_iff]
    change ((d * x * d⁻¹ * x⁻¹ : Γ) : Γ ⧸ Z) = 1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h2 : (d : Γ ⧸ Z) * (x : Γ ⧸ Z) = (x : Γ ⧸ Z) * (d : Γ ⧸ Z) := h1
    rw [h2]
    group
  have hd1 : ρ d = 1 := (nat.act_one d).mpr hact
  have hdI : d ∈ CFSG.pPrimeCore 3 Γ := nat.ker_le hd1
  have hdvd : 3 ∣ Nat.card (CFSG.pPrimeCore 3 Γ) := by
    have h1 := Subgroup.orderOf_dvd_natCard (CFSG.pPrimeCore 3 Γ) hdI
    rwa [conf.ctx.d_order] at h1
  exact absurd (Nat.Coprime.eq_one_of_dvd (CFSG.pPrimeCore_coprime_card (p := 3) (G := Γ)) hdvd)
    (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
