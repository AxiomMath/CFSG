module

public import CFSG.Quasithin.Background.E1Sec3
public import CFSG.Quasithin.Background.E1Residual

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_of_pow_mem_of_coprime {N : Subgroup G} {x : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : x ^ a ∈ N) (hb : x ^ b ∈ N) : x ∈ N := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one] at h
  have e : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b = 1 := by
      simpa using h.symm
    rw [this, zpow_one]
  rw [e]
  exact N.mul_mem (N.zpow_mem ha _) (N.zpow_mem hb _)

theorem mem_of_pow_mem_two_p {N : Subgroup G} {x : G} {p k j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : x ^ p ^ k ∈ N) (h2 : x ^ 2 ^ j ∈ N) : x ∈ N :=
  mem_of_pow_mem_of_coprime (Nat.Coprime.pow k j
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)) h1 h2

section Residual

variable [Finite G]

theorem twoResidual_eq_map_top (K : Subgroup G) :
    twoResidual K = (twoResidual (⊤ : Subgroup ↥K)).map K.subtype := by
  set M : Subgroup ↥K := twoResidual (⊤ : Subgroup ↥K) with hM
  have hMnorm : Subgroup.normalizer (M : Set ↥K) = ⊤ := top_le_iff.mp (le_normalizer_twoResidual ⊤)
  refine le_antisymm ?_ ?_
  · refine twoResidual_le_of_isTwoQuotient (Subgroup.map_subtype_le _) ?_ ?_
    · intro x hx
      exact Subgroup.le_normalizer_map K.subtype
        (Subgroup.mem_map_of_mem K.subtype (show (⟨x, hx⟩ : ↥K) ∈ Subgroup.normalizer (M : Set ↥K)
          from hMnorm ▸ Subgroup.mem_top _))
    · intro y hy
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup ↥K) ⟨y, hy⟩ (Subgroup.mem_top _)
      exact ⟨k, ⟨_, hk, by simp⟩⟩
  · have hN : (twoResidual K).subgroupOf K ≥ M := by
      refine twoResidual_le_of_isTwoQuotient (le_top) ?_ ?_
      · intro x _
        rw [Subgroup.mem_normalizer_iff]
        intro w
        simp only [Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual K x.2) (w : G))
      · intro y _
        obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient K y.1 y.2
        exact ⟨k, by simpa [Subgroup.mem_subgroupOf] using hk⟩
    calc M.map K.subtype ≤ ((twoResidual K).subgroupOf K).map K.subtype := Subgroup.map_mono hN
      _ = twoResidual K := Subgroup.map_subgroupOf_eq_of_le (twoResidual_le K)

theorem map_twoResidual {G' : Type*} [Group G'] [Finite G'] (f : G →* G') (J : Subgroup G) :
    (twoResidual J).map f = twoResidual (J.map f) := by
  refine le_antisymm ?_ ?_
  · set N' := twoResidual (J.map f) with hN'
    have h1 : twoResidual J ≤ J ⊓ N'.comap f := by
      refine twoResidual_le_of_isTwoQuotient inf_le_left ?_ ?_
      · intro j hj
        rw [Subgroup.mem_normalizer_iff]
        intro w
        have hjb : f j ∈ J.map f := Subgroup.mem_map_of_mem f hj
        have h1 := Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual (J.map f) hjb) (f w)
        simp only [Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
        constructor
        · rintro ⟨hwJ, hw⟩
          exact ⟨J.mul_mem (J.mul_mem hj hwJ) (J.inv_mem hj), h1.mp hw⟩
        · rintro ⟨hwJ, hw⟩
          refine ⟨?_, h1.mpr hw⟩
          have := J.mul_mem (J.mul_mem (J.inv_mem hj) hwJ) hj
          simpa [mul_assoc] using this
      · intro y hy
        obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (J.map f) (f y) (Subgroup.mem_map_of_mem f hy)
        refine ⟨k, Subgroup.mem_inf.mpr ⟨J.pow_mem hy _, ?_⟩⟩
        show f (y ^ 2 ^ k) ∈ N'
        rw [map_pow]
        exact hk
    rintro _ ⟨y, hy, rfl⟩
    exact (h1 hy).2
  · refine twoResidual_le_of_isTwoQuotient (Subgroup.map_mono (twoResidual_le J)) ?_ ?_
    · rintro _ ⟨j, hj, rfl⟩
      exact Subgroup.le_normalizer_map f ⟨j, le_normalizer_twoResidual J hj, rfl⟩
    · rintro _ ⟨j, hj, rfl⟩
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient J j hj
      exact ⟨k, ⟨_, hk, by rw [map_pow]⟩⟩

theorem twoResidual_mono {U V : Subgroup G} (h : U ≤ V) : twoResidual U ≤ twoResidual V := by
  have h1 : twoResidual U ≤ U ⊓ twoResidual V := by
    refine twoResidual_le_of_isTwoQuotient inf_le_left ?_ ?_
    · exact le_normalizer_inf_of_le_normalizer (h.trans (le_normalizer_twoResidual V))
    · intro y hy
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient V y (h hy)
      exact ⟨k, U.pow_mem hy _, hk⟩
  exact h1.trans inf_le_right

theorem twoResidual_sup_eq {I S : Subgroup G} (hS : S ≤ I) :
    twoResidual (twoResidual I ⊔ S) = twoResidual I := by
  refine le_antisymm ?_ ?_
  · refine twoResidual_le_of_isTwoQuotient le_sup_left
      ((sup_le (twoResidual_le I) hS).trans (le_normalizer_twoResidual I)) ?_
    intro y hy
    exact twoResidual_isTwoQuotient I y ((sup_le (twoResidual_le I) hS) hy)
  · calc twoResidual I = twoResidual (twoResidual I) := (twoResidual_twoResidual I).symm
      _ ≤ twoResidual (twoResidual I ⊔ S) := twoResidual_mono le_sup_left

end Residual

theorem isSylowIn_two_of_sup_inf [Finite G] {N S : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) (hS2 : IsPGroup 2 S)
    (h : IsSylowIn 2 (S ⊓ N) N) : IsSylowIn 2 S (N ⊔ S) := by
  refine ⟨le_sup_right, hS2, ?_⟩
  have := B6.relIndex_inf_eq_relIndex_sup hSN
  have e : S ⊔ N = N ⊔ S := sup_comm S N
  rw [e] at this
  rw [← this]
  exact h.not_dvd_relIndex

section OTwoP

theorem le_oTwoP_of_series {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    {N R : Subgroup Q} [N.Normal] [R.Normal] (hN : IsPGroup 2 N)
    (hp : ∀ x ∈ R, ∃ k : ℕ, x ^ p ^ k ∈ N) : R ≤ oTwoP Q p := by
  have hN2 : N ≤ CFSG.Open.pCore 2 Q := CFSG.LieType.BorelTits.le_pCore 2 inferInstance hN
  have hpg : IsPGroup p (R.map (QuotientGroup.mk' (CFSG.Open.pCore 2 Q))) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    obtain ⟨k, hk⟩ := hp x hx
    refine ⟨k, Subtype.ext ?_⟩
    show (y : Q ⧸ CFSG.Open.pCore 2 Q) ^ p ^ k = 1
    rw [← hxy, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hN2 hk)
  have hnorm : (R.map (QuotientGroup.mk' (CFSG.Open.pCore 2 Q))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  exact fun x hx => CFSG.LieType.BorelTits.le_pCore p hnorm hpg (Subgroup.mem_map_of_mem _ hx)

theorem exists_pow_mem_of_mem_oTwoP {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    {m : Q} (hm : m ∈ oTwoP Q p) : ∃ k : ℕ, m ^ p ^ k ∈ CFSG.Open.pCore 2 Q := by
  have hm' : (QuotientGroup.mk' (CFSG.Open.pCore 2 Q) m) ∈
      CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) := hm
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup p) ⟨_, hm'⟩
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  simpa using congrArg Subtype.val hk

theorem oTwoP_eq_of_series {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {R : Subgroup Q} [R.Normal] (hNR : CFSG.Open.pCore 2 Q ≤ R)
    (hpow : ∀ x ∈ R, ∃ k : ℕ, x ^ p ^ k ∈ CFSG.Open.pCore 2 Q)
    (h2 : ∀ q : Q, ∃ k : ℕ, q ^ 2 ^ k ∈ R) : oTwoP Q p = R := by
  refine le_antisymm (fun x hx => ?_) (le_oTwoP_of_series
    (CFSG.LieType.BorelTits.pCore_isPGroup 2) hpow)
  obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_oTwoP hx
  obtain ⟨j, hj⟩ := h2 x
  exact mem_of_pow_mem_two_p hp.out hp2 (hNR hk) hj

theorem card_barO2_eq_relIndex {Q : Type*} [Group Q] (B : Subgroup Q) :
    Nat.card (barO2 Q B) = (CFSG.Open.pCore 2 Q).relIndex B := by
  have := Subgroup.relIndex_ker (K := B) (QuotientGroup.mk' (CFSG.Open.pCore 2 Q))
  rw [QuotientGroup.ker_mk'] at this
  exact this.symm

end OTwoP

@[expose] def EOneAmb (S A : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ R : Subgroup G, R ≤ S ∧ S ≤ Subgroup.normalizer (R : Set G) ∧
    pCoreOf 2 S ≤ R ∧ (∀ x ∈ R, ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 S) ∧
    (∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k ∈ R) ∧ R ≠ pCoreOf 2 S ∧
    R ≤ ⁅R, A⁆ ⊔ pCoreOf 2 S ∧ (pCoreOf 2 S).relIndex A = 2

section EOneAmb

variable [Finite G]

theorem eOneAmb_of_eOne {S A : Subgroup G} (hAS : A ≤ S) (h : EOne ↥S (A.subgroupOf S)) :
    EOneAmb S A := by
  obtain ⟨p, hp, hp2, ha, hb1, hb2, hb3⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  set N := CFSG.Open.pCore 2 ↥S with hN
  set M := oTwoP ↥S p with hM
  have hMnorm : Subgroup.normalizer (M : Set ↥S) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hNM : N ≤ M := fun n hn => by
    show ((n : ↥S) : ↥S ⧸ N) ∈ CFSG.Open.pCore p (↥S ⧸ N)
    rw [(QuotientGroup.eq_one_iff n).mpr hn]
    exact Subgroup.one_mem _
  have hpC : CFSG.Open.pCore p (↥S ⧸ N) = M.map (QuotientGroup.mk' N) :=
    (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _).symm
  have hBmap : (A.subgroupOf S).map S.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAS
  refine ⟨p, hp, hp2, M.map S.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact Subgroup.le_normalizer_map S.subtype
      (Subgroup.mem_map_of_mem S.subtype (show (⟨s, hs⟩ : ↥S) ∈ Subgroup.normalizer (M : Set ↥S)
        from hMnorm ▸ Subgroup.mem_top _))
  · exact Subgroup.map_mono hNM
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_oTwoP hm
    exact ⟨k, ⟨m ^ p ^ k, hk, by simp⟩⟩
  · intro s hs
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_pCore (M := M) (fun q => by
      have hq : q ∈ oTwoPTwo ↥S p := by rw [ha]; exact Subgroup.mem_top q
      exact hq) ⟨s, hs⟩
    exact ⟨k, ⟨_, hk, by simp⟩⟩
  · intro heq
    have h1 : M = N := Subgroup.map_injective S.subtype_injective heq
    apply hb1
    rw [hpC, h1, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  · rintro _ ⟨m, hm, rfl⟩
    have hcomm : M.map (QuotientGroup.mk' N) = (⁅M, A.subgroupOf S⁆).map (QuotientGroup.mk' N) := by
      rw [hpC] at hb2
      rw [Subgroup.map_commutator]
      exact hb2
    have hm' : QuotientGroup.mk' N m ∈ (⁅M, A.subgroupOf S⁆).map (QuotientGroup.mk' N) :=
      hcomm ▸ Subgroup.mem_map_of_mem _ hm
    obtain ⟨c, hc, hcm⟩ := hm'
    have hcN : c⁻¹ * m ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, hcm]
      simp
    have hmc : m = c * (c⁻¹ * m) := by group
    have : m ∈ ⁅M, A.subgroupOf S⁆ ⊔ N := by
      rw [hmc]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hcN)
    have h2 := Subgroup.mem_map_of_mem S.subtype this
    rw [Subgroup.map_sup, Subgroup.map_commutator, hBmap] at h2
    exact h2
  · have := card_barO2_eq_relIndex (A.subgroupOf S)
    rw [hb3] at this
    calc (pCoreOf 2 S).relIndex A = (N.map S.subtype).relIndex ((A.subgroupOf S).map S.subtype) := by
          rw [hBmap]; rfl
      _ = N.relIndex (A.subgroupOf S) := Subgroup.relIndex_map_map_of_injective _ _ S.subtype_injective
      _ = 2 := this.symm

theorem eOne_of_eOneAmb {S A : Subgroup G} (hAS : A ≤ S) (h : EOneAmb S A) :
    EOne ↥S (A.subgroupOf S) := by
  obtain ⟨p, hp, hp2, R, hRS, hSR, hNR, hR1, hR2, hRne, hRcomm, hrel⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  set N := CFSG.Open.pCore 2 ↥S with hN
  set R' := R.subgroupOf S with hR'
  have hR'n : R'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRS).mpr hSR
  have hNR' : N ≤ R' := fun n hn => Subgroup.mem_subgroupOf.mpr (hNR ⟨n, hn, rfl⟩)
  have hpow : ∀ x ∈ R', ∃ k : ℕ, x ^ p ^ k ∈ N := by
    intro x hx
    obtain ⟨k, n, hn, hnx⟩ := hR1 (x : G) (Subgroup.mem_subgroupOf.mp hx)
    refine ⟨k, ?_⟩
    have : n = x ^ p ^ k := Subtype.ext (by simpa using hnx)
    rwa [← this]
  have h2' : ∀ q : ↥S, ∃ k : ℕ, q ^ 2 ^ k ∈ R' := by
    intro q
    obtain ⟨k, hk⟩ := hR2 (q : G) q.2
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (by simpa using hk)⟩
  have hM : oTwoP ↥S p = R' := oTwoP_eq_of_series hp2 hNR' hpow h2'
  have hpC : CFSG.Open.pCore p (↥S ⧸ N) = R'.map (QuotientGroup.mk' N) := by
    rw [← hM]
    exact (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _).symm
  have hRmap : R'.map S.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRS
  have hBmap : (A.subgroupOf S).map S.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAS
  refine ⟨p, hp, hp2, oTwoPTwo_eq_top_of_series (N₂ := N) (N₂p := R')
    (CFSG.LieType.BorelTits.pCore_isPGroup 2) hpow h2', ?_, ?_, ?_⟩
  · rw [hpC]
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    apply hRne
    rw [← hRmap, le_antisymm h hNR']
    rfl
  · rw [hpC]
    refine le_antisymm ?_ (Subgroup.commutator_le_left _ _)
    rintro _ ⟨r, hr, rfl⟩
    have hr' : (r : G) ∈ ⁅R, A⁆ ⊔ pCoreOf 2 S := hRcomm (Subgroup.mem_subgroupOf.mp hr)
    have hcomm : ⁅R, A⁆ ⊔ pCoreOf 2 S = (⁅R', A.subgroupOf S⁆ ⊔ N).map S.subtype := by
      rw [Subgroup.map_sup, Subgroup.map_commutator, hRmap, hBmap]
      rfl
    rw [hcomm] at hr'
    obtain ⟨z, hz, hzr⟩ := hr'
    have hzr' : z = r := Subtype.ext hzr
    rw [hzr'] at hz
    have h3 := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hz
    rw [Subgroup.map_sup, Subgroup.map_commutator] at h3
    have hNb : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hNb, sup_bot_eq] at h3
    exact h3
  · have := card_barO2_eq_relIndex (A.subgroupOf S)
    rw [this]
    calc N.relIndex (A.subgroupOf S) = (N.map S.subtype).relIndex ((A.subgroupOf S).map S.subtype) :=
          (Subgroup.relIndex_map_map_of_injective _ _ S.subtype_injective).symm
      _ = (pCoreOf 2 S).relIndex A := by rw [hBmap]; rfl
      _ = 2 := hrel

theorem eOne_iff_amb {S A : Subgroup G} (hAS : A ≤ S) :
    EOne ↥S (A.subgroupOf S) ↔ EOneAmb S A :=
  ⟨eOneAmb_of_eOne hAS, eOne_of_eOneAmb hAS⟩

end EOneAmb

end E1

end CFSG.Quasithin
