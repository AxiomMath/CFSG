module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10
import CFSG.LocalAnalysis.UniquenessCase.UCKPOut
import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_card_center_dvd (hG : GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] {n : ℕ} (hX : IsSU3 X n) : Nat.card (center X) ∣ Nat.gcd 3 (2 ^ n + 1) := by
  obtain ⟨hq, hU⟩ := hX
  haveI : Group.IsPerfect X := Group.isPerfect_def.2 hq.1
  let e : (X ⧸ center X) ≃* (X ⧸ center X) := MulEquiv.refl _
  let π := CFSG.RankThree.PerfectCover.centralQuotientMap e
  have hπs : Function.Surjective π :=
    CFSG.RankThree.PerfectCover.centralQuotientMap_surjective e
  have hk : π.ker = center X := CFSG.RankThree.PerfectCover.centralQuotientMap_ker e
  let ψ : griessHopfMultiplier (X ⧸ center X) →* π.ker :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer π hπs hk.le).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (X ⧸ center X)).toMonoidHom
  have hψ : Function.Surjective ψ :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective π hπs hk.le).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (X ⧸ center X)).surjective
  have hdvd : Nat.card π.ker ∣ Nat.card (griessHopfMultiplier (X ⧸ center X)) :=
    Subgroup.card_dvd_of_surjective hψ
  rwa [hk, UCK.card_griessHopfMultiplier_psu3 hG hU] at hdvd

theorem uc22ine229_not_dvd_two_pow_add_one {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {n : ℕ}
    (hqn : q ∣ 2 ^ n - 1) : ¬ q ∣ 2 ^ n + 1 := by
  intro h
  have h2 : 2 ^ n + 1 = (2 ^ n - 1) + 2 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  rw [h2] at h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 ((Nat.dvd_add_right hqn).1 h))

theorem uc22ine229_not_dvd_card_center (hG : GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] {n : ℕ} (hX : IsSU3 X n) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqn : q ∣ 2 ^ n - 1) : ¬ q ∣ Nat.card (center X) := fun h =>
  uc22ine229_not_dvd_two_pow_add_one hq hq2 hqn
    ((h.trans (uc22ine229_card_center_dvd hG hX)).trans (Nat.gcd_dvd_right _ _))

theorem uc22ine229_map_rhoL_le_inner {M Y : Subgroup G} (hN : M ≤ normalizer (Y : Set G))
    {n : ℕ} (hX : IsSU3 (Bar2 Y) n) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hOp : F10.OpRes p M = M) {A : Subgroup G} (hAM : A ≤ M) (hAel : IsElemAbelian p A) :
    (A.subgroupOf (normalizer (Y : Set G))).map (UC6S846.rhoL Y) ≤
      (MulAut.conj : Bar2 Y →* MulAut (Bar2 Y)).range := by
  obtain ⟨Nsub, hNn, -, hcyc, hcube, -⟩ := UCK.u3OutShape (Bar2 Y) n hX
  haveI := hNn
  have hgen := UC6S846.closure_pPrime_map (UC6S846.rhoL Y) _
    (UC6S846.closure_pPrime_subgroupOf hN (p := p) hOp)
  rintro _ ⟨a, ha, rfl⟩
  have haA : (a : G) ∈ A := ha
  have hap : UC6S846.rhoL Y a ^ (p ^ 1) = 1 := by
    rw [← map_pow]
    have : a ^ p ^ 1 = 1 := Subtype.ext (by simpa using hAel.2 _ haA)
    rw [this, map_one]
  exact UC6S846.mem_inner_of_pPow _ Nsub _ hcyc hcube hp (Or.inl hp3) hgen
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (hAM haA))) hap

theorem uc22ine229_card_le_of_not_dvd {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsSU3 X n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpn : ¬ p ∣ 2 ^ n + 1)
    {R : Subgroup (MulAut X)} (hR : IsElemAbelian p R) : Nat.card R ≤ p ^ 2 := by
  obtain ⟨N, hNn, -, hcyc, hcube, -⟩ := UCK.u3OutShape X n hX
  haveI := hNn
  haveI : IsCyclic (MulAut X ⧸ N) := hcyc
  let f : ↥R →* MulAut X ⧸ N := (QuotientGroup.mk' N).comp R.subtype
  have hpow : ∀ r : ↥R, r ^ p = 1 := fun r => Subtype.ext (by simpa using hR.2 r.1 r.2)
  have hrange : Nat.card f.range ≤ p := by
    have hexp : Monoid.exponent f.range ∣ p := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      rintro ⟨_, r, rfl⟩
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← map_pow, hpow r, map_one, OneMemClass.coe_one]
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.pos hexp
  have hKinn : f.ker.map R.subtype ≤ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨r, hr, rfl⟩
    have h3 := hcube _ ((QuotientGroup.eq_one_iff (r : MulAut X)).1 (MonoidHom.mem_ker.1 hr))
    have hcop : Nat.Coprime 3 (orderOf (r : MulAut X)) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one (hR.2 _ r.2))
        ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    show (r : MulAut X) ∈ _
    rw [← hm]
    exact Subgroup.pow_mem _ h3 m
  have hker : Nat.card f.ker ≤ p := by
    rw [← Subgroup.card_map_of_injective R.subtype_injective]
    exact UCK.u3RankOne X n hX p hp hp2 hpn _ hKinn (hR.mono (Subgroup.map_subtype_le _))
  rw [← Subgroup.card_ker_mul_card_range f, sq]
  exact Nat.mul_le_mul hker hrange

theorem uc22ine229_exists_B₁_of_normal {M Y : Subgroup G} (hY : Y ∈ calC M)
    (hN : M ≤ normalizer (Y : Set G)) {n : ℕ} (hX : IsSU3 (Bar2 Y) n) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hOp : F10.OpRes p M = M) (h4 : 4 ≤ CFSG.Open.pRank p M) {X : Subgroup G}
    (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hXq : IsPGroup q X) :
    ∃ B₁ : Subgroup G, B₁ ≤ M ∧ IsElemAbelian p B₁ ∧ Nat.card B₁ = p ^ 2 ∧
      B₁ ≤ centralizer (X : Set G) ∧ ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨B, hBM, hBel, hBc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp h4
  obtain ⟨B₀, hB₀B, hB₀el, hB₀c, hB₀Y⟩ := uc22ine229_exists_kernel hY.1 hp (hBM.trans hN) hBel
    hBc (uc22ine229_card_le_of_le_inner hX hp hp2
      (uc22ine229_map_rhoL_le_inner hN hX hp hp3 hOp hBM hBel) ((hBel.subgroupOf _).map _))
  exact uc22ine229_exists_copy hY.1.le hp hp2 hq hq2 (hB₀B.trans hBM) hB₀el hB₀c hB₀Y hXY hXq

theorem uc22ine229_exists_B₁_of_not_dvd {M Y : Subgroup G} (hY : Y ∈ calC M) {n : ℕ}
    (hX : IsSU3 (Bar2 Y) n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : ¬ p ∣ 2 ^ n + 1)
    (h4 : 4 ≤ CFSG.Open.pRank p M) {X : Subgroup G} (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hXc : Nat.card X = q) (hZ : ¬ q ∣ Nat.card (center (Bar2 Y)))
    (hrank : CFSG.Open.pRank q M ≤ 3) :
    ∃ B₁ : Subgroup G, B₁ ≤ M ∧ IsElemAbelian p B₁ ∧ Nat.card B₁ = p ^ 2 ∧
      B₁ ≤ centralizer (X : Set G) ∧ ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨B, hBM, hBel, hBc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp h4
  have hBN := uc22ine229_le_normalizer hY hp hp5 hq hq2 hXY hXc hZ hrank hBM hBel
  obtain ⟨B₀, hB₀B, hB₀el, hB₀c, hB₀Y⟩ := uc22ine229_exists_kernel hY.1 hp hBN hBel hBc
    (uc22ine229_card_le_of_not_dvd hX hp hp2 hp3 hpn ((hBel.subgroupOf _).map _))
  exact uc22ine229_exists_copy hY.1.le hp hp2 hq hq2 (hB₀B.trans hBM) hB₀el hB₀c hB₀Y hXY
    (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one]))

theorem uc22ine229_exists_B₁_of_isSU3 (hSyl : UCK.U3SylOmega) {M Y : Subgroup G}
    (hY : Y ∈ calC M) {n : ℕ} (hX : IsSU3 (Bar2 Y) n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hOp : F10.OpRes p M = M) (h4 : 4 ≤ CFSG.Open.pRank p M) {X : Subgroup G} (hXY : X ≤ Y)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hXc : Nat.card X = q)
    (hZ : ¬ q ∣ Nat.card (center (Bar2 Y))) (hrank : CFSG.Open.pRank q M ≤ 3) :
    ∃ B₁ : Subgroup G, B₁ ≤ M ∧ IsElemAbelian p B₁ ∧ Nat.card B₁ = p ^ 2 ∧
      B₁ ≤ centralizer (X : Set G) ∧ ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  have hXq : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  by_cases hN : M ≤ normalizer (Y : Set G)
  · exact uc22ine229_exists_B₁_of_normal hY hN hX hp hp5 hOp h4 hXY hq hq2 hXq
  by_cases hpn : p ∣ 2 ^ n + 1
  · obtain ⟨B₀, hB₀M, hB₀el, hB₀c, hB₀Y⟩ :=
      uc22ine229_exists_conj_sq hSyl hY hX hp (by omega) hpn hN
    exact uc22ine229_exists_copy hY.1.le hp (by omega) hq hq2 hB₀M hB₀el hB₀c hB₀Y hXY hXq
  · exact uc22ine229_exists_B₁_of_not_dvd hY hX hp hp5 hpn h4 hXY hq hq2 hXc hZ hrank

end CFSG.LocalAnalysis.UniquenessCase.UC22
