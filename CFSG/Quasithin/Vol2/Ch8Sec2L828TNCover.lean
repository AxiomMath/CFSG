module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallSylowCentralCover
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.H13.L828N

open scoped commutatorElement

private lemma factorization_eq_one_of_dvd_not_sq {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h1 : p ∣ n) (h2 : ¬ p ^ 2 ∣ n) : n.factorization p = 1 := by
  have hle1 : 1 ≤ n.factorization p :=
    (hp.pow_dvd_iff_le_factorization (k := 1) hn).mp (by rw [pow_one]; exact h1)
  have hle2 : ¬ 2 ≤ n.factorization p := fun h =>
    h2 ((hp.pow_dvd_iff_le_factorization (k := 2) hn).mpr h)
  omega

theorem sylow5_card_five {R : Type*} [Group R] [Finite R] (h5 : 5 ∣ Nat.card R)
    (h25 : ¬ 25 ∣ Nat.card R) (S : Sylow 5 R) : Nat.card S = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hn : Nat.card R ≠ 0 := fun h => h25 (by rw [h]; exact dvd_zero 25)
  have hfac : (Nat.card R).factorization 5 = 1 :=
    factorization_eq_one_of_dvd_not_sq (by norm_num : Nat.Prime 5) hn h5
      (by rw [show (5 : ℕ) ^ 2 = 25 by norm_num]; exact h25)
  calc Nat.card S = 5 ^ (Nat.card R).factorization 5 := Sylow.card_eq_multiplicity S
    _ = 5 := by rw [hfac, pow_one]

theorem sylow3_elem_nine {R : Type*} [Group R] [Finite R] (h9 : 9 ∣ Nat.card R)
    (h27 : ¬ 27 ∣ Nat.card R) (hno9 : ∀ r : R, r ^ 9 = 1 → r ^ 3 = 1) (S : Sylow 3 R) :
    CFSG.Open.IsElemAbelian 3 (S : Subgroup R) ∧ Nat.card S = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hn : Nat.card R ≠ 0 := fun h => h27 (by rw [h]; exact dvd_zero 27)
  have hfac : (Nat.card R).factorization 3 = 2 := by
    have hle1 : 2 ≤ (Nat.card R).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization (p := 3) (k := 2) Nat.prime_three hn).mp
        (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact h9)
    have hle2 : ¬ 3 ≤ (Nat.card R).factorization 3 := by
      intro h
      have h' : 3 ^ 3 ∣ Nat.card R :=
        (Nat.Prime.pow_dvd_iff_le_factorization (p := 3) (k := 3) Nat.prime_three hn).mpr h
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num] at h'
      exact h27 h'
    omega
  have hcardS : Nat.card (S : Subgroup R) = 9 :=
    calc Nat.card (S : Subgroup R) = 3 ^ (Nat.card R).factorization 3 :=
          Sylow.card_eq_multiplicity S
      _ = 9 := by simp [hfac]
  refine ⟨?_, hcardS⟩
  have hexp : ∀ x ∈ (S : Subgroup R), x ^ 3 = 1 := by
    intro x hx
    apply hno9
    have h1 : orderOf (⟨x, hx⟩ : (S : Subgroup R)) ∣ 9 := by
      have h := orderOf_dvd_natCard (⟨x, hx⟩ : (S : Subgroup R))
      rwa [hcardS] at h
    have h2 : (⟨x, hx⟩ : (S : Subgroup R)) ^ 9 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have hcomm : IsMulCommutative (S : Subgroup R) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (hcardS.trans (by norm_num))
  unfold CFSG.Open.IsElemAbelian
  exact ⟨hcomm, hexp⟩

theorem not_dvd_of_dvd_20160 {n : ℕ} (h : n ∣ 20160) : ¬ 25 ∣ n ∧ ¬ 27 ∣ n := by
  constructor
  · intro h25
    have := dvd_trans h25 h
    norm_num at this
  · intro h27
    have := dvd_trans h27 h
    norm_num at this

private lemma s828N_core {K R : Type} [Group K] [Finite K] [Group R] (ψ : K →* R)
    (hψ : Function.Surjective ψ) (O : Subgroup K) [hOn : O.Normal] (hOp : IsPGroup 2 O)
    (hq : CFSG.IsQuasisimple (K ⧸ O))
    (hcent : ∀ k ∈ ψ.ker, ∀ x : K, ⁅x, k⁆ ∈ O)
    (hR : Nat.card R ∣ 20160) (h5 : 5 ∣ Nat.card R) (h9 : 9 ∣ Nat.card R)
    (hno9 : ∀ r : R, r ^ 9 = 1 → r ^ 3 = 1) :
    ¬ 5 ∣ Nat.card ψ.ker ∧ ¬ 9 ∣ Nat.card ψ.ker ∧ (∃ f : K, f ^ 5 = 1 ∧ ψ f ≠ 1) ∧
      (∀ S : Sylow 3 K, ¬ IsCyclic (S : Subgroup K)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Finite R := Finite.of_surjective ψ hψ
  obtain ⟨hperf, -⟩ := hq
  haveI : Group.IsPerfect (K ⧸ O) := hperf
  have hnot27R : ¬ 27 ∣ Nat.card R := (not_dvd_of_dvd_20160 hR).2
  haveI hWn : (O.map ψ).Normal := Subgroup.Normal.map hOn ψ hψ
  have hWp : IsPGroup 2 (O.map ψ) := hOp.map ψ
  obtain ⟨n, hnW⟩ : ∃ n : ℕ, Nat.card (O.map ψ) = 2 ^ n := IsPGroup.iff_card.mp hWp
  have hcardRW : Nat.card R = Nat.card (R ⧸ O.map ψ) * Nat.card (O.map ψ) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (O.map ψ)
  have hdvdR : Nat.card (R ⧸ O.map ψ) ∣ Nat.card R := ⟨Nat.card (O.map ψ), hcardRW⟩
  have hdvdRb : Nat.card (R ⧸ O.map ψ) ∣ 20160 := hdvdR.trans hR
  have hc5 : Nat.Coprime 5 (Nat.card (O.map ψ)) := by
    rw [hnW]; exact Nat.Coprime.pow_right n (by norm_num)
  have hc9 : Nat.Coprime 9 (Nat.card (O.map ψ)) := by
    rw [hnW]; exact Nat.Coprime.pow_right n (by norm_num)
  have h5Rb : 5 ∣ Nat.card (R ⧸ O.map ψ) := by
    apply Nat.Coprime.dvd_of_dvd_mul_right hc5
    rw [← hcardRW]; exact h5
  have h9Rb : 9 ∣ Nat.card (R ⧸ O.map ψ) := by
    apply Nat.Coprime.dvd_of_dvd_mul_right hc9
    rw [← hcardRW]; exact h9
  have hnot25Rb : ¬ 25 ∣ Nat.card (R ⧸ O.map ψ) := (not_dvd_of_dvd_20160 hdvdRb).1
  have hnot27Rb : ¬ 27 ∣ Nat.card (R ⧸ O.map ψ) := (not_dvd_of_dvd_20160 hdvdRb).2
  have hno9Rb : ∀ g : R ⧸ O.map ψ, g ^ 9 = 1 → g ^ 3 = 1 := by
    intro g hg
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
    have hgpow : ∀ k : ℕ, ((r : R ⧸ O.map ψ)) ^ k = ((r ^ k : R) : R ⧸ O.map ψ) :=
      fun k => rfl
    have hr9 : r ^ 9 ∈ O.map ψ :=
      (QuotientGroup.eq_one_iff _).mp ((hgpow 9).symm.trans hg)
    obtain ⟨o, ho, hoψ⟩ := Subgroup.mem_map.mp hr9
    obtain ⟨m, hm⟩ := hOp ⟨o, ho⟩
    have hom : o ^ 2 ^ m = 1 := by
      have h := congrArg Subtype.val hm
      simpa using h
    have hrm : (r ^ 9) ^ 2 ^ m = 1 := by
      rw [← hoψ, ← map_pow, hom, map_one]
    have hs3 : (r ^ 2 ^ m) ^ 3 = 1 := by
      apply hno9
      rw [← pow_mul, mul_comm, pow_mul, hrm]
    have hr3 : r ^ (3 * 2 ^ m) = 1 := by
      rw [mul_comm, pow_mul]; exact hs3
    have ht3 : ((r : R ⧸ O.map ψ) ^ 3) ^ 3 = 1 := by
      rw [← pow_mul]; exact hg
    have ht2 : ((r : R ⧸ O.map ψ) ^ 3) ^ 2 ^ m = 1 := by
      rw [← pow_mul, hgpow]
      exact (QuotientGroup.eq_one_iff _).mpr (by rw [hr3]; exact Subgroup.one_mem _)
    have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
    have hord1 : orderOf ((r : R ⧸ O.map ψ) ^ 3) ∣ Nat.gcd 3 (2 ^ m) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ht3) (orderOf_dvd_of_pow_eq_one ht2)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at hord1
    exact hord1
  have hle : O ≤ (O.map ψ).comap ψ :=
    fun x hx => Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem ψ hx)
  obtain ⟨phi, hphi⟩ : ∃ phi : K ⧸ O →* R ⧸ O.map ψ,
      ∀ x : K, phi (x : K ⧸ O) = ((ψ x : R) : R ⧸ O.map ψ) :=
    ⟨QuotientGroup.map O (O.map ψ) ψ hle, fun x => rfl⟩
  have hphisurj : Function.Surjective phi := by
    intro r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
    obtain ⟨k, rfl⟩ := hψ x
    exact ⟨(k : K ⧸ O), hphi k⟩
  have hkerphi : phi.ker ≤ Subgroup.center (K ⧸ O) := by
    intro q hq
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hk : ψ k ∈ O.map ψ := by
      have h1 : phi (k : K ⧸ O) = 1 := hq
      rw [hphi k] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨o, ho, hoψ⟩ := Subgroup.mem_map.mp hk
    obtain ⟨c, hc⟩ : ∃ c : K, c = k * o⁻¹ := ⟨_, rfl⟩
    have hcker : c ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hc, map_mul, map_inv, hoψ, mul_inv_cancel]
    have hk_eq : k = c * o := by rw [hc, inv_mul_cancel_right]
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have hxo : ⁅x, o⁆ ∈ O := by
      rw [commutatorElement_def]
      exact O.mul_mem (hOn.conj_mem o ho x) (O.inv_mem ho)
    have hxk : ⁅x, k⁆ ∈ O := by
      have hid : ⁅x, c * o⁆ = ⁅x, c⁆ * (c * ⁅x, o⁆ * c⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [hk_eq, hid]
      exact O.mul_mem (hcent c hcker x) (hOn.conj_mem _ hxo c)
    have hcomm : Commute (x : K ⧸ O) (k : K ⧸ O) := by
      rw [← commutatorElement_eq_one_iff_commute]
      have h2 : ((⁅x, k⁆ : K) : K ⧸ O) = ⁅(x : K ⧸ O), (k : K ⧸ O)⁆ :=
        map_commutatorElement (QuotientGroup.mk' O) x k
      rw [← h2]
      exact (QuotientGroup.eq_one_iff _).mpr hxk
    exact hcomm.eq
  obtain ⟨Q5⟩ : Nonempty (Sylow 5 (R ⧸ O.map ψ)) := inferInstance
  have hQ5card : Nat.card (Q5 : Subgroup (R ⧸ O.map ψ)) = 5 :=
    sylow5_card_five h5Rb hnot25Rb Q5
  have hcycQ5 : IsCyclic (Q5 : Subgroup (R ⧸ O.map ψ)) := isCyclic_of_prime_card hQ5card
  have hC5 : ∀ C : Sylow 5 phi.ker, (C : Subgroup phi.ker) = ⊥ := fun C =>
    CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot phi hphisurj hkerphi
      C Q5 hcycQ5
  have hnot5B : ¬ 5 ∣ Nat.card phi.ker := by
    intro h
    obtain ⟨C⟩ : Nonempty (Sylow 5 phi.ker) := inferInstance
    exact Sylow.ne_bot_of_dvd_card C h (hC5 C)
  obtain ⟨Q3⟩ : Nonempty (Sylow 3 (R ⧸ O.map ψ)) := inferInstance
  obtain ⟨helem3, hcard3⟩ := sylow3_elem_nine h9Rb hnot27Rb hno9Rb Q3
  have hcard3' : Nat.card (Q3 : Subgroup (R ⧸ O.map ψ)) = 3 ^ 2 :=
    hcard3.trans (by norm_num)
  have hC3 : ∀ C : Sylow 3 phi.ker, Nat.card (C : Subgroup phi.ker) ≤ 3 := fun C =>
    (CFSG.ShultStronglyClosedTI.central_cover_elementary_rank_two_sylow_kernel_bound
      phi hphisurj hkerphi C Q3 helem3 hcard3').2
  have hnot9B : ¬ 9 ∣ Nat.card phi.ker := by
    intro h
    obtain ⟨C⟩ : Nonempty (Sylow 3 phi.ker) := inferInstance
    have h9' : 3 ^ 2 ∣ Nat.card phi.ker := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact h
    have hle9 : 3 ^ 2 ≤ Nat.card (C : Subgroup phi.ker) :=
      Nat.le_of_dvd Nat.card_pos (C.pow_dvd_card_of_pow_dvd_card h9')
    exact absurd (le_trans hle9 (hC3 C)) (by norm_num)
  obtain ⟨f1, hf1⟩ : ∃ f1 : ψ.ker →* K ⧸ O, ∀ g : ψ.ker, f1 g = ((g : K) : K ⧸ O) :=
    ⟨(QuotientGroup.mk' O).comp ψ.ker.subtype, fun g => rfl⟩
  have hf1range : f1.range ≤ phi.ker := by
    intro y hy
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [MonoidHom.mem_ker, hf1, hphi]
    have hg : ψ (g : K) = 1 := g.2
    exact (QuotientGroup.eq_one_iff _).mpr (by rw [hg]; exact Subgroup.one_mem _)
  have hf1ker : f1.ker = O.comap ψ.ker.subtype := by
    ext g
    rw [MonoidHom.mem_ker, hf1, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  have hf1ker2 : IsPGroup 2 f1.ker := by
    rw [hf1ker]; exact hOp.comap_subtype
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card f1.ker = 2 ^ m := IsPGroup.iff_card.mp hf1ker2
  have key : ∀ p : ℕ, Nat.Coprime p (2 ^ m) → p ∣ Nat.card ψ.ker → p ∣ Nat.card phi.ker := by
    intro p hp hdvd
    have hcop : Nat.Coprime p (Nat.card f1.ker) := by rw [hm]; exact hp
    have h1 : p ∣ Nat.card f1.ker * Nat.card f1.range := by
      rw [Subgroup.card_ker_mul_card_range]; exact hdvd
    exact (hcop.dvd_of_dvd_mul_left h1).trans (Subgroup.card_dvd_of_le hf1range)
  have hnot5A : ¬ 5 ∣ Nat.card ψ.ker := fun h =>
    hnot5B (key 5 (Nat.Coprime.pow_right m (by norm_num)) h)
  have hnot9A : ¬ 9 ∣ Nat.card ψ.ker := fun h =>
    hnot9B (key 9 (Nat.Coprime.pow_right m (by norm_num)) h)
  have hdvdK : 5 ∣ Nat.card K := by
    have hqR : Nat.card (K ⧸ ψ.ker) = Nat.card R :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, hqR]
    exact Dvd.dvd.mul_right h5 _
  have hf5 : ∃ f : K, f ^ 5 = 1 ∧ ψ f ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 hdvdK
    refine ⟨x, ?_, ?_⟩
    · rw [← hx]; exact pow_orderOf_eq_one x
    · intro hψx
      have hxker : x ∈ ψ.ker := hψx
      have hord : orderOf (⟨x, hxker⟩ : ψ.ker) = 5 :=
        (Subgroup.orderOf_coe (⟨x, hxker⟩ : ψ.ker)).symm.trans hx
      have hdiv := orderOf_dvd_natCard (⟨x, hxker⟩ : ψ.ker)
      rw [hord] at hdiv
      exact hnot5A hdiv
  have hcyc3 : ∀ S : Sylow 3 K, ¬ IsCyclic (S : Subgroup K) := by
    intro S hS
    have hcardS' : Nat.card (Sylow.mapSurjective hψ S : Subgroup R) = 9 :=
      (sylow3_elem_nine h9 hnot27R hno9 (Sylow.mapSurjective hψ S)).2
    have hcycS' : IsCyclic (Sylow.mapSurjective hψ S : Subgroup R) := by
      rw [Sylow.coe_mapSurjective hψ S]
      exact isCyclic_of_surjective (ψ.subgroupMap (S : Subgroup K))
        (ψ.subgroupMap_surjective _)
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
      (α := (Sylow.mapSurjective hψ S : Subgroup R))
    have hord : orderOf (g : R) = 9 := (Subgroup.orderOf_coe g).trans (hg.trans hcardS')
    have h9g : (g : R) ^ 9 = 1 := by
      have h := pow_orderOf_eq_one (g : R)
      rwa [hord] at h
    have hdvd3 := orderOf_dvd_of_pow_eq_one (hno9 _ h9g)
    rw [hord] at hdvd3
    norm_num at hdvd3
  exact ⟨hnot5A, hnot9A, hf5, hcyc3⟩

theorem s828N_cover {K R : Type} [Group K] [Finite K] [Group R] (ψ : K →* R)
    (hψ : Function.Surjective ψ)
    (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hcent : ∀ k ∈ ψ.ker, ∀ x : K, ⁅x, k⁆ ∈ CFSG.pCore 2 K)
    (hR : Nat.card R ∣ 20160) (h5 : 5 ∣ Nat.card R) (h9 : 9 ∣ Nat.card R)
    (hno9 : ∀ r : R, r ^ 9 = 1 → r ^ 3 = 1) :
    ¬ 5 ∣ Nat.card ψ.ker ∧ ¬ 9 ∣ Nat.card ψ.ker ∧ (∃ f : K, f ^ 5 = 1 ∧ ψ f ≠ 1) ∧
      (∀ S : Sylow 3 K, ¬ IsCyclic (S : Subgroup K)) :=
  s828N_core ψ hψ (CFSG.pCore 2 K) CFSG.pCore_isPGroup hq hcent hR h5 h9 hno9

end CFSG.Quasithin.H13.L828N
