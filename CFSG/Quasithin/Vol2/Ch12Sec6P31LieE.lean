module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolic

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

private theorem psl34e_finite_sylow (p : ℕ) (G : Type*) [Group G] [Finite G] :
    Finite (Sylow p G) :=
  Finite.of_injective (fun P : Sylow p G => ((P : Subgroup G) : Set G))
    (fun _ _ h => Sylow.ext (SetLike.coe_injective h))

private theorem psl34e_dvd_card_of_sup_eq_top {G : Type*} [Group G] [Finite G]
    (M H : Subgroup G) [M.Normal] (hH : H ⊔ M = ⊤) {p : ℕ} [Fact p.Prime]
    (hpG : p ∣ Nat.card G) (hpM : ¬ p ∣ Nat.card M) : p ∣ Nat.card H := by
  have h1 : M.relIndex (H ⊔ M) = M.relIndex H := Subgroup.relIndex_sup_right H M
  rw [hH, Subgroup.relIndex_top_right] at h1
  have h2 : Nat.card M * M.index = Nat.card G := Subgroup.card_mul_index M
  have h3 : p ∣ M.index := by
    rw [← h2] at hpG
    exact ((Nat.Prime.dvd_mul Fact.out).1 hpG).resolve_left hpM
  have h4 : M.relIndex H ∣ Nat.card H :=
    Dvd.intro_left _ (Subgroup.card_mul_index (H := M.subgroupOf H))
  rw [← h1] at h4
  exact h3.trans h4

private theorem psl34e_exists_commute_of_normalizer {G : Type*} [Group G] [Finite G]
    {Q : Subgroup G} (hQ : Nat.card Q = 3) {y : G} (hy : y ∈ Subgroup.normalizer (Q : Set G))
    (hodd : Odd (orderOf y)) : ∃ x ∈ Q, orderOf x = 3 ∧ y * x = x * y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 3 (by rw [hQ])
  obtain ⟨x, hxQ, hxord⟩ : ∃ x ∈ Q, orderOf x = 3 :=
    ⟨x0, x0.2, by rw [Subgroup.orderOf_coe, hx0]⟩
  have hzp : Subgroup.zpowers x = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.2 hxQ
    · exact le_of_eq (by rw [Nat.card_zpowers, hxord, hQ])
  have hyx : y * x * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hy x).1 hxQ
  rw [← hzp, Subgroup.mem_zpowers_iff] at hyx
  obtain ⟨m, hm⟩ := hyx
  have hconj_ord : ∀ g : G, orderOf (MulAut.conj y g) = orderOf g := fun g =>
    orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective g
  have hcx : MulAut.conj y x = x ^ m := by rw [MulAut.conj_apply, hm]
  have hmne : x ^ m ≠ 1 := by
    intro h
    have h1 := hconj_ord x
    rw [hcx, h, orderOf_one, hxord] at h1
    norm_num at h1
  have hxpow : ∀ z : ℤ, x ^ z = x ^ (z % 3) := by
    intro z
    have h := zpow_mod_orderOf x z
    rw [hxord] at h
    exact_mod_cast h.symm
  have hmod : m % 3 = 1 ∨ m % 3 = 2 := by
    have h0 : m % 3 ≠ 0 := by
      intro h
      apply hmne
      rw [hxpow m, h, zpow_zero]
    omega
  have hmm : (m * m) % 3 = 1 := by
    rcases hmod with h | h <;> simp [Int.mul_emod, h]
  have hcc : MulAut.conj y (MulAut.conj y x) = x := by
    rw [hcx, map_zpow, hcx, ← zpow_mul, hxpow (m * m), hmm, zpow_one]
  have hc2 : ((MulAut.conj y) ^ 2) x = x := by
    rw [pow_two, MulAut.mul_apply, hcc]
  have hfix : ∀ i : ℕ, ((MulAut.conj y) ^ (2 * i)) x = x := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, pow_add, MulAut.mul_apply, hc2, ih]
  obtain ⟨j, hj⟩ := hodd
  have hcpow : (MulAut.conj y) ^ orderOf y = 1 := by
    have h := map_pow (MulAut.conj : G →* MulAut G) y (orderOf y)
    rw [pow_orderOf_eq_one, map_one] at h
    exact h.symm
  have hfixc : MulAut.conj y x = x := by
    have h1 : ((MulAut.conj y) ^ (2 * j)) (MulAut.conj y x) = x := by
      rw [← MulAut.mul_apply, ← pow_succ, ← hj, hcpow, MulAut.one_apply]
    exact ((MulAut.conj y) ^ (2 * j)).injective (h1.trans (hfix j).symm)
  refine ⟨x, hxQ, hxord, ?_⟩
  rw [MulAut.conj_apply] at hfixc
  exact mul_inv_eq_iff_eq_mul.1 hfixc

private theorem psl34e_orderOf_dvd_nine {K : Type} [Group K] [Finite K] {k : Type} [Field k]
    (e : K ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 k)
    (hk : Nat.card k = 4) {x y : K} (hx : orderOf x = 3) (hxy : Commute x y) :
    orderOf y ∣ 9 := by
  haveI : Finite k := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : ∀ g : K, orderOf (e g) = orderOf g := fun g =>
    orderOf_injective e.toMonoidHom e.injective g
  have hx₁ : orderOf (e x) = 3 := by rw [hord, hx]
  have hc₁ : Commute (e x) (e y) := hxy.map e
  have hP : IsPGroup 3 (Subgroup.zpowers (e x)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₁, pow_one])
  obtain ⟨E, hE⟩ := hP.exists_le_sylow
  have hEcard : Nat.card (E : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL
      3 k)) = 9 := by
    have h := Sylow.card_eq_multiplicity E
    rw [CFSG.RankThree.PartTwo.KFacts.L34.factorization_card hk] at h
    norm_num at h
    exact h
  have hxE : e x ∈ (E : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL
      3 k)) := hE (Subgroup.mem_zpowers (e x))
  have hx1 : e x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx₁
    norm_num at hx₁
  have hC := CFSG.RankThree.PartTwo.KFacts.L34.centralizer_eq_of_card_eq_nine hk hEcard hxE hx1
  have hyC : e y ∈ Subgroup.centralizer
      ({e x} : Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 k)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hc₁.symm.eq
  rw [hC] at hyC
  have hdvd := orderOf_dvd_natCard (⟨e y, hyC⟩ :
    (E : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 k)))
  rw [Subgroup.orderOf_mk, hEcard] at hdvd
  rw [← hord y]
  exact hdvd

private theorem psl34e_no_odd_prime_dvd {K : Type} [Group K] [Finite K] {k : Type} [Field k]
    (e : K ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 k)
    (hk : Nat.card k = 4) (N W : Subgroup K) (hWN : W ≤ N) (hWnorm : (W.subgroupOf N).Normal)
    (hW23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = 3)
    (h3 : 3 ∣ Nat.card W) (h9 : ¬ 9 ∣ Nat.card N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hpN : p ∣ Nat.card N) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite k := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  have hMcard : Nat.card (W.subgroupOf N) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWN).toEquiv
  have hpM : ¬ p ∣ Nat.card (W.subgroupOf N) := by
    rw [hMcard]
    intro h
    rcases hW23 p hp h with h2 | h2
    · exact hp2 h2
    · exact hp3 h2
  have h3M : 3 ∣ Nat.card (W.subgroupOf N) := by rw [hMcard]; exact h3
  have hMN : Nat.card (W.subgroupOf N) ∣ Nat.card N := Subgroup.card_subgroup_dvd_card _
  have h9M : ¬ 9 ∣ Nat.card (W.subgroupOf N) := fun h => h9 (h.trans hMN)
  haveI : Finite (Sylow 3 (W.subgroupOf N)) := psl34e_finite_sylow 3 _
  obtain ⟨Q⟩ : Nonempty (Sylow 3 (W.subgroupOf N)) := inferInstance
  have hfac : (Nat.card (W.subgroupOf N)).factorization 3 = 1 := by
    have hM0 : Nat.card (W.subgroupOf N) ≠ 0 := Nat.card_pos.ne'
    have h1 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three hM0).1 h3M
    have h2 : ¬ 2 ≤ (Nat.card (W.subgroupOf N)).factorization 3 := fun h =>
      h9M (by simpa using (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hM0).2 h)
    omega
  have hQcard : Nat.card Q = 3 := by
    have h := Sylow.card_eq_multiplicity Q
    rw [hfac] at h
    norm_num at h
    exact h
  have hfrat := Sylow.normalizer_sup_eq_top Q
  obtain ⟨Qn, hQn⟩ : ∃ Qn : Subgroup N, Qn = Q.map (W.subgroupOf N).subtype := ⟨_, rfl⟩
  rw [← hQn] at hfrat
  have hQncard : Nat.card Qn = 3 := by
    rw [hQn]
    exact (Subgroup.card_map_of_injective (W.subgroupOf N).subtype_injective).trans hQcard
  have hpH : p ∣ Nat.card (Subgroup.normalizer (Qn : Set N)) :=
    psl34e_dvd_card_of_sup_eq_top (W.subgroupOf N) _ hfrat hpN hpM
  obtain ⟨y0, hy0⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.normalizer (Qn : Set N))) p hpH
  have hyN : (y0 : N) ∈ Subgroup.normalizer (Qn : Set N) := y0.2
  have hodd : Odd (orderOf (y0 : N)) := by
    rw [Subgroup.orderOf_coe, hy0]
    exact hp.odd_of_ne_two hp2
  obtain ⟨x, _, hxord, hcomm⟩ := psl34e_exists_commute_of_normalizer hQncard hyN hodd
  have hxK : orderOf (x : K) = 3 := by rw [Subgroup.orderOf_coe, hxord]
  have hcK : Commute (x : K) ((y0 : N) : K) := by
    have h := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul] at h
    exact h.symm
  have hdvd := psl34e_orderOf_dvd_nine e hk hxK hcK
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy0] at hdvd
  have hp9 : p ∣ 3 ^ 2 := by norm_num; exact hdvd
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hp9))

private theorem psl34e_card_eq_192 {n : ℕ} (h192 : 192 ∣ n) (hn : n ∣ 20160) (h9 : ¬ 9 ∣ n)
    (h5 : ¬ 5 ∣ n) (h7 : ¬ 7 ∣ n) : n = 192 := by
  obtain ⟨c, rfl⟩ := h192
  have h20160 : (20160 : ℕ) = 192 * 105 := by norm_num
  rw [h20160] at hn
  have hc : c ∣ 105 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hn
  have hc105 : c ≤ 105 := Nat.le_of_dvd (by norm_num) hc
  interval_cases c <;> omega

theorem psl34_overgroup
    {K : Type} [Group K] [Finite K] (hK : IsPSL 3 2 2 K) (T N W : Subgroup K)
    (hT : IsSylowTwoOf T ⊤) (h192 : Nat.card ↥(Subgroup.normalizer (T : Set K)) = 192)
    (hB : Subgroup.normalizer (T : Set K) ≤ N) (hNB : N ≠ Subgroup.normalizer (T : Set K))
    (hNK : N ≠ ⊤) (hWN : W ≤ N) (hWnorm : (W.subgroupOf N).Normal)
    (hW23 : ∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = 3) : ¬ 3 ∣ Nat.card W := by
  intro h3
  have hcardK : Nat.card K = 20160 := (isPSL_three_two_two_props hK).2
  have hLie : CFSG.Blueprint.LieModel K .PSL 3 2 2 := Or.inl ⟨by decide, hK⟩
  obtain ⟨k, hkf, hkfin, hk, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  have hk4 : Nat.card k = 4 := hk.trans (by norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTi : ¬ 2 ∣ T.index := by
    have h : ¬ 2 ∣ T.relIndex ⊤ := hT.2.2
    rwa [Subgroup.relIndex_top_right] at h
  let T2 : Sylow 2 K := hT.2.1.toSylow hTi
  have hB2 : Subgroup.normalizer ((T2 : Subgroup K) : Set K) ≤ N := hB
  have hN9 : ¬ 9 ∣ Nat.card N := fun h9 =>
    hNK (CFSG.ComponentClassification.GrSLit.L34Facts.l34ParabolicFact K hLie T2 N hB2 h9)
  have hdvd192 : 192 ∣ Nat.card N := by
    have h := Subgroup.card_dvd_of_le hB
    rwa [h192] at h
  have hdvdK : Nat.card N ∣ 20160 := by
    have h := Subgroup.card_subgroup_dvd_card N
    rwa [hcardK] at h
  have h5 : ¬ 5 ∣ Nat.card N := fun h =>
    psl34e_no_odd_prime_dvd e hk4 N W hWN hWnorm hW23 h3 hN9 (by norm_num) (by norm_num)
      (by norm_num) h
  have h7 : ¬ 7 ∣ Nat.card N := fun h =>
    psl34e_no_odd_prime_dvd e hk4 N W hWN hWnorm hW23 h3 hN9 (by norm_num) (by norm_num)
      (by norm_num) h
  have hN192 : Nat.card N = 192 := psl34e_card_eq_192 hdvd192 hdvdK hN9 h5 h7
  exact hNB (Subgroup.eq_of_le_of_card_ge hB (le_of_eq (by rw [hN192, h192]))).symm

end CFSG.Quasithin.H13.S126P31
