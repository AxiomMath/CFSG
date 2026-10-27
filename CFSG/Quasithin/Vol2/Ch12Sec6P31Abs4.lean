module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31b
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs1
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs2
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Abs3

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits Equiv

theorem card_mul_card_inf_of_sup_eq_top {Y : Type*} [Group Y] [Finite Y] (K M : Subgroup Y)
    [K.Normal] (h : K ⊔ M = ⊤) :
    Nat.card Y * Nat.card ↥(K ⊓ M) = Nat.card K * Nat.card M := by
  have h1 : K.relIndex (M ⊔ K) = K.relIndex M := Subgroup.relIndex_sup_right M K
  rw [sup_comm, h, Subgroup.relIndex_top_right] at h1
  have h2 : K.relIndex M * Nat.card ↥(K ⊓ M) = Nat.card M := Subgroup.relIndex_mul_card _ _
  have h3 : K.index * Nat.card K = Nat.card Y := Subgroup.index_mul_card K
  rw [← h3, ← h2, h1]
  ring


theorem case3_abs {Y : Type*} [Group Y] [Finite Y]
    (Ks Ts Ms Bs Rs : Subgroup Y) [Ks.Normal] (e : ↥Ks ≃* alternatingGroup (Fin 5))
    (hT : IsSylowTwoOf Ts ⊤)
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    (hKM : Ms ⊓ Ks = Ks ⊓ Subgroup.normalizer ((Ts ⊓ Ks : Subgroup Y) : Set Y))
    (hTB : Ts ≤ Bs) (hBM : Bs ≤ Ms) (hsup : Ks ⊔ Bs = ⊤)
    (h27 : ¬ 27 ∣ Nat.card Ms) (h9 : 9 ∣ Nat.card Bs)
    (hcop : ∀ (y : Y) (n : ℕ), y ^ n = 1 → Nat.Coprime n 6 → y ∈ Ks)
    (hRT : Rs ≤ Ts) (hRn : Bs ≤ Subgroup.normalizer (Rs : Set Y)) (hRp : IsPGroup 2 Rs)
    (hRmax : ∀ N : Subgroup Y, N ≤ Bs → Bs ≤ Subgroup.normalizer (N : Set Y) → IsPGroup 2 N →
      N ≤ Rs)
    (hRidx : 4 ≤ Rs.relIndex Ts) :
    Ms = Bs ∧ Nonempty (Y ≃* Perm (Fin 5) × Perm (Fin 3)) ∧ Ms.index = 5 ∧
      Rs = pCoreOf 2 Ms ∧ Nat.card Rs = 4 ∧ ∀ x ∈ Rs, x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsupM : Ks ⊔ Ms = ⊤ := eq_top_iff.2 (hsup ▸ sup_le_sup_left hBM _)
  set S₀ : Subgroup Y := Ts ⊓ Ks with hS₀
  have hSyl : IsSylowTwoOf S₀ Ks :=
    A4.isSylowTwoOf_inf_normal hT le_top Subgroup.le_normalizer_of_normal
  have hKcard : Nat.card Ks = 60 := card_of_alt5 e
  have hS₀card : Nat.card S₀ = 4 := card_sylow_of_alt5 e hSyl
  have hBk : Nat.card ↥(Ks ⊓ Subgroup.normalizer (S₀ : Set Y)) = 12 := card_inf_normalizer e hSyl
  have hMK : Nat.card ↥(Ms ⊓ Ks) = 12 := by rw [hKM]; exact hBk
  have hMK' : Nat.card ↥(Ks ⊓ Ms) = 12 := by rw [inf_comm]; exact hMK
  have hYM : Nat.card Y * 12 = 60 * Nat.card Ms := by
    have := card_mul_card_inf_of_sup_eq_top Ks Ms hsupM
    rwa [hMK', hKcard] at this
  have hYM5 : Nat.card Y = 5 * Nat.card Ms := by omega
  have hD := card_mul_card_inf_of_sup_eq_top Ks Bs hsup
  rw [hKcard] at hD
  have hDle : Ks ⊓ Bs ≤ Ks ⊓ Ms := inf_le_inf_left _ hBM
  have hS₀D : S₀ ≤ Ks ⊓ Bs := le_inf inf_le_right (inf_le_left.trans hTB)
  have hD4 : 4 ∣ Nat.card ↥(Ks ⊓ Bs) := hS₀card ▸ Subgroup.card_dvd_of_le hS₀D
  have hD12 : Nat.card ↥(Ks ⊓ Bs) ∣ 12 := hMK' ▸ Subgroup.card_dvd_of_le hDle
  have hMsBs : Ms = Bs := by
    have hDcases : Nat.card ↥(Ks ⊓ Bs) = 4 ∨ Nat.card ↥(Ks ⊓ Bs) = 12 := by
      obtain ⟨a, ha⟩ := hD4
      have hle : Nat.card ↥(Ks ⊓ Bs) ≤ 12 := Nat.le_of_dvd (by norm_num) hD12
      have hpos : 0 < Nat.card ↥(Ks ⊓ Bs) := Nat.card_pos
      have ha3 : a ≤ 3 := by omega
      have ha0 : 0 < a := by omega
      interval_cases a
      · left; omega
      · rw [ha] at hD12; exact absurd hD12 (by norm_num)
      · right; omega
    rcases hDcases with h4 | h12
    · exfalso
      rw [h4] at hD
      have h3 : Nat.card Ms = 3 * Nat.card Bs := by omega
      apply h27
      rw [h3]
      obtain ⟨c, hc⟩ := h9
      exact ⟨c, by rw [hc]; ring⟩
    · refine (Subgroup.eq_of_le_of_card_ge hBM ?_).symm
      rw [h12] at hD
      omega
  have hRM : Rs ≤ Ms := hRT.trans (hTB.trans hBM)
  have hMn : Ms ≤ Subgroup.normalizer (Rs : Set Y) := hMsBs ▸ hRn
  have hRcore : Rs = pCoreOf 2 Ms := by
    refine le_antisymm (le_pCoreOf_of_le_normalizer 2 hRM hMn hRp) ?_
    exact hRmax _ ((pCoreOf_le 2 Ms).trans hMsBs.le) (hMsBs ▸ le_normalizer_pCoreOf 2 Ms)
      (pCoreOf_isPGroup 2 Ms)
  have hBkn : Ms ≤ Subgroup.normalizer ((Ms ⊓ Ks : Subgroup Y) : Set Y) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxM, hxK⟩
      exact ⟨Ms.mul_mem (Ms.mul_mem hm hxM) (Ms.inv_mem hm),
        Subgroup.Normal.conj_mem inferInstance x hxK m⟩
    · rintro ⟨hxM, hxK⟩
      refine ⟨?_, ?_⟩
      · have := Ms.mul_mem (Ms.mul_mem (Ms.inv_mem hm) hxM) hm
        simpa [mul_assoc] using this
      · have := Subgroup.Normal.conj_mem (inferInstance : Ks.Normal) _ hxK m⁻¹
        simpa [mul_assoc] using this
  have hS₀le : S₀ ≤ Ms ⊓ Ks := by
    rw [hKM]
    exact le_inf inf_le_right Subgroup.le_normalizer
  have hS₀B : S₀ ≤ pCoreOf 2 (Ms ⊓ Ks) :=
    le_pCoreOf_of_le_normalizer 2 hS₀le (hKM ▸ inf_le_right) hSyl.2.1
  have hBkR : pCoreOf 2 (Ms ⊓ Ks) ≤ Rs := by
    rw [hRcore]
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans inf_le_left)
      (hBkn.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hS₀R : S₀ ≤ Rs := hS₀B.trans hBkR
  have hRc4 : 4 ≤ Nat.card Rs := hS₀card ▸ Subgroup.card_le_of_le hS₀R
  have hTsR : Rs.relIndex Ts * Nat.card Rs = Nat.card Ts := by
    have := Subgroup.relIndex_mul_card Rs Ts
    rwa [inf_of_le_left hRT] at this
  have hTs16 : 16 ≤ Nat.card Ts := by
    rw [← hTsR]
    nlinarith
  have h16 : 16 ∣ Nat.card Ts := by
    obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
    have hk4 : 4 ≤ k := by
      by_contra hlt
      push Not at hlt
      rw [hk] at hTs16
      interval_cases k <;> norm_num at hTs16
    rw [hk]
    have h4 : (2 : ℕ) ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 hk4
    norm_num at h4
    exact h4
  have hY16 : 16 ∣ Nat.card Y := h16.trans (Subgroup.card_subgroup_dvd_card Ts)
  have hY9 : 9 ∣ Nat.card Y := h9.trans (Subgroup.card_subgroup_dvd_card Bs)
  have hY5 : 5 ∣ Nat.card Y :=
    (show 5 ∣ 60 by norm_num).trans (hKcard ▸ Subgroup.card_subgroup_dvd_card Ks)
  have hY720 : 720 ∣ Nat.card Y := by
    have h144 : 144 ∣ Nat.card Y :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 16 9) hY16 hY9
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 144 5) h144 hY5
  have hsimple : IsSimpleGroup ↥Ks := by
    have := isSimpleGroup_alt5
    exact e.isSimpleGroup
  set C := Subgroup.centralizer (Ks : Set Y) with hC
  have hCn : C.Normal := inferInstance
  have hKC : Ks ⊓ C = ⊥ :=
    inf_eq_bot_of_commute hsimple (not_comm_of_mulEquiv e) fun x hx y hy =>
      Subgroup.mem_centralizer_iff.1 hy x hx
  have hCcom : ∀ x ∈ Ks, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 hy x hx
  have hCp : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥C → p = 2 ∨ p = 3 := by
    intro p hp hpd
    by_contra hne
    push Not at hne
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hpd
    have hcop' : Nat.Coprime p 6 := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h6
      rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 from h6) with h2 | h2
      · exact hne.1 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
      · exact hne.2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h2)
    have hc1 : ((c : Y)) ^ p = 1 := by
      rw [← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one]; rfl
    have hcK : (c : Y) ∈ Ks := hcop (c : Y) p hc1 hcop'
    have hmem : (c : Y) ∈ Ks ⊓ C := ⟨hcK, c.2⟩
    rw [hKC] at hmem
    have hc0 : c = 1 := Subtype.ext hmem
    rw [hc0, orderOf_one] at hc
    exact hp.one_lt.ne hc
  have hC9 : ¬ 9 ∣ Nat.card ↥C := by
    intro h9C
    have hsc := L1233.card_sup_of_commute hCcom hKC
    have hdvd : Nat.card ↥(Ks ⊔ C) ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card _
    rw [hsc, hKcard, hYM5] at hdvd
    obtain ⟨c, hc⟩ := h9C
    have h27' : 27 ∣ 5 * Nat.card Ms := by
      refine (show 27 ∣ 60 * Nat.card ↥C from ⟨20 * c, by rw [hc]; ring⟩).trans hdvd
    exact h27 ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 27 5)) h27')
  have hCO2 : ∀ N : Subgroup ↥C, N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hNp
    have hpN : pCoreOf 2 C = ⊥ := by
      refine hO2 _ ?_ (pCoreOf_isPGroup 2 C)
      have h1 : Subgroup.normalizer (C : Set Y) = ⊤ := Subgroup.normalizer_eq_top_iff.2 hCn
      have h2 := normalizer_le_normalizer_pCoreOf 2 C
      rw [h1] at h2
      exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 h2)
    have hcore : pCore 2 ↥C = ⊥ := by
      have : (pCore 2 ↥C).map C.subtype = ⊥ := hpN
      exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 this
    exact le_bot_iff.1 (hcore ▸ le_pCore 2 hN hNp)
  have hC6 : Nat.card ↥C ≤ 6 := card_le_six_of_primes hCp hC9 hCO2
  have hYC : Nat.card Y ≤ 120 * Nat.card ↥C := card_le_mul_centralizer_alt5 Ks e
  have hYle : Nat.card Y ≤ 720 := by omega
  have hY720' : Nat.card Y = 720 := by
    obtain ⟨k, hk⟩ := hY720
    have hpos : 0 < Nat.card Y := Nat.card_pos
    have : k = 1 := by
      rcases Nat.lt_or_ge k 2 with h | h
      · omega
      · omega
    rw [hk, this]
  have hCeq : Nat.card ↥C = 6 := by omega
  have hiso := nonempty_mulEquiv_perm_five_three Ks e hY720' hCeq hO2
  have hMs5 : Ms.index = 5 := by
    have h1 := Subgroup.card_mul_index Ms
    have hpos : 0 < Nat.card ↥Ms := Nat.card_pos
    rw [hYM5] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  have hTs : Nat.card Ts = 16 := by
    obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
    have hd : 2 ^ k ∣ 720 := hk ▸ (hY720' ▸ Subgroup.card_subgroup_dvd_card Ts)
    have hk4 : 4 ≤ k := by
      by_contra hlt
      push Not at hlt
      rw [hk] at hTs16
      interval_cases k <;> norm_num at hTs16
    have hk4' : k ≤ 4 := by
      by_contra hlt
      push Not at hlt
      have h5 : 2 ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := h5.trans hd
      norm_num at this
    have : k = 4 := le_antisymm hk4' hk4
    rw [hk, this]; norm_num
  have hRc : Nat.card Rs = 4 := by
    rw [hTs] at hTsR
    nlinarith
  have hSR : S₀ = Rs := Subgroup.eq_of_le_of_card_ge hS₀R (by omega)
  refine ⟨hMsBs, hiso, hMs5, hRcore, hRc, ?_⟩
  exact sq_eq_one_of_isPGroup_alt5 e (hSR ▸ inf_le_right) hRp

end CFSG.Quasithin.H13.S126P31
