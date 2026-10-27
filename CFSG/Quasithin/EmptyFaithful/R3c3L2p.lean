module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L2pB
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsGroup
public import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

namespace CFSG.Quasithin.R3c3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Unc25Small
open scoped MatrixGroups

section Arithmetic

theorem sixteen_dvd_psl2_order {p : ℕ} (h17 : 17 ≤ p)
    (hpow : (p % 8 = 1 ∧ ∃ m : ℕ, p = 2 ^ m + 1) ∨ (p % 8 = 7 ∧ ∃ m : ℕ, p + 1 = 2 ^ m)) :
    16 ∣ p * (p ^ 2 - 1) / 2 := by
  rcases hpow with ⟨-, m, hm⟩ | ⟨-, m, hm⟩
  · have hm4 : 4 ≤ m := by
      by_contra hlt
      have : 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨a, ha⟩ : 16 ∣ 2 ^ m := by
      have := pow_dvd_pow 2 hm4
      simpa using this
    have hpa : p = 16 * a + 1 := by omega
    have key : p * (p ^ 2 - 1) / 2 = 16 * ((16 * a + 1) * (8 * a ^ 2 + a)) := by
      apply Nat.div_eq_of_eq_mul_left (by norm_num)
      have h1 : (16 * a + 1) ^ 2 = 256 * a ^ 2 + 32 * a + 1 := by ring
      have h2 : (16 * a + 1) ^ 2 - 1 = 256 * a ^ 2 + 32 * a := by omega
      rw [hpa, h2]
      ring
    rw [key]
    exact Dvd.intro _ rfl
  · have hm5 : 5 ≤ m := by
      by_contra hlt
      have : 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨a, ha⟩ : 32 ∣ 2 ^ m := by
      have := pow_dvd_pow 2 hm5
      simpa using this
    obtain ⟨c, hc⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    have hpc : p = 32 * c + 31 := by omega
    have key : p * (p ^ 2 - 1) / 2 = 32 * (p * (16 * c ^ 2 + 31 * c + 15)) := by
      apply Nat.div_eq_of_eq_mul_left (by norm_num)
      have h1 : (32 * c + 31) ^ 2 = 1024 * c ^ 2 + 1984 * c + 961 := by ring
      have h2 : (32 * c + 31) ^ 2 - 1 = 1024 * c ^ 2 + 1984 * c + 960 := by omega
      rw [hpc, h2]
      ring
    rw [key]
    exact (by norm_num : (16 : ℕ) ∣ 32).mul_right _

end Arithmetic

section PSL2

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem sixteen_dvd_card_psl2 (H : L2pHyp K p) (h17 : 17 ≤ p) : 16 ∣ Nat.card PSL(2, K) := by
  rw [CFSG.GorensteinWalter.psl2_card_formula K H.odd, H.hK]
  exact sixteen_dvd_psl2_order h17 H.hpow

theorem sixteen_dvd_card_sylow (H : L2pHyp K p) (h17 : 17 ≤ p) {P : Subgroup PSL(2, K)}
    (hP : IsSylowTwoOf P ⊤) : 16 ∣ Nat.card P := by
  have h16 := sixteen_dvd_card_psl2 H h17
  have hv : 4 ≤ (Nat.card PSL(2, K)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
      (by simpa using h16)
  have hc : Nat.card P = 2 ^ (Nat.card PSL(2, K)).factorization 2 := by
    rw [hP.card_eq]
    simp [twoPart]
  rw [hc]
  have := pow_dvd_pow 2 hv
  simpa using this

theorem isPGroup_centralizer_involution (H : L2pHyp K p) {t : PSL(2, K)} (ht : t * t = 1)
    (ht1 : t ≠ 1) : IsPGroup 2 ↥(Subgroup.centralizer ({t} : Set PSL(2, K))) :=
  Unc25K1.psl2_cent_two H.hp7 H.hK H.hpow t (orderOf_eq_prime (by rw [pow_two]; exact ht) ht1)

theorem eq_one_of_commute_involution_of_pow_eq_one (H : L2pHyp K p) {t : PSL(2, K)}
    (ht : t * t = 1) (ht1 : t ≠ 1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {m : PSL(2, K)}
    (hm : m ∈ Subgroup.centralizer ({t} : Set PSL(2, K))) (hmr : m ^ r = 1) : m = 1 := by
  obtain ⟨k, hk⟩ := isPGroup_centralizer_involution H ht ht1 ⟨m, hm⟩
  have hk' : m ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) r :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
  have := pow_gcd_eq_one.2 ⟨hk', hmr⟩
  rwa [hcop, pow_one] at this

theorem invert_of_involution (H : L2pHyp K p) {N : Subgroup PSL(2, K)}
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hexp : ∀ x ∈ N, x ^ r = 1) {t : PSL(2, K)} (ht : t * t = 1) (ht1 : t ≠ 1)
    (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) {n : PSL(2, K)} (hn : n ∈ N) : t * n * t⁻¹ = n⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hn' : t * n * t⁻¹ ∈ N := htN n hn
  have hm : n * (t * n * t⁻¹) ∈ N := N.mul_mem hn hn'
  have hc : t * (n * (t * n * t⁻¹)) * t⁻¹ = n * (t * n * t⁻¹) := by
    have h1 : t * (n * (t * n * t⁻¹)) * t⁻¹ = (t * n * t⁻¹) * (t * (t * n * t⁻¹) * t⁻¹) := by group
    have h2 : t * (t * n * t⁻¹) * t⁻¹ = n := by
      calc t * (t * n * t⁻¹) * t⁻¹ = (t * t) * n * (t⁻¹ * t⁻¹) := by group
        _ = n := by rw [ht, htinv, ht]; group
    rw [h1, h2, hcomm _ hn' _ hn]
  have hmc : n * (t * n * t⁻¹) ∈ Subgroup.centralizer ({t} : Set PSL(2, K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : t * (n * (t * n * t⁻¹)) = n * (t * n * t⁻¹) * t := by
      calc t * (n * (t * n * t⁻¹)) = t * (n * (t * n * t⁻¹)) * t⁻¹ * t := by group
        _ = n * (t * n * t⁻¹) * t := by rw [hc]
    exact this.symm
  have hmr : (n * (t * n * t⁻¹)) ^ r = 1 := by
    have hmN := hexp _ hm
    exact hmN
  have h1 := eq_one_of_commute_involution_of_pow_eq_one H ht ht1 hr hr2 hmc hmr
  exact eq_inv_of_mul_eq_one_right h1

theorem eq_bot_of_normal_odd (H : L2pHyp K p) {P Q N : Subgroup PSL(2, K)} (hP : IsSylowTwoOf P ⊤)
    (hPQ : P ≤ Q) (hNQ : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hexp : ∀ x ∈ N, x ^ r = 1) : N = ⊥ := by
  obtain ⟨m, hm2, ⟨eP⟩⟩ := psl2_sylow_dihedral H P hP
  set k : ZMod (2 ^ m) := ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) with hk
  have h2m1 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hk2 : k + k = ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [hk, ← Nat.cast_add, h2m1]
    congr 1
    omega
  have hk4 : k + k + (k + k) = 0 := by
    rw [hk2, ← Nat.cast_add]
    have : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by omega
    rw [this]
    exact ZMod.natCast_self _
  have hk2ne : k + k ≠ 0 := by
    rw [hk2]
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have hle := Nat.le_of_dvd (by positivity) h
    have : 0 < 2 ^ (m - 1) := by positivity
    omega
  let s0 : ↥P := eP.symm (DihedralGroup.sr 0)
  let v : ↥P := eP.symm (DihedralGroup.r k)
  have hs0sq : s0 * s0 = 1 := by
    rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
  have hs1sq : (s0 * v) * (s0 * v) = 1 := by
    have : s0 * v = eP.symm (DihedralGroup.sr (0 + k)) := by
      rw [← map_mul, DihedralGroup.sr_mul_r]
    rw [this, ← map_mul, DihedralGroup.sr_mul_self, map_one]
  have ht0sq : (v * v) * (v * v) = 1 := by
    have : v * v = eP.symm (DihedralGroup.r (k + k)) := by
      rw [← map_mul, DihedralGroup.r_mul_r]
    rw [this, ← map_mul, DihedralGroup.r_mul_r, hk4]
    exact (map_one eP.symm).trans rfl
  have hs0ne : s0 ≠ 1 := by
    intro h
    have : DihedralGroup.sr (0 : ZMod (2 ^ m)) = 1 := by
      have := congrArg eP h
      simpa [s0] using this
    rw [DihedralGroup.one_def] at this
    cases this
  have hs1ne : s0 * v ≠ 1 := by
    intro h
    have : DihedralGroup.sr (0 + k) = (1 : DihedralGroup (2 ^ m)) := by
      have h' := congrArg eP h
      rw [map_mul] at h'
      simpa [s0, v, DihedralGroup.sr_mul_r] using h'
    rw [DihedralGroup.one_def] at this
    cases this
  have ht0ne : v * v ≠ 1 := by
    intro h
    have h' := congrArg eP h
    rw [map_mul, map_one] at h'
    simp only [v, MulEquiv.apply_symm_apply, DihedralGroup.r_mul_r] at h'
    rw [DihedralGroup.one_def] at h'
    have := DihedralGroup.r.inj h'
    exact hk2ne this
  have htN : ∀ t : ↥P, ∀ n ∈ N, (t : PSL(2, K)) * n * (t : PSL(2, K))⁻¹ ∈ N :=
    fun t n hn => hNQ _ (hPQ t.2) n hn
  have hcoe1 : ∀ t : ↥P, t ≠ 1 → (t : PSL(2, K)) ≠ 1 := fun t ht h =>
    ht (Subtype.ext h)
  have hcoe2 : ∀ t : ↥P, t * t = 1 → (t : PSL(2, K)) * (t : PSL(2, K)) = 1 := fun t h =>
    congrArg Subtype.val h
  have hinv : ∀ t : ↥P, t ≠ 1 → t * t = 1 → ∀ n ∈ N,
      (t : PSL(2, K)) * n * (t : PSL(2, K))⁻¹ = n⁻¹ := fun t ht1 ht2 n hn =>
    invert_of_involution H hcomm hr hr2 hexp (hcoe2 t ht2) (hcoe1 t ht1) (htN t) hn
  have hS0 := hinv s0 hs0ne hs0sq
  have hS1 := hinv (s0 * v) hs1ne hs1sq
  have hT0 := hinv (v * v) ht0ne ht0sq
  have hv : ∀ n ∈ N, (v : PSL(2, K)) * n * (v : PSL(2, K))⁻¹ = n := by
    intro n hn
    have h0 : (s0 : PSL(2, K)) * (s0 : PSL(2, K)) = 1 := hcoe2 s0 hs0sq
    have h1 := hS1 n hn
    have h0n := hS0 n hn
    have e1 : ((s0 * v : ↥P) : PSL(2, K)) = (s0 : PSL(2, K)) * (v : PSL(2, K)) := rfl
    rw [e1] at h1
    have hs0inv : (s0 : PSL(2, K))⁻¹ = (s0 : PSL(2, K)) := inv_eq_of_mul_eq_one_right h0
    have hb : (v : PSL(2, K)) = (s0 : PSL(2, K)) * ((s0 : PSL(2, K)) * (v : PSL(2, K))) := by
      rw [← mul_assoc, h0, one_mul]
    calc (v : PSL(2, K)) * n * (v : PSL(2, K))⁻¹
        = ((s0 : PSL(2, K)) * ((s0 : PSL(2, K)) * (v : PSL(2, K)))) * n *
            ((s0 : PSL(2, K)) * ((s0 : PSL(2, K)) * (v : PSL(2, K))))⁻¹ := by rw [← hb]
      _ = (s0 : PSL(2, K)) * (((s0 : PSL(2, K)) * (v : PSL(2, K))) * n *
            ((s0 : PSL(2, K)) * (v : PSL(2, K)))⁻¹) * (s0 : PSL(2, K))⁻¹ := by group
      _ = (s0 : PSL(2, K)) * n⁻¹ * (s0 : PSL(2, K))⁻¹ := by rw [h1]
      _ = ((s0 : PSL(2, K)) * n * (s0 : PSL(2, K))⁻¹)⁻¹ := by group
      _ = n := by rw [h0n, inv_inv]
  refine (Subgroup.eq_bot_iff_forall N).2 fun n hn => ?_
  have h3 := hT0 n hn
  have e : ((v * v : ↥P) : PSL(2, K)) = (v : PSL(2, K)) * (v : PSL(2, K)) := rfl
  rw [e] at h3
  have h4 : (v : PSL(2, K)) * (v : PSL(2, K)) * n * ((v : PSL(2, K)) * (v : PSL(2, K)))⁻¹ = n := by
    calc (v : PSL(2, K)) * (v : PSL(2, K)) * n * ((v : PSL(2, K)) * (v : PSL(2, K)))⁻¹
        = (v : PSL(2, K)) * ((v : PSL(2, K)) * n * (v : PSL(2, K))⁻¹) * (v : PSL(2, K))⁻¹ := by
          group
      _ = n := by rw [hv n hn, hv n hn]
  have hnn : n = n⁻¹ := h4.symm.trans h3
  have hn2 : n ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [hnn]
    exact inv_mul_cancel n
  have hcop : Nat.gcd 2 r = 1 := (Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2)
  have := pow_gcd_eq_one.2 ⟨hn2, hexp n hn⟩
  rwa [hcop, pow_one] at this

theorem false_of_normal_two (H : L2pHyp K p)
    {P Q N : Subgroup PSL(2, K)} (h16 : 16 ∣ Nat.card P) (hPQ : P ≤ Q)
    (hNQ : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hexp : ∀ x ∈ N, x * x = 1) (hN : N ≠ ⊥) (h3 : 3 ∣ Nat.card Q) : False := by
  by_cases hbig : ∃ a ∈ N, ∃ b ∈ N, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b
  · obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := hbig
    have hF4 : IsFourSubgroup (Subgroup.closure ({a, b} : Set PSL(2, K))) :=
      Unc25K1.isFourSubgroup_of_pair (hexp a ha) (hexp b hb) (hcomm a ha b hb) ha1 hb1 hab
    set F := Subgroup.closure ({a, b} : Set PSL(2, K)) with hF
    have hFN : F ≤ N := by
      refine (Subgroup.closure_le N).2 ?_
      intro x hx
      rcases hx with rfl | hx
      · exact ha
      · rw [Set.mem_singleton_iff.mp hx]
        exact hb
    have hcent : Subgroup.centralizer (F : Set PSL(2, K)) = F :=
      psl2_centralizer_kleinFour H (isKleinFour_of_isFourSubgroup hF4)
    have hNF : N ≤ F := by
      intro n hn
      have : n ∈ Subgroup.centralizer (F : Set PSL(2, K)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        exact hcomm f (hFN hf) n hn
      rwa [hcent] at this
    have hNeq : N = F := le_antisymm hNF hFN
    obtain ⟨e⟩ := psl2_four_normalizer H F hF4
    have hcard : Nat.card ↥(Subgroup.normalizer (F : Set PSL(2, K))) = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    have hQle : Q ≤ Subgroup.normalizer (F : Set PSL(2, K)) := by
      intro q hq
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [← hNeq]
      refine ⟨fun hh => hNQ q hq h hh, fun hh => ?_⟩
      have := hNQ q⁻¹ (Q.inv_mem hq) _ hh
      simpa [mul_assoc] using this
    have hdvd : Nat.card Q ∣ 24 := hcard ▸ Subgroup.card_dvd_of_le hQle
    have h16Q : 16 ∣ Nat.card Q := h16.trans (Subgroup.card_dvd_of_le hPQ)
    have hle : Nat.card Q ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have hq16 : Nat.card Q = 16 := by omega
    rw [hq16] at hdvd
    exact absurd hdvd (by norm_num)
  · push Not at hbig
    obtain ⟨n₀, hn₀, hn₀1⟩ : ∃ n ∈ N, n ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hN ((Subgroup.eq_bot_iff_forall N).2 hcon)
    have hC2 := isPGroup_centralizer_involution H (hexp n₀ hn₀) hn₀1
    have hQle : Q ≤ Subgroup.centralizer ({n₀} : Set PSL(2, K)) := by
      intro q hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hNQ q hq n₀ hn₀
      have h2 : q * n₀ * q⁻¹ ≠ 1 := by
        intro h
        apply hn₀1
        have := congrArg (fun x => q⁻¹ * x * q) h
        simpa [mul_assoc] using this
      have h3 := hbig _ h1 n₀ hn₀ h2 hn₀1
      calc q * n₀ = q * n₀ * q⁻¹ * q := by group
        _ = n₀ * q := by rw [h3]
    exact R3c.not_three_dvd_card_of_isPGroup_two (IsPGroup.to_le hC2 hQle) h3

theorem not_three_dvd_of_solvable_sylow
    (H : L2pHyp K p) (h17 : 17 ≤ p) {P Q : Subgroup PSL(2, K)} (hP : IsSylowTwoOf P ⊤) (hPQ : P ≤ Q)
    (hQ : Group.IsSolvable ↥Q) : ¬ 3 ∣ Nat.card Q := by
  intro h3
  have h16 := sixteen_dvd_card_sylow H h17 hP
  have hQnt : Nontrivial ↥Q := by
    refine Finite.one_lt_card_iff_nontrivial.1 ?_
    have := Nat.le_of_dvd Nat.card_pos h3
    omega
  obtain ⟨M, hMn, hMne, hMmin⟩ := CFSG.exists_minimal_normal hQ hQnt
  have : M.Normal := hMn
  have : CFSG.IsMinimalNormal M := ⟨fun K' [hK : K'.Normal] hKM => by
    by_cases h : K' = ⊥
    · exact Or.inl h
    · exact Or.inr (hMmin K' hK hKM h)⟩
  have : Group.IsSolvable ↥Q := hQ
  obtain ⟨r, hr, hea⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian M
  have := hea
  set N : Subgroup PSL(2, K) := M.map Q.subtype with hN
  have hNQ : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N := by
    intro q hq n hn
    obtain ⟨y, hy, rfl⟩ := hn
    exact ⟨⟨q, hq⟩ * y * ⟨q, hq⟩⁻¹, hMn.conj_mem y hy ⟨q, hq⟩, rfl⟩
  have hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    have := hea.toIsMulCommutative.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩
    exact congrArg (fun w : ↥M => ((w : ↥Q) : PSL(2, K))) this
  have hexp : ∀ x ∈ N, x ^ r = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := r) (A := M) y hy
    exact congrArg Subtype.val this
  have hN0 : N ≠ ⊥ := by
    intro h
    apply hMne
    rw [eq_bot_iff]
    intro y hy
    have : (y : PSL(2, K)) ∈ N := ⟨y, hy, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  by_cases hr2 : r = 2
  · subst hr2
    exact false_of_normal_two H h16 hPQ hNQ hcomm
      (fun x hx => by have := hexp x hx; rwa [pow_two] at this) hN0 h3
  · exact hN0 (eq_bot_of_normal_odd H hP hPQ hNQ hcomm hr hr2 hexp)

end PSL2

section Transport

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_top_map {H : Type} [Group H] [Finite H] {L P : Subgroup G}
    (hP : IsSylowTwoOf P L) (e : ↥L ≃* H) :
    IsSylowTwoOf ((P.subgroupOf L).map e.toMonoidHom) ⊤ := by
  have hP2 := hP.2.1
  have hPcard := hP.card_eq
  refine isSylowTwoOf_iff.2 ⟨le_top, ?_, ?_⟩
  · exact hP2.of_equiv
      ((Subgroup.subgroupOfEquivOfLe hP.1).symm.trans
        (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective))
  · have h1 : Nat.card ↥((P.subgroupOf L).map e.toMonoidHom) = Nat.card P := by
      rw [Subgroup.card_map_of_injective e.injective]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv
    rw [h1, hPcard]
    have h2 : Nat.card ↥(⊤ : Subgroup H) = Nat.card ↥L := by
      rw [Subgroup.card_top]
      exact (Nat.card_congr e.toEquiv).symm
    simp only [twoPart, h2]

theorem not_three_dvd_of_solvable_sylow_of_mulEquiv {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] (H : L2pHyp K p)
    (h17 : 17 ≤ p) {L P Q : Subgroup G} (e : ↥L ≃* PSL(2, K)) (hP : IsSylowTwoOf P L) (hPQ : P ≤ Q)
    (hQL : Q ≤ L) (hQ : Group.IsSolvable ↥Q) : ¬ 3 ∣ Nat.card Q := by
  have hP' := isSylowTwoOf_top_map hP e
  have hPQ' : (P.subgroupOf L).map e.toMonoidHom ≤ (Q.subgroupOf L).map e.toMonoidHom :=
    Subgroup.map_mono (Subgroup.comap_mono hPQ)
  have hcard : Nat.card ↥((Q.subgroupOf L).map e.toMonoidHom) = Nat.card Q := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
  have hsolv : Group.IsSolvable ↥((Q.subgroupOf L).map e.toMonoidHom) := by
    have : Group.IsSolvable ↥Q := hQ
    refine Group.isSolvable_of_isSolvable_injective
      (f := ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).symm.trans
        (Subgroup.subgroupOfEquivOfLe hQL)).toMonoidHom) (MulEquiv.injective _)
  rw [← hcard]
  exact not_three_dvd_of_solvable_sylow H h17 hP' hPQ' hsolv

end Transport

end CFSG.Quasithin.R3c3
