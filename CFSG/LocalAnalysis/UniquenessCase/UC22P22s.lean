module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)

variable {G : Type} [Group G] [Finite G]

namespace P22s

omit [Finite G] in
theorem exists_mul_of_mem_sup {N S : Subgroup G} (hSN : S ≤ normalizer (N : Set G)) {h : G}
    (hh : h ∈ N ⊔ S) : ∃ n ∈ N, ∃ s ∈ S, h = n * s := by
  rw [Subgroup.sup_eq_closure] at hh
  induction hh using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, S.one_mem, by simp⟩
    · exact ⟨1, N.one_mem, x, hx, by simp⟩
  | inv_mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x⁻¹, N.inv_mem hx, 1, S.one_mem, by simp⟩
    · exact ⟨1, N.one_mem, x⁻¹, S.inv_mem hx, by simp⟩
  | one => exact ⟨1, N.one_mem, 1, S.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, s, hs, rfl⟩ := hx
    obtain ⟨n', hn', s', hs', rfl⟩ := hy
    refine ⟨n * (s * n' * s⁻¹), N.mul_mem hn ((mem_normalizer_iff.1 (hSN hs) n').1 hn'), s * s',
      S.mul_mem hs hs', by group⟩

omit [Finite G] in
theorem exists_pow_eq_mul {N : Subgroup G} {n s : G} (hn : n ∈ N) (hs : s ∈ normalizer (N : Set G))
    (k : ℕ) : ∃ n' ∈ N, (n * s) ^ k = n' * s ^ k := by
  induction k with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨n', hn', he⟩ := ih
    have hsk : s ^ k ∈ normalizer (N : Set G) := pow_mem hs k
    refine ⟨n' * (s ^ k * n * (s ^ k)⁻¹), N.mul_mem hn' ((mem_normalizer_iff.1 hsk n).1 hn), ?_⟩
    rw [pow_succ, he, pow_succ]
    group

theorem exists_two_pow_mem_of_mem_sup {N S : Subgroup G} (hS : IsPGroup 2 S)
    (hSN : S ≤ normalizer (N : Set G)) {h : G} (hh : h ∈ N ⊔ S) : ∃ k : ℕ, h ^ (2 ^ k) ∈ N := by
  obtain ⟨n, hn, s, hs, rfl⟩ := exists_mul_of_mem_sup hSN hh
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hk' : s ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨n', hn', he⟩ := exists_pow_eq_mul hn (hSN hs) (2 ^ k)
  exact ⟨k, by rw [he, hk', mul_one]; exact hn'⟩

omit [Finite G] in
theorem conj_eq_of_commute_commutator {y q : G} {r : ℕ} (hr : Odd r) (hy : y ^ r = 1)
    (hc2 : ∃ b : ℕ, (y * q * y⁻¹ * q⁻¹) ^ (2 ^ b) = 1)
    (hcomm : y * (y * q * y⁻¹ * q⁻¹) = (y * q * y⁻¹ * q⁻¹) * y) : y * q * y⁻¹ = q := by
  set c := y * q * y⁻¹ * q⁻¹ with hc
  have hyc : y * c * y⁻¹ = c := by rw [hcomm]; group
  have hyck : ∀ k : ℕ, y * c ^ k * y⁻¹ = c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y * c ^ (k + 1) * y⁻¹ = (y * c ^ k * y⁻¹) * (y * c * y⁻¹) := by rw [pow_succ]; group
        _ = c ^ (k + 1) := by rw [ih, hyc, pow_succ]
  have hpow : ∀ k : ℕ, y ^ k * q * (y ^ k)⁻¹ = c ^ k * q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y ^ (k + 1) * q * (y ^ (k + 1))⁻¹ = y * (y ^ k * q * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
        _ = (y * c ^ k * y⁻¹) * (y * q * y⁻¹) := by rw [ih]; group
        _ = c ^ k * (c * q) := by rw [hyck k, hc]; group
        _ = c ^ (k + 1) * q := by rw [pow_succ]; group
  have hcr : c ^ r = 1 := by
    have h1 := hpow r
    rw [hy] at h1
    have : q = c ^ r * q := by simpa using h1
    have h2 := congrArg (fun z => z * q⁻¹) this
    simpa using h2.symm
  obtain ⟨b, hb⟩ := hc2
  have hdvd1 : orderOf c ∣ r := orderOf_dvd_of_pow_eq_one hcr
  have hdvd2 : orderOf c ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hb
  have hcop : Nat.Coprime r (2 ^ b) :=
    Nat.Coprime.pow_right b ((Nat.coprime_two_right).2 hr)
  have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have hc1 : c = 1 := orderOf_eq_one_iff.1 h1
  have : y * q * y⁻¹ * q⁻¹ * q = q := by rw [← hc, hc1, one_mul]
  simpa using this

omit [Finite G] in
theorem mem_normalizer_centralizer {P : Subgroup G} {h : G} (hh : h ∈ normalizer (P : Set G)) :
    h ∈ normalizer (centralizer (P : Set G) : Set G) := by
  have key : ∀ h ∈ normalizer (P : Set G), ∀ z ∈ centralizer (P : Set G),
      h * z * h⁻¹ ∈ centralizer (P : Set G) := by
    intro h hh z hz
    rw [mem_centralizer_iff] at hz ⊢
    intro p hp
    have hp' : h⁻¹ * p * h⁻¹⁻¹ ∈ P := (mem_normalizer_iff.1 (inv_mem hh) p).1 hp
    have := hz _ hp'
    calc p * (h * z * h⁻¹) = h * ((h⁻¹ * p * h⁻¹⁻¹) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * p * h⁻¹⁻¹)) * h⁻¹ := by rw [this]
      _ = h * z * h⁻¹ * p := by group
  rw [mem_normalizer_iff]
  intro z
  refine ⟨fun hz => key h hh z hz, fun hz => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hz
  simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_inf' {A B : Subgroup G} {h : G} (hA : h ∈ normalizer (A : Set G))
    (hB : h ∈ normalizer (B : Set G)) : h ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨hzA, hzB⟩
    exact ⟨(mem_normalizer_iff.1 hA z).1 hzA, (mem_normalizer_iff.1 hB z).1 hzB⟩
  · rintro ⟨hzA, hzB⟩
    exact ⟨(mem_normalizer_iff.1 hA z).2 hzA, (mem_normalizer_iff.1 hB z).2 hzB⟩

end P22s

open P22s

theorem uc22p22s_centralizer_pCore_sup_le {M N Ni S : Subgroup G}
    (hQ : M ⊓ centralizer (CFSG.Open.pCoreOf 2 M : Set G) ≤ CFSG.Open.pCoreOf 2 M)
    (hNM : N ≤ M) (hN : M ≤ normalizer (N : Set G)) (hNiN : Ni ≤ N)
    (hQN : CFSG.Open.pCoreOf 2 M ⊓ N ≤ Ni) (hS : IsPGroup 2 S) (hSM : S ≤ M)
    (hSNi : S ≤ normalizer (Ni : Set G)) :
    (Ni ⊔ S) ⊓ centralizer (CFSG.Open.pCoreOf 2 (Ni ⊔ S) : Set G) ≤ CFSG.Open.pCoreOf 2 (Ni ⊔ S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M with hQdef
  set H : Subgroup G := Ni ⊔ S with hHdef
  set P : Subgroup G := CFSG.Open.pCoreOf 2 H with hPdef
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMQ : M ≤ normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hHP : H ≤ normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hNiM : Ni ≤ M := hNiN.trans hNM
  have hHM : H ≤ M := sup_le hNiM hSM
  have hHNi : H ≤ normalizer (Ni : Set G) := sup_le Subgroup.le_normalizer hSNi
  have h1 : Q ⊓ Ni ≤ P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_right.trans le_sup_left)
      (fun h hh => mem_normalizer_inf' (hMQ (hHM hh)) (hHNi hh)) (hQ2.to_le inf_le_left)
  have h2 : IsPGroup 2 ↥(H ⊓ centralizer (P : Set G)) := by
    rintro ⟨x, hxH, hxC⟩
    obtain ⟨e, r, hr, hor⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    set y : G := x ^ (2 ^ e) with hydef
    have hyr : y ^ r = 1 := by rw [hydef, ← pow_mul, ← hor, pow_orderOf_eq_one]
    have hyH : y ∈ H := pow_mem hxH _
    have hyC : y ∈ centralizer (P : Set G) := pow_mem hxC _
    have hyNi : y ∈ Ni := by
      obtain ⟨j, hj⟩ := exists_two_pow_mem_of_mem_sup hS hSNi hyH
      have hcop : (2 ^ j).gcd (orderOf y) = 1 := by
        have hdvd : orderOf y ∣ r := orderOf_dvd_of_pow_eq_one hyr
        have : Nat.Coprime (2 ^ j) r :=
          Nat.Coprime.pow_left j ((Nat.coprime_two_left).2 hr)
        exact Nat.Coprime.coprime_dvd_right hdvd this
      have hmem : y ∈ zpowers (y ^ (2 ^ j)) := mem_zpowers_pow_iff.2 hcop
      exact (zpowers_le.2 hj) hmem
    have hyM : y ∈ M := hHM hyH
    have hyN : y ∈ N := hNiN hyNi
    have hyQ : ∀ q ∈ Q, y * q * y⁻¹ = q := by
      intro q hq
      have hcQ : y * q * y⁻¹ * q⁻¹ ∈ Q :=
        Q.mul_mem ((mem_normalizer_iff.1 (hMQ hyM) q).1 hq) (Q.inv_mem hq)
      have hqM : q ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hq
      have hcN : y * q * y⁻¹ * q⁻¹ ∈ N := by
        have h' : q * y⁻¹ * q⁻¹ ∈ N := (mem_normalizer_iff.1 (hN hqM) y⁻¹).1 (N.inv_mem hyN)
        have := N.mul_mem hyN h'
        simpa [mul_assoc] using this
      have hcP : y * q * y⁻¹ * q⁻¹ ∈ P := h1 ⟨hcQ, hQN ⟨hcQ, hcN⟩⟩
      have hcomm := (mem_centralizer_iff.1 hyC) _ hcP
      have hc2 : ∃ b : ℕ, (y * q * y⁻¹ * q⁻¹) ^ (2 ^ b) = 1 := by
        obtain ⟨b, hb⟩ := hQ2 ⟨_, hcQ⟩
        exact ⟨b, by simpa using congrArg Subtype.val hb⟩
      exact conj_eq_of_commute_commutator hr hyr hc2 hcomm.symm
    have hyCQ : y ∈ centralizer (Q : Set G) := by
      rw [mem_centralizer_iff]
      intro q hq
      have := hyQ q hq
      calc q * y = (y * q * y⁻¹) * y := by rw [this]
        _ = y * q := by group
    have hyQ' : y ∈ Q := hQ ⟨hyM, hyCQ⟩
    obtain ⟨b, hb⟩ := hQ2 ⟨y, hyQ'⟩
    have hb' : y ^ (2 ^ b) = 1 := by simpa using congrArg Subtype.val hb
    have hcop : Nat.Coprime r (2 ^ b) :=
      Nat.Coprime.pow_right b ((Nat.coprime_two_right).2 hr)
    have hy1 : y = 1 := orderOf_eq_one_iff.1
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hyr) (orderOf_dvd_of_pow_eq_one hb'))
    refine ⟨e, ?_⟩
    ext
    simp [← hydef, hy1]
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun h hh => mem_normalizer_inf' (Subgroup.le_normalizer hh)
      (mem_normalizer_centralizer (hHP hh))) h2

end CFSG.LocalAnalysis.UniquenessCase.UC22
