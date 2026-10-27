module

public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Ly
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Suz.Simple
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.ON.Simple
public import CFSG.Sporadic.Co3
public import CFSG.Sporadic.Co2
public import CFSG.Sporadic.HN
public import CFSG.Sporadic.Th.Certificate

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Blueprint TauCeti

@[expose] def SporadicPairNC (s : SporadicName) (p : ℕ) : Prop :=
  (s = .J4 ∧ p = 11) ∨ (s = .McL ∧ p = 5) ∨ (s = .Ly ∧ p = 5) ∨ (s = .HS ∧ p = 5) ∨
    (s = .He ∧ p = 7) ∨ (s = .Ru ∧ p = 5) ∨ (s = .ONan ∧ p = 7) ∨ (s = .Co3 ∧ p = 5) ∨
    (s = .Co2 ∧ p = 5) ∨ (s = .HN ∧ p = 5) ∨ (s = .Th ∧ p = 5)

@[expose] def SporadicPairAb (s : SporadicName) (p : ℕ) : Prop :=
  (s = .J2 ∧ p = 5) ∨ (s = .He ∧ p = 5) ∨ (s = .Suz ∧ p = 5) ∨ (s = .Th ∧ p = 7)

@[expose] def SporadicPair (s : SporadicName) (p : ℕ) : Prop :=
  SporadicPairNC s p ∨ SporadicPairAb s p


theorem sqdvd_M11 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 7920) : SporadicPair .M11 p := by
  have h1 : p ∈ Nat.primeFactors 7920 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 7920 = {2, 3, 5, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_M12 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 95040) : SporadicPair .M12 p := by
  have h1 : p ∈ Nat.primeFactors 95040 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 95040 = {2, 3, 5, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_M22 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 443520) : SporadicPair .M22 p := by
  have h1 : p ∈ Nat.primeFactors 443520 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 443520 = {2, 3, 5, 7, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_M23 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 10200960) : SporadicPair .M23 p := by
  have h1 : p ∈ Nat.primeFactors 10200960 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 10200960 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_M24 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 244823040) : SporadicPair .M24 p := by
  have h1 : p ∈ Nat.primeFactors 244823040 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 244823040 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_J1 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 175560) : SporadicPair .J1 p := by
  have h1 : p ∈ Nat.primeFactors 175560 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 175560 = {2, 3, 5, 7, 11, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_J2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 604800) : SporadicPair .J2 p := by
  have h1 : p ∈ Nat.primeFactors 604800 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 604800 = {2, 3, 5, 7} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl
  · omega
  · omega
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h

theorem sqdvd_J3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 50232960) : SporadicPair .J3 p := by
  have h1 : p ∈ Nat.primeFactors 50232960 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 50232960 = {2, 3, 5, 17, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_J4 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 86775571046077562880) : SporadicPair .J4 p := by
  have h1 : p ∈ Nat.primeFactors 86775571046077562880 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 86775571046077562880 = {2, 3, 5, 7, 11, 23, 29, 31, 37, 43} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_McL {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 898128000) : SporadicPair .McL p := by
  have h1 : p ∈ Nat.primeFactors 898128000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 898128000 = {2, 3, 5, 7, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_Ly {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 51765179004000000) : SporadicPair .Ly p := by
  have h1 : p ∈ Nat.primeFactors 51765179004000000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 51765179004000000 = {2, 3, 5, 7, 11, 31, 37, 67} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_HS {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 44352000) : SporadicPair .HS p := by
  have h1 : p ∈ Nat.primeFactors 44352000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 44352000 = {2, 3, 5, 7, 11} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_He {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 4030387200) : SporadicPair .He p := by
  have h1 : p ∈ Nat.primeFactors 4030387200 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 4030387200 = {2, 3, 5, 7, 17} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h

theorem sqdvd_Suz {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 448345497600) : SporadicPair .Suz p := by
  have h1 : p ∈ Nat.primeFactors 448345497600 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 448345497600 = {2, 3, 5, 7, 11, 13} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_Ru {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 145926144000) : SporadicPair .Ru p := by
  have h1 : p ∈ Nat.primeFactors 145926144000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 145926144000 = {2, 3, 5, 7, 13, 29} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_ONan {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 460815505920) : SporadicPair .ONan p := by
  have h1 : p ∈ Nat.primeFactors 460815505920 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 460815505920 = {2, 3, 5, 7, 11, 19, 31} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exfalso; norm_num at h
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_Co3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 495766656000) : SporadicPair .Co3 p := by
  have h1 : p ∈ Nat.primeFactors 495766656000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 495766656000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_Co2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 42305421312000) : SporadicPair .Co2 p := by
  have h1 : p ∈ Nat.primeFactors 42305421312000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 42305421312000 = {2, 3, 5, 7, 11, 23} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_HN {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 273030912000000) : SporadicPair .HN p := by
  have h1 : p ∈ Nat.primeFactors 273030912000000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 273030912000000 = {2, 3, 5, 7, 11, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem sqdvd_Th {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ 90745943887872000) : SporadicPair .Th p := by
  have h1 : p ∈ Nat.primeFactors 90745943887872000 :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h, by norm_num⟩
  have hpf : Nat.primeFactors 90745943887872000 = {2, 3, 5, 7, 13, 19, 31} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · simp [SporadicPair, SporadicPairNC, SporadicPairAb]
  · exfalso; norm_num at h
  · exfalso; norm_num at h
  · exfalso; norm_num at h

theorem card_M23 :
    Nat.card NativeSporadic.M23 = 10200960 := by
  rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
  exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans CFSG.M23.M23Group.card_M23

theorem card_Th :
    Nat.card NativeSporadic.Th = 90745943887872000 :=
  CFSG.Sporadic.Th.card_nativeTh_kernel

theorem sporadicPair_of_sq_dvd
    {s : SporadicName} (hs : s ∈ CFSG.RankThree.PartOne.Census3.sporadicsThm3) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ^ 2 ∣ Nat.card (NativeSporadic.Carrier s)) :
    SporadicPair s p := by
  simp only [CFSG.RankThree.PartOne.Census3.sporadicsThm3, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact sqdvd_M11 hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .M11) = _ from CFSG.Sporadic.Mathieu.card_M11] at h'
      exact h')
  · exact sqdvd_M12 hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .M12) = _ from CFSG.Sporadic.Mathieu.card_M12] at h'
      exact h')
  · exact sqdvd_M22 hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .M22) = _ from CFSG.Sporadic.Mathieu.card_M22] at h'
      exact h')
  · exact sqdvd_M23 hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .M23) = _ from card_M23] at h'
      exact h')
  · exact sqdvd_M24 hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .M24) = _ from CFSG.Sporadic.Mathieu.card_M24] at h'
      exact h')
  · exact sqdvd_J1 hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .J1) = _ from CFSG.Sporadic.J1.card_J1] at h'
      exact h')
  · exact sqdvd_J2 hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .J2) = _ from CFSG.Sporadic.J2.card_J2] at h'
      exact h')
  · exact sqdvd_J3 hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .J3) = _ from CFSG.Sporadic.J3.card_J3] at h'
      exact h')
  · exact sqdvd_J4 hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .J4) = _ from CFSG.Sporadic.J4.card_J4] at h'
      exact h')
  · exact sqdvd_McL hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .McL) = _ from CFSG.Sporadic.McL.card_McL] at h'
      exact h')
  · exact sqdvd_Ly hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .Ly) = _ from CFSG.Sporadic.Ly.card_Ly] at h'
      exact h')
  · exact sqdvd_HS hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .HS) = _ from CFSG.Sporadic.HS.card_HS] at h'
      exact h')
  · exact sqdvd_He hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .He) = _ from CFSG.Sporadic.He.card_He] at h'
      exact h')
  · exact sqdvd_Suz hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .Suz) = _ from CFSG.Sporadic.Suz.card_Suz] at h'
      exact h')
  · exact sqdvd_Ru hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .Ru) = _ from CFSG.Sporadic.Ru.card_Ru] at h'
      exact h')
  · exact sqdvd_ONan hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .ONan) = _ from CFSG.Sporadic.ON.card_ON_eq] at h'
      exact h')
  · exact sqdvd_Co3 hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .Co3) = _ from CFSG.Sporadic.Co3.card_Co3] at h'
      exact h')
  · exact sqdvd_Co2 hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .Co2) = _ from CFSG.Sporadic.Co2.card_Co2] at h'
      exact h')
  · exact sqdvd_HN hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .HN) = _ from CFSG.Sporadic.HN.card_HN] at h'
      exact h')
  · exact sqdvd_Th hp hp5 (by
      have h' := h
      rw [show Nat.card (NativeSporadic.Carrier .Th) = _ from card_Th] at h'
      exact h')

end CFSG.RankThree.PartOne.CTP
