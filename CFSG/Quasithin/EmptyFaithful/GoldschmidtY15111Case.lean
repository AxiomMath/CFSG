module

public import CFSG.Quasithin.Background.F6Solvable
public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Free

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {I : Type} [Group I] [Finite I] {P H : Subgroup I}

theorem two_pow_eq_four {k i m : ℕ} (hi : Odd i) (hm : Odd m) (h : 2 ^ k * i = 4 * m) :
    2 ^ k = 4 := by
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k
    · exfalso
      obtain ⟨a, rfl⟩ := hi
      obtain ⟨b, rfl⟩ := hm
      omega
    · exfalso
      obtain ⟨a, rfl⟩ := hi
      obtain ⟨b, rfl⟩ := hm
      omega
    · rfl
  · exfalso
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    obtain ⟨a, rfl⟩ := hi
    obtain ⟨b, rfl⟩ := hm
    have h8 : 2 ^ (3 + j) = 8 * 2 ^ j := by rw [pow_add]; norm_num
    rw [h8] at h
    have : 8 ∣ 4 * (2 * b + 1) := by
      rw [← h]
      exact ⟨2 ^ j * (2 * a + 1), by ring⟩
    omega

theorem card_eq_four_of_isSylow {D : Type} [Group D] [Finite D] {S : Subgroup D}
    (hS : IsSylowTwoOf S ⊤) {m : ℕ} (hm : Odd m) (hD : Nat.card D = 4 * m) :
    Nat.card S = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (hS.2.1).exists_card_eq
  have h1 := Subgroup.card_mul_index S
  have hidx : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right _
  have hodd : Odd S.index := by
    have := hS.2.2
    rw [hidx] at this
    exact Nat.not_even_iff_odd.mp fun he => this (even_iff_two_dvd.mp he)
  rw [hD, hk] at h1
  rw [hk]
  exact two_pow_eq_four hodd hm h1


theorem pCore_le_pCoreOf_left (h : IsGoldschmidtTriple P H) : Open.pCore 2 I ≤ pCoreOf 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (Open.pCore 2 I).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  exact le_pCoreOf 2 (h.pCore_le_inf.trans inf_le_left) inferInstance
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := I) 2)

theorem pCore_le_pCoreOf_right (h : IsGoldschmidtTriple P H) : Open.pCore 2 I ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (Open.pCore 2 I).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  exact le_pCoreOf 2 (h.pCore_le_inf.trans inf_le_right) inferInstance
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := I) 2)

theorem pCoreOf_le_pCore_of_map_eq_bot (h : IsGoldschmidtTriple P H)
    (hq : pCoreOf 2 (P.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 I))) = ⊥) :
    pCoreOf 2 P ≤ Open.pCore 2 I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := CFSG.LieType.BorelTits.map_pCoreOf_le (r := 2)
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 I)) P
  rw [hq] at h1
  have h2 : pCoreOf 2 P ≤ CFSG.pPrimeCore 3 I := by
    intro x hx
    have := Subgroup.mem_bot.mp (h1 ⟨x, hx, rfl⟩)
    exact (QuotientGroup.eq_one_iff x).mp this
  rw [← F6.inf_pPrimeCore_eq_pCore_left h]
  exact le_inf (pCoreOf_le 2 P) h2





theorem false_of_index_four (h : IsGoldschmidtTriple P H) {V : Subgroup I} {c : I}
    (hV16 : Nat.card V = 16) (hVQ : V ≤ pCoreOf 2 P) (hVH : ¬ V ≤ pCoreOf 2 H)
    (hcV : c ∈ Subgroup.normalizer (V : Set I)) (hc3 : c ^ 3 = 1)
    (hfree : ∀ v ∈ V, c * v * c⁻¹ = v → v = 1)
    (hidx : (Open.pCore 2 I).relIndex (P ⊓ H) = 4) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := P ⊓ H with hT
  set Q1 := pCoreOf 2 P with hQ1
  set Q2 := pCoreOf 2 H with hQ2
  set B := Open.pCore 2 I with hB
  have hQ1T : Q1 ≤ T := F6.pCoreOf_le_inf_left h
  have hQ2T : Q2 ≤ T := F6.pCoreOf_le_inf_right h
  have hBQ1 : B ≤ Q1 := pCore_le_pCoreOf_left h
  have hBQ2 : B ≤ Q2 := pCore_le_pCoreOf_right h
  have hBT : B ≤ T := hBQ1.trans hQ1T
  have e1 := Subgroup.relIndex_mul_card Q1 T
  rw [inf_eq_left.mpr hQ1T, F6.relIndex_pCoreOf_left h] at e1
  have e2 := Subgroup.relIndex_mul_card B T
  rw [inf_eq_left.mpr hBT, hidx] at e2
  have hnQ : ¬ Q1 ≤ Q2 := fun hle => hVH (hVQ.trans hle)
  have e3 := Subgroup.relIndex_mul_card Q2 Q1
  have h1 : Q2.relIndex Q1 ≠ 1 := fun h1 => hnQ (Subgroup.relIndex_eq_one.mp h1)
  have h0 : Q2.relIndex Q1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e3
    have := Nat.card_pos (α := Q1)
    omega
  have hle : Nat.card (Q2 ⊓ Q1 : Subgroup I) * 2 ≤ Nat.card Q1 := by
    have : 2 ≤ Q2.relIndex Q1 := by omega
    rw [← e3]
    nlinarith
  have hBle : B ≤ Q2 ⊓ Q1 := le_inf hBQ2 hBQ1
  have hBcard : Nat.card (Q2 ⊓ Q1 : Subgroup I) ≤ Nat.card B := by omega
  have hBeq : B = Q2 ⊓ Q1 := Subgroup.eq_of_le_of_card_ge hBle hBcard
  have hVB : V ⊓ B = V ⊓ Q2 := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxV, hxB⟩
      exact ⟨hxV, hBQ2 hxB⟩
    · rintro ⟨hxV, hx2⟩
      refine ⟨hxV, ?_⟩
      rw [hBeq]
      exact ⟨hx2, hVQ hxV⟩
  have hVT : V ≤ T := hVQ.trans hQ1T
  have hr : Q2.relIndex V ≤ Q2.relIndex T :=
    Subgroup.relIndex_le_of_le_right hVT (by rw [F6.relIndex_pCoreOf_right h]; norm_num)
  rw [F6.relIndex_pCoreOf_right h] at hr
  have hr1 : Q2.relIndex V ≠ 1 := fun h1 => hVH (Subgroup.relIndex_eq_one.mp h1)
  have e4 := Subgroup.relIndex_mul_card Q2 V
  have hr0 : Q2.relIndex V ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e4
    have := Nat.card_pos (α := V)
    omega
  have hr2 : Q2.relIndex V = 2 := by omega
  rw [hr2, hV16] at e4
  have hc8 : Nat.card (V ⊓ B : Subgroup I) = 8 := by
    rw [hVB, inf_comm]
    omega
  have hcB : c ∈ Subgroup.normalizer (B : Set I) := by
    have : (Open.pCore 2 I).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    rw [Subgroup.normalizer_eq_top_iff.mpr this]
    exact Subgroup.mem_top c
  have hcW : c ∈ Subgroup.normalizer ((V ⊓ B : Subgroup I) : Set I) := by
    rw [Subgroup.mem_normalizer_iff] at hcV hcB ⊢
    intro y
    simp only [Subgroup.mem_inf]
    rw [hcV y, hcB y]
  have hmod := card_mod_three_of_free hcW hc3 (fun w hw hcw => hfree w hw.1 hcw)
  omega


end Y15111

end CFSG.Quasithin
