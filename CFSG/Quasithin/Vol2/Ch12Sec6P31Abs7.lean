module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31b

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 Equiv

theorem sup_eq_top_of_pow_two {Y : Type*} [Group Y] [Finite Y] (O Ts : Subgroup Y) [O.Normal]
    (hT : IsSylowTwoOf Ts ⊤) (hY2 : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ O) : O ⊔ Ts = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (Y ⧸ O) := by
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := hY2 y
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hOi : O.index = 2 ^ n := by rw [Subgroup.index_eq_card, hn]
  have hTi : ¬ 2 ∣ Ts.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  have hd1 : (O ⊔ Ts).index ∣ 2 ^ n := by
    have h := Subgroup.index_dvd_of_le (le_sup_left : O ≤ O ⊔ Ts)
    rwa [hOi] at h
  have hd2 : (O ⊔ Ts).index ∣ Ts.index :=
    Subgroup.index_dvd_of_le (le_sup_right : Ts ≤ O ⊔ Ts)
  have hd3 : ¬ 2 ∣ (O ⊔ Ts).index := fun h => hTi (h.trans hd2)
  have h1 : (O ⊔ Ts).index = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.prime_two.coprime_pow_of_not_dvd hd3) dvd_rfl hd1
  exact Subgroup.index_eq_one.1 h1

theorem eq_sup_borel_of_normal {Y : Type*} [Group Y] [Finite Y] (X O Ts Ms : Subgroup Y)
    [X.Normal] [O.Normal] (hT : IsSylowTwoOf Ts ⊤) (hXO : X ≤ O)
    (hY2 : ∀ y : Y, ∃ k : ℕ, y ^ 2 ^ k ∈ O) (hTO : Ts ⊓ O ≤ X) (hTM : Ts ≤ Ms)
    (hKM : Ms ⊓ X = X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y))
    (hsol : ∀ Z : Subgroup Y, Ts ≤ Z → Group.IsSolvable ↥Z → Z ≤ Ms) :
    Ms = Ts ⊔ borel O Ts := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥Ts := hT.2.1
  have hS0X : IsSylowTwoOf (Ts ⊓ X) X :=
    A4.isSylowTwoOf_inf_normal hT le_top Subgroup.le_normalizer_of_normal
  have hBX : Ts ⊓ X ≤ X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) :=
    le_inf inf_le_right Subgroup.le_normalizer
  have hSB : IsSylowTwoOf (Ts ⊓ X) (X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y)) :=
    A4.isSylowTwoOf_mono hS0X hBX inf_le_left
  have hS0 : Ts ⊓ X = pCoreOf 2 (X ⊓ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y)) :=
    le_antisymm (le_pCoreOf_of_le_normalizer 2 hBX inf_le_right (hTp.to_le inf_le_left))
      (F7.isSylowTwoOf_pCoreOf_le hSB)
  have hMsN : Ms ≤ Subgroup.normalizer ((Ts ⊓ X : Subgroup Y) : Set Y) := by
    have h1 : Ms ≤ Subgroup.normalizer ((Ms ⊓ X : Subgroup Y) : Set Y) := by
      have key : ∀ m ∈ Ms, ∀ x ∈ Ms ⊓ X, m * x * m⁻¹ ∈ Ms ⊓ X := by
        intro m hm x hx
        exact ⟨Ms.mul_mem (Ms.mul_mem hm hx.1) (Ms.inv_mem hm),
          (inferInstance : X.Normal).conj_mem x hx.2 m⟩
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact key m hm x
      · intro hx
        have h := key m⁻¹ (Ms.inv_mem hm) _ hx
        have e : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
        rwa [e] at h
    have h2 := normalizer_le_normalizer_pCoreOf 2 (Ms ⊓ X)
    have h3 : pCoreOf 2 (Ms ⊓ X) = Ts ⊓ X := by
      rw [hKM]
      exact hS0.symm
    rw [h3] at h2
    exact h1.trans h2
  have hTX : Ts ≤ Subgroup.normalizer ((O : Subgroup Y) : Set Y) :=
    Subgroup.le_normalizer_of_normal
  have hTO' : IsSylowTwoOf (Ts ⊓ O) O :=
    A4.isSylowTwoOf_inf_normal hT le_top Subgroup.le_normalizer_of_normal
  have hS2 : Ts ⊔ borel O Ts ≤ Ms :=
    hsol (Ts ⊔ borel O Ts) le_sup_left (isSolvable_sup_borel hTp hTX hTO')
  have hsup : O ⊔ Ts = ⊤ := sup_eq_top_of_pow_two O Ts hT hY2
  have hTsO : Ts ⊓ O = Ts ⊓ X :=
    le_antisymm (le_inf inf_le_left hTO) (le_inf inf_le_left (inf_le_right.trans hXO))
  have hMs' : Ms ≤ Ts ⊔ borel O Ts := by
    intro m hm
    have hmO : m ∈ O ⊔ Ts := by
      rw [hsup]
      exact Subgroup.mem_top m
    obtain ⟨o, ho, t, ht, hot⟩ := Subgroup.mem_sup_of_normal_left.1 hmO
    have hoM : o ∈ Ms := by
      have e : o = m * t⁻¹ := by rw [← hot, mul_inv_cancel_right]
      rw [e]
      exact Ms.mul_mem hm (Ms.inv_mem (hTM ht))
    have hoN : o ∈ Subgroup.normalizer ((Ts ⊓ O : Subgroup Y) : Set Y) := by
      rw [hTsO]
      exact hMsN hoM
    have hob : o ∈ borel O Ts := by
      rw [S126.borel, Subgroup.mem_inf]
      exact ⟨ho, hoN⟩
    rw [← hot, sup_comm]
    exact Subgroup.mul_mem_sup hob ht
  exact le_antisymm hMs' hS2

end CFSG.Quasithin.H13.S126P31
