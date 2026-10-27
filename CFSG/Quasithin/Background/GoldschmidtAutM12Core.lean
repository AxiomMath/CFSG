module

public import CFSG.Quasithin.Background.F6CatRecogOut

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank

namespace AutM12Recog

structure TProps (T : Type) [Group T] : Prop where
  card : Nat.card T = 2 ^ 7
  exp : ∀ x : T, x ^ 8 = 1
  rank : ∀ B : Subgroup T, IsElemAbelian 2 B → Nat.card B ≤ 16
  uniq : ∀ B B' : Subgroup T, IsElemAbelian 2 B → IsElemAbelian 2 B' → Nat.card B = 16 →
    Nat.card B' = 16 → B = B'
  hasE16 : ∃ B : Subgroup T, IsElemAbelian 2 B ∧ Nat.card B = 16

namespace TProps

variable {T : Type} [Group T] (hT : TProps T)
include hT

theorem pow_eight_eq_one {Q : Type} [Group Q] (f : Q →* T) (hf : Function.Injective f) (g : Q) :
    g ^ 8 = 1 :=
  hf (by rw [map_pow, map_one]; exact hT.exp (f g))

theorem card_le_sixteen {Q : Type} [Group Q] (f : Q →* T) (hf : Function.Injective f)
    (B : Subgroup Q) (hB : IsElemAbelian 2 B) : Nat.card B ≤ 16 := by
  have hB' : IsElemAbelian 2 (B.map f) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
      apply Subtype.ext
      show f a * f b = f b * f a
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hB.2 a ha, map_one]
  have := hT.rank _ hB'
  rwa [← Nat.card_congr (B.equivMapOfInjective f hf).toEquiv] at this

theorem false_of_two_E16 {Q : Type} [Group Q] (f : Q →* T) (hf : Function.Injective f)
    (B B' : Subgroup Q) (hB : IsElemAbelian 2 B) (hB' : IsElemAbelian 2 B')
    (hc : Nat.card B = 16) (hc' : Nat.card B' = 16) (hne : B ≠ B') : False := by
  have key : ∀ C : Subgroup Q, IsElemAbelian 2 C → IsElemAbelian 2 (C.map f) := by
    intro C hC
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
      apply Subtype.ext
      show f a * f b = f b * f a
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hC.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hC.2 a ha, map_one]
  have h := hT.uniq (B.map f) (B'.map f) (key B hB) (key B' hB')
    (by rw [← Nat.card_congr (B.equivMapOfInjective f hf).toEquiv, hc])
    (by rw [← Nat.card_congr (B'.equivMapOfInjective f hf).toEquiv, hc'])
  exact hne (Subgroup.map_injective hf h)

end TProps

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem dvd_card_outer_of_dvd_card_mulAut {K : Type} [Group K] [Finite K] {m : ℕ}
    (h : Nat.card K * m ∣ Nat.card (MulAut K)) : m ∣ Nat.card (Outer K) := by
  have h1 : Nat.card (MulAut K) = Nat.card (Outer K) * Nat.card (inner K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (inner K)
  obtain ⟨d, hd⟩ : Nat.card (inner K) ∣ Nat.card K :=
    Subgroup.card_range_dvd (MulAut.conj : K →* MulAut K)
  have hpos : 0 < Nat.card (inner K) := Nat.card_pos
  rw [h1] at h
  have e1 : Nat.card K * m = Nat.card (inner K) * (d * m) := by rw [hd]; ring
  have h' : Nat.card (inner K) * (d * m) ∣ Nat.card (inner K) * Nat.card (Outer K) := by
    rw [← e1, mul_comm (Nat.card (inner K))]
    exact h
  exact (dvd_mul_left m d).trans ((Nat.mul_dvd_mul_iff_left hpos).mp h')

theorem exists_sylow_mulEquiv {A B : Type*} [Group A] [Finite A] [Group B] (ψ : A ≃* B)
    (Q : Sylow 2 A) :
    ∃ Q' : Sylow 2 B, Nonempty (↥(Q : Subgroup A) ≃* ↥(Q' : Subgroup B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Q.mapSurjective (f := ψ.toMonoidHom) ψ.surjective, ⟨?_⟩⟩
  exact ((Q : Subgroup A).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
    (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm)

@[expose] def Excl (K : Type) [Group K] [Finite K] : Prop :=
  ∀ (T : Type) [Group T] [Finite T], TProps T → ∀ (Q : Sylow 2 K) (n : ℕ) (N : Subgroup T),
    Nonempty (↥(Q : Subgroup K) ≃* ↥N) → Nat.card T = Nat.card N * 2 ^ n →
    Nat.card K * 2 ^ n ∣ Nat.card (MulAut K) → False

theorem Excl.of_mulEquiv {K K' : Type} [Group K] [Finite K] [Group K'] [Finite K'] (e : K ≃* K')
    (h : Excl K') : Excl K := by
  intro T _ _ hT Q n N hQN hc hA
  obtain ⟨Q', ⟨ι⟩⟩ := exists_sylow_mulEquiv e Q
  refine h T hT Q' n N ⟨ι.symm.trans hQN.some⟩ hc ?_
  rwa [← Nat.card_congr e.toEquiv, ← Nat.card_congr (MulAut.congr e).toEquiv]

theorem setting_excl_data {D : Type} [Group D] [Finite D] (hS : F618RecogSetting D) (S : Sylow 2 D)
    {T : Type} [Group T] (e : ↥(S : Subgroup D) ≃* T) :
    ∃ (n : ℕ) (Q : Sylow 2 (TwoResidualQuot D)) (N : Subgroup T),
      (twoResidual (⊤ : Subgroup D)).index = 2 ^ n ∧
      Nonempty (↥(Q : Subgroup (TwoResidualQuot D)) ≃* ↥N) ∧
      Nat.card T = Nat.card N * 2 ^ n ∧
      Nat.card (TwoResidualQuot D) * 2 ^ n ∣ Nat.card (MulAut (TwoResidualQuot D)) := by
  have := twoResidual_top_normal (D := D)
  obtain ⟨n, hn⟩ := exists_index_twoResidual_eq (D := D)
  obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_quotient_of_setting hS S
  let M : Subgroup ↥(S : Subgroup D) := ((S : Subgroup D) ⊓ twoResidual ⊤).subgroupOf S
  have eM : ↥M ≃* ↥Q := (Subgroup.subgroupOfEquivOfLe inf_le_left).trans eQ
  refine ⟨n, Q, M.map e.toMonoidHom, hn, ⟨(eM.symm.trans (M.equivMapOfInjective e.toMonoidHom
    e.injective))⟩, ?_, ?_⟩
  · have h := card_sylow_eq_mul_index (twoResidual ⊤) hn S
    have h1 : Nat.card ↥(S : Subgroup D) = Nat.card T := Nat.card_congr e.toEquiv
    have h2 : Nat.card ↥(M.map e.toMonoidHom) = Nat.card ↥M :=
      (Nat.card_congr (M.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
    have h3 : Nat.card ↥M = Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [← h1, h, h2, h3]
  · have := card_mul_index_dvd_card_mulAut hS
    rwa [hn] at this

end AutM12Recog

end CFSG.Quasithin.F6
