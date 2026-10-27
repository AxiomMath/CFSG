module

public import CFSG.Quasithin.Vol2.Ch10SecASL2OverMain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.QuasithinUnique

theorem card_eq_of_isSylowTwoOf_top {Q : Type} [Group Q] [Finite Q] {S : Subgroup Q}
    (hS : IsSylowTwoOf S ⊤) {n b : ℕ} (hb : Odd b) (hQ : Nat.card Q = 2 ^ n * b) :
    Nat.card S = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hS2, hidx⟩ := hS
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at hidx
  have h := S.card_mul_index
  rw [hk, hQ] at h
  have hodd : Odd S.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hidx)
  rw [hk, (two_pow_mul_odd_inj hodd hb h).1]

theorem le_normalizer_or_eq_top_of_mulEquiv
    {Q : Type} [Group Q] [Finite Q] {K : Type}
    [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) K) {S X : Subgroup Q} (hS : IsSylowTwoOf S ⊤)
    (hSX : S ≤ X) : X ≤ Subgroup.normalizer (S : Set Q) ∨ X = ⊤ := by
  have hQ : Nat.card Q = 2 ^ n * (4 ^ n - 1) := by
    rw [Nat.card_congr e.toEquiv, card_SL_two_pow hK]
  have hSc := card_eq_of_isSylowTwoOf_top hS (odd_four_pow_sub_one (by omega)) hQ
  have hS2 : IsPGroup 2 ↥(S.map e.toMonoidHom) := hS.2.1.map e.toMonoidHom
  have hSc' : Nat.card ↥(S.map e.toMonoidHom) = 2 ^ n := by
    rw [Subgroup.card_map_of_injective e.injective, hSc]
  rcases le_normalizer_or_eq_top_SL_two hn hK hS2 hSc'
      (Subgroup.map_mono (f := e.toMonoidHom) hSX) with h | h
  · left
    have h' : X.map e.toMonoidHom ≤ (Subgroup.normalizer (S : Set Q)).map e.toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq S e]
      exact h
    exact (Subgroup.map_le_map_iff_of_injective e.injective).mp h'
  · right
    have h' := congrArg (Subgroup.comap e.toMonoidHom) h
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at h'

variable {G : Type} [Group G]

theorem isSylowTwoOf_map_of_surjective {K : Type*} [Group K] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* K) (hρ : Function.Surjective ρ) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ⊤ := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨le_top, hS2.map ρ, ?_⟩
  rw [show (((S.subgroupOf H).map ρ).subgroupOf ⊤).index = ((S.subgroupOf H).map ρ).index from
    Subgroup.relIndex_top_right _]
  exact fun hd => hS.2.2 (hd.trans (Subgroup.index_map_dvd _ hρ))

end CFSG.Quasithin.Vol2.Ch10.SecA
