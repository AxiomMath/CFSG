module

public import CFSG.Quasithin.EmptyFaithful.S146zMStep
public import CFSG.Quasithin.EmptyFaithful.S146zQArith
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.S146zT

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.LieType.Ree
open scoped Pointwise

theorem suzukiModel_of_equiv_sz {J : Type} [Group J] {a : ℕ} (ha : 1 ≤ a) (e : J ≃* ↥(Sz a)) :
    SuzukiModel J 2 (2 * a + 1) := by
  have hcard : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  refine ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl, hcard, ⟨?_⟩⟩
  exact (e.trans (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard).symm).trans
    (MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a (GaloisField 2 (2 * a + 1))).symm)

theorem exists_prime_dvd_two_pow_odd_sub_one_ge_seven (a : ℕ) (ha : 1 ≤ a) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ 2 ^ (2 * a + 1) - 1 ∧ 7 ≤ ℓ := by
  have hpos : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : 2 ^ (2 * a + 1) - 1 ≠ 1 := by omega
  obtain ⟨ℓ, hℓ, hd⟩ := Nat.exists_prime_and_dvd hne
  exact ⟨ℓ, hℓ, hd, CFSG.Quasithin.prime_dvd_two_pow_sub_one_ge_seven ⟨a, rfl⟩ (by omega) hℓ hd⟩

section Solv

variable {J : Type} [Group J] [Finite J]

theorem suzuki_normalizer_sylow_seven {f : ℕ}
    (hf : SuzukiModel J 2 f) (S : Sylow 2 J) :
    Group.IsSolvable ↥(Subgroup.normalizer ((S : Subgroup J) : Set J)) ∧
      ∃ ℓ : ℕ, ℓ.Prime ∧ 7 ≤ ℓ ∧
        ℓ ∣ Nat.card ↥(Subgroup.normalizer ((S : Subgroup J) : Set J)) := by
  refine ⟨CFSG.Quasithin.suzuki_normalizer_solvable hf S, ?_⟩
  obtain ⟨-, a, ha, K, hKf, hKfin, hfa, hKcard, ⟨e⟩⟩ := hf
  subst hfa
  let S' : Sylow 2 (suzukiGroup a K) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : (S' : Subgroup (suzukiGroup a K)) = (S : Subgroup J).map e.toMonoidHom := rfl
  have hN : Subgroup.normalizer ((S' : Subgroup (suzukiGroup a K)) : Set (suzukiGroup a K)) =
      (Subgroup.normalizer ((S : Subgroup J) : Set J)).map e.toMonoidHom := by
    rw [hmap]
    exact (Subgroup.map_equiv_normalizer_eq (S : Subgroup J) e).symm
  have hdvd := CFSG.Quasithin.suzukiGroup_normalizer_dvd (a := a) (K := K) hKcard S'
  rw [hN, Subgroup.card_map_of_injective e.injective] at hdvd
  obtain ⟨ℓ, hℓ, hℓd, h7⟩ := exists_prime_dvd_two_pow_odd_sub_one_ge_seven a ha
  exact ⟨ℓ, hℓ, h7, hℓd.trans hdvd⟩

end Solv

section Bor

variable {Q : Type} [Group Q] [Finite Q]

theorem borOf_suzuki_seven {T L : Subgroup Q}
    (hT : IsSylowTwoOf T ⊤) (hsub : IsSubnormal L ⊤) {f : ℕ}
    (hf : CFSG.Blueprint.SuzukiModel ↥L 2 f) :
    Group.IsSolvable ↥(CFSG.Quasithin.borOf T L) ∧
      ∃ ℓ : ℕ, ℓ.Prime ∧ 7 ≤ ℓ ∧ ℓ ∣ Nat.card ↥(CFSG.Quasithin.borOf T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl := CFSG.Quasithin.zm_isSylowTwoOf_inf_of_isSubnormal hsub hT
  have hpg : IsPGroup 2 ↥((T ⊓ L).subgroupOf L) :=
    hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.1).symm
  let S₁ : Sylow 2 ↥L := hpg.toSylow hSyl.2.2
  obtain ⟨hs, ℓ, hℓ, h7, hdvd⟩ := suzuki_normalizer_sylow_seven hf S₁
  set N := Subgroup.normalizer ((S₁ : Subgroup ↥L) : Set ↥L) with hN
  have hS₁ : (S₁ : Subgroup ↥L) = (T ⊓ L).subgroupOf L := rfl
  have hNeq : N = (Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q)).comap L.subtype := by
    rw [hN, hS₁]
    exact (Subgroup.comap_normalizer_eq_of_le_range (f := L.subtype)
      (by rw [Subgroup.range_subtype]; exact inf_le_right)).symm
  have hbor : CFSG.Quasithin.borOf T L = N.map L.subtype := by
    rw [hNeq, Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_comm _ _
  rw [hbor]
  refine ⟨Group.isSolvable_of_surjective (f := L.subtype.subgroupMap N)
    (L.subtype.subgroupMap_surjective N), ℓ, hℓ, h7, ?_⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective]
  exact hdvd

end Bor

end CFSG.Quasithin.S146zT
