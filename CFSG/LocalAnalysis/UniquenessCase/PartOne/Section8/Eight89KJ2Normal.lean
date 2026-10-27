module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KJ2Basic
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup

private theorem k91j2n_normalizer {J : Type} [Group J] (K : Subgroup J)
    (S : Subgroup (MulAut J))
    (hN : ∀ k ∈ K, MulAut.conj k ∈ normalizer (S : Set (MulAut J))) :
    K ≤ normalizer ((S.comap (MulAut.conj : J →* MulAut J) : Subgroup J) : Set J) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro x
  have := (mem_normalizer_iff.mp (hN k hk)) (MulAut.conj x)
  simp only [mem_comap, map_mul, map_inv]
  exact this

private theorem k91j2n_normal_two_group_trivial {K : Type} [Group K] [Finite K]
    (hK : Nat.card K = 1080)
    (hnorm : ∀ N : Subgroup K, N.Normal → N = ⊤ ∨ N ≤ center K) (hZ : Nat.card (center K) = 3)
    (N : Subgroup K) (hNn : N.Normal) (hNp : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hNp.exists_card_eq
  rw [← Subgroup.card_eq_one]
  rcases hnorm N hNn with h | h
  · rw [h, card_top, hK] at hn
    exfalso
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 1080)
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h3))
    omega
  · have hd := Subgroup.card_dvd_of_le h
    rw [hZ, hn] at hd
    rw [hn]
    rcases n with _ | n
    · rfl
    · exfalso
      have : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hd
      omega

private theorem k91j2n_inf_eq_bot {J : Type} [Group J] [Finite J] (K T : Subgroup J)
    (hKN : K ≤ normalizer (T : Set J)) (hT : IsPGroup 2 T) (hK : Nat.card K = 1080)
    (hnorm : ∀ N : Subgroup K, N.Normal → N = ⊤ ∨ N ≤ center K) (hZ : Nat.card (center K) = 3) :
    K ⊓ T = ⊥ := by
  let N : Subgroup K := T.comap K.subtype
  have hNn : N.Normal := by
    constructor
    intro n hn g
    simp only [N, mem_comap, coe_subtype, coe_mul, coe_inv] at hn ⊢
    exact (mem_normalizer_iff.mp (hKN g.2) n).mp hn
  have hNp : IsPGroup 2 N := hT.comap_of_injective K.subtype K.subtype_injective
  have hN1 := k91j2n_normal_two_group_trivial hK hnorm hZ N hNn hNp
  rw [eq_bot_iff]
  rintro x ⟨hxK, hxT⟩
  have hmem : (⟨x, hxK⟩ : K) ∈ N := hxT
  rw [hN1, mem_bot] at hmem
  exact (mem_bot).mpr (congrArg Subtype.val hmem)

private theorem k91j2n_card_dvd_sixteen {J : Type} [Group J] [Finite J]
    (hcard : Nat.card J = 604800) (K T : Subgroup J) (hKN : K ≤ normalizer (T : Set J))
    (hT : IsPGroup 2 T) (hK : Nat.card K = 1080) (hinf : K ⊓ T = ⊥) : Nat.card T ∣ 16 := by
  have hsup :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hKN
  rw [hinf, card_bot, mul_one, hK] at hsup
  have hd : 1080 * Nat.card T ∣ 604800 := hsup ▸ hcard ▸ Subgroup.card_subgroup_dvd_card _
  have hd' : Nat.card T ∣ 16 * 35 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 1080) (by simpa using hd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  rw [hn] at hd' ⊢
  exact (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 35)).dvd_of_dvd_mul_right hd'

theorem j2AutCore_comap_conj_dvd {J : Type} [Group J] [Finite J] (hcard : Nat.card J = 604800)
    (hcenter : center J = ⊥) (K : Subgroup J) (hK : Nat.card K = 1080)
    (hnorm : ∀ N : Subgroup K, N.Normal → N = ⊤ ∨ N ≤ center K) (hZ : Nat.card (center K) = 3)
    (S : Subgroup (MulAut J)) (hS : IsPGroup 2 S)
    (hN : ∀ k ∈ K, MulAut.conj k ∈ normalizer (S : Set (MulAut J))) :
    K ≤ normalizer ((S.comap (MulAut.conj : J →* MulAut J) : Subgroup J) : Set J) ∧
      Nat.card (S.comap (MulAut.conj : J →* MulAut J)) ∣ 16 := by
  have hconj := mulAut_conj_injective_of_center_eq_bot hcenter
  have hT₀p : IsPGroup 2 (S.comap (MulAut.conj : J →* MulAut J)) :=
    hS.comap_of_injective _ hconj
  have hKN := k91j2n_normalizer K S hN
  exact ⟨hKN, k91j2n_card_dvd_sixteen hcard K _ hKN hT₀p hK
    (k91j2n_inf_eq_bot K _ hKN hT₀p hK hnorm hZ)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
