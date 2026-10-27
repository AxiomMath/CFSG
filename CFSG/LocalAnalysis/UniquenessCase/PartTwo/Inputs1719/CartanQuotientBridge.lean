module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
public import TauCeti.Algebra.Group.NormalizerQuotient.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient normalizerQuotientMk normalizerQuotientMk_eq_one_iff)

theorem le_pRank_normalizerQuotient_of_le_normalizer {K : Type} [Group K] [Finite K] {ℓ k : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {S F : Subgroup K} (hS : IsPGroup 2 S)
    (hFN : F ≤ Subgroup.normalizer (S : Set K)) (hFE : IsElemAbelian ℓ F)
    (hFc : Nat.card F = ℓ ^ k) :
    k ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup (normalizerQuotient S)) ∧
      ℓ ^ k ∣ Nat.card (normalizerQuotient S) := by
  classical
  let ψ : F →* normalizerQuotient S := (normalizerQuotientMk S).comp (Subgroup.inclusion hFN)
  have hpow : ∀ a : F, a ^ ℓ = 1 := fun a => Subtype.ext (by simpa using hFE.2 a.1 a.2)
  have hFp : IsPGroup ℓ F := fun a => ⟨1, by simpa using hpow a⟩
  have hdisj : Disjoint F S :=
    IsPGroup.disjoint_of_coprime hFp hS ((Nat.coprime_primes hℓ Nat.prime_two).2 hℓ2)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxS : (x : K) ∈ S := (normalizerQuotientMk_eq_one_iff S _).1 hx
    exact Subtype.ext (Subgroup.disjoint_def.1 hdisj x.2 hxS)
  have hE : IsElemAbelian ℓ ψ.range := by
    refine ⟨IsMulCommutative.of_setLike_mul_comm fun x hx y hy => ?_, ?_⟩
    · obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      rw [← map_mul, ← map_mul, hFE.1.is_comm.comm a b]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow, hpow a, map_one]
  have hc : Nat.card ψ.range = ℓ ^ k := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hFc]
  refine ⟨CFSG.SectionRank.le_pRank hℓ.one_lt le_top hE hc, ?_⟩
  rw [← hc]
  exact Subgroup.card_subgroup_dvd_card _

theorem le_pRank_normalizerQuotient_of_borelWit {K : Type} [Group K] [Finite K] {ℓ k : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20oBorelWit K ℓ k)
    (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    k ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup (normalizerQuotient S)) ∧
      ℓ ^ k ∣ Nat.card (normalizerQuotient S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hS2, hSi⟩ := hS
  have hidx : ¬ 2 ∣ S.index := by
    rw [← Subgroup.relIndex_top_right (H := S)]
    exact hSi
  obtain ⟨F, hFN, hFE, hFc⟩ := h (hS2.toSylow hidx)
  have hPS : ((hS2.toSylow hidx : Sylow 2 K) : Set K) = (S : Set K) := by
    ext x
    exact IsPGroup.mem_toSylow hS2 hidx
  rw [hPS] at hFN
  exact le_pRank_normalizerQuotient_of_le_normalizer hℓ hℓ2 hS2 hFN hFE hFc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
