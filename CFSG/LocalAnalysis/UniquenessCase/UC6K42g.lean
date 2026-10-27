module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K42f
public import CFSG.LargeExtraspecial.AS35CS63Inn
public import CFSG.LocalAnalysis.UniquenessCase.UC6K42d
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)
open scoped commutatorElement Pointwise

theorem fermat_main_uc6 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type} [Group G] [Finite G]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) G V) (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p) {D Q : Subgroup G}
    (hD : Nat.card D = r) (hfix : fixV ρ D = ⊥) (hQ2 : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hDQ : D ≤ normalizer (Q : Set G)) (hcomm : ⁅D, Q⁆ = Q) (htop : Q ⊔ D = ⊤)
    (hmin : IsDMin_uc6 D Q) : ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k := by
  have hnab : ¬ IsMulCommutative ↥Q := fun hQab =>
    abelian_false_uc6 ρ hρ Nat.prime_two (Ne.symm hp2) hr D hD hfix Q hQ2 hQne hQab hDQ hcomm
  obtain ⟨hcomm1, hsq, hDZ⟩ := structure1_uc6 hr hr2 hD hQ2 hQne hDQ hcomm hmin hnab
  have hZcen : ∀ z ∈ (center ↥Q).map Q.subtype, z ∈ center G := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [← htop]
      refine sup_le (fun q hq => ?_) (fun d hd => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (mem_centerG_uc6.1 hz).2 q hq
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hDZ d hd z hz
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))
  haveI : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  haveI := hirr
  have hcycG : IsCyclic ↥(center G) :=
    CFSG.center_cyclic_of_representation_faithful_irreducible ρ hρ
  have hcyc : IsCyclic ↥(center ↥Q) := by
    refine isCyclic_of_injective (G := ↥(center ↥Q)) (G' := ↥(center G))
      { toFun := fun z => ⟨((z : ↥Q) : G), hZcen _ ⟨z, z.2, rfl⟩⟩
        map_one' := rfl
        map_mul' := fun a b => rfl } ?_
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨hcardZ, hcent⟩ := structure2_uc6 hr hD hDQ hcomm hnab hcomm1 hsq hDZ hcyc
  haveI hext : CFSG.IsExtraspecial 2 ↥Q := isExtraspecial_uc6 hcardZ hcomm1 hsq hnab
  obtain ⟨w, hw⟩ := CFSG.LargeExtraspecial.S63.exists_card_extraspecial
    (CFSG.IsExtraspecial.isExtraspecialPGroup (P := ↥Q))
  have hcardQ : Nat.card Q = 2 ^ (2 * w + 1) := by rw [hw, add_comm]
  have hnormalizer : normalizer (Q : Set G) = ⊤ :=
    eq_top_iff.2 (htop ▸ sup_le Subgroup.le_normalizer hDQ)
  haveI hQnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.1 hnormalizer
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card D) := by
    rw [hcardQ, hD]
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hr).2 (Ne.symm hr2))
  have hdisj : Disjoint Q D := by
    rw [Subgroup.disjoint_def]
    intro y hyQ hyD
    have h1 : orderOf y ∣ Nat.card Q := by
      have := orderOf_dvd_natCard (⟨y, hyQ⟩ : ↥Q)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf y ∣ Nat.card D := by
      have := orderOf_dvd_natCard (⟨y, hyD⟩ : ↥D)
      rwa [Subgroup.orderOf_mk] at this
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hmul : (Q : Set G) * (D : Set G) = Set.univ := by
    rw [← Subgroup.normal_mul Q D, htop]
    rfl
  have hKR : Q.IsComplement' D := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have hℓ : ¬ p ∣ Nat.card G := by
    rw [← hKR.card_mul, hcardQ, hD]
    intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h2 | h2
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1
        ((Fact.out : p.Prime).dvd_of_dvd_pow h2))
    · exact hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hr).1 h2).symm
  have hshult := shult_card_uc6 Q D hKR hcop (hD ▸ hr) hℓ ρ hρ hirr hfix hcent hDZ hcardQ
  exact fermat_pow_two_uc6 hr hr2 (hD.symm.trans hshult)

end CFSG.LocalAnalysis.UniquenessCase.UC6
