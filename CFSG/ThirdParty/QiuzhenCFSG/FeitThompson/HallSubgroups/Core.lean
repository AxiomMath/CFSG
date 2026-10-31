module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index

import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Finite

namespace CFSG
end CFSG
open CFSG


/-- A Hall `π`-subgroup: a subgroup whose order involves only primes in `π` and whose index involves only primes not in `π`. -/
public class CFSG.IsHallSubgroup {G : Type*} [Group G] (π : Set Nat.Primes) (H : Subgroup G) : Prop where
  p_in_pi_of_p_dvd_card (p : Nat.Primes) : p.val ∣ Nat.card H → p ∈ π
  p_in_pi_of_p_dvd_index (p : Nat.Primes) : p.val ∣ H.index → p ∉ π

/-- A `π`-subgroup (all prime divisors of its order lie in `π`). -/
@[expose]
public def CFSG.IsPiSubgroup {G : Type*} [Group G] (π : Set Nat.Primes) (H : Subgroup G) : Prop :=
  ∀ p : Nat.Primes, p.val ∣ Nat.card H → p ∈ π

-- TODO(tianjiao): The Agemo subgroup.

section HallInfrastructure

variable {G : Type*} [Group G]

/-- A convenient constructor for `IsHallSubgroup`: it suffices to control prime divisors of
`Nat.card H` and to exclude primes in `π` from dividing the index `H.index`. -/
public lemma CFSG.isHallSubgroup_of
    (π : Set Nat.Primes) (H : Subgroup G)
    (hcard : ∀ p : Nat.Primes, p.val ∣ Nat.card H → p ∈ π)
    (hindex : ∀ p : Nat.Primes, p ∈ π → ¬ p.val ∣ H.index) :
    IsHallSubgroup π H := by
  refine ⟨hcard, ?_⟩
  intro p hp_dvd_index
  by_contra hp_in
  exact hindex p hp_in hp_dvd_index

public lemma CFSG.isHallSubgroup_top_of_card_eq_one
    (π : Set Nat.Primes) (hG : Nat.card G = 1) :
    IsHallSubgroup π (⊤ : Subgroup G) := by
  classical
  refine isHallSubgroup_of (G := G) (π := π) (H := (⊤ : Subgroup G))
    (hcard := ?_) (hindex := ?_)
  · intro p hp_dvd
    exfalso
    have : p.val ∣ 1 := by simpa [hG] using hp_dvd
    exact p.property.not_dvd_one this
  · intro p _hp_mem hp_dvd
    exfalso
    have : p.val ∣ 1 := by simpa using hp_dvd
    exact p.property.not_dvd_one this

end HallInfrastructure

section PiInfrastructure

variable {G : Type*} [Group G]

section HallCardinality

variable {π : Set Nat.Primes} {H H₁ H₂ K : Subgroup G}

public lemma CFSG.IsHallSubgroup.card_coprime_index (hH : IsHallSubgroup π H) :
    Nat.Coprime (Nat.card H) H.index := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hq_dvd_card hq_dvd_index
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hq_mem : q' ∈ π := hH.p_in_pi_of_p_dvd_card q' hq_dvd_card
  have hq_not_mem : q' ∉ π := hH.p_in_pi_of_p_dvd_index q' hq_dvd_index
  exact hq_not_mem hq_mem

public lemma CFSG.IsHallSubgroup.card_coprime_index_other
    (hH₁ : IsHallSubgroup π H₁) (hH₂ : IsHallSubgroup π H₂) :
    Nat.Coprime (Nat.card H₁) H₂.index := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hq_dvd_card hq_dvd_index
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hq_mem : q' ∈ π := hH₁.p_in_pi_of_p_dvd_card q' hq_dvd_card
  have hq_not_mem : q' ∉ π := hH₂.p_in_pi_of_p_dvd_index q' hq_dvd_index
  exact hq_not_mem hq_mem

public lemma CFSG.IsHallSubgroup.card_dvd_card
    (hH₁ : IsHallSubgroup π H₁) (hH₂ : IsHallSubgroup π H₂) :
    Nat.card H₁ ∣ Nat.card H₂ := by
  have hdiv_mul : Nat.card H₁ ∣ Nat.card H₂ * H₂.index := by
    simpa [Subgroup.index_mul_card] using (Subgroup.card_subgroup_dvd_card (H₁ : Subgroup G))
  have hcop : Nat.Coprime (Nat.card H₁) H₂.index :=
    hH₁.card_coprime_index_other hH₂
  exact hcop.dvd_of_dvd_mul_right hdiv_mul

public lemma CFSG.IsHallSubgroup.card_eq
    (hH₁ : IsHallSubgroup π H₁) (hH₂ : IsHallSubgroup π H₂) :
    Nat.card H₁ = Nat.card H₂ :=
  Nat.dvd_antisymm (hH₁.card_dvd_card hH₂) (hH₂.card_dvd_card hH₁)


public lemma CFSG.IsHallSubgroup.eq_of_le
    [Finite G] (hH₁ : IsHallSubgroup π H₁) (hH₂ : IsHallSubgroup π H₂) (hH₁H₂ : H₁ ≤ H₂) :
    H₁ = H₂ := by
  apply le_antisymm hH₁H₂
  have hcard_eq : Nat.card H₁ = Nat.card H₂ := hH₁.card_eq hH₂
  have hEq : H₁ = H₂ := Subgroup.eq_of_le_of_card_ge hH₁H₂ (by simp [hcard_eq])
  exact hEq.ge

public lemma CFSG.IsHallSubgroup.le_of_le_normalizer
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup π K) (hK_norm : K ≤ Subgroup.normalizer H.carrier) :
    K ≤ H := by
  let HK : Subgroup G := K ⊔ H
  have hHsub_norm : (H.subgroupOf HK).Normal := by
    simpa [HK] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := K) (N := H) hK_norm)
  have hrel_dvd_cardK : H.relIndex HK ∣ Nat.card K := by
    change (H.subgroupOf HK).index ∣ Nat.card K
    have htop : H.subgroupOf HK ⊔ K.subgroupOf HK = ⊤ := by
      calc
        H.subgroupOf HK ⊔ K.subgroupOf HK = (H ⊔ K).subgroupOf HK := by
          symm
          simpa [HK] using
            (Subgroup.subgroupOf_sup (A := H) (A' := K) (B := HK) (by exact le_sup_right)
              (by exact le_sup_left))
        _ = ⊤ := by
          apply (Subgroup.subgroupOf_eq_top).2
          simp [HK, sup_comm]
    have hrel_eq :
        (H.subgroupOf HK).index =
          (H.subgroupOf HK).relIndex (K.subgroupOf HK) := by
      calc
        (H.subgroupOf HK).index = (H.subgroupOf HK).relIndex ⊤ := by
          exact (Subgroup.relIndex_top_right (H := H.subgroupOf HK)).symm
        _ = (H.subgroupOf HK).relIndex (H.subgroupOf HK ⊔ K.subgroupOf HK) := by
          rw [← htop]
        _ = (H.subgroupOf HK).relIndex (K.subgroupOf HK) := by
          rw [sup_comm]
          exact Subgroup.relIndex_sup_right (H := K.subgroupOf HK) (K := H.subgroupOf HK)
    have hdiv :
        (H.subgroupOf HK).relIndex (K.subgroupOf HK) ∣ Nat.card (K.subgroupOf HK) :=
      Subgroup.relIndex_dvd_card (H := H.subgroupOf HK) (K := K.subgroupOf HK)
    have hcard_Ksub : Nat.card (K.subgroupOf HK) = Nat.card K := by
      simpa using
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := K) (K := HK) (by exact le_sup_left)).toEquiv
    exact hrel_eq ▸ (hcard_Ksub ▸ hdiv)
  have hrel_dvd_index : H.relIndex HK ∣ H.index :=
    Subgroup.relIndex_dvd_index_of_le (H := H) (K := HK) le_sup_right
  have hcop : Nat.Coprime (Nat.card K) H.index := hK.card_coprime_index_other hH
  have hrel_eq_one : H.relIndex HK = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hrel_dvd_cardK hrel_dvd_index
  have hHK_le_H : HK ≤ H := (Subgroup.relIndex_eq_one).1 hrel_eq_one
  exact le_trans le_sup_left hHK_le_H


public lemma CFSG.IsHallSubgroup.le_of_normal
    (hH : IsHallSubgroup π H) (hK : IsHallSubgroup π K) [H.Normal] :
    K ≤ H := by
  have hK_norm : K ≤ Subgroup.normalizer (H : Set G) := by
    simp [Subgroup.normalizer_eq_top]
  exact IsHallSubgroup.le_of_le_normalizer (hH := hH) (hK := hK) hK_norm

public lemma CFSG.IsHallSubgroup.eq_of_normal
    [Finite G] (hH : IsHallSubgroup π H) (hK : IsHallSubgroup π K) [H.Normal] :
    K = H :=
  hK.eq_of_le hH (hH.le_of_normal hK)

public lemma CFSG.IsHallSubgroup.subgroupOf
    (hH : IsHallSubgroup π H) {K : Subgroup G} (hHK : H ≤ K) :
    IsHallSubgroup π (H.subgroupOf K) := by
  refine isHallSubgroup_of (G := K) (π := π) (H := H.subgroupOf K) (hcard := ?_) (hindex := ?_)
  · intro q hq_dvd
    have hcard_eq : Nat.card (H.subgroupOf K) = Nat.card H := by
      simpa using Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := H) (K := K) hHK).toEquiv
    exact hH.p_in_pi_of_p_dvd_card q (hcard_eq ▸ hq_dvd)
  · intro q hq_mem hq_dvd_idx
    have hidx_dvd : (H.subgroupOf K).index ∣ H.index := by
      have hmap : (H.subgroupOf K).map K.subtype = H := by
        ext x
        simp [hHK]
      have hidx_map : ((H.subgroupOf K).map K.subtype).index =
          (H.subgroupOf K).index * K.index :=
        Subgroup.index_map_subtype (K := H.subgroupOf K)
      exact ⟨K.index, by simpa [hmap] using hidx_map⟩
    have hq_dvd_Hidx : q.val ∣ H.index := hq_dvd_idx.trans hidx_dvd
    exact (hH.p_in_pi_of_p_dvd_index q hq_dvd_Hidx) hq_mem

public lemma CFSG.IsHallSubgroup.map_mulAut
    (hH : IsHallSubgroup π H) (e : MulAut G) :
    IsHallSubgroup π (H.map e.toMonoidHom) := by
  refine isHallSubgroup_of (G := G) (π := π) (H := H.map e.toMonoidHom) (hcard := ?_) (hindex := ?_)
  · intro q hq_dvd
    have hcard_map : Nat.card { x // ∃ x' ∈ H, e x' = x } = Nat.card H := by
      simpa using
        (Subgroup.card_map_of_injective (K := H) (f := e.toMonoidHom) e.injective)
    exact hH.p_in_pi_of_p_dvd_card q (by simpa [Subgroup.map, hcard_map] using hq_dvd)
  · intro q hq_mem hq_dvd_idx
    have hidx_map : (H.map e.toMonoidHom).index = H.index := by
      exact Subgroup.index_map_equiv (H := H) e
    exact (hH.p_in_pi_of_p_dvd_index q (by simpa [hidx_map] using hq_dvd_idx)) hq_mem

public lemma CFSG.IsHallSubgroup.map_conj
    (hH : IsHallSubgroup π H) (g : G) :
    IsHallSubgroup π (H.map (MulAut.conj g).toMonoidHom) :=
  hH.map_mulAut (MulAut.conj g)

end HallCardinality

public lemma CFSG.IsPiSubgroup.of_le {π : Set Nat.Primes} {H K : Subgroup G} (hHK : H ≤ K)
    (hK : IsPiSubgroup π K) : IsPiSubgroup π H := by
  intro p hp
  apply hK p
  have : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK
  exact hp.trans this

public lemma CFSG.card_map_dvd_card {G Q : Type*} [Group G] [Group Q] (f : G →* Q) (H : Subgroup G)
    : Nat.card (H.map f) ∣ Nat.card H :=
  Subgroup.card_map_dvd H f

end PiInfrastructure
