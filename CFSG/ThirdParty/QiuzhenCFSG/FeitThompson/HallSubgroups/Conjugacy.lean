module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Bracket
import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Notation.Defs
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Sylow
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Basic
import Mathlib.Tactic.TypeStar

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Complements
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Existence

namespace CFSG
end CFSG
open CFSG


/-
**Kind**: Theorem
**Note**: Proposition 1.5
**Stmt**:
Let $G$ be a finite solvable group.
Let $A$ be an operator group on $G$ with $gcd(|A|, |G|) = 1$.
Let $\pi$ be a set of primes.
(a) $A$ fixes some Hall $\pi$-subgroup of $G$.
(b) Every $A$-invariant $\pi$-subgroup of $G$ is contained in an $A$-invariant Hall $\pi$-subgroup of $G$.
(c) If $H_1$ and $H_2$ are $A$-invariant Hall $\pi$-subgroups of $G$, then $H_1$ and $H_2$ are conjugate by an element of $C_G(A)$.
(d) If $H$ is any $A$-invariant normal subgroup of $G$, then $C_{G/H}(A)$ is the image of $C_G(A)$ in $G/H$.
(e) If $C_G(A)$ contains a Hall $\pi'$-subgroup of $G$, then $[G, A] \subset \mathcal{O}_{\pi}(G)$.
-/

universe u v

open scoped IsMulCommutative


public theorem CFSG.inf_normalizer_le_of_isHallSubgroup_of_isInvariant
    {G : Type u} {A : Type v} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    {π : Set Nat.Primes} {H₁ H₂ : Subgroup G}
    (hHall₁ : IsHallSubgroup π H₁) (hHall₂ : IsHallSubgroup π H₂)
    (hInv₁ : IsInvariant A G H₁) (hInv₂ : IsInvariant A G H₂) :
    H₂ ⊓ Subgroup.normalizer H₁ ≤ H₁ := by
  let N : Subgroup G := Subgroup.normalizer H₁
  let K : Subgroup N := H₂.subgroupOf N
  let _ : IsInvariant A G H₁ := hInv₁
  have hN_inv : IsInvariant A G N := by
    simpa [N] using isInvariant_normalizer_of_isInvariant (A := A) (G := G) H₁
  let _ : IsInvariant A G N := hN_inv
  let _ : Group.IsSolvable G := hsolv
  have hsolvN : Group.IsSolvable N := by infer_instance
  have hcoprimeN : Nat.Coprime (Nat.card A) (Nat.card N) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card (s := N) (α := G)) hcoprime
  have hPiH₂ : IsPiSubgroup (G := G) π H₂ := by
    intro p hp
    exact hHall₂.p_in_pi_of_p_dvd_card p hp
  have hK_pi : IsPiSubgroup (G := N) π K := by
    intro p hp
    have hcard_dvd : Nat.card K ∣ Nat.card H₂ := by
      have hmap_le : K.map N.subtype ≤ H₂ := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact hy
      have hdiv_map : Nat.card (K.map N.subtype) ∣ Nat.card H₂ :=
        Subgroup.card_dvd_of_le hmap_le
      have hcard_map : Nat.card (K.map N.subtype) = Nat.card K := by
        simpa using
          (Subgroup.card_map_of_injective (K := K) (f := N.subtype) N.subtype_injective)
      exact hcard_map.symm ▸ hdiv_map
    exact hPiH₂ p (hp.trans hcard_dvd)
  have hK_inv : IsInvariant A N K := by
    refine ⟨?_⟩
    intro a x
    change (x.1 ∈ H₂) ↔ (a • x.1 ∈ H₂)
    exact hInv₂.invariant a x.1
  obtain ⟨L, hL_hall, _hL_inv, hK_le_L⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := N) (A := A) hsolvN hcoprimeN π K hK_pi hK_inv
  have hH₁N_hall : IsHallSubgroup π (H₁.subgroupOf N) :=
    hHall₁.subgroupOf (hHK := by
      change H₁ ≤ Subgroup.normalizer H₁
      exact Subgroup.le_normalizer)
  have hL_eq : L = H₁.subgroupOf N := hH₁N_hall.eq_of_normal hL_hall
  have hK_le_H₁N : K ≤ H₁.subgroupOf N := by
    simpa [hL_eq] using hK_le_L
  intro x hx
  change ((⟨x, hx.2⟩ : N) : G) ∈ H₁
  have hxK : (⟨x, hx.2⟩ : N) ∈ K := by
    change x ∈ H₂
    exact hx.1
  exact hK_le_H₁N hxK

public lemma CFSG.IsHallSubgroup.map_of_surjective
    {G : Type*} {G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {π : Set Nat.Primes} {H : Subgroup G} (hHall : IsHallSubgroup π H)
    (f : G →* G') (hf : Function.Surjective f) :
    IsHallSubgroup π (H.map f) := by
  refine isHallSubgroup_of (G := G') (π := π) (H := H.map f) (hcard := ?_) (hindex := ?_)
  · intro q hq_dvd
    exact hHall.p_in_pi_of_p_dvd_card q (hq_dvd.trans (Subgroup.card_map_dvd (H := H) f))
  · intro q hq_mem hq_dvd_idx
    have hidx_dvd : (H.map f).index ∣ H.index := Subgroup.index_map_dvd (H := H) hf
    exact (hHall.p_in_pi_of_p_dvd_index q (hq_dvd_idx.trans hidx_dvd)) hq_mem

lemma CFSG.normal_pSubgroup_le_of_isHallSubgroup_of_prime_mem
    {G : Type*} [Group G] [Finite G] {π : Set Nat.Primes}
    {H N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime]
    (hNp : IsPGroup p N) (hHall : IsHallSubgroup π H)
    (hp_mem : (⟨p, Fact.out⟩ : Nat.Primes) ∈ π) :
    N ≤ H := by
  classical
  let PH : Sylow p H := Classical.choice (Sylow.nonempty (p := p) (G := H))
  let Psub : Subgroup G := (PH : Subgroup H).map H.subtype
  have hPsub_p : IsPGroup p Psub := by
    simpa [Psub] using
      (IsPGroup.map (p := p) (H := (PH : Subgroup H)) PH.isPGroup' H.subtype)
  have hp_not_dvd_Hindex : ¬ p ∣ H.index := by
    intro hp_dvd
    exact (hHall.p_in_pi_of_p_dvd_index ⟨p, Fact.out⟩ hp_dvd) hp_mem
  have hp_not_dvd_PHindex : ¬ p ∣ (PH : Subgroup H).index := PH.not_dvd_index
  have hp_not_dvd_Psubindex : ¬ p ∣ Psub.index := by
    have hidx : Psub.index = (PH : Subgroup H).index * H.index := by
      simpa [Psub] using (Subgroup.index_map_subtype (K := (PH : Subgroup H)))
    rw [hidx]
    exact Nat.Prime.not_dvd_mul Fact.out hp_not_dvd_PHindex hp_not_dvd_Hindex
  let S : Sylow p G := IsPGroup.toSylow (p := p) hPsub_p hp_not_dvd_Psubindex
  have hS_le_H : (S : Subgroup G) ≤ H := by
    intro x hx
    change x ∈ Psub at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  obtain ⟨Q, hNQ⟩ := IsPGroup.exists_le_sylow (p := p) hNp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  have hN_le_gQ : N ≤ ((g • Q : Sylow p G) : Subgroup G) := by
    intro n hn
    rw [Sylow.coe_subgroup_smul]
    refine (Subgroup.mem_pointwise_smul_iff_inv_smul_mem (a := MulAut.conj g)
      (S := (Q : Subgroup G)) (x := n)).2 ?_
    have hconj : g⁻¹ * n * g ∈ N := by
      simpa using ((inferInstance : N.Normal).conj_mem n hn g⁻¹)
    have hQ : g⁻¹ * n * g ∈ (Q : Subgroup G) := hNQ hconj
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hQ
  have hN_le_S : N ≤ (S : Subgroup G) := by
    simpa [hg] using hN_le_gQ
  exact le_trans hN_le_S hS_le_H

lemma CFSG.disjoint_isHallSubgroup_normal_pSubgroup_of_prime_not_mem
    {G : Type*} [Group G] [Finite G] {π : Set Nat.Primes}
    {H N : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hHall : IsHallSubgroup π H) (hNp : IsPGroup p N)
    (hp_not_mem : (⟨p, Fact.out⟩ : Nat.Primes) ∉ π) :
    Disjoint H N := by
  have hHN_p : IsPGroup p (H.subgroupOf N) := by
    exact IsPGroup.to_subgroup (H := H.subgroupOf N) hNp
  have hsub_eq_bot : H.subgroupOf N = ⊥ := by
    by_contra hsub_ne_bot
    obtain ⟨k, hk⟩ := hHN_p.exists_card_eq
    have hp_dvd_subcard : p ∣ Nat.card (H.subgroupOf N) := by
      cases k with
      | zero =>
          exfalso
          have hcard_one : Nat.card (H.subgroupOf N) = 1 := by simp [hk]
          exact hsub_ne_bot ((Subgroup.card_eq_one (H := H.subgroupOf N)).1 hcard_one)
      | succ k =>
          exact ⟨p ^ k, by simp [hk, Nat.pow_succ, Nat.mul_comm]⟩
    have hcard_sub_dvd : Nat.card (H.subgroupOf N) ∣ Nat.card H := by
      have hmap_le : (H.subgroupOf N).map N.subtype ≤ H := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact hy
      have hdiv_map : Nat.card ((H.subgroupOf N).map N.subtype) ∣ Nat.card H :=
        Subgroup.card_dvd_of_le hmap_le
      have hcard_map : Nat.card ((H.subgroupOf N).map N.subtype) = Nat.card (H.subgroupOf N) := by
        simpa using (Subgroup.card_map_of_injective (K := H.subgroupOf N) (f := N.subtype)
          N.subtype_injective)
      exact hcard_map.symm ▸ hdiv_map
    have hp_dvd_card_H : p ∣ Nat.card H := hp_dvd_subcard.trans hcard_sub_dvd
    exact hp_not_mem (hHall.p_in_pi_of_p_dvd_card ⟨p, Fact.out⟩ hp_dvd_card_H)
  rw [Subgroup.disjoint_def]
  intro x hxH hxN
  have hx_sub : (⟨x, hxN⟩ : N) ∈ H.subgroupOf N := hxH
  have hx_sub_eq_one : (⟨x, hxN⟩ : N) = 1 := by
    exact (Subgroup.eq_bot_iff_forall (H := H.subgroupOf N)).1 hsub_eq_bot ⟨x, hxN⟩ hx_sub
  exact congrArg Subtype.val hx_sub_eq_one

lemma CFSG.map_mk'_map_conj_eq
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N) =
      (H.map (QuotientGroup.mk' N)).map (MulAut.conj ((QuotientGroup.mk' N) g)).toMonoidHom := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(QuotientGroup.mk' N) y, ⟨y, hy, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨x, hx, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨g * y * g⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
    · simp [MulAut.conj_apply, mul_assoc]

lemma CFSG.lift_conj_eq_of_map_eq
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {H₁ H₂ : Subgroup G} (g : G)
    (hker₁ : N ≤ H₁) (hker₂ : N ≤ H₂)
    (hmap : H₂.map (QuotientGroup.mk' N) =
      (H₁.map (QuotientGroup.mk' N)).map (MulAut.conj ((QuotientGroup.mk' N) g)).toMonoidHom) :
    H₂ = H₁.map (MulAut.conj g).toMonoidHom := by
  let H₁g : Subgroup G := H₁.map (MulAut.conj g).toMonoidHom
  have hker₂' : (QuotientGroup.mk' N).ker ≤ H₂ := by
    simpa [QuotientGroup.ker_mk'] using hker₂
  have hker₁g : (QuotientGroup.mk' N).ker ≤ H₁g := by
    intro x hx
    have hxN : x ∈ N := by
      simpa [QuotientGroup.ker_mk'] using hx
    refine Subgroup.mem_map.mpr ?_
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact hker₁ (by simpa [mul_assoc] using ((inferInstance : N.Normal).conj_mem x hxN g⁻¹))
    · simp [MulAut.conj_apply, mul_assoc]
  have hmap' : H₂.map (QuotientGroup.mk' N) = H₁g.map (QuotientGroup.mk' N) := by
    calc
      H₂.map (QuotientGroup.mk' N)
          = (H₁.map (QuotientGroup.mk' N)).map (MulAut.conj ((QuotientGroup.mk' N) g)).toMonoidHom :=
              hmap
      _ = (H₁.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N) :=
            (map_mk'_map_conj_eq (N := N) H₁ g).symm
      _ = H₁g.map (QuotientGroup.mk' N) := rfl
  have hcomap := congrArg (fun K : Subgroup (G ⧸ N) => K.comap (QuotientGroup.mk' N)) hmap'
  have hcomap' : H₂ = H₁g ⊔ N := by
    simpa [Subgroup.comap_map_eq_self hker₂', Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using hcomap
  have hN_le_H₁g : N ≤ H₁g := by
    simpa [QuotientGroup.ker_mk'] using hker₁g
  have hsup_eq : H₁g ⊔ N = H₁g := sup_eq_left.mpr hN_le_H₁g
  change H₂ = H₁g
  exact hcomap'.trans hsup_eq

public lemma CFSG.map_subgroupOf_map_conj_eq
    {G : Type*} [Group G]
    {K0 K : Subgroup G} (hK : K ≤ K0) (n : K0) :
    ((K.subgroupOf K0).map (MulAut.conj (n : K0)).toMonoidHom).map K0.subtype
      = K.map (MulAut.conj ((n : K0) : G)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(z : G), hz, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    have hyK0 : y ∈ K0 := hK hy
    have hny_mem : (n : G) * y ∈ K0 := K0.mul_mem n.property hyK0
    have hxyK0 : (n : G) * y * (n : G)⁻¹ ∈ K0 :=
      K0.mul_mem hny_mem (K0.inv_mem n.property)
    refine ⟨⟨(n : G) * y * (n : G)⁻¹, hxyK0⟩, ?_, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    let z : K.subgroupOf K0 := ⟨⟨y, hK hy⟩, hy⟩
    refine ⟨z, z.property, ?_⟩
    ext
    simp [z, MulAut.conj_apply, mul_assoc]

public lemma CFSG.map_conj_mul_right_eq_of_mem_normalizer
    {G : Type*} [Group G] {H : Subgroup G} (g : G) (x : Subgroup.normalizer H) :
    H.map (MulAut.conj (g * x.val)).toMonoidHom = H.map (MulAut.conj g).toMonoidHom := by
  ext z
  constructor
  · intro hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(x : G) * y * (x : G)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp x.property y).1 hy
    · simp [MulAut.conj_apply, mul_assoc]
  · intro hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(x : G)⁻¹ * y * (x : G), ?_, ?_⟩
    · have hxinv : (x : G)⁻¹ ∈ Subgroup.normalizer H := (Subgroup.normalizer H).inv_mem (by exact x.property)
      simpa using (Subgroup.mem_normalizer_iff.mp hxinv y).1 hy
    · simp [MulAut.conj_apply, mul_assoc]

public lemma CFSG.exists_fixedPoint_conj_of_normalizer_coboundary
    {G : Type u} {A : Type v} [Group G] [Group A] [MulDistribMulAction A G]
    {H₁ H₂ : Subgroup G} {g : G}
    (hconj : H₂ = H₁.map (MulAut.conj g).toMonoidHom)
    (φ : A → Subgroup.normalizer H₁) (hsmul_g : ∀ a : A, a • g = g * (φ a : G))
    (x : Subgroup.normalizer H₁) (hx : ∀ a : A, (φ a).val = (x : G) * (a • x.val)⁻¹) :
    ∃ c : G, c ∈ fixedPointSubgroup A G ∧ H₂ = H₁.map (MulAut.conj c).toMonoidHom := by
  refine ⟨g * (x : G), ?_, ?_⟩
  · refine ?_
    simp [fixedPointSubgroup]
    intro a
    calc
      (a • g) * (a • (x : G)) = (g * (φ a : G)) * (a • (x : G)) := by rw [hsmul_g a]
      _ = (g * ((x : G) * (a • (x : G))⁻¹)) * (a • (x : G)) := by rw [hx a]
      _ = g * (x : G) := by simp [mul_assoc]
  · calc
      H₂ = H₁.map (MulAut.conj g).toMonoidHom := hconj
      _ = H₁.map (MulAut.conj (g * (x : G))).toMonoidHom :=
        (map_conj_mul_right_eq_of_mem_normalizer (H := H₁) g x).symm

lemma CFSG.exists_normalizer_factor_of_conj_eq_of_isInvariant
    {G : Type*} {A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    {H₁ H₂ : Subgroup G} (hInv₁ : IsInvariant A G H₁) (hInv₂ : IsInvariant A G H₂)
    {g : G} (hconj : H₂ = H₁.map (MulAut.conj g).toMonoidHom) :
    ∃ φ : A → Subgroup.normalizer H₁,
      (∀ a : A, a • g = g * (φ a : G)) ∧
      (∀ a b : A, (φ (a * b) : G) = (φ a : G) * (a • (φ b).val)) := by
  have hconj_mem (z : G) : z ∈ H₂ ↔ g⁻¹ * z * g ∈ H₁ := by
    simpa [hconj, MulAut.conj_symm_apply, mul_assoc] using
      (Subgroup.mem_map_equiv (f := MulAut.conj g) (K := H₁) (x := z))
  let φ : A → Subgroup.normalizer H₁ := fun a =>
    ⟨g⁻¹ * (a • g), by
      refine (Subgroup.mem_normalizer_iff).2 ?_
      intro h
      calc
        h ∈ H₁ ↔ a⁻¹ • h ∈ H₁ := (hInv₁.invariant a⁻¹ h)
        _ ↔ g⁻¹ * (g * (a⁻¹ • h) * g⁻¹) * g ∈ H₁ := by simp [mul_assoc]
        _ ↔ g * (a⁻¹ • h) * g⁻¹ ∈ H₂ := (hconj_mem (g * (a⁻¹ • h) * g⁻¹)).symm
        _ ↔ a • (g * (a⁻¹ • h) * g⁻¹) ∈ H₂ := (hInv₂.invariant a (g * (a⁻¹ • h) * g⁻¹))
        _ ↔ (a • g) * h * (a • g)⁻¹ ∈ H₂ := by
              simp [smul_mul', smul_inv_smul, mul_assoc]
        _ ↔ g⁻¹ * ((a • g) * h * (a • g)⁻¹) * g ∈ H₁ := hconj_mem ((a • g) * h * (a • g)⁻¹)
        _ ↔ (g⁻¹ * (a • g)) * h * (g⁻¹ * (a • g))⁻¹ ∈ H₁ := by
              simp [mul_assoc]⟩
  refine ⟨φ, ?_, ?_⟩
  · intro a
    simp [φ]
  · intro a b
    have hab₁ : (a * b) • g = g * (φ (a * b) : G) := by
      simp [φ]
    have hab₂ : (a * b) • g = g * ((φ a : G) * (a • (φ b : G))) := by
      calc
        (a * b) • g = a • (b • g) := by simp [mul_smul]
        _ = a • (g * (φ b : G)) := by rw [show b • g = g * (φ b : G) by simp [φ]]
        _ = (a • g) * (a • (φ b : G)) := by simp [smul_mul']
        _ = (g * (φ a : G)) * (a • (φ b : G)) := by rw [show a • g = g * (φ a : G) by simp [φ]]
        _ = g * ((φ a : G) * (a • (φ b : G))) := by simp [mul_assoc]
    have hEq : g * (φ (a * b) : G) = g * ((φ a : G) * (a • (φ b : G))) := hab₁.symm.trans hab₂
    exact mul_left_cancel hEq

public theorem CFSG.exists_principal_cocycle_of_solvable_coprime
    {A : Type v} [Group A] [Finite A] :
    ∀ {N : Type u} [Group N] [Finite N] [MulDistribMulAction A N],
      Group.IsSolvable N →
      Nat.Coprime (Nat.card A) (Nat.card N) →
      ∀ c : A → N, (∀ a b : A, c (a * b) = c a * (a • c b)) →
        ∃ x : N, ∀ a : A, c a = x * (a • x)⁻¹ := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (N' : Type u) [Group N'] [Finite N'] [MulDistribMulAction A N'],
      Nat.card N' = n →
      Group.IsSolvable N' →
      Nat.Coprime (Nat.card A) (Nat.card N') →
      ∀ c : A → N', (∀ a b : A, c (a * b) = c a * (a • c b)) →
        ∃ x : N', ∀ a : A, c a = x * (a • x)⁻¹
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih N' _ _ _ hcard hsolv' hcop' c hc
    by_cases hcomm : IsMulCommutative N'
    · let _ : IsMulCommutative N' := hcomm
      obtain ⟨x, hx⟩ :=
        exists_coboundary_of_cocycle_of_coprime_card
          (A := A) (N := N') c hc hcop'
      refine ⟨x, ?_⟩
      intro a
      simpa [mul_comm] using hx a
    · have hnot_subsingleton : ¬ Subsingleton N' := by
        intro hsub
        have hcommStd : Std.Commutative (· * · : N' → N' → N') := by
          refine ⟨?_⟩
          intro x y
          have hx : x = 1 := hsub.elim x 1
          have hy : y = 1 := hsub.elim y 1
          simp [hx, hy]
        have hcomm' : IsMulCommutative N' := ⟨hcommStd⟩
        exact hcomm hcomm'
      have _ : Nontrivial N' := not_subsingleton_iff_nontrivial.mp hnot_subsingleton
      let _ : Group.IsSolvable N' := hsolv'
      let D : Subgroup N' := commutator N'
      have hDlt_top : D < ⊤ := by
        simpa [D] using (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := N'))
      let _ : D.Normal := by
        simpa [D] using (inferInstance : (commutator N').Normal)
      let _ : D.Characteristic := by
        simpa [D] using (inferInstance : (commutator N').Characteristic)
      let _ : IsInvariant A N' D :=
        isInvariant_of_characteristic (A := A) (G := N') D
      let _ : MulAction.QuotientAction A D :=
        quotientAction_of_isInvariant (A := A) (G := N') D (inferInstance : IsInvariant A N' D)
      let _ : Finite (N' ⧸ D) := by infer_instance
      let _ : MulDistribMulAction A (N' ⧸ D) :=
        quotientMulDistribMulAction (A := A) (G := N') D (inferInstance : IsInvariant A N' D)
      let _ : IsMulCommutative (N' ⧸ D) := by
        exact
          (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := D)).2
            (le_rfl : commutator N' ≤ commutator N')
      let cQ : A → N' ⧸ D := fun a => (QuotientGroup.mk' D) (c a)
      have hcQ : ∀ a b : A, cQ (a * b) = cQ a * (a • cQ b) := by
        intro a b
        change
          (QuotientGroup.mk' D) (c (a * b)) =
            (QuotientGroup.mk' D) (c a) * (a • ((QuotientGroup.mk' D) (c b)))
        simp [hc, MulAction.Quotient.smul_mk]
      have hcopQ : Nat.Coprime (Nat.card A) (Nat.card (N' ⧸ D)) := by
        have hdvd : Nat.card (N' ⧸ D) ∣ Nat.card N' :=
          Subgroup.card_quotient_dvd_card (s := D)
        exact Nat.Coprime.of_dvd_right hdvd hcop'
      obtain ⟨xQ, hxQ⟩ :=
        exists_coboundary_of_cocycle_of_coprime_card
          (A := A) (N := N' ⧸ D) cQ hcQ hcopQ
      obtain ⟨x0, rfl⟩ := QuotientGroup.mk'_surjective D xQ
      let cD : A → D := fun a =>
        ⟨x0⁻¹ * c a * (a • x0), by
          have hEqQ :
              (QuotientGroup.mk' D) (c a) =
                (QuotientGroup.mk' D) (x0 * (a • x0)⁻¹) := by
            calc
              (QuotientGroup.mk' D) (c a)
                  = (a • ((QuotientGroup.mk' D) x0))⁻¹ * (QuotientGroup.mk' D) x0 := by
                      simpa [cQ, MulAction.Quotient.smul_mk] using hxQ a
              _ = (QuotientGroup.mk' D) x0 * (a • ((QuotientGroup.mk' D) x0))⁻¹ := by
                      simp [mul_comm]
              _ = (QuotientGroup.mk' D) (x0 * (a • x0)⁻¹) := by
                      simp [MulAction.Quotient.smul_mk]
          have hdiv_mem : (x0 * (a • x0)⁻¹) / c a ∈ D :=
            (QuotientGroup.eq_iff_div_mem).1 hEqQ.symm
          have hmul_mem : c a * (a • x0) * x0⁻¹ ∈ D := by
            have hdiv_inv : ((x0 * (a • x0)⁻¹) / c a)⁻¹ ∈ D := D.inv_mem hdiv_mem
            simpa [div_eq_mul_inv, mul_assoc] using hdiv_inv
          have hconj :
              x0⁻¹ * (c a * (a • x0) * x0⁻¹) * (x0⁻¹)⁻¹ ∈ D :=
            (inferInstance : D.Normal).conj_mem _ hmul_mem x0⁻¹
          simpa [mul_assoc] using hconj⟩
      have hcD : ∀ a b : A, cD (a * b) = cD a * (a • cD b) := by
        intro a b
        ext
        change
          x0⁻¹ * c (a * b) * ((a * b) • x0) =
            (x0⁻¹ * c a * (a • x0)) * (a • (x0⁻¹ * c b * (b • x0)))
        simp [hc, smul_mul', smul_smul, mul_assoc]
      have hcopD : Nat.Coprime (Nat.card A) (Nat.card D) := by
        have hdvd : Nat.card D ∣ Nat.card N' := Subgroup.card_subgroup_dvd_card (s := D)
        exact Nat.Coprime.of_dvd_right hdvd hcop'
      have hDlt : Nat.card D < n := by
        have hD_one_lt : 1 < D.index := Subgroup.one_lt_index_of_ne_top (ne_of_lt hDlt_top)
        have hD_pos : 0 < Nat.card D := Nat.card_pos (α := D)
        have hlt : Nat.card D < Nat.card D * D.index := by
          simpa [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hD_one_lt hD_pos
        have hEq : Nat.card D * D.index = n := by
          calc
            Nat.card D * D.index = D.index * Nat.card D := by simp [Nat.mul_comm]
            _ = Nat.card N' := by simpa using (Subgroup.index_mul_card (H := D))
            _ = n := hcard
        simpa [hEq] using hlt
      have hsolvD : Group.IsSolvable D := by infer_instance
      obtain ⟨y, hy⟩ :=
        (ih (Nat.card D) hDlt) D rfl hsolvD hcopD cD hcD
      refine ⟨x0 * (y : N'), ?_⟩
      intro a
      have hy' : x0⁻¹ * c a * (a • x0) = (y : N') * (a • (y : N'))⁻¹ := by
        have htmp := congrArg Subtype.val (hy a)
        change x0⁻¹ * c a * (a • x0) = (y : N') * (a • (y : N'))⁻¹ at htmp
        exact htmp
      calc
        c a = x0 * (x0⁻¹ * c a * (a • x0)) * (a • x0)⁻¹ := by
                simp [mul_assoc]
        _ = x0 * ((y : N') * (a • (y : N'))⁻¹) * (a • x0)⁻¹ := by
                rw [hy']
        _ = (x0 * (y : N')) * (a • (x0 * (y : N')))⁻¹ := by
                simp [smul_mul', mul_assoc]
  exact fun {N} _ _ _ hsolv hcop c hc =>
    hP (Nat.card N) N rfl hsolv hcop c hc

open scoped Pointwise in
public theorem CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable
    {G : Type u} [Group G] [Finite G] (hsolv : Group.IsSolvable G)
    {π : Set Nat.Primes} {H₁ H₂ : Subgroup G}
    (hHall₁ : IsHallSubgroup π H₁) (hHall₂ : IsHallSubgroup π H₂) :
    ∃ g : G, H₂ = H₁.map (MulAut.conj g).toMonoidHom := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (G' : Type u) [Group G'] [Finite G'],
      Nat.card G' = n →
      Group.IsSolvable G' →
      ∀ (π' : Set Nat.Primes) (K₁ K₂ : Subgroup G'),
        IsHallSubgroup π' K₁ →
        IsHallSubgroup π' K₂ →
          ∃ g : G', K₂ = K₁.map (MulAut.conj g).toMonoidHom
  have main : ∀ n, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih G' _ _ hcard hsolv' π' K₁ K₂ hHallK₁ hHallK₂
    by_cases hG' : Nat.card G' = 1
    · refine ⟨1, ?_⟩
      have hK₁_bot : K₁ = ⊥ := by
        have hcardK₁ : Nat.card K₁ = 1 := by
          have hdiv : Nat.card K₁ ∣ Nat.card G' := Subgroup.card_subgroup_dvd_card K₁
          rw [hG'] at hdiv
          exact Nat.eq_one_of_dvd_one hdiv
        exact (Subgroup.card_eq_one (H := K₁)).1 hcardK₁
      have hK₂_bot : K₂ = ⊥ := by
        have hcardK₂ : Nat.card K₂ = 1 := by
          have hdiv : Nat.card K₂ ∣ Nat.card G' := Subgroup.card_subgroup_dvd_card K₂
          rw [hG'] at hdiv
          exact Nat.eq_one_of_dvd_one hdiv
        exact (Subgroup.card_eq_one (H := K₂)).1 hcardK₂
      subst hK₁_bot
      subst hK₂_bot
      ext x
      simp
    have hG'_pos : 0 < Nat.card G' := Nat.card_pos (α := G')
    have hG'_one_lt : 1 < Nat.card G' :=
      lt_of_le_of_ne (Nat.succ_le_iff.mp hG'_pos) (Ne.symm hG')
    let pds : ℕ → Prop := fun i => derivedSeries G' i = ⊥
    have hpds : ∃ i, pds i := hsolv'.solvable
    let i : ℕ := Nat.find hpds
    have hi_spec : derivedSeries G' i = ⊥ := Nat.find_spec hpds
    have hi_ne_zero : i ≠ 0 := by
      intro hi0
      have h0 : derivedSeries G' 0 = ⊥ := by simpa [i, hi0] using hi_spec
      have htop : (⊤ : Subgroup G') = (⊥ : Subgroup G') := by
        simpa [derivedSeries_zero] using h0
      have hcard' : Nat.card G' = 1 := by
        have : Nat.card (⊤ : Subgroup G') = 1 := by
          exact (Subgroup.card_eq_one (H := (⊤ : Subgroup G'))).2 htop
        simpa using this
      exact (ne_of_gt hG'_one_lt) hcard'
    let N : Subgroup G' := derivedSeries G' (i - 1)
    have hN_ne_bot : N ≠ ⊥ := by
      have hi_lt : i - 1 < i := Nat.sub_one_lt hi_ne_zero
      have : ¬ pds (i - 1) := Nat.find_min hpds hi_lt
      exact fun hN_bot => this (by simp only [pds, N, hN_bot])
    have _ : N.Normal := derivedSeries_normal (G := G') (i - 1)
    have _ : N.Characteristic := derivedSeries_characteristic (G := G') (i - 1)
    have hcomm_bot : ⁅N, N⁆ = ⊥ := by
      have hi1 : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi_ne_zero)
      have hderived : derivedSeries G' i = ⁅N, N⁆ := by
        calc
          derivedSeries G' i = derivedSeries G' (i - 1 + 1) := by simp only [hi1]
          _ = ⁅derivedSeries G' (i - 1), derivedSeries G' (i - 1)⁆ := by
                simp only [derivedSeries_succ]
          _ = ⁅N, N⁆ := by simp only [N]
      simpa [hderived] using hi_spec
    have _ : IsMulCommutative (↥N) := by
      have hN_le_centralizer : N ≤ Subgroup.centralizer (N : Set G') :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := N) (H₂ := N)).1 hcomm_bot
      exact (Subgroup.le_centralizer_iff_isMulCommutative (K := N)).1 hN_le_centralizer
    have hN_card_ne_one : Nat.card (↥N) ≠ 1 := by
      have : 1 < Nat.card (↥N) := (Subgroup.one_lt_card_iff_ne_bot (H := N)).2 hN_ne_bot
      exact ne_of_gt this
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (↥N)) hN_card_ne_one
    have _ : Fact p.Prime := ⟨hp_prime⟩
    let P₀ : Sylow p N := Classical.choice (Sylow.nonempty (p := p) (G := N))
    have hP₀_ne_bot : (P₀ : Subgroup N) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := N) P₀ (by simpa using hp_dvd)
    have hP₀_normal : (P₀ : Subgroup N).Normal := by
      simpa using (Subgroup.normal_of_isMulCommutative (H := (P₀ : Subgroup N)))
    have _ : Unique (Sylow p N) := Sylow.unique_of_normal (G := N) (p := p) P₀ hP₀_normal
    have _ : Subsingleton (Sylow p N) := by infer_instance
    have _ : (P₀ : Subgroup N).Characteristic := Sylow.characteristic_of_subsingleton (G := N) P₀
    let Psub : Subgroup G' := (P₀ : Subgroup N).map N.subtype
    have hP₀_p : IsPGroup p (P₀ : Subgroup N) := P₀.isPGroup'
    have hPsub_p : IsPGroup p Psub := by
      simpa [Psub] using (IsPGroup.map (p := p) (H := (P₀ : Subgroup N)) hP₀_p N.subtype)
    have _ : Psub.Normal := by infer_instance
    let Q := G' ⧸ Psub
    let _ : Group Q := by infer_instance
    let _ : Finite Q := by infer_instance
    have hQ_solv : Group.IsSolvable Q := by infer_instance
    have hQ_lt : Nat.card Q < n := by
      have hmul := (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := G') (s := Psub))
      have hPsub_ne_bot : Psub ≠ ⊥ := by
        intro hbot
        have hmap_bot : (P₀ : Subgroup N).map N.subtype = ⊥ := by simpa [Psub] using hbot
        have hP0_bot : (P₀ : Subgroup N) = ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective (H := (P₀ : Subgroup N)) (f := N.subtype)
            N.subtype_injective).1 hmap_bot
        exact hP₀_ne_bot hP0_bot
      have hPsub_one_lt : 1 < Nat.card Psub := (Subgroup.one_lt_card_iff_ne_bot (H := Psub)).2 hPsub_ne_bot
      have hQ_pos : 0 < Nat.card Q := Nat.card_pos (α := Q)
      have hlt : Nat.card Q < Nat.card Q * Nat.card Psub := by
        simpa [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hPsub_one_lt hQ_pos
      have : Nat.card Q * Nat.card Psub = n := by simpa [hcard] using hmul.symm
      simpa [this] using hlt
    let f : G' →* Q := QuotientGroup.mk' Psub
    have hf : Function.Surjective f := by
      simpa only [f, Q] using QuotientGroup.mk'_surjective Psub
    let Kbar₁ : Subgroup Q := K₁.map f
    let Kbar₂ : Subgroup Q := K₂.map f
    have hHallbar₁ : IsHallSubgroup π' Kbar₁ := by
      simpa [Kbar₁] using (IsHallSubgroup.map_of_surjective (hHall := hHallK₁) f hf)
    have hHallbar₂ : IsHallSubgroup π' Kbar₂ := by
      simpa [Kbar₂] using (IsHallSubgroup.map_of_surjective (hHall := hHallK₂) f hf)
    obtain ⟨qbar, hqbar⟩ :=
      (ih (Nat.card Q) hQ_lt) Q rfl hQ_solv π' Kbar₁ Kbar₂ hHallbar₁ hHallbar₂
    obtain ⟨g, hg_lift⟩ := QuotientGroup.mk'_surjective Psub qbar
    have hqbar' :
        K₂.map f = (K₁.map f).map (MulAut.conj (f g)).toMonoidHom := by
      subst qbar
      simpa only [Kbar₁, Kbar₂, f, Q, QuotientGroup.mk'_apply] using hqbar
    let p' : Nat.Primes := ⟨p, hp_prime⟩
    by_cases hp_mem : p' ∈ π'
    · have hp_mem_fact : (⟨p, Fact.out⟩ : Nat.Primes) ∈ π' := by
        rw [show (⟨p, Fact.out⟩ : Nat.Primes) = p' by rfl]
        exact hp_mem
      have hPsub_le_K₁ : Psub ≤ K₁ :=
        normal_pSubgroup_le_of_isHallSubgroup_of_prime_mem
          (H := K₁) (N := Psub) hPsub_p hHallK₁ hp_mem_fact
      have hPsub_le_K₂ : Psub ≤ K₂ :=
        normal_pSubgroup_le_of_isHallSubgroup_of_prime_mem
          (H := K₂) (N := Psub) hPsub_p hHallK₂ hp_mem_fact
      refine ⟨g, ?_⟩
      exact lift_conj_eq_of_map_eq
        (N := Psub) (H₁ := K₁) (H₂ := K₂) g hPsub_le_K₁ hPsub_le_K₂ hqbar'
    · have hp_not_mem : p' ∉ π' := hp_mem
      have hp_not_mem_fact : (⟨p, Fact.out⟩ : Nat.Primes) ∉ π' := by
        rw [show (⟨p, Fact.out⟩ : Nat.Primes) = p' by rfl]
        exact hp_not_mem
      let K₁g : Subgroup G' := K₁.map (MulAut.conj g).toMonoidHom
      have hHallK₁g : IsHallSubgroup π' K₁g := by
        simpa [K₁g] using hHallK₁.map_conj g
      have hDisK₂ : Disjoint K₂ Psub :=
        disjoint_isHallSubgroup_normal_pSubgroup_of_prime_not_mem
          (H := K₂) (N := Psub) hHallK₂ hPsub_p hp_not_mem_fact
      have hDisK₁g : Disjoint K₁g Psub :=
        disjoint_isHallSubgroup_normal_pSubgroup_of_prime_not_mem
          (H := K₁g) (N := Psub) hHallK₁g hPsub_p hp_not_mem_fact
      have hmapK₁g : (K₁.map f).map (MulAut.conj (f g)).toMonoidHom = K₁g.map f := by
        simpa only [K₁g, f, Q, QuotientGroup.mk'_apply] using
          (map_mk'_map_conj_eq (N := Psub) K₁ g).symm
      have hqbar'' : K₂.map f = K₁g.map f := hqbar'.trans hmapK₁g
      let K0 : Subgroup G' := (K₂.map f).comap f
      have hK₂_le_K0 : K₂ ≤ K0 := by
        intro x hx
        change f x ∈ K₂.map f
        exact ⟨x, hx, rfl⟩
      have hK₁g_le_K0 : K₁g ≤ K0 := by
        intro x hx
        change f x ∈ K₂.map f
        have hx' : f x ∈ K₁g.map f := ⟨x, hx, rfl⟩
        simpa [K0, hqbar''] using hx'
      have hker_eq : f.ker = Psub := by
        change (QuotientGroup.mk' Psub).ker = Psub
        exact QuotientGroup.ker_mk' Psub
      have hPsub_le_K0 : Psub ≤ K0 := by
        exact hker_eq ▸ (Subgroup.ker_le_comap f (K₂.map f))
      let Pk : Subgroup K0 := Psub.subgroupOf K0
      let K₂k : Subgroup K0 := K₂.subgroupOf K0
      let K₁gk : Subgroup K0 := K₁g.subgroupOf K0
      have _ : Pk.Normal := by
        simpa [Pk] using
          (Subgroup.Normal.subgroupOf (H := Psub) (K := K0) (inferInstance : Psub.Normal))
      have _ : IsMulCommutative (↥Pk) := by infer_instance
      have hK0_eq_sup_K₂ : K0 = K₂ ⊔ Psub := by
        calc
          K0 = (K₂.map f).comap f := rfl
          _ = K₂ ⊔ f.ker := Subgroup.comap_map_eq (f := f) (H := K₂)
          _ = K₂ ⊔ Psub := by rw [hker_eq]
      have hK0_eq_sup_K₁g : K0 = K₁g ⊔ Psub := by
        calc
          K0 = (K₂.map f).comap f := rfl
          _ = (K₁g.map f).comap f := by simp [hqbar'']
          _ = K₁g ⊔ f.ker := Subgroup.comap_map_eq (f := f) (H := K₁g)
          _ = K₁g ⊔ Psub := by rw [hker_eq]
      have hsup_K₂ : K₂k ⊔ Pk = ⊤ := by
        calc
          K₂k ⊔ Pk = (K₂ ⊔ Psub).subgroupOf K0 := by
            simpa [K₂k, Pk] using
              (Subgroup.subgroupOf_sup (A := K₂) (A' := Psub) (B := K0) hK₂_le_K0 hPsub_le_K0).symm
          _ = K0.subgroupOf K0 := by simp [hK0_eq_sup_K₂]
          _ = ⊤ := by simp
      have hsup_K₁g : K₁gk ⊔ Pk = ⊤ := by
        calc
          K₁gk ⊔ Pk = (K₁g ⊔ Psub).subgroupOf K0 := by
            simpa [K₁gk, Pk] using
              (Subgroup.subgroupOf_sup (A := K₁g) (A' := Psub) (B := K0) hK₁g_le_K0 hPsub_le_K0).symm
          _ = K0.subgroupOf K0 := by simp [hK0_eq_sup_K₁g]
          _ = ⊤ := by simp
      have hdis_K₂ : Disjoint K₂k Pk := by
        rw [Subgroup.disjoint_def]
        intro x hx₂ hxP
        exact Subtype.ext ((Subgroup.disjoint_def.mp hDisK₂) hx₂ hxP)
      have hdis_K₁g : Disjoint K₁gk Pk := by
        rw [Subgroup.disjoint_def]
        intro x hx₁ hxP
        exact Subtype.ext ((Subgroup.disjoint_def.mp hDisK₁g) hx₁ hxP)
      have hmul_univ_K₂ : ((K₂k : Set K0) * (Pk : Set K0)) = Set.univ := by
        calc
          (K₂k : Set K0) * (Pk : Set K0) = (↑(K₂k ⊔ Pk) : Set K0) := by
            simpa using (Subgroup.mul_normal K₂k Pk).symm
          _ = Set.univ := by simp [hsup_K₂]
      have hmul_univ_K₁g : ((K₁gk : Set K0) * (Pk : Set K0)) = Set.univ := by
        calc
          (K₁gk : Set K0) * (Pk : Set K0) = (↑(K₁gk ⊔ Pk) : Set K0) := by
            simpa using (Subgroup.mul_normal K₁gk Pk).symm
          _ = Set.univ := by simp [hsup_K₁g]
      have hcomp_K₂ : Pk.IsComplement' K₂k := by
        exact (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis_K₂ hmul_univ_K₂).symm
      have hcomp_K₁g : Pk.IsComplement' K₁gk := by
        exact (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis_K₁g hmul_univ_K₁g).symm
      have hPk_p : IsPGroup p Pk := by
        change IsPGroup p (Psub.comap K0.subtype)
        exact IsPGroup.comap_subtype (p := p) (H := Psub) hPsub_p (K := K0)
      have hPk_coprime_index : Nat.Coprime (Nat.card Pk) Pk.index := by
        have hcard_congr : Nat.card (K0 ⧸ Pk) = Nat.card (K₂.map f) := by
          simpa [K0, Pk, hker_eq] using
            card_quotient_subgroupOf_comap_eq (f := f) (hf := hf) (H := (K₂.map f))
        refine Nat.coprime_of_dvd ?_
        intro q hqprime hq_dvd_card hq_dvd_idx
        rcases hPk_p.exists_card_eq with ⟨k, hk⟩
        have hq_dvd_pow : q ∣ p ^ k := by simpa [hk] using hq_dvd_card
        have hq_eq : q = p := Nat.prime_eq_prime_of_dvd_pow hqprime hp_prime hq_dvd_pow
        have hp_dvd_idx : p ∣ Pk.index := by simpa [hq_eq] using hq_dvd_idx
        have hp_dvd_quot : p ∣ Nat.card (K0 ⧸ Pk) := by
          have : Pk.index = Nat.card (K0 ⧸ Pk) := by simp [Subgroup.index_eq_card]
          simpa [this] using hp_dvd_idx
        have hp_dvd_bar : p ∣ Nat.card (K₂.map f) := by simpa [hcard_congr] using hp_dvd_quot
        have : p' ∈ π' := hHallbar₂.p_in_pi_of_p_dvd_card p' hp_dvd_bar
        exact hp_not_mem this
      obtain ⟨n, hn⟩ :=
        Subgroup.exists_conj_eq_of_isComplement'
          (G := K0) (H := Pk) (K₁ := K₁gk) (K₂ := K₂k)
          hPk_coprime_index hcomp_K₁g hcomp_K₂
      have hmap_K₂k : K₂k.map K0.subtype = K₂ := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hK₂_le_K0 hx⟩, hx, rfl⟩
      have hmap_hn := congrArg (fun S : Subgroup K0 => S.map K0.subtype) hn
      have hK₂_eq_conj :
          K₂ = K₁g.map (MulAut.conj (((n : Pk) : K0) : G')).toMonoidHom := by
        calc
          K₂ = K₂k.map K0.subtype := hmap_K₂k.symm
          _ = (K₁gk.map (MulAut.conj (n : K0)).toMonoidHom).map K0.subtype := hmap_hn
          _ = K₁g.map (MulAut.conj (((n : Pk) : K0) : G')).toMonoidHom := by
                simpa [K₁gk] using
                  (map_subgroupOf_map_conj_eq (K0 := K0) (K := K₁g) hK₁g_le_K0 (n := (n : K0)))
      refine ⟨((n : Pk) : K0) * g, ?_⟩
      let n0 : G' := ((n : Pk) : K0)
      have hcomp_conj :
          ((MulAut.conj n0).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
            (MulAut.conj (n0 * g)).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      calc
        K₂ = K₁g.map (MulAut.conj n0).toMonoidHom := by simpa [n0] using hK₂_eq_conj
        _ = K₁.map ((MulAut.conj n0).toMonoidHom.comp (MulAut.conj g).toMonoidHom) := by
              simpa [K₁g] using
                (Subgroup.map_map (K := K₁) (g := (MulAut.conj n0).toMonoidHom)
                  (f := (MulAut.conj g).toMonoidHom))
        _ = K₁.map (MulAut.conj ((((n : Pk) : K0) : G') * g)).toMonoidHom := by
              simpa [n0] using congrArg (fun h : G' →* G' => K₁.map h) hcomp_conj
  exact main (Nat.card G) G rfl hsolv π H₁ H₂ hHall₁ hHall₂

public theorem CFSG.exists_fixedPoint_conj_of_isHallSubgroup_of_isInvariant
    {G : Type u} {A : Type v} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (π : Set Nat.Primes) {H₁ H₂ : Subgroup G}
    (hHall₁ : IsHallSubgroup π H₁) (hHall₂ : IsHallSubgroup π H₂)
    (hInv₁ : IsInvariant A G H₁) (hInv₂ : IsInvariant A G H₂) :
    ∃ g : G, g ∈ fixedPointSubgroup A G ∧ H₂ = H₁.map (MulAut.conj g) := by
  by_cases hH₁norm : H₁.Normal
  · let _ : H₁.Normal := hH₁norm
    have hEq : H₂ = H₁ := hHall₁.eq_of_normal hHall₂
    refine ⟨1, ?_, ?_⟩
    · simp [fixedPointSubgroup]
    · simpa [hEq] using
        (show H₁ = H₁.map ((1 : MulAut G).toMonoidHom) from by
          ext x
          simp)
  · by_cases hH₂norm : H₂.Normal
    · let _ : H₂.Normal := hH₂norm
      have hEq : H₁ = H₂ := hHall₂.eq_of_normal hHall₁
      have : H₁.Normal := by simpa [hEq] using (inferInstance : H₂.Normal)
      exact (hH₁norm this).elim
    · have hInf_le : H₂ ⊓ Subgroup.normalizer H₁ ≤ H₁ :=
        inf_normalizer_le_of_isHallSubgroup_of_isInvariant
          (G := G) (A := A) hsolv hcoprime hHall₁ hHall₂ hInv₁ hInv₂
      by_cases hH₂leN : H₂ ≤ Subgroup.normalizer H₁
      · have hH₂leH₁ : H₂ ≤ H₁ := by
          intro x hx
          exact hInf_le ⟨hx, hH₂leN hx⟩
        have hEq : H₂ = H₁ := hHall₂.eq_of_le hHall₁ hH₂leH₁
        refine ⟨1, ?_, ?_⟩
        · simp [fixedPointSubgroup]
        · simpa [hEq] using
            (show H₁ = H₁.map ((1 : MulAut G).toMonoidHom) from by
              ext x
              simp)
      · have hH₂nleN : ¬ H₂ ≤ Subgroup.normalizer H₁ := hH₂leN
        have hInf'_le : H₁ ⊓ Subgroup.normalizer H₂ ≤ H₂ :=
          inf_normalizer_le_of_isHallSubgroup_of_isInvariant
            (G := G) (A := A) hsolv hcoprime hHall₂ hHall₁ hInv₂ hInv₁
        by_cases hH₁leN₂ : H₁ ≤ Subgroup.normalizer H₂
        · have hH₁leH₂ : H₁ ≤ H₂ := by
            intro x hx
            exact hInf'_le ⟨hx, hH₁leN₂ hx⟩
          have hEq : H₁ = H₂ := hHall₁.eq_of_le hHall₂ hH₁leH₂
          refine ⟨1, ?_, ?_⟩
          · simp [fixedPointSubgroup]
          · simpa [hEq] using
              (show H₁ = H₁.map ((1 : MulAut G).toMonoidHom) from by
                ext x
                simp)
        · have hH₁nleN₂ : ¬ H₁ ≤ Subgroup.normalizer H₂ := hH₁leN₂
          have hH₂_not_subset : ¬ ((H₂ : Set G) ⊆ (Subgroup.normalizer (H₁ : Set G) : Set G)) := hH₂nleN
          have hH₁_not_subset : ¬ ((H₁ : Set G) ⊆ (Subgroup.normalizer (H₂ : Set G) : Set G)) := hH₁nleN₂
          obtain ⟨x, hxH₂, hxN⟩ := Set.not_subset.mp hH₂_not_subset
          obtain ⟨y, hyH₁, hyN⟩ := Set.not_subset.mp hH₁_not_subset
          let _ : x ∈ H₂ := hxH₂
          let _ : x ∉ Subgroup.normalizer H₁ := hxN
          let _ : y ∈ H₁ := hyH₁
          let _ : y ∉ Subgroup.normalizer H₂ := hyN
          have hconj_exists : ∃ g : G, H₂ = H₁.map (MulAut.conj g).toMonoidHom := by
            exact exists_conj_eq_of_isHallSubgroup_of_solvable
              (G := G) hsolv (H₁ := H₁) (H₂ := H₂) hHall₁ hHall₂
          rcases hconj_exists with ⟨g, hconj⟩
          obtain ⟨φ, hsmul_g, hcocycle⟩ :=
            exists_normalizer_factor_of_conj_eq_of_isInvariant
              (H₁ := H₁) (H₂ := H₂) hInv₁ hInv₂ hconj
          let _ : Group.IsSolvable G := hsolv
          have hsolvN : Group.IsSolvable (Subgroup.normalizer (H₁ : Set G)) := by infer_instance
          have hcopN : Nat.Coprime (Nat.card A) (Nat.card (Subgroup.normalizer (H₁ : Set G))) := by
            exact Nat.Coprime.of_dvd_right
              (Subgroup.card_subgroup_dvd_card (s := Subgroup.normalizer H₁) (α := G)) hcoprime
          let _ : IsInvariant A G H₁ := hInv₁
          have hInvN : IsInvariant A G (Subgroup.normalizer H₁) := by
            simpa using isInvariant_normalizer_of_isInvariant (A := A) (G := G) H₁
          let _ : IsInvariant A G (Subgroup.normalizer (H₁ : Set G)) := hInvN
          have hcocycle' :
              ∀ a b : A, φ (a * b) = φ a * (a • φ b) := by
            intro a b
            ext
            exact hcocycle a b
          obtain ⟨x, hx⟩ :=
            exists_principal_cocycle_of_solvable_coprime
              (A := A) (N := Subgroup.normalizer (H₁ : Set G)) hsolvN hcopN φ hcocycle'
          have hphi : ∀ a : A, (φ a : G) = (x : G) * (a • (x : G))⁻¹ := by
            intro a
            exact congrArg Subtype.val (hx a)
          exact exists_fixedPoint_conj_of_normalizer_coboundary
            (H₁ := H₁) (H₂ := H₂) (g := g) hconj φ hsmul_g x hphi
