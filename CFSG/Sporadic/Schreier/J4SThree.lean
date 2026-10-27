
module

public import CFSG.Sporadic.Schreier.J4SThreeBase1

public import CFSG.Sporadic.Schreier.J4SThreeData
public import CFSG.Sporadic.Schreier.J4SOuter
public import CFSG.Sporadic.Schreier.J4SInvolution
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFive
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import Certificates.Certificate2177
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public meta import CFSG.Sporadic.Schreier.J4SKCent
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native
open CFSG.LocalAnalysis.ComponentInitial CFSG.GroupActions MulAction

theorem q3Elt_zero :
    q3Elt 0 = 1 :=
  eq_of_actsBy (Q3_le_K (q3Elt_spec (by norm_num)).1) K.one_mem (q3Elt_spec (by norm_num)).2
    (q3_zero ▸ actsBy_one)

theorem q3Elt_mul
    {k g : ℕ} (hk : k < 27) (hg : g < 2) :
    q3Elt k * q3gen g = q3Elt (q3Edges[k]!)[g]! := by
  obtain ⟨he, hcols⟩ := (q3_all k hk).2.2.2 g hg
  have h1 := actsBy_mul (q3Elt_spec hk).2 (q3gen_acts hg)
  rw [← hcols] at h1
  exact eq_of_actsBy (K.mul_mem (Q3_le_K (q3Elt_spec hk).1) (q3gen_mem_K g))
    (Q3_le_K (q3Elt_spec he).1) h1 (q3Elt_spec he).2

theorem mem_Q3_iff
    {g : J} : g ∈ Q3 ↔ ∃ k < 27, q3Elt k = g := by
  constructor
  · intro hg
    have hg' : g ∈ Submonoid.closure (Set.range fun i : Fin 2 => q3gen i) := by
      rw [← Subgroup.closure_toSubmonoid_of_finite]
      exact hg
    clear hg
    induction hg' using Submonoid.closure_induction_right with
    | one => exact ⟨0, by norm_num, q3Elt_zero⟩
    | mul_right g _ s hs ih =>
      obtain ⟨i, rfl⟩ := hs
      obtain ⟨k, hk, rfl⟩ := ih
      beta_reduce
      exact ⟨_, ((q3_all k hk).2.2.2 i i.isLt).1, (q3Elt_mul hk i.isLt).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact (q3Elt_spec hk).1

theorem card_Q3 :
    Nat.card Q3 = 27 := by
  have hf : Function.Injective fun k : Fin 27 => (⟨q3Elt k, (q3Elt_spec k.isLt).1⟩ : Q3) := by
    intro k k' h
    have h' := Subtype.ext_iff.1 h
    dsimp only at h'
    exact Fin.ext (q3Elt_injOn k.isLt k'.isLt h')
  have hs : Function.Surjective fun k : Fin 27 => (⟨q3Elt k, (q3Elt_spec k.isLt).1⟩ : Q3) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk, rfl⟩ := mem_Q3_iff.1 hg
    exact ⟨⟨k, hk⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hf, hs⟩), Nat.card_fin]

theorem Q3_centralizer
    {q : J} (hq : q ∈ Q3) (h1 : q ≠ 1) :
    Nat.card (Subgroup.centralizer {q} ⊓ N : Subgroup J) ≤ 32 := by
  obtain ⟨k, hk, rfl⟩ := mem_Q3_iff.1 hq
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd q3Elt_zero h1
    · exact h
  rw [card_centralizer_N_of_actsBy (q3Elt_spec hk).2 (fun j hj => by
    rw [← getElem!_eq_getD']; exact (q3_all k hk).2.1 j hj)]
  exact q3_fix k hk hk0

section Generic

variable {G : Type*} [Group G]

end Generic

section Kernel

variable {G : Type*} [Group G] [Finite G] {X : Type*} [MulAction G X] [Finite X]
  [IsPretransitive G X] {H N : Subgroup G} {r : X}

end Kernel

section Core

variable {G : Type*} [Group G] [Finite G]

end Core

theorem card_H_eq :

    Nat.card H = 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 * 23 := by rw [card_H]; norm_num

theorem card_Q3_sylow :
    Nat.card Q3 = 3 ^ (Nat.card H).factorization 3 := by
  rw [card_Q3, card_H_eq]
  have h2 : Nat.Prime 2 := Nat.prime_two
  have h3 : Nat.Prime 3 := Nat.prime_three
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h23 : Nat.Prime 23 := by norm_num
  repeat rw [Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow h2, Nat.Prime.factorization_pow h3,
    Nat.Prime.factorization h5, Nat.Prime.factorization h7, Nat.Prime.factorization h11,
    Nat.Prime.factorization h23, Finsupp.single_apply]
  norm_num

theorem card_centralizer_three
    {h : J} (hh : h ∈ H) (ho : orderOf h = 3) :
    Nat.card (Subgroup.centralizer {h} ⊓ N : Subgroup J) ≤ 32 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb := card_centralizer_le_of_sylow (Q3_le_K.trans K_le_H) card_Q3_sylow conj_mem_N_of_mem_H
    (fun q hq h1 => Q3_centralizer hq h1) hh ho
  exact hb

theorem CTU_J4_pointwise_local_binary_subgroup_automorphism_kernel_is_two_group :
    IsPGroup 2 (pointwiseFixingAut N) ∧ IsPGroup 2 (pointwiseFixingAut H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut J) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut J))
  have hno3 : ∀ {α : MulAut J}, α ∈ pointwiseFixingAut H → α ^ 3 = 1 → α = 1 := by
    intro α hα hα3
    obtain ⟨x₀, hx₀, hu⟩ := horb_J 28336 (by simp)
    have h := pointwise_kernel_no_three stabilizer_root H_isCoatom N_le_H conj_mem_N_of_mem_H
      (by rw [card_N]; norm_num) card_H ⟨x₀, hx₀, hu⟩ (fun h hh ho => card_centralizer_three hh ho)
      hα hα3
    exact h
  have hH : IsPGroup 2 (pointwiseFixingAut H) := by
    refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd (p := 2)
      (Nat.card_pos (α := pointwiseFixingAut H)).ne' fun {q} hq hdvd => ?_)
    rcases R3E_J4_pointwise_local_automorphism_kernel_no_large_primes.2 q hq hdvd with h2 | h3
    · exact h2
    · exfalso
      subst h3
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨β, hβ⟩ := exists_prime_orderOf_dvd_card' (G := pointwiseFixingAut H) 3 hdvd
      have h1 : (β : MulAut J) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, ← hβ, pow_orderOf_eq_one, Subgroup.coe_one]
      have h2 := hno3 β.2 h1
      have : β = 1 := Subtype.ext h2
      rw [this, orderOf_one] at hβ
      omega
  refine ⟨isPGroup_pointwise_of_core N_le_H normalizer_N
    QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2.le isPGroup_N hH, hH⟩

end CFSG.Sporadic.J4Schreier
