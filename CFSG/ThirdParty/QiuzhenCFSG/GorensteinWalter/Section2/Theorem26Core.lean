module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.OddQCoreCentralized
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.OddPCoresCentralizeFitting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FittingCentralizedInvolutionTwoCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleInvolutions
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma21
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma22
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentPGL2AmbientCentralizers
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.DihedralCentralizerInvolutionConjugator
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionNormalizerInfConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerFixesCentralInvolutionOfLargeDihedralSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralInvolutionMemLargeDihedralSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowTorusFixedSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowReflectedToriCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2LowOddCyclicCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralUniqueCentralInvolution
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

namespace CFSG
end CFSG
open CFSG

/-!
# Theorem 2.6 (Bender, "Finite Groups with Dihedral Sylow 2-Subgroups")

Pinned statement (verbatim from `tasks/gw-theorem26.md`):

    CentralizerStructure c

The paper's proof (`refs/bender-dihedral-sylow.tex` L218--L264) splits into
two branches:

* `O₂(Ĥ) ≠ 1`: `U = O(Ĥ)`, `C_S(U) = O₂(Ĥ)`, and the
  `(O₂(Ĥ) ≤ S0 ∧ Ĥ = H)` alternative, using Lemma 2.1 and the preamble
  involution-conjugacy facts;
* `O₂(Ĥ) = 1`: first `E(Ĥ) = 1` (the PGL₂(q) contradiction), then the long
  argument that `t` centralizes every `Ĥ`-invariant odd `p`-subgroup, which
  assembles the final structure.

This module keeps the branch decomposition explicit.  The branch facts are
proved below through explicit reusable endpoints.
In the nontrivial-`O₂` case, the paper proves the full theorem assertion, not
only its first alternative.  The helpers specialized to `Ĥ = H` below retain
the easy first-subcase consequences, while the registered source case has the
full `CentralizerStructure c` conclusion.

The remaining reflected-torus infrastructure for the component branch is
tracked in `tasks/gw-theorem26-r2.md`.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! ## Local `S ≤ H` infrastructure

The setup does not expose `S ≤ H = C_G(t)` in the acyclic import graph, so
we keep the short cyclic-`2`-group argument here: `t` is the unique
involution of the index-two cyclic subgroup `S0` of the dihedral Sylow
subgroup `S`, hence is fixed by conjugation by every element of `S`.
-/

/-- In a cyclic group of order `2^m` with `m ≥ 1`, every two involutions
coincide. -/
private lemma unique_involution_of_cyclic_two_group_t26 {A : Type*} [Group A] [Finite A]
    (hcyc : IsCyclic A) {m : ℕ} (hm : 1 ≤ m)
    (hcard : Nat.card A = 2 ^ m) :
    ∀ x y : A, x ≠ 1 → x ^ 2 = 1 → y ≠ 1 → y ^ 2 = 1 → x = y := by
  classical
  let : IsCyclic A := hcyc
  rcases IsCyclic.exists_monoid_generator (α := A) with ⟨g, hg⟩
  have hord : orderOf g = 2 ^ m := by
    rw [← hcard]
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x
    rcases hg x with ⟨k, rfl⟩
    exact ⟨k, zpow_natCast g k⟩
  have hmm : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have h2m : 2 * 2 ^ (m - 1) = 2 ^ m := by
    calc
      2 * 2 ^ (m - 1) = 2 ^ (m - 1) * 2 := by rw [Nat.mul_comm]
      _ = 2 ^ (m - 1 + 1) := by exact (pow_succ 2 (m - 1)).symm
      _ = 2 ^ m := by rw [hmm]
  have hgpow : g ^ (2 ^ m) = 1 := by
    exact (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 ^ m)).1 (by simp [hord])
  have h2h : (g ^ (2 ^ (m - 1))) ^ 2 = 1 := by
    calc
      (g ^ (2 ^ (m - 1))) ^ 2 = g ^ (2 ^ (m - 1) * 2) := by
        exact (pow_mul g (2 ^ (m - 1)) 2).symm
      _ = g ^ (2 * 2 ^ (m - 1)) := by rw [Nat.mul_comm]
      _ = g ^ (2 ^ m) := by rw [h2m]
      _ = 1 := hgpow
  have h_pow_odd : ∀ k : ℕ, (g ^ (2 ^ (m - 1))) ^ (2 * k + 1) = g ^ (2 ^ (m - 1)) := by
    intro k
    calc
      (g ^ (2 ^ (m - 1))) ^ (2 * k + 1) =
          (g ^ (2 ^ (m - 1))) ^ (2 * k) * g ^ (2 ^ (m - 1)) := by
        exact pow_succ (g ^ (2 ^ (m - 1))) (2 * k)
      _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k * g ^ (2 ^ (m - 1)) := by
        exact congrArg (fun z : A => z * g ^ (2 ^ (m - 1)))
          (pow_mul (g ^ (2 ^ (m - 1))) 2 k)
      _ = 1 ^ k * g ^ (2 ^ (m - 1)) := by rw [h2h]
      _ = g ^ (2 ^ (m - 1)) := by simp
  intro x y hx1 hx2 hy1 hy2
  rcases hg x with ⟨a, rfl⟩
  rcases hg y with ⟨b, rfl⟩
  have hxa : orderOf g ∣ 2 * a := by
    apply (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 * a)).2
    simpa [pow_mul, Nat.mul_comm] using hx2
  have hya : orderOf g ∣ 2 * b := by
    apply (orderOf_dvd_iff_pow_eq_one (x := g) (n := 2 * b)).2
    simpa [pow_mul, Nat.mul_comm] using hy2
  have hdiv_a : 2 ^ (m - 1) ∣ a := by
    rw [hord] at hxa
    rw [← h2m] at hxa
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hxa
  have hdiv_b : 2 ^ (m - 1) ∣ b := by
    rw [hord] at hya
    rw [← h2m] at hya
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hya
  rcases hdiv_a with ⟨a', rfl⟩
  rcases hdiv_b with ⟨b', rfl⟩
  have hx_ne : (g ^ (2 ^ (m - 1))) ^ a' ≠ 1 := by
    simpa [pow_mul] using hx1
  have hy_ne : (g ^ (2 ^ (m - 1))) ^ b' ≠ 1 := by
    simpa [pow_mul] using hy1
  have hodd_a : Odd a' := by
    rcases Nat.even_or_odd a' with he | ho
    · exfalso
      rcases he with ⟨k, rfl⟩
      have hkk : (g ^ (2 ^ (m - 1))) ^ (k + k) = 1 := by
        calc
          (g ^ (2 ^ (m - 1))) ^ (k + k) = (g ^ (2 ^ (m - 1))) ^ (2 * k) := by
            rw [Nat.two_mul]
          _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k := by
            exact pow_mul (g ^ (2 ^ (m - 1))) 2 k
          _ = 1 ^ k := by rw [h2h]
          _ = 1 := by simp
      exact hx_ne hkk
    · exact ho
  have hodd_b : Odd b' := by
    rcases Nat.even_or_odd b' with he | ho
    · exfalso
      rcases he with ⟨k, rfl⟩
      have hkk : (g ^ (2 ^ (m - 1))) ^ (k + k) = 1 := by
        calc
          (g ^ (2 ^ (m - 1))) ^ (k + k) = (g ^ (2 ^ (m - 1))) ^ (2 * k) := by
            rw [Nat.two_mul]
          _ = ((g ^ (2 ^ (m - 1))) ^ 2) ^ k := by
            exact pow_mul (g ^ (2 ^ (m - 1))) 2 k
          _ = 1 ^ k := by rw [h2h]
          _ = 1 := by simp
      exact hy_ne hkk
    · exact ho
  rcases hodd_a with ⟨ka, rfl⟩
  rcases hodd_b with ⟨kb, rfl⟩
  calc
    g ^ (2 ^ (m - 1) * (2 * ka + 1)) = (g ^ (2 ^ (m - 1))) ^ (2 * ka + 1) := by
      exact pow_mul g (2 ^ (m - 1)) (2 * ka + 1)
    _ = g ^ (2 ^ (m - 1)) := h_pow_odd ka
    _ = (g ^ (2 ^ (m - 1))) ^ (2 * kb + 1) := (h_pow_odd kb).symm
    _ = g ^ (2 ^ (m - 1) * (2 * kb + 1)) := by
      exact (pow_mul g (2 ^ (m - 1)) (2 * kb + 1)).symm

/-- The cyclic index-two subgroup `S0` has order `2^m`. -/
private lemma natCard_S0_eq_two_pow {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    Nat.card ↥c.S0 = 2 ^ c.m := by
  have hcardS : Nat.card ↥(c.S : Subgroup G) = 2 * 2 ^ c.m := by
    rcases c.dihedralEquiv with ⟨e⟩
    calc
      Nat.card ↥(c.S : Subgroup G) = Nat.card (DihedralGroup (2 ^ c.m)) := by
        exact Nat.card_congr e.toEquiv
      _ = 2 * 2 ^ c.m := by
        rw [Nat.card_eq_fintype_card]
        exact DihedralGroup.card
  have hindex : Nat.card ↥(c.S : Subgroup G) = 2 * Nat.card ↥c.S0 :=
    c.S_index_two
  rw [hcardS] at hindex
  exact (Nat.mul_left_cancel (by norm_num : 0 < 2) hindex).symm

/-- The four-element subgroup generated by two commuting involutions. -/
private def kleinFourOfCommutingInvolutions
    {G : Type u} [Group G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) :
    Subgroup G where
  carrier := {a * b, a, b, 1}
  one_mem' := by simp
  mul_mem' := by
    have hba : b * a = a * b := hab.eq.symm
    have ha_ab : a * (a * b) = b := by
      rw [← mul_assoc, ha, one_mul]
    have hb_ab : b * (a * b) = a := by
      rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
    have hab_a : (a * b) * a = b := by
      rw [mul_assoc, hba, ha_ab]
    have hab_b : (a * b) * b = a := by
      rw [mul_assoc, hb, mul_one]
    have hab_sq : (a * b) * (a * b) = 1 := by
      rw [← mul_assoc, hab_a, hb]
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with (rfl | rfl | rfl | rfl) <;>
      rcases hy with (rfl | rfl | rfl | rfl) <;>
      simp [ha, hb, hba, ha_ab, hb_ab, hab_a, hab_b, hab_sq]
  inv_mem' := by
    have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have hab_sq : (a * b) * (a * b) = 1 := by
      calc
        (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab.eq.symm]
        _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]
    have hab_inv : (a * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right hab_sq
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with (rfl | rfl | rfl | rfl) <;>
      simp [ha_inv, hb_inv, hab_inv]

/-- Two distinct nontrivial commuting involutions generate a Klein four
subgroup. -/
private theorem isKleinFour_kleinFourOfCommutingInvolutions
    {G : Type u} [Group G]
    (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (habne : a ≠ b) (hab : Commute a b) :
    IsKleinFour (kleinFourOfCommutingInvolutions a b ha hb hab) := by
  classical
  let V := kleinFourOfCommutingInvolutions a b ha hb hab
  have hoa : orderOf a = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ha) ha1
  have hob : orderOf b = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hb) hb1
  have habnot : a * b ∉ ({a, b, 1} : Set G) :=
    mul_notMem_of_orderOf_eq_two hoa hob habne
  constructor
  · change Nat.card V = 4
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    change ({a * b, a, b, 1} : Set G).ncard = 4
    simp [habnot, ha1, hb1, habne]
  · apply Nat.dvd_antisymm
    · apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      rcases x with ⟨x, hx⟩
      apply Subtype.ext
      change x ^ 2 = 1
      change x ∈ ({a * b, a, b, 1} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with (rfl | rfl | rfl | rfl)
      · calc
          (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
          _ = a * (a * b) * b := by rw [hab.eq.symm]
          _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]
      · simpa [pow_two] using ha
      · simpa [pow_two] using hb
      · simp
    · have haV : a ∈ V := by
        change a ∈ ({a * b, a, b, 1} : Set G)
        simp
      have hordV : orderOf (⟨a, haV⟩ : V) = 2 := by
        simpa [Subgroup.orderOf_mk] using hoa
      simpa [hordV] using
        (Monoid.order_dvd_exponent (⟨a, haV⟩ : V))

/-- Every involution of a finite group can be conjugated into a fixed Sylow
`2`-subgroup. -/
private lemma involution_conjugate_into_sylow_two
    {M : Type u} [Group M] [Finite M]
    (P : Sylow 2 M) (x : M) (hx : IsInvolution x) :
    ∃ g : M, g * x * g⁻¹ ∈ (P : Subgroup M) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxord : orderOf x = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hx.2) hx.1
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, hxord])
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hxp
  obtain ⟨g, hg⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq M (Sylow 2 M)
      inferInstance inferInstance Q P
  refine ⟨g, ?_⟩
  have hxQ : x ∈ (Q : Subgroup M) := hQ (Subgroup.mem_zpowers x)
  have hmem : g * x * g⁻¹ ∈ ((g • Q : Sylow 2 M) : Subgroup M) := by
    change (MulAut.conj g) x ∈
      (Q : Subgroup M).map (MulAut.conj g).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨x, hxQ, rfl⟩
  rw [hg] at hmem
  exact hmem

/-- A concrete rotation in the symmetric group on three letters. -/
private def permThreeRotation : Equiv.Perm (Fin 3) :=
  Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2

/-- A concrete reflection in the symmetric group on three letters. -/
private def permThreeReflection : Equiv.Perm (Fin 3) :=
  Equiv.swap (0 : Fin 3) 1

private lemma permThree_generators :
    (⊤ : Subgroup (Equiv.Perm (Fin 3))) =
      Subgroup.zpowers permThreeRotation ⊔
        Subgroup.zpowers permThreeReflection := by
  let A : Subgroup (Equiv.Perm (Fin 3)) :=
    Subgroup.zpowers permThreeRotation
  let L : Subgroup (Equiv.Perm (Fin 3)) :=
    Subgroup.zpowers permThreeRotation ⊔
      Subgroup.zpowers permThreeReflection
  have hrho : orderOf permThreeRotation = 3 :=
    orderOf_eq_prime (by decide) (by decide)
  have hsigmaNot : permThreeReflection ∉ A := by
    intro h
    have hdvd := orderOf_dvd_of_mem_zpowers h
    have hsigma : orderOf permThreeReflection = 2 :=
      orderOf_eq_prime (by decide) (by decide)
    rw [hrho, hsigma] at hdvd
    norm_num at hdvd
  have hAcard : Nat.card A = 3 := by
    dsimp [A]
    rw [Nat.card_zpowers, hrho]
  have hA_le_L : A ≤ L := by exact le_sup_left
  have h3dvd : 3 ∣ Nat.card L := by
    simpa only [hAcard] using Subgroup.card_dvd_of_le hA_le_L
  have hLd6 : Nat.card L ∣ 6 := by
    have hdvd := L.card_subgroup_dvd_card
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using hdvd
  have hLne3 : Nat.card L ≠ 3 := by
    intro hLcard
    have hAL : A = L :=
      Subgroup.eq_of_le_of_card_ge hA_le_L (by rw [hAcard, hLcard])
    apply hsigmaNot
    rw [hAL]
    exact (show Subgroup.zpowers permThreeReflection ≤ L from le_sup_right)
      (Subgroup.mem_zpowers permThreeReflection)
  have hLcard : Nat.card L = 6 := by
    obtain ⟨a, ha⟩ := h3dvd
    have hLpos : 0 < Nat.card L := Nat.card_pos
    have ha2 : a ∣ 2 := by
      apply (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).mp
      simpa [ha] using hLd6
    have hale : a ≤ 2 := Nat.le_of_dvd (by norm_num) ha2
    omega
  symm
  change L = ⊤
  apply Subgroup.eq_top_of_card_eq
  have hPermCard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  exact hLcard.trans hPermCard.symm

/-- The symmetric group on three letters is the dihedral group of order
six. -/
private theorem permThree_mulEquiv_dihedralThree :
    Nonempty (Equiv.Perm (Fin 3) ≃* DihedralGroup 3) := by
  have h := dihedral_of_generators_of_not_mem
    permThreeRotation permThreeReflection permThree_generators
    (by decide) (by decide)
    (by
      intro hmem
      have hdvd := orderOf_dvd_of_mem_zpowers hmem
      have hrho : orderOf permThreeRotation = 3 :=
        orderOf_eq_prime (by decide) (by decide)
      have hsigma : orderOf permThreeReflection = 2 :=
        orderOf_eq_prime (by decide) (by decide)
      rw [hrho, hsigma] at hdvd
      norm_num at hdvd)
  rw [show orderOf permThreeRotation = 3 by
    exact orderOf_eq_prime (by decide) (by decide)] at h
  exact h

/-- A normal Klein four subgroup with transitive fusion has full `S₃`
automorphism quotient when a containing Sylow `2`-subgroup is dihedral and
the ambient group has at least two involution classes.

The action on the three nonidentity core elements supplies the factor `3`.
The centralizer quotient embeds in `Aut(V) ≃ S₃`.  If its order were only
`3`, every ambient involution would lie in the centralizer, could be
conjugated into the fixed dihedral Sylow subgroup, and hence into `V`; the
fusion hypothesis would then give a single involution class. -/
private theorem quotient_centralizer_equiv_perm_three_of_kleinFour_fusion
    {M : Type u} [Group M] [Finite M]
    (N K : Subgroup M)
    (hNnormal : N.Normal)
    (hKnormal : K.Normal)
    (hN : IsKleinFour N)
    (P : Sylow 2 M)
    {m : ℕ} (hm : 1 ≤ m)
    (eP : P ≃* DihedralGroup (2 ^ m))
    (hNleP : N ≤ (P : Subgroup M))
    (hCent : Subgroup.centralizer (N : Set M) = K)
    (hfusion : ∀ x y : N, x ≠ 1 → y ≠ 1 →
      ∃ g : M, g * (x : M) * g⁻¹ = (y : M))
    (hclasses : HasAtLeastTwoInvolutionClasses M) :
    Nonempty ((M ⧸ K) ≃* Equiv.Perm (Fin 3)) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : N.Normal := hNnormal
  let : K.Normal := hKnormal
  let : IsKleinFour N := hN
  let NP : Subgroup P := N.subgroupOf P
  let eNNP : N ≃* NP := (Subgroup.subgroupOfEquivOfLe hNleP).symm
  have hNP : IsKleinFour NP := {
    card_four := (Nat.card_congr eNNP.toEquiv).symm.trans hN.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eNNP).symm.trans hN.exponent_two
  }
  have hCentNPle : Subgroup.centralizer (NP : Set P) ≤ NP :=
    centralizer_kleinFour_le_of_dihedral_mulEquiv hm eP NP hNP
  rcases quotient_centralizer_mulAut_embedding N with ⟨φ, hφ⟩
  let eQ : (M ⧸ K) ≃* (M ⧸ Subgroup.centralizer (N : Set M)) :=
    QuotientGroup.quotientMulEquivOfEq hCent.symm
  let φK : (M ⧸ K) →* MulAut N := φ.comp eQ.toMonoidHom
  have hφK : Function.Injective φK := hφ.comp eQ.injective
  rcases gw_prop9_aut_kleinFour_is_S3 hN with ⟨eAut⟩
  let ψ : (M ⧸ K) →* Equiv.Perm (Fin 3) :=
    eAut.toMonoidHom.comp φK
  have hψ : Function.Injective ψ := eAut.injective.comp hφK
  have hqdvd : Nat.card (M ⧸ K) ∣ 6 := by
    have hdvd := Subgroup.card_dvd_of_injective ψ hψ
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using hdvd
  have : Nontrivial N :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hN.card_four]; norm_num)
  obtain ⟨t, ht1⟩ := exists_ne (1 : N)
  let : MulDistribMulAction M N :=
    MulDistribMulAction.compHom N (MulAut.conjNormal (H := N))
  let T : Set N := {x | x ≠ 1}
  have horbit : MulAction.orbit M t = T := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      change g • t ≠ 1
      change MulAut.conjNormal g t ≠ 1
      exact (MulEquiv.map_ne_one_iff (MulAut.conjNormal g)).2 ht1
    · intro hx
      change x ≠ 1 at hx
      obtain ⟨g, hg⟩ := hfusion t x ht1 hx
      refine ⟨g, ?_⟩
      change MulAut.conjNormal g t = x
      apply Subtype.ext
      simpa using hg
  have hTcard : T.ncard = 3 := by
    have hset : T = Set.univ \ {1} := by
      ext x
      simp [T]
    rw [hset, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : N))]
    simpa [hN.card_four]
  let St : Subgroup M := MulAction.stabilizer M t
  let Ct : Subgroup M := Subgroup.centralizer ({(t : M)} : Set M)
  have hStCt : St = Ct := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hg
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxt : x = (t : M) := by simpa using hx
      subst x
      change MulAut.conjNormal g t = t at hg
      have hconj := congrArg Subtype.val hg
      rw [MulAut.conjNormal_apply] at hconj
      exact (eq_mul_of_mul_inv_eq hconj).symm
    · intro hg
      rw [Subgroup.mem_centralizer_iff] at hg
      change MulAut.conjNormal g t = t
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hcomm := hg (t : M) (by simp)
      exact mul_inv_eq_of_eq_mul hcomm.symm
  have hCtindex : Ct.index = 3 := by
    rw [← hStCt]
    exact (MulAction.index_stabilizer M t).trans (horbit ▸ hTcard)
  have hKleCt : K ≤ Ct := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxt : x = (t : M) := by simpa using hx
    subst x
    have hkCent : k ∈ Subgroup.centralizer (N : Set M) := by
      rw [hCent]
      exact hk
    exact (Subgroup.mem_centralizer_iff.mp hkCent) (t : M) t.2
  have h3dvdIndex : 3 ∣ K.index := by
    have hrel := Subgroup.relIndex_mul_index hKleCt
    rw [hCtindex] at hrel
    exact ⟨K.relIndex Ct, by omega⟩
  have h3dvd : 3 ∣ Nat.card (M ⧸ K) := by
    simpa [Subgroup.index_eq_card] using h3dvdIndex
  have hqpos : 0 < Nat.card (M ⧸ K) := Nat.card_pos
  have hqle : Nat.card (M ⧸ K) ≤ 6 :=
    Nat.le_of_dvd (by norm_num) hqdvd
  have hqne1 : Nat.card (M ⧸ K) ≠ 1 := by
    intro h
    norm_num [h] at h3dvd
  have hqne2 : Nat.card (M ⧸ K) ≠ 2 := by
    intro h
    norm_num [h] at h3dvd
  have hqne4 : Nat.card (M ⧸ K) ≠ 4 := by
    intro h
    norm_num [h] at hqdvd
  have hqne5 : Nat.card (M ⧸ K) ≠ 5 := by
    intro h
    norm_num [h] at hqdvd
  have hcases : Nat.card (M ⧸ K) = 3 ∨ Nat.card (M ⧸ K) = 6 := by
    omega
  have hq6 : Nat.card (M ⧸ K) = 6 := by
    rcases hcases with hq3 | hq6
    · exfalso
      rcases hclasses with ⟨x, y, hxInv, hyInv, hxy⟩
      apply hxy
      let q : M →* M ⧸ K := QuotientGroup.mk' K
      have involution_mem_K : ∀ z : M, IsInvolution z → z ∈ K := by
        intro z hz
        let : Fintype (M ⧸ K) := Fintype.ofFinite (M ⧸ K)
        have hqpow : (q z) ^ 2 = 1 := by
          rw [← map_pow, hz.2, map_one]
        have hord2 : orderOf (q z) ∣ 2 :=
          orderOf_dvd_of_pow_eq_one hqpow
        have hord3 : orderOf (q z) ∣ 3 := by
          rw [← hq3]
          simpa [Nat.card_eq_fintype_card] using
            (orderOf_dvd_card (G := M ⧸ K) (x := q z))
        have hord1 : orderOf (q z) = 1 := by
          apply Nat.dvd_one.mp
          simpa using Nat.dvd_gcd hord2 hord3
        have hqz : q z = 1 := orderOf_eq_one_iff.mp hord1
        exact (QuotientGroup.eq_one_iff (N := K) z).mp hqz
      have hxK : x ∈ K := involution_mem_K x hxInv
      have hyK : y ∈ K := involution_mem_K y hyInv
      obtain ⟨gx, hgxP⟩ := involution_conjugate_into_sylow_two P x hxInv
      obtain ⟨gy, hgyP⟩ := involution_conjugate_into_sylow_two P y hyInv
      have hgxK : gx * x * gx⁻¹ ∈ K :=
        hKnormal.conj_mem x hxK gx
      have hgyK : gy * y * gy⁻¹ ∈ K :=
        hKnormal.conj_mem y hyK gy
      let zxP : P := ⟨gx * x * gx⁻¹, hgxP⟩
      let zyP : P := ⟨gy * y * gy⁻¹, hgyP⟩
      have hzxCent : zxP ∈ Subgroup.centralizer (NP : Set P) := by
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        apply Subtype.ext
        have hzxK : (zxP : M) ∈ Subgroup.centralizer (N : Set M) := by
          rw [hCent]
          exact hgxK
        exact (Subgroup.mem_centralizer_iff.mp hzxK) (n : M) hn
      have hzyCent : zyP ∈ Subgroup.centralizer (NP : Set P) := by
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        apply Subtype.ext
        have hzyK : (zyP : M) ∈ Subgroup.centralizer (N : Set M) := by
          rw [hCent]
          exact hgyK
        exact (Subgroup.mem_centralizer_iff.mp hzyK) (n : M) hn
      have hzxNP : zxP ∈ NP := hCentNPle hzxCent
      have hzyNP : zyP ∈ NP := hCentNPle hzyCent
      let zxN : N := ⟨gx * x * gx⁻¹, hzxNP⟩
      let zyN : N := ⟨gy * y * gy⁻¹, hzyNP⟩
      have hzx1 : zxN ≠ 1 := by
        intro hz
        apply hxInv.1
        have hzval : gx * x * gx⁻¹ = 1 := congrArg Subtype.val hz
        calc
          x = gx⁻¹ * (gx * x * gx⁻¹) * gx := by group
          _ = 1 := by rw [hzval]; simp
      have hzy1 : zyN ≠ 1 := by
        intro hz
        apply hyInv.1
        have hzval : gy * y * gy⁻¹ = 1 := congrArg Subtype.val hz
        calc
          y = gy⁻¹ * (gy * y * gy⁻¹) * gy := by group
          _ = 1 := by rw [hzval]; simp
      obtain ⟨g, hg⟩ := hfusion zxN zyN hzx1 hzy1
      refine ⟨gy⁻¹ * g * gx, ?_⟩
      calc
        (gy⁻¹ * g * gx) * x * (gy⁻¹ * g * gx)⁻¹ =
            gy⁻¹ * (g * (gx * x * gx⁻¹) * g⁻¹) * gy := by group
        _ = gy⁻¹ * (gy * y * gy⁻¹) * gy := by
          simpa [zxN, zyN] using hg
        _ = y := by group
    · exact hq6
  have hPermCard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hcardψ : Nat.card (M ⧸ K) = Nat.card (Equiv.Perm (Fin 3)) :=
    hq6.trans hPermCard.symm
  have hψbij : Function.Bijective ψ :=
    (Nat.bijective_iff_injective_and_card ψ).2 ⟨hψ, hcardψ⟩
  exact ⟨MulEquiv.ofBijective ψ hψbij⟩

/-- `t` is centralized by `S`: `t` is the unique involution of the cyclic
index-two subgroup `S0` of the dihedral group `S`. -/
private lemma t_mem_center_S {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    ∀ s : G, s ∈ (c.S : Subgroup G) → c.t * s * c.t⁻¹ = s := by
  classical
  let S' : Subgroup G := c.S
  let S0' : Subgroup (↥S') := c.S0.subgroupOf S'
  have hmap : (c.S0.subgroupOf (c.S : Subgroup G)).map (c.S : Subgroup G).subtype = c.S0 := by
    ext y
    constructor
    · intro hy
      rcases (Subgroup.mem_map.mp hy) with ⟨x, hx, rfl⟩
      exact (Subgroup.mem_subgroupOf.mp hx)
    · intro hy
      refine Subgroup.mem_map.mpr ⟨⟨y, c.S0_le_S hy⟩, ?_⟩
      constructor
      · exact (Subgroup.mem_subgroupOf (H := c.S0) (K := (c.S : Subgroup G))
          (h := ⟨y, c.S0_le_S hy⟩)).mpr hy
      · rfl
  have hS0'_index : (c.S0.subgroupOf (c.S : Subgroup G)).index = 2 := by
    have h1 := Subgroup.card_mul_index (c.S0.subgroupOf (c.S : Subgroup G))
    have hc : Nat.card ↥(c.S0.subgroupOf (c.S : Subgroup G)) = Nat.card ↥c.S0 := by
      have hcs := Subgroup.card_subtype (c.S : Subgroup G) (c.S0.subgroupOf (c.S : Subgroup G))
      rw [hmap] at hcs
      exact hcs.symm
    rw [hc, c.S_index_two] at h1
    have hpos : 0 < Nat.card ↥c.S0 := Nat.card_pos
    exact Nat.mul_right_cancel hpos (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h1)
  have hS0'_normal : S0'.Normal := by
    apply Subgroup.normal_of_index_eq_two
    exact hS0'_index
  have huniq : ∀ x y : ↥c.S0, x ≠ 1 → x ^ 2 = 1 → y ≠ 1 → y ^ 2 = 1 → x = y :=
    unique_involution_of_cyclic_two_group_t26 c.S0_cyclic c.one_le_m
      (natCard_S0_eq_two_pow c)
  intro s hs
  let sS : ↥S' := ⟨s, hs⟩
  let tS : ↥S' := ⟨c.t, c.S0_le_S c.t_mem_S0⟩
  have htS' : tS ∈ S0' := by
    simpa [S0', S', tS, Subgroup.mem_subgroupOf] using c.t_mem_S0
  have hconj : sS * tS * sS⁻¹ ∈ S0' := hS0'_normal.conj_mem tS htS' sS
  let x : ↥c.S0 := ⟨s * c.t * s⁻¹, by
    simpa [sS, tS, S0', S', Subgroup.mem_subgroupOf] using hconj⟩
  let y : ↥c.S0 := ⟨c.t, c.t_mem_S0⟩
  have hx1 : x ≠ 1 := by
    intro hx
    apply c.t_involution.1
    have hval : s * c.t * s⁻¹ = 1 := by
      simpa [x] using congrArg Subtype.val hx
    calc
      c.t = s⁻¹ * (s * c.t * s⁻¹) * s := by group
      _ = s⁻¹ * 1 * s := by rw [hval]
      _ = 1 := by simp
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    have ht2 : c.t * c.t = 1 := by simpa [pow_two] using c.t_involution.2
    calc
      (s * c.t * s⁻¹) ^ 2 = (s * c.t * s⁻¹) * (s * c.t * s⁻¹) := by rw [pow_two]
      _ = s * c.t * (s⁻¹ * s) * c.t * s⁻¹ := by group
      _ = s * (c.t * c.t) * s⁻¹ := by group
      _ = s * 1 * s⁻¹ := by rw [ht2]
      _ = 1 := by simp
  have hy1 : y ≠ 1 := by
    intro hy
    apply c.t_involution.1
    simpa [y] using congrArg Subtype.val hy
  have hy2 : y ^ 2 = 1 := by
    apply Subtype.ext
    simpa [y, pow_two] using c.t_involution.2
  have heq : x = y := huniq x y hx1 hx2 hy1 hy2
  have hval : s * c.t * s⁻¹ = c.t := by
    simpa [x, y] using congrArg Subtype.val heq
  have hcomm : c.t * s = s * c.t := by
    calc
      c.t * s = s * c.t * s⁻¹ * s := by rw [hval]
      _ = s * c.t := by group
  calc
    c.t * s * c.t⁻¹ = (s * c.t) * c.t⁻¹ := by rw [hcomm]
    _ = s := by group

/-- `S ≤ H = C_G(t)`. -/
public lemma S_le_H {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : (c.S : Subgroup G) ≤ c.H := by
  intro s hs
  have ht : c.t * s * c.t⁻¹ = s := t_mem_center_S c s hs
  rw [c.H_eq_centralizer]
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzt : z = c.t := by simpa using hz
  rw [hzt]
  calc
    c.t * s = (c.t * s * c.t⁻¹) * c.t := by group
    _ = s * c.t := by rw [ht]

/-- `U = O(H)` is normal in `H`. -/
private lemma U_isNormalIn_H {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : IsNormalIn c.U c.H := by
  refine ⟨?_, ?_⟩
  · exact Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨p, hp, rfl⟩
    have hconj : (⟨h, hh⟩ : ↥c.H) * p * (⟨h, hh⟩ : ↥c.H)⁻¹ ∈
        pPrimeCore 2 c.H :=
      (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        p hp (⟨h, hh⟩ : ↥c.H)
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥c.H) * p * (⟨h, hh⟩ : ↥c.H)⁻¹, hconj, by simp⟩

/-- Since `H = S·U`, the quotient `H/U` is a `2`-group.  Hence every
odd-order subgroup of `H` lies in `U`. -/
private lemma odd_order_subgroup_le_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    {X : Subgroup G} (hXH : X ≤ c.H)
    (hXodd : Nat.Coprime 2 (Nat.card X)) : X ≤ c.U := by
  classical
  have hUH : c.U ≤ c.H := (U_isNormalIn_H c).1
  have hU_normal : (c.U.subgroupOf c.H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (le_normalizer_of_isNormalIn (U_isNormalIn_H c))
  let U' : Subgroup (↥c.H) := c.U.subgroupOf c.H
  let : U'.Normal := hU_normal
  let S' : Subgroup (↥c.H) := (c.S : Subgroup G).subgroupOf c.H
  let q : ↥c.H →* ↥c.H ⧸ U' := QuotientGroup.mk' U'
  have hSH : (c.S : Subgroup G) ≤ c.H := S_le_H c
  have hHsup : (c.S : Subgroup G) ⊔ c.U = c.H :=
    fact_2_preamble_H_eq_SU_proved hmin c
  have hS_norm_U : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
    hSH.trans (le_normalizer_of_isNormalIn (U_isNormalIn_H c))
  have htop' : S' ⊔ U' = ⊤ := by
    refine le_antisymm le_top ?_
    intro x hx
    have hxSU : (x : G) ∈ (c.S : Subgroup G) ⊔ c.U := by
      rw [hHsup]
      exact x.2
    have hxprod : (x : G) ∈ ((c.S : Subgroup G) : Set G) * (c.U : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right
        (H := c.S) (N := c.U) hS_norm_U]
      exact hxSU
    rcases hxprod with ⟨s, hs, u, hu, hsmu⟩
    have hsS' : (⟨s, hSH hs⟩ : ↥c.H) ∈ S' :=
      (Subgroup.mem_subgroupOf).2 hs
    have huU' : (⟨u, hUH hu⟩ : ↥c.H) ∈ U' :=
      (Subgroup.mem_subgroupOf).2 hu
    have hxeq : x = (⟨s, hSH hs⟩ : ↥c.H) * (⟨u, hUH hu⟩ : ↥c.H) := by
      apply Subtype.ext
      exact hsmu.symm
    rw [hxeq]
    exact Subgroup.mul_mem_sup hsS' huU'
  have hS2 : IsPGroup 2 ↥(c.S : Subgroup G) := c.S.isPGroup'
  have hf : IsPGroup 2 (↥c.H ⧸ U') := by
    let f : ↥(c.S : Subgroup G) →* ↥c.H ⧸ U' :=
      q.comp (Subgroup.inclusion hSH)
    have hf_surj : Function.Surjective f := by
      intro y
      rcases QuotientGroup.mk'_surjective U' y with ⟨h, rfl⟩
      have hhSU : h ∈ S' ⊔ U' := by
        simpa [htop'] using (Subgroup.mem_top h)
      have hhprod : (h : ↥c.H) ∈ (S' : Set (↥c.H)) * (U' : Set (↥c.H)) := by
        rw [← Subgroup.mul_normal (H := S') (N := U')]
        exact hhSU
      rcases hhprod with ⟨s, hsS', u, huU', hsmu⟩
      have hqu1 : q u = 1 :=
        (QuotientGroup.eq_one_iff (N := U') u).2 huU'
      have hqs : q (s : ↥c.H) = q h := by
        calc
          q (s : ↥c.H) = q (s : ↥c.H) * 1 := by simp
          _ = q (s : ↥c.H) * q u := by rw [hqu1]
          _ = q ((s : ↥c.H) * u) := by rw [map_mul]
          _ = q h := by exact congrArg q hsmu
      have hsS : (s : G) ∈ (c.S : Subgroup G) := by
        simpa [S', Subgroup.mem_subgroupOf] using hsS'
      refine ⟨⟨(s : G), hsS⟩, ?_⟩
      change q (s : ↥c.H) = QuotientGroup.mk' U' h
      simpa [q, f] using hqs
    exact IsPGroup.of_surjective hS2 f hf_surj
  let X' : Subgroup (↥c.H) := X.subgroupOf c.H
  have hX2 : IsPGroup 2 ↥(X'.map q) := IsPGroup.to_subgroup hf (X'.map q)
  have hcopX' : Nat.Coprime 2 (Nat.card ↥(X'.map q)) := by
    have hdvd : Nat.card ↥(X'.map q) ∣ Nat.card X := by
      exact (Subgroup.card_map_dvd X' q).trans
        (by rw [natCard_subgroupOf_eq X c.H hXH])
    exact Nat.Coprime.of_dvd_right hdvd hXodd
  have hX'map_bot : X'.map q = ⊥ :=
    section8_eq_bot_of_isPGroup_of_coprime (H := X'.map q) hX2 hcopX'
  intro x hx
  have hxX' : (⟨x, hXH hx⟩ : ↥c.H) ∈ X' := by
    simpa [X', Subgroup.mem_subgroupOf] using hx
  have hqx1 : q ⟨x, hXH hx⟩ = 1 := by
    have hmem : q ⟨x, hXH hx⟩ ∈ X'.map q :=
      Subgroup.mem_map.mpr ⟨⟨x, hXH hx⟩, hxX', rfl⟩
    have hbot : q ⟨x, hXH hx⟩ ∈ (⊥ : Subgroup (↥c.H ⧸ U')) := by
      simpa [hX'map_bot] using hmem
    exact Subgroup.mem_bot.mp hbot
  have hxU' : (⟨x, hXH hx⟩ : ↥c.H) ∈ U' :=
    (QuotientGroup.eq_one_iff (N := U') ⟨x, hXH hx⟩).1 hqx1
  exact Subgroup.mem_subgroupOf.mp hxU'

/-- Membership in an explicitly conjugated subgroup. -/
private lemma mem_conjugateSubgroup_iff {G : Type u} [Group G]
    (H : Subgroup G) (g x : G) :
    x ∈ conjugateSubgroup H g ↔ ∃ h ∈ H, x = g * h * g⁻¹ := by
  constructor
  · intro hx
    rcases (show x ∈ H.map (MulAut.conj g).toMonoidHom from by
      simpa [conjugateSubgroup] using hx) with ⟨h, hh, hval⟩
    refine ⟨h, hh, ?_⟩
    simpa [MulAut.conj_apply] using hval.symm
  · rintro ⟨h, hh, hx⟩
    rw [conjugateSubgroup, Subgroup.mem_map]
    refine ⟨h, hh, ?_⟩
    simpa [MulAut.conj_apply] using hx.symm

/-- Conjugation preserves subgroup cardinality. -/
private lemma natCard_conjugateSubgroup {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (g : G) :
    Nat.card (conjugateSubgroup H g) = Nat.card H := by
  unfold conjugateSubgroup
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- `O₂(N)` is normal in `N`, after mapping the internal `pCore` back to
the ambient group. -/
private lemma twoCoreOf_isNormalIn {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) : IsNormalIn (twoCoreOf N) N := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
    rw [← hfx]
    change (f : G) ∈ N
    simp
  · intro h hh k hk
    rcases (Subgroup.mem_map).1 hk with ⟨f, hf, hfk⟩
    rw [← hfk]
    have hconj : (⟨h, hh⟩ : ↥N) * f * (⟨h, hh⟩ : ↥N)⁻¹ ∈ pCore 2 N :=
      (pCore_normal (p := 2) (G := N)).conj_mem
        f hf (⟨h, hh⟩ : ↥N)
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥N) * f * (⟨h, hh⟩ : ↥N)⁻¹, hconj, by simp⟩

/-- A nontrivial `2`-core contains an involution. -/
private lemma exists_involution_mem_twoCore_of_ne_bot
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) (hN : twoCoreOf N ≠ ⊥) :
    ∃ z : G, IsInvolution z ∧ z ∈ twoCoreOf N := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNp : IsPGroup 2 (twoCoreOf N) := by
    change IsPGroup 2 (qCoreOf N 2)
    exact qCoreOf_isPGroup N 2
  let : Nontrivial (twoCoreOf N) :=
    (twoCoreOf N).nontrivial_iff_ne_bot.mpr hN
  rcases hNp.nontrivial_iff_card.mp (inferInstance : Nontrivial (twoCoreOf N)) with
    ⟨n, hn, hcard⟩
  have h2dvd : 2 ∣ Nat.card (twoCoreOf N) := by
    refine ⟨2 ^ (n - 1), ?_⟩
    rw [hcard, ← pow_succ']
    congr 1
    omega
  rcases exists_prime_orderOf_dvd_card' (G := twoCoreOf N) 2 h2dvd with
    ⟨z, hzord⟩
  have hzordG : orderOf (z : G) = 2 :=
    (Subgroup.orderOf_coe z).trans hzord
  have hzne : (z : G) ≠ 1 := by
    intro hz1
    have : orderOf (z : G) = 1 := orderOf_eq_one_iff.mpr hz1
    omega
  have hz2 : (z : G) ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by simp [hzordG])
  exact ⟨z, ⟨hzne, hz2⟩, z.2⟩

/-! ## Provable branch-one infrastructure

These facts do not need Lemma 2.1 and are the first formal pieces of the
`O₂(Ĥ) ≠ 1` branch:

* `twoCoreOf_le_S`: `O₂(Ĥ) ≤ S`, because `O₂(Ĥ)` is a normal `2`-subgroup
  of `Ĥ` and `S` is a Sylow `2`-subgroup of `Ĥ`.
* `twoCoreOf_centralizes_oddCoreOf`: distinct-prime cores of `Ĥ` commute
  (Bender [1, §1] / PCore centralizer API).
* `S_inter_centralizer_U_le_twoCoreOf_of_Hhat_eq_H`: once `Ĥ = H`, the
  subgroup `C_S(U)` is normal in `H = S·U`, hence lies in `O₂(H)`.
-/

/-- `O₂(Ĥ) ≤ S`. -/
private lemma twoCoreOf_le_S {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    twoCoreOf c.Hhat ≤ (c.S : Subgroup G) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSleHhat : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let S' : Sylow 2 (↥c.Hhat) := (c.S).subtype hSleHhat
  let T : Subgroup (↥c.Hhat) := (twoCoreOf c.Hhat).subgroupOf c.Hhat
  have hTleHhat : twoCoreOf c.Hhat ≤ c.Hhat := qCoreOf_le c.Hhat 2
  have hTnormal : T.Normal := by
    dsimp [T]
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      (H := c.Hhat) (N := twoCoreOf c.Hhat)
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in c.Hhat 2))
  have hTp0 : IsPGroup 2 (twoCoreOf c.Hhat) := by
    change IsPGroup 2 (qCoreOf c.Hhat 2)
    exact qCoreOf_isPGroup c.Hhat 2
  have hTp : IsPGroup 2 T :=
    hTp0.of_equiv (Subgroup.subgroupOfEquivOfLe hTleHhat).symm
  have hTleS' : T ≤ (S' : Subgroup (↥c.Hhat)) :=
    hTp.le_sylow_of_normal S'
  have hTmap : T.map c.Hhat.subtype = twoCoreOf c.Hhat := by
    dsimp [T]
    exact Subgroup.map_subgroupOf_eq_of_le hTleHhat
  intro x hx
  have hxTmap : x ∈ T.map c.Hhat.subtype := by
    simpa [hTmap] using hx
  rcases (Subgroup.mem_map).1 hxTmap with ⟨y, hyT, rfl⟩
  exact (Subgroup.mem_subgroupOf).mp (hTleS' hyT)

/-- `O₂(Ĥ) ≤ C_G(O(Ĥ))`: the `2`-core and the odd core of the same group
commute elementwise. -/
private lemma oddCoreOf_le_centralizer_twoCoreOf {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) :
    oddCoreOf H ≤ Subgroup.centralizer (twoCoreOf H : Set G) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup 2 (pCore 2 (↥H)) := pCore_isPGroup (G := ↥H) (p := 2)
  obtain ⟨n, hcardB⟩ := hBp.exists_card_eq
  have hp_not_dvd_A : ¬ 2 ∣ Nat.card (pPrimeCore 2 (↥H)) := by
    exact (Fact.out : Nat.Prime 2).coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (G := ↥H) (p := 2))
  have hAcopB : Nat.Coprime (Nat.card (pPrimeCore 2 (↥H)))
      (Nat.card (pCore 2 (↥H))) := by
    rw [hcardB]
    exact (Fact.out : Nat.Prime 2).coprime_pow_of_not_dvd (m := n) hp_not_dvd_A
  have hdisj : Disjoint (pPrimeCore 2 (↥H)) (pCore 2 (↥H)) := by
    exact Subgroup.disjoint_of_coprime_natCard hAcopB
  have hcomm_bot : ⁅pPrimeCore 2 (↥H), pCore 2 (↥H)⁆ = ⊥ := by
    apply bot_unique
    calc
      ⁅pPrimeCore 2 (↥H), pCore 2 (↥H)⁆ ≤
          (pPrimeCore 2 (↥H)) ⊓ pCore 2 (↥H) := by
        exact Subgroup.commutator_le_inf
          (H₁ := pPrimeCore 2 (↥H)) (H₂ := pCore 2 (↥H))
      _ = ⊥ := hdisj.eq_bot
  have hcentralH :
      pPrimeCore 2 (↥H) ≤
        Subgroup.centralizer (pCore 2 (↥H) : Set (↥H)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := pPrimeCore 2 (↥H)) (H₂ := pCore 2 (↥H))).1 hcomm_bot
  intro x hx
  rcases (Subgroup.mem_map).1 hx with ⟨x₀, hx₀, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases (Subgroup.mem_map).1 hy with ⟨y₀, hy₀, rfl⟩
  exact congrArg Subtype.val
    ((Subgroup.mem_centralizer_iff.mp (hcentralH hx₀)) y₀ hy₀)

private lemma twoCoreOf_centralizes_oddCoreOf {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) :
    twoCoreOf H ≤ Subgroup.centralizer (oddCoreOf H : Set G) := by
  have h : oddCoreOf H ≤ Subgroup.centralizer (twoCoreOf H : Set G) :=
    oddCoreOf_le_centralizer_twoCoreOf H
  have hcomm : ⁅oddCoreOf H, twoCoreOf H⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := oddCoreOf H) (H₂ := twoCoreOf H)).mpr h
  have hcomm' : ⁅twoCoreOf H, oddCoreOf H⁆ = ⊥ := by
    simpa [Subgroup.commutator_comm] using hcomm
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer
    (H₁ := twoCoreOf H) (H₂ := oddCoreOf H)).mp hcomm'

/-- The local odd core `U = O(H)` centralizes `O₂(Ĥ)` already in source
order.  Both subgroups normalize one another (`O₂(Ĥ) ≤ S ≤ H ≤ Ĥ`), and
their orders are coprime. -/
private lemma twoCoreOf_centralizes_U {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    twoCoreOf c.Hhat ≤ Subgroup.centralizer (c.U : Set G) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNleH : twoCoreOf c.Hhat ≤ c.H :=
    (twoCoreOf_le_S c).trans (S_le_H c)
  have hUleHhat : c.U ≤ c.Hhat :=
    (U_isNormalIn_H c).1.trans c.H_le_Hhat
  have hU_norm_N : c.U ≤ Subgroup.normalizer (twoCoreOf c.Hhat : Set G) :=
    hUleHhat.trans (le_normalizer_of_isNormalIn (twoCoreOf_isNormalIn c.Hhat))
  have hN_norm_U : twoCoreOf c.Hhat ≤ Subgroup.normalizer (c.U : Set G) :=
    hNleH.trans (le_normalizer_of_isNormalIn (U_isNormalIn_H c))
  have hcommN : ⁅twoCoreOf c.Hhat, c.U⁆ ≤ twoCoreOf c.Hhat :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hU_norm_N
  have hcommU : ⁅twoCoreOf c.Hhat, c.U⁆ ≤ c.U :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp hN_norm_U
  have hNp : IsPGroup 2 (twoCoreOf c.Hhat) := by
    change IsPGroup 2 (qCoreOf c.Hhat 2)
    exact qCoreOf_isPGroup c.Hhat 2
  obtain ⟨n, hcardN⟩ := hNp.exists_card_eq
  have hUodd : Nat.Coprime 2 (Nat.card (↥c.U)) := by
    unfold CentralizerSetup.U oddCoreOf
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have h2_not_dvd_U : ¬ 2 ∣ Nat.card (↥c.U) :=
    Nat.prime_two.coprime_iff_not_dvd.mp hUodd
  have hUcopN : Nat.Coprime (Nat.card (↥c.U))
      (Nat.card (↥(twoCoreOf c.Hhat))) := by
    rw [hcardN]
    exact Nat.prime_two.coprime_pow_of_not_dvd (m := n) h2_not_dvd_U
  have hdisj : Disjoint (twoCoreOf c.Hhat) c.U :=
    Subgroup.disjoint_of_coprime_natCard hUcopN.symm
  have hcomm : ⁅twoCoreOf c.Hhat, c.U⁆ = ⊥ := by
    apply le_antisymm
    · exact (le_inf hcommN hcommU).trans (by simpa using hdisj.eq_bot.le)
    · exact bot_le
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer
    (H₁ := twoCoreOf c.Hhat) (H₂ := c.U)).mp hcomm

/-- Any conjugator carrying an element of `C_G(U)` to `t` normalizes `U`.
The conjugated copy of `U` lies in `C_G(t)=H`, and its odd order then
forces it back into `U`. -/
private lemma conjugator_of_U_centralizing_element_mem_normalizer_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    {x a : G}
    (hxC : x ∈ Subgroup.centralizer (c.U : Set G))
    (haxt : a * x * a⁻¹ = c.t) :
    a ∈ Subgroup.normalizer (c.U : Set G) := by
  classical
  have hUodd : Nat.Coprime 2 (Nat.card (↑c.U)) := by
    unfold CentralizerSetup.U oddCoreOf
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hUaH : conjugateSubgroup c.U a ≤ c.H := by
    intro x hx
    rcases (mem_conjugateSubgroup_iff c.U a x).mp hx with ⟨u, hu, rfl⟩
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff]
    intro y hy
    have hyt : y = c.t := by simpa using hy
    rw [hyt, ← haxt]
    have hxu : x * u = u * x :=
      ((Subgroup.mem_centralizer_iff.mp hxC) u hu).symm
    calc
      (a * x * a⁻¹) * (a * u * a⁻¹) = a * (x * u) * a⁻¹ := by group
      _ = a * (u * x) * a⁻¹ := by rw [hxu]
      _ = (a * u * a⁻¹) * (a * x * a⁻¹) := by group
  have hUaOdd : Nat.Coprime 2 (Nat.card (↑(conjugateSubgroup c.U a))) := by
    rw [natCard_conjugateSubgroup]
    exact hUodd
  have hUaLeU : conjugateSubgroup c.U a ≤ c.U :=
    odd_order_subgroup_le_U hmin c hUaH hUaOdd
  have hUaEqU : conjugateSubgroup c.U a = c.U := by
    apply Subgroup.eq_of_le_of_card_ge hUaLeU
    rw [natCard_conjugateSubgroup]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [conjugateSubgroup] using hUaEqU

/-- Any conjugator carrying an involution of `O₂(Ĥ)` to `t` normalizes
`U`.  This specializes the centralizer calculation using
`[O₂(Ĥ),U]=1`. -/
private lemma conjugator_of_twoCore_involution_mem_normalizer_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    {z a : G}
    (hzN : z ∈ twoCoreOf c.Hhat)
    (hazt : a * z * a⁻¹ = c.t) :
    a ∈ Subgroup.normalizer (c.U : Set G) := by
  exact conjugator_of_U_centralizing_element_mem_normalizer_U hmin c
    (twoCoreOf_centralizes_U c hzN) hazt

/-- In the nontrivial-`O₂(Ĥ)` branch, every element of `Ĥ` normalizes
`U`.  Choose an involution `z ∈ O₂(Ĥ)` and conjugate it to `t`.  The
conjugator sends `U` into `C_G(t) = H`, where odd-order subgroups lie in
`U`, so it normalizes `U`.  The same argument applied after any `g ∈ Ĥ`
shows `U^g ≤ U`; equality follows from cardinality. -/
private lemma branch_one_Hhat_le_normalizer_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat ≠ ⊥) :
    c.Hhat ≤ Subgroup.normalizer (c.U : Set G) := by
  classical
  obtain ⟨z, hzInv, hzN⟩ :=
    exists_involution_mem_twoCore_of_ne_bot c.Hhat hO2
  obtain ⟨a, hazt⟩ :=
    fact_2_preamble_involutions_conjugate_proved hmin z c.t hzInv c.t_involution
  have haNorm : a ∈ Subgroup.normalizer (c.U : Set G) :=
    conjugator_of_twoCore_involution_mem_normalizer_U hmin c hzN hazt
  have hUodd : Nat.Coprime 2 (Nat.card (↑c.U)) := by
    unfold CentralizerSetup.U oddCoreOf
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  intro g hg
  have hXH : conjugateSubgroup (conjugateSubgroup c.U g) a ≤ c.H := by
    intro x hx
    rcases (mem_conjugateSubgroup_iff (conjugateSubgroup c.U g) a x).mp hx with
      ⟨v, hv, rfl⟩
    rcases (mem_conjugateSubgroup_iff c.U g v).mp hv with ⟨u, hu, rfl⟩
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff]
    intro y hy
    have hyt : y = c.t := by simpa using hy
    rw [hyt, ← hazt]
    have hzConj : g⁻¹ * z * g ∈ twoCoreOf c.Hhat := by
      simpa using (twoCoreOf_isNormalIn c.Hhat).2 g⁻¹
        (c.Hhat.inv_mem hg) z hzN
    have hzgu : (g⁻¹ * z * g) * u = u * (g⁻¹ * z * g) :=
      ((Subgroup.mem_centralizer_iff.mp
        (twoCoreOf_centralizes_U c hzConj)) u hu).symm
    calc
      (a * z * a⁻¹) * (a * (g * u * g⁻¹) * a⁻¹) =
          a * (g * ((g⁻¹ * z * g) * u) * g⁻¹) * a⁻¹ := by group
      _ = a * (g * (u * (g⁻¹ * z * g)) * g⁻¹) * a⁻¹ := by rw [hzgu]
      _ = (a * (g * u * g⁻¹) * a⁻¹) * (a * z * a⁻¹) := by group
  have hXOdd : Nat.Coprime 2
      (Nat.card (↑(conjugateSubgroup (conjugateSubgroup c.U g) a))) := by
    rw [natCard_conjugateSubgroup, natCard_conjugateSubgroup]
    exact hUodd
  have hXLeU : conjugateSubgroup (conjugateSubgroup c.U g) a ≤ c.U :=
    odd_order_subgroup_le_U hmin c hXH hXOdd
  have hUgLeU : conjugateSubgroup c.U g ≤ c.U := by
    intro v hv
    have hav : a * v * a⁻¹ ∈
        conjugateSubgroup (conjugateSubgroup c.U g) a :=
      (mem_conjugateSubgroup_iff (conjugateSubgroup c.U g) a
        (a * v * a⁻¹)).mpr ⟨v, hv, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp haNorm v).mpr (hXLeU hav)
  have hUgEqU : conjugateSubgroup c.U g = c.U := by
    apply Subgroup.eq_of_le_of_card_ge hUgLeU
    rw [natCard_conjugateSubgroup]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [conjugateSubgroup] using hUgEqU

/-- The sole use of `U ≠ 1` in the normalizer argument: simplicity makes
`N_G(U)` proper, so maximality upgrades `Ĥ ≤ N_G(U)` to equality. -/
private lemma branch_one_normalizer_U_eq_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat ≠ ⊥)
    (hUne : c.U ≠ ⊥) :
    Subgroup.normalizer (c.U : Set G) = c.Hhat := by
  have hle : c.Hhat ≤ Subgroup.normalizer (c.U : Set G) :=
    branch_one_Hhat_le_normalizer_U hmin c hO2
  apply (c.Hhat_maximal.ne_top_iff_eq hle).mp
  intro hNtop
  have hUnormal : c.U.Normal :=
    Subgroup.normalizer_eq_top_iff.mp hNtop
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ (minimalCounterexample_isSimple hmin)
      c.U hUnormal with hUbot | hUtop
  · exact hUne hUbot
  · have hUHhat : c.U ≤ c.Hhat :=
      (U_isNormalIn_H c).1.trans c.H_le_Hhat
    rw [hUtop] at hUHhat
    exact c.Hhat_maximal.ne_top (top_unique hUHhat)

/-- After `N_G(U)=Ĥ`, all involutions of `C_S(U)` are conjugate inside
`Ĥ`: conjugate each one to `t`; the conjugators normalize `U` by the
preceding centralizer calculation. -/
private lemma branch_one_involutions_in_C_conjugate
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat)
    {x y : G}
    (hxInv : IsInvolution x)
    (hyInv : IsInvolution y)
    (hxC : x ∈ (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G))
    (hyC : y ∈ (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G)) :
    ∃ g : G, g ∈ c.Hhat ∧ g * x * g⁻¹ = y := by
  obtain ⟨a, haxt⟩ :=
    fact_2_preamble_involutions_conjugate_proved hmin x c.t hxInv c.t_involution
  obtain ⟨b, hbyt⟩ :=
    fact_2_preamble_involutions_conjugate_proved hmin y c.t hyInv c.t_involution
  have haNorm : a ∈ Subgroup.normalizer (c.U : Set G) :=
    conjugator_of_U_centralizing_element_mem_normalizer_U hmin c hxC.2 haxt
  have hbNorm : b ∈ Subgroup.normalizer (c.U : Set G) :=
    conjugator_of_U_centralizing_element_mem_normalizer_U hmin c hyC.2 hbyt
  have haHhat : a ∈ c.Hhat := by
    rw [← hNorm]
    exact haNorm
  have hbHhat : b ∈ c.Hhat := by
    rw [← hNorm]
    exact hbNorm
  refine ⟨b⁻¹ * a, c.Hhat.mul_mem (c.Hhat.inv_mem hbHhat) haHhat, ?_⟩
  calc
    (b⁻¹ * a) * x * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * x * a⁻¹) * b := by group
    _ = b⁻¹ * c.t * b := by rw [haxt]
    _ = b⁻¹ * (b * y * b⁻¹) * b := by rw [hbyt]
    _ = y := by group

/-- Public wrapper: in the nontrivial-`O₂(Ĥ)` branch the normalizer of
`U = O(Ĥ)` is exactly `Ĥ`. -/
public theorem theorem26_normalizer_U_eq_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat ≠ ⊥) (hUne : c.U ≠ ⊥) :
    Subgroup.normalizer (c.U : Set G) = c.Hhat :=
  branch_one_normalizer_U_eq_Hhat hmin c hO2 hUne

/-- Public wrapper: in the nontrivial-`O₂(Ĥ)` branch any two involutions
of `S ∩ C_G(U)` are conjugate inside `Ĥ`. -/
public theorem theorem26_involutions_in_C_conjugate
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat)
    {x y : G}
    (hxInv : IsInvolution x) (hyInv : IsInvolution y)
    (hxC : x ∈ (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G))
    (hyC : y ∈ (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G)) :
    ∃ g : G, g ∈ c.Hhat ∧ g * x * g⁻¹ = y :=
  branch_one_involutions_in_C_conjugate hmin c hNorm hxInv hyInv hxC hyC

/-- Once the normalizer has been identified with `Ĥ`, normality of
`O₂(Ĥ)` transports the chosen involution to the distinguished involution
`t`. -/
private lemma branch_one_t_mem_twoCoreOf
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat ≠ ⊥)
    (hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat) :
    c.t ∈ twoCoreOf c.Hhat := by
  obtain ⟨z, hzInv, hzN⟩ :=
    exists_involution_mem_twoCore_of_ne_bot c.Hhat hO2
  obtain ⟨a, hazt⟩ :=
    fact_2_preamble_involutions_conjugate_proved hmin z c.t hzInv c.t_involution
  have haNorm : a ∈ Subgroup.normalizer (c.U : Set G) :=
    conjugator_of_twoCore_involution_mem_normalizer_U hmin c hzN hazt
  have haHhat : a ∈ c.Hhat := by
    rw [← hNorm]
    exact haNorm
  have hatN : a * z * a⁻¹ ∈ twoCoreOf c.Hhat :=
    (twoCoreOf_isNormalIn c.Hhat).2 a haHhat z hzN
  simpa [hazt] using hatN

/-- In the complementary branch `O₂(Ĥ) ≰ S0`, the two-core is Klein
four.  A reflection `x ∈ O₂(Ĥ)` is fused with `t` inside `Ĥ`; normality
then makes `x` centralize the two-core.  The Klein four subgroup generated by
`t,x` is self-centralizing in the dihedral Sylow subgroup, forcing equality. -/
private lemma branch_one_twoCore_isKleinFour_of_not_le_S0
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat)
    (htN : c.t ∈ twoCoreOf c.Hhat)
    (hNnot : ¬ twoCoreOf c.Hhat ≤ c.S0) :
    IsKleinFour (pCore 2 c.Hhat) := by
  classical
  obtain ⟨x, hxN, hxnotS0⟩ := SetLike.not_le_iff_exists.mp hNnot
  have hxS : x ∈ (c.S : Subgroup G) := twoCoreOf_le_S c hxN
  have hxInv : IsInvolution x :=
    centralizerSetup_reflection_isInvolution c ⟨hxS, hxnotS0⟩
  have htC : c.t ∈
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) :=
    ⟨twoCoreOf_le_S c htN, twoCoreOf_centralizes_U c htN⟩
  have hxC : x ∈
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) :=
    ⟨hxS, twoCoreOf_centralizes_U c hxN⟩
  obtain ⟨g, hgHhat, hgtx⟩ :=
    branch_one_involutions_in_C_conjugate hmin c hNorm
      c.t_involution hxInv htC hxC
  have htCommN : ∀ {n : G}, n ∈ twoCoreOf c.Hhat → Commute c.t n := by
    intro n hn
    show c.t * n = n * c.t
    have hconj : c.t * n * c.t⁻¹ = n :=
      t_mem_center_S c n (twoCoreOf_le_S c hn)
    calc
      c.t * n = (c.t * n * c.t⁻¹) * c.t := by group
      _ = n * c.t := by rw [hconj]
  have hxCommN : ∀ {n : G}, n ∈ twoCoreOf c.Hhat → Commute x n := by
    intro n hn
    have hn' : g⁻¹ * n * g ∈ twoCoreOf c.Hhat := by
      simpa using (twoCoreOf_isNormalIn c.Hhat).2 g⁻¹
        (c.Hhat.inv_mem hgHhat) n hn
    show x * n = n * x
    rw [← hgtx]
    calc
      (g * c.t * g⁻¹) * n =
          g * (c.t * (g⁻¹ * n * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * n * g) * c.t) * g⁻¹ := by
        rw [(htCommN hn').eq]
      _ = n * (g * c.t * g⁻¹) := by group
  have ht2 : c.t * c.t = 1 := by
    simpa [pow_two] using c.t_involution.2
  have hx2 : x * x = 1 := by
    simpa [pow_two] using hxInv.2
  have htxne : c.t ≠ x := by
    intro htx
    apply hxnotS0
    rw [← htx]
    exact c.t_mem_S0
  have htxComm : Commute c.t x := htCommN hxN
  let V : Subgroup G :=
    kleinFourOfCommutingInvolutions c.t x ht2 hx2 htxComm
  have hV : IsKleinFour V := by
    exact isKleinFour_kleinFourOfCommutingInvolutions c.t x ht2 hx2
      c.t_involution.1 hxInv.1 htxne htxComm
  have hVleN : V ≤ twoCoreOf c.Hhat := by
    intro v hv
    change v ∈ ({c.t * x, c.t, x, 1} : Set G) at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact (twoCoreOf c.Hhat).mul_mem htN hxN
    · exact htN
    · exact hxN
    · exact (twoCoreOf c.Hhat).one_mem
  have hNleCentV :
      twoCoreOf c.Hhat ≤ Subgroup.centralizer (V : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    change v ∈ ({c.t * x, c.t, x, 1} : Set G) at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · calc
        (c.t * x) * n = c.t * (x * n) := by group
        _ = c.t * (n * x) := by rw [(hxCommN hn).eq]
        _ = (c.t * n) * x := by group
        _ = (n * c.t) * x := by rw [(htCommN hn).eq]
        _ = n * (c.t * x) := by group
    · exact (htCommN hn).eq
    · exact (hxCommN hn).eq
    · simp
  have hVleS : V ≤ (c.S : Subgroup G) :=
    hVleN.trans (twoCoreOf_le_S c)
  let S' : Subgroup G := c.S
  let VS : Subgroup S' := V.subgroupOf S'
  let NS : Subgroup S' := (twoCoreOf c.Hhat).subgroupOf S'
  let eVS : V ≃* VS := (Subgroup.subgroupOfEquivOfLe hVleS).symm
  have hVS : IsKleinFour VS := {
    card_four := (Nat.card_congr eVS.toEquiv).symm.trans hV.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eVS).symm.trans hV.exponent_two
  }
  have hNSleCentVS : NS ≤ Subgroup.centralizer (VS : Set S') := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hNleCentV hn)) (v : G) hv
  obtain ⟨eS⟩ := c.dihedralEquiv
  have hCentVSle : Subgroup.centralizer (VS : Set S') ≤ VS :=
    centralizer_kleinFour_le_of_dihedral_mulEquiv c.one_le_m eS VS hVS
  have hNSleVS : NS ≤ VS := hNSleCentVS.trans hCentVSle
  have hNleV : twoCoreOf c.Hhat ≤ V := by
    intro n hn
    let nS : S' := ⟨n, twoCoreOf_le_S c hn⟩
    have hnNS : nS ∈ NS := by
      simpa [NS, S', nS, Subgroup.mem_subgroupOf] using hn
    have hnVS : nS ∈ VS := hNSleVS hnNS
    simpa [VS, S', nS, Subgroup.mem_subgroupOf] using hnVS
  have hNV : twoCoreOf c.Hhat = V := le_antisymm hNleV hVleN
  have hNK4 : IsKleinFour (twoCoreOf c.Hhat) := by
    rw [hNV]
    exact hV
  let eN : pCore 2 c.Hhat ≃* twoCoreOf c.Hhat :=
    Subgroup.equivMapOfInjective (pCore 2 c.Hhat) c.Hhat.subtype
      c.Hhat.subtype_injective
  exact {
    card_four := (Nat.card_congr eN.toEquiv).trans hNK4.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eN).trans hNK4.exponent_two
  }

/-- The centralizer in `Ĥ` of a Klein-four two-core is exactly the product
of the two-core and the odd core.  The dihedral Sylow subgroup makes the
two-core a Sylow subgroup of its centralizer; Burnside's normal-complement
theorem then supplies the odd factor. -/
private lemma branch_one_centralizer_twoCore_eq_sup_cores
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hK4 : IsKleinFour (pCore 2 c.Hhat)) :
    Subgroup.centralizer (pCore 2 c.Hhat : Set c.Hhat) =
      pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M : Subgroup G := c.Hhat
  let N : Subgroup M := pCore 2 M
  let O : Subgroup M := pPrimeCore 2 M
  let C : Subgroup M := Subgroup.centralizer (N : Set M)
  have : N.Normal := by dsimp [N]; infer_instance
  have : C.Normal := by dsimp [C]; infer_instance
  have hSleM : (c.S : Subgroup G) ≤ M :=
    (centralizerSetup_S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 M := c.S.subtype hSleM
  have hNleP : N ≤ (P : Subgroup M) :=
    (pCore_isPGroup (G := M) (p := 2)).le_sylow_of_normal P
  let NP : Subgroup P := N.subgroupOf P
  let eNNP : N ≃* NP := (Subgroup.subgroupOfEquivOfLe hNleP).symm
  have hNP : IsKleinFour NP := {
    card_four := (Nat.card_congr eNNP.toEquiv).symm.trans hK4.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eNNP).symm.trans hK4.exponent_two
  }
  obtain ⟨eS⟩ := c.dihedralEquiv
  let ePS : P ≃* (c.S : Subgroup G) :=
    Subgroup.subgroupOfEquivOfLe hSleM
  let eP : P ≃* DihedralGroup (2 ^ c.m) := ePS.trans eS
  have hCentNPle : Subgroup.centralizer (NP : Set P) ≤ NP :=
    centralizer_kleinFour_le_of_dihedral_mulEquiv c.one_le_m eP NP hNP
  have hNleC : N ≤ C := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    let : IsKleinFour N := hK4
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := N)).is_comm.comm
        (⟨x, hx⟩ : N) (⟨n, hn⟩ : N))
  have hOleC : O ≤ C := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hoG : (o : G) ∈ oddCoreOf c.Hhat :=
      Subgroup.mem_map.mpr ⟨o, ho, rfl⟩
    have hnG : (n : G) ∈ twoCoreOf c.Hhat :=
      Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
    exact Subtype.ext
      ((Subgroup.mem_centralizer_iff.mp
        (pPrimeCore_map_le_centralizer_pCore_map (p := 2) c.Hhat hoG))
          (n : G) hnG)
  have hsupLeC : N ⊔ O ≤ C := sup_le hNleC hOleC
  let NC : Subgroup C := N.subgroupOf C
  have hNCp : IsPGroup 2 NC :=
    (pCore_isPGroup (G := M) (p := 2)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hNleC).symm
  let PC : Sylow 2 C := by
    refine {
      toSubgroup := NC
      isPGroup' := hNCp
      is_maximal' := ?_
    }
    intro Q hQ hNCQ
    apply le_antisymm ?_ hNCQ
    intro q hq
    have hQmap : IsPGroup 2 (Q.map C.subtype) := hQ.map C.subtype
    obtain ⟨R, hQR⟩ := IsPGroup.exists_le_sylow hQmap
    obtain ⟨g, hg⟩ :=
      @MulAction.IsPretransitive.exists_smul_eq M (Sylow 2 M)
        inferInstance inferInstance R P
    have hqR : (q : M) ∈ (R : Subgroup M) :=
      hQR (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩)
    have hqconjP : g * (q : M) * g⁻¹ ∈ (P : Subgroup M) := by
      have hmem : g * (q : M) * g⁻¹ ∈
          ((g • R : Sylow 2 M) : Subgroup M) := by
        change (MulAut.conj g) (q : M) ∈
          (R : Subgroup M).map (MulAut.conj g).toMonoidHom
        exact Subgroup.mem_map.mpr ⟨(q : M), hqR, rfl⟩
      rw [hg] at hmem
      exact hmem
    have hqconjC : g * (q : M) * g⁻¹ ∈ C :=
      (inferInstance : C.Normal).conj_mem (q : M) q.2 g
    let zP : P := ⟨g * (q : M) * g⁻¹, hqconjP⟩
    have hzCent : zP ∈ Subgroup.centralizer (NP : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hqconjC) (n : M) hn
    have hzNP : zP ∈ NP := hCentNPle hzCent
    have hzN : g * (q : M) * g⁻¹ ∈ N := hzNP
    have hback : g⁻¹ * (g * (q : M) * g⁻¹) * (g⁻¹)⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem
        (g * (q : M) * g⁻¹) hzN g⁻¹
    have hqN : (q : M) ∈ N := by
      have heq : g⁻¹ * (g * (q : M) * g⁻¹) * (g⁻¹)⁻¹ = (q : M) := by
        group
      rwa [heq] at hback
    exact hqN
  have hPCcenter : (PC : Subgroup C) ≤
      centerIn (G := C) (Subgroup.normalizer (PC : Subgroup C)) := by
    intro n hn
    refine ⟨Subgroup.le_normalizer hn, ?_⟩
    change n ∈ Subgroup.centralizer
      (Subgroup.normalizer ((PC : Subgroup C) : Set C) : Set C)
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hnN : (n : M) ∈ N := hn
    have hqC : (q : M) ∈ C := q.2
    have hcomm : (n : M) * (q : M) = (q : M) * (n : M) :=
      (Subgroup.mem_centralizer_iff.mp hqC) (n : M) hnN
    exact Subtype.ext hcomm.symm
  have hcomp : HasNormalPComplement 2 C :=
    hasNormalPComplement_of_sylow_le_center_normalizer 2 PC hPCcenter
  have hCQ :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 C hcomp
  have hgen : (PC : Subgroup C) ⊔ pPrimeCore 2 C = ⊤ :=
    preambleSylow_sup_of_quotient_pgroup (pPrimeCore 2 C) PC hCQ
  have hmapPC : (PC : Subgroup C).map C.subtype = N := by
    change NC.map C.subtype = N
    exact Subgroup.map_subgroupOf_eq_of_le hNleC
  have hmapO : (pPrimeCore 2 C).map C.subtype ≤ O := by
    exact pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 C
  have hCle : C ≤ N ⊔ O := by
    intro x hx
    have hxtop : (⟨x, hx⟩ : C) ∈ (PC : Subgroup C) ⊔ pPrimeCore 2 C := by
      rw [hgen]
      trivial
    have hxmap : x ∈ ((PC : Subgroup C) ⊔ pPrimeCore 2 C).map C.subtype :=
      Subgroup.mem_map.mpr ⟨⟨x, hx⟩, hxtop, rfl⟩
    rw [Subgroup.map_sup, hmapPC] at hxmap
    exact (sup_le_sup le_rfl hmapO) hxmap
  exact le_antisymm hCle hsupLeC

/-- In the noncyclic-core subcase, internal fusion forces
`C_S(U)=O₂(Ĥ)`.  An element of the centralizer outside the two-core either
is already a reflection, or becomes one after multiplication by a fixed
two-core reflection.  It is then fused with `t` inside `Ĥ`, contradicting
normality of the two-core. -/
private lemma branch_one_C_eq_twoCore_of_not_le_S0
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat)
    (htN : c.t ∈ twoCoreOf c.Hhat)
    (hNnot : ¬ twoCoreOf c.Hhat ≤ c.S0) :
    (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) =
      twoCoreOf c.Hhat := by
  classical
  have hNleC : twoCoreOf c.Hhat ≤
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) := by
    intro z hz
    exact ⟨twoCoreOf_le_S c hz, twoCoreOf_centralizes_U c hz⟩
  apply le_antisymm ?_ hNleC
  intro x hxC
  by_contra hxN
  obtain ⟨r, hrN, hrnotS0⟩ := SetLike.not_le_iff_exists.mp hNnot
  have hrC : r ∈
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) :=
    hNleC hrN
  have htC : c.t ∈
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) :=
    hNleC htN
  by_cases hxS0 : x ∈ c.S0
  · let y : G := r * x
    have hyC : y ∈
        (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) :=
      ((c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G)).mul_mem
        hrC hxC
    have hynotS0 : y ∉ c.S0 := by
      intro hyS0
      apply hrnotS0
      have hrEq : r = y * x⁻¹ := by
        dsimp [y]
        group
      rw [hrEq]
      exact c.S0.mul_mem hyS0 (c.S0.inv_mem hxS0)
    have hynotN : y ∉ twoCoreOf c.Hhat := by
      intro hyN
      apply hxN
      have hxEq : x = r⁻¹ * y := by
        dsimp [y]
        group
      rw [hxEq]
      exact (twoCoreOf c.Hhat).mul_mem
        ((twoCoreOf c.Hhat).inv_mem hrN) hyN
    have hyInv : IsInvolution y :=
      centralizerSetup_reflection_isInvolution c ⟨hyC.1, hynotS0⟩
    obtain ⟨g, hgHhat, hgty⟩ :=
      branch_one_involutions_in_C_conjugate hmin c hNorm
        c.t_involution hyInv htC hyC
    have hyN : y ∈ twoCoreOf c.Hhat := by
      have hconj :=
        (twoCoreOf_isNormalIn c.Hhat).2 g hgHhat c.t htN
      rwa [hgty] at hconj
    exact hynotN hyN
  · have hxInv : IsInvolution x :=
      centralizerSetup_reflection_isInvolution c ⟨hxC.1, hxS0⟩
    obtain ⟨g, hgHhat, hgtx⟩ :=
      branch_one_involutions_in_C_conjugate hmin c hNorm
        c.t_involution hxInv htC hxC
    have hxN' : x ∈ twoCoreOf c.Hhat := by
      have hconj :=
        (twoCoreOf_isNormalIn c.Hhat).2 g hgHhat c.t htN
      rwa [hgtx] at hconj
    exact hxN hxN'

/-- A normalizer equality gives the ambient normality statement for `U`. -/
private lemma U_isNormalIn_Hhat_of_normalizer_eq
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat) :
    IsNormalIn c.U c.Hhat := by
  refine ⟨(U_isNormalIn_H c).1.trans c.H_le_Hhat, ?_⟩
  intro h hh u hu
  have hhNorm : h ∈ Subgroup.normalizer (c.U : Set G) := by
    rw [hNorm]
    exact hh
  exact (Subgroup.mem_normalizer_iff.mp hhNorm u).mp hu

/-- If `U` is normal in `Ĥ`, then `U ≤ O(Ĥ)`.  This is the easy half of
branch-one `U = O(Ĥ)`; the missing half is `O(Ĥ) ≤ H`. -/
private lemma U_le_oddCoreOf_of_normal_in_Hhat
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hUN : IsNormalIn c.U c.Hhat) :
    c.U ≤ oddCoreOf c.Hhat := by
  classical
  have hUleHhat : c.U ≤ c.Hhat := hUN.1
  have hUnorm : (c.U.subgroupOf c.Hhat).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (H := c.Hhat) (N := c.U) (le_normalizer_of_isNormalIn hUN)
  have hUodd : Nat.Coprime 2 (Nat.card (↥c.U)) := by
    unfold CentralizerSetup.U oddCoreOf
    rw [Subgroup.card_map_of_injective c.H.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  have hUodd' : Nat.Coprime 2
      (Nat.card (↥(c.U.subgroupOf c.Hhat))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleHhat).toEquiv]
    exact hUodd
  have hUleP : c.U ≤ (pPrimeCore 2 c.Hhat).map c.Hhat.subtype := by
    have hle : (c.U.subgroupOf c.Hhat) ≤ pPrimeCore 2 c.Hhat :=
      le_sSup ⟨hUnorm, hUodd'⟩
    have hmap : (c.U.subgroupOf c.Hhat).map c.Hhat.subtype ≤
        (pPrimeCore 2 c.Hhat).map c.Hhat.subtype :=
      Subgroup.map_mono (f := c.Hhat.subtype) hle
    simpa [Subgroup.map_subgroupOf_eq_of_le hUleHhat] using hmap
  simpa [oddCoreOf] using hUleP

/-- If `t ∈ O₂(Ĥ)`, then the odd core of `Ĥ` centralizes `t` and is
therefore contained in `H=C_G(t)`. -/
private lemma oddCoreOf_Hhat_le_H_of_t_mem_twoCore
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (htN : c.t ∈ twoCoreOf c.Hhat) :
    oddCoreOf c.Hhat ≤ c.H := by
  intro x hx
  rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff]
  intro y hy
  have hyt : y = c.t := by simpa using hy
  rw [hyt]
  exact (Subgroup.mem_centralizer_iff.mp
    (oddCoreOf_le_centralizer_twoCoreOf c.Hhat hx)) c.t htN

/-- Source-order identification `U=O(Ĥ)` after the normalizer equality.
The forward inclusion is normality; the reverse inclusion uses
`t ∈ O₂(Ĥ)` and odd-order uniqueness inside `H`. -/
private lemma branch_one_U_eq_oddCoreOf
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat)
    (htN : c.t ∈ twoCoreOf c.Hhat) :
    c.U = oddCoreOf c.Hhat := by
  apply le_antisymm
  · exact U_le_oddCoreOf_of_normal_in_Hhat c
      (U_isNormalIn_Hhat_of_normalizer_eq c hNorm)
  · apply odd_order_subgroup_le_U hmin c
      (oddCoreOf_Hhat_le_H_of_t_mem_twoCore c htN)
    unfold oddCoreOf
    rw [Subgroup.card_map_of_injective c.Hhat.subtype_injective]
    exact pPrimeCore_coprime_card (p := 2) (G := c.Hhat)

/-- If `O₂(Ĥ)` lies in the cyclic subgroup `S0`, then its distinguished
involution `t` is fixed by all of `Ĥ`; hence `Ĥ=C_G(t)=H`. -/
private lemma branch_one_Hhat_eq_H_of_twoCore_le_S0
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (htN : c.t ∈ twoCoreOf c.Hhat)
    (hNleS0 : twoCoreOf c.Hhat ≤ c.S0) :
    c.Hhat = c.H := by
  apply le_antisymm ?_ c.H_le_Hhat
  intro h hh
  rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff]
  intro y hy
  have hyt : y = c.t := by simpa using hy
  rw [hyt]
  have hconjN : h * c.t * h⁻¹ ∈ twoCoreOf c.Hhat :=
    (twoCoreOf_isNormalIn c.Hhat).2 h hh c.t htN
  let x : ↥c.S0 := ⟨h * c.t * h⁻¹, hNleS0 hconjN⟩
  let z : ↥c.S0 := ⟨c.t, c.t_mem_S0⟩
  have hx1 : x ≠ 1 := by
    intro hx
    apply c.t_involution.1
    have hxval : h * c.t * h⁻¹ = 1 := by
      simpa [x] using congrArg Subtype.val hx
    calc
      c.t = h⁻¹ * (h * c.t * h⁻¹) * h := by group
      _ = h⁻¹ * 1 * h := by rw [hxval]
      _ = 1 := by simp
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    have ht2 : c.t * c.t = 1 := by
      simpa [pow_two] using c.t_involution.2
    calc
      (h * c.t * h⁻¹) ^ 2 = h * (c.t * c.t) * h⁻¹ := by
        rw [pow_two]
        group
      _ = h * 1 * h⁻¹ := by rw [ht2]
      _ = 1 := by simp
  have hz1 : z ≠ 1 := by
    intro hz
    apply c.t_involution.1
    simpa [z] using congrArg Subtype.val hz
  have hz2 : z ^ 2 = 1 := by
    apply Subtype.ext
    simpa [z, pow_two] using c.t_involution.2
  have hxz : x = z :=
    unique_involution_of_cyclic_two_group_t26 c.S0_cyclic c.one_le_m
      (natCard_S0_eq_two_pow c) x z hx1 hx2 hz1 hz2
  have hconj : h * c.t * h⁻¹ = c.t := by
    simpa [x, z] using congrArg Subtype.val hxz
  have hcomm : h * c.t = c.t * h := by
    calc
      h * c.t = (h * c.t * h⁻¹) * h := by group
      _ = c.t * h := by rw [hconj]
  exact hcomm.symm

/-- The two-core is contained in `S ∩ C_G(U)` in source order; no prior
identification `U = O(Ĥ)` is needed. -/
private lemma twoCoreOf_le_S_inter_centralizer_U
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    twoCoreOf c.Hhat ≤
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) := by
  intro x hx
  exact ⟨twoCoreOf_le_S c hx, twoCoreOf_centralizes_U c hx⟩

/-- The noncyclic two-core acts as the natural Klein four subgroup of an
`S₃` quotient.  Internal fusion is transitive on its three nonidentity
elements, while Lemma 2.1 rules out the order-three automorphism subgroup;
the resulting `S₃` quotient is identified with `D₆`. -/
private theorem branch_one_quotient_equiv_dihedral_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat)
    (hK4 : IsKleinFour (pCore 2 c.Hhat)) :
    Nonempty ((c.Hhat ⧸
      (pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat)) ≃* DihedralGroup 3) := by
  classical
  let M : Subgroup G := c.Hhat
  let N : Subgroup M := pCore 2 M
  let O : Subgroup M := pPrimeCore 2 M
  let K : Subgroup M := N ⊔ O
  have hNnormal : N.Normal := by
    dsimp [N, M]
    infer_instance
  have hKnormal : K.Normal := by
    dsimp [K, N, O, M]
    infer_instance
  have hSleM : (c.S : Subgroup G) ≤ M :=
    (centralizerSetup_S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 M := c.S.subtype hSleM
  have hNleP : N ≤ (P : Subgroup M) :=
    (pCore_isPGroup (G := M) (p := 2)).le_sylow_of_normal P
  obtain ⟨eS⟩ := c.dihedralEquiv
  let ePS : P ≃* (c.S : Subgroup G) :=
    Subgroup.subgroupOfEquivOfLe hSleM
  let eP : P ≃* DihedralGroup (2 ^ c.m) := ePS.trans eS
  have hCent : Subgroup.centralizer (N : Set M) = K := by
    simpa [M, N, O, K] using
      branch_one_centralizer_twoCore_eq_sup_cores c hK4
  have hfusion : ∀ x y : N, x ≠ 1 → y ≠ 1 →
      ∃ g : M, g * (x : M) * g⁻¹ = (y : M) := by
    let : IsKleinFour N := hK4
    intro x y hx1 hy1
    have hxInvM : IsInvolution (x : M) := by
      constructor
      · intro hx
        apply hx1
        exact Subtype.ext hx
      · simpa [pow_two] using
          congrArg Subtype.val (IsKleinFour.mul_self x)
    have hyInvM : IsInvolution (y : M) := by
      constructor
      · intro hy
        apply hy1
        exact Subtype.ext hy
      · simpa [pow_two] using
          congrArg Subtype.val (IsKleinFour.mul_self y)
    have hxInvG : IsInvolution (x : G) := by
      constructor
      · intro hx
        apply hxInvM.1
        exact Subtype.ext hx
      · simpa using congrArg (fun z : M => (z : G)) hxInvM.2
    have hyInvG : IsInvolution (y : G) := by
      constructor
      · intro hy
        apply hyInvM.1
        exact Subtype.ext hy
      · simpa using congrArg (fun z : M => (z : G)) hyInvM.2
    have hxCore : (x : G) ∈ twoCoreOf c.Hhat := by
      exact Subgroup.mem_map.mpr ⟨(x : M), x.2, rfl⟩
    have hyCore : (y : G) ∈ twoCoreOf c.Hhat := by
      exact Subgroup.mem_map.mpr ⟨(y : M), y.2, rfl⟩
    have hxC : (x : G) ∈
        (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) :=
      twoCoreOf_le_S_inter_centralizer_U c hxCore
    have hyC : (y : G) ∈
        (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) :=
      twoCoreOf_le_S_inter_centralizer_U c hyCore
    obtain ⟨g, hgHhat, hgxy⟩ :=
      branch_one_involutions_in_C_conjugate hmin c hNorm
        hxInvG hyInvG hxC hyC
    refine ⟨⟨g, hgHhat⟩, ?_⟩
    apply Subtype.ext
    exact hgxy
  obtain ⟨eQ⟩ :=
    quotient_centralizer_equiv_perm_three_of_kleinFour_fusion
      N K hNnormal hKnormal hK4 P c.one_le_m eP hNleP hCent
      hfusion (lemma_2_1 hmin c)
  obtain ⟨eD⟩ := permThree_mulEquiv_dihedralThree
  simpa [M, N, O, K] using (show Nonempty ((M ⧸ K) ≃* DihedralGroup 3) from
    ⟨eQ.trans eD⟩)

/-- If `Ĥ = H = S·U`, then `C_S(U)` is normal in `Ĥ`; being a `2`-subgroup,
it lies in `O₂(Ĥ)`.  This is one half of the theorem's centralizer equality
and needs only the preamble equality `H = S·U` (not Lemma 2.1). -/
private lemma S_inter_centralizer_U_le_twoCoreOf_of_Hhat_eq_H
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hHhat : c.Hhat = c.H)
    (hHSU : (c.S : Subgroup G) ⊔ c.U = c.H) :
    (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) ≤
      twoCoreOf c.Hhat := by
  classical
  let C : Subgroup G :=
    (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G)
  have hC_le_S : C ≤ (c.S : Subgroup G) := inf_le_left
  have hC_le_Hhat : C ≤ c.Hhat := by
    intro x hx
    rw [hHhat]
    exact (hC_le_S.trans (S_le_H c)) hx
  have hU_le_H : c.U ≤ c.H := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨p, _hp, rfl⟩
    exact p.2
  have hU_normal_H : IsNormalIn c.U c.H := by
    refine ⟨hU_le_H, ?_⟩
    intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨p, hp, rfl⟩
    have hconj : (⟨h, hh⟩ : ↥c.H) * p * (⟨h, hh⟩ : ↥c.H)⁻¹ ∈
        pPrimeCore 2 c.H :=
      (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        p hp (⟨h, hh⟩ : ↥c.H)
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥c.H) * p * (⟨h, hh⟩ : ↥c.H)⁻¹, hconj, by simp⟩
  have hS_norm_U : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
    (S_le_H c).trans (le_normalizer_of_isNormalIn hU_normal_H)
  have hHnormalC : c.H ≤ Subgroup.normalizer (C : Set G) := by
    refine (Subgroup.le_normalizer_iff).mpr ?_
    intro h hh c0 hc0
    have hhSU : h ∈ (c.S : Subgroup G) ⊔ c.U := by
      rw [hHSU]
      exact hh
    have hhprod : h ∈ ((c.S : Subgroup G) : Set G) * (c.U : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right
        (H := c.S) (N := c.U) hS_norm_U]
      exact hhSU
    rcases hhprod with ⟨s, hs, u, hu, hsmu⟩
    have hc0u : c0 * u = u * c0 :=
      ((Subgroup.mem_centralizer_iff (g := c0) (s := (c.U : Set G))).1
        hc0.2 u hu).symm
    have hmain : h * c0 * h⁻¹ = s * c0 * s⁻¹ := by
      rw [← hsmu]
      calc
        (s * u) * c0 * (s * u)⁻¹ = s * (u * c0 * u⁻¹) * s⁻¹ := by group
        _ = s * c0 * s⁻¹ := by
          have hu_c0 : u * c0 * u⁻¹ = c0 := by
            rw [hc0u.symm]
            group
          rw [hu_c0]
    have hc0S : c0 ∈ (c.S : Subgroup G) := hc0.1
    have hS' : s * c0 * s⁻¹ ∈ (c.S : Subgroup G) :=
      (c.S : Subgroup G).mul_mem
        ((c.S : Subgroup G).mul_mem hs hc0S) ((c.S : Subgroup G).inv_mem hs)
    have hcent : s * c0 * s⁻¹ ∈ Subgroup.centralizer (c.U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : s⁻¹ * v * s ∈ c.U :=
        by
          simpa using (Subgroup.le_normalizer_iff.mp hS_norm_U) s⁻¹
            ((c.S : Subgroup G).inv_mem hs) v hv
      have hc0v' : c0 * (s⁻¹ * v * s) = (s⁻¹ * v * s) * c0 :=
        ((Subgroup.mem_centralizer_iff (g := c0) (s := (c.U : Set G))).1
          hc0.2 (s⁻¹ * v * s) hv').symm
      calc
        v * (s * c0 * s⁻¹) = s * ((s⁻¹ * v * s) * c0) * s⁻¹ := by group
        _ = s * (c0 * (s⁻¹ * v * s)) * s⁻¹ := by rw [hc0v']
        _ = (s * c0 * s⁻¹) * v := by group
    have hC' : s * c0 * s⁻¹ ∈ C := ⟨hS', hcent⟩
    rw [hmain]
    exact hC'
  have hCnormal : (C.subgroupOf c.Hhat).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_Hhat, hHhat]
    exact hHnormalC
  have hCp : IsPGroup 2 C :=
    (c.S).isPGroup'.to_le hC_le_S
  exact le_qCoreOf_of_normal_isPGroup c.Hhat C 2 hC_le_Hhat hCnormal hCp

/-! ## Branch 1: `O₂(Ĥ) ≠ 1` -/

/-- First-alternative subcase, `U = O(Ĥ)`, after `Ĥ = H`.  Since `U` is
defined to be `O(H)`, this is definitional. -/
private theorem theorem_2_6_branch_one_U {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hHhat : c.Hhat = c.H) :
    c.U = oddCoreOf c.Hhat := by
  rw [hHhat]
  rfl

/-- First-alternative subcase, `C_S(U) = O₂(Ĥ)`, factored away from the
group-specific route.

The forward inclusion uses `Ĥ = H = S ⊔ U`; the reverse inclusion is the
source-order commutativity fact `O₂(Ĥ) ≤ C_S(U)`. -/
private theorem theorem_2_6_branch_one_C {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hHhat : c.Hhat = c.H)
    (hHSU : (c.S : Subgroup G) ⊔ c.U = c.H) :
    (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) =
      twoCoreOf c.Hhat := by
  apply le_antisymm
  · exact S_inter_centralizer_U_le_twoCoreOf_of_Hhat_eq_H c
      hHhat hHSU
  · exact twoCoreOf_le_S_inter_centralizer_U c

/-- Complete assembly of the cyclic-core subcase in the nontrivial-`O₂`
branch.  The normalizer equality identifies the odd core and puts `t` in
`O₂(Ĥ)`; containment in `S0` then forces `Ĥ=H`. -/
private theorem theorem_2_6_branch_one_first_subcase
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat ≠ ⊥)
    (hUne : c.U ≠ ⊥)
    (hNleS0 : twoCoreOf c.Hhat ≤ c.S0) :
    CentralizerStructure c := by
  have hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    branch_one_normalizer_U_eq_Hhat hmin c hO2 hUne
  have htN : c.t ∈ twoCoreOf c.Hhat :=
    branch_one_t_mem_twoCoreOf hmin c hO2 hNorm
  have hU : c.U = oddCoreOf c.Hhat :=
    branch_one_U_eq_oddCoreOf hmin c hNorm htN
  have hHhat : c.Hhat = c.H :=
    branch_one_Hhat_eq_H_of_twoCore_le_S0 c htN hNleS0
  have hHSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
    fact_2_preamble_H_eq_SU_proved hmin c
  have hC :
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) =
        twoCoreOf c.Hhat :=
    theorem_2_6_branch_one_C c hHhat hHSU
  exact ⟨hU, hC, Or.inl ⟨hNleS0, hHhat⟩⟩

/-- Complete assembly of the Klein-four subcase in the nontrivial-`O₂`
branch. -/
private theorem theorem_2_6_branch_one_second_subcase
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat ≠ ⊥)
    (hUne : c.U ≠ ⊥)
    (hNnot : ¬ twoCoreOf c.Hhat ≤ c.S0) :
    CentralizerStructure c := by
  have hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    branch_one_normalizer_U_eq_Hhat hmin c hO2 hUne
  have htN : c.t ∈ twoCoreOf c.Hhat :=
    branch_one_t_mem_twoCoreOf hmin c hO2 hNorm
  have hU : c.U = oddCoreOf c.Hhat :=
    branch_one_U_eq_oddCoreOf hmin c hNorm htN
  have hK4 : IsKleinFour (pCore 2 c.Hhat) :=
    branch_one_twoCore_isKleinFour_of_not_le_S0
      hmin c hNorm htN hNnot
  have hC :
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) =
        twoCoreOf c.Hhat :=
    branch_one_C_eq_twoCore_of_not_le_S0 hmin c hNorm htN hNnot
  have hQ : Nonempty ((c.Hhat ⧸
      (pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat)) ≃* DihedralGroup 3) :=
    branch_one_quotient_equiv_dihedral_three hmin c hNorm hK4
  exact ⟨hU, hC, Or.inr ⟨hK4, hQ⟩⟩

/-- The complete nontrivial-two-core route, conditional only on the
nontriviality of `U`. -/
private theorem theorem_2_6_branch_one_of_U_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat ≠ ⊥)
    (hUne : c.U ≠ ⊥) :
    CentralizerStructure c := by
  by_cases hNleS0 : twoCoreOf c.Hhat ≤ c.S0
  · exact theorem_2_6_branch_one_first_subcase
      hmin c hO2 hUne hNleS0
  · exact theorem_2_6_branch_one_second_subcase
      hmin c hO2 hUne hNleS0

/-- **REGISTERED BRIDGE** — nontrivial-`O₂` source case (legacy name).

Statement: if `O₂(Ĥ) ≠ 1`, then the full `CentralizerStructure c` holds.

Why needed: the paper says that in this case “the assertion follows
immediately”; the assertion includes both structure alternatives.

Elimination condition: prove `U = O(Ĥ)` and `C_S(U) = O₂(Ĥ)` from
`N_G(U)=Ĥ`, then use the D-group structure of the proper subgroup `Ĥ` and
`lemma_2_1` to obtain the theorem's full disjunction. -/
private theorem theorem_2_6_branch_one_alternative {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat ≠ ⊥) :
    CentralizerStructure c := by
  exact theorem_2_6_branch_one_of_U_ne_bot
    hmin c hO2 (lemma_2_2 hmin c).2

/-- Nontrivial-`O₂` case, kept as a named assembly point. -/
public theorem theorem_2_6_branch_one {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat ≠ ⊥) :
    CentralizerStructure c := by
  exact theorem_2_6_branch_one_alternative hmin c hO2

/-! ## Branch 2: `O₂(Ĥ) = 1` -/

/-- A nontrivial layer contains an actual component.  This is the first
source-faithful reduction in the `O₂(Ĥ)=1` branch: the paper's notation
`1 ≠ E := E(Ĥ)` is unpacked into a selected quasisimple subnormal subgroup
before any classification or `PGL₂` transport is attempted. -/
theorem exists_component_of_componentLayerOf_ne_bot
    {G : Type u} [Group G]
    (N : Subgroup G) (hE : componentLayerOf N ≠ ⊥) :
    ∃ E : Subgroup G, IsComponentOf E N := by
  by_cases hex : ∃ E : Subgroup G, IsComponentOf E N
  · exact hex
  · exfalso
    apply hE
    rw [componentLayerOf]
    apply le_antisymm
    · refine sSup_le (fun E hcomp => ?_)
      have hEbot : E = ⊥ := by
        by_contra hne
        exact hex ⟨E, hcomp⟩
      rw [hEbot]
    · exact bot_le

/-- The proved data available immediately after selecting a component in the
trivial-two-core branch.  In particular, this records the exact boundary
before the missing source step `S E / Z(E) ≅ PGL₂(q)`: proper-subgroup
classification and Lemma 2.1 are present, and the internal `2`-core is
trivial, but no concrete linear model has yet been transported. -/
public structure Theorem26ComponentBranchData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) where
  E : Subgroup G
  isComponent : IsComponentOf E c.Hhat
  E_ne_bot : E ≠ ⊥
  hhat_isDGroup : IsDGroup c.Hhat
  hhat_hasTwoInvolutionClasses : HasAtLeastTwoInvolutionClasses c.Hhat
  internal_twoCore_eq_bot : pCore 2 c.Hhat = ⊥

/-- Assemble the component-branch data from `O₂(Ĥ)=1` and
`E(Ĥ)≠1`.  The remaining proof must refine the `IsDGroup` alternatives,
eliminate all but the `PGL₂(q)` extension, and transport the two reflected
tori; none of those steps is hidden in this extraction lemma. -/
public theorem exists_theorem26ComponentBranchData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat = ⊥)
    (hE : componentLayerOf c.Hhat ≠ ⊥) :
    Nonempty (Theorem26ComponentBranchData c) := by
  obtain ⟨E, hEcomp⟩ :=
    exists_component_of_componentLayerOf_ne_bot c.Hhat hE
  have hEne : E ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot E).mp hEcomp.2.2.1
  have hHhatD : IsDGroup c.Hhat :=
    properSubgroups_areDGroups hmin c.Hhat c.Hhat_maximal.ne_top
  have hclasses : HasAtLeastTwoInvolutionClasses c.Hhat :=
    lemma_2_1 hmin c
  have hO2map : (pCore 2 c.Hhat).map c.Hhat.subtype = ⊥ := by
    simpa [twoCoreOf] using hO2
  have hO2internal : pCore 2 c.Hhat = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (H := pCore 2 c.Hhat) (f := c.Hhat.subtype)
      (hf := c.Hhat.subtype_injective)).mp hO2map
  exact ⟨⟨E, hEcomp, hEne, hHhatD, hclasses, hO2internal⟩⟩

/-- The `D`-group two-group-quotient alternative cannot contain the selected
component.  Indeed, the odd core is solvable by Feit--Thompson and the
quotient is solvable because it is a finite `2`-group, so the whole subgroup
is solvable.  Its component would then be both solvable and nontrivial
perfect, a contradiction. -/
private theorem component_impossible_of_quotient_isTwoGroup
    {G : Type u} [Group G] [Finite G]
    (N E : Subgroup G)
    (hE : IsComponentOf E N)
    (hQ : IsPGroup 2 (N ⧸ pPrimeCore 2 N)) : False := by
  let O : Subgroup N := pPrimeCore 2 N
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := N)
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp hOcop
  have hOsolv : Group.IsSolvable O := odd_order_theorem O hOodd
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (N ⧸ O) :=
    IsPGroup.isNilpotent (by simpa [O] using hQ)
  have hQsolv : Group.IsSolvable (N ⧸ O) := inferInstance
  let : O.Normal := by
    dsimp [O]
    infer_instance
  let : Group.IsSolvable O := hOsolv
  let : Group.IsSolvable (N ⧸ O) := hQsolv
  have hNsolv : Group.IsSolvable N :=
    isSolvable_of_normal_subgroup_and_quotient O
  let : Group.IsSolvable N := hNsolv
  let : Group.IsSolvable (E.subgroupOf N) := inferInstance
  have hEsolv : Group.IsSolvable E :=
    isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hE.1)
  let : Nontrivial E := hE.2.2.1
  let : Group.IsPerfect E :=
    ⟨by simpa [derivedSubgroup] using hE.2.2.2.1⟩
  exact Group.IsPerfect.not_isSolvable E hEsolv

/-- First genuine refinement of the proper-subgroup `D`-group
classification: component-branch data rule out the two-group quotient
constructor. -/
private theorem Theorem26ComponentBranchData.not_quotientIsTwoGroup
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c) :
    ¬ IsPGroup 2 (c.Hhat ⧸ pPrimeCore 2 c.Hhat) := by
  intro hQ
  exact component_impossible_of_quotient_isTwoGroup
    c.Hhat d.E d.isComponent hQ

/-! ### Eliminating the `A₇` quotient branch

An involution of `A₇` has cycle type `(2,2)`, so all involutions of `A₇`
are conjugate.  Across an odd normal kernel, quotient conjugacy of
involutions lifts to actual conjugacy: after making the quotient images
equal, the two order-two subgroups are Schur--Zassenhaus complements inside
their common inverse-image subgroup.  This contradicts the two involution
classes supplied by Lemma 2.1. -/

section ASevenOddKernel

open Equiv.Perm

/-- Every involution of `A₇` is a product of exactly two disjoint
transpositions. -/
private lemma alternatingGroup_fin_seven_involution_cycleType
    (x : alternatingGroup (Fin 7)) (hx : IsInvolution x) :
    (x : Equiv.Perm (Fin 7)).cycleType = {2, 2} := by
  let g : Equiv.Perm (Fin 7) := x
  have hgpow : g ^ 2 = 1 := by
    exact congrArg Subtype.val hx.2
  have htypes : ∀ n, n ∈ cycleType g → n = 2 :=
    pow_prime_eq_one_iff.mp hgpow
  rw [← Multiset.eq_replicate_card] at htypes
  have hsupport := g.support.card_le_univ
  rw [← sum_cycleType, htypes, Multiset.sum_replicate, smul_eq_mul] at hsupport
  norm_num at hsupport
  have hcard : Multiset.card g.cycleType ≤ 3 := by
    omega
  have hsign : sign g = 1 := by
    exact mem_alternatingGroup.mp x.property
  rw [sign_of_cycleType, htypes] at hsign
  simp at hsign
  rw [pow_add, pow_mul, Int.units_pow_two, one_mul,
    neg_one_pow_eq_one_iff_even] at hsign
  swap
  · decide
  interval_cases h : Multiset.card g.cycleType
  · exfalso
    apply hx.1
    apply Subtype.ext
    exact card_cycleType_eq_zero.mp h
  · simp at hsign
  · simpa [g, h] using htypes
  · contradiction

/-- All involutions of `A₇` are conjugate inside `A₇`. -/
private theorem alternatingGroup_fin_seven_involutions_conjugate
    (x y : alternatingGroup (Fin 7))
    (hx : IsInvolution x) (hy : IsInvolution y) :
    ∃ g : alternatingGroup (Fin 7), g * x * g⁻¹ = y := by
  have hcx := alternatingGroup_fin_seven_involution_cycleType x hx
  have hcy := alternatingGroup_fin_seven_involution_cycleType y hy
  have hcPerm : IsConj (x : Equiv.Perm (Fin 7)) (y : Equiv.Perm (Fin 7)) :=
    isConj_iff_cycleType_eq.mpr (hcx.trans hcy.symm)
  have hsupp :
      (x : Equiv.Perm (Fin 7)).support.card + 2 ≤ Fintype.card (Fin 7) := by
    rw [← sum_cycleType, hcx]
    decide
  have hc := alternatingGroup.isConj_of hcPerm hsupp
  exact isConj_iff.mp hc

/-- Two involutions with the same image modulo an odd normal subgroup are
conjugate.  Their cyclic order-two subgroups are complements to the kernel
inside the same subgroup, hence Schur--Zassenhaus conjugacy applies. -/
private theorem involutions_conjugate_of_quotient_eq_of_odd_kernel
    {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    {x y : H} (hx : IsInvolution x) (hy : IsInvolution y)
    (hxy : QuotientGroup.mk' N x = QuotientGroup.mk' N y) :
    ∃ g : H, g * x * g⁻¹ = y := by
  let X : Subgroup H := Subgroup.zpowers x
  let Y : Subgroup H := Subgroup.zpowers y
  let S : Subgroup H := N ⊔ X
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hxOrder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
  have hyOrder : orderOf y = 2 := orderOf_eq_prime hy.2 hy.1
  have hXcard : Nat.card X = 2 := by
    simp [X, Nat.card_zpowers, hxOrder]
  have hYcard : Nat.card Y = 2 := by
    simp [Y, Nat.card_zpowers, hyOrder]
  have hyxN : y * x⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N)]
    change q (y * x⁻¹) = 1
    simp [q, map_mul, map_inv, hxy]
  have hxyN : x * y⁻¹ ∈ N := by
    rw [← QuotientGroup.eq_one_iff (N := N)]
    change q (x * y⁻¹) = 1
    simp [q, map_mul, map_inv, hxy]
  have hyS : y ∈ S := by
    change y ∈ N ⊔ X
    have h1 : y * x⁻¹ ∈ N ⊔ X :=
      (show N ≤ N ⊔ X from le_sup_left) hyxN
    have h2 : x ∈ N ⊔ X :=
      (show X ≤ N ⊔ X from le_sup_right) (Subgroup.mem_zpowers x)
    have hmul := (N ⊔ X).mul_mem h1 h2
    simpa [mul_assoc] using hmul
  have hxNY : x ∈ N ⊔ Y := by
    have h1 : x * y⁻¹ ∈ N ⊔ Y :=
      (show N ≤ N ⊔ Y from le_sup_left) hxyN
    have h2 : y ∈ N ⊔ Y :=
      (show Y ≤ N ⊔ Y from le_sup_right) (Subgroup.mem_zpowers y)
    have hmul := (N ⊔ Y).mul_mem h1 h2
    simpa [mul_assoc] using hmul
  have hYleS : Y ≤ S := Subgroup.zpowers_le.mpr hyS
  have hXleNY : X ≤ N ⊔ Y := Subgroup.zpowers_le.mpr hxNY
  have hsup : N ⊔ Y = S := by
    apply le_antisymm
    · exact sup_le le_sup_left hYleS
    · change N ⊔ X ≤ N ⊔ Y
      exact sup_le le_sup_left hXleNY
  have hNXcop : Nat.Coprime (Nat.card N) (Nat.card X) := by
    rw [hXcard]
    exact (Nat.coprime_two_left.mpr hNodd).symm
  have hNYcop : Nat.Coprime (Nat.card N) (Nat.card Y) := by
    rw [hYcard]
    exact (Nat.coprime_two_left.mpr hNodd).symm
  have hNXdisj : Disjoint N X :=
    Subgroup.disjoint_of_coprime_natCard hNXcop
  have hNYdisj : Disjoint N Y :=
    Subgroup.disjoint_of_coprime_natCard hNYcop
  have hcompX :
      (N.subgroupOf S).IsComplement' (X.subgroupOf S) := by
    simpa [S] using
      (isComplement'_subgroupOf_sup_of_disjoint N X hNXdisj)
  have hcompY :
      (N.subgroupOf S).IsComplement' (Y.subgroupOf S) := by
    have h0 := isComplement'_subgroupOf_sup_of_disjoint N Y hNYdisj
    rw [hsup] at h0
    exact h0
  have hNnormalS : (N.subgroupOf S).Normal :=
    (inferInstance : N.Normal).subgroupOf S
  have hNcardS : Nat.card (N.subgroupOf S) = Nat.card N :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show N ≤ S from le_sup_left))
  have hNoddS : Odd (Nat.card (N.subgroupOf S)) := by
    rw [hNcardS]
    exact hNodd
  have hXcardS : Nat.card (X.subgroupOf S) = 2 := by
    calc
      Nat.card (X.subgroupOf S) = Nat.card X :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (show X ≤ S from le_sup_right))
      _ = 2 := hXcard
  have hNindexS : (N.subgroupOf S).index = 2 := by
    rw [hcompX.symm.index_eq_card, hXcardS]
  have hcopS : Nat.Coprime (Nat.card (N.subgroupOf S))
      (N.subgroupOf S).index := by
    rw [hNindexS]
    exact (Nat.coprime_two_left.mpr hNoddS).symm
  obtain ⟨g, hg⟩ :=
    SchurZassenhaus.complements_conjugate_of_coprime
      (N.subgroupOf S) (X.subgroupOf S) (Y.subgroupOf S)
      hNnormalS hcompX hcompY hcopS
  let yS : S := ⟨y, hyS⟩
  have hyY : yS ∈ Y.subgroupOf S := by
    exact Subgroup.mem_zpowers y
  rw [hg] at hyY
  obtain ⟨a, haX, hga⟩ := Subgroup.mem_map.mp hyY
  have ha_ne : a ≠ 1 := by
    intro ha
    subst a
    simp at hga
    exact hy.1 (congrArg Subtype.val hga.symm)
  let aX : X.subgroupOf S := ⟨a, haX⟩
  let xS : S := ⟨x,
    (show X ≤ S from le_sup_right) (Subgroup.mem_zpowers x)⟩
  let xX : X.subgroupOf S := ⟨xS, Subgroup.mem_zpowers x⟩
  have haX_ne : aX ≠ 1 := by
    intro ha
    exact ha_ne (congrArg Subtype.val ha)
  have hxX_ne : xX ≠ 1 := by
    intro hxone
    exact hx.1 (congrArg Subtype.val (congrArg Subtype.val hxone))
  obtain ⟨w, _hwne, hwuniq⟩ :=
    (Nat.card_eq_two_iff' (1 : X.subgroupOf S)).mp hXcardS
  have hax : aX = xX :=
    (hwuniq aX haX_ne).trans (hwuniq xX hxX_ne).symm
  have haxS : a = xS := congrArg Subtype.val hax
  have hconjS : (MulAut.conj g) xS = yS := by
    simpa [haxS] using hga
  exact ⟨(g : H), congrArg Subtype.val hconjS⟩

/-- The image of an involution modulo an odd normal subgroup remains an
involution. -/
private theorem quotient_involution_of_odd_kernel
    {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    {x : H} (hx : IsInvolution x) :
    IsInvolution (QuotientGroup.mk' N x) := by
  constructor
  · intro hqx
    have hxN : x ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) x).mp hqx
    let xN : N := ⟨x, hxN⟩
    have hxNI : IsInvolution xN := by
      constructor
      · intro hone
        exact hx.1 (congrArg Subtype.val hone)
      · exact Subtype.ext hx.2
    have hxNOrder : orderOf xN = 2 :=
      orderOf_eq_prime hxNI.2 hxNI.1
    have htwo : 2 ∣ Nat.card N := by
      rw [← hxNOrder]
      exact orderOf_dvd_natCard xN
    exact hNodd.not_two_dvd_nat htwo
  · simpa using congrArg (QuotientGroup.mk' N) hx.2

/-- Conjugacy of quotient involutions lifts across an odd normal kernel. -/
private theorem involutions_conjugate_of_quotient_conjugate_of_odd_kernel
    {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    {x y : H} (hx : IsInvolution x) (hy : IsInvolution y)
    (hconj : ∃ gq : H ⧸ N,
      gq * QuotientGroup.mk' N x * gq⁻¹ = QuotientGroup.mk' N y) :
    ∃ g : H, g * x * g⁻¹ = y := by
  obtain ⟨gq, hgq⟩ := hconj
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N gq
  let z : H := g * x * g⁻¹
  have hz : IsInvolution z := by
    constructor
    · intro hzone
      apply hx.1
      have h := congrArg (fun w : H => g⁻¹ * w * g) hzone
      simpa [z, mul_assoc] using h
    · calc
        z ^ 2 = g * (x ^ 2) * g⁻¹ := by
          simp [z, pow_two, mul_assoc]
        _ = 1 := by rw [hx.2]; simp
  have hqzy : QuotientGroup.mk' N z = QuotientGroup.mk' N y := by
    dsimp [z]
    change (QuotientGroup.mk' N g) * (QuotientGroup.mk' N x) *
      (QuotientGroup.mk' N g)⁻¹ = QuotientGroup.mk' N y
    rw [hg]
    exact hgq
  obtain ⟨a, ha⟩ :=
    involutions_conjugate_of_quotient_eq_of_odd_kernel N hNodd hz hy hqzy
  refine ⟨a * g, ?_⟩
  calc
    (a * g) * x * (a * g)⁻¹ = a * z * a⁻¹ := by
      simp [z, mul_assoc]
    _ = y := ha

/-- An odd-core extension of `A₇` has only one involution class. -/
private theorem not_hasAtLeastTwoInvolutionClasses_of_odd_kernel_quotient_ASeven
    {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    (e : (H ⧸ N) ≃* alternatingGroup (Fin 7)) :
    ¬ HasAtLeastTwoInvolutionClasses H := by
  rintro ⟨x, y, hx, hy, hnconj⟩
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hqx : IsInvolution (q x) :=
    quotient_involution_of_odd_kernel N hNodd hx
  have hqy : IsInvolution (q y) :=
    quotient_involution_of_odd_kernel N hNodd hy
  have hex : IsInvolution (e (q x)) := by
    constructor
    · intro hone
      exact hqx.1 (e.injective (by simpa using hone))
    · simpa using congrArg e hqx.2
  have hey : IsInvolution (e (q y)) := by
    constructor
    · intro hone
      exact hqy.1 (e.injective (by simpa using hone))
    · simpa using congrArg e hqy.2
  obtain ⟨a, ha⟩ :=
    alternatingGroup_fin_seven_involutions_conjugate
      (e (q x)) (e (q y)) hex hey
  let gq : H ⧸ N := e.symm a
  have hgq : gq * q x * gq⁻¹ = q y := by
    apply e.injective
    simpa [gq] using ha
  exact hnconj
    (involutions_conjugate_of_quotient_conjugate_of_odd_kernel
      N hNodd hx hy ⟨gq, hgq⟩)

/-- The selected component branch cannot be the `A₇` quotient constructor,
because Lemma 2.1 supplies two involution classes in `Ĥ`. -/
private theorem Theorem26ComponentBranchData.not_quotientIsASeven
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c) :
    ¬ Nonempty
      ((c.Hhat ⧸ pPrimeCore 2 c.Hhat) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let : O.Normal := by
    dsimp [O]
    infer_instance
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp hOcop
  exact
    (not_hasAtLeastTwoInvolutionClasses_of_odd_kernel_quotient_ASeven
      O hOodd (by simpa [O] using e)) d.hhat_hasTwoInvolutionClasses

end ASevenOddKernel

/-! ### Eliminating the `PSL₂` normal-subgroup model

A normal subgroup of odd index contains every involution.  Odd
`PSL₂(K)` has one involution class: for `|K| = 3` this is the explicit
`A₄` model, while for larger fields it follows from the proved
Gorenstein--Walter Lemma 2.1 trichotomy, since simplicity excludes normal
subgroups of index two (and hence four).  Quotient conjugacy then lifts
across the odd core by the Schur--Zassenhaus helper above. -/

section PSL2OddIndex

/-- The three involutions of `A₄` form one conjugacy class. -/
private theorem alternatingGroup_fin_four_involutions_conjugate
    (x y : alternatingGroup (Fin 4))
    (hx : IsInvolution x) (hy : IsInvolution y) :
    ∃ g : alternatingGroup (Fin 4), g * x * g⁻¹ = y := by
  revert x y
  simp only [IsInvolution]
  decide

/-- Transport one-class involution fusion through a group equivalence. -/
private theorem involutions_conjugate_of_mulEquiv
    {A B : Type*} [Group A] [Group B]
    (e : A ≃* B)
    (hB : ∀ x y : B, IsInvolution x → IsInvolution y →
      ∃ g : B, g * x * g⁻¹ = y) :
    ∀ x y : A, IsInvolution x → IsInvolution y →
      ∃ g : A, g * x * g⁻¹ = y := by
  intro x y hx hy
  have hex : IsInvolution (e x) := by
    constructor
    · intro h
      exact hx.1 (e.injective (by simpa using h))
    · simpa using congrArg e hx.2
  have hey : IsInvolution (e y) := by
    constructor
    · intro h
      exact hy.1 (e.injective (by simpa using h))
    · simpa using congrArg e hy.2
  obtain ⟨g, hg⟩ := hB (e x) (e y) hex hey
  refine ⟨e.symm g, ?_⟩
  apply e.injective
  simpa using hg

/-- A normal subgroup of index four forces a normal subgroup of index two. -/
private theorem normal_index_two_of_normal_index_four_local
    {Q : Type*} [Group Q] [Finite Q]
    (hN4 : ∃ N : Subgroup Q, N.Normal ∧ N.index = 4) :
    ∃ N : Subgroup Q, N.Normal ∧ N.index = 2 := by
  classical
  rcases hN4 with ⟨N4, hN4, hindex4⟩
  let : N4.Normal := hN4
  let : Fintype (Q ⧸ N4) := N4.fintypeQuotientOfFiniteIndex
  have hcardQ : Nat.card (Q ⧸ N4) = 4 := by
    rw [← N4.index_eq_card, hindex4]
  have h2dvd : 2 ∣ Fintype.card (Q ⧸ N4) := by
    rw [← Nat.card_eq_fintype_card, hcardQ]
    norm_num
  obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card (G := Q ⧸ N4) 2 h2dvd
  let H : Subgroup (Q ⧸ N4) := Subgroup.zpowers x
  have hHcard : Nat.card H = 2 := by
    rw [Nat.card_zpowers, hx2]
  have hHindex : H.index = 2 := by
    have hprod := H.index_mul_card
    rw [hHcard, hcardQ] at hprod
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
      (by simpa [mul_comm] using hprod)
  have hHnormal : H.Normal := Subgroup.normal_of_index_eq_two hHindex
  let N : Subgroup Q := H.comap (QuotientGroup.mk' N4)
  have hNnormal : N.Normal := hHnormal.comap (QuotientGroup.mk' N4)
  have hNindex : N.index = 2 := by
    rw [Subgroup.index_comap_of_surjective H (QuotientGroup.mk'_surjective N4)]
    exact hHindex
  exact ⟨N, hNnormal, hNindex⟩

/-- A simple finite group with dihedral Sylow `2`-subgroups has one
involution class. -/
private theorem involutions_conjugate_of_simple_dihedral
    {Q : Type*} [Group Q] [Finite Q]
    (hSimple : IsSimpleGroup Q)
    (hDihedral : HasDihedralSylowTwo Q) :
    ∀ x y : Q, IsInvolution x → IsInvolution y →
      ∃ g : Q, g * x * g⁻¹ = y := by
  let : IsSimpleGroup Q := hSimple
  have hno2 : ¬ ∃ N : Subgroup Q, N.Normal ∧ N.index = 2 := by
    rintro ⟨N, hNnormal, hNindex⟩
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hSimple N hNnormal with hNbot | hNtop
    · let S : Sylow 2 Q := Classical.choice Sylow.nonempty
      obtain ⟨m, hm, ⟨eS⟩⟩ := hDihedral S
      have hcardQge : 4 ≤ Nat.card Q := by
        have hcardS : Nat.card (S : Subgroup Q) = 2 * 2 ^ m := by
          exact (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
        have hfour : 4 ≤ Nat.card (S : Subgroup Q) := by
          rw [hcardS]
          have hpow : 2 ≤ 2 ^ m := by
            calc
              2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
          omega
        exact hfour.trans
          (Nat.le_of_dvd Nat.card_pos S.card_subgroup_dvd_card)
      have hcardQ : Nat.card Q = 2 := by
        rw [hNbot, Subgroup.index_bot] at hNindex
        exact hNindex
      omega
    · rw [hNtop, Subgroup.index_top] at hNindex
      omega
  rcases gw_lemma_2_1 hDihedral with hfirst | hrest
  · exact hfirst.2.1
  · rcases hrest with hsecond | hthird
    · exact False.elim (hno2 hsecond.1)
    · exact False.elim
        (hno2 (normal_index_two_of_normal_index_four_local hthird.1))

/-- All involutions of odd `PSL₂(K)` are conjugate. -/
private theorem psl2_odd_involutions_conjugate
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    ∀ x y : PSL2 K, IsInvolution x → IsInvolution y →
      ∃ g : PSL2 K, g * x * g⁻¹ = y := by
  have hcard_ge : 3 ≤ Nat.card K := by
    rcases hK with ⟨p, n, hp, hpodd, hn, hcard⟩
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      exact hpodd.not_two_dvd_nat (by simp)
    have hpge : 3 ≤ p := by
      have hp2 := hp.two_le
      omega
    rw [hcard]
    exact hpge.trans (by
      calc
        p = p ^ 1 := by simp
        _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn)
  by_cases hcard3 : Nat.card K = 3
  · let : Fintype K := Fintype.ofFinite K
    have hFcard : Fintype.card K = 3 := by
      simpa [Nat.card_eq_fintype_card] using hcard3
    let eK : ZMod 3 ≃+* K :=
      ZMod.ringEquivOfPrime K Nat.prime_three hFcard
    let e : PSL2 K ≃* alternatingGroup (Fin 4) :=
      (psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup
    exact involutions_conjugate_of_mulEquiv e
      alternatingGroup_fin_four_involutions_conjugate
  · have hcard_gt : 3 < Nat.card K := by omega
    have hSimple : IsSimpleGroup (PSL2 K) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact involutions_conjugate_of_simple_dihedral hSimple
      (psl2_odd_hasDihedralSylowTwo_model K hK)

/-- Every involution belongs to a normal subgroup of odd index. -/
private theorem involution_mem_normal_odd_index
    {Q : Type*} [Group Q] [Finite Q]
    (L : Subgroup Q) [L.Normal] (hLindex : Odd L.index)
    {x : Q} (hx : IsInvolution x) : x ∈ L := by
  let pi : Q →* Q ⧸ L := QuotientGroup.mk' L
  have hquotOdd : Odd (Nat.card (Q ⧸ L)) := by
    simpa only [Subgroup.index_eq_card] using hLindex
  have hsquare : (pi x) ^ 2 = 1 := by
    simpa using congrArg pi hx.2
  have hone : pi x = 1 :=
    eq_one_of_sq_eq_one_of_coprime_two hquotOdd.coprime_two_left hsquare
  exact (QuotientGroup.eq_one_iff (N := L) x).mp hone

/-- One-class fusion in a normal odd-index subgroup gives one-class fusion
in the ambient group. -/
private theorem involutions_conjugate_of_normal_odd_index_fusion
    {Q : Type*} [Group Q] [Finite Q]
    (L : Subgroup Q) [L.Normal] (hLindex : Odd L.index)
    (hLfusion : ∀ x y : L, IsInvolution x → IsInvolution y →
      ∃ g : L, g * x * g⁻¹ = y) :
    ∀ x y : Q, IsInvolution x → IsInvolution y →
      ∃ g : Q, g * x * g⁻¹ = y := by
  intro x y hx hy
  have hxL : x ∈ L := involution_mem_normal_odd_index L hLindex hx
  have hyL : y ∈ L := involution_mem_normal_odd_index L hLindex hy
  let xL : L := ⟨x, hxL⟩
  let yL : L := ⟨y, hyL⟩
  have hxLI : IsInvolution xL := by
    constructor
    · intro h
      exact hx.1 (congrArg Subtype.val h)
    · exact Subtype.ext hx.2
  have hyLI : IsInvolution yL := by
    constructor
    · intro h
      exact hy.1 (congrArg Subtype.val h)
    · exact Subtype.ext hy.2
  obtain ⟨g, hg⟩ := hLfusion xL yL hxLI hyLI
  exact ⟨g, congrArg Subtype.val hg⟩

/-- A normal odd-index `PSL₂(K)` subgroup makes all ambient involutions
conjugate. -/
private theorem quotient_involutions_conjugate_of_normal_odd_index_psl2
    {Q : Type u} [Group Q] [Finite Q]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup Q) [L.Normal] (hLindex : Odd L.index)
    (e : L ≃* PSL2 K) :
    ∀ x y : Q, IsInvolution x → IsInvolution y →
      ∃ g : Q, g * x * g⁻¹ = y := by
  exact involutions_conjugate_of_normal_odd_index_fusion L hLindex
    (involutions_conjugate_of_mulEquiv e
      (psl2_odd_involutions_conjugate K hK))

/-- An odd-kernel extension whose quotient has a normal odd-index
`PSL₂(K)` subgroup has only one involution class. -/
private theorem not_hasAtLeastTwoInvolutionClasses_of_odd_kernel_normal_odd_index_psl2
    {H : Type u} [Group H] [Finite H]
    (O : Subgroup H) [O.Normal] (hOodd : Odd (Nat.card O))
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (H ⧸ O)) [L.Normal] (hLindex : Odd L.index)
    (e : L ≃* PSL2 K) :
    ¬ HasAtLeastTwoInvolutionClasses H := by
  rintro ⟨x, y, hx, hy, hnconj⟩
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  have hqx : IsInvolution (q x) :=
    quotient_involution_of_odd_kernel O hOodd hx
  have hqy : IsInvolution (q y) :=
    quotient_involution_of_odd_kernel O hOodd hy
  obtain ⟨gq, hgq⟩ :=
    quotient_involutions_conjugate_of_normal_odd_index_psl2
      K hK L hLindex e (q x) (q y) hqx hqy
  exact hnconj
    (involutions_conjugate_of_quotient_conjugate_of_odd_kernel
      O hOodd hx hy ⟨gq, hgq⟩)

/-- The selected component branch cannot use the `PSL₂(K)` model in its
normal odd-index linear subgroup. -/
private theorem Theorem26ComponentBranchData.not_linearModelPSL2
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PSL2 K) : False := by
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let : O.Normal := by
    dsimp [O]
    infer_instance
  let : L.Normal := hLnormal
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp hOcop
  exact
    (not_hasAtLeastTwoInvolutionClasses_of_odd_kernel_normal_odd_index_psl2
      O hOodd K hK L hLindex (by simpa [O] using e))
      d.hhat_hasTwoInvolutionClasses

end PSL2OddIndex

/-! ### Identifying the selected component in the surviving `PGL₂` model

The component first descends across the odd core.  Its quotient image remains
nontrivial, perfect, and subnormal; perfectness also forces it into the normal
odd-index linear subgroup.  After transport to `PGL₂(K)`, the small field
`|K| = 3` is impossible because the derived subgroup is solvable `A₄`, while
for larger fields simplicity of `PSL₂(K)` makes the image equal to the full
derived subgroup. -/

section PGL2ComponentImage

/-- A perfect subgroup has perfect image under any group homomorphism. -/
public theorem perfect_map_subgroup
    {A B : Type u} [Group A] [Group B]
    (E : Subgroup A) (f : A →* B) (hEperf : Group.IsPerfect E) :
    Group.IsPerfect (E.map f) := by
  let ef : E →* E.map f :=
    (f.comp E.subtype).codRestrict (E.map f) (fun x => by
      exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hef : Function.Surjective ef := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let : Group.IsPerfect E := hEperf
  exact Group.IsPerfect.ofSurjective hef

/-- The image of a nontrivial perfect subnormal subgroup across a solvable
normal kernel remains nontrivial, perfect, and subnormal.  If the quotient
has a normal odd-index subgroup `L`, that image lies in `L`: its further
image in the odd-order quotient by `L` is both perfect and solvable. -/
public theorem perfect_subnormal_image_le_normal_odd_index
    {H : Type u} [Group H] [Finite H]
    (E : Subgroup H) (hEperf : Group.IsPerfect E) (hEne : E ≠ ⊥)
    (hEsn : E.IsSubnormal)
    (O : Subgroup H) [O.Normal] (hOsolv : Group.IsSolvable O)
    (L : Subgroup (H ⧸ O)) (hLnormal : L.Normal)
    (hLindex : Odd L.index) :
    let q : H →* H ⧸ O := QuotientGroup.mk' O
    let Ebar : Subgroup (H ⧸ O) := E.map q
    Ebar ≠ ⊥ ∧ Group.IsPerfect Ebar ∧ Ebar.IsSubnormal ∧ Ebar ≤ L := by
  dsimp
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (H ⧸ O) := E.map q
  have hEbarperf : Group.IsPerfect Ebar := by
    dsimp [Ebar]
    exact perfect_map_subgroup E q hEperf
  have hEbarne : Ebar ≠ ⊥ := by
    intro hbot
    have hEleO : E ≤ O := by
      have hker : E ≤ q.ker := (Subgroup.map_eq_bot_iff E).mp hbot
      simpa [q, QuotientGroup.ker_mk'] using hker
    let : Group.IsSolvable O := hOsolv
    have : Group.IsSolvable (E.subgroupOf O) := inferInstance
    have hEsolv : Group.IsSolvable E :=
      isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hEleO)
    let : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne
    let : Group.IsPerfect E := hEperf
    exact Group.IsPerfect.not_isSolvable E hEsolv
  have hEbarsn : Ebar.IsSubnormal := by
    dsimp [Ebar]
    exact hEsn.map (QuotientGroup.mk'_surjective O)
  let : L.Normal := hLnormal
  let pi : (H ⧸ O) →* (H ⧸ O) ⧸ L := QuotientGroup.mk' L
  let I : Subgroup ((H ⧸ O) ⧸ L) := Ebar.map pi
  have hIperf : Group.IsPerfect I := by
    dsimp [I]
    exact perfect_map_subgroup Ebar pi hEbarperf
  have hQodd : Odd (Nat.card ((H ⧸ O) ⧸ L)) := by
    simpa only [Subgroup.index_eq_card] using hLindex
  have hQsolv : Group.IsSolvable ((H ⧸ O) ⧸ L) :=
    odd_order_theorem ((H ⧸ O) ⧸ L) hQodd
  have hIbot : I = ⊥ := by
    by_contra hIne
    let : Group.IsSolvable ((H ⧸ O) ⧸ L) := hQsolv
    have hIsolv : Group.IsSolvable I := inferInstance
    let : Nontrivial I := (Subgroup.nontrivial_iff_ne_bot I).2 hIne
    let : Group.IsPerfect I := hIperf
    exact Group.IsPerfect.not_isSolvable I hIsolv
  have hEbarL : Ebar ≤ L := by
    have hker : Ebar ≤ pi.ker := (Subgroup.map_eq_bot_iff Ebar).mp hIbot
    simpa [pi, QuotientGroup.ker_mk'] using hker
  exact ⟨hEbarne, hEbarperf, hEbarsn, hEbarL⟩

/-- Package the complete quotient-image identification for a component in a
normal odd-index `PGL₂(K)` subgroup. -/
public theorem perfect_subnormal_component_image_in_pgl2
    {H : Type u} [Group H] [Finite H]
    (E : Subgroup H) (hEperf : Group.IsPerfect E) (hEne : E ≠ ⊥)
    (hEsn : E.IsSubnormal)
    (O : Subgroup H) [O.Normal] (hOsolv : Group.IsSolvable O)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (H ⧸ O)) (hLnormal : L.Normal)
    (hLindex : Odd L.index) (e : L ≃* PGL2 K) :
    let q : H →* H ⧸ O := QuotientGroup.mk' O
    let Ebar : Subgroup (H ⧸ O) := E.map q
    let J : Subgroup (PGL2 K) := (Ebar.subgroupOf L).map e.toMonoidHom
    3 < Nat.card K ∧ Ebar ≠ ⊥ ∧ Group.IsPerfect Ebar ∧
      Ebar.IsSubnormal ∧ Ebar ≤ L ∧ J = commutator (PGL2 K) := by
  dsimp
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (H ⧸ O) := E.map q
  obtain ⟨hEbarne, hEbarperf, hEbarsn, hEbarL⟩ :=
    perfect_subnormal_image_le_normal_odd_index
      E hEperf hEne hEsn O hOsolv L hLnormal hLindex
  let EL : Subgroup L := Ebar.subgroupOf L
  let J : Subgroup (PGL2 K) := EL.map e.toMonoidHom
  have hELne : EL ≠ ⊥ := by
    intro hbot
    apply hEbarne
    have hmap : EL.map L.subtype = Ebar :=
      Subgroup.map_subgroupOf_eq_of_le hEbarL
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hJne : J ≠ ⊥ := by
    dsimp [J]
    exact (Subgroup.map_eq_bot_iff_of_injective EL e.injective).not.mpr hELne
  have hELperf : Group.IsPerfect EL := by
    let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbarL
    let : Group.IsPerfect Ebar := hEbarperf
    exact Group.IsPerfect.ofSurjective
      (f := eEL.symm.toMonoidHom) eEL.symm.surjective
  have hJperf : Group.IsPerfect J := by
    dsimp [J]
    exact perfect_map_subgroup EL e.toMonoidHom hELperf
  have hELsn : EL.IsSubnormal := hEbarsn.subgroupOf
  have hJsn : J.IsSubnormal := by
    dsimp [J]
    exact hELsn.map e.surjective
  obtain ⟨hcard, hJeq⟩ :=
    pgl2_perfect_subnormal_eq_commutator K hK J hJne hJperf hJsn
  exact ⟨hcard, hEbarne, hEbarperf, hEbarsn, hEbarL, hJeq⟩

/-- In the surviving `PGL₂(K)` classification branch, the selected component
maps exactly to the derived `PSL₂(K)` subgroup of the model. -/
public theorem Theorem26ComponentBranchData.pgl2_component_image_eq_commutator
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K) :
    let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
    let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
    let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
    let Ebar : Subgroup (c.Hhat ⧸ O) := Ei.map q
    let J : Subgroup (PGL2 K) := (Ebar.subgroupOf L).map e.toMonoidHom
    3 < Nat.card K ∧ Ebar ≠ ⊥ ∧ Group.IsPerfect Ebar ∧
      Ebar.IsSubnormal ∧ Ebar ≤ L ∧ J = commutator (PGL2 K) := by
  dsimp
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
  let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
  have hEperf : Group.IsPerfect d.E :=
    ⟨by simpa [derivedSubgroup] using d.isComponent.2.2.2.1⟩
  have hEiperf : Group.IsPerfect Ei := by
    let eEi : Ei ≃* d.E :=
      Subgroup.subgroupOfEquivOfLe d.isComponent.1
    let : Group.IsPerfect d.E := hEperf
    exact Group.IsPerfect.ofSurjective
      (f := eEi.symm.toMonoidHom) eEi.symm.surjective
  have hEine : Ei ≠ ⊥ := by
    intro hbot
    apply d.E_ne_bot
    have hmap : Ei.map c.Hhat.subtype = d.E :=
      Subgroup.map_subgroupOf_eq_of_le d.isComponent.1
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hEisn : Ei.IsSubnormal := d.isComponent.2.1
  let : O.Normal := by
    dsimp [O]
    infer_instance
  have hOodd : Odd (Nat.card O) := by
    have hOcop : Nat.Coprime 2 (Nat.card O) := by
      simpa [O] using
        pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
    exact Nat.coprime_two_left.mp hOcop
  have hOsolv : Group.IsSolvable O := odd_order_theorem O hOodd
  simpa [O, q, Ei] using
    (perfect_subnormal_component_image_in_pgl2
      Ei hEiperf hEine hEisn O hOsolv K hK L hLnormal hLindex e)

/-- The image of the center under a group equivalence is the center. -/
lemma map_center_eq_center_of_mulEquiv_local
    {A B : Type u} [Group A] [Group B]
    (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact (Subgroup.centerCongr e ⟨y, hy⟩).2
  · intro x hx
    refine ⟨e.symm x, ?_, ?_⟩
    · exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2
    · exact e.apply_symm_apply x

/-- Quasisimplicity transported through a theorem-local group equivalence. -/
public theorem isQuasisimple_mulEquiv_local
    {A B : Type u} [Group A] [Group B]
    (e : A ≃* B) (hA : IsQuasisimple A) : IsQuasisimple B := by
  have hNontriv : Nontrivial B := by
    let : Nontrivial A := hA.1
    exact e.toEquiv.injective.nontrivial
  have hPerf : Group.IsPerfect B := by
    let : Group.IsPerfect A := (Group.isPerfect_def).2 hA.2.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hSimple : IsSimpleGroup (B ⧸ Subgroup.center B) := by
    have he : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B :=
      map_center_eq_center_of_mulEquiv_local e
    exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e he)).mp
        hA.2.2
  exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩

/-- For a quasisimple subgroup whose image is the derived subgroup of a
`PGL₂(K)` model, the odd-kernel intersection is exactly its center, and its
central quotient is `PSL₂(K)`. -/
public theorem quasisimple_component_kernel_eq_center_and_quotient_psl2
    {H : Type u} [Group H] [Finite H]
    (E : Subgroup H) (hEq : IsQuasisimple E) (hEsn : E.IsSubnormal)
    (O : Subgroup H) [O.Normal] (hOsolv : Group.IsSolvable O)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (H ⧸ O)) (hLnormal : L.Normal)
    (hLindex : Odd L.index) (e : L ≃* PGL2 K) :
    let q : H →* H ⧸ O := QuotientGroup.mk' O
    let Ebar : Subgroup (H ⧸ O) := E.map q
    let f : E →* Ebar :=
      (q.comp E.subtype).codRestrict Ebar (fun x =>
        Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
    f.ker = Subgroup.center E ∧
      Nonempty ((E ⧸ Subgroup.center E) ≃* PSL2 K) := by
  dsimp
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (H ⧸ O) := E.map q
  let f : E →* Ebar :=
    (q.comp E.subtype).codRestrict Ebar (fun x => by
      exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hf : Function.Surjective f := by
    intro y
    rcases Subgroup.mem_map.mp y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  have hEperf : Group.IsPerfect E := (Group.isPerfect_def).2 hEq.2.1
  have hEne : E ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot E).mp hEq.1
  obtain ⟨hcard, hEbarne, _hEbarperf, _hEbarsn, hEbarL, hJeq⟩ :=
    perfect_subnormal_component_image_in_pgl2
      E hEperf hEne hEsn O hOsolv K hK L hLnormal hLindex e
  let EL : Subgroup L := Ebar.subgroupOf L
  let J : Subgroup (PGL2 K) := EL.map e.toMonoidHom
  let eEL : EL ≃* Ebar := Subgroup.subgroupOfEquivOfLe hEbarL
  let eMap : EL ≃* J :=
    Subgroup.equivMapOfInjective EL e.toMonoidHom e.injective
  let eJ : J ≃* commutator (PGL2 K) := MulEquiv.subgroupCongr hJeq
  let eComm : commutator (PGL2 K) ≃* PSL2 K :=
    (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      K hK hcard (MulEquiv.refl (PGL2 K))).some
  let eBar : Ebar ≃* PSL2 K :=
    ((eEL.symm.trans eMap).trans eJ).trans eComm
  have hZbar : Subgroup.center Ebar = ⊥ :=
    center_eq_bot_of_mulEquiv eBar (psl2_center_eq_bot K)
  have hker_le : f.ker ≤ Subgroup.center E := by
    rcases normal_subgroup_le_center_or_eq_top hEq f.ker inferInstance with
      hle | htop
    · exact hle
    · exfalso
      apply hEbarne
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_bot]
        let ybar : Ebar := ⟨y, hy⟩
        obtain ⟨x, hx⟩ := hf ybar
        have hxker : x ∈ f.ker := by
          rw [htop]
          trivial
        have hfx : f x = 1 := MonoidHom.mem_ker.mp hxker
        have hyone : ybar = 1 := by rw [← hx, hfx]
        exact congrArg Subtype.val hyone
      · exact bot_le
  have hcenter_le : Subgroup.center E ≤ f.ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    have hfxcenter : f x ∈ Subgroup.center Ebar := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := hf y
      simpa using congrArg f (Subgroup.mem_center_iff.mp hx z)
    have hfxbot : f x ∈ (⊥ : Subgroup Ebar) := by
      simpa [hZbar] using hfxcenter
    exact Subgroup.mem_bot.mp hfxbot
  have hker : f.ker = Subgroup.center E := le_antisymm hker_le hcenter_le
  let eRangeTop : f.range ≃* (⊤ : Subgroup Ebar) :=
    MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hf)
  let eQuotBar : E ⧸ f.ker ≃* Ebar :=
    ((QuotientGroup.quotientKerEquivRange f).trans eRangeTop).trans
      Subgroup.topEquiv
  let eCenterKer : E ⧸ Subgroup.center E ≃* E ⧸ f.ker :=
    QuotientGroup.quotientMulEquivOfEq (M := Subgroup.center E)
      (N := f.ker) hker.symm
  exact ⟨hker, ⟨(eCenterKer.trans eQuotBar).trans eBar⟩⟩

/-- The selected component has central odd-core kernel and central quotient
`PSL₂(K)` in the surviving `PGL₂(K)` branch. -/
public theorem Theorem26ComponentBranchData.pgl2_component_kernel_eq_center
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K) :
    let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
    let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
    let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
    let Ebar : Subgroup (c.Hhat ⧸ O) := Ei.map q
    let f : Ei →* Ebar :=
      (q.comp Ei.subtype).codRestrict Ebar (fun x =>
        Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
    f.ker = Subgroup.center Ei ∧
      Nonempty ((Ei ⧸ Subgroup.center Ei) ≃* PSL2 K) := by
  dsimp
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
  let eEi : Ei ≃* d.E :=
    Subgroup.subgroupOfEquivOfLe d.isComponent.1
  have hEiQ : IsQuasisimple Ei :=
    isQuasisimple_mulEquiv_local eEi.symm d.isComponent.2.2
  have hEisn : Ei.IsSubnormal := d.isComponent.2.1
  let : O.Normal := by
    dsimp [O]
    infer_instance
  have hOodd : Odd (Nat.card O) := by
    have hOcop : Nat.Coprime 2 (Nat.card O) := by
      simpa [O] using
        pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
    exact Nat.coprime_two_left.mp hOcop
  have hOsolv : Group.IsSolvable O := odd_order_theorem O hOodd
  simpa [O, Ei] using
    (quasisimple_component_kernel_eq_center_and_quotient_psl2
      Ei hEiQ hEisn O hOsolv K hK L hLnormal hLindex e)

/-- A Sylow `2`-subgroup of `PGL₂(K)` together with its derived subgroup
generates the whole group when `|K| > 3`. -/
theorem pgl2_sylow_sup_commutator_eq_top
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) :
    commutator (PGL2 K) ⊔ (P : Subgroup (PGL2 K)) = ⊤ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hJindex : J.index = 2 := by
    dsimp [J]
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    exact pgl2_psl2Range_index_eq_two K hK
  have hPnot : ¬ (P : Subgroup (PGL2 K)) ≤ J := by
    intro hPJ
    have hrel := Subgroup.relIndex_mul_index hPJ
    rw [hJindex] at hrel
    apply P.not_dvd_index
    refine ⟨(P : Subgroup (PGL2 K)).relIndex J, ?_⟩
    omega
  let T : Subgroup (PGL2 K) := J ⊔ (P : Subgroup (PGL2 K))
  have hJT : J ≤ T := le_sup_left
  have hrel := Subgroup.relIndex_mul_index hJT
  rw [hJindex] at hrel
  have hprod : J.relIndex T * T.index = 2 := hrel
  have hrel_ne_one : J.relIndex T ≠ 1 := by
    intro hrel1
    have hTJ : T ≤ J := Subgroup.relIndex_eq_one.mp hrel1
    exact hPnot (le_sup_right.trans hTJ)
  have hTindex : T.index = 1 := by
    by_contra hTne
    exact (Nat.not_prime_of_mul_eq hprod hrel_ne_one hTne) Nat.prime_two
  exact Subgroup.index_eq_one.mp hTindex

/-- A Sylow `2`-subgroup lies in every normal odd-index subgroup. -/
public theorem sylow_le_of_normal_odd_index_local
    {Q : Type u} [Group Q] [Finite Q]
    (L : Subgroup Q) (hLnormal : L.Normal) (hLindex : Odd L.index)
    (P : Sylow 2 Q) : (P : Subgroup Q) ≤ L := by
  let : L.Normal := hLnormal
  let pi : Q →* Q ⧸ L := QuotientGroup.mk' L
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmapP : IsPGroup 2 ((P : Subgroup Q).map pi) :=
    P.isPGroup'.map pi
  rcases IsPGroup.iff_card.mp hmapP with ⟨n, hn⟩
  have hcard_dvd : Nat.card ((P : Subgroup Q).map pi) ∣ Nat.card (Q ⧸ L) :=
    Subgroup.card_subgroup_dvd_card ((P : Subgroup Q).map pi)
  have hquot_odd : Odd (Nat.card (Q ⧸ L)) := by
    simpa only [Subgroup.index_eq_card] using hLindex
  cases n with
  | zero =>
      have hmap_bot : (P : Subgroup Q).map pi = ⊥ := by
        exact Subgroup.eq_bot_of_card_eq
          ((P : Subgroup Q).map pi) (by simpa using hn)
      have hle_ker : (P : Subgroup Q) ≤ pi.ker :=
        (Subgroup.map_eq_bot_iff (H := (P : Subgroup Q)) (f := pi)).mp hmap_bot
      simpa [pi, QuotientGroup.ker_mk'] using hle_ker
  | succ n =>
      have htwo_dvd_map : 2 ∣ Nat.card ((P : Subgroup Q).map pi) := by
        rw [hn]
        exact dvd_pow_self 2 (Nat.succ_ne_zero n)
      exact False.elim
        (hquot_odd.not_two_dvd_nat (htwo_dvd_map.trans hcard_dvd))

/-- In an odd-kernel quotient, the fixed Sylow image and a component image
identified with `PGL₂(K)'` generate the full normal odd-index linear subgroup.
-/
theorem sylow_sup_component_image_eq_pgl2_linear_subgroup
    {H : Type u} [Group H] [Finite H]
    (O : Subgroup H) [O.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (H ⧸ O)) (hLnormal : L.Normal)
    (hLindex : Odd L.index) (e : L ≃* PGL2 K)
    (P : Sylow 2 H)
    (Ebar : Subgroup (H ⧸ O)) (hEbarL : Ebar ≤ L)
    (hcard : 3 < Nat.card K)
    (hJeq : (Ebar.subgroupOf L).map e.toMonoidHom =
      commutator (PGL2 K)) :
    let Pq : Sylow 2 (H ⧸ O) :=
      P.mapSurjective (QuotientGroup.mk'_surjective O)
    (Pq : Subgroup (H ⧸ O)) ⊔ Ebar = L := by
  dsimp
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Pq : Sylow 2 (H ⧸ O) :=
    P.mapSurjective (QuotientGroup.mk'_surjective O)
  have hPqL : (Pq : Subgroup (H ⧸ O)) ≤ L :=
    sylow_le_of_normal_odd_index_local L hLnormal hLindex Pq
  let PL : Sylow 2 L := Pq.subtype hPqL
  let Pmodel : Sylow 2 (PGL2 K) :=
    PL.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmodel : commutator (PGL2 K) ⊔
      (Pmodel : Subgroup (PGL2 K)) = ⊤ :=
    pgl2_sylow_sup_commutator_eq_top K hK hcard Pmodel
  let EL : Subgroup L := Ebar.subgroupOf L
  let SL : Subgroup L := EL ⊔ (PL : Subgroup L)
  have hmapSL : SL.map e.toMonoidHom = ⊤ := by
    calc
      SL.map e.toMonoidHom =
          EL.map e.toMonoidHom ⊔
            (PL : Subgroup L).map e.toMonoidHom := by
        exact Subgroup.map_sup EL (PL : Subgroup L) e.toMonoidHom
      _ = commutator (PGL2 K) ⊔
          (Pmodel : Subgroup (PGL2 K)) := by
        rw [hJeq]
        change commutator (PGL2 K) ⊔
            (PL : Subgroup L).map e.toMonoidHom =
          commutator (PGL2 K) ⊔ (PL : Subgroup L).map e.toMonoidHom
        rfl
      _ = ⊤ := hmodel
  have hSLtop : SL = ⊤ := by
    apply le_antisymm le_top
    intro x _hx
    have hex : e x ∈ SL.map e.toMonoidHom := by
      rw [hmapSL]
      trivial
    rcases Subgroup.mem_map.mp hex with ⟨y, hy, hey⟩
    have hyx : y = x := e.injective hey
    simpa [hyx] using hy
  calc
    (Pq : Subgroup (H ⧸ O)) ⊔ Ebar = SL.map L.subtype := by
      dsimp [SL, EL, PL]
      rw [Subgroup.map_sup]
      rw [Subgroup.map_subgroupOf_eq_of_le hEbarL]
      rw [Subgroup.map_subgroupOf_eq_of_le hPqL]
      exact sup_comm (Pq : Subgroup (H ⧸ O)) Ebar
    _ = L := by
      rw [hSLtop]
      simpa only [← MonoidHom.range_eq_map] using L.range_subtype

/-- Specialized quotient-level form of the source step
`S E / Z(E) ≃ PGL₂(q)` for the selected component. -/
theorem Theorem26ComponentBranchData.pgl2_sylow_sup_component_image_eq_linear_subgroup
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K) :
    let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
    let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
    let P : Sylow 2 c.Hhat :=
      c.S.subtype ((S_le_H c).trans c.H_le_Hhat)
    let Pq : Sylow 2 (c.Hhat ⧸ O) :=
      P.mapSurjective (QuotientGroup.mk'_surjective O)
    let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
    let Ebar : Subgroup (c.Hhat ⧸ O) := Ei.map q
    (Pq : Subgroup (c.Hhat ⧸ O)) ⊔ Ebar = L := by
  dsimp
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
  have hSle : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 c.Hhat := c.S.subtype hSle
  let Pq : Sylow 2 (c.Hhat ⧸ O) :=
    P.mapSurjective (QuotientGroup.mk'_surjective O)
  let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
  let Ebar : Subgroup (c.Hhat ⧸ O) := Ei.map q
  obtain ⟨hcard, _hEbarne, _hEbarperf, _hEbarsn, hEbarL, hJeq⟩ :=
    d.pgl2_component_image_eq_commutator K hK L hLnormal hLindex e
  let : O.Normal := by
    dsimp [O]
    infer_instance
  simpa [O, q, P, Pq, Ei, Ebar] using
    (sylow_sup_component_image_eq_pgl2_linear_subgroup
      O K hK L hLnormal hLindex e P Ebar hEbarL hcard hJeq)

/-- Transport the distinguished involution through the odd-core quotient,
the normal linear subgroup, and its `PGL₂` model.  In the resulting fixed
Sylow subgroup it is the central rotation of the transported dihedral model.
-/
public theorem pgl2_model_sylow_transport_distinguished_involution
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (O : Subgroup c.Hhat) [O.Normal]
    (hOcop : Nat.Coprime 2 (Nat.card O))
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ O))
    (e : L ≃* PGL2 K)
    (hPqL :
      let P : Sylow 2 c.Hhat :=
        c.S.subtype ((S_le_H c).trans c.H_le_Hhat)
      let Pq : Sylow 2 (c.Hhat ⧸ O) :=
        P.mapSurjective (QuotientGroup.mk'_surjective O)
      (Pq : Subgroup (c.Hhat ⧸ O)) ≤ L) :
    let P : Sylow 2 c.Hhat :=
      c.S.subtype ((S_le_H c).trans c.H_le_Hhat)
    let Pq : Sylow 2 (c.Hhat ⧸ O) :=
      P.mapSurjective (QuotientGroup.mk'_surjective O)
    let PL : Sylow 2 L := Pq.subtype hPqL
    let Pmodel : Sylow 2 (PGL2 K) :=
      PL.mapSurjective (f := e.toMonoidHom) e.surjective
    2 ≤ c.m ∧
      ∃ eTransport : P ≃* Pmodel,
      ∃ eP : Pmodel ≃* DihedralGroup (2 ^ c.m), ∃ tModel : Pmodel,
        (tModel : PGL2 K) = e ⟨QuotientGroup.mk' O
          (⟨c.t, ((S_le_H c).trans c.H_le_Hhat)
            (c.S0_le_S c.t_mem_S0)⟩ : c.Hhat), hPqL
          (Subgroup.mem_map.mpr ⟨
            (⟨c.t, ((S_le_H c).trans c.H_le_Hhat)
              (c.S0_le_S c.t_mem_S0)⟩ : c.Hhat),
            c.S0_le_S c.t_mem_S0, rfl⟩)⟩ ∧
        tModel = eP.symm (DihedralGroup.r
          (2 ^ (c.m - 1) : ZMod (2 ^ c.m))) ∧
        ∀ p : P, (eTransport p : PGL2 K) = e
          ⟨QuotientGroup.mk' O p, hPqL
            (Subgroup.mem_map.mpr ⟨p, p.2, rfl⟩)⟩ := by
  dsimp
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSle : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 c.Hhat := c.S.subtype hSle
  let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
  let Pq : Sylow 2 (c.Hhat ⧸ O) :=
    P.mapSurjective (QuotientGroup.mk'_surjective O)
  let PL : Sylow 2 L := Pq.subtype hPqL
  let Pmodel : Sylow 2 (PGL2 K) :=
    PL.mapSurjective (f := e.toMonoidHom) e.surjective
  let qP : P →* c.Hhat ⧸ O :=
    q.comp (P : Subgroup c.Hhat).subtype
  have hqPinj : Function.Injective qP := by
    have hcop : Nat.Coprime (Nat.card (P : Subgroup c.Hhat))
        (Nat.card O) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
      rw [hn]
      exact hOcop.pow_left n
    have hdis : Disjoint (P : Subgroup c.Hhat) O :=
      Subgroup.disjoint_of_coprime_natCard hcop
    apply (MonoidHom.ker_eq_bot_iff qP).mp
    apply le_antisymm
    · intro x hx
      have hxO : (x : c.Hhat) ∈ O := by
        apply (QuotientGroup.eq_one_iff (N := O) (x : c.Hhat)).mp
        exact hx
      have hxone : (x : c.Hhat) = 1 :=
        Subgroup.disjoint_def.mp hdis x.2 hxO
      exact Subgroup.mem_bot.mpr (Subtype.ext hxone)
    · exact bot_le
  let qPq : P →* Pq :=
    qP.codRestrict (Pq : Subgroup (c.Hhat ⧸ O)) (fun x => by
      change q x ∈ (Pq : Subgroup (c.Hhat ⧸ O))
      exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  have hqPqinj : Function.Injective qPq := by
    intro x y hxy
    apply hqPinj
    exact congrArg Subtype.val hxy
  have hqPqsurj : Function.Surjective qPq := by
    intro y
    have hy : y.1 ∈ (P : Subgroup c.Hhat).map q := by
      change y.1 ∈ (P : Subgroup c.Hhat).map q
      exact y.2
    rcases Subgroup.mem_map.mp hy with ⟨x, hxP, hxy⟩
    let xP : P := ⟨x, hxP⟩
    refine ⟨xP, ?_⟩
    apply Subtype.ext
    exact hxy
  let ePq : P ≃* Pq :=
    MulEquiv.ofBijective qPq ⟨hqPqinj, hqPqsurj⟩
  let ePLPq : PL ≃* Pq :=
    Subgroup.subgroupOfEquivOfLe hPqL
  let ePLModel : PL ≃* Pmodel :=
    Subgroup.equivMapOfInjective
      (PL : Subgroup L) e.toMonoidHom e.injective
  let eTransport : P ≃* Pmodel :=
    (ePq.trans ePLPq.symm).trans ePLModel
  obtain ⟨eS⟩ := c.dihedralEquiv
  let ePS : P ≃* c.S := Subgroup.subgroupOfEquivOfLe hSle
  let eP : Pmodel ≃* DihedralGroup (2 ^ c.m) :=
    eTransport.symm.trans (ePS.trans eS)
  let tH : c.Hhat := ⟨c.t, hSle (c.S0_le_S c.t_mem_S0)⟩
  let tP : P := ⟨tH, c.S0_le_S c.t_mem_S0⟩
  let tModel : Pmodel := eTransport tP
  have htPcenter : tP ∈ Subgroup.center P := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hxS : ((x : c.Hhat) : G) ∈ (c.S : Subgroup G) := x.2
    have hxH : ((x : c.Hhat) : G) ∈ c.H := S_le_H c hxS
    have hxC : ((x : c.Hhat) : G) ∈
        Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact hxH
    have hxcomm : Commute ((x : c.Hhat) : G) c.t :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    exact Subtype.ext hxcomm.eq
  have htModelcenter : tModel ∈ Subgroup.center Pmodel := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := eTransport.surjective y
    have hcomm := Subgroup.mem_center_iff.mp htPcenter x
    simpa [tModel] using congrArg eTransport hcomm
  have htModelsq : tModel ^ 2 = 1 := by
    calc
      tModel ^ 2 = eTransport (tP ^ 2) := by
        simpa [tModel] using
          (eTransport.toMonoidHom.map_pow tP 2).symm
      _ = eTransport 1 := by
        congr 1
        apply Subtype.ext
        exact Subtype.ext c.t_involution.2
      _ = 1 := by simp
  have htModelne : tModel ≠ 1 := by
    intro ht
    have htPone : tP = 1 :=
      eTransport.injective (by simpa [tModel] using ht)
    apply c.t_involution.1
    exact congrArg (fun x : P => ((x : c.Hhat) : G)) htPone
  have hm2 : 2 ≤ c.m :=
    pgl2_dihedral_sylow_parameter_ge_two K hK Pmodel eP
  have hetcenter : eP tModel ∈
      Subgroup.center (DihedralGroup (2 ^ c.m)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := eP.surjective y
    have hcomm := Subgroup.mem_center_iff.mp htModelcenter x
    simpa using congrArg eP hcomm
  have hetpow : (eP tModel) ^ 2 = 1 := by
    simpa using congrArg eP htModelsq
  have hetne : eP tModel ≠ 1 := by
    intro h
    exact htModelne (eP.injective (by simpa using h))
  have het : eP tModel = DihedralGroup.r
      (2 ^ (c.m - 1) : ZMod (2 ^ c.m)) :=
    unique_central_involution_of_dihedral_two_pow
      hm2 (eP tModel) hetcenter hetpow hetne
  have htcentral : tModel = eP.symm (DihedralGroup.r
      (2 ^ (c.m - 1) : ZMod (2 ^ c.m))) := by
    apply eP.injective
    simpa using het
  have heTransport :
      ∀ p : P, (eTransport p : PGL2 K) = e ⟨q p,
          hPqL (Subgroup.mem_map.mpr ⟨p, p.2, rfl⟩)⟩ := by
    intro p
    dsimp [eTransport, ePq, ePLPq, ePLModel]
    rfl
  exact ⟨hm2, eTransport, eP, tModel, rfl, htcentral, heTransport⟩

/-- In the surviving `PGL₂(K)` model, the quotient image of the
distinguished involution lies in the selected component image. -/
theorem Theorem26ComponentBranchData.pgl2_distinguished_involution_mem_component_image
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K) :
    let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
    let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
    let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
    let Ebar : Subgroup (c.Hhat ⧸ O) := Ei.map q
    q ⟨c.t, ((S_le_H c).trans c.H_le_Hhat)
      (c.S0_le_S c.t_mem_S0)⟩ ∈ Ebar := by
  dsimp
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
  let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
  let Ebar : Subgroup (c.Hhat ⧸ O) := Ei.map q
  obtain ⟨hcard, _hEbarne, _hEbarperf, _hEbarsn, hEbarL, hJeq⟩ :=
    d.pgl2_component_image_eq_commutator
      K hK L hLnormal hLindex e
  have hSle : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 c.Hhat := c.S.subtype hSle
  let Pq : Sylow 2 (c.Hhat ⧸ O) :=
    P.mapSurjective (QuotientGroup.mk'_surjective O)
  have hPqL : (Pq : Subgroup (c.Hhat ⧸ O)) ≤ L :=
    sylow_le_of_normal_odd_index_local L hLnormal hLindex Pq
  let PL : Sylow 2 L := Pq.subtype hPqL
  let Pmodel : Sylow 2 (PGL2 K) :=
    PL.mapSurjective (f := e.toMonoidHom) e.surjective
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using
      (pPrimeCore_coprime_card (p := 2) (G := c.Hhat))
  obtain ⟨_hm2, _eTransport, eP, tModel, htModelVal, htModelCentral,
      _heTransport⟩ :=
    pgl2_model_sylow_transport_distinguished_involution
      c O hOcop K hK L e hPqL
  obtain ⟨_U, _s, r, g, _hUcyc, _hUodd, _hUcard, _hsU, _hsJ,
      _hsne, _hssq, hrJ, _hrU, _hrsq, _hrinv, _hsP, hrcentral⟩ :=
    pgl2_low_two_part_torus_reflection_data_fixed_sylow
      K hK hcard Pmodel eP
  have hrconjJ : g * r * g⁻¹ ∈ commutator (PGL2 K) :=
    (inferInstance : (commutator (PGL2 K)).Normal).conj_mem r hrJ g
  have htModelJ : (tModel : PGL2 K) ∈ commutator (PGL2 K) := by
    rw [hrcentral, ← htModelCentral] at hrconjJ
    exact hrconjJ
  have htModelMap : (tModel : PGL2 K) ∈
      (Ebar.subgroupOf L).map e.toMonoidHom := by
    rw [hJeq]
    exact htModelJ
  rcases Subgroup.mem_map.mp htModelMap with ⟨x, hxEbar, hxeq⟩
  let tH : c.Hhat := ⟨c.t, hSle (c.S0_le_S c.t_mem_S0)⟩
  have htPq : q tH ∈ (Pq : Subgroup (c.Hhat ⧸ O)) := by
    change q tH ∈ (P : Subgroup c.Hhat).map q
    exact Subgroup.mem_map.mpr
      ⟨tH, c.S0_le_S c.t_mem_S0, rfl⟩
  let tL : L := ⟨q tH, hPqL htPq⟩
  have hxtL : x = tL := by
    apply e.injective
    calc
      e x = (tModel : PGL2 K) := hxeq
      _ = e tL := by
        simpa [tL, tH, q, P, Pq, PL, Pmodel] using htModelVal
  have htLEbar : tL ∈ Ebar.subgroupOf L := by
    rw [← hxtL]
    exact hxEbar
  simpa [O, q, Ei, Ebar, tL, tH] using
    (Subgroup.mem_subgroupOf.mp htLEbar)

end PGL2ComponentImage

/-- Source-facing packaging of the involutory conjugator step in the
surviving component branch.  Once the Sylow parameter is at least two,
global involution fusion conjugates `ts` to `t`; conjugating the fixed Sylow
back gives an order divisible by eight subgroup of `C_G(ts)`. -/
public theorem exists_theorem26_product_centralizer_conjugator
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hm2 : 2 ≤ c.m)
    (s : G) (hsI : IsInvolution s)
    (hts : Commute c.t s) (htsne : c.t ≠ s) :
    ∃ y : G, IsInvolution y ∧
      y * c.t * y⁻¹ = s ∧
      y ∈ Subgroup.centralizer ({c.t * s} : Set G) := by
  classical
  have htt : c.t * c.t = 1 := by
    simpa [pow_two] using c.t_involution.2
  have hss : s * s = 1 := by simpa [pow_two] using hsI.2
  have hprodSq : (c.t * s) ^ 2 = 1 := by
    rw [pow_two]
    calc
      (c.t * s) * (c.t * s) = c.t * (s * c.t) * s := by group
      _ = c.t * (c.t * s) * s := by rw [← hts.eq]
      _ = (c.t * c.t) * (s * s) := by group
      _ = 1 := by rw [htt, hss]; simp
  have hprodNe : c.t * s ≠ 1 := by
    intro hprod
    apply htsne
    calc
      c.t = c.t * 1 := by simp
      _ = c.t * (s * s) := by rw [hss]
      _ = (c.t * s) * s := by group
      _ = 1 * s := by rw [hprod]
      _ = s := by simp
  have hprodI : IsInvolution (c.t * s) := ⟨hprodNe, hprodSq⟩
  obtain ⟨a, ha⟩ :=
    fact_2_preamble_involutions_conjugate_proved
      hmin (c.t * s) c.t hprodI c.t_involution
  let Sa : Subgroup G := conjugateSubgroup (c.S : Subgroup G) a⁻¹
  have hSaC : Sa ≤ Subgroup.centralizer ({c.t * s} : Set G) := by
    intro x hx
    rcases (mem_conjugateSubgroup_iff (c.S : Subgroup G) a⁻¹ x).mp hx with
      ⟨q, hqS, rfl⟩
    have hqC : q ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact S_le_H c hqS
    have hqcomm : q * c.t = c.t * q :=
      Subgroup.mem_centralizer_singleton_iff.mp hqC
    have hback : c.t * s = a⁻¹ * c.t * a := by
      calc
        c.t * s = a⁻¹ * (a * (c.t * s) * a⁻¹) * a := by group
        _ = a⁻¹ * c.t * a := by rw [ha]
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [inv_inv]
    rw [hback]
    calc
      (a⁻¹ * q * a) * (a⁻¹ * c.t * a) =
          a⁻¹ * (q * c.t) * a := by group
      _ = a⁻¹ * (c.t * q) * a := by rw [hqcomm]
      _ = (a⁻¹ * c.t * a) * (a⁻¹ * q * a) := by group
  obtain ⟨eS⟩ := c.dihedralEquiv
  have hScard : Nat.card (↥(c.S : Subgroup G)) = 2 * 2 ^ c.m :=
    (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
  have h8S : 8 ∣ Nat.card (↥(c.S : Subgroup G)) := by
    rw [hScard]
    have hpow : 2 ^ 3 ∣ 2 ^ (c.m + 1) :=
      pow_dvd_pow 2 (by omega)
    simpa [pow_succ'] using hpow
  have h8C : 8 ∣ Nat.card
      (Subgroup.centralizer ({c.t * s} : Set G)) := by
    have hdvd := Subgroup.card_dvd_of_le hSaC
    rw [natCard_conjugateSubgroup] at hdvd
    exact h8S.trans hdvd
  exact
    exists_involution_conjugator_in_product_centralizer_of_dihedral_sylow
      c.S eS c.t s c.t_involution hsI hts htsne h8C

/-- The quotient-image calculation upgrades to the complete component
endpoint: the selected component is normal in `Ĥ`, contains `t`, fuses all
of its involutions to `t`, and every such involution has ambient centralizer
inside `Ĥ`. -/
public theorem Theorem26ComponentBranchData.pgl2_component_ambient_endpoint
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K) :
    let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
    Ei.Normal ∧
      c.t ∈ d.E ∧
      (∀ z : G, z ∈ d.E → IsInvolution z →
        ∃ g : G, g ∈ d.E ∧ g * z * g⁻¹ = c.t) ∧
      ∀ z : G, z ∈ d.E → IsInvolution z →
        Subgroup.centralizer ({z} : Set G) ≤ c.Hhat := by
  dsimp
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
  let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
  let Ebar : Subgroup (c.Hhat ⧸ O) := Ei.map q
  let f : Ei →* Ebar :=
    (q.comp Ei.subtype).codRestrict Ebar (fun x =>
      Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
  obtain ⟨_hcard, hEbarne, hEbarperf, _hEbarsn, hEbarL, hJeq⟩ :=
    d.pgl2_component_image_eq_commutator
      K hK L hLnormal hLindex e
  obtain ⟨hker, hcenterQuotient⟩ :=
    d.pgl2_component_kernel_eq_center
      K hK L hLnormal hLindex e
  have htbar : q ⟨c.t, ((S_le_H c).trans c.H_le_Hhat)
      (c.S0_le_S c.t_mem_S0)⟩ ∈ Ebar := by
    simpa [O, q, Ei, Ebar] using
      (d.pgl2_distinguished_involution_mem_component_image
        K hK L hLnormal hLindex e)
  have hOodd : Odd (Nat.card O) := by
    have hOcop : Nat.Coprime 2 (Nat.card O) := by
      simpa [O] using
        (pPrimeCore_coprime_card (p := 2) (G := c.Hhat))
    exact Nat.coprime_two_left.mp hOcop
  let eEi : Ei ≃* d.E :=
    Subgroup.subgroupOfEquivOfLe d.isComponent.1
  have hEiQ : IsQuasisimple Ei :=
    isQuasisimple_mulEquiv_local eEi.symm d.isComponent.2.2
  have hEcompTop : IsComponentOf Ei (⊤ : Subgroup c.Hhat) := by
    refine ⟨le_top, ?_, hEiQ⟩
    exact d.isComponent.2.1.subgroupOf
  have htH : c.t ∈ c.Hhat :=
    ((S_le_H c).trans c.H_le_Hhat)
      (c.S0_le_S c.t_mem_S0)
  have hcentralizer : Subgroup.centralizer ({c.t} : Set G) ≤ c.Hhat := by
    rw [← c.H_eq_centralizer]
    exact c.H_le_Hhat
  have hend :=
    component_normal_ambient_fusion_and_centralizers_of_pgl2_quotient_data
      c.Hhat Ei O hEcompTop (inferInstance : O.Normal) hOodd
      K hK L hLnormal e hcenterQuotient htH c.t_involution hcentralizer
      hEbarL hEbarne hEbarperf hJeq hker htbar
  have hEambient : Ei.map c.Hhat.subtype = d.E := by
    dsimp [Ei]
    exact Subgroup.map_subgroupOf_eq_of_le d.isComponent.1
  simpa [O, q, Ei, Ebar, f, hEambient] using hend

/-! ## Ambient reflected-torus transport -/

/-- Lift the model's outer torus involution back through the fixed Sylow
transport to an involution of `S` outside the selected component. -/
public theorem Theorem26ComponentBranchData.pgl2_outer_involution_lift
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G}
    (d : Theorem26ComponentBranchData c)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (e : L ≃* PGL2 K) :
    ∃ (Pmodel : Sylow 2 (PGL2 K))
      (eP : Pmodel ≃* DihedralGroup (2 ^ c.m))
      (T : PGL2LowReflectedToriData K Pmodel eP),
      ∃ sG : G, ∃ hsG_S : sG ∈ (c.S : Subgroup G),
        IsInvolution sG ∧ sG ∉ d.E ∧ Commute c.t sG ∧
          e ⟨QuotientGroup.mk' (pPrimeCore 2 c.Hhat)
              ⟨sG, ((S_le_H c).trans c.H_le_Hhat) hsG_S⟩,
            (sylow_le_of_normal_odd_index_local L hLnormal hLindex
              (let P : Sylow 2 c.Hhat :=
                c.S.subtype ((S_le_H c).trans c.H_le_Hhat)
               let Pq : Sylow 2 (c.Hhat ⧸ pPrimeCore 2 c.Hhat) :=
                P.mapSurjective (QuotientGroup.mk'_surjective
                  (pPrimeCore 2 c.Hhat))
               Pq))
            (Subgroup.mem_map.mpr ⟨
              ⟨sG, ((S_le_H c).trans c.H_le_Hhat) hsG_S⟩,
              hsG_S, rfl⟩)⟩ = T.g * T.s * T.g⁻¹ ∧
          e ⟨QuotientGroup.mk' (pPrimeCore 2 c.Hhat)
              ⟨c.t, ((S_le_H c).trans c.H_le_Hhat)
                (c.S0_le_S c.t_mem_S0)⟩,
            (sylow_le_of_normal_odd_index_local L hLnormal hLindex
              (let P : Sylow 2 c.Hhat :=
                c.S.subtype ((S_le_H c).trans c.H_le_Hhat)
               let Pq : Sylow 2 (c.Hhat ⧸ pPrimeCore 2 c.Hhat) :=
                P.mapSurjective (QuotientGroup.mk'_surjective
                  (pPrimeCore 2 c.Hhat))
               Pq))
            (Subgroup.mem_map.mpr ⟨
              ⟨c.t, ((S_le_H c).trans c.H_le_Hhat)
                (c.S0_le_S c.t_mem_S0)⟩,
              c.S0_le_S c.t_mem_S0, rfl⟩)⟩ = T.g * T.t * T.g⁻¹ := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup c.Hhat := pPrimeCore 2 c.Hhat
  let q : c.Hhat →* c.Hhat ⧸ O := QuotientGroup.mk' O
  let Ei : Subgroup c.Hhat := d.E.subgroupOf c.Hhat
  let Ebar : Subgroup (c.Hhat ⧸ O) := Ei.map q
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hSle : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 c.Hhat := c.S.subtype hSle
  let Pq : Sylow 2 (c.Hhat ⧸ O) :=
    P.mapSurjective (QuotientGroup.mk'_surjective O)
  have hPqL : (Pq : Subgroup (c.Hhat ⧸ O)) ≤ L :=
    sylow_le_of_normal_odd_index_local L hLnormal hLindex Pq
  let PL : Sylow 2 L := Pq.subtype hPqL
  let Pmodel : Sylow 2 (PGL2 K) :=
    PL.mapSurjective (f := e.toMonoidHom) e.surjective
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using (pPrimeCore_coprime_card (p := 2) (G := c.Hhat))
  obtain ⟨_hm2, eTransport, _ePtransport, _tModel, _htModelVal, _htModelCentral,
      heTransport⟩ :=
    pgl2_model_sylow_transport_distinguished_involution
      c O hOcop K hK L e hPqL
  obtain ⟨hcard, _hEbarne, _hEbarperf, _hEbarsn, hEbarL, hJeq⟩ :=
    d.pgl2_component_image_eq_commutator K hK L hLnormal hLindex e
  obtain ⟨T⟩ := pgl2_low_reflected_tori_card_four K hK hcard Pmodel _ePtransport
  let sP : Pmodel := ⟨T.g * T.s * T.g⁻¹, T.conj_s_mem_P⟩
  let sHatP : P := eTransport.symm sP
  let sHat : c.Hhat := (sHatP : c.Hhat)
  let sG : G := (sHat : G)
  have hsG_S : sG ∈ (c.S : Subgroup G) := by
    exact sHatP.2
  have hsP_ne : sP ≠ 1 := by
    intro h
    apply T.s_involution.1
    have hval : T.g * T.s * T.g⁻¹ = 1 := congrArg Subtype.val h
    calc
      T.s = T.g⁻¹ * (T.g * T.s * T.g⁻¹) * (T.g⁻¹)⁻¹ := by group
      _ = 1 := by rw [hval]; simp
  have hsP_sq : sP * sP = 1 := by
    apply Subtype.ext
    change (T.g * T.s * T.g⁻¹) * (T.g * T.s * T.g⁻¹) = 1
    calc
      (T.g * T.s * T.g⁻¹) * (T.g * T.s * T.g⁻¹) =
          T.g * (T.s * T.s) * T.g⁻¹ := by group
      _ = 1 := by
        have hss : T.s * T.s = 1 := by
          simpa [pow_two] using T.s_involution.2
        rw [hss]
        simp
  have hsP_I : IsInvolution sP :=
    ⟨hsP_ne, by simpa [pow_two] using hsP_sq⟩
  have hsHatP_ne : (sHatP : P) ≠ 1 := by
    intro h
    exact hsP_ne (by
      dsimp [sHatP] at h
      have h0 : eTransport (eTransport.symm sP) = eTransport 1 :=
        congrArg eTransport h
      have hsP_one : sP = 1 := by
        calc
          sP = eTransport (eTransport.symm sP) :=
            (eTransport.apply_symm_apply sP).symm
          _ = eTransport 1 := h0
          _ = 1 := eTransport.map_one
      exact hsP_one)
  have hsHatP_sq : (sHatP : P) ^ 2 = 1 := by
    dsimp [sHatP]
    calc
      (eTransport.symm sP) ^ 2 = eTransport.symm (sP * sP) := by
        rw [pow_two, ← map_mul]
      _ = eTransport.symm 1 := congrArg eTransport.symm hsP_sq
      _ = 1 := eTransport.symm.map_one
  have hsHatP_I : IsInvolution sHatP :=
    ⟨hsHatP_ne, by simpa [pow_two] using hsHatP_sq⟩
  have hsHat_I : IsInvolution sHat := by
    constructor
    · intro h
      exact hsHatP_I.1 (Subtype.ext h)
    · change (sHat : c.Hhat) ^ 2 = 1
      exact congrArg Subtype.val hsHatP_I.2
  have hsG_I : IsInvolution sG := by
    constructor
    · intro h
      exact hsHat_I.1 (Subtype.ext h)
    · exact congrArg Subtype.val hsHat_I.2
  have hcomm : Commute c.t sG := by
    change c.t * sG = sG * c.t
    have ht := t_mem_center_S c sG hsG_S
    have htin : c.t⁻¹ = c.t :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using c.t_involution.2)
    calc
      c.t * sG = (c.t * sG) * (c.t⁻¹ * c.t) := by group
      _ = (c.t * sG * c.t⁻¹) * c.t := by group
      _ = sG * c.t := by rw [ht]
  let sH : c.Hhat := ⟨sG, hSle hsG_S⟩
  let tH : c.Hhat := ⟨c.t, hSle (c.S0_le_S c.t_mem_S0)⟩
  let sL : L := ⟨q sH, hPqL (Subgroup.mem_map.mpr ⟨sH, hsG_S, rfl⟩)⟩
  let tL : L := ⟨q tH, hPqL (Subgroup.mem_map.mpr
    ⟨tH, c.S0_le_S c.t_mem_S0, rfl⟩)⟩
  have hesL : e sL = (sP : PGL2 K) := by
    have h := heTransport sHatP
    have hsym : eTransport sHatP = sP := by
      dsimp [sHatP]
      exact eTransport.apply_symm_apply sP
    rw [hsym] at h
    dsimp [sH, sL, sHat, sG]
    exact h.symm
  have hs0eq : e sL = T.g * T.s * T.g⁻¹ := by
    simpa [sP] using hesL
  have ht0eq : e tL = T.g * T.t * T.g⁻¹ := by
    calc
      e tL = (_tModel : PGL2 K) := by
        simpa [tL, tH, q, O] using _htModelVal.symm
      _ = T.g * T.t * T.g⁻¹ := by
        calc
          (_tModel : PGL2 K) =
              (_ePtransport.symm (DihedralGroup.r
                (2 ^ (c.m - 1) : ZMod (2 ^ c.m))) : PGL2 K) := by
            exact congrArg Subtype.val _htModelCentral
          _ = T.g * T.t * T.g⁻¹ := T.conj_t_eq_central.symm
  have hsG_notE : sG ∉ d.E := by
    intro hsE
    have hsHatEi : sHat ∈ Ei := Subgroup.mem_subgroupOf.mpr hsE
    have hsHatqEbar : q sHat ∈ Ebar := by
      exact Subgroup.mem_map.mpr ⟨sHat, hsHatEi, rfl⟩
    have hsHatqPq : q sHat ∈ (Pq : Subgroup (c.Hhat ⧸ O)) := by
      change q sHat ∈ (P : Subgroup c.Hhat).map q
      exact Subgroup.mem_map.mpr ⟨sHat, sHatP.2, rfl⟩
    have hsL_eq : sL = ⟨q sHat, hPqL hsHatqPq⟩ := by
      have hsH : sH = sHat := by
        apply Subtype.ext
        rfl
      dsimp [sL, sH, sHat, sG]
    have hsP_J : (sP : PGL2 K) ∈ J := by
      have hsL_Ebar : sL ∈ Ebar.subgroupOf L :=
        Subgroup.mem_subgroupOf.mpr hsHatqEbar
      have hsL_map : e sL ∈ (Ebar.subgroupOf L).map e.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨sL, hsL_Ebar, rfl⟩
      have hsL_J : e sL ∈ J := by
        simpa [J] using hJeq ▸ hsL_map
      simpa [J] using (hesL.symm ▸ hsL_J)
    have hs_J : T.s ∈ J := by
      have hback :=
        (inferInstance : J.Normal).conj_mem
          (sP : PGL2 K) hsP_J T.g⁻¹
      simpa [sP, J, mul_assoc] using hback
    exact T.s_not_mem_commutator hs_J
  exact ⟨Pmodel, _ePtransport, T, sG, hsG_S,
    hsG_I, hsG_notE, hcomm, hs0eq, ht0eq⟩

/-- The commutator of two subgroups of `E` lies in `E`. -/
public theorem commutator_le_of_le_t26 {G : Type u} [Group G]
    (A B E : Subgroup G) (hA : A ≤ E) (hB : B ≤ E) :
    ⁅A, B⁆ ≤ E := by
  rw [Subgroup.commutator_le]
  intro g hg c hc
  have hgE : g ∈ E := hA hg
  have hcE : c ∈ E := hB hc
  have hgi : g⁻¹ ∈ E := E.inv_mem hgE
  have hci : c⁻¹ ∈ E := E.inv_mem hcE
  have hgc : g * c ∈ E := E.mul_mem hgE hcE
  have hmid : (g * c) * (g⁻¹ * c⁻¹) ∈ E :=
    E.mul_mem hgc (E.mul_mem hgi hci)
  simpa [commutatorElement_def, mul_assoc] using hmid

/-- For commuting involutions `t,s` and an involution `y` conjugating `t` to
`s`, the reflected commutator `[⟨t⟩, C_E(s)]` lies in `E`, in `Ĥ`, and in
`Ĥ^y`.  This is the free half of the source's reflected-torus containment. -/
public theorem reflected_R_le_inter_of_conjugator_t26
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (E : Subgroup G)
    {s y : G} (htE : c.t ∈ E) (hEH : E ≤ c.Hhat)
    (hsS : s ∈ (c.S : Subgroup G))
    (hyts : y * c.t * y⁻¹ = s) (hy2 : y * y = 1) :
    let CEs : Subgroup G := Subgroup.centralizer ({s} : Set G) ⊓ E
    let R : Subgroup G := ⁅Subgroup.zpowers c.t, CEs⁆
    R ≤ E ∧ R ≤ c.Hhat ∧ R ≤ conjugateSubgroup c.Hhat y := by
  classical
  intro CEs R
  have hsC : s ∈ Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
    exact S_le_H c hsS
  have hM : Subgroup.centralizer ({c.t} : Set G) ≤ c.Hhat := by
    rw [← c.H_eq_centralizer]
    exact c.H_le_Hhat
  have hRE : R ≤ E := by
    dsimp [R, CEs]
    exact commutator_le_of_le_t26 (Subgroup.zpowers c.t) CEs E
      (Subgroup.zpowers_le.mpr htE) inf_le_right
  have hRM : R ≤ c.Hhat := hRE.trans hEH
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hty : c.t = y⁻¹ * s * y := by
    calc
      c.t = y⁻¹ * (y * c.t * y⁻¹) * y := by group
      _ = y⁻¹ * s * y := by rw [hyts]
  have hmap : R.map (MulAut.conj y).toMonoidHom =
      ⁅Subgroup.zpowers s, CEs.map (MulAut.conj y).toMonoidHom⁆ := by
    dsimp [R, CEs]
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, hyts]
  have hCEsy : CEs.map (MulAut.conj y).toMonoidHom ≤
      Subgroup.centralizer ({c.t} : Set G) := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨z0, hz0, hz⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz0C : z0 ∈ Subgroup.centralizer ({s} : Set G) :=
      (inf_le_left : CEs ≤ Subgroup.centralizer ({s} : Set G)) hz0
    have hz0s : z0 * s = s * z0 :=
      Subgroup.mem_centralizer_singleton_iff.mp hz0C
    have hzv : z = y * z0 * y⁻¹ := by
      simpa [MulAut.conj_apply] using hz.symm
    subst z
    change (y * z0 * y⁻¹) * c.t = c.t * (y * z0 * y⁻¹)
    calc
      (y * z0 * y⁻¹) * c.t = (y * z0 * y) * c.t := by rw [hyinv]
      _ = (y * z0 * y) * (y⁻¹ * s * y) := by rw [hty]
      _ = y * (z0 * s) * y := by
        rw [hyinv]
        calc
          (y * z0 * y) * (y * s * y) = y * z0 * (y * y) * s * y := by group
          _ = y * (z0 * s) * y := by rw [hy2]; simp [mul_assoc]
      _ = y * (s * z0) * y := by rw [hz0s]
      _ = c.t * (y * z0 * y⁻¹) := by
        rw [hty, hyinv]
        calc
          y * (s * z0) * y = y * s * z0 * y := by group
          _ = y * s * 1 * z0 * y := by simp
          _ = y * s * (y * y) * z0 * y := by rw [← hy2]
          _ = (y * s * y) * (y * z0 * y) := by group
  have hsCz : Subgroup.zpowers s ≤
      Subgroup.centralizer ({c.t} : Set G) :=
    Subgroup.zpowers_le.mpr hsC
  have hRyC : R.map (MulAut.conj y).toMonoidHom ≤
      Subgroup.centralizer ({c.t} : Set G) := by
    rw [hmap]
    exact commutator_le_of_le_t26 (Subgroup.zpowers s)
      (CEs.map (MulAut.conj y).toMonoidHom)
      (Subgroup.centralizer ({c.t} : Set G)) hsCz hCEsy
  have hRyM : R.map (MulAut.conj y).toMonoidHom ≤ c.Hhat := hRyC.trans hM
  refine ⟨hRE, hRM, ?_⟩
  intro x hx
  have hxy : y * x * y⁻¹ ∈ c.Hhat :=
    hRyM (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  refine (mem_conjugateSubgroup_iff c.Hhat y x).mpr
    ⟨y * x * y⁻¹, hxy, ?_⟩
  calc
    x = (y * y) * x * (y⁻¹ * y⁻¹) := by simp [hy2, hyinv]
    _ = y * (y * x * y⁻¹) * y⁻¹ := by group

/-- An involutory normalizer of a finite subgroup fixes some Sylow
`2`-subgroup of that subgroup.  This is the Frattini-style input for the
final large-intersection contradiction. -/
public theorem exists_invariant_sylow_two_of_involutive_normalizer_t26
    {G : Type u} [Group G] [Finite G] (B : Subgroup G) {y : G}
    (hyN : y ∈ Subgroup.normalizer (B : Set G)) (hy2 : y * y = 1) :
    ∃ T : Sylow 2 B, ∀ x : B, x ∈ T → ⟨y * (x : G) * y⁻¹,
      ((Subgroup.mem_normalizer_iff.mp hyN) (x : G)).mp x.2⟩ ∈ T := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : B →* B :=
    { toFun := fun x => ⟨y * (x : G) * y⁻¹,
        ((Subgroup.mem_normalizer_iff.mp hyN) (x : G)).mp x.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        simp [mul_assoc] }
  have hfinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have hval : y * (a : G) * y⁻¹ = y * (b : G) * y⁻¹ := by
      simpa [f] using congrArg Subtype.val h
    calc
      (a : G) = y⁻¹ * (y * (a : G) * y⁻¹) * (y⁻¹)⁻¹ := by group
      _ = y⁻¹ * (y * (b : G) * y⁻¹) * (y⁻¹)⁻¹ := by rw [hval]
      _ = (b : G) := by group
  have hfsurj : Function.Surjective f := by
    intro b
    have hyinvN : y⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
      (Subgroup.normalizer (B : Set G)).inv_mem hyN
    have hmem : y⁻¹ * (b : G) * y ∈ B := by
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      have h0 := ((Subgroup.mem_normalizer_iff.mp hyinvN) (b : G)).mp b.2
      simpa [hyinv] using h0
    refine ⟨⟨y⁻¹ * (b : G) * y, hmem⟩, ?_⟩
    ext
    have hyinv' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    change y * (y⁻¹ * (b : G) * y) * y⁻¹ = (b : G)
    rw [hyinv']
    calc
      y * (y * (b : G) * y) * y = (y * y) * (b : G) * (y * y) := by group
      _ = (b : G) := by rw [hy2]; simp
  let φ : B ≃* B := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  let σ : Equiv.Perm (Sylow 2 B) :=
    { toFun := fun T => T.mapSurjective (f := φ.toMonoidHom) φ.toEquiv.surjective
      invFun := fun T => T.mapSurjective (f := φ.symm.toMonoidHom) φ.symm.toEquiv.surjective
      left_inv := by
        intro T
        apply Sylow.ext
        change (((T : Subgroup B).map φ.toMonoidHom).map φ.symm.toMonoidHom) = T
        rw [Subgroup.map_map]
        have hφφ : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id B := by
          ext x
          simpa using congrArg Subtype.val (φ.left_inv x)
        rw [hφφ, Subgroup.map_id]
      right_inv := by
        intro T
        apply Sylow.ext
        change (((T : Subgroup B).map φ.symm.toMonoidHom).map φ.toMonoidHom) = T
        rw [Subgroup.map_map]
        have hφφ : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id B := by
          ext x
          simpa using congrArg Subtype.val (φ.right_inv x)
        rw [hφφ, Subgroup.map_id] }
  have hσsq : σ ^ 2 = 1 := by
    apply DFunLike.ext
    intro T
    apply Sylow.ext
    change (((T : Subgroup B).map φ.toMonoidHom).map φ.toMonoidHom) = T
    rw [Subgroup.map_map]
    have hφsq : φ.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id B := by
      ext x
      dsimp [φ]
      change y * (y * (x : G) * y⁻¹) * y⁻¹ = (x : G)
      rw [hyinv]
      calc
        y * (y * (x : G) * y) * y = (y * y) * (x : G) * (y * y) := by group
        _ = (x : G) := by rw [hy2]; simp
    rw [hφsq, Subgroup.map_id]
  let : Fintype (Sylow 2 B) := Fintype.ofFinite (Sylow 2 B)
  have hcardmod : Nat.card (Sylow 2 B) ≡ 1 [MOD 2] :=
    card_sylow_modEq_one (p := 2) (G := B)
  have hnot2 : ¬ 2 ∣ Fintype.card (Sylow 2 B) := by
    intro h
    have hzero : Nat.card (Sylow 2 B) ≡ 0 [MOD 2] :=
      (Nat.modEq_zero_iff_dvd (n := 2)).2 (by simpa [Nat.card_eq_fintype_card] using h)
    have hone : (1 : ℕ) ≡ 0 [MOD 2] := hcardmod.symm.trans hzero
    norm_num at hone
  obtain ⟨T, hT⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1)
    (by simpa [Nat.card_eq_fintype_card] using hnot2) (σ := σ) hσsq
  refine ⟨T, ?_⟩
  intro x hx
  have hfixed : σ T = T := hT
  have hmem : (x : B) ∈ (σ T : Sylow 2 B) := by
    rwa [hfixed]
  have hfsurjφ : Function.Surjective (φ.toMonoidHom) := φ.surjective
  have hmap : (x : B) ∈
      (T.mapSurjective (f := φ.toMonoidHom) hfsurjφ : Sylow 2 B) := by
    simpa [σ] using hmem
  have hmap'' : (x : B) ∈
      ((T.mapSurjective hfsurjφ : Sylow 2 B) : Subgroup B) := hmap
  have hmap' : (x : B) ∈ (T : Subgroup B).map φ.toMonoidHom := by
    rwa [Sylow.coe_mapSurjective hfsurjφ T] at hmap''
  rcases Subgroup.mem_map.mp hmap' with ⟨z, hz, hzv⟩
  have hzv' : f z = x := by
    exact Subtype.ext (congrArg Subtype.val hzv)
  have hgoal : f x ∈ T := by
    rw [← hzv']
    have hfz : f (f z) = z := by
      apply Subtype.ext
      change y * (y * (z : G) * y⁻¹) * y⁻¹ = (z : G)
      rw [hyinv]
      calc
        y * (y * (z : G) * y) * y = (y * y) * (z : G) * (y * y) := by group
        _ = (z : G) := by rw [hy2]; simp
    rw [hfz]
    exact hz
  exact hgoal

/-- The final contradiction of the component branch: an involution `y`
normalizing `B := Ĥ ⊓ Ĥ^y` with `8 ∣ |B|` centralizes an involution of `E`,
whose centralizer is contained in `Ĥ`, contrary to `y ∉ Ĥ`. -/
public theorem component_branch_final_contradiction_t26
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (E : Subgroup G) {s y : G}
    (hm2 : 2 ≤ c.m)
    (htE : c.t ∈ E) (hsE : s ∉ E)
    (hEamb : ∀ {h x : G}, h ∈ c.Hhat → x ∈ E → h * x * h⁻¹ ∈ E)
    (hcent : ∀ z : G, z ∈ E → IsInvolution z →
      Subgroup.centralizer ({z} : Set G) ≤ c.Hhat)
    (hyI : IsInvolution y) (hyts : y * c.t * y⁻¹ = s)
    (h8 : 8 ∣ Nat.card ↥(c.Hhat ⊓ conjugateSubgroup c.Hhat y)) :
    False := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
  have hy2 : y * y = 1 := by simpa [pow_two] using hyI.2
  have hyN : y ∈ Subgroup.normalizer (B : Set G) := by
    simpa [B] using
      (involution_mem_normalizer_inf_conjugateSubgroup c.Hhat hy2)
  obtain ⟨T, hTinv⟩ :=
    exists_invariant_sylow_two_of_involutive_normalizer_t26 B hyN hy2
  let T0 : Subgroup G := (T : Subgroup B).map B.subtype
  have hT0leB : T0 ≤ B := Subgroup.map_subtype_le (T : Subgroup B)
  have hT0leH : T0 ≤ c.Hhat := hT0leB.trans (inf_le_left : B ≤ c.Hhat)
  have hT0p : IsPGroup 2 T0 := by
    dsimp [T0]
    exact T.isPGroup'.map B.subtype
  have hT0card : Nat.card T0 = Nat.card (T : Subgroup B) := by
    dsimp [T0]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective (T : Subgroup B) B.subtype
        Subtype.coe_injective).toEquiv).symm
  have hfac : 3 ≤ (Nat.card B).factorization 2 := by
    apply (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (Nat.card_pos (α := B)).ne').mp
    simpa [B] using h8
  have hT0ge : 8 ≤ Nat.card T0 := by
    rw [hT0card, T.card_eq_multiplicity]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2 hfac
  obtain ⟨QH, hT0QH⟩ :=
    IsPGroup.exists_le_sylow (G := c.Hhat) (p := 2)
      (by
        let e : (T0.subgroupOf c.Hhat) ≃* T0 :=
          Subgroup.subgroupOfEquivOfLe hT0leH
        exact IsPGroup.of_equiv hT0p e.symm)
  have hSle : (c.S : Subgroup G) ≤ c.Hhat :=
    (S_le_H c).trans c.H_le_Hhat
  let P : Sylow 2 c.Hhat := c.S.subtype hSle
  obtain ⟨h, hh⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq c.Hhat (Sylow 2 c.Hhat)
      inferInstance inferInstance QH P
  let g : c.Hhat := h⁻¹
  let Sg : Subgroup G := conjugateSubgroup (c.S : Subgroup G) g
  have hT0Sg : T0 ≤ Sg := by
    intro x hx
    have hxQ : (⟨x, hT0leH hx⟩ : c.Hhat) ∈ (QH : Subgroup c.Hhat) := by
      have hxT0H : (⟨x, hT0leH hx⟩ : c.Hhat) ∈ T0.subgroupOf c.Hhat :=
        Subgroup.mem_subgroupOf.mpr hx
      exact hT0QH hxT0H
    have hxP : (h * ⟨x, hT0leH hx⟩ * h⁻¹ : c.Hhat) ∈
        (P : Subgroup c.Hhat) := by
      have hQ : (h * ⟨x, hT0leH hx⟩ * h⁻¹ : c.Hhat) ∈
          ((h • QH : Sylow 2 c.Hhat) : Subgroup c.Hhat) := by
        change (MulAut.conj h) ⟨x, hT0leH hx⟩ ∈
          ((QH : Subgroup c.Hhat).map
            (MulAut.conj h).toMonoidHom)
        exact Subgroup.mem_map.mpr ⟨⟨x, hT0leH hx⟩, hxQ, rfl⟩
      simpa using (by rw [hh] at hQ; exact hQ)
    have hxS : ((h * ⟨x, hT0leH hx⟩ * h⁻¹ : c.Hhat) : G) ∈
        (c.S : Subgroup G) := by
      change ((h * ⟨x, hT0leH hx⟩ * h⁻¹ : c.Hhat) : G) ∈ (c.S : Subgroup G)
      exact hxP
    change x ∈ (conjugateSubgroup (c.S : Subgroup G) g)
    rw [conjugateSubgroup, Subgroup.mem_map]
    refine ⟨((h * ⟨x, hT0leH hx⟩ * h⁻¹ : c.Hhat) : G), hxS, ?_⟩
    have hgval : (g : G) = (h : G)⁻¹ := by
      simp [g, Subgroup.coe_inv]
    rw [hgval]
    change (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * ((h : G)⁻¹)⁻¹ = x
    simp
    group
  obtain ⟨eS⟩ := c.dihedralEquiv
  let eSg : Sg ≃* DihedralGroup (2 ^ c.m) :=
    (Subgroup.equivMapOfInjective (c.S : Subgroup G)
      (MulAut.conj (g : G)).toMonoidHom (MulAut.conj (g : G)).injective).symm.trans eS
  let z : G := g * c.t * g⁻¹
  have hzSg : z ∈ Sg := by
    change z ∈ (conjugateSubgroup (c.S : Subgroup G) g)
    rw [conjugateSubgroup, Subgroup.mem_map]
    refine ⟨c.t, c.S0_le_S c.t_mem_S0, ?_⟩
    simp [MulAut.conj_apply, z]
  have hzI : IsInvolution z := by
    constructor
    · intro hz1
      apply c.t_involution.1
      have hval : (g : G)⁻¹ * (g * c.t * (g : G)⁻¹) * (g : G) = 1 := by
        change (g : G)⁻¹ * z * (g : G) = 1
        rw [hz1]
        simp
      calc
        c.t = (g : G)⁻¹ * (g * c.t * (g : G)⁻¹) * (g : G) := by
          simp [Subgroup.coe_inv, Subgroup.coe_mul, mul_assoc]
        _ = 1 := hval
    · calc
        z ^ 2 = g * (c.t ^ 2) * g⁻¹ := by
          simp [z, pow_two, mul_assoc]
        _ = 1 := by
          rw [show c.t ^ 2 = 1 by simpa [pow_two] using c.t_involution.2]
          simp
  have hzcenter : (⟨z, hzSg⟩ : Sg) ∈ Subgroup.center Sg := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    rcases (Subgroup.mem_map.mp x.2) with ⟨w, hw, hx⟩
    change (x : G) * z = z * (x : G)
    rw [← hx]
    dsimp [z]
    have hcomm : c.t * w = w * c.t := by
      have ht := t_mem_center_S c w hw
      calc
        c.t * w = c.t * w * c.t⁻¹ * c.t := by group
        _ = w * c.t := by rw [ht]
    calc
      ((g : G) * w * (g : G)⁻¹) * ((g : G) * c.t * (g : G)⁻¹) =
          (g : G) * (w * c.t) * (g : G)⁻¹ := by group
      _ = (g : G) * (c.t * w) * (g : G)⁻¹ := by rw [hcomm]
      _ = ((g : G) * c.t * (g : G)⁻¹) * ((g : G) * w * (g : G)⁻¹) := by group
  have hzT0 : z ∈ T0 :=
    central_involution_mem_large_subgroup_of_dihedral
      Sg T0 hT0Sg hm2 eSg hzSg hzI hzcenter hT0ge
  have hT0_fwd : ∀ u : G, u ∈ T0 → y * u * y⁻¹ ∈ T0 := by
    intro u hu
    rcases Subgroup.mem_map.mp hu with ⟨x, hx, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨⟨y * (x : G) * y⁻¹,
        ((Subgroup.mem_normalizer_iff.mp hyN) (x : G)).mp x.2⟩, hTinv x hx, rfl⟩
  have hyNT0 : y ∈ Subgroup.normalizer (T0 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hT0_fwd w
    · intro hw
      have hw' := hT0_fwd (y * w * y⁻¹) hw
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      have hw_eq : y * (y * w * y) * y = w := by
        calc
          y * (y * w * y) * y = (y * y) * w * (y * y) := by group
          _ = w := by rw [hy2]; simp
      simpa [hyinv, hw_eq] using hw'
  have hyz : y * z * y⁻¹ = z :=
    normalizer_fixes_central_involution_of_large_subgroup_of_dihedral
      Sg T0 hT0Sg hm2 eSg hzSg hzT0 hzI hzcenter hT0ge hyNT0
  have hzE : z ∈ E := by
    have hzconj : z = g * c.t * g⁻¹ := rfl
    simpa [hzconj] using hEamb g.2 htE
  have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have hstep : (y * z * y) * y = y * z := by
      rw [mul_assoc, hy2, mul_one]
    calc
      y * z = (y * z * y) * y := hstep.symm
      _ = z * y := by
        rw [show y * z * y = z by simpa [hyinv] using hyz]
  have hyH : y ∈ c.Hhat := (hcent z hzE hzI) hyC
  have hsE' : s ∈ E := by
    simpa [hyts] using hEamb hyH htE
  exact hsE hsE'

/-- Once the surviving `PGL₂` constructor is ruled out for the selected
component, the layer of `Ĥ` is trivial.  This packages the already completed
classification pruning (two-group quotient, `A₇`, and `PSL₂`) so that the
remaining source argument has exactly one model-shaped input. -/
public theorem componentLayerOf_eq_bot_of_pgl2_model_impossible
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hO2 : twoCoreOf c.Hhat = ⊥)
    (hPGL : ∀ (_d : Theorem26ComponentBranchData c)
        (K : Type u) [Field K] [Finite K]
        (_hK : IsOddPrimePower (Nat.card K))
        (L : Subgroup (c.Hhat ⧸ pPrimeCore 2 c.Hhat))
        (_hLnormal : L.Normal) (_hLindex : Odd L.index)
        (_e : L ≃* PGL2 K), False) :
    componentLayerOf c.Hhat = ⊥ := by
  by_contra hE
  rcases exists_theorem26ComponentBranchData hmin c hO2 hE with ⟨d⟩
  rcases d.hhat_isDGroup with
      ⟨_hSylow, hQ⟩ | ⟨_hSylow, hASeven⟩ |
        ⟨_hSylow, K, hK, L, hLnormal, hLindex, hlinear⟩
  · exact d.not_quotientIsTwoGroup hQ
  · exact d.not_quotientIsASeven hASeven
  · rcases hlinear with hPSL | hPGLModel
    · exact d.not_linearModelPSL2 K hK L hLnormal hLindex hPSL.some
    · exact hPGL d K hK L hLnormal hLindex hPGLModel.some

/-- Final structure after the component layer has been shown trivial. -/
public theorem theorem_2_6_structure_of_component_trivial
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hE : componentLayerOf c.Hhat = ⊥) :
    CentralizerStructure c := by
  by_cases hO2 : twoCoreOf c.Hhat ≠ ⊥
  · exact theorem_2_6_branch_one hmin c hO2
  · have hO2bot : twoCoreOf c.Hhat = ⊥ := not_not.mp hO2
    have hodd : ∀ p : ℕ, p.Prime → Odd p →
        c.t ∈ Subgroup.centralizer (qCoreOf c.Hhat p : Set G) := by
      intro p hp hpodd
      exact mem_centralizer_qCoreOf_of_minimalCounterexample hmin c p hp hpodd
    have htF : c.t ∈
        Subgroup.centralizer (fittingSubgroupOf c.Hhat : Set G) :=
      mem_centralizer_fittingSubgroupOf_of_mem_centralizer_odd_qCores_of_twoCoreOf_eq_bot
        c.Hhat c.t hO2bot hodd
    exact False.elim
      ((twoCoreOf_ne_bot_of_involution_centralizes_fitting_of_componentLayer_eq_bot
          c.Hhat c.t
          (c.H_le_Hhat (S_le_H c (c.S0_le_S c.t_mem_S0)))
          c.t_involution hE htF) hO2bot)

end CFSG.GorensteinWalter
