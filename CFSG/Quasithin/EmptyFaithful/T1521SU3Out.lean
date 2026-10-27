module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.Quasithin.U31521

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.OutStructure
open CFSG.Assembly.LowTwoRank

section PrimeForm

variable {f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 f K)

theorem odd_two_pow_add_one_of_pos (hf : 1 ≤ f) : Odd (2 ^ f + 1) :=
  (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one

theorem mem_inner_of_mem_primeFormD_of_pow_aux (C : GL (Fin n) K)
    {β : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))}
    (hβD : β ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K)) {k : ℕ} (hβk : β ^ 2 ^ k = 1) :
    β ∈ inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
  set D := primeFormD h (C : Matrix (Fin n) (Fin n) K) with hD
  set I := (inner (primeFormP h (C : Matrix (Fin n) (Fin n) K))).subgroupOf D with hI
  set x : D ⧸ I := ((⟨β, hβD⟩ : D) : D ⧸ I) with hx
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    rw [hx, ← QuotientGroup.mk_pow]
    have : (⟨β, hβD⟩ : D) ^ 2 ^ k = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, hβk, OneMemClass.coe_one])
    rw [this, QuotientGroup.mk_one])
  have h2 : orderOf x ∣ 2 ^ f + 1 :=
    (orderOf_dvd_natCard x).trans (card_primeFormD_quotient_dvd h C)
  have hcop : Nat.Coprime (2 ^ k) (2 ^ f + 1) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).2 (odd_two_pow_add_one_of_pos h.one_le))
  have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, hx, QuotientGroup.eq_one_iff, hI, mem_subgroupOf] at h3
  exact h3

theorem inner_le_primeFormD_aux (C : Matrix (Fin n) (Fin n) K) :
    inner (primeFormP h C) ≤ primeFormD h C := by
  intro α hα
  obtain ⟨s, rfl⟩ := (mem_inner_primeFormP h C α).1 hα
  exact ⟨_, rfl⟩

include h in
theorem isCyclic_ringAut_aux : IsCyclic (K ≃+* K) := by
  have := h.finite
  exact (card_ringAut_and_isCyclic Nat.prime_two K h.card).2

theorem isCyclic_map_outer_primeFormP_aux (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    {B : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)))} (hB : IsPGroup 2 B) :
    IsCyclic (B.map (QuotientGroup.mk' (inner (primeFormP h (C : Matrix (Fin n) (Fin n) K))))) := by
  set P := primeFormP h (C : Matrix (Fin n) (Fin n) K)
  set F := primeFormFieldFactor h hC hn hq with hF
  have hker : F.ker = primeFormD h (C : Matrix (Fin n) (Fin n) K) :=
    ker_primeFormFieldFactor h hC hn hq
  have hinn : inner P ≤ F.ker := by
    rw [hker]
    exact inner_le_primeFormD_aux h _
  set Fbar : Outer P →* (K ≃+* K) := QuotientGroup.lift (inner P) F hinn with hFbar
  set I := B.map (QuotientGroup.mk' (inner P)) with hI
  have := isCyclic_ringAut_aux h
  refine isCyclic_of_injective (Fbar.comp I.subtype) ?_
  rw [injective_iff_map_eq_one]
  rintro ⟨x, hx⟩ hι
  obtain ⟨β, hβB, rfl⟩ := mem_map.1 hx
  have hFβ : F β = 1 := by
    have e : Fbar (QuotientGroup.mk' (inner P) β) = F β := QuotientGroup.lift_mk _ _ _
    rw [← e]
    exact hι
  have hβD : β ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K) := by
    rw [← hker]
    exact hFβ
  obtain ⟨k, hk⟩ := hB ⟨β, hβB⟩
  have hβk : β ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
  have hβi := mem_inner_of_mem_primeFormD_of_pow_aux h C hβD hβk
  apply Subtype.ext
  change QuotientGroup.mk' (inner P) β = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hβi

end PrimeForm

theorem isCyclic_map_outer_of_mulEquiv_aux {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ B : Subgroup (MulAut Y), IsPGroup 2 B →
      IsCyclic (B.map (QuotientGroup.mk' (inner Y))))
    (B : Subgroup (MulAut X)) (hB : IsPGroup 2 B) :
    IsCyclic (B.map (QuotientGroup.mk' (inner X))) := by
  set I := B.map (QuotientGroup.mk' (inner X)) with hI
  set J := (B.map (MulAut.congr e).toMonoidHom).map (QuotientGroup.mk' (inner Y)) with hJ
  have e1 : I.map (equivalence e).toMonoidHom = J := by
    rw [hI, hJ, map_map, map_map]
    rfl
  have hcyc : IsCyclic J := hY _ (hB.map (MulAut.congr e).toMonoidHom)
  have hcyc' : IsCyclic (I.map (equivalence e).toMonoidHom) := by rw [e1]; exact hcyc
  exact @isCyclic_of_injective _ _ _ _ hcyc'
    (I.equivMapOfInjective (equivalence e).toMonoidHom (equivalence e).injective).toMonoidHom
    (MulEquiv.injective _)

theorem cyclic_map_outer_of_isPGroup {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hX : IsPSU 3 2 n X) {B : Subgroup (MulAut X)} (hB : IsPGroup 2 B) :
    IsCyclic (B.map (QuotientGroup.mk' (inner X))) := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hX
  have hU : UnitaryFieldData 2 n K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(3 = 3 ∧ 2 ^ n = 2) := fun ⟨_, h2⟩ => by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := 3)) (le_refl 3) hq
  have e' : X ≃* primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact isCyclic_map_outer_of_mulEquiv_aux e'
    (fun B' hB' => isCyclic_map_outer_primeFormP_aux hU (le_refl 3) hq isPrimeFormGram_one hB')
    B hB

end CFSG.Quasithin.U31521
