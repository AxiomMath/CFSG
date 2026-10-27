module

public import CFSG.Quasithin.H13.NQCatJ4Exclusion
public import CFSG.Quasithin.H13.NQCatUniqueModels

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQCat

open Subgroup
open scoped Pointwise commutatorElement

theorem eq_eleven_of_sq_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 2 ∣ Nat.card Sporadic.J4.J) : p = 11 := by
  rw [card_J4J, show (86775571046077562880 : ℕ) =
    2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 by norm_num] at h
  have hpd := (dvd_pow_self p two_ne_zero).trans h
  have hq : ∀ q : ℕ, q.Prime → ∀ n : ℕ, p ∣ q ^ n → p = q := fun q hq n hn =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hn)
  simp only [Nat.Prime.dvd_mul hp, or_assoc] at hpd
  rcases hpd with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · have := hq 2 Nat.prime_two 21 h1; omega
  · have := hq 3 Nat.prime_three 3 h1; omega
  · have := hq 5 (by norm_num) 1 (by rw [pow_one]; exact h1)
    subst this
    norm_num at h
  · have := hq 7 (by norm_num) 1 (by rw [pow_one]; exact h1)
    subst this
    norm_num at h
  · exact hq 11 (by norm_num) 3 h1
  · have := hq 23 (by norm_num) 1 (by rw [pow_one]; exact h1)
    subst this
    norm_num at h
  · have := hq 29 (by norm_num) 1 (by rw [pow_one]; exact h1)
    subst this
    norm_num at h
  · have := hq 31 (by norm_num) 1 (by rw [pow_one]; exact h1)
    subst this
    norm_num at h
  · have := hq 37 (by norm_num) 1 (by rw [pow_one]; exact h1)
    subst this
    norm_num at h
  · have := hq 43 (by norm_num) 1 (by rw [pow_one]; exact h1)
    subst this
    norm_num at h

theorem permutable_map_conj {A B : Subgroup Sporadic.J4.J} (g : Sporadic.J4.J)
    (h : (A : Set Sporadic.J4.J) * (B : Set Sporadic.J4.J) = (B : Set Sporadic.J4.J) * A) :
    ((A.map (MulAut.conj g).toMonoidHom : Subgroup Sporadic.J4.J) : Set Sporadic.J4.J) *
        ((B.map (MulAut.conj g).toMonoidHom : Subgroup Sporadic.J4.J) : Set Sporadic.J4.J) =
      ((B.map (MulAut.conj g).toMonoidHom : Subgroup Sporadic.J4.J) : Set Sporadic.J4.J) *
        ((A.map (MulAut.conj g).toMonoidHom : Subgroup Sporadic.J4.J) : Set Sporadic.J4.J) := by
  simp only [coe_map]
  rw [← Set.image_mul, ← Set.image_mul, h]

theorem zpowers_conj
    (g : Sporadic.J4.J) :
    zpowers ⁅g * j4x * g⁻¹, g * j4y * g⁻¹⁆ =
      (zpowers j4z).map (MulAut.conj g).toMonoidHom := by
  rw [commutator_conj, MonoidHom.map_zpowers]
  rfl

theorem J4_noncyclic_prime_sylow_product_full_normalizer_preserves_line
    {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (A : Subgroup Sporadic.J4.J) (hA : IsPGroup p A) (hAc : ¬ IsCyclic A)
    (U : Sylow 2 Sporadic.J4.J)
    (hAU : (A : Set Sporadic.J4.J) * (U : Set Sporadic.J4.J) = (U : Set Sporadic.J4.J) * A) :
    p = 11 ∧ IsElementaryAbelian 11 A ∧ Nat.card A = 11 ^ 2 ∧
      ∃ C : Subgroup Sporadic.J4.J, C ≤ A ∧ Nat.card C = 11 ∧
        (∀ α : MulAut Sporadic.J4.J,
          A.map (MulEquiv.toMonoidHom (M := Sporadic.J4.J) (N := Sporadic.J4.J) α) = A →
            C.map (MulEquiv.toMonoidHom (M := Sporadic.J4.J) (N := Sporadic.J4.J) α) = C) ∧
        ∀ α ∈ CFSG.LocalAnalysis.ComponentInitial.pairAutSubgroup A (U : Subgroup Sporadic.J4.J),
          C.map (MulEquiv.toMonoidHom (M := Sporadic.J4.J) (N := Sporadic.J4.J) α) = C := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp11 : p = 11 := by
    refine eq_eleven_of_sq_dvd hp hp5 ?_
    by_contra hsq
    exact hAc (isCyclic_of_isPGroup_of_not_sq_dvd hA hsq)
  subst hp11
  obtain ⟨g, hAg⟩ := exists_le_conj hA
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hD := j4DataConj g
  have hQ' := closure_conj g
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hk3 : k ≤ 3 := by
    have h1 := card_le_of_le hAg
    rw [card_map_of_injective hinj, hk, j4Data.card_closure] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hk2 : k = 2 := by
    rcases (show k ≤ 1 ∨ k = 2 ∨ k = 3 by omega) with h1 | h2 | h3
    · exfalso
      apply hAc
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · have : Subsingleton A := by
          rw [← Finite.card_le_one_iff_subsingleton, hk, pow_zero]
        infer_instance
      · exact isCyclic_of_prime_card (hk.trans (pow_one 11))
    · exact h2
    · exfalso
      have hAeq : A = j4Q.map (MulAut.conj g).toMonoidHom :=
        eq_of_le_of_card_ge hAg (by
          rw [card_map_of_injective hinj, hk, h3, j4Data.card_closure])
      have hAU' : (A : Set Sporadic.J4.J) * ((U : Subgroup Sporadic.J4.J) : Set Sporadic.J4.J) =
          ((U : Subgroup Sporadic.J4.J) : Set Sporadic.J4.J) * A := hAU
      have hperm := permutable_map_conj g⁻¹ hAU'
      have hback : A.map (MulAut.conj g⁻¹).toMonoidHom = j4Q := by
        rw [hAeq, map_map]
        have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
            MonoidHom.id _ := by
          ext x
          simp [MulAut.conj_apply, mul_assoc]
        rw [this, map_id]
      rw [hback] at hperm
      apply not_permutable_j4Q (g⁻¹ • U)
      rw [CFSG.LieType.Chevalley.coe_smul_sylow_eq_map]
      exact hperm
  subst hk2
  have hAcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hk
  have hel : IsElementaryAbelian 11 A := by
    refine { toIsMulCommutative := hAcomm, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hD.pow_eleven (hQ'.symm ▸ hAg a.2)
  set C := (zpowers j4z).map (MulAut.conj g).toMonoidHom with hCdef
  have hCA : C ≤ A := by
    rw [hCdef, ← zpowers_conj]
    exact hD.zpowers_le_of_card (hQ'.symm ▸ hAg) hk
  have hCcard : Nat.card C = 11 := by
    rw [hCdef, card_map_of_injective hinj, Nat.card_zpowers, j4Data.orderOf_z]
  have hline : ∀ α : MulAut Sporadic.J4.J,
      A.map (MulEquiv.toMonoidHom (M := Sporadic.J4.J) (N := Sporadic.J4.J) α) = A →
        C.map (MulEquiv.toMonoidHom (M := Sporadic.J4.J) (N := Sporadic.J4.J) α) = C := by
    intro α hα
    obtain ⟨c, hc⟩ := exists_eq_conj α
    have hle :
        C.map (MulEquiv.toMonoidHom (M := Sporadic.J4.J) (N := Sporadic.J4.J) α) ≤ C := by
      rintro _ ⟨u, hu, rfl⟩
      by_cases hu1 : u = 1
      · rw [hu1, map_one]
        exact one_mem _
      have huA : α u ∈ A := hα ▸ ⟨u, hCA hu, rfl⟩
      have hαu1 : α u ≠ 1 := fun h => hu1 (α.injective (h.trans (map_one α).symm))
      have h2 : fixDim (α u) = 2 := by
        rw [hc, fixDim_conj]
        exact (fixDim_of_mem_conj g (map_mono (zpowers_le.2 ElevenData.z_mem) hu) hu1).1 hu
      by_contra hnot
      have h12 := (fixDim_of_mem_conj g (hAg huA) hαu1).2 hnot
      omega
    exact eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective
        (f := MulEquiv.toMonoidHom (M := Sporadic.J4.J) (N := Sporadic.J4.J) α) α.injective])
  refine ⟨rfl, hel, hk, C, hCA, hCcard, hline, fun α hα => hline α hα.1⟩

end CFSG.Quasithin.H13.NQCat
