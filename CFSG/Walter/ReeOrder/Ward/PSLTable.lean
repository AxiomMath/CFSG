module

public import CFSG.CharacterTheory.Semidihedral.MatrixTorus
public import CFSG.CharacterTheory.PSL2Table.Classes
public import CFSG.CharacterTheory.PSL2Table.Halves

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.Ward

open CFSG CFSG.PSL2Table Matrix

namespace PSLTable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem unip_pow (t : F) (n : ℕ) : unip t ^ n = unip ((n : F) * t) := by
  induction n with
  | zero => simp [unip_zero]
  | succ n ih => rw [pow_succ, ih, ← unip_add]; push_cast; ring_nf

omit [DecidableEq F] in
theorem orderOf_unip (hF : ringChar F ≠ 2) {t : F} (ht : t ≠ 0) :
    orderOf (mk (unip t) : PSL(2, F)) = ringChar F := by
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, unip_pow, CharP.cast_eq_zero F (ringChar F), zero_mul, unip_zero, map_one]
  · rw [Ne, mk_unip_eq_one_iff (Ring.two_ne_zero hF)]
    exact ht

omit [DecidableEq F] in
theorem U_order (hF : ringChar F ≠ 2) :
    ∀ x ∈ unipotent F, x ≠ 1 → orderOf x = ringChar F := by
  intro x hx hx1
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
  have ht : t ≠ 0 := by
    rintro rfl
    exact hx1 (by rw [unip_zero, map_one])
  exact orderOf_unip hF ht

omit [DecidableEq F] in
theorem nonsplit_isCyclic {ν : F} (hν : ¬ IsSquare ν) : IsCyclic (nonsplitTorus ν) := by
  have hν0 : ν ≠ 0 := fun h => hν ⟨0, by rw [h]; ring⟩
  set a : Fˣ := Units.mk0 (-ν) (neg_ne_zero.mpr hν0)
  have heq : nonsplitSL ν = Semidihedral.MatrixTorus.Torus F a := by
    ext X
    rw [Semidihedral.MatrixTorus.mem_torus_iff]
    have hna : -((a : Fˣ) : F) = ν := by simp [a]
    rw [hna]
    change ((X : Matrix (Fin 2) (Fin 2) F) 1 1 = (X : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      (X : Matrix (Fin 2) (Fin 2) F) 0 1 = ν * (X : Matrix (Fin 2) (Fin 2) F) 1 0) ↔ _
    tauto
  have hcyc : IsCyclic (nonsplitSL ν) := by
    rw [heq]
    exact Semidihedral.MatrixTorus.nonsplit_torus_cyclic F a (by simpa [a] using hν)
  exact isCyclic_of_surjective (mk.subgroupMap (nonsplitSL ν))
    (MonoidHom.subgroupMap_surjective _ _)

theorem quadChar_two (h8 : Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5) :
    quadChar F 2 = -1 := by
  have h2 : ¬ IsSquare (2 : F) := by
    rw [FiniteField.isSquare_two_iff]
    omega
  rw [quadChar_apply, quadraticChar_neg_one_iff_not_isSquare.mpr h2]
  simp

theorem exists_two_mod {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : 0 < N) :
    ∃ k : ℕ, k.Coprime N ∧ k ≡ 2 [MOD p] := by
  set M := N / p ^ N.factorization p with hM
  have hMp : M.Coprime p := (Nat.coprime_ordCompl hp hN.ne').symm
  obtain ⟨k, hk⟩ := Nat.chineseRemainder hMp.symm 2 1
  refine ⟨k, ?_, hk.1⟩
  have hNeq : N = p ^ N.factorization p * M := (Nat.ordProj_mul_ordCompl_eq_self N p).symm
  rw [hNeq]
  refine Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ?_) ?_
  · have h1 : k % p = 2 % p := hk.1
    have h2 : 2 % p = 2 := Nat.mod_eq_of_lt (by have := hp.two_le; omega)
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have := Nat.mod_eq_zero_of_dvd hdvd
    omega
  · rw [Nat.coprime_iff_gcd_eq_one]
    have e1 : Nat.gcd k M ∣ k := Nat.gcd_dvd_left _ _
    have e2 : Nat.gcd k M ∣ M := Nat.gcd_dvd_right _ _
    have e3 : k ≡ 1 [MOD Nat.gcd k M] := Nat.ModEq.of_dvd e2 hk.2
    have e4 : k % Nat.gcd k M = 0 := Nat.mod_eq_zero_of_dvd e1
    unfold Nat.ModEq at e3
    rw [e4] at e3
    exact Nat.dvd_one.mp (Nat.dvd_of_mod_eq_zero e3.symm)

omit [DecidableEq F] in
theorem exists_psi : ∃ ψ : AddChar F ℂ, ψ.IsPrimitive := by
  obtain ⟨ψ, hψ1⟩ := (AddChar.exists_apply_ne_zero (a := (1 : F))).mpr one_ne_zero
  exact ⟨ψ, AddChar.IsPrimitive.of_ne_one (fun h => hψ1 (by rw [h]; rfl))⟩

omit [DecidableEq F] in
theorem p_dvd_card : ringChar F ∣ Fintype.card F := by
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  rw [hn]
  exact dvd_pow_self _ n.ne_zero

theorem classes' (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F} (hν : ¬ IsSquare ν)
    (g : PSL(2, F)) : g = 1 ∨ (∃ x ∈ unipotent F, x ≠ 1 ∧ IsConj g x) ∨
      (∃ x ∈ splitTorus F, x ≠ 1 ∧ IsConj g x) ∨ (∃ x ∈ nonsplitTorus ν, x ≠ 1 ∧ IsConj g x) := by
  have h2 := Ring.two_ne_zero hF
  have hν0 : ν ≠ 0 := fun h => hν ⟨0, by rw [h]; ring⟩
  rcases conj_cases hF hq hν g with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨mk (unip 1), (mem_unipotent_iff_exists _).mpr ⟨1, rfl⟩,
      by rw [Ne, mk_unip_eq_one_iff h2]; exact one_ne_zero, h⟩)
  · exact Or.inr (Or.inl ⟨mk (unip ν), (mem_unipotent_iff_exists _).mpr ⟨ν, rfl⟩,
      by rw [Ne, mk_unip_eq_one_iff h2]; exact hν0, h⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem galois_U' (hF : ringChar F ≠ 2) (h8 : Fintype.card F % 8 = 3 ∨ Fintype.card F % 8 = 5)
    {ν : F} (hν : ¬ IsSquare ν) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (N : ℕ) (hN : 0 < N) :
    ∃ k : ℕ, k.Coprime N ∧ ∀ x ∈ unipotent F, x ≠ 1 →
      halfPlus hF ψ ν (x ^ k) = halfMinus hF ψ ν x ∧
        halfMinus hF ψ ν (x ^ k) = halfPlus hF ψ ν x := by
  have h2 := Ring.two_ne_zero hF
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  obtain ⟨k, hk, hk2⟩ := exists_two_mod hp hF hN
  have hkF : (k : F) = 2 := by
    have := (CharP.natCast_eq_natCast F (ringChar F)).mpr hk2
    rw [this]
    norm_num
  refine ⟨k, hk, fun x hx hx1 => ?_⟩
  obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).mp hx
  have ht : t ≠ 0 := by
    rintro rfl
    exact hx1 (by rw [unip_zero, map_one])
  have h2t : (2 : F) * t ≠ 0 := mul_ne_zero h2 ht
  have hpow : (mk (unip t) : PSL(2, F)) ^ k = mk (unip (2 * t)) := by
    rw [← map_pow, unip_pow, hkF]
  have hχ : quadChar F (2 * t) = -quadChar F t := by
    rw [map_mul, quadChar_two h8, neg_one_mul]
  rw [hpow, halfPlus_unip hF hψ hν h2t, halfMinus_unip hF hψ hν h2t, halfPlus_unip hF hψ hν ht,
    halfMinus_unip hF hψ hν ht, hχ]
  constructor <;> ring

theorem conj_eps (hε : epsSign F = 1 ∨ epsSign F = -1) :
    starRingEnd ℂ (epsSign F) = epsSign F := by
  rcases hε with h | h <;> rw [h] <;> simp

end PSLTable

end CFSG.Walter.Ward
