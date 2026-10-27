module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LinearGroups

variable {m : ℕ} {F' : Type} [Field F']

private theorem u3_eq_of_mulVecLin {p f : ℕ} {K : Type} [Field K] {n : ℕ}
    {A B : ↥(unitarySU p f K n)}
    (h : Matrix.mulVecLin ((A : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.mulVecLin ((B : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    A = B := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hij := LinearMap.congr_fun h (Pi.single j 1)
  simpa [Matrix.mulVec_single_one] using congrFun hij i

private theorem u3_mulVecLin_mul {p f : ℕ} {K : Type} [Field K] {n : ℕ}
    (A B : ↥(unitarySU p f K n)) :
    Matrix.mulVecLin ((((A * B : ↥(unitarySU p f K n)) : Matrix.GeneralLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) =
      Matrix.mulVecLin ((A : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ∘ₗ
        Matrix.mulVecLin ((B : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  ext x
  simp [Matrix.mulVec_mulVec]

private theorem u3_norm_mul_mem_traceZero {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero) (t : K) :
    h.norm t * c ∈ h.traceZero := by
  rw [UnitaryFieldData.mem_traceZero] at hc ⊢
  have key : h.bar (t * h.bar t) = h.bar t * t := by
    rw [map_mul, h.bar_bar]
  simp only [UnitaryFieldData.trace, UnitaryFieldData.norm] at hc ⊢
  rw [map_mul, key]
  linear_combination (t * h.bar t) * hc

theorem model3_unitary_card_point (hF' : UnitaryFieldData 2 m F')
    {L : Submodule F' (Fin 3 → F')} (hL : L ∈ isotropicLines hF' 3) :
    Nat.card ↥(isotropicTransvectionGroup hF' 3 L) = 2 ^ m ∧
      ∀ x ∈ isotropicTransvectionGroup hF' 3 L, x * x = 1 := by
  haveI : CharP F' 2 := hF'.charP
  obtain ⟨hfin, hiso⟩ := mem_isotropicLines.mp hL
  obtain ⟨v, hvL, hv0, hspan⟩ : ∃ v : Fin 3 → F', v ∈ L ∧ v ≠ 0 ∧
      ∀ a ∈ L, ∃ t : F', t • v = a := by
    obtain ⟨w, hw0, hwall⟩ := finrank_eq_one_iff'.mp hfin
    refine ⟨(w : Fin 3 → F'), w.2, fun h => hw0 (Subtype.ext h), fun a ha => ?_⟩
    obtain ⟨t, ht⟩ := hwall ⟨a, ha⟩
    exact ⟨t, congrArg Subtype.val ht⟩
  have hvv : stdHermForm hF' 3 v v = 0 := hiso v hvL
  have hB : (stdHermForm hF' 3).IsSymm := stdHermForm_isSymm hF' 3
  have hgen : ∀ c : ↥hF'.traceZero, ∃ g ∈ isotropicTransvectionGroup hF' 3 L,
      Matrix.mulVecLin ((g : Matrix.GeneralLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') =
        hermTransvection (stdHermForm hF' 3) v (c : F') :=
    fun c => exists_mem_isotropicTransvectionGroup hF' hL hvL c.2
  choose g hgG hgT using hgen
  have hmul : ∀ c d : ↥hF'.traceZero, g (c + d) = g c * g d := by
    intro c d
    apply u3_eq_of_mulVecLin
    rw [u3_mulVecLin_mul, hgT, hgT, hgT, AddSubgroup.coe_add, hermTransvection_comp _ hvv]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Multiplicative ↥hF'.traceZero →* ↥(unitarySU 2 m F' 3),
      ∀ x, Φ x = g x.toAdd :=
    ⟨MonoidHom.mk' (fun x => g x.toAdd) (fun x y => hmul x.toAdd y.toAdd), fun x => rfl⟩
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hΦ] at hx
    have hT : hermTransvection (stdHermForm hF' 3) v (x.toAdd : F') = LinearMap.id := by
      rw [← hgT x.toAdd, hx]
      ext y
      simp
    obtain ⟨w1, hw1, -⟩ :=
      (hermitian_hyperbolic_splitting hF' hB (stdHermForm_separatingLeft hF' 3) hv0 hvv).1
    have hw := LinearMap.congr_fun hT w1
    rw [hermTransvection_apply, LinearMap.id_apply, hw1, mul_one] at hw
    have hsm : (x.toAdd : F') • v = 0 := by
      simpa using hw
    have hc0 : (x.toAdd : F') = 0 := by
      rcases smul_eq_zero.mp hsm with h | h
      · exact h
      · exact absurd h hv0
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact Subtype.ext hc0
  have hrange : isotropicTransvectionGroup hF' 3 L = Φ.range := by
    apply le_antisymm
    · unfold isotropicTransvectionGroup
      rw [Subgroup.closure_le]
      rintro k ⟨a, haL, c, hc, hk⟩
      obtain ⟨t, rfl⟩ := hspan a haL
      rw [(hermitian_unitary_transvection hF' hB hvv).2.2.2.2.2 c hc t] at hk
      have hd : hF'.norm t * c ∈ hF'.traceZero := u3_norm_mul_mem_traceZero hF' hc t
      refine MonoidHom.mem_range.mpr
        ⟨Multiplicative.ofAdd (⟨hF'.norm t * c, hd⟩ : ↥hF'.traceZero), ?_⟩
      rw [hΦ]
      apply u3_eq_of_mulVecLin
      rw [hk]
      exact hgT _
    · rintro _ ⟨x, rfl⟩
      rw [hΦ]
      exact hgG x.toAdd
  refine ⟨?_, ?_⟩
  · rw [hrange]
    calc Nat.card ↥(Φ.range) = Nat.card (Multiplicative ↥hF'.traceZero) :=
          Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv.symm
      _ = Nat.card ↥hF'.traceZero := Nat.card_congr Multiplicative.ofAdd.symm
      _ = 2 ^ m := hF'.card_traceZero
  · intro x hx
    rw [hrange] at hx
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
    have hyy : y * y = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      apply Subtype.ext
      rw [AddSubgroup.coe_add, AddSubgroup.coe_zero]
      exact CharTwo.add_self_eq_zero _
    rw [← map_mul, hyy, map_one]

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
