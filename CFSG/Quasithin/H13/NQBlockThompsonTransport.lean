module

public import CFSG.Foundations.HigherElementaryThompson

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG

variable {A B : Type*} [Group A] [Group B]

theorem pRank_mulEquiv (e : A ≃* B) (p : ℕ) [Fact p.Prime] :
    CFSG.pRank p A = CFSG.pRank p B := by
  unfold CFSG.pRank
  congr 1
  ext r
  constructor
  · rintro ⟨E, hE, hc⟩
    exact ⟨E.map e.toMonoidHom, CFSG.IsElementaryAbelian.map (A := E) e.toMonoidHom,
      by rw [Subgroup.card_map_of_injective e.injective, hc]⟩
  · rintro ⟨E, hE, hc⟩
    exact ⟨E.map e.symm.toMonoidHom, CFSG.IsElementaryAbelian.map (A := E) e.symm.toMonoidHom,
      by rw [Subgroup.card_map_of_injective e.symm.injective, hc]⟩

theorem pRank_map_mulEquiv (e : A ≃* B) (C : Subgroup A) (p : ℕ) [Fact p.Prime] :
    CFSG.pRank p ↥(C.map e.toMonoidHom) = CFSG.pRank p ↥C :=
  (pRank_mulEquiv (C.equivMapOfInjective e.toMonoidHom e.injective) p).symm

theorem image_higherElemThompsonFamily (e : A ≃* B) (j : ℕ) :
    Subgroup.map e.toMonoidHom '' higherElemThompsonFamily A j = higherElemThompsonFamily B j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ext D
  constructor
  · rintro ⟨C, ⟨hC, hCr⟩, rfl⟩
    refine ⟨CFSG.IsElementaryAbelian.map (A := C) e.toMonoidHom, ?_⟩
    rw [pRank_map_mulEquiv, hCr, pRank_mulEquiv e]
  · rintro ⟨hD, hDr⟩
    refine ⟨D.map e.symm.toMonoidHom, ⟨CFSG.IsElementaryAbelian.map (A := D) e.symm.toMonoidHom,
      ?_⟩, ?_⟩
    · rw [pRank_map_mulEquiv, hDr, pRank_mulEquiv e]
    · rw [Subgroup.map_map]
      convert Subgroup.map_id D
      ext x
      simp

theorem map_higherElemThompson (e : A ≃* B) (j : ℕ) :
    (higherElemThompson A j).map e.toMonoidHom = higherElemThompson B j := by
  rw [higherElemThompson, higherElemThompson, (Subgroup.gc_map_comap e.toMonoidHom).l_sSup,
    ← image_higherElemThompsonFamily e j, sSup_image]

theorem mem_omegaOneCenter_iff' {J : Subgroup A} {z : A} :
    z ∈ omegaOneCenter J ↔ z ∈ J ∧ (∀ x ∈ J, x * z = z * x) ∧ z ^ 2 = 1 := by
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hz⟩
    exact ⟨c.2, fun x hx => congrArg Subtype.val (mem_center_iff.mp hc ⟨x, hx⟩), hz⟩
  · rintro ⟨hzJ, hc, hz⟩
    exact ⟨⟨⟨z, hzJ⟩, mem_center_iff.mpr fun g => Subtype.ext (hc g g.2), rfl⟩, hz⟩

theorem map_omegaOneCenter (e : A ≃* B) (J : Subgroup A) :
    (omegaOneCenter J).map e.toMonoidHom = omegaOneCenter (J.map e.toMonoidHom) := by
  ext b
  rw [mem_map, mem_omegaOneCenter_iff']
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨haJ, hac, ha2⟩ := mem_omegaOneCenter_iff'.mp ha
    refine ⟨mem_map_of_mem _ haJ, ?_, by rw [← map_pow, ha2, map_one]⟩
    rintro _ ⟨x, hx, rfl⟩
    change e x * e a = e a * e x
    rw [← map_mul, ← map_mul, hac x hx]
  · rintro ⟨⟨a, haJ, rfl⟩, hc, h2⟩
    refine ⟨a, mem_omegaOneCenter_iff'.mpr ⟨haJ, fun x hx => ?_, ?_⟩, rfl⟩
    · apply e.injective
      rw [map_mul, map_mul]
      exact hc _ (mem_map_of_mem _ hx)
    · apply e.injective
      rw [map_pow, map_one]
      exact h2

theorem map_higherElemThompsonOmega (e : A ≃* B) (j : ℕ) :
    (higherElemThompsonOmega A j).map e.toMonoidHom = higherElemThompsonOmega B j := by
  rw [higherElemThompsonOmega, higherElemThompsonOmega, map_omegaOneCenter,
    map_higherElemThompson]

end CFSG.Quasithin.H13.NQBlock
