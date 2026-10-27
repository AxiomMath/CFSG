module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoPhiKer
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoKLayer

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

namespace PhiData

variable (P : PhiData O β)

theorem range_le_fixV (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    P.φ.range ≤ fixV (rImg ρ (octFix O)) := by
  rintro v ⟨x, rfl⟩
  rw [mem_fixV]
  intro u hu
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hu
  have hkO : (k : S24) ∈ octFix O := Subgroup.mem_subgroupOf.mp hk
  have hfix : ∀ p, (k : S24) (P.o p) = P.o ((1 : Equiv.Perm (Fin 8)) p) := fun p =>
    (mem_octFix_iff.mp hkO).2 (P.o p) ((P.o_mem (P.o p)).mpr ⟨p, rfl⟩)
  have h := P.equivariant hM (g := k) (σ := 1) hfix x
  simpa using h

theorem range_eq_fixV (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) :
    P.φ.range = fixV (rImg ρ (octFix O)) := by
  haveI : Finite V := mctx_finite hM
  haveI : Finite ↥(fixV (rImg ρ (octFix O))) := Subtype.finite
  have hcard6 : Nat.card (Multiplicative (Fin 6 → ZMod 2)) = 2 ^ 6 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
    simp [Fintype.card_fun, ZMod.card]
  refine Subgroup.eq_of_le_of_card_ge (range_le_fixV P hM) ?_
  rw [kLayer_card_fixV hM]
  by_cases hd : d = 22
  · rw [if_pos hd]
    have hker : Nat.card ↥P.φ.ker = 2 := by
      rw [ker_eq22 P hM hd, Nat.card_zpowers]
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_one, toAdd_ofAdd, CharTwo.add_self_eq_zero]
      · intro h
        have h0 : Multiplicative.toAdd (Multiplicative.ofAdd (evPair 0 1)) = 0 := by
          rw [h, toAdd_one]
        have hev : evPair 0 1 = (0 : Fin 6 → ZMod 2) := by simpa using h0
        have hq : (1 : ZMod 2) = 0 := by
          rw [← qPlus6_evPair (show (0 : Fin 8) ≠ 1 by decide), hev]
          decide
        exact one_ne_zero hq
    have hmul := Subgroup.card_ker_mul_card_range P.φ
    rw [hker, hcard6] at hmul
    have hrange : Nat.card ↥P.φ.range = 2 ^ 5 := by
      norm_num at hmul ⊢
      omega
    exact le_of_eq hrange.symm
  · rw [if_neg hd]
    have hinj : Function.Injective P.φ :=
      (MonoidHom.ker_eq_bot_iff P.φ).mp (ker_ne22 P hM hd)
    have hrange : Nat.card ↥P.φ.range = 2 ^ 6 :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hcard6
    exact le_of_eq hrange.symm

end PhiData

end CFSG.ASVolI.AppH

