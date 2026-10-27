module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.QuasithinUnique

theorem isSL2_of_naturalSL2Action {p : ℕ} {X : Type} [Group X] {F : Subgroup X} [F.Normal]
    (h : NaturalSL2Action p X F) : IsSL2 p (X ⧸ F) := by
  obtain ⟨-, ψ, hψ, hker, -⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem mul_sq_sub_one_lt {p r : ℕ} (hp : 1 ≤ p) (h : p < r) :
    p * (p ^ 2 - 1) < r * (r ^ 2 - 1) := by
  have hr : 4 ≤ r ^ 2 := by nlinarith
  calc p * (p ^ 2 - 1) ≤ p * (r ^ 2 - 1) :=
        Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.pow_le_pow_left h.le 2) 1)
    _ < r * (r ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right h (by omega)

theorem eq_of_mul_sq_sub_one {p r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r)
    (h : p * (p ^ 2 - 1) = r * (r ^ 2 - 1)) : p = r := by
  rcases lt_trichotomy p r with hlt | heq | hgt
  · exact absurd h (mul_sq_sub_one_lt hp hlt).ne
  · exact heq
  · exact absurd h.symm (mul_sq_sub_one_lt hr hgt).ne

@[expose] noncomputable def multFinTwoEquiv (p : ℕ) :
    Multiplicative (Fin 2 → ZMod p) ≃* Multiplicative (ZMod p) × Multiplicative (ZMod p) :=
  (AddEquiv.toMultiplicative { finTwoArrowEquiv (ZMod p) with map_add' := fun _ _ => rfl }).trans
    (MulEquiv.prodMultiplicative (ZMod p) (ZMod p))

theorem a36Case4_of_case3_five {X : Type} [Group X] [Finite X]
    (hFF : CFSG.generalizedFitting X = CFSG.fittingSubgroup X)
    (hE : IsElemAbelianOfRank 5 2 ↥(CFSG.fittingSubgroup X))
    (hN : NaturalSL2Action 5 X (CFSG.fittingSubgroup X)) : A36Case4 X := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := hE
  have hcardF : Nat.card ↥(CFSG.fittingSubgroup X) = 5 ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Fin 2 → ZMod 5) = 5 ^ 2
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hp5 : IsPGroup 5 ↥(CFSG.fittingSubgroup X) := IsPGroup.of_card hcardF
  have hle1 : CFSG.fittingSubgroup X ≤ CFSG.pCore 5 X := le_sSup ⟨inferInstance, hp5⟩
  have hle2 : CFSG.pCore 5 X ≤ CFSG.fittingSubgroup X :=
    le_sSup ⟨CFSG.pCore_normal, (CFSG.pCore_isPGroup (p := 5) (G := X)).isNilpotent⟩
  have heq : CFSG.pCore 5 X = CFSG.fittingSubgroup X := le_antisymm hle2 hle1
  refine ⟨hFF, inferInstance, isSL2_of_naturalSL2Action hN, fun q hq hqd => ?_⟩
  rw [hcardF] at hqd
  have hq5 : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqd)
  subst hq5
  exact ⟨Or.inr (Or.inr rfl), Or.inr ⟨1, le_rfl,
    ⟨((MulEquiv.subgroupCongr heq).trans e).trans (multFinTwoEquiv 5)⟩⟩⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
