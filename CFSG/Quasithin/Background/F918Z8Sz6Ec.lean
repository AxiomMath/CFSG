module

public import CFSG.Quasithin.Background.F918Z8Sz6Ea
public import CFSG.Quasithin.Background.F918Z8Sz6Eb

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

section Assembly

variable {K : Type} [Field K]

theorem exists_scalar_of_commute_natAct
    (g : Multiplicative (Fin 3 → K) ≃* Multiplicative (Fin 3 → K))
    (hg : ∀ (A : ↥(StatedSL 3 K)) (x : Multiplicative (Fin 3 → K)),
      g (natAct (StatedSL 3 K) A x) = natAct (StatedSL 3 K) A (g x)) :
    ∃ s : K, ∀ v : Fin 3 → K, Multiplicative.toAdd (g (Multiplicative.ofAdd v)) = s • v := by
  let gA : (Fin 3 → K) →+ (Fin 3 → K) :=
    { toFun := fun v => Multiplicative.toAdd (g (Multiplicative.ofAdd v))
      map_zero' := by
        show Multiplicative.toAdd (g 1) = 0
        rw [map_one]
        rfl
      map_add' := fun x y => by
        show Multiplicative.toAdd (g (Multiplicative.ofAdd x * Multiplicative.ofAdd y)) = _
        rw [map_mul]
        rfl }
  refine exists_scalar_of_commute_transvection gA fun i j hij c v => ?_
  have h := hg (specialLinearGroupEquivStatedSL 3 K (Matrix.SpecialLinearGroup.transvection hij c))
    (Multiplicative.ofAdd v)
  exact congrArg Multiplicative.toAdd h

theorem natSL3_comm_order_proved {R : Type} [CommGroup R] [Finite R] {L : Subgroup (MulAut R)}
    {m : ℕ} (hnat : BinaryNaturalSL L ⊤ ⊥ 3 m) {γ : MulAut R} (hγ : ∀ l ∈ L, γ * l = l * γ) :
    orderOf γ ∣ 2 ^ m - 1 := by
  obtain ⟨K, hK, hfin, hcard, e, he⟩ := hnat.exists_natEquiv
  let g : Multiplicative (Fin 3 → K) ≃* Multiplicative (Fin 3 → K) := e.symm.trans (γ.trans e)
  have hge : ∀ r : R, g (e r) = e (γ r) := fun r => by
    show e (γ (e.symm (e r))) = _
    rw [e.symm_apply_apply]
  have hg : ∀ (A : ↥(StatedSL 3 K)) (x : Multiplicative (Fin 3 → K)),
      g (natAct (StatedSL 3 K) A x) = natAct (StatedSL 3 K) A (g x) := by
    intro A x
    obtain ⟨l, hl, hle⟩ := he A
    obtain ⟨r, rfl⟩ := e.surjective x
    have hc : γ (l r) = l (γ r) := by
      have := congrArg (fun f : MulAut R => f r) (hγ l hl)
      simpa using this
    rw [← hle, hge, hge, hc, hle]
  obtain ⟨s, hs⟩ := exists_scalar_of_commute_natAct g hg
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h1 : g (Multiplicative.ofAdd (Pi.single 0 1)) = g 1 := by
      have := hs (Pi.single 0 1)
      rw [zero_smul] at this
      rw [map_one]
      exact Multiplicative.toAdd.injective this
    have h2 := congrFun (Multiplicative.ofAdd.injective (g.injective h1)) 0
    simp at h2
  have hpow : ∀ (n : ℕ) (r : R),
      Multiplicative.toAdd (e ((γ ^ n) r)) = s ^ n • Multiplicative.toAdd (e r) := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
      intro r
      have h1 : (γ ^ (n + 1)) r = (γ ^ n) (γ r) := by rw [pow_succ]; rfl
      have h2 : Multiplicative.toAdd (g (e r)) = s • Multiplicative.toAdd (e r) :=
        hs (Multiplicative.toAdd (e r))
      rw [h1, ih, ← hge, h2, smul_smul, pow_succ]
  let : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  apply orderOf_dvd_of_pow_eq_one
  refine MulEquiv.ext fun r => e.injective (Multiplicative.toAdd.injective ?_)
  rw [hpow, ← hK, FiniteField.pow_card_sub_one_eq_one s hs0, one_smul]
  rfl

end Assembly

end CFSG.Quasithin
