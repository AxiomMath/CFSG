module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  Multiplicative Matrix

private theorem ggKGUc_diag_eq_of_mul_eq {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) {ζ : K} {g : hypSU h r 0} {t t' : Fin r → ZMod p}
    (hm : (((g : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K) * diagonal (hypEntries ζ t) =
      diagonal (hypEntries ζ t') * (((g : hypSU h r 0) : GL (HypIndex r 0) K) :
        Matrix (HypIndex r 0) (HypIndex r 0) K))
    {x y : HypIndex r 0}
    (hxy : (((g : hypSU h r 0) : GL (HypIndex r 0) K) :
      Matrix (HypIndex r 0) (HypIndex r 0) K) y x ≠ 0) :
    hypEntries ζ t x = hypEntries ζ t' y := by
  have e := congrArg (fun M : Matrix (HypIndex r 0) (HypIndex r 0) K => M y x) hm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  exact mul_left_cancel₀ hxy (e.trans (mul_comm _ _))

private theorem ggKGUc_monomial_data {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (ι : (Fin r → Multiplicative (ZMod p)) →* hypSU h r 0)
    (hι : ∀ f, (((ι f : hypSU h r 0) : GL (HypIndex r 0) K) :
      Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal (hypEntries ζ (fun i => toAdd (f i))))
    (g : hypSU h r 0) :
    ∃ (j : Fin r → Fin r) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f' : Fin r → Multiplicative (ZMod p),
        g * ι f * g⁻¹ = ι f' → ∀ i, toAdd (f' (j i)) = ε i * toAdd (f i) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let u : Kˣ := (hζ.isUnit hp.ne_zero).unit
  have hu : (u : K) = ζ := (hζ.isUnit hp.ne_zero).unit_spec
  have huo : orderOf u = p :=
    (IsPrimitiveRoot.isUnit_unit (n := p) hp.ne_zero hζ).eq_orderOf.symm
  have hm : ∀ f f' : Fin r → Multiplicative (ZMod p), g * ι f * g⁻¹ = ι f' →
      (((g : hypSU h r 0) : GL (HypIndex r 0) K) :
          Matrix (HypIndex r 0) (HypIndex r 0) K) *
          diagonal (hypEntries ζ (fun k => toAdd (f k))) =
        diagonal (hypEntries ζ (fun k => toAdd (f' k))) *
          (((g : hypSU h r 0) : GL (HypIndex r 0) K) :
            Matrix (HypIndex r 0) (HypIndex r 0) K) := by
    intro f f' hff'
    have h1 : (g : GL (HypIndex r 0) K) * (ι f : GL (HypIndex r 0) K) *
        (g : GL (HypIndex r 0) K)⁻¹ = (ι f' : GL (HypIndex r 0) K) :=
      congrArg (fun y : hypSU h r 0 => (y : GL (HypIndex r 0) K)) hff'
    have h2 : (g : GL (HypIndex r 0) K) * (ι f : GL (HypIndex r 0) K) =
        (ι f' : GL (HypIndex r 0) K) * (g : GL (HypIndex r 0) K) := by
      rw [← h1]; group
    have h3 := congrArg (fun y : GL (HypIndex r 0) K =>
      (y : Matrix (HypIndex r 0) (HypIndex r 0) K)) h2
    simpa only [Units.val_mul, hι f, hι f'] using h3
  have key : ∀ i : Fin r, ∃ j : Fin r, ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
      ∀ f f', g * ι f * g⁻¹ = ι f' → toAdd (f' j) = ε * toAdd (f i) := by
    intro i
    obtain ⟨y, hy⟩ := ReflSp.exists_ne_zero_col ((g : hypSU h r 0) : GL (HypIndex r 0) K)
      (Sum.inl i)
    have hdiag : ∀ f f', g * ι f * g⁻¹ = ι f' →
        hypEntries ζ (fun k => toAdd (f k)) (Sum.inl i) =
          hypEntries ζ (fun k => toAdd (f' k)) y := fun f f' hff' =>
      ggKGUc_diag_eq_of_mul_eq h (hm f f' hff') hy
    rcases y with j | k | j
    · refine ⟨j, 1, Or.inl rfl, fun f f' hff' => ?_⟩
      have h1 := hdiag f f' hff'
      simp only [hypEntries] at h1
      have h1' : u ^ (toAdd (f i)).val = u ^ (toAdd (f' j)).val := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu]
        exact h1)
      have h2 := (pow_inj_mod (x := u)).mp h1'
      rw [huo, Nat.mod_eq_of_lt (ZMod.val_lt _),
        Nat.mod_eq_of_lt (ZMod.val_lt _)] at h2
      have h3 : toAdd (f' j) = toAdd (f i) := (ZMod.val_injective p h2).symm
      rw [h3, one_mul]
    · exact k.elim0
    · refine ⟨j, -1, Or.inr rfl, fun f f' hff' => ?_⟩
      have h1 := hdiag f f' hff'
      simp only [hypEntries] at h1
      rw [← hypEntries_neg hp hζ.pow_eq_one (toAdd (f' j))] at h1
      have h1' : u ^ (toAdd (f i)).val = u ^ ((-(toAdd (f' j)))).val := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu]
        exact h1)
      have h2 := (pow_inj_mod (x := u)).mp h1'
      rw [huo, Nat.mod_eq_of_lt (ZMod.val_lt _),
        Nat.mod_eq_of_lt (ZMod.val_lt _)] at h2
      have h3 : toAdd (f i) = -(toAdd (f' j)) := ZMod.val_injective p h2
      have h4 : toAdd (f' j) = -toAdd (f i) := by rw [h3, neg_neg]
      rw [h4, neg_one_mul]
  choose j ε hε hj using key
  exact ⟨j, ε, hε, fun f f' h i => hj i f f' h⟩

theorem ggKGUc_normalizer {n r p : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (ι : (Fin r → Multiplicative (ZMod p)) →* hypSU h r 0)
    (hι : ∀ f, (((ι f : hypSU h r 0) : GL (HypIndex r 0) K) :
      Matrix (HypIndex r 0) (HypIndex r 0) K) = diagonal (hypEntries ζ (fun i => toAdd (f i))))
    (g : hypSU h r 0) (hg : ∀ f, ∃ f', g * ι f * g⁻¹ = ι f') :
    ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f', g * ι f * g⁻¹ = ι f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
  obtain ⟨j, ε, hε, hrel⟩ := ggKGUc_monomial_data h hp ζ hζ ι hι g
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hjinj : Function.Injective j := by
    intro i i' hii'
    by_contra hne
    obtain ⟨f', hf'⟩ := hg (Pi.mulSingle i (ofAdd (1 : ZMod p)))
    have h1 := hrel (Pi.mulSingle i (ofAdd (1 : ZMod p))) f' hf' i
    have h3 := hrel (Pi.mulSingle i (ofAdd (1 : ZMod p))) f' hf' i'
    rw [SpCoord.toAdd_mulSingle i i 1, if_pos rfl, mul_one] at h1
    rw [SpCoord.toAdd_mulSingle i i' 1, if_neg (Ne.symm hne), mul_zero] at h3
    rw [← hii'] at h3
    have h2 : ε i = 0 := h1.symm.trans h3
    rcases hε i with hh | hh
    · rw [hh] at h2; exact (one_ne_zero : (1 : ZMod p) ≠ 0) h2
    · rw [hh] at h2; exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0) h2
  exact ⟨Equiv.ofBijective j hjinj.bijective_of_finite, ε, hε,
    fun f f' hff' i => hrel f f' hff' i⟩

end CFSG.StandardType

end
