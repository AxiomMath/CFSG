module

public import CFSG.Quasithin.SteinbergBSSymplecticRoots
public import CFSG.Quasithin.Vol2.Ch3E213MP6CA

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp uElt uElt_mul uElt_inv
  antiSp_ext uMat_zero antiUnipotent antiUnipotentCenter minorAut)
open CFSG.Quasithin.SteinbergBS (rootLong)

variable {k : Type} [Field k] [CharP k 2]

@[expose] def szCentre (F₀ : Subfield k) (a : ℕ) : Subgroup (antiSp k) where
  carrier := {g | ∃ b ∈ F₀, g = uElt 0 b (b ^ 2 ^ (a + 1)) 0}
  mul_mem' := by
    rintro _ _ ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
    refine ⟨b + b', F₀.add_mem hb hb', ?_⟩
    rw [uElt_mul, add_pow_char_pow]
    congr 1 <;> ring
  one_mem' := ⟨0, F₀.zero_mem, by
    rw [zero_pow (pow_ne_zero _ two_ne_zero)]
    exact antiSp_ext uMat_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨b, hb, ?_⟩
    rw [uElt_inv]
    congr 1
    ring

theorem mem_szCentre {F₀ : Subfield k} {a : ℕ} {g : antiSp k} :
    g ∈ szCentre F₀ a ↔ ∃ b ∈ F₀, g = uElt 0 b (b ^ 2 ^ (a + 1)) 0 :=
  Iff.rfl

@[expose] def FactSp4CTwo : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] (n : ℕ), 2 ≤ n → Nat.card k = 2 ^ n →
    ∀ W : Subgroup (antiSp k), W ≤ antiUnipotentCenter k → W ⊓ rootLong k = ⊥ →
      SpansCenter W →
      (∃ h ∈ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)), ∃ j : ℕ, Odd j ∧
        ∀ w ∈ W, (MulAut.conj h * minorAut k ^ j) w ∈ W) →
      ∀ g : antiSp k, IsOppStd g →
      (∀ x ∈ W ⊔ W.map (MulAut.conj g).toMonoidHom, ¬ IsTransvection x) →
      (∀ x ∈ W ⊔ W.map (MulAut.conj g).toMonoidHom, ¬ IsTransvection (minorAut k x)) →
      ∃ (F₀ : Subfield k) (a : ℕ), 1 ≤ a ∧ Nat.card F₀ = 2 ^ (2 * a + 1) ∧
        ∃ d : antiSp k, IsUpper d ∧ W ≤ (szCentre F₀ a).map (MulAut.conj d).toMonoidHom

end CFSG.Quasithin.Ch3E213M
