module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

@[expose] noncomputable def qTwoOneVec (m : ℕ) (h3 : 3 ∣ m) : ↥(sumZero m 3) :=
  ⟨fun _ => Multiplicative.ofAdd (1 : ZMod 3), by
    rw [mem_sumZero]
    simp only [toAdd_ofAdd]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [CharP.cast_eq_zero_iff (ZMod 3) 3 m]
    exact h3⟩

abbrev QTwoHm (m : ℕ) (h3 : 3 ∣ m) : Type := ↥(sumZero m 3) ⧸ Subgroup.zpowers (qTwoOneVec m h3)

abbrev QTwoQm (m : ℕ) : Type :=
  (Fin m → Multiplicative (ZMod 3)) ⧸
    Subgroup.zpowers (fun _ => Multiplicative.ofAdd (1 : ZMod 3))

structure IsAugModel (m : ℕ) (V : Type) [Group V] (ρ : Equiv.Perm (Fin m) →* MulAut V) : Prop where
  ex : ∃ e : ↥(sumZero m 3) ≃* V, ∀ σ v, e (permAutV σ v) = ρ σ (e v)

structure IsHmModel (m : ℕ) (h3 : 3 ∣ m) (V : Type) [Group V]
    (ρ : Equiv.Perm (Fin m) →* MulAut V) : Prop where
  ex : ∃ π : ↥(sumZero m 3) →* V, Function.Surjective π ∧
    (∀ v, π v = 1 ↔ v ∈ Subgroup.zpowers (qTwoOneVec m h3)) ∧
    ∀ σ v, π (permAutV σ v) = ρ σ (π v)

structure IsQmModel (m : ℕ) (V : Type) [Group V] (ρ : Equiv.Perm (Fin m) →* MulAut V) : Prop where
  ex : ∃ π : (Fin m → Multiplicative (ZMod 3)) →* V, Function.Surjective π ∧
    (∀ v, π v = 1 ↔ v ∈ Subgroup.zpowers (fun _ => Multiplicative.ofAdd (1 : ZMod 3))) ∧
    ∀ σ (v : Fin m → Multiplicative (ZMod 3)), π (fun i => v (σ⁻¹ i)) = ρ σ (π v)

end CFSG.StandardType.QTwo

end
