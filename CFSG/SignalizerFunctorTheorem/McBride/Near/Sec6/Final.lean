module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.FinalAuxEx

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem thetaStarFun_eq
    (h : Counterexample p A θ) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    thetaStarFun p A θ a = θ a :=
  Sec6S33.thetaStarFun_eq_apply h ha ha1

theorem lemma616
    (h : Counterexample p A θ) {a : G}
    (ha : Subgroup.zpowers a ∈ rSetN p A θ 1) :
    ∀ x ∈ θ a, ∃ m n : ℕ, x ^ (2 ^ m * 3 ^ n) ∈ kOf (θ a) := fun x hx =>
  ⟨1, 1, by simpa using Sec6S33.pow_six_mem_kOf h ha hx⟩

theorem thm617a
    (h : Counterexample p A θ) :
    ∃! E : Subgroup G, E ∈ signalizerFunctorEk p 1 A ∧ E ∉ rSetN p A θ 1 := by
  obtain ⟨E, hE, hER⟩ := Sec6S33.exists_not_mem_rSetN h
  exact ⟨E, ⟨hE, hER⟩, fun E' hE' => Sec6S33.eq_of_not_mem_rSetN h hE'.1 hE hE'.2 hER⟩

theorem thm617b
    (h : Counterexample p A θ) {E : Subgroup G} (hE : E ∈ signalizerFunctorEk p 1 A)
    (hER : E ∉ rSetN p A θ 1) {f : G} (hf : f ∈ A) (hfE : f ∉ E) :
    E ⊔ Subgroup.zpowers f = A ⊓ khat (A ⊔ θ f) :=
  Sec6S33.eq_inf_khat h hE hER hf hfE

theorem lemma618
    (h : Counterexample p A θ) {B X : Subgroup G} (hB : B ∈ rSet p A θ)
    (hX : X ∈ assoc p A θ) (hXs : Group.IsSolvable X) (hXK : Admits (kOf (thetaOf θ B)) X) :
    X = ⊥ :=
  Sec6S33.eq_bot_of_rSet h hB hX hXs hXK

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
