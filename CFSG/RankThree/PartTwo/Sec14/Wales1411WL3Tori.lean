module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WL3Odd
import CFSG.RankThree.PartTwo.Sec14.Wales1411WTori

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

@[expose] def KL3HessTori : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ f →
    Sec4.IsoLThreePi X p f → ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E →
      Nat.card E = 9 →
      (∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
        ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁) →
      (∀ W : Subgroup X, IsPGroup 2 W → E ≤ Subgroup.normalizer (W : Set X) → W ≠ ⊥ →
        ∃ x ∈ E, W ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set X))) ∧
      (∀ x ∈ E, ∀ x' ∈ E, ∀ W W' : Subgroup X, W ≠ ⊥ → W' ≠ ⊥ →
        W ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set X)) →
        W' ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x'} : Set X)) →
        E ≤ Subgroup.normalizer (W : Set X) → E ≤ Subgroup.normalizer (W' : Set X) →
        ∃ n ∈ (W ⊔ W') ⊓ Subgroup.normalizer (E : Set X),
          (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set X))).map
              (MulAut.conj n).toMonoidHom =
            CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x'} : Set X)))

namespace Wales1411W

variable {M : Type} [Group M] [Finite M]

theorem le_normalizer_pCoreOf_centralizer {E : Subgroup M} (hE : IsMulCommutative E)
    {x : M} (hx : x ∈ E) :
    E ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set M)) : Set M) ∧
      Subgroup.centralizer (E : Set M) ≤
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({x} : Set M)) : Set M) := by
  have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Subgroup.centralizer ({x} : Set M))
  refine ⟨fun y hy => hN ?_, (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx)).trans hN⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hE.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)

end Wales1411W

open Wales1411W in
theorem kl3HessETrans2_of_tori (h : KL3HessTori) : KL3HessETrans2 := by
  intro X _ _ p f _ hp2 hf hiso E hEe hE9 htr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := h X p f hp2 hf hiso E hEe hE9 htr
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEe.2 x x.2)⟩
  exact etrans2_of_tori (N := ⊤) (fun x => CFSG.Open.pCoreOf 2 (Subgroup.centralizer {x})) hE3
    (fun _ _ _ => Subgroup.mem_top _)
    (fun x _ => CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (fun x hx => (le_normalizer_pCoreOf_centralizer hEe.1 hx).1)
    (fun x hx => (le_normalizer_pCoreOf_centralizer hEe.1 hx).2)
    (fun W _ hW2 hEW hW => h1 W hW2 hEW hW) h2

end CFSG.RankThree.PartTwo.Sec14
