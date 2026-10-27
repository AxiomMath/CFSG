module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.Background.Harris.OrdinaryProofs

namespace Case34A7

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem endIsField_one_of_zero_or_one [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤)
    (h : ∀ f ∈ endCommutant L, f = 0 ∨ f = 1) : EndIsField L 1 := by
  obtain ⟨e, ⟨α⟩⟩ := exists_endIsField hL
  have hnt := endCommutant_nontrivial hL
  have hcard : Nat.card (endCommutant L) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨0, 1, fun h01 => zero_ne_one h01, ?_⟩
    ext x
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, iff_true]
    rcases h x.1 x.2 with h0 | h1
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext h1)
  have hc : Nat.card (GaloisField 2 e) = 2 ^ 1 := by
    rw [← Nat.card_congr α.toEquiv, hcard]; simp
  exact ⟨α.trans (GaloisField.algEquivGaloisField 2 1 hc)⟩

theorem zero_or_one_of_probe {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) {u : V} (hu : u ≠ 0)
    (hfix : ∀ f ∈ endCommutant L, f u = 0 ∨ f u = u) :
    ∀ f ∈ endCommutant L, f = 0 ∨ f = 1 := by
  intro f hf
  rcases hfix f hf with h0 | h1
  · left
    by_contra hne
    have hinj := injective_of_mem_endCommutant hL hf hne
    exact hu (hinj (h0.trans (map_zero f).symm))
  · right
    have hg : f - 1 ∈ endCommutant L := Subalgebra.sub_mem _ hf (Subalgebra.one_mem _)
    by_contra hne
    have hne' : f - 1 ≠ 0 := sub_ne_zero.2 hne
    have hinj := injective_of_mem_endCommutant hL hg hne'
    apply hu
    apply hinj
    simp [h1]

theorem endIsField_one_of_fixed [Finite V] {L : Subgroup (GLV V)} (hL : IsIrr L ⊤)
    {H₀ : Set (GLV V)} (hH₀ : H₀ ⊆ L) {u : V} (hu : u ≠ 0) (hfu : ∀ h ∈ H₀, h u = u)
    (hS : ∀ w : V, (∀ h ∈ H₀, h w = w) → w = 0 ∨ w = u) : EndIsField L 1 := by
  refine endIsField_one_of_zero_or_one hL (zero_or_one_of_probe hL hu fun f hf => hS _ fun h hh => ?_)
  rw [← endCommutant_apply_comm hf (hH₀ hh), hfu h hh]

end Case34A7

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
