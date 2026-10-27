module

public import CFSG.Quasithin.Background.G118NT
public import CFSG.Quasithin.Background.G93ApplyRestrict
public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

namespace G118

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Glue

variable {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem endOn_eq_endCommutant (hHI : Invariant H I) :
    endOn H I = endCommutant (restrictRange H I hHI) := by
  unfold endOn endCommutant
  congr 1
  ext f
  constructor
  · rintro ⟨h, hh, hH, rfl⟩
    exact ⟨_, restrictEquiv_mem_restrictRange hHI hH, rfl⟩
  · rintro ⟨h', hh', rfl⟩
    obtain ⟨h, hH, hk⟩ := (mem_restrictRange_iff' hHI).1 hh'
    exact ⟨h, hHI.conjSub_eq hH, hH, by rw [hk]⟩

theorem natCard_F_of_endIsField (D : E11Data H I) (hHI : Invariant H I) {e : ℕ} (he : e ≠ 0)
    (h : EndIsField (restrictRange H I hHI) e) : Nat.card D.F = 2 ^ e := by
  obtain ⟨ψ⟩ := h
  have hcard : Nat.card ↥(endOn H I) = Nat.card ↥(endCommutant (restrictRange H I hHI)) := by
    rw [endOn_eq_endCommutant hHI]
  rw [← Nat.card_congr D.endEquiv.toEquiv, hcard, Nat.card_congr ψ.toEquiv,
    GaloisField.card 2 e he]

theorem endTrivial_iff_card_two [Finite V] (D : E11Data H I) (hI0 : I ≠ ⊥) :
    EndTrivial H I ↔ Nat.card D.F = 2 := by
  have hcard : Nat.card D.F = Nat.card ↥(endOn H I) := (Nat.card_congr D.endEquiv.toEquiv).symm
  have : Finite ↥(endOn H I) := Finite.of_equiv D.F D.endEquiv.symm.toEquiv
  have hne : (0 : endOn H I) ≠ 1 := by
    intro h
    have h1 : (0 : Module.End (ZMod 2) ↥I) = 1 := congrArg Subtype.val h
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff I).1 hI0
    have := congrArg (fun T : Module.End (ZMod 2) ↥I => ((T ⟨x, hx⟩ : ↥I) : V)) h1
    exact hx0 (by simpa using this.symm)
  rw [hcard]
  constructor
  · intro hET
    have hset : (Set.univ : Set (endOn H I)) = {0, 1} := by
      ext f
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
      rcases hET f.1 f.2 with h | h
      · left
        exact Subtype.ext h
      · right
        exact Subtype.ext h
    rw [← Set.ncard_univ, hset, Set.ncard_pair hne]
  · intro h2 f hf
    have hset : (Set.univ : Set (endOn H I)) = {0, 1} := by
      refine (Set.eq_of_subset_of_ncard_le (by intro x _; trivial) ?_ (Set.toFinite _)).symm
      rw [Set.ncard_pair hne, Set.ncard_univ, h2]
    have hf' : (⟨f, hf⟩ : endOn H I) ∈ (Set.univ : Set (endOn H I)) := Set.mem_univ _
    rw [hset] at hf'
    rcases hf' with h | h
    · left
      exact congrArg Subtype.val h
    · right
      exact congrArg Subtype.val h

end Glue

end G118

end G11

end CFSG.Quasithin
