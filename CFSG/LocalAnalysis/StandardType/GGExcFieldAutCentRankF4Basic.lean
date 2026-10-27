module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.ExcFieldAutCentRankF4

open CFSG.Open (IsElemAbelian)

theorem pullback_elemAbelian {C G : Type} [Group C] [Group G] (ψ : C →* G)
    (hinj : Function.Injective ψ) (p : ℕ) (E : Subgroup G) (hEr : E ≤ ψ.range)
    (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap ψ) ∧ Nat.card (E.comap ψ) = Nat.card E := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply hinj
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨ψ a, a.2⟩ ⟨ψ b, b.2⟩)
    simpa [map_mul] using h
  · apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hx
  · have h1 := Nat.card_congr (Subgroup.equivMapOfInjective (E.comap ψ) ψ hinj).toEquiv
    rw [Subgroup.map_comap_eq_self hEr] at h1
    exact h1

theorem exists_aut_of_mem_normalizer {C G : Type} [Group C] [Group G] (ψ : C →* G)
    (hinj : Function.Injective ψ) {y : G} (hy : y ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ α : MulAut C, ∀ u, ψ (α u) = y * ψ u * y⁻¹ := by
  let e : C ≃* ψ.range := MonoidHom.ofInjective hinj
  refine ⟨e.trans ((ψ.range.normalizerMonoidHom ⟨y, hy⟩).trans e.symm), fun u => ?_⟩
  have h1 : (e u : G) = ψ u := rfl
  have h2 : ∀ x : ψ.range, ψ (e.symm x) = (x : G) := fun x => by
    obtain ⟨c, hc⟩ := x.2
    have : e.symm x = c := e.symm_apply_eq.2 (Subtype.ext hc.symm)
    rw [this]
    exact hc
  show ψ (e.symm ((ψ.range.normalizerMonoidHom ⟨y, hy⟩) (e u))) = _
  rw [h2, Subgroup.normalizerMonoidHom_apply_apply_coe, h1]

end CFSG.StandardType.ExcFieldAutCentRankF4
