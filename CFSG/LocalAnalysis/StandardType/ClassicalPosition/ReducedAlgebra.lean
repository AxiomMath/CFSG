module

public import TauCeti.LinearAlgebra.End.FiniteOrder

public section

namespace CFSG.StandardType.ClassicalPosition

private lemma redAux_isSemisimple_commute {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Set (Module.End K V))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, ∃ o : ℕ, Odd o ∧ s ^ o = 1) :
    ∀ z ∈ Algebra.adjoin K S, z.IsSemisimple ∧ ∀ s ∈ S, Commute z s := by
  intro z hz
  refine Algebra.adjoin_induction (p := fun z _ => z.IsSemisimple ∧ ∀ s ∈ S, Commute z s)
    ?_ ?_ ?_ ?_ hz
  · intro x hx
    obtain ⟨o, ho, hxo⟩ := hodd x hx
    exact ⟨TauCeti.End.isSemisimple_of_pow_eq_one (by
        intro h
        exact ho.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 o).mp h)) hxo,
      fun s hs => hS x hx s hs⟩
  · intro r
    exact ⟨by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Module.End.IsSemisimple_smul r Module.End.isSemisimple_id,
      fun s _ => Algebra.commute_algebraMap_left r s⟩
  · intro x y _ hy ihx ihy
    obtain ⟨hxs, hxc⟩ := ihx
    obtain ⟨hys, hyc⟩ := ihy
    exact ⟨Module.End.IsSemisimple.add_of_commute
        (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy hxc) hxs hys,
      fun s hs => (hxc s hs).add_left (hyc s hs)⟩
  · intro x y _ hy ihx ihy
    obtain ⟨hxs, hxc⟩ := ihx
    obtain ⟨hys, hyc⟩ := ihy
    exact ⟨Module.End.IsSemisimple.mul_of_commute
        (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy hxc) hxs hys,
      fun s hs => (hxc s hs).mul_left (hyc s hs)⟩

theorem isReduced_adjoin_of_commute_of_odd {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Set (Module.End K V))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, ∃ o : ℕ, Odd o ∧ s ^ o = 1) :
    IsReduced (Algebra.adjoin K S) := by
  rw [isReduced_iff]
  intro x hx
  have hxval : IsNilpotent (x : Module.End K V) := by
    simpa using hx.map (Subalgebra.val (Algebra.adjoin K S))
  have hsem : (x : Module.End K V).IsSemisimple :=
    (redAux_isSemisimple_commute S hS hodd x x.2).1
  exact Subtype.ext (Module.End.eq_zero_of_isNilpotent_isSemisimple hxval hsem)

end CFSG.StandardType.ClassicalPosition
