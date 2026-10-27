module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.F918X.AL2

theorem nontrivial_of_quasisimple {B : Type*} [Group B] (hB : CFSG.IsQuasisimple B) :
    Nontrivial B := by
  have hs : IsSimpleGroup (B ⧸ Subgroup.center B) := hB.2.1
  exact (QuotientGroup.mk_surjective (s := Subgroup.center B)).nontrivial

theorem bijective_of_surjective_of_quasisimple {A B : Type*} [Group A] [IsSimpleGroup A]
    [Group B] (hB : CFSG.IsQuasisimple B) (π : A →* B) (hπ : Function.Surjective π) :
    Function.Bijective π := by
  have := nontrivial_of_quasisimple hB
  refine ⟨?_, hπ⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff π).mp h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : B)
    obtain ⟨a, rfl⟩ := hπ x
    refine hx ?_
    have ha : a ∈ π.ker := by rw [h]; trivial
    exact ha

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : Subgroup.center A = ⊥) : Subgroup.center B = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_center_iff] at hz
  have hz' : e.symm z ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hz (e g)
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  simpa using congrArg e hz'

end CFSG.Quasithin.F918X.AL2
