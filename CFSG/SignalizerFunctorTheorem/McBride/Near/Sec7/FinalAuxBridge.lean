module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.Summary
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7.FinalAux3

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem Data.mk'
    (h : Counterexample p A θ) {E : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hEs : Group.IsSolvable (thetaOf θ E)) : Data h E := by
  obtain ⟨E₀, hE₀, J, inst, hJ, hnab, hE₀s, hb, hc, hd, he⟩ := h.thm61
  have hEE : E₀ = E := by
    obtain ⟨E', _, huniq⟩ := h.thm617a
    have h1 : E₀ ∉ rSetN p A θ 1 := fun hmem => (h.mem_rSetN_iff.mp hmem).2.2.1 hE₀s
    have h2 : E ∉ rSetN p A θ 1 := fun hmem => (h.mem_rSetN_iff.mp hmem).2.2.1 hEs
    exact (huniq E₀ ⟨hE₀, h1⟩).trans (huniq E ⟨hE, h2⟩).symm
  subst hEE
  have hp := h.hyp.prime
  refine ⟨hE, hEs, fun f hf hfE hsol => ?_, fun f hf hfE hs => ?_,
    fun f hf hfE => (hb f hf hfE).2.2.1, hc, hd.2, he⟩
  · obtain ⟨e⟩ := (hb f hf hfE).1
    have h1 : Group.IsSolvable ↥(kOf (θ f)) :=
      Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (kOf_le (θ f)))
    have h2 : Group.IsSolvable (Fin p → J) :=
      Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    exact not_isSolvable_pi hp.one_le hnab h2
  · obtain ⟨e⟩ := (hb f hf hfE).1
    have h2 : IsSimpleGroup (Fin p → J) := e.symm.isSimpleGroup
    exact not_isSimpleGroup_pi hnab hp.two_le h2

theorem VData.exists
    (h : Counterexample p A θ) {E : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hEs : Group.IsSolvable (thetaOf θ E)) :
    ∃ (V : Subgroup G) (r : ℕ), VData p A θ E V r := by
  obtain ⟨r, hr, -, V, hmax, -, hcomm, hsyl, hgen⟩ := h.thm62 hE hEs
  exact ⟨V, r, hr, hmax.1.1, hmax.1.2, hcomm,
    fun f hf hfE => ⟨(hsyl f hf hfE).2.1, (hsyl f hf hfE).2.2⟩, hgen⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35
