module

public import CFSG.Quasithin.EmptyFaithful.S1421QA25Lat
public import CFSG.Quasithin.EmptyFaithful.S1421QA25Defs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Quasithin.A312M23 CFSG.Quasithin.H.MathieuLat

namespace QA25

theorem exists_conj_of_isSylowTwoOf_top {X : Type} [Group X] [Finite X] {S₁ S₂ : Subgroup X}
    (h₁ : IsSylowTwoOf S₁ ⊤) (h₂ : IsSylowTwoOf S₂ ⊤) :
    ∃ g : X, S₁.map (MulAut.conj g).toMonoidHom = S₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ¬ 2 ∣ S.index := by
    intro S hS
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  let P₁ : Sylow 2 X := h₁.2.1.toSylow (hidx S₁ h₁)
  let P₂ : Sylow 2 X := h₂.2.1.toSylow (hidx S₂ h₂)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₁ P₂
  refine ⟨g, ?_⟩
  have h := congrArg (fun T : Sylow 2 X => (T : Subgroup X)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  exact h

theorem m23L34Diagram_holds :
    M23L34Diagram := by
  intro M _ _ hM A S hA hS hSN
  rw [← stableMax_iff]
  obtain ⟨e0⟩ := hM
  let e : M ≃* Gm := e0
  have htop : (⊤ : Subgroup M).map e.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ e.surjective
  have hS1 : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    have := isSylowTwoOf_map_equiv e hS
    rwa [htop] at this
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hS1 m23_S_sylow
  let f : M ≃* Gm := e.trans (MulAut.conj g)
  have hSf : S.map f.toMonoidHom = m23Ctx.S := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hAf : IsPSL 3 2 2 ↥(A.map f.toMonoidHom) :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv
      (A.equivMapOfInjective f.toMonoidHom f.injective).symm hA
  have hSNf : m23Ctx.S ≤ Subgroup.normalizer ((A.map f.toMonoidHom : Subgroup Gm) : Set Gm) := by
    rw [← hSf]
    rintro _ ⟨s, hs, rfl⟩
    exact (mem_normalizer_map_equiv f A s).mpr (hSN hs)
  have h1 := (stableMax_lattice hAf hSNf).map f.symm
  rw [← hSf, map_map_symm, map_map_symm] at h1
  exact h1

end QA25

end CFSG.Quasithin
