module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.SpecialLinear

theorem ggCoxeterA_mulEquivPerm (N : ℕ) :
    ∃ e : (CoxeterMatrix.A N).Group ≃* Equiv.Perm (Fin (N + 1)),
      ∀ k : Fin N, e ((CoxeterMatrix.A N).simple k) = Equiv.swap k.castSucc k.succ := by
  have h := coxeterMatrix_isFiniteType_A_eq N
  suffices H : ∀ M : CoxeterMatrix (Fin N), coxeterMatrix (isFiniteType_A N) = M →
      ∃ e : M.Group ≃* Equiv.Perm (Fin (N + 1)),
        ∀ k : Fin N, e (M.simple k) = Equiv.swap k.castSucc k.succ from H _ h
  intro M hM
  subst hM
  exact ⟨(typeAWeylEquiv N).symm, fun k => by
    rw [MulEquiv.symm_apply_eq]
    exact (typeAWeylEquiv_swap N k).symm⟩

theorem ggTorusAutomizerClauses_of_permAut {N : ℕ} {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} (n : Fin N → L')
    (hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (ρ : Equiv.Perm (Fin (N + 1)) →* MulAut ↥A) (hρ : Function.Injective ρ)
    (hrange : ρ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hsw : ∀ k : Fin N, ρ (Equiv.swap k.castSucc k.succ) = ggConjAut A (hn k)) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
        Subgroup.closure (Set.range fun k => ggConjAut A (hn k)) ∧
      ∃ e : (CoxeterMatrix.A N).Group ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A),
        ∀ k, (e ((CoxeterMatrix.A N).simple k) : MulAut ↥A) = ggConjAut A (hn k) := by
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm N
  have hgen : Subgroup.closure (Set.range fun k : Fin N => Equiv.swap k.castSucc k.succ) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submonoid.closure (Set.range fun k : Fin N => Equiv.swap k.castSucc k.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    exact Submonoid.closure_le.mpr (fun y hy => Subgroup.subset_closure hy) hx
  refine ⟨?_, (e0.trans (MonoidHom.ofInjective hρ)).trans (MulEquiv.subgroupCongr hrange), ?_⟩
  · rw [← hrange, MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, ← Set.range_comp]
    congr 2
    funext k
    exact hsw k
  · intro k
    simp only [MulEquiv.trans_apply, he0, MulEquiv.subgroupCongr_apply]
    rw [MonoidHom.ofInjective_apply]
    exact hsw k

end CFSG.StandardType
