module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeInputs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.HardMathSupport.Solomon.Coordinator CFSG.Open

private theorem s15k_mclorth_plus_singular {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (k : ℕ)
    (b : Module.Basis (Fin k ⊕ Fin k) (ZMod 2) V) (Q : QuadraticForm (ZMod 2) V)
    (hb : ∀ v, Q v = GLAQPlus (ZMod 2) k (b.equivFun v)) :
    Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range fun i : Fin k => b (Sum.inl i))) = k ∧
      ∀ u ∈ Submodule.span (ZMod 2) (Set.range fun i : Fin k => b (Sum.inl i)), Q u = 0 := by
  have hli : LinearIndependent (ZMod 2) (fun i : Fin k => b (Sum.inl i)) :=
    b.linearIndependent.comp (fun i : Fin k => Sum.inl i) Sum.inl_injective
  refine ⟨?_, ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · intro u hu
    have hsupp : ((b.repr u).support : Set (Fin k ⊕ Fin k)) ⊆
        Set.range (fun i : Fin k => Sum.inl i) := by
      have hu' : u ∈ Submodule.span (ZMod 2)
          (b '' Set.range (fun i : Fin k => Sum.inl i)) := by
        simpa only [Set.range_comp'] using hu
      exact (b.mem_span_image).1 hu'
    have hzero : ∀ j : Fin k, b.equivFun u (Sum.inr j) = 0 := by
      intro j
      have hmem : Sum.inr j ∉ (b.repr u).support := by
        intro hmem
        obtain ⟨i, hi⟩ := hsupp hmem
        exact Sum.inl_ne_inr hi
      simpa only [Module.Basis.equivFun_apply] using Finsupp.notMem_support_iff.mp hmem
    rw [hb u]
    change (∑ i : Fin k, b.equivFun u (Sum.inl i) * b.equivFun u (Sum.inr i)) = 0
    exact Finset.sum_eq_zero fun i _ => by rw [hzero i, mul_zero]

private theorem s15k_mclorth_minus_reindex {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (k : ℕ)
    (b : Module.Basis (GLAMinusIdx (k - 1)) (ZMod 2) V) (v : V) :
    GLAQMinus (k - 1) (1 : ZMod 2) 1 (b.equivFun v) =
      StatedQuadMinus k (ZMod 2) 1 1
        ((b.reindex (Equiv.sumAssoc (Fin (k - 1)) (Fin (k - 1)) (Fin 2))).equivFun v) := by
  set e : (Fin (k - 1) ⊕ Fin (k - 1)) ⊕ Fin 2 ≃ Fin (k - 1) ⊕ (Fin (k - 1) ⊕ Fin 2) :=
    Equiv.sumAssoc (Fin (k - 1)) (Fin (k - 1)) (Fin 2) with he
  set w : (Fin (k - 1) ⊕ Fin (k - 1)) ⊕ Fin 2 → ZMod 2 := b.equivFun v with hw
  have hw' : (b.reindex e).equivFun v = w ∘ e.symm := by
    funext x
    simp only [hw, Function.comp_apply, Module.Basis.equivFun_apply,
      Module.Basis.repr_reindex_apply]
  rw [hw']
  change (∑ i : Fin (k - 1), w (Sum.inl (Sum.inl i)) * w (Sum.inl (Sum.inr i))) +
      w (Sum.inr 0) ^ 2 + 1 * w (Sum.inr 0) * w (Sum.inr 1) + 1 * w (Sum.inr 1) ^ 2 =
    (∑ i : Fin (k - 1), (w ∘ e.symm) (Sum.inl i) * (w ∘ e.symm) (Sum.inr (Sum.inl i))) +
      (w ∘ e.symm) (Sum.inr (Sum.inr 0)) ^ 2 +
      1 * (w ∘ e.symm) (Sum.inr (Sum.inr 0)) * (w ∘ e.symm) (Sum.inr (Sum.inr 1)) +
      1 * (w ∘ e.symm) (Sum.inr (Sum.inr 1)) ^ 2
  simp only [he, Function.comp_apply, Equiv.sumAssoc_symm_apply_inl,
    Equiv.sumAssoc_symm_apply_inr_inl, Equiv.sumAssoc_symm_apply_inr_inr]

theorem s15k_mcl_orth {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (D : McRep J R) (hev : Even (Module.finrank (ZMod 2) D.V))
    (h4 : 4 ≤ Module.finrank (ZMod 2) D.V) (Q : QuadraticForm (ZMod 2) D.V)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (h : D.ρ.range = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) D.V).toMonoidHom)
    (hE : 6 ≤ Module.finrank (ZMod 2) D.V ∨
      ¬ ∃ U : Submodule (ZMod 2) D.V, Module.finrank (ZMod 2) U = 2 ∧ ∀ u ∈ U, Q u = 0) :
    (∃ n : ℕ, 6 ≤ n ∧ NatOrthPlus J R ⊥ n 1) ∨ (∃ n : ℕ, 4 ≤ n ∧ NatOrthMinus J R ⊥ n 1) := by
  obtain ⟨k, hk⟩ := hev
  have hdim : Module.finrank (ZMod 2) D.V = 2 * k := by omega
  have hk2 : 2 ≤ k := by omega
  have hdiv : (k + k) / 2 = k := by
    rw [← Nat.two_mul]
    exact Nat.mul_div_right k (by norm_num)
  have hG : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) D.V,
      g ∈ D.ρ.range ↔ ∀ v : D.V, Q ((g : D.V →ₗ[ZMod 2] D.V) v) = Q v := by
    intro g
    rw [h, Subgroup.mem_comap, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    rfl
  rcases mclt_exists_basis_quadratic Q hnd (n := k) (by omega) hdim with ⟨b, hb⟩ | ⟨b, hb⟩
  · have hΓ : D.ρ.range.map (mclt_glMatrixEquiv b).toMonoidHom =
        CFSG.MatrixModel.isometryCore (StatedQuadPlus k (ZMod 2)) :=
      mclt_map_glMatrixEquiv_eq_closure (Q := fun v => Q v) b hb hG
    have hreal : (FFModel.nat (CFSG.MatrixModel.isometryCore
        (StatedQuadPlus k (ZMod 2)))).Realizes J R ⊥ :=
      s15k_mcl_realizes_nat D b _ hΓ
    have hk3 : 6 ≤ k + k := by
      by_contra hlt
      have hno : ¬ ∃ U : Submodule (ZMod 2) D.V,
          Module.finrank (ZMod 2) U = 2 ∧ ∀ u ∈ U, Q u = 0 :=
        hE.resolve_left (by omega)
      have hk_eq : k = 2 := by omega
      have hpl := s15k_mclorth_plus_singular k b Q hb
      refine hno ⟨Submodule.span (ZMod 2) (Set.range fun i : Fin k => b (Sum.inl i)),
        ?_, hpl.2⟩
      rw [hpl.1]
      exact hk_eq
    refine Or.inl ⟨k + k, hk3, ?_⟩
    exact ⟨⟨k, rfl⟩, ZMod 2, inferInstance, inferInstance, by simp [Nat.card_zmod],
      by rw [hdiv]; exact hreal⟩
  · let b' : Module.Basis (Fin (k - 1) ⊕ (Fin (k - 1) ⊕ Fin 2)) (ZMod 2) D.V :=
      b.reindex (Equiv.sumAssoc (Fin (k - 1)) (Fin (k - 1)) (Fin 2))
    have hb' : ∀ v, Q v = StatedQuadMinus k (ZMod 2) 1 1 (b'.equivFun v) := by
      intro v
      rw [hb v]
      exact s15k_mclorth_minus_reindex k b v
    have hΓ' : D.ρ.range.map (mclt_glMatrixEquiv b').toMonoidHom =
        CFSG.MatrixModel.isometryCore (StatedQuadMinus k (ZMod 2) 1 1) :=
      mclt_map_glMatrixEquiv_eq_closure (Q := fun v => Q v) b' hb' hG
    have hreal : (FFModel.nat (CFSG.MatrixModel.isometryCore
        (StatedQuadMinus k (ZMod 2) 1 1))).Realizes J R ⊥ :=
      s15k_mcl_realizes_nat D b' _ hΓ'
    refine Or.inr ⟨k + k, by omega, ?_⟩
    exact ⟨⟨k, rfl⟩, ZMod 2, inferInstance, inferInstance, 1, 1, by simp [Nat.card_zmod],
      by decide, by rw [hdiv]; exact hreal⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
