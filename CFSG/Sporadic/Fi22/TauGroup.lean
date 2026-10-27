module

public import CFSG.Sporadic.Fi22.Nfp
public import CFSG.Fischer.Aut.TauGroup

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ptD_conj_mem_tauGroup
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ tauAut) :
    (ptD.symm.trans (σ.trans ptD) : Equiv.Perm D) ∈ tauGroup pair_D := by
  intro x y
  obtain ⟨i, rfl⟩ := ptD.surjective x
  obtain ⟨j, rfl⟩ := ptD.surjective y
  show ptD (σ (ptD.symm (tauE pair_D (ptD i) (ptD j)))) =
    tauE pair_D (ptD (σ (ptD.symm (ptD i)))) (ptD (σ (ptD.symm (ptD j))))
  have h1 : tauE pair_D (ptD i) (ptD j) = tauD (ptD i) (ptD j) := rfl
  rw [h1, ← ptD_tauIdx, Equiv.symm_apply_apply, tauAut_apply hσ, ptD_tauIdx,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

theorem ptD_symm_conj_mem_tauAut
    {σ : Equiv.Perm D} (hσ : σ ∈ tauGroup pair_D) :
    (ptD.trans (σ.trans ptD.symm) : Equiv.Perm (Fin 3510)) ∈ tauAut := by
  apply mem_tauAut_of_apply
  intro i j
  show ptD.symm (σ (ptD (tauIdx i j))) =
    tauIdx (ptD.symm (σ (ptD i))) (ptD.symm (σ (ptD j)))
  apply ptD.injective
  rw [Equiv.apply_symm_apply, ptD_tauIdx, ptD_tauIdx, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact hσ (ptD i) (ptD j)

@[expose] noncomputable def tauAutEquiv :
    tauAut ≃* tauGroup pair_D where
  toFun σ := ⟨ptD.symm.trans ((σ : Equiv.Perm (Fin 3510)).trans ptD),
    ptD_conj_mem_tauGroup σ.2⟩
  invFun σ := ⟨ptD.trans ((σ : Equiv.Perm D).trans ptD.symm), ptD_symm_conj_mem_tauAut σ.2⟩
  left_inv σ := by ext i; simp
  right_inv σ := by ext x; simp
  map_mul' σ π := by ext x; simp

theorem card_tauGroup :
    Nat.card (tauGroup pair_D) = 129123503308800 := by
  rw [← Nat.card_congr tauAutEquiv.toEquiv, card_tauAut]

theorem index_innerTau_range :
    (innerTau pair_D).range.index = 2 := by
  have hinj : Function.Injective (innerTau pair_D) := innerTau_injective pair_D center_eq_bot
  have hcard : Nat.card (innerTau pair_D).range = 64561751654400 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_J]
  have := (innerTau pair_D).range.card_mul_index
  rw [hcard, card_tauGroup] at this
  omega

theorem tauGroup_complete_D :
    ∀ φ : MulAut (tauGroup pair_D), ∃ σ : tauGroup pair_D, φ = MulAut.conj σ :=
  tauGroup_complete pair_D center_eq_bot commutator_eq_top pair_eq_D index_innerTau_range

end CFSG.Sporadic.Fi22
