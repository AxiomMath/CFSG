module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.GroupTheory.Perm.ClosureSwap

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem closure_swaps_of_connected {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (hG : G.Connected) (S : Subgroup (Equiv.Perm ι))
    (hS : ∀ u v : ι, G.Adj u v → Equiv.swap u v ∈ S) : S = ⊤ := by
  classical
  have hwalk : ∀ u v : ι, G.Reachable u v → Equiv.swap u v ∈ S := by
    intro u v h
    obtain ⟨p⟩ := h
    induction p with
    | nil => rw [Equiv.swap_self]; exact S.one_mem
    | cons h p ih => exact SubmonoidClass.swap_mem_trans S (hS _ _ h) ih
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap]
  apply (Subgroup.closure_le _).mpr
  rintro σ ⟨a, b, -, rfl⟩
  exact hwalk a b (hG.preconnected a b)

private theorem w16g_map_mul (U : Subgroup W) (g h : MulAut W) :
    (U.map g.toMonoidHom).map h.toMonoidHom = U.map (h * g).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem w16g_map_map_inv (U : Subgroup W) (g : MulAut W) :
    (U.map g.toMonoidHom).map (g⁻¹).toMonoidHom = U := by
  rw [w16g_map_mul, inv_mul_cancel]
  have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by ext x; rfl
  rw [hone, Subgroup.map_id]

private theorem w16g_map_map_inv' (U : Subgroup W) (g : MulAut W) :
    (U.map (g⁻¹).toMonoidHom).map g.toMonoidHom = U := by
  rw [w16g_map_mul, mul_inv_cancel]
  have hone : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by ext x; rfl
  rw [hone, Subgroup.map_id]

private theorem w16g_eq_swap_of_apply {α : Type*} [DecidableEq α] (π : Equiv.Perm α) {a b : α}
    (ha : π a = b) (hb : π b = a)
    (hfix : ∀ x, x ≠ a → x ≠ b → π x = x) : π = Equiv.swap a b := by
  ext x
  by_cases hxa : x = a
  · rw [hxa, ha, Equiv.swap_apply_left]
  · by_cases hxb : x = b
    · rw [hxb, hb, Equiv.swap_apply_right]
    · rw [hfix x hxa hxb, Equiv.swap_apply_of_ne_of_ne hxa hxb]

private theorem w16g_one_toMonoidHom :
    ((1 : MulAut W)).toMonoidHom = MonoidHom.id W := by
  ext x; rfl

theorem s13_deltaSym_of_edge_swaps {A : Subgroup (MulAut W)} {t : MulAut W} {r m : ℕ}
    (C : Set (Subgroup W)) (hC : C.ncard = r + 1) (hrk : ∀ U ∈ C, rk ↥U = m)
    (hind : sSupIndep C)
    (hperm : ∀ g ∈ A ⊓ stabSub (sSup C), ∀ U ∈ C, U.map g.toMonoidHom ∈ C)
    (G : SimpleGraph ↥C) (hconn : G.Connected)
    (hedge : ∀ U U' : ↥C, G.Adj U U' → ∃ g ∈ A ⊓ stabSub (sSup C),
      U.1.map g.toMonoidHom = U'.1 ∧ U'.1.map g.toMonoidHom = U.1 ∧
        ∀ V ∈ C, V ≠ U.1 → V ≠ U'.1 → V.map g.toMonoidHom = V)
    (ht : t ∈ A ⊓ stabSub (sSup C))
    (htswap : ∃ U ∈ C, ∃ U' ∈ C, U ≠ U' ∧ U.map t.toMonoidHom = U' ∧ U'.map t.toMonoidHom = U ∧
      ∀ V ∈ C, V ≠ U → V ≠ U' → V.map t.toMonoidHom = V)
    (htfix : 2 < r → ∀ V ∈ C, V.map t.toMonoidHom = V → ∀ x ∈ V, t x = x) :
    DeltaSym A t (sSup C) r m := by
  classical
  have hCfin : C.Finite := Set.finite_of_ncard_ne_zero (by rw [hC]; omega)
  haveI : Fintype ↥C := hCfin.fintype
  let e : Fin (r + 1) ≃ ↥C :=
    (Finite.equivFinOfCardEq (α := ↥C) (n := r + 1) (by rw [Nat.card_coe_set_eq, hC])).symm
  let Δ : Fin (r + 1) → Subgroup W := fun i => (e i).1
  have hrange : Set.range Δ = C := by
    ext X
    constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hX
      exact ⟨e.symm ⟨X, hX⟩, by
        show (e (e.symm ⟨X, hX⟩)).1 = X
        rw [Equiv.apply_symm_apply]⟩
  let πfun : ↥(A ⊓ stabSub (sSup C)) → ↥C → ↥C :=
    fun g U => ⟨U.1.map (g : MulAut W).toMonoidHom, hperm g g.2 U.1 U.2⟩
  let πPerm : ↥(A ⊓ stabSub (sSup C)) → Equiv.Perm ↥C := fun g =>
    { toFun := πfun g
      invFun := fun U =>
        ⟨U.1.map ((g : MulAut W)⁻¹).toMonoidHom,
          hperm (g⁻¹) ((A ⊓ stabSub (sSup C)).inv_mem g.2) U.1 U.2⟩
      left_inv := fun U => Subtype.ext (by
        simp only [πfun]
        exact w16g_map_map_inv U.1 (g : MulAut W))
      right_inv := fun U => Subtype.ext (by
        simp only [πfun]
        exact w16g_map_map_inv' U.1 (g : MulAut W)) }
  have πPerm_one : πPerm 1 = 1 := by
    apply Equiv.ext
    intro U
    apply Subtype.ext
    show U.1.map (((1 : ↥(A ⊓ stabSub (sSup C))) : MulAut W)).toMonoidHom = U.1
    rw [show ((1 : ↥(A ⊓ stabSub (sSup C))) : MulAut W) = 1 from rfl, w16g_one_toMonoidHom,
      Subgroup.map_id]
  have πPerm_mul : ∀ g h, πPerm (g * h) = πPerm g * πPerm h := by
    intro g h
    apply Equiv.ext
    intro U
    apply Subtype.ext
    show U.1.map (((g * h : ↥(A ⊓ stabSub (sSup C))) : MulAut W)).toMonoidHom =
      (U.1.map ((h : ↥(A ⊓ stabSub (sSup C))) : MulAut W).toMonoidHom).map
        ((g : ↥(A ⊓ stabSub (sSup C))) : MulAut W).toMonoidHom
    rw [show ((g * h : ↥(A ⊓ stabSub (sSup C))) : MulAut W) =
        (g : MulAut W) * (h : MulAut W) from rfl]
    exact (w16g_map_mul U.1 (h : MulAut W) (g : MulAut W)).symm
  let πHom : ↥(A ⊓ stabSub (sSup C)) →* Equiv.Perm ↥C :=
    { toFun := πPerm, map_one' := πPerm_one, map_mul' := πPerm_mul }
  have hsurjπ : πHom.range = ⊤ := by
    refine closure_swaps_of_connected G hconn πHom.range ?_
    intro U U' hUU'
    obtain ⟨g, hgA, hgU, hgU', hgfix⟩ := hedge U U' hUU'
    have hswap : πPerm ⟨g, hgA⟩ = Equiv.swap U U' := by
      refine w16g_eq_swap_of_apply (πPerm ⟨g, hgA⟩) ?_ ?_ ?_
      · apply Subtype.ext; exact hgU
      · apply Subtype.ext; exact hgU'
      · intro V hV hV'
        apply Subtype.ext
        exact hgfix V.1 V.2 (fun h => hV (Subtype.ext h)) (fun h => hV' (Subtype.ext h))
    exact ⟨⟨g, hgA⟩, hswap⟩
  let σ : ↥(A ⊓ stabSub (sSup C)) →* Equiv.Perm (Fin (r + 1)) :=
    (e.symm.permCongrHom).toMonoidHom.comp πHom
  have hsurj : Function.Surjective σ := by
    intro p
    let q : Equiv.Perm ↥C := (e.symm.permCongrHom).symm p
    have hq : q ∈ πHom.range := by rw [hsurjπ]; exact Subgroup.mem_top q
    obtain ⟨g, hg⟩ := hq
    refine ⟨g, ?_⟩
    have hσg : σ g = e.symm.permCongrHom (πHom g) := rfl
    rw [hσg, hg, MulEquiv.apply_symm_apply]
  have hsig : ∀ (g : ↥(A ⊓ stabSub (sSup C))) (i : Fin (r + 1)),
      (Δ i).map (g : MulAut W).toMonoidHom = Δ (σ g i) := by
    intro g i
    have h1 : (σ g) i = e.symm ((πPerm g) (e i)) := by
      show e.symm.permCongr (πHom g) i = e.symm ((πPerm g) (e i))
      rw [Equiv.permCongr_apply, Equiv.symm_symm]
      rfl
    rw [h1]
    show (e i).1.map (g : MulAut W).toMonoidHom =
      (e (e.symm ((πPerm g) (e i)))).1
    rw [Equiv.apply_symm_apply]
    rfl
  obtain ⟨U, hU, U', hU', hne, hUt, hU't, htfixV⟩ := htswap
  let a : ↥C := ⟨U, hU⟩
  let b : ↥C := ⟨U', hU'⟩
  have hswapT : πPerm ⟨t, ht⟩ = Equiv.swap a b := by
    refine w16g_eq_swap_of_apply (πPerm ⟨t, ht⟩) ?_ ?_ ?_
    · apply Subtype.ext; exact hUt
    · apply Subtype.ext; exact hU't
    · intro V hV hV'
      apply Subtype.ext
      exact htfixV V.1 V.2 (fun h => hV (Subtype.ext h)) (fun h => hV' (Subtype.ext h))
  have hne' : e.symm a ≠ e.symm b := fun h =>
    hne (congrArg Subtype.val (e.symm.injective h))
  refine ⟨Δ, ?_, ?_, ?_, ?_, σ, hsurj, hsig, ht, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    exact hrk (e i).1 (e i).2
  · rw [hrange]; exact hind
  · rw [← sSup_range, hrange]
  · have hσt : σ ⟨t, ht⟩ = e.symm.permCongr (πPerm ⟨t, ht⟩) := by
      show e.symm.permCongrHom (πHom ⟨t, ht⟩) = e.symm.permCongr (πPerm ⟨t, ht⟩)
      rw [Equiv.permCongrHom_coe]
      rfl
    rw [hσt, hswapT]
    have hswap : e.symm.permCongr (Equiv.swap a b) = Equiv.swap (e.symm a) (e.symm b) := by
      simpa [Equiv.permCongr_def] using Equiv.symm_trans_swap_trans a b e.symm
    rw [hswap]
    exact ⟨_, _, hne', rfl⟩
  · intro h2r i hi
    have hm : (Δ i).map t.toMonoidHom = Δ i := by
      have h := hsig ⟨t, ht⟩ i
      rw [hi] at h
      exact h
    exact htfix h2r (Δ i) (by rw [← hrange]; exact Set.mem_range_self i) hm

end CFSG.LocalAnalysis.WeakClosure81
