module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.Monster.B.Geometry.InitialIsometryParabolic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Monster.B.Geometry

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResSideDatum_of_standard_parabolic
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs X J : Subgroup G} (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hent : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = -1 ∨ C i j = -2)
    (hT : SecFiveRootRefl.CartanTree C) (b : Λ)
    (hWMJ : GGIsWeylMatrix (parMatrix M {j | j ≠ b}))

    (f : M.Group ≃* ↥(ggAutomizer X Bs))
    (hrefl : ∀ i, GGIsReflection p (f (M.simple i) : MulAut ↥Bs))
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b} => (f (M.simple j) : MulAut ↥Bs))) :
    GGResSideDatum p Bs X J := by
  classical
  let φ : Λ → MulAut ↥Bs := fun i => f (M.simple i)
  let S : Set Λ := {j | j ≠ b}
  let MJ := parMatrix M S
  have hind (H : Subgroup G) : ∀ a ∈ ggAutomizer H Bs, a ∈ ggInduced ⊤ Bs := by
    intro a ha
    obtain ⟨g, hg, hgN, hact⟩ := mem_ggAutomizer_iff.mp ha
    exact ⟨g, Subgroup.mem_top g, hgN, hact⟩
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := p) hEl
  obtain ⟨h, α, hα, hreflection, hpair⟩ :=
    SecFiveRootRefl.exists_cartan_pairing_of_iso hp2 hNT hC hent hT f hrefl (hind X) ι
  have hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i := by
    intro i w
    rw [hreflection i]
    rfl
  let gX : M.Group →* MulAut ↥Bs := (ggAutomizer X Bs).subtype.comp f.toMonoidHom
  have hgXrange : gX.range = ggAutomizer X Bs := by
    apply le_antisymm
    · rintro a ⟨x, rfl⟩
      exact (f x).2
    · intro a ha
      obtain ⟨x, hx⟩ := f.surjective ⟨a, ha⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  have hgenX : Subgroup.closure (Set.range M.simple) = ⊤ := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
      M.toCoxeterSystem.subgroup_closure_range_simple
  have hclosX : ggAutomizer X Bs = Subgroup.closure (Set.range φ) := by
    rw [← hgXrange, MonoidHom.range_eq_map, ← hgenX, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  let g : MJ.Group →* MulAut ↥Bs := gX.comp (parToGroup M.toCoxeterSystem S)
  have hg_simple : ∀ j : S, g (MJ.simple j) = φ j := by
    intro j
    change (f (parToGroup M.toCoxeterSystem S (MJ.simple j)) : MulAut ↥Bs) = φ j
    rw [parToGroup_simple]
    rfl
  have hg_inj : Function.Injective g :=
    (ggAutomizer X Bs).subtype_injective.comp
      (f.injective.comp (parToGroup_injective M.toCoxeterSystem S))
  have hgenJ : Subgroup.closure (Set.range MJ.simple) = ⊤ := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
      MJ.toCoxeterSystem.subgroup_closure_range_simple
  have hg_range : g.range = ggAutomizer J Bs := by
    rw [MonoidHom.range_eq_map, ← hgenJ, MonoidHom.map_closure, hJ]
    congr 1
    ext a
    constructor
    · rintro ⟨v, ⟨j, rfl⟩, rfl⟩
      exact ⟨⟨j.1, j.2⟩, (hg_simple j).symm⟩
    · rintro ⟨j, rfl⟩
      let j' : S := ⟨j.1, j.2⟩
      exact ⟨MJ.simple j', ⟨j', rfl⟩, hg_simple j'⟩

  let fJ : MJ.Group ≃* ↥(ggAutomizer J Bs) :=
    (MonoidHom.ofInjective hg_inj).trans (MulEquiv.subgroupCongr hg_range)
  have hfJ : ∀ j : S, (fJ (MJ.simple j) : MulAut ↥Bs) = φ j := by
    intro j
    simpa only [fJ, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply] using hg_simple j
  have hNG2 : ¬ ∃ e : Fin 2 ≃ S, MJ = CoxeterMatrix.G₂.reindex e := by
    rintro ⟨e, he⟩
    have hij : ((e 0 : S) : Λ) ≠ ((e 1 : S) : Λ) := by
      intro h
      have h' : (0 : Fin 2) = 1 := e.injective (Subtype.ext h)
      exact (by decide : (0 : Fin 2) ≠ 1) h'
    have h6 : M.M (e 0) (e 1) = 6 := by
      change MJ.M (e 0) (e 1) = 6
      rw [he]
      simp [CoxeterMatrix.reindex_apply, CoxeterMatrix.G₂]
    rcases hC.entries hij with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1⟩
    · omega
    · omega
    · omega
    · rcases h1 with ⟨-, h1⟩ | ⟨h1, -⟩
      · rcases hent (e 1) (e 0) (Ne.symm hij) with h0 | h0 | h0 <;> omega
      · rcases hent (e 0) (e 1) hij with h0 | h0 | h0 <;> omega
  have hconj : GGReflConjSimple p (ggAutomizer J Bs) (fun j : S => φ j) := by
    intro t ht hrt
    obtain ⟨j, w, hw⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds
      G p Bs (Fact.out : p.Prime) hp2 hEl hNT (ggAutomizer J Bs) (hind J)
      S MJ hWMJ hNG2 fJ (fun j => by rw [hfJ j]; exact hrefl j) ⟨t, ht⟩ hrt
    refine ⟨(fJ w : MulAut ↥Bs), (fJ w).2, j, ?_⟩
    calc t = (fJ (w * MJ.simple j * w⁻¹) : MulAut ↥Bs) := congrArg Subtype.val hw
      _ = (fJ w : MulAut ↥Bs) * φ j * (fJ w : MulAut ↥Bs)⁻¹ := by
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hfJ]
  refine ⟨Λ, inferInstance, inferInstance, b, M, C, MJ, V, inferInstance, inferInstance,
    ι, φ, h, α, hM, hC, hWMJ, ?_, hlin, hrefl, hpair, ⟨f, fun _ => rfl⟩,
    hclosX, ⟨fJ, hfJ⟩, hJ, hconj⟩
  intro j j'
  rfl

theorem ggResSideDatum_of_B3_end
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs X J : Subgroup G} (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (b : Fin 3) (hb : b = 0 ∨ b = 2)
    (f : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer X Bs))
    (hrefl : ∀ i, GGIsReflection p (f ((CoxeterMatrix.B 3).simple i) : MulAut ↥Bs))
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin 3 // j ≠ b} => (f ((CoxeterMatrix.B 3).simple j) : MulAut ↥Bs))) :
    GGResSideDatum p Bs X J := by
  classical
  have hM : GGIsWeylMatrix (CoxeterMatrix.B 3) := by
    refine Or.inl ⟨3, Equiv.refl _, by decide, Or.inr (Or.inl ⟨by decide, ?_⟩)⟩
    ext i j
    rfl
  have hMJ : GGIsWeylMatrix (parMatrix (CoxeterMatrix.B 3) {j | j ≠ b}) := by
    rcases hb with hb | hb
    · subst b
      let e : Fin 2 ≃ {j : Fin 3 // j ≠ 0} := (Fin.succAboveOrderIso (0 : Fin 3)).toEquiv.trans
        (Equiv.subtypeEquivRight (fun i : Fin 3 => by simp))
      have he : parMatrix (CoxeterMatrix.B 3) {j | j ≠ (0 : Fin 3)} =
          (CoxeterMatrix.B 2).reindex e := by
        ext j k
        obtain ⟨i, rfl⟩ := e.surjective j
        obtain ⟨l, rfl⟩ := e.surjective k
        simp only [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
        fin_cases i <;> fin_cases l <;> decide +kernel
      exact Or.inl ⟨2, e, by decide, Or.inr (Or.inl ⟨by decide, he⟩)⟩
    · subst b
      let e : Fin 2 ≃ {j : Fin 3 // j ≠ 2} := (Fin.succAboveOrderIso (2 : Fin 3)).toEquiv.trans
        (Equiv.subtypeEquivRight (fun i : Fin 3 => by simp))
      have he : parMatrix (CoxeterMatrix.B 3) {j | j ≠ (2 : Fin 3)} =
          (CoxeterMatrix.A 2).reindex e := by
        ext j k
        obtain ⟨i, rfl⟩ := e.surjective j
        obtain ⟨l, rfl⟩ := e.surjective k
        simp only [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply]
        fin_cases i <;> fin_cases l <;> decide +kernel
      exact Or.inl ⟨2, e, by decide, Or.inl he⟩
  exact ggResSideDatum_of_standard_parabolic hp2 hEl hNT hM (ggIntCartan_B 3)
    (SecFiveRootRefl.entries_B 3) (SecFiveRootRefl.cartanTree_B 3 (by decide)) b hMJ f hrefl hJ


end CFSG.StandardType
