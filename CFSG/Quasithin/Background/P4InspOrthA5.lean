module

public import CFSG.Quasithin.Background.P4InspOrthPerm
public import CFSG.Quasithin.Background.G116IIIA5
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin

namespace G11

namespace P4InspOrth

open CFSG.GroupTheory.WeirSylow

section Model5

@[expose] def p4insporth_dot (n : ℕ) : LinearMap.BilinForm (ZMod 2) ↥(permCore n) :=
  LinearMap.mk₂ (ZMod 2) (fun u v => (u : Fin n → ZMod 2) ⬝ᵥ (v : Fin n → ZMod 2))
    (by intro u u' v; simp [add_dotProduct])
    (by intro c u v; simp [smul_dotProduct])
    (by intro u v v'; simp [dotProduct_add])
    (by intro c u v; simp [dotProduct_smul])

@[expose] def p4insporth_qN (n : ℕ) (x : ↥(permCore n)) : ZMod 2 :=
  p4insporth_qP (x : Fin n → ZMod 2)

theorem p4insporth_qN_add (n : ℕ) (x y : ↥(permCore n)) :
    p4insporth_qN n (x + y) = p4insporth_qN n x + p4insporth_qN n y + p4insporth_dot n x y :=
  p4insporth_qP_add x.2 y.2

theorem p4insporth_dot_alt (n : ℕ) (x : ↥(permCore n)) : p4insporth_dot n x x = 0 := by
  have hsq : ∀ a : ZMod 2, a * a = a := by decide
  have hx : ∑ i, (x : Fin n → ZMod 2) i = 0 := x.2
  show (x : Fin n → ZMod 2) ⬝ᵥ (x : Fin n → ZMod 2) = 0
  simp only [dotProduct, hsq]
  exact hx

theorem p4insporth_dot5_sep (x : ↥(permCore 5)) (h : ∀ y, p4insporth_dot 5 x y = 0) : x = 0 := by
  have key : ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 →
      (∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 → x ⬝ᵥ y = 0) → x = 0 := by
    decide +kernel
  exact Subtype.ext (key x x.2 fun y hy => h ⟨y, hy⟩)

theorem p4insporth_symplectic5 : IsSymplectic (p4insporth_dot 5) :=
  ⟨p4insporth_dot_alt 5, fun x hx => p4insporth_dot5_sep x hx⟩

noncomputable abbrev p4insporth_Q5 : QuadraticForm (ZMod 2) ↥(permCore 5) :=
  p4insporth_quad (f := p4insporth_dot 5) (q := p4insporth_qN 5) (p4insporth_qN_add 5)

theorem p4insporth_not_plus5 : ¬ IsPlusType p4insporth_Q5 := by
  rintro ⟨W, hW, hWs⟩
  have hd : Module.finrank (ZMod 2) W = 2 := by
    have := finrank_permCore_five
    omega
  obtain ⟨x, hxW, hx0⟩ : ∃ x ∈ W, x ≠ 0 := by
    by_contra h
    push Not at h
    have : W = ⊥ := (Submodule.eq_bot_iff W).2 h
    rw [this, finrank_bot] at hd
    omega
  have hspan : ¬ W ≤ Submodule.span (ZMod 2) {x} := by
    intro hle
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hx0, hd] at h1
    omega
  obtain ⟨y, hyW, hy⟩ := IsConcreteLE.not_le_iff_exists.1 hspan
  have hy0 : y ≠ 0 := fun h => hy (h ▸ Submodule.zero_mem _)
  have hyx : x ≠ y := fun h => hy (h ▸ Submodule.mem_span_singleton_self x)
  have hq : ∀ z ∈ W, p4insporth_qP (z : Fin 5 → ZMod 2) = 0 := fun z hz => hWs z hz
  have key : ∀ a b : Fin 5 → ZMod 2, ¬ (∑ i, a i = 0 ∧ ∑ i, b i = 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      p4insporth_qP a = 0 ∧ p4insporth_qP b = 0 ∧ p4insporth_qP (a + b) = 0) := by
    decide +kernel
  exact key x y ⟨x.2, y.2, fun h => hx0 (Subtype.ext h), fun h => hy0 (Subtype.ext h),
    fun h => hyx (Subtype.ext h), hq x hxW, hq y hyW, hq (x + y) (W.add_mem hxW hyW)⟩

theorem p4insporth_card_orth5 : Nat.card ↥(orthSub (p4insporth_qN 5)) = 120 := by
  have h := natCard_orthogonalGroup_of_type (K := ZMod 2)
    (p4insporth_nondegenerate_quad p4insporth_symplectic5 (p4insporth_qN_add 5))
    (m := 1) (by rw [finrank_permCore_five]) (ε := -1) (Or.inr ⟨rfl, p4insporth_not_plus5⟩)
  rw [p4insporth_orthogonalGroup_quad (p4insporth_qN_add 5), Nat.card_zmod] at h
  norm_num [Finset.Icc_self] at h
  exact_mod_cast h

theorem p4insporth_range_perm5 :
    (p4insporth_permHom 5).range = orthSub (p4insporth_qN 5) := by
  have hle : (p4insporth_permHom 5).range ≤ orthSub (p4insporth_qN 5) := by
    rintro _ ⟨σ, rfl⟩ x
    exact p4insporth_qP_permAct σ (x : Fin 5 → ZMod 2)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [p4insporth_card_orth5]
  have hinj := p4insporth_permHom_injective (n := 5) (by norm_num)
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  decide

theorem p4insporth_comm_orth5 : ⁅orthSub (p4insporth_qN 5), orthSub (p4insporth_qN 5)⁆ =
    (alternatingGroup (Fin 5)).map (p4insporth_permHom 5) := by
  rw [← p4insporth_range_perm5, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  congr 1
  exact alternatingGroup.commutator_perm_eq (by simp)

theorem p4insporth_simple_comm5 :
    IsSimpleGroup ↥⁅orthSub (p4insporth_qN 5), orthSub (p4insporth_qN 5)⁆ := by
  have hinj := p4insporth_permHom_injective (n := 5) (by norm_num)
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rw [p4insporth_comm_orth5]
  exact (Subgroup.equivMapOfInjective _ _ hinj).symm.isSimpleGroup

theorem p4insporth_isPermCore5 :
    IsPermCoreModule ⁅orthSub (p4insporth_qN 5), orthSub (p4insporth_qN 5)⁆
      (alternatingGroup (Fin 5)) := by
  have hinj := p4insporth_permHom_injective (n := 5) (by norm_num)
  let e : ↥⁅orthSub (p4insporth_qN 5), orthSub (p4insporth_qN 5)⁆ ≃*
      ↥(alternatingGroup (Fin 5)) :=
    (MulEquiv.subgroupCongr p4insporth_comm_orth5).trans
      (Subgroup.equivMapOfInjective _ _ hinj).symm
  refine ⟨e, LinearMap.id, fun u => ⟨u, rfl⟩, fun u => ?_, fun γ u u' hu' => ?_⟩
  · have h5 : ¬ Even 5 := by decide
    simp [h5]
  · have h1 := congrArg (fun z : ↥((alternatingGroup (Fin 5)).map (p4insporth_permHom 5)) =>
      (z : GLV ↥(permCore 5)))
      ((Subgroup.equivMapOfInjective _ _ hinj).apply_symm_apply
        (MulEquiv.subgroupCongr p4insporth_comm_orth5 γ))
    simp only [Subgroup.coe_equivMapOfInjective_apply, MulEquiv.subgroupCongr_apply] at h1
    have h2 : (γ : GLV ↥(permCore 5)) = p4insporth_permHom 5 (e γ : Equiv.Perm (Fin 5)) := h1.symm
    show u' = (γ : GLV ↥(permCore 5)) u
    rw [h2]
    exact Subtype.ext hu'

end Model5

section Transport5

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}
  {q : U → ZMod 2}

theorem p4insporth_minus_four [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hdim : Module.finrank (ZMod 2) U = 4)
    (hminus : ¬ IsPlusType (p4insporth_quad hq)) :
    IsSimpleGroup ↥⁅orthSub q, orthSub q⁆ ∧
      IsPermCoreModule ⁅orthSub q, orthSub q⁆ (alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff (n := 2)
    (p4insporth_nondegenerate_quad hf hq)
    (p4insporth_nondegenerate_quad p4insporth_symplectic5 (p4insporth_qN_add 5))
    hdim (by rw [finrank_permCore_five])
    (iff_of_false hminus p4insporth_not_plus5)
  have hι : ∀ x, p4insporth_qN 5 (e.toLinearEquiv x) = q x := fun x => e.map_app x
  exact ⟨p4insporth_isSimpleGroup_commutator_of_iso e.toLinearEquiv hι p4insporth_simple_comm5,
    p4insporth_isPermCore_of_map e.toLinearEquiv
      (p4insporth_map_cg_commutator e.toLinearEquiv hι) p4insporth_isPermCore5⟩

end Transport5

end P4InspOrth

end G11

end CFSG.Quasithin
