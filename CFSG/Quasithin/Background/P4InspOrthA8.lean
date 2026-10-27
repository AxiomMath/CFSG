module

public import CFSG.Quasithin.Background.P4InspOrthPerm
public import CFSG.Quasithin.Background.P3OrthoA8Main
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin

namespace G11

namespace P4InspOrth

open CFSG.GroupTheory.WeirSylow

section Dim

@[expose] def p4insporth_sumLin (n : ℕ) : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

theorem p4insporth_finrank_permCore {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank (ZMod 2) ↥(permCore n) + 1 = n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (p4insporth_sumLin n)
  have h2 : LinearMap.range (p4insporth_sumLin n) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨Pi.single ⟨0, by omega⟩ c, ?_⟩
    change ∑ i, Pi.single (⟨0, by omega⟩ : Fin n) c i = c
    rw [Finset.sum_pi_single']
    simp
  rw [h2, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
  have h3 : permCore n = LinearMap.ker (p4insporth_sumLin n) := rfl
  rw [h3]
  omega

end Dim

section Model8

@[expose] def p4insporth_one8 : ↥(permCore 8) :=
  ⟨fun _ => 1, by
    show ∑ i : Fin 8, (fun _ => (1 : ZMod 2)) i = 0
    decide⟩

@[expose] def p4insporth_L8 : Submodule (ZMod 2) ↥(permCore 8) :=
  Submodule.span (ZMod 2) {p4insporth_one8}

abbrev p4insporth_V8 : Type := ↥(permCore 8) ⧸ p4insporth_L8

instance p4insporth_finite_V8 : Finite p4insporth_V8 :=
  Finite.of_surjective p4insporth_L8.mkQ (Submodule.mkQ_surjective _)

theorem p4insporth_map_L8 (σ : Equiv.Perm (Fin 8)) :
    Submodule.map ((p4insporth_permLin σ : ↥(permCore 8) ≃ₗ[ZMod 2] ↥(permCore 8)) :
      ↥(permCore 8) →ₗ[ZMod 2] ↥(permCore 8)) p4insporth_L8 = p4insporth_L8 := by
  rw [p4insporth_L8, Submodule.map_span, Set.image_singleton]
  congr 2

@[expose] def p4insporth_perm8Lin (σ : Equiv.Perm (Fin 8)) :
    p4insporth_V8 ≃ₗ[ZMod 2] p4insporth_V8 :=
  Submodule.Quotient.equiv p4insporth_L8 p4insporth_L8 (p4insporth_permLin σ)
    (p4insporth_map_L8 σ)

theorem p4insporth_perm8Lin_mk (σ : Equiv.Perm (Fin 8)) (x : ↥(permCore 8)) :
    p4insporth_perm8Lin σ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (p4insporth_permHom 8 σ x) := by
  simp [p4insporth_perm8Lin, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    p4insporth_permHom]

@[expose] def p4insporth_perm8Hom : Equiv.Perm (Fin 8) →* GLV p4insporth_V8 where
  toFun := p4insporth_perm8Lin
  map_one' := by
    refine LinearEquiv.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun x => ?_
    rw [p4insporth_perm8Lin_mk, map_one]
    rfl
  map_mul' σ τ := by
    refine LinearEquiv.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun x => ?_
    rw [LinearEquiv.mul_apply, p4insporth_perm8Lin_mk, p4insporth_perm8Lin_mk,
      p4insporth_perm8Lin_mk, map_mul]
    rfl

theorem p4insporth_perm8Hom_mk (σ : Equiv.Perm (Fin 8)) (x : ↥(permCore 8)) :
    p4insporth_perm8Hom σ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (p4insporth_permHom 8 σ x) := p4insporth_perm8Lin_mk σ x

theorem p4insporth_exists_not_mem_four (a b c d : Fin 8) :
    ∃ k : Fin 8, k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ k ≠ d := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin 8)) ⊆ {a, b, c, d} := by
    intro k _
    by_cases ha : k = a
    · simp [ha]
    by_cases hb : k = b
    · simp [hb]
    by_cases hc : k = c
    · simp [hc]
    have := h k ha hb hc
    simp [this]
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b, c, d} : Finset (Fin 8)).card ≤ 4 := Finset.card_le_four
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem p4insporth_perm8Hom_injective : Function.Injective p4insporth_perm8Hom := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine p4insporth_eq_one_of_fix (by norm_num) fun i j hij => ?_
  have h1 := LinearEquiv.congr_fun hσ
    (Submodule.Quotient.mk ⟨p4insporth_pairVec i j, p4insporth_pairVec_mem i j⟩)
  rw [p4insporth_perm8Hom_mk] at h1
  have h2 : p4insporth_permHom 8 σ ⟨p4insporth_pairVec i j, p4insporth_pairVec_mem i j⟩ -
      ⟨p4insporth_pairVec i j, p4insporth_pairVec_mem i j⟩ ∈ p4insporth_L8 :=
    (Submodule.Quotient.eq _).1 h1
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h2
  rcases g12_eq_zero_or_one a with rfl | rfl
  · rw [zero_smul] at ha
    have h3 := sub_eq_zero.1 ha.symm
    exact congrArg Subtype.val h3
  · exfalso
    rw [one_smul] at ha
    obtain ⟨k, hki, hkj, hks1, hks2⟩ := p4insporth_exists_not_mem_four i j (σ i) (σ j)
    have h4 := congrFun (congrArg Subtype.val ha) k
    have h5 : p4insporth_pairVec i j k = 0 := by
      simp [p4insporth_pairVec, hki, hkj]
    have h6 : p4insporth_pairVec (σ i) (σ j) k = 0 := by
      simp [p4insporth_pairVec, hks1, hks2]
    have h7 : permAct σ (p4insporth_pairVec i j) k = 0 := by
      rw [p4insporth_permAct_pairVec]
      exact h6
    simp only [p4insporth_one8, Submodule.coe_sub, Pi.sub_apply] at h4
    have h8 : (p4insporth_permHom 8 σ ⟨p4insporth_pairVec i j, p4insporth_pairVec_mem i j⟩ :
        ↥(permCore 8)).1 k = 0 := h7
    rw [h8, h5] at h4
    exact absurd h4 (by simp)

@[expose] def p4insporth_H8 : Subgroup (GLV p4insporth_V8) :=
  (alternatingGroup (Fin 8)).map p4insporth_perm8Hom

theorem p4insporth_ker8 (u : ↥(permCore 8)) :
    p4insporth_L8.mkQ u = 0 ↔ (u = 0 ∨ (Even 8 ∧ ∀ i, (u : Fin 8 → ZMod 2) i = 1)) := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, p4insporth_L8,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rcases g12_eq_zero_or_one a with rfl | rfl
    · left
      simp
    · right
      exact ⟨by decide, fun i => rfl⟩
  · rintro (rfl | ⟨-, h⟩)
    · exact ⟨0, by simp⟩
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      funext i
      exact (h i).symm

theorem p4insporth_coe_eq_perm8 (γ : ↥p4insporth_H8) :
    (γ : GLV p4insporth_V8) = p4insporth_perm8Hom
      (((Subgroup.equivMapOfInjective _ _ p4insporth_perm8Hom_injective).symm γ :
        ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) := by
  have h1 := congrArg (fun z : ↥((alternatingGroup (Fin 8)).map p4insporth_perm8Hom) =>
    (z : GLV p4insporth_V8))
    ((Subgroup.equivMapOfInjective _ _ p4insporth_perm8Hom_injective).apply_symm_apply γ)
  simp only [Subgroup.coe_equivMapOfInjective_apply] at h1
  exact h1.symm

@[expose] noncomputable def p4insporth_D8 : P3Ortho.Data p4insporth_V8 p4insporth_H8 where
  φ := (Subgroup.equivMapOfInjective _ _ p4insporth_perm8Hom_injective).symm
  β := p4insporth_L8.mkQ
  surj := Submodule.mkQ_surjective _
  ker := p4insporth_ker8
  equ := by
    intro γ u u' hu'
    rw [p4insporth_coe_eq_perm8 γ]
    have h1 : u' = p4insporth_permHom 8 (((Subgroup.equivMapOfInjective _ _
      p4insporth_perm8Hom_injective).symm γ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8))
        u := Subtype.ext hu'
    rw [h1]
    exact (p4insporth_perm8Hom_mk _ u).symm

theorem p4insporth_isPermCore8 : IsPermCoreModule p4insporth_H8 (alternatingGroup (Fin 8)) :=
  ⟨p4insporth_D8.φ, p4insporth_D8.β, p4insporth_D8.surj, p4insporth_D8.ker, p4insporth_D8.equ⟩

@[expose] noncomputable def p4insporth_f8 : LinearMap.BilinForm (ZMod 2) p4insporth_V8 :=
  p4insporth_D8.B0

@[expose] noncomputable def p4insporth_q8 : p4insporth_V8 → ZMod 2 := p4insporth_D8.q

theorem p4insporth_q8_add (x y : p4insporth_V8) :
    p4insporth_q8 (x + y) = p4insporth_q8 x + p4insporth_q8 y + p4insporth_f8 x y :=
  p4insporth_D8.q_add x y

theorem p4insporth_symplectic8 : IsSymplectic p4insporth_f8 :=
  ⟨p4insporth_D8.B0_alt, p4insporth_D8.B0_left_sep⟩

theorem p4insporth_finrank8 : Module.finrank (ZMod 2) p4insporth_V8 = 6 := by
  have h1 : Module.finrank (ZMod 2) p4insporth_V8 + Module.finrank (ZMod 2) ↥p4insporth_L8 =
      Module.finrank (ZMod 2) ↥(permCore 8) := Submodule.finrank_quotient_add_finrank p4insporth_L8
  have h0 : p4insporth_one8 ≠ 0 := fun h => by
    have := congrFun (congrArg Subtype.val h) 0
    simp [p4insporth_one8] at this
  have h2 : Module.finrank (ZMod 2) ↥p4insporth_L8 = 1 := finrank_span_singleton h0
  have h3 := p4insporth_finrank_permCore (n := 8) (by norm_num)
  omega

theorem p4insporth_plus8 : IsPlusType (p4insporth_quad (f := p4insporth_f8)
    (q := p4insporth_q8) p4insporth_q8_add) :=
  ⟨p4insporth_D8.sing3, by rw [p4insporth_D8.finrank_sing3, p4insporth_finrank8],
    fun x hx => p4insporth_D8.sing3_q x hx⟩

theorem p4insporth_q8_perm (σ : Equiv.Perm (Fin 8)) (y : p4insporth_V8) :
    p4insporth_q8 (p4insporth_perm8Hom σ y) = p4insporth_q8 y := by
  have hq : ∀ x : ↥(permCore 8),
      p4insporth_q8 (Submodule.Quotient.mk x) = P3Ortho.qP (x : Fin 8 → ZMod 2) :=
    fun x => p4insporth_D8.q_β x
  refine Submodule.Quotient.induction_on _ y fun x => ?_
  rw [p4insporth_perm8Hom_mk, hq, hq]
  exact P3Ortho.qP_permAct σ _

theorem p4insporth_card_orth8 : Nat.card ↥(orthSub p4insporth_q8) = 40320 := by
  have h := natCard_orthogonalGroup_of_type (K := ZMod 2)
    (p4insporth_nondegenerate_quad p4insporth_symplectic8 p4insporth_q8_add)
    (m := 2) (by rw [p4insporth_finrank8]) (ε := 1) (Or.inl ⟨rfl, p4insporth_plus8⟩)
  rw [p4insporth_orthogonalGroup_quad p4insporth_q8_add, Nat.card_zmod] at h
  simp only [Nat.cast_ofNat] at h
  have h2 : (∏ i ∈ Finset.Icc 1 2, (((2 : ℤ) ^ 2) ^ i - 1)) = 45 := by decide
  rw [h2] at h
  norm_num at h
  exact_mod_cast h

theorem p4insporth_range_perm8 :
    p4insporth_perm8Hom.range = orthSub p4insporth_q8 := by
  have hle : p4insporth_perm8Hom.range ≤ orthSub p4insporth_q8 := by
    rintro _ ⟨σ, rfl⟩ y
    exact p4insporth_q8_perm σ y
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [p4insporth_card_orth8]
  rw [← Nat.card_congr (MonoidHom.ofInjective p4insporth_perm8Hom_injective).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem p4insporth_comm_orth8 :
    ⁅orthSub p4insporth_q8, orthSub p4insporth_q8⁆ = p4insporth_H8 := by
  rw [← p4insporth_range_perm8, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  exact congrArg _ (alternatingGroup.commutator_perm_eq (by simp))

theorem p4insporth_simple_comm8 :
    IsSimpleGroup ↥⁅orthSub p4insporth_q8, orthSub p4insporth_q8⁆ := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  rw [p4insporth_comm_orth8]
  exact (Subgroup.equivMapOfInjective _ _ p4insporth_perm8Hom_injective).symm.isSimpleGroup

theorem p4insporth_isPermCore8' :
    IsPermCoreModule ⁅orthSub p4insporth_q8, orthSub p4insporth_q8⁆ (alternatingGroup (Fin 8)) := by
  rw [p4insporth_comm_orth8]
  exact p4insporth_isPermCore8

end Model8

section Transport8

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}
  {q : U → ZMod 2}

theorem p4insporth_plus_six [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hdim : Module.finrank (ZMod 2) U = 6)
    (hplus : IsPlusType (p4insporth_quad hq)) :
    IsSimpleGroup ↥⁅orthSub q, orthSub q⁆ ∧
      IsPermCoreModule ⁅orthSub q, orthSub q⁆ (alternatingGroup (Fin 8)) := by
  obtain ⟨e⟩ := nonempty_isometry_of_isPlusType_iff (n := 3)
    (p4insporth_nondegenerate_quad hf hq)
    (p4insporth_nondegenerate_quad p4insporth_symplectic8 p4insporth_q8_add)
    hdim p4insporth_finrank8 (iff_of_true hplus p4insporth_plus8)
  have hι : ∀ x, p4insporth_q8 (e.toLinearEquiv x) = q x := fun x => e.map_app x
  exact ⟨p4insporth_isSimpleGroup_commutator_of_iso e.toLinearEquiv hι p4insporth_simple_comm8,
    p4insporth_isPermCore_of_map e.toLinearEquiv
      (p4insporth_map_cg_commutator e.toLinearEquiv hι) p4insporth_isPermCore8'⟩

end Transport8

end P4InspOrth

end G11

end CFSG.Quasithin
