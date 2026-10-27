module

public import CFSG.Quasithin.Vol2.Ch12Sec5ZV
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Quasithin S125 S125ZV Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification

namespace S125Aut

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

theorem proj_injective : Function.Injective (proj 5 (ZMod 2)) := by
  have hscal : scalars 5 (ZMod 2) = ⊥ := by
    have h := card_scalars_dvd (K := ZMod 2) (n := 5) (by norm_num)
    rw [Nat.card_zmod] at h
    exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp h)
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, hscal]

theorem ringEquiv_eq_one (σ : ZMod 2 ≃+* ZMod 2) : σ = 1 := by
  ext x
  fin_cases x
  · exact map_zero σ
  · exact map_one σ

theorem exists_sl_of_gl (A : GL (Fin 5) (ZMod 2)) : ∃ a : SL5, SpecialLinearGroup.toGL a = A := by
  have hdet : (A : Matrix (Fin 5) (Fin 5) (ZMod 2)).det = 1 := by
    have h : (A : Matrix (Fin 5) (Fin 5) (ZMod 2)).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    generalize (A : Matrix (Fin 5) (Fin 5) (ZMod 2)).det = x at h ⊢
    fin_cases x
    · exact absurd rfl h
    · rfl
  exact ⟨⟨A, hdet⟩, Units.ext (SpecialLinearGroup.coe_GL_coe_matrix _)⟩

theorem slConjugation_toGL (a x : SL5) :
    CatalogueBHigherLinearAction.slConjugation 5 (ZMod 2) (SpecialLinearGroup.toGL a) x =
      a * x * a⁻¹ := by
  apply Subtype.ext
  rw [coe_slConjugation, ← map_inv, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

theorem sl5_aut (β : MulAut SL5) :
    ∃ (a : SL5) (ε : ℕ), ε ≤ 1 ∧
      ∀ g, β g = a * (CatalogueBGraphForm.slGraphAut 5 (ZMod 2) ^ ε) g * a⁻¹ := by
  obtain ⟨-, hgen⟩ := automorphism_generation (n := 5) (K := ZMod 2) (by norm_num)
  obtain ⟨A, σ, ε, hε, hα⟩ := hgen (descendAut 5 (ZMod 2) β)
  obtain ⟨a, rfl⟩ := exists_sl_of_gl A
  refine ⟨a, ε, hε, fun g => ?_⟩
  apply proj_injective
  have h1 := DFunLike.congr_fun hα (proj 5 (ZMod 2) g)
  rw [descendAut_proj, ringEquiv_eq_one σ, map_one, mul_one] at h1
  rw [h1]
  have hδ : (dualAut 5 (ZMod 2) ^ ε) (proj 5 (ZMod 2) g) =
      proj 5 (ZMod 2) ((CatalogueBGraphForm.slGraphAut 5 (ZMod 2) ^ ε) g) := by
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · rfl
    · rw [pow_one, pow_one, dualAut_proj]
      rfl
  rw [MulAut.mul_apply, hδ, conjAut_proj, slConjugation_toGL]

theorem card_vanish (S : Finset (Fin 10)) :
    Nat.card {x : Fin 10 → ZMod 2 // ∀ k ∈ S, x k = 0} = 2 ^ (10 - S.card) := by
  classical
  let e : {x : Fin 10 → ZMod 2 // ∀ k ∈ S, x k = 0} ≃ ({k : Fin 10 // k ∉ S} → ZMod 2) :=
    { toFun := fun x k => x.1 k
      invFun := fun f => ⟨fun k => if h : k ∈ S then 0 else f ⟨k, h⟩, fun k hk => by simp [hk]⟩
      left_inv := fun x => Subtype.ext (funext fun k => by
        by_cases hk : k ∈ S
        · simp [hk, x.2 k hk]
        · simp [hk])
      right_inv := fun f => funext fun k => by simp [k.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

@[expose] def trB : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem wedgeMat_trB : JonesParshall.wedgeMat trB =
    1 + Matrix.single 0 4 1 + Matrix.single 2 7 1 + Matrix.single 3 8 1 := by decide

theorem wedgeMat_tr0T : JonesParshall.wedgeMat tr0ᵀ =
    1 + Matrix.single 4 1 1 + Matrix.single 5 2 1 + Matrix.single 6 3 1 := by decide

theorem wedgeMat_trBT : JonesParshall.wedgeMat trBᵀ =
    1 + Matrix.single 4 0 1 + Matrix.single 7 2 1 + Matrix.single 8 3 1 := by decide

theorem det_tr0 : tr0.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (by intro i j h; fin_cases i <;> fin_cases j <;>
    first | rfl | exact absurd h (by decide))]
  simp [Fin.prod_univ_five, tr0]

theorem det_trB : trB.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (by intro i j h; fin_cases i <;> fin_cases j <;>
    first | rfl | exact absurd h (by decide))]
  simp [Fin.prod_univ_five, trB]

@[expose] def g0 : SL5 := ⟨tr0, det_tr0⟩

@[expose] def gB : SL5 := ⟨trB, det_trB⟩

theorem g0_mul_self : g0 * g0 = 1 := Subtype.ext (by decide)

theorem gB_mul_self : gB * gB = 1 := Subtype.ext (by decide)

theorem coe_graph_g0 :
    ((CatalogueBGraphForm.slGraphAut 5 (ZMod 2) g0 : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      tr0ᵀ := by
  change (((g0⁻¹).transpose : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = _
  rw [inv_eq_of_mul_eq_one_right g0_mul_self, SpecialLinearGroup.coe_transpose]
  rfl

theorem coe_graph_gB :
    ((CatalogueBGraphForm.slGraphAut 5 (ZMod 2) gB : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      trBᵀ := by
  change (((gB⁻¹).transpose : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = _
  rw [inv_eq_of_mul_eq_one_right gB_mul_self, SpecialLinearGroup.coe_transpose]
  rfl

theorem wedgeRep_mul_apply (g h : SL5) (x : Fin 10 → ZMod 2) :
    JonesParshall.wedgeRep (g * h) x = JonesParshall.wedgeRep g (JonesParshall.wedgeRep h x) := by
  rw [map_mul]
  rfl

theorem wedgeRep_inv_apply (g : SL5) (x : Fin 10 → ZMod 2) :
    JonesParshall.wedgeRep g⁻¹ (JonesParshall.wedgeRep g x) = x := by
  rw [← wedgeRep_mul_apply, inv_mul_cancel, map_one]
  rfl

theorem wedgeRep_apply_inv (g : SL5) (x : Fin 10 → ZMod 2) :
    JonesParshall.wedgeRep g (JonesParshall.wedgeRep g⁻¹ x) = x := by
  rw [← wedgeRep_mul_apply, mul_inv_cancel, map_one]
  rfl

theorem not_outer (E : (Fin 10 → ZMod 2) ≃+ (Fin 10 → ZMod 2)) (a : SL5)
    (hE : ∀ (g : SL5) (x : Fin 10 → ZMod 2), E (JonesParshall.wedgeRep g x) =
      JonesParshall.wedgeRep (a * CatalogueBGraphForm.slGraphAut 5 (ZMod 2) g * a⁻¹) (E x)) :
    False := by
  have hfixδ : ∀ x : Fin 10 → ZMod 2, (∀ k ∈ ({0, 1, 2, 3} : Finset (Fin 10)), x k = 0) →
      ∀ g ∈ ({g0, gB} : Set SL5),
        JonesParshall.wedgeRep (CatalogueBGraphForm.slGraphAut 5 (ZMod 2) g) x = x := by
    intro x hx g hg
    have h0 : x 0 = 0 := hx 0 (by decide)
    have h1 : x 1 = 0 := hx 1 (by decide)
    have h2 : x 2 = 0 := hx 2 (by decide)
    have h3 : x 3 = 0 := hx 3 (by decide)
    have hu : ∀ i : Fin 10, Function.update (0 : Fin 10 → ZMod 2) i 0 = 0 := fun i => by simp
    rw [wedgeRep_apply]
    rcases hg with rfl | rfl
    · rw [coe_graph_g0, wedgeMat_tr0T]
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, one_mul, h1, h2, h3,
        hu, add_zero]
    · rw [coe_graph_gB, wedgeMat_trBT]
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec, one_mul, h0, h2, h3,
        hu, add_zero]
  have hvan : ∀ y : Fin 10 → ZMod 2, JonesParshall.wedgeRep g0 y = y →
      JonesParshall.wedgeRep gB y = y → ∀ k ∈ ({4, 5, 6, 7, 8} : Finset (Fin 10)), y k = 0 := by
    intro y hy0 hyB
    rw [wedgeRep_apply] at hy0 hyB
    change JonesParshall.wedgeMat tr0 *ᵥ y = y at hy0
    change JonesParshall.wedgeMat trB *ᵥ y = y at hyB
    rw [wedgeMat_tr0] at hy0
    rw [wedgeMat_trB] at hyB
    obtain ⟨y4, y5, y6⟩ := fix_aux hy0 (by decide) (by decide) (by decide)
    obtain ⟨-, y7, y8⟩ := fix_aux hyB (by decide) (by decide) (by decide)
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> assumption
  let f : {x : Fin 10 → ZMod 2 // ∀ k ∈ ({0, 1, 2, 3} : Finset (Fin 10)), x k = 0} →
      {y : Fin 10 → ZMod 2 // ∀ k ∈ ({4, 5, 6, 7, 8} : Finset (Fin 10)), y k = 0} :=
    fun x => ⟨E.symm (JonesParshall.wedgeRep a x.1), by
      have hfix : ∀ g ∈ ({g0, gB} : Set SL5),
          JonesParshall.wedgeRep g (E.symm (JonesParshall.wedgeRep a x.1)) =
            E.symm (JonesParshall.wedgeRep a x.1) := by
        intro g hg
        apply E.injective
        rw [hE, AddEquiv.apply_symm_apply, wedgeRep_mul_apply, wedgeRep_mul_apply,
          wedgeRep_inv_apply, hfixδ x.1 x.2 g hg]
      exact hvan _ (hfix g0 (Set.mem_insert _ _)) (hfix gB (Set.mem_insert_of_mem _ rfl))⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    simp only [f] at h
    have h2 := congrArg (JonesParshall.wedgeRep a⁻¹) (E.symm.injective h)
    rw [wedgeRep_inv_apply, wedgeRep_inv_apply] at h2
    exact Subtype.ext h2
  have hle := Nat.card_le_card_of_injective f hf
  rw [card_vanish, card_vanish] at hle
  simp at hle

@[expose] def pk : Fin 10 → Equiv.Perm (Fin 5) :=
  ![1, Equiv.swap 1 2, Equiv.swap 1 3, Equiv.swap 1 4, Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 0 1 * Equiv.swap 1 3, Equiv.swap 0 1 * Equiv.swap 1 4,
    Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 0 2 * Equiv.swap 1 4,
    Equiv.swap 0 3 * Equiv.swap 1 4]

theorem det_permMatrix (σ : Equiv.Perm (Fin 5)) : (σ.permMatrix (ZMod 2)).det = 1 := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> decide

theorem wedgeMat_pk : ∀ k : Fin 10,
    JonesParshall.wedgeMat ((pk k)⁻¹.permMatrix (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single k 1 := by
  decide

theorem eq_self_of_commute (C : (Fin 10 → ZMod 2) →+ (Fin 10 → ZMod 2))
    (hCi : Function.Injective C)
    (hC : ∀ (g : SL5) x, C (JonesParshall.wedgeRep g x) = JonesParshall.wedgeRep g (C x)) :
    ∀ x, C x = x := by
  set e₀ : Fin 10 → ZMod 2 := Pi.single 0 1 with he₀
  have hfix : ∀ M : Matrix (Fin 5) (Fin 5) (ZMod 2), (M = tr0 ∨ M = tr1 ∨ M = tr2 ∨ M = tr3) →
      JonesParshall.wedgeMat M *ᵥ C e₀ = C e₀ := by
    intro M hM
    obtain ⟨u, hu, rfl⟩ := exists_tr M hM
    rw [← wedgeRep_apply, ← hC, wedgeRep_apply, he₀, wedgeMat_mulVec_single hu]
  have h0 := fixed_tr (C e₀) (hfix _ (Or.inl rfl)) (hfix _ (Or.inr (Or.inl rfl)))
    (hfix _ (Or.inr (Or.inr (Or.inl rfl)))) (hfix _ (Or.inr (Or.inr (Or.inr rfl))))
  have hCe : C e₀ = e₀ := by
    have hs : C e₀ = Pi.single 0 (C e₀ 0) := by
      funext k
      by_cases hk : k = 0
      · subst hk
        simp
      · rw [h0 k hk, Pi.single_eq_of_ne hk]
    have hne : C e₀ 0 ≠ 0 := by
      intro h
      rw [h, Pi.single_zero] at hs
      have : e₀ = 0 := hCi (by rw [hs, map_zero])
      have h1 := congrFun this 0
      simp [he₀] at h1
    rw [hs, he₀]
    congr 1
    generalize C e₀ 0 = c at hne
    fin_cases c
    · exact absurd rfl hne
    · rfl
  have hbasis : ∀ (k : Fin 10) (c : ZMod 2), C (Pi.single k c) = Pi.single k c := by
    intro k c
    fin_cases c
    · show C (Pi.single k 0) = Pi.single k 0
      rw [Pi.single_zero, map_zero]
    · let p : SL5 := ⟨(pk k)⁻¹.permMatrix (ZMod 2), det_permMatrix _⟩
      have hp : JonesParshall.wedgeRep p e₀ = Pi.single k 1 := by
        rw [wedgeRep_apply]
        exact wedgeMat_pk k
      change C (Pi.single k 1) = Pi.single k 1
      rw [← hp, hC, hCe]
  intro x
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  conv_rhs => rw [← Finset.univ_sum_single x]
  exact Finset.sum_congr rfl fun k _ => hbasis k (x k)

theorem eq_wedgeRep_of_intertwines (E : (Fin 10 → ZMod 2) ≃+ (Fin 10 → ZMod 2))
    (β : MulAut SL5)
    (hE : ∀ (g : SL5) x, E (JonesParshall.wedgeRep g x) = JonesParshall.wedgeRep (β g) (E x)) :
    ∃ a : SL5, ∀ x, E x = JonesParshall.wedgeRep a x := by
  obtain ⟨a, ε, hε, hβ⟩ := sl5_aut β
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · refine ⟨a, ?_⟩
    let C : (Fin 10 → ZMod 2) →+ (Fin 10 → ZMod 2) :=
      { toFun := fun x => JonesParshall.wedgeRep a⁻¹ (E x)
        map_zero' := by rw [map_zero, map_zero]
        map_add' := fun x y => by rw [map_add, map_add] }
    have hCi : Function.Injective C := fun x y h => by
      have h2 := congrArg (JonesParshall.wedgeRep a) h
      simp only [C, AddMonoidHom.coe_mk, ZeroHom.coe_mk, wedgeRep_apply_inv] at h2
      exact E.injective h2
    have hC : ∀ (g : SL5) x, C (JonesParshall.wedgeRep g x) = JonesParshall.wedgeRep g (C x) := by
      intro g x
      simp only [C, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [hE, hβ, pow_zero, MulAut.one_apply, ← wedgeRep_mul_apply, ← wedgeRep_mul_apply,
        show a⁻¹ * (a * g * a⁻¹) = g * a⁻¹ by group]
    intro x
    have h := eq_self_of_commute C hCi hC x
    simp only [C, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
    have h2 := congrArg (JonesParshall.wedgeRep a) h
    rwa [wedgeRep_apply_inv] at h2
  · exact (not_outer E a fun g x => by rw [hE, hβ, pow_one]).elim

end S125Aut

end CFSG.Quasithin.H13
