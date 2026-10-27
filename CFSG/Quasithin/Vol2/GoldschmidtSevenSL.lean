module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.Quasithin.H13.Seven

open Matrix
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

@[expose] def sym3 : SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 0, 1, 1; 1, 1, 0], by decide⟩

@[expose] def sym4 : SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1; 0, 1, 1, 0], by decide⟩

theorem orderOf_sym3 : orderOf sym3 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_sym4 : orderOf sym4 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem graph_sym3 : slGraphAut 3 (ZMod 2) sym3 = sym3⁻¹ := by decide

theorem graph_sym4 : slGraphAut 4 (ZMod 2) sym4 = sym4⁻¹ := by decide

theorem exists_symmetric_seven {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∃ x : SpecialLinearGroup (Fin m) (ZMod 2), orderOf x = 7 ∧ slGraphAut m (ZMod 2) x = x⁻¹ := by
  rcases hm with rfl | rfl
  · exact ⟨sym3, orderOf_sym3, graph_sym3⟩
  · exact ⟨sym4, orderOf_sym4, graph_sym4⟩

theorem mulAut_eq_conj_or_graph {m : ℕ} (hm : 3 ≤ m)
    (β : MulAut (SpecialLinearGroup (Fin m) (ZMod 2))) :
    (∃ A : SpecialLinearGroup (Fin m) (ZMod 2), β = MulAut.conj A) ∨
      ∃ A : SpecialLinearGroup (Fin m) (ZMod 2), β = MulAut.conj A * slGraphAut m (ZMod 2) := by
  obtain ⟨A, σ, ε, hε, h⟩ := CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl hm β
  have hσ : σ = 1 := by
    refine RingEquiv.ext fun x => ?_
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x with rfl | rfl
    · simp
    · simp
  have hu : Matrix.GeneralLinearGroup.det A = 1 := by
    have : ∀ u : (ZMod 2)ˣ, u = 1 := by decide
    exact this _
  have hdet : (A : Matrix (Fin m) (Fin m) (ZMod 2)).det = 1 := by
    have := Matrix.GeneralLinearGroup.val_det_apply A
    rw [← this, hu]
    rfl
  set A' : SpecialLinearGroup (Fin m) (ZMod 2) := ⟨A, hdet⟩ with hA'
  have hconj : CatalogueBHigherLinearAction.slConjugation m (ZMod 2) A = MulAut.conj A' := by
    refine MulEquiv.ext fun g => ?_
    apply Matrix.SpecialLinearGroup.toGL_injective
    have htoGL : Matrix.SpecialLinearGroup.toGL A' = A := Units.ext rfl
    rw [CatalogueBHigherLinearAction.toGL_slConjugation, MulAut.conj_apply, map_mul, map_mul,
      map_inv, htoGL]
  rw [hσ, map_one, mul_one, hconj] at h
  interval_cases ε
  · exact Or.inl ⟨A', by simpa using h⟩
  · exact Or.inr ⟨A', by simpa using h⟩

theorem eq_bot_of_normal_isPGroup_two {m : ℕ} (hm : m = 3 ∨ m = 4)
    (H : Subgroup (SpecialLinearGroup (Fin m) (ZMod 2))) [H.Normal] (hH : IsPGroup 2 H) :
    H = ⊥ := by
  have hq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin m) (ZMod 2)) := by
    rcases hm with rfl | rfl
    · exact CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 (ZMod 2) le_rfl
    · exact CFSG.LieType.Universal.SpecialLinear.isQuasisimple 3 (ZMod 2) (by norm_num)
  have hcenter : Subgroup.center (SpecialLinearGroup (Fin m) (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    have key : ∀ r : ZMod 2, r ^ Fintype.card (Fin m) = 1 → r = 1 := by
      rcases hm with rfl | rfl <;> decide
    obtain ⟨r, hr, hsc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    have hr1 : r = 1 := key r hr
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hsc, hr1]
    simp
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq H with hc | htop
  · rw [hcenter] at hc
    exact le_bot_iff.1 hc
  · exfalso
    obtain ⟨x, hx7, -⟩ := exists_symmetric_seven hm
    have hmem : x ∈ H := by rw [htop]; exact Subgroup.mem_top x
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hH) ⟨x, hmem⟩
    have : orderOf x = 2 ^ k := by rw [← hk]; exact (Subgroup.orderOf_mk x hmem).symm
    rw [hx7] at this
    rcases k with _ | k
    · norm_num at this
    · rw [pow_succ] at this
      omega

end CFSG.Quasithin.H13.Seven
