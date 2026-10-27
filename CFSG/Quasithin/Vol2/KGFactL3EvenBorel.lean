module

public import CFSG.Quasithin.Vol2.KGFactL3EvenConf

public section

namespace CFSG.Quasithin.H13.KGL3Even

open Matrix CFSG.Quasithin.H13.Ch4.KGSL3 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {F : Type} [Field F]

theorem normalizer_le_upperTriangular {R₀ : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hR : R₀ ≤ unitriangular 3 F) {r r' : SpecialLinearGroup (Fin 3) F} (hr : r ∈ R₀)
    (hr' : r' ∈ R₀) (hb : (r : Matrix (Fin 3) (Fin 3) F) 1 2 ≠ 0)
    (ha : (r' : Matrix (Fin 3) (Fin 3) F) 0 1 ≠ 0) :
    Subgroup.normalizer (R₀ : Set (SpecialLinearGroup (Fin 3) F)) ≤ upperTriangular 3 F := by
  intro g hg
  have hcol : ∀ t' ∈ R₀, (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ * t' * g :
      SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (t' : Matrix (Fin 3) (Fin 3) F) * g := by
    intro t' _
    have : g * (g⁻¹ * t' * g) = t' * g := by group
    exact congrArg Subtype.val this
  have hmemR : ∀ t' ∈ R₀, g⁻¹ * t' * g ∈ R₀ := by
    intro t' ht'
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) t').mp ht'
    rwa [inv_inv] at h
  have hc0 : ∀ t' ∈ R₀, ∀ i : Fin 3, (g : Matrix (Fin 3) (Fin 3) F) i 0 =
      ((t' : Matrix (Fin 3) (Fin 3) F) * g) i 0 := by
    intro t' ht' i
    have h := congrFun (congrFun (hcol t' ht') i) 0
    rw [← h, unitri_entries (hR (hmemR t' ht'))]
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  have h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
    have h := hc0 r hr 1
    rw [unitri_entries (hR hr)] at h
    simp [Matrix.mul_apply, Fin.sum_univ_three] at h
    exact h.resolve_left hb
  have h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by
    have h := hc0 r' hr' 0
    rw [unitri_entries (hR hr')] at h
    simp [Matrix.mul_apply, Fin.sum_univ_three, h20] at h
    exact h.resolve_left ha
  have h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
    have hrow : (g : Matrix (Fin 3) (Fin 3) F) * r =
        ((g * r * g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * g := by
      have : g * r = (g * r * g⁻¹) * g := by group
      exact congrArg Subtype.val this
    have hm : g * r * g⁻¹ ∈ R₀ := (Subgroup.mem_normalizer_iff.mp hg r).mp hr
    have h := congrFun (congrFun hrow 2) 2
    rw [unitri_entries (hR hm), unitri_entries (hR hr)] at h
    simp [Matrix.mul_apply, Fin.sum_univ_three, h20] at h
    exact h.resolve_right hb
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem diag_mul_of_upper {g h : SpecialLinearGroup (Fin 3) F} (hg : g ∈ upperTriangular 3 F)
    (hh : h ∈ upperTriangular 3 F) (i : Fin 3) :
    ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i =
      (g : Matrix (Fin 3) (Fin 3) F) i i * (h : Matrix (Fin 3) (Fin 3) F) i i :=
  mul_apply_self_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.mp hg)
    (mem_upperTriangular_iff_isUpperTriangular.mp hh) i

theorem diag_inv_of_upper {g : SpecialLinearGroup (Fin 3) F} (hg : g ∈ upperTriangular 3 F)
    (i : Fin 3) :
    (g : Matrix (Fin 3) (Fin 3) F) i i *
      ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i = 1 :=
  coe_inv_apply_self_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.mp hg) i

theorem commutator_upper_le : ⁅upperTriangular 3 F, upperTriangular 3 F⁆ ≤ unitriangular 3 F := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hB : ⁅g, h⁆ ∈ upperTriangular 3 F := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
      (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)
  refine ⟨hB, fun i => ?_⟩
  have hgi := Subgroup.inv_mem _ hg
  have hhi := Subgroup.inv_mem _ hh
  rw [commutatorElement_def, diag_mul_of_upper (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh) hgi)
    hhi, diag_mul_of_upper (Subgroup.mul_mem _ hg hh) hgi, diag_mul_of_upper hg hh]
  have e1 := diag_inv_of_upper hg i
  have e2 := diag_inv_of_upper hh i
  linear_combination ((h⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i *
    ((h : Matrix (Fin 3) (Fin 3) F) i i) * e1 + e2

@[expose] def zU : Subgroup (SpecialLinearGroup (Fin 3) F) where
  carrier := {t | t ∈ unitriangular 3 F ∧ (t : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧
    (t : Matrix (Fin 3) (Fin 3) F) 1 2 = 0}
  one_mem' := ⟨(unitriangular 3 F).one_mem, by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨(unitriangular 3 F).mul_mem ha hb, ?_, ?_⟩
    · change ((a : Matrix (Fin 3) (Fin 3) F) * b) 0 1 = 0
      rw [unitri_entries ha, unitri_entries hb]
      simp [Matrix.mul_apply, Fin.sum_univ_three, ha1, hb1]
    · change ((a : Matrix (Fin 3) (Fin 3) F) * b) 1 2 = 0
      rw [unitri_entries ha, unitri_entries hb]
      simp [Matrix.mul_apply, Fin.sum_univ_three, ha2, hb2]
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    refine ⟨(unitriangular 3 F).inv_mem ha, ?_, ?_⟩
    · change (adjugate (a : Matrix (Fin 3) (Fin 3) F)) 0 1 = 0
      rw [adjugate_fin_three, unitri_entries ha]
      simp [ha1]
    · change (adjugate (a : Matrix (Fin 3) (Fin 3) F)) 1 2 = 0
      rw [adjugate_fin_three, unitri_entries ha]
      simp [ha2]

theorem zU_le_uSub : (zU : Subgroup (SpecialLinearGroup (Fin 3) F)) ≤ uSub :=
  fun _ ht => ⟨_, _, eq_uSL_of_unitri ht.1 ht.2.1⟩

theorem commutator_unitri_le : ⁅unitriangular 3 F, unitriangular 3 F⁆ ≤ zU := by
  have hadd : ∀ a ∈ unitriangular 3 F, ∀ b ∈ unitriangular 3 F,
      ((a * b : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 =
        (a : Matrix (Fin 3) (Fin 3) F) 0 1 + (b : Matrix (Fin 3) (Fin 3) F) 0 1 ∧
      ((a * b : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 =
        (a : Matrix (Fin 3) (Fin 3) F) 1 2 + (b : Matrix (Fin 3) (Fin 3) F) 1 2 := by
    intro a ha b hb
    change ((a : Matrix (Fin 3) (Fin 3) F) * b) 0 1 = _ ∧
      ((a : Matrix (Fin 3) (Fin 3) F) * b) 1 2 = _
    rw [unitri_entries ha, unitri_entries hb]
    constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have hinv : ∀ a ∈ unitriangular 3 F,
      ((a⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1 =
        -(a : Matrix (Fin 3) (Fin 3) F) 0 1 ∧
      ((a⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 =
        -(a : Matrix (Fin 3) (Fin 3) F) 1 2 := by
    intro a ha
    obtain ⟨h1, h2⟩ := hadd a ha a⁻¹ ((unitriangular 3 F).inv_mem ha)
    rw [mul_inv_cancel] at h1 h2
    change (1 : Matrix (Fin 3) (Fin 3) F) 0 1 = _ at h1
    change (1 : Matrix (Fin 3) (Fin 3) F) 1 2 = _ at h2
    rw [Matrix.one_apply_ne (by decide)] at h1 h2
    constructor
    · linear_combination -h1
    · linear_combination -h2
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have ha' := (unitriangular 3 F).inv_mem ha
  have hb' := (unitriangular 3 F).inv_mem hb
  have hab := (unitriangular 3 F).mul_mem ha hb
  have haba := (unitriangular 3 F).mul_mem hab ha'
  refine ⟨?_, ?_, ?_⟩
  · rw [commutatorElement_def]
    exact (unitriangular 3 F).mul_mem haba hb'
  · rw [commutatorElement_def, (hadd _ haba _ hb').1, (hadd _ hab _ ha').1, (hadd _ ha _ hb).1,
      (hinv _ ha).1, (hinv _ hb).1]
    ring
  · rw [commutatorElement_def, (hadd _ haba _ hb').2, (hadd _ hab _ ha').2, (hadd _ ha _ hb).2,
      (hinv _ ha).2, (hinv _ hb).2]
    ring

theorem comm2_of_le_upperTriangular {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hK : K ≤ upperTriangular 3 F) : Comm2 K := by
  have h1 : ⁅K, K⁆ ≤ unitriangular 3 F :=
    (Subgroup.commutator_mono hK hK).trans commutator_upper_le
  have h2 : ⁅⁅K, K⁆, ⁅K, K⁆⁆ ≤ uSub :=
    ((Subgroup.commutator_mono h1 h1).trans commutator_unitri_le).trans zU_le_uSub
  intro a ha b hb
  exact uSub_comm (h2 ha) (h2 hb)

theorem unitri_trichotomy [CharP F 2] {R₀ K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hc : LConf R₀ K) (hR : R₀ ≤ unitriangular 3 F) (hR1 : R₀ ≠ ⊥) (hK : ¬ Comm2 K) :
    R₀ = uSub ∨ R₀.map theta.toMonoidHom = uSub := by
  by_cases h01 : ∀ r ∈ R₀, (r : Matrix (Fin 3) (Fin 3) F) 0 1 = 0
  · have hRU : R₀ ≤ uSub := fun r hr => ⟨_, _, eq_uSL_of_unitri (hR hr) (h01 r hr)⟩
    rcases plane_case hRU hR1 hc.le_normalizer hc.normalizer_le hc.core with h' | h'
    · exact Or.inl h'
    · exact absurd h' hK
  by_cases h12 : ∀ r ∈ R₀, (r : Matrix (Fin 3) (Fin 3) F) 1 2 = 0
  · have hRU : R₀.map theta.toMonoidHom ≤ uSub := by
      rintro _ ⟨r, hr, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, eq_vSL_of_unitri (hR hr) (h12 r hr), theta_vSL]
      exact ⟨_, _, rfl⟩
    have hR1' : R₀.map theta.toMonoidHom ≠ ⊥ := by
      intro hb
      apply hR1
      rw [← map_map_symm theta R₀, hb, Subgroup.map_bot]
    have hc' := hc.map theta
    rcases plane_case hRU hR1' hc'.le_normalizer hc'.normalizer_le hc'.core with h' | h'
    · exact Or.inr h'
    · exact absurd (Comm2.of_map theta h') hK
  push Not at h01 h12
  obtain ⟨r', hr', ha⟩ := h01
  obtain ⟨r, hr, hb⟩ := h12
  exact absurd (comm2_of_le_upperTriangular
    (hc.le_normalizer.trans (normalizer_le_upperTriangular hR hr hr' hb ha))) hK

end CFSG.Quasithin.H13.KGL3Even
