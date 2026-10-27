module

public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Core
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5VecAux
public import CFSG.Quasithin.Vol2.Ch10SecALiftA
public import CFSG.Quasithin.Vol2.Ch10SecANatCoord

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

section Transitive

variable {F : Type} [Field F]

theorem exists_SL_mulVec_single_eq {w : Fin 2 → F} (hw : w ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) F,
      (A : Matrix (Fin 2) (Fin 2) F).mulVec (Pi.single 0 1) = w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := fun h1 => hw (by
      ext i
      fin_cases i
      · exact h0
      · exact h1)
    refine ⟨⟨!![0, -(w 1)⁻¹; w 1, 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![w 0, 0; w 1, (w 0)⁻¹], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end Transitive

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem NatCoord.mem_centralizer_of_beta [IsMulCommutative ↥(fsuUL T L I)]
    (hyp : Ch10.Hyp10 G T L I) {n : ℕ} (h1 : Ch10.Case10_1_1One T L I n) {F : Type} [Field F]
    (c : NatCoord T L I F) {y : ↥(fsuUL T L I)}
    (hy : c.β y = Multiplicative.ofAdd (((c.g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).mulVec (Pi.single 0 1))) :
    (y : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  refine mem_centralizer_of_case_one hyp h1 y.2 fun s hs => ?_
  set e : Fin 2 → F := ((c.g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F).mulVec (Pi.single 0 1) with he
  set φ := conjAct (fsuUL T L I) ⟨s, hLU hs.2⟩ with hφdef
  have hφ : φ ∈ autOn (T ⊓ L) (fsuUL T L I) := mem_autOn_iff'.mpr ⟨_, hs, rfl⟩
  have hφL : φ ∈ autOn L (fsuUL T L I) := A4.autOn_mono inf_le_right hφ
  set γ := c.eρ.symm ⟨φ, hφL⟩ with hγdef
  have hγ : ((c.eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) = φ := by
    rw [hγdef, MulEquiv.apply_symm_apply]
  obtain ⟨b, hb⟩ := (c.unip γ).mp (by rw [hγ]; exact hφ)
  have hγ' : γ = c.g⁻¹ * unipSL b * c.g := by rw [← hb]; group
  have h5 : ((c.g⁻¹ * unipSL b * c.g : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).mulVec e = e := by
    rw [he, Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, Matrix.mul_assoc, coe_mul_inv_SL,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, coe_unipSL, unipSL_mulVec]
    congr 1
    ext i
    fin_cases i <;> simp
  have h2 : c.β (φ y) = c.β y := by
    rw [← hγ, c.equivariant, hy, toAdd_ofAdd, hγ', h5]
  have h3 : c.β (φ y * y⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
  have h4 := (c.ker _).mp h3
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hφdef,
    coe_conjAct_apply'] at h4
  refine ⟨?_, h4⟩
  have hUV := fsuUL_le_fsuVM T L I
  exact (fsuVM T L I).mul_mem (hUV ((Subgroup.mem_normalizer_iff.mp (hLU hs.2) _).mp y.2))
    ((fsuVM T L I).inv_mem (hUV y.2))

theorem exists_conj_mem_centralizer_of_case_one (hyp : Ch10.Hyp10 G T L I) {n : ℕ}
    (h1 : Ch10.Case10_1_1One T L I n) {v : G} (hvU : v ∈ fsuUL T L I)
    (hvC : v ∉ fsuCVM T L I) :
    ∃ l ∈ L, l * v * l⁻¹ ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨hUab, F, _, _, _, -, -, ⟨c⟩⟩ := exists_natCoord hyp h1
  have hβu : c.β ⟨v, hvU⟩ ≠ 1 := by
    intro h
    apply hvC
    exact ⟨fsuUL_le_fsuVM T L I hvU, Subgroup.mem_subgroupOf.mp ((c.ker _).mp h)⟩
  have hw : Multiplicative.toAdd (c.β ⟨v, hvU⟩) ≠ 0 := fun h =>
    hβu (by rw [← ofAdd_toAdd (c.β ⟨v, hvU⟩), h, ofAdd_zero])
  obtain ⟨A, hA⟩ := exists_SL_mulVec_single_eq hw
  obtain ⟨g', hg'L, hg'⟩ := mem_autOn_iff'.mp (c.eρ (c.g⁻¹ * A⁻¹)).2
  refine ⟨g', hg'L, ?_⟩
  have hy : c.β (conjAct (fsuUL T L I) g' ⟨v, hvU⟩) = Multiplicative.ofAdd
      (((c.g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).mulVec (Pi.single 0 1)) := by
    rw [hg', c.equivariant]
    congr 1
    rw [← hA, Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
      coe_inv_mul_SL, Matrix.mul_one]
  have h2 := c.mem_centralizer_of_beta hyp h1 hy
  rwa [coe_conjAct_apply'] at h2

theorem exists_conj_mem_centralizer_of_case_one' (hyp : Ch10.Hyp10 G T L I) {n : ℕ}
    (h1 : Ch10.Case10_1_1One T L I n) {t : G} (ht : t ∈ T) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆) (hvC : v ∉ fsuCVM T L I) :
    ∃ l ∈ CFSG.conjugate L t, l * v * l⁻¹ ∈
      Subgroup.centralizer ((T ⊓ CFSG.conjugate L t : Subgroup G) : Set G) := by
  have htM := le_fsuM T L ht
  have hvU' : v ∈ CFSG.conjugate (fsuUL T L I) t := by
    rw [conjugate_commutator_fsuVM htM]
    exact hv
  have hv' : t * v * t⁻¹ ∈ fsuUL T L I := mem_conjugate_iff.mp hvU'
  have hvC' : t * v * t⁻¹ ∉ fsuCVM T L I := fun h => hvC (by
    have := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_fsuCVM T L I ((fsuM T L).inv_mem htM)) _).mp h
    simpa [mul_assoc] using this)
  obtain ⟨l, hlL, hlC⟩ := exists_conj_mem_centralizer_of_case_one hyp h1 hv' hvC'
  refine ⟨t⁻¹ * l * t, conj_mem_conjugate t hlL, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hs' : t * s * t⁻¹ ∈ T ⊓ L :=
    (mem_inf_iff_conj ht _).mpr (by simpa [mul_assoc] using hs)
  have h2 := Subgroup.mem_centralizer_iff.mp hlC _ hs'
  calc s * (t⁻¹ * l * t * v * (t⁻¹ * l * t)⁻¹) =
      t⁻¹ * (t * s * t⁻¹ * (l * (t * v * t⁻¹) * l⁻¹)) * t := by group
    _ = t⁻¹ * (l * (t * v * t⁻¹) * l⁻¹ * (t * s * t⁻¹)) * t := by rw [h2]
    _ = t⁻¹ * l * t * v * (t⁻¹ * l * t)⁻¹ * s := by group

end CFSG.Quasithin.Vol2.Ch10.SecA
