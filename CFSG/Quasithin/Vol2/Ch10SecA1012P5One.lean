module

public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Vec
public import CFSG.Quasithin.Vol2.Ch10SecATorusA
public import CFSG.Quasithin.Vol2.Ch10SecALiftA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_mem_centralizer_of_case_one (hyp : Ch10.Hyp10 G T L I) {n : ℕ}
    (h1 : Ch10.Case10_1_1One T L I n) :
    ∃ v ∈ fsuUL T L I, v ∉ fsuCVM T L I ∧
      v ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨hUab, F, _, _, _, -, -, ⟨c⟩⟩ := exists_natCoord hyp h1
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  set e : Fin 2 → F := ((c.g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F).mulVec (Pi.single 0 1) with he
  obtain ⟨u, hu⟩ := c.surj (Multiplicative.ofAdd e)
  have hcomm : ∀ s ∈ T ⊓ L, s * (u : G) * s⁻¹ * (u : G)⁻¹ ∈ fsuCVM T L I := by
    intro s hs
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
    have h2 : c.β (φ u) = c.β u := by
      rw [← hγ, c.equivariant, hu, toAdd_ofAdd, hγ', h5]
    have h3 : c.β (φ u * u⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
    have h4 := (c.ker _).mp h3
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hφdef,
      coe_conjAct_apply'] at h4
    refine ⟨?_, h4⟩
    have hUV := fsuUL_le_fsuVM T L I
    exact (fsuVM T L I).mul_mem (hUV ((Subgroup.mem_normalizer_iff.mp (hLU hs.2) _).mp u.2))
      ((fsuVM T L I).inv_mem (hUV u.2))
  refine ⟨u, u.2, ?_, mem_centralizer_of_case_one hyp h1 u.2 hcomm⟩
  intro hC
  have h1 : c.β u = 1 := (c.ker u).mpr (Subgroup.mem_subgroupOf.mpr hC.2)
  rw [hu] at h1
  have h2 : e = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa using this
  have h3 := congrArg (fun z => ((c.g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F).mulVec z) h2
  simp only [he, Matrix.mulVec_mulVec, coe_mul_inv_SL, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h3
  have h4 := congrFun h3 0
  simp at h4

theorem inf_centralizer_eq_bot_of_case_one
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I)
    {n : ℕ} (h1 : Ch10.Case10_1_1One T L I n) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (B0 T L)) :
    D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = ⊥ := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hyp.not_normal h
  obtain ⟨v, hvU, hvC, hvS⟩ := exists_mem_centralizer_of_case_one hyp h1
  obtain ⟨w₁, hw₁U, hw₁C, hw₁S, w₂, hw₂U, hw₂C, hw₂S, hx⟩ :=
    exists_vectors h37 h38 h322 hyp ht htn hD hvU hvC hvS
  rw [eq_bot_iff]
  intro x hxDZ
  rw [Subgroup.mem_bot]
  have hxX := oTwoUpper_le _ (hD.1 hxDZ.1)
  have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard _ hxDZ.1)
  obtain ⟨hx1, hx2⟩ := hx x hxDZ
  have hS : ∀ {K : Subgroup G} {w : G}, w ∈ Subgroup.centralizer (K : Set G) →
      ∀ s ∈ K, s * w * s⁻¹ * w⁻¹ ∈ fsuCVM T L I := by
    intro K w hw s hs
    rw [Subgroup.mem_centralizer_iff.mp hw s hs, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  exact eq_one_of_centralizes h37 h38 hyp
    (fun y hyL0 hyodd hyN w hwU hwC hwS hwy =>
      centralizes_of_case_one h37 h38 hyp h1 hyL0 hyodd hyN hwU hwC hwS hwy)
    ht htn hxX.1 hxX.2 hxodd hw₁U hw₁C (hS hw₁S) hx1 hw₂U hw₂C (hS hw₂S) hx2

end CFSG.Quasithin.Vol2.Ch10.SecA
