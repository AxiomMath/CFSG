module

public import CFSG.Quasithin.Vol2.Ch11SecBFactsG2W
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecB21J
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem flagG2_of (hNF : NatFacts) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2)
    (hyp : Hyp11 G T L I n) {V₁ V₂ V₃ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindG2 L (fsuV T I) n) :
    FlagG2 L (fsuV T I) ⊤ T V₁ V₂ V₃ n := by
  obtain ⟨U₁, U₂, U₃, hU₁, hU₂, hU₃, h12, h23, hu1, hu2, hu3⟩ := exists_isVi hNF h1102 hyp
  have e1 : V₁ = U₁ := hu1 V₁ hV₁
  have e2 : V₂ = U₂ := hu2 V₂ hV₂
  have e3 : V₃ = U₃ := hu3 V₃ hV₃
  rw [← e1, ← e2] at h12
  rw [← e2, ← e3] at h23
  exact
    { elem := isElemAbelian_fsuV hyp
      two_le := hyp.one_lt
      le_normalizer := L_le_normalizer_fsuV hyp
      commutator_eq := commutator_fsuV_eq_self hyp
      nat := natModuleOf_fsuV h1102 hyp
      kind := hk
      le_X := le_top
      normalizer_le := inf_le_right.trans (normalizer_fsuV_le h331 hyp)
      sylow := isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
      T_le_V := T_le_normalizer_fsuV T I
      T_le_L := hyp.normal
      cV_le := IsVi.cV_le hV₁
      le₁₂ := h12
      le₂₃ := h23
      le₃ := IsVi.le_fsuV hV₃
      stable₁ := IsVi.isEndStable hV₁
      stable₂ := IsVi.isEndStable hV₂
      stable₃ := IsVi.isEndStable hV₃
      index₁ := by rw [IsVi.relIndex_eq hV₁, mul_one]
      index₂ := IsVi.relIndex_eq hV₂
      index₃ := IsVi.relIndex_eq hV₃
      T_le_V₁ := IsVi.le_normalizer hV₁
      T_le_V₂ := IsVi.le_normalizer hV₂
      T_le_V₃ := IsVi.le_normalizer hV₃ }

omit [Finite G] in
theorem conjSubgroup_map_conj (U : Subgroup G) (h : G) :
    (conjSubgroup U h).map (MulAut.conj h).toMonoidHom = U := by
  ext x
  rw [mem_map_conj, mem_conjSubgroup_iff]
  simp [mul_assoc]

omit [Finite G] in
theorem map_conj_eq_conjSubgroup (U : Subgroup G) (h : G) :
    U.map (MulAut.conj h).toMonoidHom = conjSubgroup U h⁻¹ := by
  ext x
  rw [mem_map_conj, mem_conjSubgroup_iff, inv_inv]

theorem eq_conj_lOf_of_isCComponent (h1113 : Stmt11_1_3) (hyp : Hyp11 G T L I n)
    {V₂ : Subgroup G} (hV₂ : IsVi T L I n 2 V₂) (h : G) {K : Subgroup G}
    (hK : quasithinIsCComponent K
      (Subgroup.normalizer ((conjSubgroup V₂ h : Subgroup G) : Set G)))
    (hKc : ¬ K ≤ Subgroup.centralizer ((conjSubgroup V₂ h : Subgroup G) : Set G)) :
    K = conjSubgroup (LOf L V₂) h := by
  have h1 := isCComponent_map_equiv (MulAut.conj h) hK
  rw [map_conj_normalizer, conjSubgroup_map_conj] at h1
  have h2 : ¬ K.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro hle
    apply hKc
    have := Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hle
    have hid : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom = MonoidHom.id G := by
      ext y
      simp [mul_assoc]
    rwa [map_conj_centralizer, map_conj_eq_conjSubgroup V₂ h⁻¹, inv_inv, Subgroup.map_map, hid,
      Subgroup.map_id] at this
  have h3 := ((h1113 G T L I n V₂ hyp hV₂).2.2 _ h1 h2)
  rw [← h3, map_conj_eq_conjSubgroup, conjSubgroup_conjSubgroup, inv_mul_cancel]
  ext x
  rw [mem_conjSubgroup_iff]
  simp

theorem isCComponent_conj_lOf (h1113 : Stmt11_1_3) (hyp : Hyp11 G T L I n)
    {V₂ : Subgroup G} (hV₂ : IsVi T L I n 2 V₂) (h : G) :
    quasithinIsCComponent (conjSubgroup (LOf L V₂) h)
        (Subgroup.normalizer ((conjSubgroup V₂ h : Subgroup G) : Set G)) ∧
      ¬ conjSubgroup (LOf L V₂) h ≤
        Subgroup.centralizer ((conjSubgroup V₂ h : Subgroup G) : Set G) := by
  obtain ⟨h1, h2, -⟩ := h1113 G T L I n V₂ hyp hV₂
  have h3 := isCComponent_map_equiv (MulAut.conj h⁻¹) h1
  rw [map_conj_normalizer, map_conj_eq_conjSubgroup, map_conj_eq_conjSubgroup, inv_inv] at h3
  refine ⟨h3, fun hle => h2 ?_⟩
  have := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hle
  rwa [map_conj_centralizer, conjSubgroup_map_conj, conjSubgroup_map_conj] at this

end CFSG.Quasithin.Vol2.Ch11.SecB
