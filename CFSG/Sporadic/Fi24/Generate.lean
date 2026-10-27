module

public import CFSG.Sporadic.Fi24.Edge

public section

namespace CFSG.Sporadic.Fi24

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem tJ_mem_M :
    tJ ∈ M := by
  apply (commute_tR_iff tJ).1
  rw [jR_tJ]
  calc tR * xb * tR = tR * (xb * tR) := mul_assoc _ _ _
    _ = tR * (tR * xb) := by rw [← tR_xb_comm]

theorem fi23EquivM_tJ :
    fi23EquivM ⟨tJ, tJ_mem_M⟩ = sb := by
  show _ = fi23EquivM (mREquiv ⟨xb * tR, mul_tR_mem_MR xb_mem_localClass⟩)
  refine congrArg fi23EquivM ?_
  apply (M.equivMapOfInjective jR jR_injective).injective
  rw [show mREquiv = (M.equivMapOfInjective jR jR_injective).symm from rfl,
    MulEquiv.apply_symm_apply]
  apply Subtype.ext
  show jR tJ = xb * tR
  rw [jR_tJ, tR_xb_comm]

theorem mem_centralizer_inf_M_iff
    {x : J} (hx : x ∈ M) (m : M) :
    fi23EquivM m ∈ Subgroup.centralizer ({fi23EquivM ⟨x, hx⟩} : Set Fi23.J) ↔
      (m : J) ∈ Subgroup.centralizer ({x} : Set J) ⊓ M := by
  constructor
  · intro h
    have h1 := mem_centralizer_Fi23.1 h
    rw [← map_mul, ← map_mul] at h1
    have h2 := Subtype.ext_iff.1 (fi23EquivM.injective h1)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
    exact Subgroup.mem_inf.2 ⟨mem_centralizer_J.2 h2, m.2⟩
  · intro h
    apply mem_centralizer_Fi23.2
    rw [← map_mul, ← map_mul]
    refine congrArg fi23EquivM (Subtype.ext ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact mem_centralizer_J.1 (Subgroup.mem_inf.1 h).1

theorem isCoatom_M : IsCoatom M :=
  MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive J root

theorem maximal_L
    {x : J} (hx : x ∈ M) (hs : fi23EquivM ⟨x, hx⟩ ∈ Fi23.D23) :
    ∀ K : Subgroup J, Subgroup.centralizer ({x} : Set J) ⊓ M ≤ K → K ≤ M →
      K = Subgroup.centralizer ({x} : Set J) ⊓ M ∨ K = M :=
  maximal_of_mulEquiv fi23EquivM inf_le_right (Fi23.isCoatom_centralizer_of_mem hs)
    (mem_centralizer_inf_M_iff hx)

theorem exists_mem_localClass_sb :
    ∃ y, y ∈ LocalClass Fi23.D23 sb := by
  obtain ⟨c, hc⟩ := isConj_iff.1 sb_mem_D23
  refine ⟨c * (Fi23.ptE 0 : Fi23.J) * c⁻¹, ?_⟩
  rw [← hc]
  exact (Pair.conj_mem_localClass_iff Fi23.pair_J c).2 (Fi23.ptE 0).2

@[expose] noncomputable def y1 :
    Fi23.J := exists_mem_localClass_sb.choose

theorem y1_mem :

    y1 ∈ LocalClass Fi23.D23 sb := exists_mem_localClass_sb.choose_spec

theorem exists_conj_y1 :
    ∃ g : Fi23.J, g * sb * g⁻¹ = y1 := by
  have h := isConj_iff.1 (Pair.isConj Fi23.pair_J sb_mem_D23 y1_mem.1)
  exact h

@[expose] noncomputable def m1 :
    M := fi23EquivM.symm exists_conj_y1.choose

theorem fi23EquivM_m1 :
    fi23EquivM m1 = exists_conj_y1.choose :=
  MulEquiv.apply_symm_apply fi23EquivM _

@[expose] noncomputable def t1J :
    J := (m1 : J) * tJ * (m1 : J)⁻¹

theorem t1J_eq :
    t1J = (m1 : J) * tJ * (m1 : J)⁻¹ := rfl

theorem t1J_mem_M :
    t1J ∈ M := by
  rw [t1J_eq]
  exact M.mul_mem (M.mul_mem m1.2 tJ_mem_M) (M.inv_mem m1.2)

theorem fi23EquivM_t1J :
    fi23EquivM ⟨t1J, t1J_mem_M⟩ = y1 := by
  have h : (⟨t1J, t1J_mem_M⟩ : M) = m1 * ⟨tJ, tJ_mem_M⟩ * m1⁻¹ := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact t1J_eq)
  rw [h, map_mul, map_mul, map_inv, fi23EquivM_tJ, fi23EquivM_m1]
  exact exists_conj_y1.choose_spec

theorem t1J_mem_centralizer :
    t1J ∈ Subgroup.centralizer ({tJ} : Set J) := by
  apply mem_centralizer_J.2
  have h : y1 * sb = sb * y1 := y1_mem.2.2
  rw [← fi23EquivM_t1J, ← fi23EquivM_tJ, ← map_mul, ← map_mul] at h
  have h' := Subtype.ext_iff.1 (fi23EquivM.injective h)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h'
  exact h'

theorem t1J_ne_tJ :
    t1J ≠ tJ := by
  intro h
  apply y1_mem.2.1
  rw [← fi23EquivM_t1J, ← fi23EquivM_tJ]
  exact congrArg fi23EquivM (Subtype.ext h)

theorem sup_centralizer_eq_top
    {e : J} (he : EdgeSwap e) :
    Subgroup.centralizer ({tJ} : Set J) ⊔ Subgroup.centralizer ({t1J} : Set J) = ⊤ := by
  have hsb : fi23EquivM ⟨tJ, tJ_mem_M⟩ ∈ Fi23.D23 := by rw [fi23EquivM_tJ]; exact sb_mem_D23
  have heH : e ∈ Subgroup.centralizer ({tJ} : Set J) := by
    apply mem_centralizer_J.2
    apply jR_injective
    rw [show jR (e * tJ) = jR e * jR tJ from map_mul jR e tJ,
      show jR (tJ * e) = jR tJ * jR e from map_mul jR tJ e, jR_tJ]
    exact mem_centralizer_R.1 (Subgroup.mem_inf.1 (jR_mem_CE he)).1
  have heM : e ∉ M := by
    intro h
    have h1 := (commute_tR_iff e).2 h
    have h2 := he.swap_tR
    rw [h1, mul_inv_cancel_right] at h2
    exact tR_ne_xb h2
  have hne : ¬ Subgroup.centralizer ({t1J} : Set J) ⊓ M ≤
      Subgroup.centralizer ({tJ} : Set J) ⊓ M := by
    intro hle
    have hle' : Subgroup.centralizer ({y1} : Set Fi23.J) ≤
        Subgroup.centralizer ({sb} : Set Fi23.J) := by
      intro g hg
      obtain ⟨m, rfl⟩ := fi23EquivM.surjective g
      rw [← fi23EquivM_t1J] at hg
      rw [← fi23EquivM_tJ]
      exact (mem_centralizer_inf_M_iff tJ_mem_M m).2
        (hle ((mem_centralizer_inf_M_iff t1J_mem_M m).1 hg))
    rcases (Fi23.isCoatom_centralizer_of_mem y1_mem.1).le_iff.1 hle' with h | h
    · exact (Fi23.isCoatom_centralizer_of_mem sb_mem_D23).1 h
    ·
      have hcent : ∀ x ∈ LocalClass Fi23.D23 y1, sb * x * sb⁻¹ = x := by
        intro x hx
        have hx' : x ∈ Subgroup.centralizer ({sb} : Set Fi23.J) := by
          rw [h]
          exact mem_centralizer_Fi23.2 hx.2.2
        rw [(mem_centralizer_Fi23.1 hx').symm, mul_inv_cancel_right]
      have hcomm : sb * y1 = y1 * sb := y1_mem.2.2.symm
      rcases Fi23.eq_of_centralizes_star y1_mem.1 hcomm hcent with h1 | h1
      · exact Pair.ne_one Fi23.pair_J sb_mem_D23 h1
      · exact y1_mem.2.1 h1.symm
  exact sup_eq_top_of_maximal isCoatom_M inf_le_right inf_le_right
    (maximal_L tJ_mem_M hsb) hne inf_le_left inf_le_left heH heM

end CFSG.Sporadic.Fi24
