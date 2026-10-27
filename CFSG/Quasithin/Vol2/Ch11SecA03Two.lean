module

public import CFSG.Quasithin.Vol2.Ch11SecA03Twist
public import CFSG.Quasithin.Vol2.Ch11SecA03Three

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem isNatRealized_of_cV_eq_bot (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    [IsMulCommutative ↥(fsuV T I)] (hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    IsNatRealized (autOn L (fsuV T I)) n := by
  have hC' : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have : (v : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨v.2, hv⟩
    rw [hC, Subgroup.mem_bot] at this
    exact Subtype.ext this
  obtain ⟨_, -, -, -, hcases⟩ := h1102 G T L I n h
  rcases hcases with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ |
    ⟨K, _, _, hK, -, hG⟩
  · rw [hC'] at hπ
    exact ⟨K, inferInstance, inferInstance, hK, Or.inl ⟨π, hπ⟩⟩
  · rw [hC'] at hπ
    exact ⟨K, inferInstance, inferInstance, hK, Or.inr (Or.inl ⟨π, hπ⟩)⟩
  · rw [hC'] at hG
    obtain ⟨K', _, _, hK', hR⟩ := hG
    exact ⟨K', inferInstance, inferInstance, hK', Or.inr (Or.inr hR)⟩

theorem isXSectionIso₂_conjugate (hTw : FactTwist) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    IsXSectionIso₂ L (CFSG.conjugate (fsuV T I) m) ⊥ (fsuV T I) ⊥ := by
  obtain ⟨hcomm, -, -, ⟨e⟩, -⟩ := h1102 G T L I n h
  have hLV := L_le_normalizer_fsuV h
  have hW2 : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  set ρ := conjHomL (fsuV T I) L hLV with hρ
  have hnat : IsNatRealized ρ.range n := by
    rw [hρ, range_conjHomL]
    exact isNatRealized_of_cV_eq_bot h1102 h hC
  have hO := inf_centralizer_eq_pCoreOf hLV e
  have hker : ∀ {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) (x : ↥L),
      x ∈ ρ.ker ↔ conjL ha x ∈ ρ.ker := by
    intro a ha x
    rw [hρ, ker_conjHomL, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hO, conjL_coe]
    exact mem_pCoreOf_iff_of_mem_normalizer ha x
  let M₁ : Subgroup ↥(Subgroup.normalizer (L : Set G)) :=
    { carrier := {a | IsInducedOn ρ (conjL a.2)}
      one_mem' := isInducedOn_one
      mul_mem' := fun {a b} ha hb => isInducedOn_mul a.2 b.2 ha hb
      inv_mem' := fun {a} ha => isInducedOn_inv a.2 ha }
  have hall : ∀ a : ↥(Subgroup.normalizer (L : Set G)), a ∈ M₁ := by
    by_contra hne
    push Not at hne
    obtain ⟨a₀, ha₀⟩ := hne
    have h2 : M₁.index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨a₀, fun b => ?_⟩
      by_cases hb : b ∈ M₁
      · refine Or.inr ⟨hb, fun hba => ha₀ ?_⟩
        have := M₁.mul_mem (M₁.inv_mem hb) hba
        simpa using this
      · refine Or.inl ⟨?_, hb⟩
        obtain ⟨φ, hφ⟩ := hTw ↥L ↥(fsuV T I) hW2 ρ n h.one_lt hnat (conjL b.2) (conjL a₀.2)
          (hker b.2) (hker a₀.2) hb ha₀
        refine ⟨φ, fun x => ?_⟩
        have hx : conjL (b * a₀).2 x = conjL b.2 (conjL a₀.2 x) := by
          apply Subtype.ext
          simp only [conjL_coe, Subgroup.coe_mul]
          group
        rw [hx, ← MulEquiv.trans_apply, hφ x]
    have hT : T.subgroupOf (Subgroup.normalizer (L : Set G)) ≤ M₁ := fun t ht =>
      isInducedOn_of_mem_normalizer hLV t.2 (T_le_normalizer_fsuV T I ht)
    have hdvd := Subgroup.index_dvd_of_le hT
    rw [h2] at hdvd
    exact (isSylowTwoOf_M h).2.2 hdvd
  exact isXSectionIso₂_of_isInducedOn hLV hm (hall ⟨m, hm⟩)

theorem stmt11_0_3_two (hTw : FactTwist) (h325 : Stmt3_2_5) (h1102 : Stmt11_0_2)
    (h324 : TmpL6_3_2_2_four) (h : Hyp11 G T L I n) :
    ∀ m ∈ Subgroup.normalizer (L : Set G),
      IsXSectionIso₂ L (CFSG.conjugate (fsuV T I) m ⊔ cVM T L I) (cVM T L I)
        (fsuV T I ⊔ cVM T L I) (cVM T L I) := by
  intro m hm
  by_cases hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · have hc : cVM T L I = ⊥ := by
      obtain ⟨-, h2⟩ := h324 G T L I h.fsu
      rw [fsuCVM_eq h, fsuL0_eq h, fsuM_eq h, hC] at h2
      rw [h2, conjClosure_bot]
    rw [hc, sup_bot_eq, sup_bot_eq]
    exact isXSectionIso₂_conjugate hTw h1102 h hC hm
  · have hV := fsuV_eq_VM_of_ne_bot h325 h hC
    have hmV : m ∈ Subgroup.normalizer (fsuV T I : Set G) := by
      rw [hV]
      exact le_normalizer_conjClosure _ _ hm
    have hVm : CFSG.conjugate (fsuV T I) m = fsuV T I := by
      ext x
      rw [mem_conjugate']
      exact (Subgroup.mem_normalizer_iff.mp hmV x).symm
    rw [hVm]
    have hcV : cVM T L I ≤ fsuV T I := by
      rw [hV]
      exact inf_le_left
    have hab := (isElemAbelian_fsuV h).1
    refine isXSectionIso₂_refl ?_ ?_
    · rw [BlueprintB2.normal_subgroupOf_iff_le_normalizer le_sup_right, sup_eq_left.mpr hcV]
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro c
      constructor
      · intro hc
        have : y * c = c * y := congrArg Subtype.val
          (mul_comm (⟨y, hy⟩ : ↥(fsuV T I)) ⟨c, hcV hc⟩)
        rw [this, mul_inv_cancel_right]
        exact hc
      · intro hc
        have h1 : y * c * y⁻¹ ∈ fsuV T I := hcV hc
        have : c = y⁻¹ * (y * c * y⁻¹) * y := by group
        have hc' : c ∈ fsuV T I := by
          rw [this]
          exact (fsuV T I).mul_mem ((fsuV T I).mul_mem ((fsuV T I).inv_mem hy) h1) hy
        have : y * c = c * y := congrArg Subtype.val
          (mul_comm (⟨y, hy⟩ : ↥(fsuV T I)) ⟨c, hc'⟩)
        rw [this, mul_inv_cancel_right] at hc
        exact hc
    · intro l hl
      exact mem_normalizer_inf (le_normalizer_conjClosure _ _ (Subgroup.le_normalizer hl))
        (mem_normalizer_centralizer (Subgroup.le_normalizer hl))

end CFSG.Quasithin.Vol2.Ch11.SecA
