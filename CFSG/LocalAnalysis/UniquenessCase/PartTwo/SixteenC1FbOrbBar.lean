module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c1_ncard_conj_orbit (T : Subgroup G) (y : G) :
    Set.ncard {x : G | ∃ t ∈ T, x = t * y * t⁻¹} =
      (Subgroup.centralizer ({y} : Set G) ⊓ T).relIndex T := by
  classical
  set U' : Subgroup (ConjAct G) := T.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom
    with hU'
  have hsmul : ∀ (c : U') (x : G), c • x =
      ConjAct.ofConjAct (c : ConjAct G) * x * (ConjAct.ofConjAct (c : ConjAct G))⁻¹ :=
    fun c x => ConjAct.smul_def (c : ConjAct G) x
  have horb : MulAction.orbit U' y = {x : G | ∃ t ∈ T, x = t * y * t⁻¹} := by
    ext x
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨_, u, hu, rfl⟩ := c
      exact ⟨u, hu, by rw [hsmul]; simp⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨ConjAct.toConjAct u, u, hu, rfl⟩, by rw [hsmul]; simp⟩
  have hstab : Nat.card (MulAction.stabilizer U' y) =
      Nat.card ↥(Subgroup.centralizer ({y} : Set G) ⊓ T) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨ConjAct.ofConjAct ((c : U') : ConjAct G), ?_⟩
        invFun := fun g => ⟨⟨ConjAct.toConjAct (g : G), g, (mem_inf.mp g.2).2, rfl⟩, ?_⟩
        left_inv := fun c => by simp
        right_inv := fun g => by simp }
    · obtain ⟨⟨_, u, hu, rfl⟩, hc⟩ := c
      refine mem_inf.mpr ⟨?_, by simpa using hu⟩
      have h := MulAction.mem_stabilizer_iff.mp hc
      rw [hsmul] at h
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.toMonoidHom_eq_coe] at h ⊢
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h
    · rw [MulAction.mem_stabilizer_iff, hsmul]
      simp only [ConjAct.ofConjAct_toConjAct]
      have := mem_centralizer_singleton_iff.mp (mem_inf.mp g.2).1
      rw [mul_inv_eq_iff_eq_mul]
      exact this
  have hU'card : Nat.card U' = Nat.card T :=
    card_map_of_injective (ConjAct.toConjAct : G ≃* ConjAct G).injective
  have e1 := card_mul_index (MulAction.stabilizer U' y)
  have e2 := (Subgroup.centralizer ({y} : Set G)).relIndex_mul_card T
  rw [MulAction.index_stabilizer, horb, hstab, hU'card, ← e2, mul_comm] at e1
  rw [Subgroup.inf_relIndex_right]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos e1

theorem s16c1_orbit_bar_le {T V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {x : IntMod V hV}
    {S₁ : Subgroup (MulAut (Vtil V₀ V hV))} (hS₁ : S₁ ≤ barSub V₀ V hV T)
    (h : (T ⊓ centralizer ({x.val} : Set G)).relIndex T ≤ 4) :
    (ptCent S₁ (mkTil V₀ V hV x)).relIndex S₁ ≤ 4 := by
  classical
  set w : Vtil V₀ V hV := mkTil V₀ V hV x with hw
  set C : Subgroup G := Subgroup.centralizer ({x.val} : Set G) with hC
  set B : Set G := {y : G | ∃ t ∈ T, y = t * x.val * t⁻¹} with hB
  set Bv : Set (IntMod V hV) := {y : IntMod V hV | y.val ∈ B} with hBv
  have hstab : (ptCent S₁ w).relIndex S₁ = (MulAction.orbit S₁ w).ncard := by
    rw [ptCent, Subgroup.relIndex, Subgroup.inf_subgroupOf_left,
      MulAction.stabilizer_subgroupOf S₁ w]
    exact MulAction.index_stabilizer (↥S₁) w
  have horb_sub : MulAction.orbit S₁ w ⊆ mkTil V₀ V hV '' Bv := by
    rintro z ⟨φ, rfl⟩
    have hφbar : (φ : MulAut (Vtil V₀ V hV)) ∈ barSub V₀ V hV T := hS₁ φ.2
    obtain ⟨g, hgT, hgφ⟩ := (mem_barSub V₀ V hV T (φ : MulAut (Vtil V₀ V hV))).1 hφbar
    refine ⟨actStab V₀ V hV g x, ?_, ?_⟩
    · rw [hBv, hB]
      exact ⟨(g : G), hgT, actStab_apply_val V₀ V hV g x⟩
    · rw [hw, ← actTil_mk V₀ V hV g x, hgφ]
      rfl
  have hBv_le : Bv.ncard ≤ B.ncard := by
    rw [← Set.ncard_image_of_injective Bv IntMod.val_injective]
    exact Set.ncard_le_ncard fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      exact hy
  have hBcard : B.ncard = (T ⊓ C).relIndex T := by
    rw [hB, hC, inf_comm]
    exact s16c1_ncard_conj_orbit T x.val
  have hB4 : B.ncard ≤ 4 := by
    rw [hBcard]
    exact h
  have h1 : (MulAction.orbit S₁ w).ncard ≤ (mkTil V₀ V hV '' Bv).ncard :=
    Set.ncard_le_ncard horb_sub
  have h2 : (mkTil V₀ V hV '' Bv).ncard ≤ Bv.ncard := Set.ncard_image_le
  have hbound : (MulAction.orbit S₁ w).ncard ≤ 4 :=
    le_trans h1 (le_trans h2 (le_trans hBv_le hB4))
  rw [hstab]
  exact hbound

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
