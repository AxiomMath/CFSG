module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open scoped commutatorElement Pointwise

variable {V : Type} [Group V] [Finite V]

abbrev Fix {V : Type} [Group V] (F : Subgroup (MulAut V)) : Subgroup V := FixedPoints.subgroup F V

theorem index_fix_zpowers_le_sq {e y : MulAut V} (he : e * e = 1) (hy : e * y * e⁻¹ = y⁻¹)
    (hodd : Odd (orderOf y)) :
    (Fix (Subgroup.zpowers y)).index ≤ (Fix (Subgroup.zpowers e)).index ^ 2 := by
  have hF : ∀ (L : Subgroup (MulAut V)) (v : V), v ∈ Fix L ↔ ∀ f ∈ L, f v = v :=
    fun L v => ⟨fun h f hf => (FixedPoints.mem_subgroup _ _ _).mp h ⟨f, hf⟩,
      fun h => (FixedPoints.mem_subgroup _ _ _).mpr fun m => h m.1 m.2⟩
  obtain ⟨k, hk⟩ := hodd
  have h1 : e * y = y⁻¹ * e := by rw [← hy, inv_mul_cancel_right]
  have hcomm : ∀ w : V, e (y w) = y⁻¹ (e w) := by
    intro w
    calc e (y w) = (e * y) w := (MulAut.mul_apply V e y w).symm
      _ = (y⁻¹ * e) w := by rw [h1]
      _ = y⁻¹ (e w) := MulAut.mul_apply V y⁻¹ e w
  have hsub : Fix (Subgroup.zpowers e) ⊓ (Fix (Subgroup.zpowers e)).map (y : V →* V) ≤
      Fix (Subgroup.zpowers y) := by
    intro v hv
    obtain ⟨hvC, hvY⟩ := Subgroup.mem_inf.mp hv
    have hev : e v = v := (hF _ _).mp hvC e (Subgroup.mem_zpowers e)
    obtain ⟨c, hcC, hyc⟩ := Subgroup.mem_map.mp hvY
    have hyc' : y c = v := hyc
    have hec : e c = c := (hF _ _).mp hcC e (Subgroup.mem_zpowers e)
    have hvinv : y⁻¹ c = v := by
      calc y⁻¹ c = y⁻¹ (e c) := by rw [hec]
        _ = e (y c) := (hcomm c).symm
        _ = e v := by rw [hyc']
        _ = v := hev
    have hyv : y v = c := by rw [← hvinv, MulAut.apply_inv_self]
    have hy2 : y (y v) = v := by rw [hyv]; exact hyc'
    have hsq : y ^ 2 ∈ MulAction.stabilizer (MulAut V) v := by
      rw [MulAction.mem_stabilizer_iff, sq, MulAut.smul_def, MulAut.mul_apply, hy2]
    have hpow : (y ^ 2) ^ (k + 1) = y := by
      have h0 : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
      rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ, h0, one_mul]
    have hyfix : y ∈ MulAction.stabilizer (MulAut V) v := by
      have := pow_mem hsq (k + 1)
      rwa [hpow] at this
    refine (hF _ _).mpr fun f hf => ?_
    exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr hyfix hf)
  have hCy : ((Fix (Subgroup.zpowers e)).map (y : V →* V)).index =
      (Fix (Subgroup.zpowers e)).index := Subgroup.index_map_equiv _ y
  calc (Fix (Subgroup.zpowers y)).index
      ≤ (Fix (Subgroup.zpowers e) ⊓ (Fix (Subgroup.zpowers e)).map (y : V →* V)).index :=
        Subgroup.index_antitone hsub
    _ ≤ (Fix (Subgroup.zpowers e)).index *
          ((Fix (Subgroup.zpowers e)).map (y : V →* V)).index := Subgroup.index_inf_le
    _ = (Fix (Subgroup.zpowers e)).index * (Fix (Subgroup.zpowers e)).index := by rw [hCy]
    _ = (Fix (Subgroup.zpowers e)).index ^ 2 := (sq _).symm

theorem index_fix_closure_le_cube {e y₁ y₂ : MulAut V} (he : e * e = 1)
    (h₁ : e * y₁ * e⁻¹ = y₁⁻¹) (h₂ : e * y₂ * e⁻¹ = y₂⁻¹) (hodd₁ : Odd (orderOf y₁))
    (hodd₂ : Odd (orderOf y₂)) :
    (Fix (Subgroup.closure {y₁, y₂})).index ≤ (Fix (Subgroup.zpowers e)).index ^ 3 := by
  have hF : ∀ (L : Subgroup (MulAut V)) (v : V), v ∈ Fix L ↔ ∀ f ∈ L, f v = v :=
    fun L v => ⟨fun h f hf => (FixedPoints.mem_subgroup _ _ _).mp h ⟨f, hf⟩,
      fun h => (FixedPoints.mem_subgroup _ _ _).mpr fun m => h m.1 m.2⟩
  have key : ∀ y : MulAut V, e * y * e⁻¹ = y⁻¹ → Odd (orderOf y) →
      Fix (Subgroup.zpowers e) ⊓ (Fix (Subgroup.zpowers e)).map (y : V →* V) ≤
        Fix (Subgroup.zpowers y) := by
    intro y hy hodd
    obtain ⟨k, hk⟩ := hodd
    have h1 : e * y = y⁻¹ * e := by rw [← hy, inv_mul_cancel_right]
    have hcomm : ∀ w : V, e (y w) = y⁻¹ (e w) := by
      intro w
      calc e (y w) = (e * y) w := (MulAut.mul_apply V e y w).symm
        _ = (y⁻¹ * e) w := by rw [h1]
        _ = y⁻¹ (e w) := MulAut.mul_apply V y⁻¹ e w
    intro v hv
    obtain ⟨hvC, hvY⟩ := Subgroup.mem_inf.mp hv
    have hev : e v = v := (hF _ _).mp hvC e (Subgroup.mem_zpowers e)
    obtain ⟨c, hcC, hyc⟩ := Subgroup.mem_map.mp hvY
    have hyc' : y c = v := hyc
    have hec : e c = c := (hF _ _).mp hcC e (Subgroup.mem_zpowers e)
    have hvinv : y⁻¹ c = v := by
      calc y⁻¹ c = y⁻¹ (e c) := by rw [hec]
        _ = e (y c) := (hcomm c).symm
        _ = e v := by rw [hyc']
        _ = v := hev
    have hyv : y v = c := by rw [← hvinv, MulAut.apply_inv_self]
    have hy2 : y (y v) = v := by rw [hyv]; exact hyc'
    have hsq : y ^ 2 ∈ MulAction.stabilizer (MulAut V) v := by
      rw [MulAction.mem_stabilizer_iff, sq, MulAut.smul_def, MulAut.mul_apply, hy2]
    have hpow : (y ^ 2) ^ (k + 1) = y := by
      have h0 : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
      rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ, h0, one_mul]
    have hyfix : y ∈ MulAction.stabilizer (MulAut V) v := by
      have := pow_mem hsq (k + 1)
      rwa [hpow] at this
    refine (hF _ _).mpr fun f hf => ?_
    exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr hyfix hf)
  have hCy : ∀ y : MulAut V, ((Fix (Subgroup.zpowers e)).map (y : V →* V)).index =
      (Fix (Subgroup.zpowers e)).index := fun y => Subgroup.index_map_equiv _ y
  have hsub : Fix (Subgroup.zpowers e) ⊓ (Fix (Subgroup.zpowers e)).map (y₁ : V →* V) ⊓
      (Fix (Subgroup.zpowers e)).map (y₂ : V →* V) ≤ Fix (Subgroup.closure {y₁, y₂}) := by
    intro v hv
    obtain ⟨hv12, hv2⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨hvC, hv1⟩ := Subgroup.mem_inf.mp hv12
    have hf1 : v ∈ Fix (Subgroup.zpowers y₁) :=
      key y₁ h₁ hodd₁ (Subgroup.mem_inf.mpr ⟨hvC, hv1⟩)
    have hf2 : v ∈ Fix (Subgroup.zpowers y₂) :=
      key y₂ h₂ hodd₂ (Subgroup.mem_inf.mpr ⟨hvC, hv2⟩)
    have hy1 : y₁ ∈ MulAction.stabilizer (MulAut V) v :=
      MulAction.mem_stabilizer_iff.mpr ((hF _ _).mp hf1 y₁ (Subgroup.mem_zpowers y₁))
    have hy2 : y₂ ∈ MulAction.stabilizer (MulAut V) v :=
      MulAction.mem_stabilizer_iff.mpr ((hF _ _).mp hf2 y₂ (Subgroup.mem_zpowers y₂))
    have hcl : Subgroup.closure ({y₁, y₂} : Set (MulAut V)) ≤
        MulAction.stabilizer (MulAut V) v :=
      (Subgroup.closure_le _).mpr
        (Set.insert_subset_iff.mpr ⟨hy1, Set.singleton_subset_iff.mpr hy2⟩)
    exact (hF _ _).mpr fun f hf => MulAction.mem_stabilizer_iff.mp (hcl hf)
  calc (Fix (Subgroup.closure {y₁, y₂})).index
      ≤ (Fix (Subgroup.zpowers e) ⊓ (Fix (Subgroup.zpowers e)).map (y₁ : V →* V) ⊓
          (Fix (Subgroup.zpowers e)).map (y₂ : V →* V)).index := Subgroup.index_antitone hsub
    _ ≤ (Fix (Subgroup.zpowers e) ⊓ (Fix (Subgroup.zpowers e)).map (y₁ : V →* V)).index *
          ((Fix (Subgroup.zpowers e)).map (y₂ : V →* V)).index := Subgroup.index_inf_le
    _ ≤ ((Fix (Subgroup.zpowers e)).index *
          ((Fix (Subgroup.zpowers e)).map (y₁ : V →* V)).index) *
          ((Fix (Subgroup.zpowers e)).map (y₂ : V →* V)).index :=
        Nat.mul_le_mul_right _ Subgroup.index_inf_le
    _ = (Fix (Subgroup.zpowers e)).index ^ 3 := by rw [hCy y₁, hCy y₂, pow_three, mul_assoc]

theorem index_fix_le_mul {F₁ F₂ F : Subgroup (MulAut V)}
    (h : ∀ v : V, (∀ f ∈ F₁, f v = v) → (∀ f ∈ F₂, f v = v) → ∀ f ∈ F, f v = v) :
    (Fix F).index ≤ (Fix F₁).index * (Fix F₂).index := by
  have hF : ∀ (L : Subgroup (MulAut V)) (v : V), v ∈ Fix L ↔ ∀ f ∈ L, f v = v :=
    fun L v => ⟨fun h f hf => (FixedPoints.mem_subgroup _ _ _).mp h ⟨f, hf⟩,
      fun h => (FixedPoints.mem_subgroup _ _ _).mpr fun m => h m.1 m.2⟩
  have hsub : Fix F₁ ⊓ Fix F₂ ≤ Fix F := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.mp hv
    exact (hF _ _).mpr (h v ((hF _ _).mp hv1) ((hF _ _).mp hv2))
  calc (Fix F).index ≤ (Fix F₁ ⊓ Fix F₂).index := Subgroup.index_antitone hsub
    _ ≤ (Fix F₁).index * (Fix F₂).index := Subgroup.index_inf_le

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
