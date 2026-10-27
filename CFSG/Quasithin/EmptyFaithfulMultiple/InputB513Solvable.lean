module

public import CFSG.Quasithin.Background.B1Solvable
public import CFSG.Quasithin.Background.B4Dual

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin

private theorem dualGrp_sq_eq_one {V : Type*} [CommGroup V] (φ : DualGrp V) : φ ^ 2 = 1 := by
  refine DualGrp.ext fun v => ?_
  have h : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide
  exact h (φ v)

private theorem index_fixV_zpowers_le {V : Type*} [CommGroup V] [Finite V] (t : MulAut V) :
    (fixV (Subgroup.zpowers t)).index ≤ Nat.card (commV (Subgroup.zpowers t)) := by
  let φ : V →* V :=
    { toFun := fun v => t v * v⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        rw [mul_comm b⁻¹ a⁻¹]
        exact mul_mul_mul_comm _ _ _ _ }
  have hker : φ.ker = fixV (Subgroup.zpowers t) := by
    ext v
    rw [MonoidHom.mem_ker, mem_fixV]
    change t v * v⁻¹ = 1 ↔ _
    rw [mul_inv_eq_one]
    exact ⟨fun h x hx => B1.zpowers_fix h x hx, fun h => h t (Subgroup.mem_zpowers t)⟩
  have hrange : φ.range ≤ commV (Subgroup.zpowers t) := by
    rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, v, rfl⟩
  rw [← hker, Subgroup.index_ker]
  exact Subgroup.card_le_of_le hrange

theorem inputB513Solvable_holds :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ X : Subgroup (MulAut V), Group.IsSolvable ↥X → X.map (dualAct V) ≠ ⊥ →
        CFSG.Open.pCore 2 ↥(X.map (dualAct V)) = ⊥ →
        X.map (dualAct V) =
          @ffJ (V →* Multiplicative (ZMod 2)) MonoidHom.instCommGroup (X.map (dualAct V)) →
        qOf X ≤ 2 := by
  intro V _ _ hV X hsolv hne hO2 hJ
  set X' := X.map (dualAct V) with hX'
  have hV' : ∀ φ : DualGrp V, φ ^ 2 = 1 := dualGrp_sq_eq_one
  have hsolv' : Group.IsSolvable ↥X' :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective (dualAct V) X)
  have hO2' : ∀ Q : Subgroup (MulAut (DualGrp V)), Q ≤ X' → (Q.subgroupOf X').Normal →
      IsPGroup 2 Q → Q = ⊥ := by
    refine normal_two_subgroups_trivial_of_pCoreOf_eq_bot ?_
    show (CFSG.Open.pCore 2 ↥X').map X'.subtype = ⊥
    rw [hO2, Subgroup.map_bot]
  obtain ⟨A₁, hA₁⟩ : ∃ A, IsFFStarOffender X' A := by
    by_contra hno
    push Not at hno
    exact hne (hJ.trans (le_bot_iff.1 (iSup₂_le fun A hA => absurd hA (hno A))))
  obtain ⟨A₀, -, hA₀⟩ := B1.exists_isFFStarMin_le hA₁
  obtain ⟨t', ht'X, -, hA₀t⟩ := B1.exists_transvection_of_isFFStarMin hV' hsolv' hO2' hA₀
  obtain ⟨t, htX, rfl⟩ := ht'X
  set A : Subgroup (MulAut V) := Subgroup.zpowers t with hA
  have hdual : dualSub A = A₀ := by
    rw [hA₀t, hA]
    exact MonoidHom.map_zpowers (dualAct V) t
  have hcard₀ : Nat.card A₀ = 2 := key_card_two hV' hsolv' hO2' hA₀
  have hcardA : Nat.card A = 2 := by
    rw [← card_dualSub hV A, hdual]
    exact hcard₀
  have hord : orderOf t = 2 := by
    rw [← Nat.card_zpowers]
    exact hcardA
  have hA2 : IsA2 X A := by
    refine ⟨Subgroup.zpowers_le.2 htX, fun hbot => ?_, ?_, ?_⟩
    · rw [hbot, Subgroup.card_bot] at hcardA
      omega
    · intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact zpow_mul_comm t m n
    · intro a ha
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hord,
        pow_orderOf_eq_one, one_zpow]
  have hquad : IsQuadratic A := by
    rw [isQuadratic_dualSub_iff hV A, hdual]
    exact B1_4_3 hV' hA₀
  have hidx₀ : (fixV A₀).index = 2 := by
    have h1 := B1.card_mul_card_fixV_of_isFFStarMin hV' hsolv' hO2' hA₀
    have h2 := B1.card_eq_index_mul A₀
    rw [hcard₀] at h1
    have hpos : 0 < Nat.card (fixV A₀) := Nat.card_pos
    have h3 : (fixV A₀).index * Nat.card (fixV A₀) = 2 * Nat.card (fixV A₀) := by
      rw [← h2, h1]
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  have hcomm : Nat.card (commV A) = 2 := by
    rw [← index_fixV_dualSub hV A, hdual, hidx₀]
  have hidx : (fixV A).index ≤ 2 := hcomm ▸ index_fixV_zpowers_le t
  have hle : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    rw [B1.card_eq_index_mul A, hcardA]
    exact Nat.mul_le_mul_right _ hidx
  have hr : rAV A ≤ 2 := ((rAV_le_one_iff hV hA2).2 hle).trans (by norm_num)
  have hq : qOf X ≤ ((2 : ℚ) : WithTop ℚ) := qOf_le_iff.2 ⟨A, hA2, hquad, hr⟩
  exact hq

end CFSG.Quasithin.EmptyFaithfulMultiple
