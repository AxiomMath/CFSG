module

public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.H13.A5.F4P

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {G : Type} [Group G] {F : Type} [Field F]

theorem sl_transvection_inv {i j : Fin 3} (hij : i ≠ j) (c : F) :
    (SpecialLinearGroup.transvection hij (-c))⁻¹ = SpecialLinearGroup.transvection hij c := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show Matrix.transvection i j (-c) * Matrix.transvection i j c = 1
  rw [Matrix.transvection_mul_transvection_same i j hij, neg_add_cancel, Matrix.transvection_zero]

theorem exists_dual_transvection {L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)}
    (hα : Function.Surjective α) {i j : Fin 3} (hij : i ≠ j) (c : F) :
    ∃ a : ↥L, moduleAct true (α a : GL (Fin 3) F) = 1 + Matrix.single j i c := by
  have hmem : SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (-c)) ∈
      StatedSL 3 F :=
    Subgroup.subset_closure (SpecialLinearGroup.transvection hij (-c)).2
  obtain ⟨a, ha⟩ := hα ⟨_, hmem⟩
  refine ⟨a, ?_⟩
  simp only [moduleAct, ite_true, ha]
  rw [← map_inv, sl_transvection_inv]
  show (Matrix.transvection i j c)ᵀ = _
  rw [Matrix.transvection, transpose_add, transpose_one, transpose_single]

theorem exists_crd {L V Z : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)} {dual : Bool}
    (h : IsSumOfNaturalModulesVia L V Z α dual 1) :
    ∃ κ : ↥V → (Fin 3 → F), (∀ v w, κ (v * w) = κ v + κ w) ∧ (∀ t, ∃ v, κ v = t) ∧
      (∀ v, κ v = 0 ↔ (v : G) ∈ Z) ∧
      ∀ (a : ↥L) (u v : ↥V), (v : G) = a * u * a⁻¹ →
        κ v = moduleAct dual (α a : GL (Fin 3) F) *ᵥ κ u := by
  obtain ⟨-, -, β, hβs, hβk, hβe⟩ := h
  refine ⟨fun v => Multiplicative.toAdd (β v) 0, fun v w => by simp, fun t => ?_,
    fun v => ?_, fun a u v huv => hβe a u v huv 0⟩
  · obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd fun _ => t)
    exact ⟨v, by show Multiplicative.toAdd (β v) 0 = t; rw [hv]; rfl⟩
  · rw [← Subgroup.mem_subgroupOf, ← hβk, MonoidHom.mem_ker]
    constructor
    · intro h0
      apply Multiplicative.toAdd.injective
      funext k
      fin_cases k
      exact h0
    · intro h1
      show Multiplicative.toAdd (β v) 0 = 0
      rw [h1]
      rfl

theorem eq_of_not_le {L V Z X : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)}
    (hα : Function.Surjective α) (h : IsSumOfNaturalModulesVia L V Z α true 1) (hZX : Z ≤ X)
    (hXV : X ≤ V) (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hX : ¬ X ≤ Z) : X = V := by
  obtain ⟨κ, hκm, hκs, hκ0, hκc⟩ := exists_crd h
  let S : AddSubgroup (Fin 3 → F) :=
    { carrier := {t | ∃ x, ∃ hx : x ∈ X, κ ⟨x, hXV hx⟩ = t}
      zero_mem' := ⟨1, X.one_mem, (hκ0 _).mpr (by simp)⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, X.mul_mem hx hy, hκm ⟨x, hXV hx⟩ ⟨y, hXV hy⟩⟩
      neg_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨x⁻¹, X.inv_mem hx, ?_⟩
        have h1 := hκm ⟨x⁻¹, hXV (X.inv_mem hx)⟩ ⟨x, hXV hx⟩
        have h2 : κ (⟨x⁻¹, hXV (X.inv_mem hx)⟩ * ⟨x, hXV hx⟩) = 0 :=
          (hκ0 _).mpr (by simp)
        rw [h2] at h1
        exact eq_neg_of_add_eq_zero_left h1.symm }
  have hS : ∀ {i j : Fin 3}, i ≠ j → ∀ c : F, ∀ t ∈ S, t + Pi.single j (c * t i) ∈ S := by
    rintro i j hij c _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := exists_dual_transvection hα hij c
    have hy : (a : G) * x * (a : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hLX a.2) x).mp hx
    refine ⟨_, hy, ?_⟩
    rw [hκc a ⟨x, hXV hx⟩ ⟨_, hXV hy⟩ rfl, ha, add_mulVec, one_mulVec, single_mulVec]
    rfl
  obtain ⟨x, hxX, hxZ⟩ := Set.not_subset.mp hX
  have hw : κ ⟨x, hXV hxX⟩ ≠ 0 := fun h0 => hxZ ((hκ0 _).mp h0)
  obtain ⟨i, hi⟩ : ∃ i, κ ⟨x, hXV hxX⟩ i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hw (funext hne)
  have hj : ∀ j, j ≠ i → ∀ c : F, Pi.single j c ∈ S := by
    intro j hji c
    have h1 := hS (Ne.symm hji) (c / κ ⟨x, hXV hxX⟩ i) _ ⟨x, hxX, rfl⟩
    have h2 := S.sub_mem h1 ⟨x, hxX, rfl⟩
    rwa [add_sub_cancel_left, div_mul_cancel₀ _ hi] at h2
  have hsingle : ∀ k (c : F), Pi.single k c ∈ S := by
    intro k c
    by_cases hk : k = i
    · subst hk
      obtain ⟨j, hjk⟩ : ∃ j : Fin 3, j ≠ k := ⟨k + 1, by fin_cases k <;> decide⟩
      have h1 := hS hjk c _ (hj j hjk 1)
      have h2 := S.sub_mem h1 (hj j hjk 1)
      rwa [add_sub_cancel_left, Pi.single_eq_same, mul_one] at h2
    · exact hj k hk c
  refine le_antisymm hXV fun v hv => ?_
  have hvS : κ ⟨v, hv⟩ ∈ S := by
    have e : κ ⟨v, hv⟩ = Pi.single 0 (κ ⟨v, hv⟩ 0) + Pi.single 1 (κ ⟨v, hv⟩ 1) +
        Pi.single 2 (κ ⟨v, hv⟩ 2) := by
      funext k
      fin_cases k <;> simp
    rw [e]
    exact S.add_mem (S.add_mem (hsingle _ _) (hsingle _ _)) (hsingle _ _)
  obtain ⟨y, hy, hyv⟩ := hvS
  have hz : κ (⟨y, hXV hy⟩⁻¹ * ⟨v, hv⟩) = 0 := by
    have h2 := hκm (⟨y, hXV hy⟩⁻¹) ⟨y, hXV hy⟩
    rw [inv_mul_cancel, (hκ0 1).mpr (by simp)] at h2
    rw [hκm, ← hyv]
    exact h2.symm
  have hzX : (y⁻¹ * v : G) ∈ X := hZX ((hκ0 _).mp hz)
  have e : v = y * (y⁻¹ * v) := by group
  rw [e]
  exact X.mul_mem hy hzX

end CFSG.Quasithin.H13.A5.F4P
