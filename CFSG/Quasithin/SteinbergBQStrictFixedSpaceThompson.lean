module

public import CFSG.Quasithin.Background.BlueprintB2Thompson

public section

namespace CFSG.Quasithin.SteinbergBQ

open CFSG CFSG.Quasithin.BlueprintB2

theorem mem_fixedPoints_subgroup_mulAut_iff {V : Type*} [Group V] {E : Subgroup (MulAut V)}
    {v : V} : v ∈ FixedPoints.subgroup E V ↔ ∀ σ ∈ E, σ v = v :=
  ⟨fun h σ hσ => h ⟨σ, hσ⟩, fun h σ => h σ σ.2⟩

variable {T : Type*} [Group T]

theorem ker_conjNormal (V : Subgroup T) [V.Normal] :
    (MulAut.conjNormal : T →* MulAut V).ker = Subgroup.centralizer (V : Set T) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have h1 := congrArg (fun σ : MulAut V => ((σ ⟨v, hv⟩ : V) : T)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc v * x = x * v * x⁻¹ * x := by rw [h1]
      _ = x * v := by group
  · intro h
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.one_apply, ← h v v.2, mul_inv_cancel_right]

theorem card_map_eq_relIndex_ker {H : Type*} [Group H] (f : T →* H) (A : Subgroup T) :
    Nat.card (A.map f) = f.ker.relIndex A := by
  have h1 : (f.comp A.subtype).range = A.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h2 : (f.comp A.subtype).ker = f.ker.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  rw [← h1, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, h2,
    ← Subgroup.index_eq_card]
  rfl

theorem strict_fixed_space_inequality_centralizes_elementary_thompson_subgroup {p : ℕ}
    [Fact p.Prime] [Finite T] (hT : IsPGroup p T) (V : Subgroup T) [V.Normal]
    (hV : IsElementaryAbelian p V)
    (hstrict : ∀ E : Subgroup (MulAut V), E ≤ (MulAut.conjNormal : T →* MulAut V).range →
      E ≠ ⊥ → IsElementaryAbelian p E → Nat.card E < (FixedPoints.subgroup E V).index) :
    (∀ A ∈ elemThompsonFamily T p, A ≤ Subgroup.centralizer (V : Set T)) ∧
      Subgroup.map (Subgroup.centralizer (V : Set T)).subtype ''
          elemThompsonFamily (Subgroup.centralizer (V : Set T)) p = elemThompsonFamily T p ∧
      elemThompson T p =
        (elemThompson (Subgroup.centralizer (V : Set T)) p).map
          (Subgroup.centralizer (V : Set T)).subtype ∧
      elemThompson T p ≤ Subgroup.centralizer (V : Set T) := by
  classical
  have hker := ker_conjNormal V
  have hA : ∀ A ∈ elemThompsonFamily T p, A ≤ Subgroup.centralizer (V : Set T) := by
    intro A hAf
    obtain ⟨hAel, hmax⟩ := mem_elemThompsonFamily_iff.1 hAf
    obtain ⟨-, hineq, -⟩ := qt_A7_maximal_elementary_action_inequality p hT V hV A hAel hmax
    by_contra hAR
    have hE : A.map (MulAut.conjNormal : T →* MulAut V) ≠ ⊥ := by
      intro h
      apply hAR
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff _).1 h
    have h1 := hstrict _ (Subgroup.map_le_range _ A) hE (isElementaryAbelian_map hAel _)
    have h2 : Nat.card (A.map (MulAut.conjNormal : T →* MulAut V)) =
        (A ⊓ Subgroup.centralizer (V : Set T)).relIndex A := by
      rw [card_map_eq_relIndex_ker, hker, Subgroup.relIndex, Subgroup.relIndex,
        Subgroup.inf_subgroupOf_left]
    have h3 : (FixedPoints.subgroup (A.map (MulAut.conjNormal : T →* MulAut V)) V).index =
        (V ⊓ Subgroup.centralizer (A : Set T)).relIndex V := by
      rw [Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
      congr 1
      ext v
      rw [mem_fixedPoints_subgroup_mulAut_iff, Subgroup.mem_subgroupOf,
        Subgroup.mem_centralizer_iff]
      constructor
      · intro h a ha
        have h4 := congrArg Subtype.val (h _ ⟨a, ha, rfl⟩)
        change ((MulAut.conjNormal a v : V) : T) = v at h4
        rw [MulAut.conjNormal_apply] at h4
        calc a * (v : T) = a * v * a⁻¹ * a := by group
          _ = v * a := by rw [h4]
      · rintro h _ ⟨a, ha, rfl⟩
        apply Subtype.ext
        change ((MulAut.conjNormal a v : V) : T) = v
        rw [MulAut.conjNormal_apply, h a ha, mul_inv_cancel_right]
    omega
  have hJR : elemThompson T p ≤ Subgroup.centralizer (V : Set T) := sSup_le hA
  have hrk := pRank_eq_of_elemThompson_le (p := p) hJR
  have hJ := elemThompson_map_subtype (p := p) hJR
  refine ⟨hA, ?_, hJ.symm, hJR⟩
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact ⟨isElementaryAbelian_map hB.1 _, by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hB.2, hrk]⟩
  · intro hAf
    have hAR := hA A hAf
    refine ⟨A.subgroupOf _, ⟨isElementaryAbelian_subgroupOf hAf.1, ?_⟩,
      Subgroup.map_subgroupOf_eq_of_le hAR⟩
    rw [card_subgroupOf_eq hAR, hAf.2, hrk]

end CFSG.Quasithin.SteinbergBQ
