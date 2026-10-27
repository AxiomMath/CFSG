module

public import CFSG.Walter.W67.Section8.RMult
public import CFSG.Walter.W67.JR.RFacts
public import CFSG.Walter.J1Props.W67
public import CFSG.Walter.W67.Std

public section

namespace CFSG.Walter.W67

@[expose] def RCyclicSylow : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (hL : JRGroup L), hL.q ≠ 5 →
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ 3 → ∀ P : Sylow p L, IsCyclic (P : Subgroup L)

open scoped IsMulCommutative in
theorem isMulCommutative_sylow_of_isCyclic {E L : Type*} [Group E] [Finite E] [Group L]
    (Z : Subgroup E) [Z.Normal] (hZc : Z ≤ Subgroup.center E) (e : (E ⧸ Z) ≃* L) {p : ℕ}
    [Fact p.Prime] (hcyc : ∀ P : Sylow p L, IsCyclic (P : Subgroup L)) (P : Sylow p E) :
    IsMulCommutative (P : Subgroup E) := by
  set φ : E →* L := e.toMonoidHom.comp (QuotientGroup.mk' Z) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  set f : (P : Subgroup E) →* L := φ.comp (P : Subgroup E).subtype with hf
  have hrange : f.range = ((P.mapSurjective hφs : Sylow p L) : Subgroup L) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have : IsCyclic f.range := by
    rw [hrange]
    exact hcyc _
  have hker : f.rangeRestrict.ker ≤ Subgroup.center (P : Subgroup E) := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hf, MonoidHom.comp_apply, hφ,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZc hx) (y : E))
  exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f.rangeRestrict hker

theorem rMult_of_rCyclicSylow
    (hC : RCyclicSylow) : RMult := by
  intro L _ _ hL hq5 hq3 E _ _ Z _ hZc hZo hperf ⟨e⟩
  have h3 := RMult3.three_not_dvd Z hZc hL hq5 hq3 hperf e
  have hD : Z ⊓ commutator E = ⊥ := by
    refine inf_commutator_eq_bot hZc fun p hp hpZ => ?_
    have : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hZo) (even_iff_two_dvd.mpr hpZ)
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact h3 hpZ
    obtain ⟨P⟩ : Nonempty (Sylow p E) := inferInstance
    exact ⟨this, P, isMulCommutative_sylow_of_isCyclic Z hZc e (hC L hL hq5 p hp2 hp3) P⟩
  rwa [hperf, inf_top_eq] at hD

theorem theorem_of_rCyclicSylow
    (h66 : S_prop_6_6) (hC : RCyclicSylow) : Theorem := by
  have hM : RMult := rMult_of_rCyclicSylow hC
  suffices H : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G] (h : Hyp G), Nat.card G = n →
      Case1 h ∨ Case2 h by
    intro G _ _ h
    exact H _ G h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ h hn
    by_contra hc
    have hIH : IH (Nat.card G) := by
      intro X _ _ hX hlt
      exact ih (Nat.card X) (hn ▸ hlt) X hX rfl
    let m : MinCE G :=
      { toHyp := h, ih := hIH, not_case1 := fun h1 => hc (Or.inl h1),
        not_case2 := fun h2 => hc (Or.inr h2) }
    obtain ⟨s, -⟩ := Std.nonempty G m jFacts rFacts hM
    exact h66 G s jFacts rFacts hC

end CFSG.Walter.W67
