module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.BAuxOrbit

public section

open CFSG.SignalizerFunctorTheorem.Nonsolvable CFSG.SignalizerFunctorTheorem.McBride

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.BAux

variable {X G : Type*} [Group X] [Group G] {φ : X →* G}

theorem mem_sSup_commute {T : Set (Subgroup G)} {J : Subgroup G}
    (hT : ∀ J' ∈ T, ∀ a ∈ J', ∀ b ∈ J, a * b = b * a) {k : G} (hk : k ∈ sSup T) {j : G}
    (hj : j ∈ J) : k * j = j * k := by
  have hle : sSup T ≤ Subgroup.centralizer (J : Set G) := by
    refine sSup_le fun J' hJ' a ha => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hT J' hJ' a ha b hb).symm
  exact (Subgroup.mem_centralizer_iff.mp (hle hk) j hj).symm

theorem cen_empty : cen φ (∅ : Set (Subgroup G)) = ⊤ := by
  refine top_unique fun x _ J hJ => ?_
  exact absurd hJ (Set.notMem_empty J)

theorem cen_union (S₁ S₂ : Set (Subgroup G)) : cen φ (S₁ ∪ S₂) = cen φ S₁ ⊓ cen φ S₂ := by
  ext x
  simp only [mem_cen_iff, Subgroup.mem_inf, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun J hJ => h J (Or.inl hJ), fun J hJ => h J (Or.inr hJ)⟩
  · rintro ⟨h1, h2⟩ J (hJ | hJ)
    · exact h1 J hJ
    · exact h2 J hJ

theorem bound_aux [Finite X] [Finite G] (hX : oStar X = ⊤) (hperf : Group.IsPerfect X)
    {𝓛 : Set (Subgroup G)} (hfin : 𝓛.Finite) (hB : ∀ J ∈ 𝓛, HypB ↥J)
    (hcomm : ∀ J ∈ 𝓛, ∀ J' ∈ 𝓛, J ≠ J' → ∀ a ∈ J, ∀ b ∈ J', a * b = b * a) :
    ∀ n : ℕ, ∀ S : Set (Subgroup G), S ⊆ 𝓛 → IsInv φ S → S.ncard = n →
      deg X ≤ deg ↥(cen φ S) + kappa S ∧
        (deg X = deg ↥(cen φ S) + kappa S → Inner φ S) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS hSinv hn
  have hSfin : S.Finite := hfin.subset hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨J₀, hJ₀⟩
  · refine ⟨?_, fun _ x => ⟨1, one_mem _, fun J hJ => absurd hJ (Set.notMem_empty J)⟩⟩
    rw [cen_empty, kappa_empty, add_zero]
    exact (KAPI.deg_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)).ge
  set O : Set (Subgroup G) := {J | ∃ x : X, J = act φ x J₀} with hOdef
  have hOS : O ⊆ S := by
    rintro _ ⟨x, rfl⟩
    exact hSinv x J₀ hJ₀
  have hJ₀O : J₀ ∈ O := ⟨1, (act_one J₀).symm⟩
  have hOinv : IsInv φ O := by
    rintro y _ ⟨x, rfl⟩
    exact ⟨y * x, (act_mul y x J₀).symm⟩
  have hOtr : ∀ J ∈ O, ∀ J' ∈ O, ∃ x : X, act φ x J = J' := by
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
    exact ⟨x' * x⁻¹, by rw [act_mul, act_inv_act]⟩
  have hOfin : O.Finite := hSfin.subset hOS
  have hOB : ∀ J ∈ O, HypB ↥J := fun J hJ => hB J (hS (hOS hJ))
  have hO := single_orbit hX hOinv hOfin ⟨J₀, hJ₀O⟩ hOtr hOB
  by_cases hOeq : O = S
  · rw [← hOeq]
    exact ⟨hO.1, fun heq => (hO.2 hperf heq).2⟩
  ·
    have hS₂inv : IsInv φ (S \ O) := by
      intro x J hJ
      refine ⟨hSinv x J hJ.1, fun hxO => hJ.2 ?_⟩
      obtain ⟨y, hy⟩ := hxO
      refine ⟨x⁻¹ * y, ?_⟩
      rw [act_mul, ← hy, act_inv_act]
    have hS₁lt : O ⊂ S := lt_of_le_of_ne hOS hOeq
    have hS₂lt : S \ O ⊂ S := by
      refine ⟨Set.sdiff_subset, fun h => ?_⟩
      exact (h hJ₀).2 hJ₀O
    have hn₁ : O.ncard < n := hn ▸ Set.ncard_lt_ncard hS₁lt hSfin
    have hn₂ : (S \ O).ncard < n := hn ▸ Set.ncard_lt_ncard hS₂lt hSfin
    have hP₁ := ih _ hn₁ O (hOS.trans hS) hOinv rfl
    have hP₂ := ih _ hn₂ (S \ O) (Set.sdiff_subset.trans hS) hS₂inv rfl
    have hOn : (cen φ O).Normal := cen_normal hOinv
    have hS₂n : (cen φ (S \ O)).Normal := cen_normal hS₂inv
    have hunion : S = O ∪ (S \ O) := (Set.union_sdiff_cancel hOS).symm
    have hcen : cen φ S = cen φ O ⊓ cen φ (S \ O) := by
      conv_lhs => rw [hunion]
      exact cen_union _ _
    have hkap : kappa S = kappa O + kappa (S \ O) := by
      conv_lhs => rw [hunion]
      exact kappa_union hOfin (hSfin.subset Set.sdiff_subset) Set.disjoint_sdiff_right
    obtain ⟨hineq, himpl⟩ := KAPI.deg_two_normal hX (cen φ O) (cen φ (S \ O)) hP₁.1 hP₂.1
    rw [hcen, hkap]
    refine ⟨by omega, fun heq => ?_⟩
    obtain ⟨he₁, he₂⟩ := himpl (by omega)
    have hI₁ := hP₁.2 he₁
    have hI₂ := hP₂.2 he₂
    intro x
    obtain ⟨k₁, hk₁, hx₁⟩ := hI₁ x
    obtain ⟨k₂, hk₂, hx₂⟩ := hI₂ x
    refine ⟨k₁ * k₂, mul_mem (sSup_le_sSup hOS hk₁)
      (sSup_le_sSup (Set.sdiff_subset : S \ O ⊆ S) hk₂), ?_⟩
    have hk12 : k₁ * k₂ = k₂ * k₁ := by
      have hle : sSup (S \ O) ≤ Subgroup.centralizer ({k₁} : Set G) := by
        refine sSup_le fun J' hJ' a ha => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        refine (mem_sSup_commute (fun J'' hJ'' a' ha' b hb => ?_) hk₁ ha).symm
        exact hcomm J'' (hS (hOS hJ'')) J' (hS hJ'.1) (fun h => hJ'.2 (h ▸ hJ'')) a' ha' b hb
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hk₂)).symm
    intro J hJ j hj
    by_cases hJO : J ∈ O
    · have hc : ∀ J' ∈ S \ O, ∀ a ∈ J', ∀ b ∈ J, a * b = b * a := by
        intro J' hJ' a ha b hb
        exact hcomm J' (hS hJ'.1) J (hS (hOS hJO)) (fun h => hJ'.2 (h ▸ hJO)) a ha b hb
      have hk₂j := mem_sSup_commute hc hk₂ hj
      have h : k₂ * j * k₂⁻¹ = j := by rw [hk₂j]; group
      calc φ x * j * (φ x)⁻¹ = k₁ * j * k₁⁻¹ := hx₁ J hJO j hj
        _ = k₁ * (k₂ * j * k₂⁻¹) * k₁⁻¹ := by rw [h]
        _ = (k₁ * k₂) * j * (k₁ * k₂)⁻¹ := by group
    · have hJS₂ : J ∈ S \ O := ⟨hJ, hJO⟩
      have hc : ∀ J' ∈ O, ∀ a ∈ J', ∀ b ∈ J, a * b = b * a := by
        intro J' hJ' a ha b hb
        exact hcomm J' (hS (hOS hJ')) J (hS hJ) (fun h => hJO (h ▸ hJ')) a ha b hb
      have hk₁j := mem_sSup_commute hc hk₁ hj
      have h : k₁ * j * k₁⁻¹ = j := by rw [hk₁j]; group
      calc φ x * j * (φ x)⁻¹ = k₂ * j * k₂⁻¹ := hx₂ J hJS₂ j hj
        _ = k₂ * (k₁ * j * k₁⁻¹) * k₂⁻¹ := by rw [h]
        _ = (k₁ * k₂) * j * (k₁ * k₂)⁻¹ := by rw [hk12]; group

end CFSG.SignalizerFunctorTheorem.McBride.Near.BAux
