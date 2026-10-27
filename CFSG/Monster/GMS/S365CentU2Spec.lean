module

public import CFSG.Monster.GMS.S365CentU2Check
public import CFSG.Monster.GMS.S365CentDefs
public import CFSG.Monster.GMS.S365USpec

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

open CFSG.Sporadic.Co1.Module.Odd (rho3 Hst omega0 S_card_eq isCo1TwoA_rho3 oddHyp73
  uCheck39_ok)

@[expose] def UP2 (a b : Co1) : Prop :=
  ∃ v₁ v₂ : Fin 24 → ZMod 2, v₁ ≠ v₂ ∧ v₁ ∈ co1Orbit 2 ∧ v₂ ∈ co1Orbit 2 ∧
    InIm a v₁ ∧ InIm b v₁ ∧ InIm (a * b) v₁ ∧ InIm a v₂ ∧ InIm b v₂ ∧ InIm (a * b) v₂

theorem UP2.conj {a b : Co1} (g : Co1) (h : UP2 a b) : UP2 (g * a * g⁻¹) (g * b * g⁻¹) := by
  obtain ⟨v₁, v₂, hne, h1, h2, ⟨p₁, h₁⟩, ⟨p₂, h₂⟩, ⟨p₃, h₃⟩, ⟨p₄, h₄⟩, ⟨p₅, h₅⟩, ⟨p₆, h₆⟩⟩ := h
  have key : ∀ (c : Co1) (p : Fin 24 → ZMod 2),
      co1Act (g * c * g⁻¹) (co1Act g p) = co1Act g (co1Act c p) := fun c p => by
    calc co1Act (g * c * g⁻¹) (co1Act g p) = (co1Act (g * c * g⁻¹) * co1Act g) p :=
          (Module.End.mul_apply _ _ _).symm
      _ = co1Act (g * c * g⁻¹ * g) p := by rw [← map_mul]
      _ = co1Act (g * c) p := by rw [show g * c * g⁻¹ * g = g * c by group]
      _ = co1Act g (co1Act c p) := by rw [map_mul, Module.End.mul_apply]
  have hprod : g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  have hinv : ∀ u : Fin 24 → ZMod 2, co1Act g⁻¹ (co1Act g u) = u := fun u => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinj : Function.Injective (co1Act g) := fun u v huv => by
    rw [← hinv u, ← hinv v, huv]
  refine ⟨co1Act g v₁, co1Act g v₂, fun h => hne (hinj h), Leech.co1Act_mem_co1Orbit h1 g,
    Leech.co1Act_mem_co1Orbit h2 g, ⟨co1Act g p₁, ?_⟩, ⟨co1Act g p₂, ?_⟩, ⟨co1Act g p₃, ?_⟩,
    ⟨co1Act g p₄, ?_⟩, ⟨co1Act g p₅, ?_⟩, ⟨co1Act g p₆, ?_⟩⟩
  · rw [key, ← map_add, ← h₁]
  · rw [key, ← map_add, ← h₂]
  · rw [hprod, key, ← map_add, ← h₃]
  · rw [key, ← map_add, ← h₄]
  · rw [key, ← map_add, ← h₅]
  · rw [hprod, key, ← map_add, ← h₆]

theorem UP2_of_S
    {a b : Co1} (ha : a ∈ SS) (hb : b ∈ SS)
    (hab : a * b = b * a) (hab' : a * b ∈ SS) : UP2 a b := by
  obtain ⟨W, U, hW, hU⟩ := uCheck39_ok
  obtain ⟨v₁, v₂, hne, ⟨g1, a1, b1, c1⟩, ⟨g2, a2, b2, c2⟩⟩ :=
    uk45_of_S hW hU oddHyp73 (S_card_eq card_centralizer_rho3) ha hb hab hab'
  exact ⟨v₁, v₂, hne le_rfl, g1, g2, a1, b1, c1, a2, b2, c2⟩

theorem co1FourU2 :
    Co1FourU2 := by
  intro r s hr hs hrs hrs2
  have hI := co1InvolutionFacts
  have hr2 : r * r = 1 := by
    have h : r ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hr.1])
    rwa [pow_two] at h
  have hs2 : s * s = 1 := by
    have h : s ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hs.1])
    rwa [pow_two] at h
  obtain ⟨ω, hω4, hωr, hωs⟩ := exists_fixed_type4 hr2 hs2 hrs
  have hω0 : omega0 ∈ co1Orbit 2 := by
    rw [CFSG.Sporadic.Co1.Module.Pairs.co1Orbit_two, CFSG.Sporadic.Co1.Module.Pairs.orbit_Co1_eq]
    exact CFSG.Sporadic.Co1.Module.Odd.omega0_mem
  obtain ⟨y, hy⟩ := Leech.exists_co1Act_eq hω0 hω4
  have hmem : ∀ u : Co1, co1Act u ω = ω → y⁻¹ * u * y ∈ Hst := by
    intro u hu
    refine MulAction.mem_stabilizer_iff.2 ?_
    show co1Act (y⁻¹ * u * y) omega0 = omega0
    have h1 : co1Act (y⁻¹ * u * y) omega0 = co1Act y⁻¹ (co1Act u (co1Act y omega0)) := by
      simp only [map_mul, Module.End.mul_apply]
    rw [h1, hy, hu, ← hy]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hconj : ∀ u : Co1, IsCo1TwoA u → IsConj rho3 (y⁻¹ * u * y) := by
    intro u hu
    have h1 : IsConj rho3 u :=
      hI.2.2 rho3 u isCo1TwoA_rho3.1 hu.1 isCo1TwoA_rho3.2 hu.2
    exact h1.trans (isConj_iff.2 ⟨y⁻¹, by group⟩)
  have hr'S : y⁻¹ * r * y ∈ SS := ⟨hmem r hωr, hconj r hr⟩
  have hs'S : y⁻¹ * s * y ∈ SS := ⟨hmem s hωs, hconj s hs⟩
  have hrs'S : y⁻¹ * r * y * (y⁻¹ * s * y) ∈ SS := by
    have e : y⁻¹ * r * y * (y⁻¹ * s * y) = y⁻¹ * (r * s) * y := by group
    rw [e]
    refine ⟨?_, hconj _ hrs2⟩
    rw [← e]
    exact Subgroup.mul_mem _ (hmem r hωr) (hmem s hωs)
  have hcomm' : y⁻¹ * r * y * (y⁻¹ * s * y) = y⁻¹ * s * y * (y⁻¹ * r * y) := by
    calc y⁻¹ * r * y * (y⁻¹ * s * y) = y⁻¹ * (r * s) * y := by group
      _ = y⁻¹ * (s * r) * y := by rw [hrs]
      _ = y⁻¹ * s * y * (y⁻¹ * r * y) := by group
  have hUP := (UP2_of_S hr'S hs'S hcomm' hrs'S).conj y
  have e1 : y * (y⁻¹ * r * y) * y⁻¹ = r := by group
  have e2 : y * (y⁻¹ * s * y) * y⁻¹ = s := by group
  rw [e1, e2] at hUP
  exact hUP

end S365

end CFSG.Monster.GMS
