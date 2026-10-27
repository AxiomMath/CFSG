module

public import CFSG.Quasithin.EmptyFaithful.Gap6R0A
public import CFSG.Quasithin.EmptyFaithful.Gap6R0E

public section

namespace CFSG.Quasithin

namespace LRed12

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.Gap6

variable {V : Type*} [CommGroup V] [Finite V] {X : Subgroup (MulAut V)}

theorem le_normalizer_pCoreOf_Jhat (p : ℕ) [Fact p.Prime] :
    X ≤ Subgroup.normalizer ((pCoreOf p (Jhat X) : Subgroup (MulAut V)) : Set (MulAut V)) := by
  intro g hg
  have h1 := pCoreOf_map_mulEquiv (r := p) (MulAut.conj g) (Jhat X)
  rw [map_conj_Jhat hg] at h1
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1.symm

theorem pCoreOf_Jhat_le (p : ℕ) [Fact p.Prime] : pCoreOf p (Jhat X) ≤ pCoreOf p X :=
  le_pCoreOf_of_le_normalizer p ((pCoreOf_le p (Jhat X)).trans (Jhat_le X))
    (le_normalizer_pCoreOf_Jhat p) (pCoreOf_isPGroup p (Jhat X))

theorem centralizes_pCore_of_qhatStar (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hA : A ∈ QhatStar X) (hrk : 1 < rk A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    A ≤ Subgroup.centralizer (pCoreOf p X : Set (MulAut V)) := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, hmin⟩ := QhatStar_spec hA
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  by_contra hne
  have : Fact p.Prime := ⟨hp⟩
  have hD : ⁅pCoreOf p X, A⁆ ≠ ⊥ := commutator_ne_bot_iff.mpr ⟨y, hy, a, ha, fun h => hne h.symm⟩
  exact hp3 ((D2_13 hV hr hA hp2 rfl hD).2.2.2.2 hrk).1

theorem not_centralizes_pCore_three (hsolv : Group.IsSolvable ↥X) (hO2 : pCoreOf 2 X = ⊥)
    {j : MulAut V} (hjJ : j ∈ Jhat X)
    (hj5 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ y ∈ pCoreOf p X, j * y = y * j)
    (hjC : ∃ c ∈ fixV (fittingOf (Jhat X)), j c ≠ c) :
    ∃ y ∈ pCoreOf 3 (Jhat X), j * y ≠ y * j := by
  by_contra hcon
  push Not at hcon
  have hJX : Jhat X ≤ X := Jhat_le X
  have hO2J : pCoreOf 2 (Jhat X) = ⊥ := pCoreOf_two_Jhat hO2
  have hsolvJ : Group.IsSolvable ↥(Jhat X) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJX)
  have hodd : oddFitting (Jhat X) ≤ Subgroup.centralizer ({j} : Set (MulAut V)) := by
    refine iSup_le fun p => iSup_le fun hp => iSup_le fun hp2 => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases h3 : p = 3
    · subst h3
      exact (hcon y hy).symm
    · have : Fact p.Prime := ⟨hp⟩
      exact (hj5 p hp hp2 h3 y (pCoreOf_Jhat_le p hy)).symm
  have hjF : j ∈ fittingOf (Jhat X) := by
    refine fstar_of_solvable hsolvJ hjJ fun f hf => ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (hodd (fittingOf_le_oddFitting hO2J hf))
    exact this.symm
  obtain ⟨c, hc, hjc⟩ := hjC
  exact hjc (hc j hjF)

end LRed12

end CFSG.Quasithin
