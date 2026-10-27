module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFacts
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF2
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorus
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Model

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

namespace CFSG.RankThree.PartTwo.Sec19

section Plain

variable {G : Type*} [Group G]

theorem map_congr_conj_map (E₀ : Subgroup G) (g : G) :
    (E₀.map (MulAut.conj : G →* MulAut G)).map (MulAut.congr (MulAut.conj g)).toMonoidHom =
      (E₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj : G →* MulAut G) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun e => ?_
  show (MulAut.congr (MulAut.conj g)) (MulAut.conj e) = MulAut.conj ((MulAut.conj g) e)
  rw [congr_apply_eq]
  exact aut_conj_conj (MulAut.conj g) e

theorem map_conj_closure_pair (a b : G) :
    (Subgroup.closure ({a, b} : Set G)).map (MulAut.conj : G →* MulAut G) =
      Subgroup.closure ({MulAut.conj a, MulAut.conj b} : Set (MulAut G)) := by
  rw [MonoidHom.map_closure, Set.image_pair]

end Plain

section BridgeBigInner

@[expose] def TrialityThreeInnerModelBig : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (X : Type) [Field X] [Finite X] (σ : X ≃+* X),
    Nat.card X = (2 ^ n) ^ 3 → (∀ c : X, σ c = c ^ (2 ^ n)) →
      ∀ E : Subgroup (MulAut (C0 σ)), CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
        (∀ φ ∈ E, ∃ g : C0 σ, φ = MulAut.conj g) → Subgroup.closure (fixUnion E) = ⊤

theorem trialityThreeInnerBig_of_model (h : TrialityThreeInnerModelBig) :
    ∀ q : TauCeti.PrimePower, q.p = 2 → 2 ≤ q.exponent → ∀ (K : Type) [Group K] [Finite K]
      [IsSimpleGroup K], IsoLie K (.trialityD4 q) → ∀ E : Subgroup (MulAut K),
        CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 → (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) →
          Subgroup.closure (fixUnion E) = ⊤ := by
  intro q hq hge K _ _ _ hiso E hE hcard hinner
  obtain ⟨X, hF, hfin, σ, hcardX, hσ, -, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.CTP.exists_trialityD4_model hq hiso
  have hE' : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    CFSG.LieType.SeitzGeneration.isElementaryAbelian_of_isElemAbelian
      (CFSG.LieType.SeitzGeneration.isElemAbelian_map_congr e
        (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hE))
  have hcard' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 :=
    (CFSG.LieType.SeitzGeneration.card_map_congr e E).trans hcard
  have hle : E ≤ (MulAut.conj : K →* MulAut K).range := fun φ hφ =>
    MonoidHom.mem_range.mpr ((hinner φ hφ).imp fun g hg => hg.symm)
  have hle' : E.map (MulAut.congr e).toMonoidHom ≤
      (MulAut.conj : C0 σ →* MulAut (C0 σ)).range :=
    (Subgroup.map_mono (f := (MulAut.congr e).toMonoidHom) hle).trans
      (CFSG.LieType.SeitzGeneration.map_range_conj_congr e).le
  have hinner' : ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g : C0 σ, φ = MulAut.conj g :=
    fun φ hφ => (MonoidHom.mem_range.mp (hle' hφ)).imp fun g hg => hg.symm
  refine (planeGen_iff_closure_fixUnion E).mp (planeGen_of_outer_model e ?_)
  rw [planeGen_iff_closure_fixUnion]
  exact h q.exponent hge X σ hcardX hσ (E.map (MulAut.congr e).toMonoidHom) hE' hcard' hinner'

end BridgeBigInner

section AssemblyInner

variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem inner_descent (n : ℕ) (hn : 1 ≤ n) (hX : Nat.card X = (2 ^ n) ^ 3)
    (hσ : ∀ c : X, σ c = c ^ (2 ^ n)) (E : Subgroup (MulAut (C0 σ)))
    (hE : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hin : ∀ φ ∈ E, ∃ g : C0 σ, φ = MulAut.conj g) :
    ∃ E₀ : Subgroup (C0 σ), CFSG.IsElementaryAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ 2 ∧
      E = E₀.map (MulAut.conj : C0 σ →* MulAut (C0 σ)) := by
  have hinj := conj_injective_C0 σ n hn hX hσ
  have hle : E ≤ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range := fun φ hφ =>
    MonoidHom.mem_range.mpr ((hin φ hφ).imp fun g hg => hg.symm)
  have hEq : E = (E.comap (MulAut.conj : C0 σ →* MulAut (C0 σ))).map
      (MulAut.conj : C0 σ →* MulAut (C0 σ)) := (Subgroup.map_comap_eq_self hle).symm
  refine ⟨E.comap (MulAut.conj : C0 σ →* MulAut (C0 σ)), ?_, ?_, hEq⟩
  · refine isElementaryAbelian_three_of ?_ ?_
    · intro x hx y hy
      apply hinj
      rw [map_mul, map_mul]
      exact elemAb_comm hE _ hx _ hy
    · intro x hx
      apply hinj
      rw [map_pow, map_one]
      exact elemAb_cube hE _ hx
  · rw [← hcard]
    conv_rhs => rw [hEq]
    exact (Subgroup.card_map_of_injective hinj).symm

theorem trialityThreeInnerModelBig_holds (hgold : CFSG.Goldschmidt.TopStatement) :
    TrialityThreeInnerModelBig := by
  intro n hn X _ _ σ hX hσ E hE hcard hinner
  classical
  have hD : D4Par n X σ := ⟨by omega, hX, hσ⟩
  have hAB := trialityABFacts_of_par hgold hD hn
  have hR1 := trialityR1Facts_of_par hgold hD
  have hk4 := hD.four_le_card_fix hn
  haveI : Finite (C0 σ) := finite_C0
  rw [← planeGen_iff_closure_fixUnion]
  obtain ⟨E₀, hE₀, hc₀, rfl⟩ := inner_descent σ n (by omega) hX hσ E hE hcard hinner
  by_cases hY : ∃ y ∈ E₀, y ≠ 1 ∧ ∃ g : C0 σ, g * y * g⁻¹ ∈ Bsub σ
  · obtain ⟨y, hyE, hy1, hyB⟩ := hY
    obtain ⟨g, a, b, ha, hb, ha3, hb3, ha1, hb1, hmap⟩ :=
      inner_Y_case σ hAB n hn hX hσ hE₀ hc₀ hyE (elemAb_cube hE₀ y hyE) hy1 hyB
    refine (planeGen_map_congr (MulAut.conj g) _).mp ?_
    rw [map_congr_conj_map, hmap, map_conj_closure_pair]
    exact hR1.Eb hk4 ha hb ha3 hb3 ha1 hb1
  · have hall : ∀ y ∈ E₀, y ≠ 1 → IsClassX σ y := by
      intro y hy hy1
      rcases three_conj_dichotomy σ n (by omega) hX hσ (elemAb_cube hE₀ y hy) hy1 with h | h
      · exact h
      · exact absurd ⟨y, hy, hy1, h⟩ hY
    obtain ⟨x₁, hx₁E, hx₁1⟩ : ∃ x₁ ∈ E₀, x₁ ≠ 1 := by
      by_contra hcon
      have hbot : E₀ = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        by_contra hx1
        exact hcon ⟨x, hx, hx1⟩
      rw [hbot, Subgroup.card_bot] at hc₀
      omega
    have hx₁3 : x₁ ^ 3 = 1 := elemAb_cube hE₀ x₁ hx₁E
    obtain ⟨x₂, hx₂E, hx₂n⟩ : ∃ x₂ ∈ E₀, x₂ ∉ Subgroup.zpowers x₁ := by
      by_contra hcon
      have hle : E₀ ≤ Subgroup.zpowers x₁ := fun y hy => by
        by_contra hyn
        exact hcon ⟨y, hy, hyn⟩
      have h1 := Subgroup.card_le_of_le hle
      rw [card_zpowers_of_cube_one hx₁3 hx₁1, hc₀] at h1
      omega
    have hx₂1 : x₂ ≠ 1 := fun h => hx₂n (h ▸ Subgroup.one_mem _)
    refine planeGen_of_two_X_lines σ n hn hX hσ (hall x₁ hx₁E hx₁1) (hall x₂ hx₂E hx₂1)
      (elemAb_comm hE₀ x₁ hx₁E x₂ hx₂E) (fun h => hx₂n (h ▸ Subgroup.mem_zpowers x₂))
      (Subgroup.mem_map_of_mem _ hx₁E) (Subgroup.mem_map_of_mem _ hx₂E)

theorem trialityThreeInner_of_pieces (hgold : CFSG.Goldschmidt.TopStatement)
    (h1 : TrialityThreeInnerTwo) : TrialityThreeInner :=
  trialityThreeInner_of_split h1
    (trialityThreeInnerBig_of_model (trialityThreeInnerModelBig_holds hgold))

end AssemblyInner

end CFSG.RankThree.PartTwo.Sec19
