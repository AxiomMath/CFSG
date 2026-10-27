module

public import CFSG.RankThree.PartOne.D4RC.GeoFlag

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ7 CFSG.Timmesfeld.ARS

variable {K : Type} [Field K] {σ : K →+* K}

theorem rcf_not_commuting_of_opposite {G : Type*} [Group G] {A B : Subgroup G} (hA : A ≠ ⊥)
    (h : Opposite A B) : ¬ Commuting A B := by
  intro hc
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA
  obtain ⟨b, hb, -, hab⟩ := h.2.1 a a.2 fun e => ha (Subtype.ext e)
  have h1 : conjSub A b = A :=
    conjSub_of_mem_normalizer (le_normalizer_of_commute (fun x hx y hy => (hc y hy x hx).symm) hb)
  have h2 : conjSub B a = B :=
    conjSub_of_mem_normalizer (le_normalizer_of_commute hc a.2)
  exact h.1 (h1.symm.trans (hab.trans h2))

section Fixed

variable [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) [Finite (twistedGroup σ)]
  [IsSimpleGroup (twistedGroup σ)] {q : ℕ} (hK : Nat.card K = q ^ 3) {p : ℕ} (hp : p.Prime)
  (hpq : p ∣ q ^ 2 - q + 1)
include hσ hK hp hpq

theorem rcf_opposite_of_fixed {y : twistedGroup σ} (hy : orderOf y = p)
    {A B : Subgroup (twistedGroup σ)} (hA : A ∈ longClass σ) (hB : B ∈ longClass σ)
    (hne : A ≠ B) (hyA : conjSub A y = A) (hyB : conjSub B y = B) : Opposite A B := by
  have h := rcg_hyp hσ
  have hH := rcg_sigmaEqLambda hσ
  rcases rcg_long_pair_dichotomy hσ hA hB hne with hc | ho | hs
  · exfalso
    apply rcg_lfpf hσ hK hp hpq hy hA hyA (CaseH.mem_lambdaSet_of_commuting hH hA hB hne.symm hc)
    rw [rcg_conjSub_sup, hyA, hyB]
  · exact ho
  · exfalso
    apply rcg_lfpf hσ hK hp hpq hy hA hyA (CaseH.commutator_mem_lambdaSet h hA hB hs).1
    rw [rcg_conjSub_sup, hyA, Timmesfeld.ARS.conjSub, Subgroup.map_commutator]
    change A ⊔ ⁅conjSub A y, conjSub B y⁆ = A ⊔ ⁅A, B⁆
    rw [hyA, hyB]

theorem rcf_not_commuting {y z : twistedGroup σ} (hy : orderOf y = p) (hz : orderOf z = p)
    (hyz : Commute y z) {A B : Subgroup (twistedGroup σ)} (hA : A ∈ longClass σ)
    (hB : B ∈ longClass σ) (hne : A ≠ B) (hyA : conjSub A y = A) (hzB : conjSub B z = B) :
    ¬ Commuting A B := by
  intro hc
  have h := rcg_hyp hσ
  have hH := rcg_sigmaEqLambda hσ
  have hA0 := rcg_ne_bot hσ hA
  have hBΛ := CaseH.mem_lambdaSet_of_commuting hH hA hB hne.symm hc
  by_cases hzA : conjSub A z = A
  · exact rcf_not_commuting_of_opposite hA0
      (rcf_opposite_of_fixed hσ hK hp hpq hz hA hB hne hzA hzB) hc
  set A' := conjSub A z with hA'def
  have hA' : A' ∈ longClass σ := rcg_conjSub_mem hA z
  have hyA' : conjSub A' y = A' := by
    rw [hA'def, ← conjSub_mul, hyz.eq, conjSub_mul, hyA]
  have hop : Opposite A A' := rcf_opposite_of_fixed hσ hK hp hpq hy hA hA' (Ne.symm hzA) hyA hyA'
  have hcB : Commuting A' B := by
    have := rcg_commuting_conj hc z
    rwa [hzB] at this
  have hne' : A' ≠ B := by
    intro e
    have hyB : conjSub B y = B := e ▸ hyA'
    exact rcf_not_commuting_of_opposite hA0
      (rcf_opposite_of_fixed hσ hK hp hpq hy hA hB hne hyA hyB) hc
  exact CaseH.notMem_lambdaSet_of_opposite h hA hop hBΛ
    (CaseH.mem_lambdaSet_of_commuting hH hA' hB hne'.symm hcB)

theorem rcf_special_of_not_opposite {y z : twistedGroup σ} (hy : orderOf y = p)
    (hz : orderOf z = p) (hyz : Commute y z) {A B : Subgroup (twistedGroup σ)}
    (hA : A ∈ longClass σ) (hB : B ∈ longClass σ) (hne : A ≠ B) (hyA : conjSub A y = A)
    (hzB : conjSub B z = B) (hno : ¬ Opposite A B) : Special (longClass σ) A B := by
  rcases rcg_long_pair_dichotomy hσ hA hB hne with hc | ho | hs
  · exact absurd hc (rcf_not_commuting hσ hK hp hpq hy hz hyz hA hB hne hyA hzB)
  · exact absurd ho hno
  · exact hs

end Fixed

end CFSG.RankThree.PartOne.D4RC
