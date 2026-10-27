module

public import CFSG.Quasithin.Background.C1PackS14612One
public import CFSG.Quasithin.EmptyFaithful.S14612DA
public import CFSG.Quasithin.EmptyFaithful.S146R7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Shape

variable {G : Type} [Group G]

@[expose] def IsE9Z4Shape (T H : Subgroup G) (p : ℕ) : Prop :=
  p = 3 ∧ (pCoreOf 2 H).relIndex T = 4

end Shape

@[expose] def Stage14612Class : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      (∃ H₀ H₁ H₂ : Subgroup G, ∃ t : G, IsDecP T M H p H₀ H₁ H₂ t) ∨ IsE9Z4Shape T H p

@[expose] def NoE9Z4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p → ¬ IsE9Z4Shape T H p

@[expose] def Stage14612PartP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      (p = 3 ∨ p = 5) ∧ ∃ H₀ H₁ H₂ : Subgroup G, ∃ t : G, IsDecP T M H p H₀ H₁ H₂ t

theorem stage14612PartP_of_class (hc : Stage14612Class) (hN : NoE9Z4) : Stage14612PartP := by
  intro G _ _ T M S H PQ p hred hmax
  refine ⟨S.p_eq_three_or_five_of_isRedCE hred, ?_⟩
  rcases hc G T M S H PQ p hred with hdec | hshape
  · exact hdec
  · exact absurd hshape (hN G T M S H PQ p hred hmax)

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Z_le_commutator_of_isDecP (h5 : Stage1461Five) (S : Setting146 G T M) {H PQ : Subgroup G}
    {p : ℕ} (hred : IsRedCE T M H PQ p) {H₀ H₁ H₂ : Subgroup G} {t : G}
    (hdec : IsDecP T M H p H₀ H₁ H₂ t) :
    quasithinOmegaOneCenter T ≤ ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ∧
      quasithinOmegaOneCenter T ≤ ⁅conjClosure (VZ T M) H, oTwoUpper H₂⁆ := by
  have hH : IsHTM T M H := hred.isHTM
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have key : ∀ Hi : Subgroup G, Hi ≤ H → pCoreOf 2 H ≤ Hi →
      (∃ z ∈ Hi, z ∉ pCoreOf 2 H ∧ Odd (orderOf z)) →
      quasithinOmegaOneCenter T ≤ ⁅conjClosure (VZ T M) H, oTwoUpper Hi⁆ := by
    rintro Hi hHiH hQHi ⟨z, hz1, hzQ, hzodd⟩
    have hX1 : oTwoUpper Hi ≠ ⊥ := by
      intro hbot
      have hzX : z ∈ oTwoUpper Hi := mem_oTwoUpper_of_odd hz1 hzodd
      rw [hbot, Subgroup.mem_bot] at hzX
      exact hzQ (hzX ▸ (pCoreOf 2 H).one_mem)
    have hXF : oTwoUpper Hi ≤ oTwoFstarIn H :=
      (((oTwoUpper_mono hHiH).trans (hred.oTwoUpper_le_pq hT2)).trans hred.le_oTwoPIn).trans
        (oTwoPIn_le_oTwoFstarIn hred.prime H)
    exact S.lemma_14_6_2 hH (h5 G T M S H hH) hX1 (S146A.oTwoUpper_idem Hi) hXF
      (hQHi.trans (le_normalizer_oTwoUpper Hi))
  exact ⟨key H₁ (hdec.le₁.trans hdec.le) hdec.Q₁
      (exists_odd_of_secIso_dihedral hred.prime hred.odd hdec.dihedral₁),
    key H₂ (hdec.le₂.trans hdec.le) hdec.Q₂
      (exists_odd_of_secIso_dihedral hred.prime hred.odd hdec.dihedral₂)⟩

end CFSG.Quasithin
