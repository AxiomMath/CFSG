module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeLabels

public section

namespace CFSG.StandardType.SmallU

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem actsDiagU_exists_units {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t) :
    ∃ (σ : Fin d → Kˣ) (hD : diagHom d σ ∈
        Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
      (∀ k, ((σ k : Kˣ) : K) = t k) ∧
        ∀ s : ↥(unitarySU 2 n K d), a (φ s) = φ (conjN (diagHom d σ) hD s) := by
  obtain ⟨D, hD, hDt, hact⟩ := ha
  have h0 : ∀ k, t k ≠ 0 := fun k => diag_ne_zero_of_eq hDt k
  set σ : Fin d → Kˣ := fun k => Units.mk0 (t k) (h0 k) with hσ
  have hDσ : D = diagHom d σ := by
    apply Units.ext
    rw [hDt, coe_diagHom]
    rfl
  subst hDσ
  exact ⟨σ, hD, fun k => rfl, hact⟩

theorem exists_nu (hM : Model φ) (hd : 3 ≤ d) {A : Subgroup (MulAut L')}
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) (s₀ : Fin d) :
    ∃ ν : A →* (Fin d → Kˣ), ∀ a : A,
      ActsDiagU φ (a : MulAut L') (fun k => ((ν a k : Kˣ) : K)) ∧ ν a s₀ = 1 := by
  classical
  have hex : ∀ a : A, ∃ t : Fin d → K, ActsDiagU φ (a : MulAut L') t ∧ t s₀ = 1 := by
    intro a
    obtain ⟨t, ht⟩ := hdiag a a.2
    have h0 := ht.ne_zero s₀
    refine ⟨fun k => t k * (t s₀)⁻¹, actsDiagU_mul_const ht (inv_ne_zero h0), ?_⟩
    exact mul_inv_cancel₀ h0
  choose tn htn using hex
  have hun : ∀ (a : MulAut L') (t u : Fin d → K), ActsDiagU φ a t → ActsDiagU φ a u →
      t s₀ = u s₀ → t = u := by
    intro a t u ht hu hs
    funext k
    have h := ActsDiagU.ratio_eq hM.field hd hM.ker ht hu k s₀
    rw [hs] at h
    exact mul_right_cancel₀ (inv_ne_zero (hu.ne_zero s₀)) h
  have hne : ∀ (a : A) (k : Fin d), tn a k ≠ 0 := fun a k => (htn a).1.ne_zero k
  have hone : tn 1 = fun _ => 1 :=
    hun _ _ _ (htn 1).1 (actsDiagU_one φ) (by rw [(htn 1).2])
  have hmul : ∀ a b : A, tn (a * b) = fun k => tn a k * tn b k := by
    intro a b
    refine hun _ _ _ (htn (a * b)).1 (actsDiagU_mul (htn a).1 (htn b).1) ?_
    rw [(htn (a * b)).2, (htn a).2, (htn b).2, mul_one]
  refine ⟨{ toFun := fun a k => Units.mk0 (tn a k) (hne a k)
            map_one' := ?_
            map_mul' := ?_ }, fun a => ⟨?_, ?_⟩⟩
  · funext k
    apply Units.ext
    show tn 1 k = 1
    rw [hone]
  · intro a b
    funext k
    apply Units.ext
    show tn (a * b) k = tn a k * tn b k
    rw [hmul]
  · exact (htn a).1
  · apply Units.ext
    exact (htn a).2

end CFSG.StandardType.SmallU

end
