module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Extra
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Schur
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Sections

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

theorem _root_.CFSG.SignalizerFunctorTheorem.McBride.NearSimple.outer_perfect_le_inner
    {p : ℕ} {X : Type*} [Group X] [Finite X] (h : NearSimple p X) (P : Subgroup (MulAut X))
    (hP : Group.IsPerfect P) : P ≤ (MulAut.conj : X →* MulAut X).range :=
  NearSimple.outer_perfect_le_inner' h P hP

theorem _root_.CFSG.SignalizerFunctorTheorem.McBride.NearSimple.outer_coprime_pow_six_mem_inner
    {p : ℕ} {X : Type*} [Group X] [Finite X] (h : NearSimple p X) (g : MulAut X)
    (hg : Nat.Coprime p (orderOf g)) : g ^ 6 ∈ (MulAut.conj : X →* MulAut X).range :=
  NearSimple.outer_coprime_pow_six_mem_inner' h g hg

theorem hypC_of_nearPSolvable
    {p : ℕ} (hp : p.Prime) {H : Type u} [Group H] [Finite H]
    (h : signalizerNearPSolvable p H) : HypC H := by
  intro K L hLK _ hsimple hnonab
  have hQsec : IsSectionOf (K ⧸ L.subgroupOf K) H :=
    (IsSectionOf.of_surjective (QuotientGroup.mk' (L.subgroupOf K))
      (QuotientGroup.mk'_surjective _)).trans (IsSectionOf.of_subgroup K)
  obtain ⟨hcop, hmodel⟩ := signalizerNearPSolvable_iff.mp h
  have hdvd : Nat.card (K ⧸ L.subgroupOf K) ∣ Nat.card H := by
    obtain ⟨K', f, hf⟩ := hQsec
    exact (Subgroup.card_dvd_of_surjective hf).trans (Subgroup.card_subgroup_dvd_card K')
  have hQnear : signalizerNearPSolvable p (K ⧸ L.subgroupOf K) :=
    signalizerNearPSolvable_iff.mpr ⟨hcop.coprime_dvd_right hdvd,
      fun S _ _ hS hnc => hmodel S (hS.trans hQsec) hnc⟩
  have hNS : NearSimple p (K ⧸ L.subgroupOf K) := ⟨hp, hsimple, hnonab, hQnear⟩
  refine ⟨hsimple, hnonab, fun X _ hX hnot => ?_⟩
  exact absurd (NearSimple.outer_perfect_le_inner hNS X hX) hnot

theorem _root_.CFSG.SignalizerFunctorTheorem.McBride.NearSimple.exists_prime_overgroup_C₁
    {p : ℕ} {X : Type*} [Group X] [Finite X] (h : NearSimple p X) {f : MulAut X}
    (hf : orderOf f = p) :
    ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card X ∧ ¬ r ∣ Nat.card (fixedNormalizer f) ∧
      ∀ Y : Subgroup X, fixedCore1 f ≤ Y → (∃ y ∈ Y, orderOf y = r) → Y = ⊤ :=
  NearSimple.exists_prime_overgroup_C₁' h hf

theorem schur_multiplier_input
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    {Y : Type*} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (hLc : L ≤ Subgroup.center Y) (hLr : IsPGroup r L) (hL1 : L ≠ ⊥)
    (hY : Group.IsPerfect Y) (hss : IsSemisimple (⊤ : Subgroup (Y ⧸ L)))
    (hnear : signalizerNearPSolvable p (Y ⧸ L)) :
    ∃ J ∈ lcalOf (Y ⧸ L),
      (r = 2 ∧ (Nonempty (↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)) ∨
        (p = 3 ∧ Nonempty (↥J ≃* Sz 1)))) ∨
      (r = 3 ∧ Nonempty (↥J ≃* PSU3 2 p)) :=
  schur_multiplier_input' hp hp2 hr L hLc hLr hL1 hY hss hnear

end CFSG.SignalizerFunctorTheorem.McBride.Near
