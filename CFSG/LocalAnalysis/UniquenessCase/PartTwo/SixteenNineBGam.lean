module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_not_propC_of_fixed {M Z : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hM : IsStronglyPEmbedded p M) {z : G} (hz : z ∈ Z) (hz2 : orderOf z = 2)
    (hx : 1 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({z} : Set G))) : ¬ PropC M Z := by
  rintro ⟨g, hgM, hΓ⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : centralizer ({z} : Set G) ≤ conjSubgroup M g :=
    CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le hΓ hz hz2
  obtain ⟨x, hxmem, hxord⟩ := CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank hp hx
  have hxM : x ∈ M := hxmem.1
  have hxg : x ∈ conjSubgroup M g := hc hxmem.2
  have hgi : g⁻¹ ∉ M := fun h => hgM (by simpa using M.inv_mem h)
  have hmem : x ∈ M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom := ⟨hxM, hxg⟩
  have hdvd : p ∣ Nat.card (M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) := by
    rw [← hxord]
    exact Subgroup.orderOf_dvd_natCard _ hmem
  exact hM.2.2 g⁻¹ hgi hdvd

theorem s16n9b_commElt_le {V W : Subgroup G} (hWV : W ≤ V) {t : G}
    (ht : t ∈ normalizer (V : Set G)) : commElt W t ≤ V := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨w, hw, rfl⟩
  have h1 : t⁻¹ * w * t ∈ V := (Subgroup.mem_normalizer_iff''.1 ht w).1 (hWV hw)
  have h2 : w⁻¹ * t⁻¹ * w * t = w⁻¹ * (t⁻¹ * w * t) := by group
  rw [h2]
  exact V.mul_mem (V.inv_mem (hWV hw)) h1

theorem s16n9b_exists_commutator_ne_one {W : Subgroup G} {t : G}
    (h : ¬ W ≤ centralizer ({t} : Set G)) : ∃ w ∈ W, w⁻¹ * t⁻¹ * w * t ≠ 1 := by
  by_contra hne
  push Not at hne
  apply h
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h0 := hne w hw
  have h1 : t⁻¹ * w * t = w := by
    calc t⁻¹ * w * t = w * (w⁻¹ * t⁻¹ * w * t) := by group
      _ = w := by rw [h0, mul_one]
  calc w * t = t * (t⁻¹ * w * t) := by group
    _ = t * w := by rw [h1]

theorem s16n9b_lt_gammaN_of_good {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ normalizer (V : Set G)) {P : Set ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ IsStronglyPEmbedded p M) (n N : ℕ)
    (hgood : ∀ t ∈ M, (∃ a : ℕ, orderOf t = 2 ^ a) →
      E3.mQuot V (V ⊓ centralizer ({t} : Set G)) ≤ N →
      ∀ W : Subgroup G, W ≤ V → E3.mQuot V W ≤ n → ¬ W ≤ centralizer ({t} : Set G) →
        ∃ z ∈ commElt W t, z ≠ 1 ∧ ∃ p ∈ P, 1 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({z} : Set G))) :
    (N : ℕ∞) < gammaN n M V := by
  have hall : ∀ U ∈ calCn n M V, N + 1 ≤ E3.mQuot V U := by
    intro U hU
    obtain ⟨hUV, t, ⟨htM, htU⟩, ht2, W, hWV, hWn, hUW, hWt, hC⟩ := hU
    by_contra hlt
    have hlt' : E3.mQuot V U ≤ N := by omega
    have hUt : U ≤ V ⊓ centralizer ({t} : Set G) := by
      refine le_inf hUV fun u hu => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 htU u hu
    have hrank : E3.mQuot V (V ⊓ centralizer ({t} : Set G)) ≤ N :=
      (E3.mQuot_mono hUt).trans hlt'
    obtain ⟨z, hzmem, hz1, p, hpP, hpz⟩ := hgood t htM ht2 hrank W hWV hWn hWt
    have hzV : z ∈ V := s16n9b_commElt_le hWV (hMV htM) hzmem
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hz2 : orderOf z = 2 := orderOf_eq_prime (hV.2 z hzV) hz1
    exact s16n9b_not_propC_of_fixed (hP p hpP).1 (hP p hpP).2 hzmem hz2 hpz hC
  have hle : ((N + 1 : ℕ) : ℕ∞) ≤ gammaN n M V := by
    unfold gammaN
    refine le_iInf₂ fun U hU => ?_
    exact_mod_cast hall U hU
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self N) hle

theorem s16n9b_lt_gammaN_of_fixAll {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ normalizer (V : Set G)) {P : Set ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ IsStronglyPEmbedded p M) (n N : ℕ)
    (hfix : ∀ v ∈ V, v ≠ 1 →
      ∃ p ∈ P, 1 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({v} : Set G))) :
    (N : ℕ∞) < gammaN n M V := by
  refine s16n9b_lt_gammaN_of_good hV hMV hP n N ?_
  intro t htM _ _ W hWV _ hWt
  obtain ⟨w, hw, hne⟩ := s16n9b_exists_commutator_ne_one hWt
  have hmem : w⁻¹ * t⁻¹ * w * t ∈ commElt W t := Subgroup.subset_closure ⟨w, hw, rfl⟩
  have hzV : w⁻¹ * t⁻¹ * w * t ∈ V := s16n9b_commElt_le hWV (hMV htM) hmem
  exact ⟨_, hmem, hne, hfix _ hzV hne⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
