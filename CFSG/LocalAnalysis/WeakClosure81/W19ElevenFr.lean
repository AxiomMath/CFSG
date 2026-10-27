module

public import CFSG.Quasithin.Background.GoldschmidtE1Transfer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.W19Conf
public import CFSG.LocalAnalysis.WeakClosure81.W19Four
public import CFSG.LocalAnalysis.WeakClosure81.W19KSeries

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_inf_aux {x : G} {P Q : Subgroup G}
    (hP : x ∈ normalizer (P : Set G)) (hQ : x ∈ normalizer (Q : Set G)) :
    x ∈ normalizer ((P ⊓ Q : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.1 hP y,
    Subgroup.mem_normalizer_iff.1 hQ y]

private theorem conjSub_inv_eq_conjSubgroup (t : G) (A : Subgroup G) :
    A1b.conjSub t⁻¹ A = conjSubgroup A t := by
  ext x
  rw [A1b.mem_conjSub_iff, mem_conjSubgroup_iff]
  simp

namespace Conf196

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G} {g : G} {K : Subgroup G}

theorem conj_T (hc : Conf196 D V X g K) {t : G} (ht : t ∈ D.T) :
    Conf196 D V X (g * t) (conjSubgroup K t) := by
  have hTH : D.T ≤ X ⊔ D.T := le_sup_right
  refine ⟨?_, ?_⟩
  · rw [← conjSubgroup_conjSubgroup]
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have e : x = t⁻¹ * (t * x * t⁻¹) * t := by group
    rw [e]
    exact D.T.mul_mem (D.T.mul_mem (D.T.inv_mem ht) (hc.le_T hx)) ht
  · have h := E1.isE_conj_of_mem hTH (D.T.inv_mem ht) hc.isE
    rwa [conjSub_inv_eq_conjSubgroup, conjSub_inv_eq_conjSubgroup,
      conjSubgroup_conjSubgroup] at h

theorem inf_sup_pCoreOf_le (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    K ⊓ (X ⊔ pCoreOf 2 (X ⊔ D.T)) ≤ (X ⊓ K) ⊔ pCoreOf 2 (X ⊔ D.T) := by
  set Q := pCoreOf 2 (X ⊔ D.T) with hQ
  have hXQ : X ≤ normalizer (Q : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  intro k hk
  have hkN : k ∈ X ⊔ Q := hk.2
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right X Q hXQ] at hkN
  obtain ⟨x, hx, q, hq, rfl⟩ := hkN
  have hqK : q ∈ K := hc.pCoreOf_le_K c hq
  have hxK : x ∈ K := by
    have := K.mul_mem hk.1 (K.inv_mem hqK)
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hx, hxK⟩) (Subgroup.mem_sup_right hq)

theorem le_inf_sup_T (c : MinCex193 D V₀ V p X) (hc : Conf196 D V X g K) :
    K ≤ (X ⊓ K) ⊔ D.T := by
  set Q := pCoreOf 2 (X ⊔ D.T) with hQ
  set N : Subgroup G := X ⊔ Q with hN
  have hHN : X ⊔ D.T ≤ normalizer (N : Set G) := c.le_normalizer_sup_pCoreOf
  have hQT : Q ≤ D.T := Hyp193.pCoreOf_le_T c.hyp
  have hHeq : X ⊔ D.T = D.T ⊔ N :=
    le_antisymm (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
      (sup_le le_sup_right (sup_le le_sup_left (hQT.trans le_sup_right)))
  have hTN : D.T ≤ normalizer (N : Set G) := le_sup_right.trans hHN
  have hKN : K ≤ normalizer ((K ⊓ N : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_inf_aux (Subgroup.le_normalizer hk) (hHN (hc.le_H hk))
  have h2 : ∀ y ∈ K, ∃ k : ℕ, y ^ 2 ^ k ∈ K ⊓ N := by
    intro y hy
    have hyH : y ∈ D.T ⊔ N := hHeq ▸ hc.le_H hy
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_pGroup c.hyp.isSylowIn_T.isPGroup hTN hyH
    exact ⟨k, Subgroup.mem_inf.2 ⟨K.pow_mem hy _, hk⟩⟩
  have hres : twoResidual K ≤ K ⊓ N := twoResidual_le_of_isTwoQuotient inf_le_left hKN h2
  have hsup : (D.T ⊓ K) ⊔ twoResidual K = K := sup_twoResidual_eq hc.isE.2.2.1
  have hded : K ⊓ N ≤ (X ⊓ K) ⊔ Q := hc.inf_sup_pCoreOf_le c
  calc K = (D.T ⊓ K) ⊔ twoResidual K := hsup.symm
    _ ≤ D.T ⊔ ((X ⊓ K) ⊔ Q) := sup_le_sup inf_le_left (hres.trans hded)
    _ ≤ (X ⊓ K) ⊔ D.T := sup_le le_sup_right (sup_le le_sup_left (hQT.trans le_sup_right))

end Conf196

end CFSG.LocalAnalysis.WeakClosure81

end
