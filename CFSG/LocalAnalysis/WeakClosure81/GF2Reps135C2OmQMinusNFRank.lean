module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFRankHyp
public import CFSG.RankThree.OrthogonalInvolutions.Basic
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusModel
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.BorelTits.Families

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.StandardType
open CFSG.RankThree.OrthogonalInvolutions

private theorem omqnfrk_refl_sub {K : Type*} [Field K] [CharP K 2] {b c : K}
    (p : Fin 2 → K) : planeRefl b c planeOne p - p = (b * p 1) • planeOne := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  funext i
  fin_cases i
  · simp [planeRefl, polarPlane, planeNorm, planeOne, h2, Matrix.vecHead]
    exact CharTwo.neg_eq _
  · simp [planeRefl, polarPlane, planeNorm, planeOne, h2, Matrix.vecHead, Matrix.vecTail]

theorem omqnf_finrank_map_plane {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} {T : Vm n K ≃ₗ[K] Vm n K} (h : omqnfActs n b c π s T) :
    Module.finrank K
        (Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfPlane n K)) =
      if ∏ a, s a = 1 then 0 else 1 := by
  have hb : b ≠ 0 := CFSG.StandardType.GGOppRadOmega.b_ne_zero hirr
  by_cases hp : ∏ a, s a = 1
  · rw [if_pos hp]
    have hbot : Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfPlane n K) = ⊥ := by
      rw [omqnfPlane, Submodule.map_span, Submodule.span_eq_bot]
      rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
      simp [h.2 p, hp]
    rw [hbot, finrank_bot]
  · rw [if_neg hp]
    have key : ∀ p, ((T : Vm n K →ₗ[K] Vm n K) - 1) (planeVec n p) =
        (b * p 1) • planeVec n (planeOne : Fin 2 → K) := by
      intro p
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, h.2 p, if_neg hp, Module.End.one_apply]
      rw [← planeVec_sub, omqnfrk_refl_sub, planeVec_smul]
    have himg : Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfPlane n K) =
        Submodule.span K {planeVec n (planeOne : Fin 2 → K)} := by
      apply le_antisymm
      · rw [omqnfPlane, Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
        rw [key]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · rw [Submodule.span_le]
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        refine ⟨planeVec n (Pi.single 1 (b⁻¹)), Submodule.subset_span ⟨_, rfl⟩, ?_⟩
        rw [key]
        simp [hb]
    rw [himg, finrank_span_singleton]
    intro h0
    have := congrFun h0 (.inr (.inr 0))
    simp [planeVec, planeOne] at this

theorem omqnf_finrank_commSpace {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} {T : Vm n K ≃ₗ[K] Vm n K} (h : omqnfActs n b c π s T)
    (hσ : spMonoPerm π s * spMonoPerm π s = 1) :
    Module.finrank K (commSpace T) =
      (spMonoPerm π s).support.card / 2 + if ∏ a, s a = 1 then 0 else 1 := by
  rw [← omqnf_finrank_map_hyp h hσ, ← omqnf_finrank_map_plane hirr h]
  have hsup : omqnfHyp n K ⊔ omqnfPlane n K = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).span_eq,
      Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    rcases j with a | a | t
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨Sum.inr a, rfl⟩)
    · refine Submodule.mem_sup_right (Submodule.subset_span ⟨Pi.single t 1, ?_⟩)
      funext a
      rcases a with i | i | s <;> simp [planeVec, Pi.single_apply, Sum.inr.injEq]
  have hcs : commSpace T = Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfHyp n K) ⊔
      Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfPlane n K) := by
    rw [commSpace, LinearMap.range_eq_map, ← hsup, Submodule.map_sup]
  have hH : ∀ v ∈ omqnfHyp n K, ∀ t, v (.inr (.inr t)) = 0 := by
    intro v hv t
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, rfl⟩ := hy
      rcases x with a | a <;> simp [omqnfFrame, eVec, fVec, Pi.single_apply]
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul r y _ hy => simp [hy]
  have hP : ∀ v ∈ omqnfPlane n K, (∀ a, v (.inl a) = 0) ∧ ∀ a, v (.inr (.inl a)) = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      exact ⟨fun a => by simp [planeVec], fun a => by simp [planeVec]⟩
    | zero => exact ⟨fun a => rfl, fun a => rfl⟩
    | add y z _ _ hy hz =>
      exact ⟨fun a => by simp [hy.1 a, hz.1 a], fun a => by simp [hy.2 a, hz.2 a]⟩
    | smul r y _ hy => exact ⟨fun a => by simp [hy.1 a], fun a => by simp [hy.2 a]⟩
  have himH : Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfHyp n K) ≤ omqnfHyp n K := by
    rw [omqnfHyp, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, h.1 x, Module.End.one_apply]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
  have himP : Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfPlane n K) ≤
      omqnfPlane n K := by
    rw [omqnfPlane, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, h.2 p, Module.End.one_apply]
    rw [← planeVec_sub]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hdis : Disjoint (omqnfHyp n K) (omqnfPlane n K) := by
    rw [Submodule.disjoint_def]
    intro v hvH hvP
    funext x
    rcases x with a | a | t
    · exact (hP v hvP).1 a
    · exact (hP v hvP).2 a
    · exact hH v hvH t
  have hdis' := hdis.mono himH himP
  rw [hcs]
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfHyp n K))
    (Submodule.map ((T : Vm n K →ₗ[K] Vm n K) - 1) (omqnfPlane n K))
  rw [hdis'.eq_bot, finrank_bot] at hfin
  omega

end CFSG.LocalAnalysis.WeakClosure81
