module

public import CFSG.RankThree.PartOne.S15K.BlockModel
public import CFSG.RankThree.PartOne.S15K.ThetaLayer

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow QuadraticMap

theorem eq_of_isComponent_le {Γ : Type*} [Group Γ] [Finite Γ] {N C L : Subgroup Γ} (hCN : C ≤ N)
    (hLN : L ≤ N) (hC : IsComponent (C.subgroupOf N)) (hL : IsComponent (L.subgroupOf N))
    (hCL : C ≤ L) : C = L := by
  rcases eq_or_commutator_eq_bot_of_components hCN hLN hC hL with h | h
  · exact h
  · exfalso
    have hq : IsQuasisimple ↥C := by
      have := hC.1
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCN) this
    have hperf : ⁅C, C⁆ = C := (Subgroup.isPerfect_iff).1 hq.1
    have hle : ⁅C, C⁆ ≤ ⁅C, L⁆ := Subgroup.commutator_mono le_rfl hCL
    rw [h, le_bot_iff, hperf] at hle
    exact ne_bot_of_isQuasisimple hq hle

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p f : ℕ} {x : V ≃ₗ[K] V}

theorem blockModel_fixedLayer_component (hQ : (polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q p x) (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hW : ¬ IsPlusType (Q.comp (fixedSpace x).subtype)) (hW6 : finrank K (fixedSpace x) ≤ 6)
    {n : ℕ} {C : Fin n → Subgroup (ProjOrthDerived Q)}
    (hCsup : (⨆ i, C i) = fixedLayerImage Q x)
    (hC : ∀ i, CFSG.IsQuasisimple ↥(C i) ∧ C i ≤ centralizerImage Q x ∧
      ((C i).subgroupOf (centralizerImage Q x)).IsSubnormal) (i : Fin n) :
    BlockModel p ↥(C i) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hCi := hC i
  have hnb : C i ≠ ⊥ := ne_bot_of_isQuasisimple hCi.1
  have hlist : FixedLayerListed Q x := by
    by_contra hnl
    apply hnb
    have h0 : fixedLayerImage Q x = ⊥ := by simp [fixedLayerImage, hnl]
    rw [eq_bot_iff, ← h0, ← hCsup]
    exact le_iSup C i
  have hL : fixedLayerImage Q x = fixedComponentImage Q x := fixedLayerImage_of_listed hlist
  obtain ⟨m, hm⟩ := hx.even_finrank_fixed
  have h3 := hlist.1
  have hd : finrank K (fixedSpace x) = 4 ∨ finrank K (fixedSpace x) = 6 := by omega
  have hts : ∀ U : Submodule K (fixedSpace x), finrank K U = finrank K (fixedSpace x) / 2 →
      ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    exact hW ⟨U, by omega, hcon⟩
  have hWnd := hx.polarBilin_fixed_nondegenerate
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K)
    (lt_of_lt_of_le (by omega) (Submodule.finrank_le (fixedSpace x)))
  let φ₁ := fixedComponentImageEquiv hQ hx
  obtain ⟨hqL, -⟩ := nonsplit_quasisimple_dicksonDerived (Q.comp (fixedSpace x).subtype) hWnd hd hts
  have hLq : CFSG.IsQuasisimple ↥(fixedComponentImage Q x) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ₁.symm hqL
  have hLN : fixedComponentImage Q x ≤ centralizerImage Q x := fixedComponentImage_le_centralizerImage
  have hLsub := hx.normal_fixedComponentImage.isSubnormal
  have hLc : IsComponent ((fixedComponentImage Q x).subgroupOf (centralizerImage Q x)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN).symm hLq, hLsub⟩
  have hCc : IsComponent ((C i).subgroupOf (centralizerImage Q x)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCi.2.1).symm hCi.1,
      hCi.2.2⟩
  have hCiL : C i ≤ fixedComponentImage Q x := by
    rw [← hL, ← hCsup]
    exact le_iSup C i
  have hEq : C i = fixedComponentImage Q x :=
    eq_of_isComponent_le hCi.2.1 hLN hCc hLc hCiL
  exact ⟨f, K, inferInstance, inferInstance, inferInstance, hK, hf, hpq,
    Or.inr (Or.inr ⟨↥(fixedSpace x), inferInstance, inferInstance, inferInstance,
      Q.comp (fixedSpace x).subtype, hWnd, hd, hts, ⟨(MulEquiv.subgroupCongr hEq).trans φ₁⟩⟩)⟩

end CFSG.RankThree.PartOne.S15K
