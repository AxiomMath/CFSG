module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport
public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthRat

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth QuadraticMap
open scoped Matrix

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_singular_of_exchange (Pa Pb : HypPair Q) (h : Pa.Orth Pb) (W : AddSubgroup V)
    (hW1 : ∀ x ∈ W, eichler Q Pa.e Pb.e x ∈ W) (hW2 : ∀ x ∈ W, eichler Q Pa.e Pb.f x ∈ W)
    {x : V} (hx : x ∈ W) (ha : polar Q x Pa.e ≠ 0) : ∃ u ∈ W, u ≠ 0 ∧ Q u = 0 := by
  set a := polar Q x Pa.e with ha_def
  set c := polar Q x Pb.e with hc_def
  have hz1 : eichler Q Pa.e Pb.e x - x = a • Pb.e - c • Pa.e := by
    rw [eichler_apply Pa.Q_e h.ee, Pb.Q_e]
    simp only [zero_mul, add_zero]
    module
  set z₁ := a • Pb.e - c • Pa.e with hz₁
  have hz₁W : z₁ ∈ W := by rw [← hz1]; exact W.sub_mem (hW1 x hx) hx
  have hpe : polar Q z₁ Pa.e = 0 := by
    rw [hz₁, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, polar_comm Q Pb.e Pa.e,
      h.ee, Pa.polar_ee]
    ring
  have hpf : polar Q z₁ Pb.f = a := by
    rw [hz₁, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, Pb.polar_ef, h.ef]
    ring
  have hz2 : eichler Q Pa.e Pb.f z₁ - z₁ = (-a) • Pa.e := by
    rw [eichler_apply Pa.Q_e h.ef, Pb.Q_f, hpe, hpf]
    simp only [zero_smul, mul_zero, add_zero]
    module
  have hz₂W : (-a) • Pa.e ∈ W := by rw [← hz2]; exact W.sub_mem (hW2 z₁ hz₁W) hz₁W
  refine ⟨(-a) • Pa.e, hz₂W, smul_ne_zero (neg_ne_zero.mpr ha) Pa.e_ne_zero, ?_⟩
  rw [QuadraticMap.map_smul, Pa.Q_e]
  simp

theorem exists_singular_of_perp (Pa : HypPair Q) (W : AddSubgroup V) {x : V} (hx : x ∈ W)
    (hxa : polar Q x Pa.e = 0) {w : V} (hw : w ∈ Pa.perp) (hE : eichler Q Pa.e w x ∈ W)
    (hxw : polar Q x w ≠ 0) : ∃ u ∈ W, u ≠ 0 ∧ Q u = 0 := by
  have hwe : polar Q Pa.e w = 0 := (HypPair.mem_perp.mp hw).1
  have h1 : eichler Q Pa.e w x - x = (-polar Q x w) • Pa.e := by
    rw [eichler_apply Pa.Q_e hwe, hxa]
    simp only [zero_smul, mul_zero, add_zero]
    module
  have h2 : (-polar Q x w) • Pa.e ∈ W := by rw [← h1]; exact W.sub_mem hE hx
  refine ⟨_, h2, smul_ne_zero (neg_ne_zero.mpr hxw) Pa.e_ne_zero, ?_⟩
  rw [QuadraticMap.map_smul, Pa.Q_e]
  simp

variable [FiniteDimensional K V]

theorem addSubgroup_eq_bot_or_top_of_elementaryGroup_invariant
    (hQ : (polarBilin Q).Nondegenerate)
    (hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j))
    (W : AddSubgroup V) (hW : ∀ g ∈ elementaryGroup Q, ∀ x ∈ W, g x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨P, hPorth⟩ := hP
  have hWe : ∀ u w : V, ∀ x ∈ W, eichler Q u w x ∈ W :=
    fun u w x hx => hW _ (eichler_mem_elementaryGroup Q u w) x hx
  have htwo : ∀ i : Fin 2, ∃ j : Fin 2, j ≠ i := by
    intro i
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
  have hsing : ∃ u ∈ W, u ≠ 0 ∧ Q u = 0 := by
    obtain ⟨⟨x, hxW⟩, hx0'⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hbot
    have hx0 : x ≠ 0 := fun h => hx0' (Subtype.ext h)
    by_cases hA : ∃ i : Fin 2, polar Q x (P i).e ≠ 0
    · obtain ⟨i, hi⟩ := hA
      obtain ⟨j, hji⟩ := htwo i
      exact exists_singular_of_exchange (P i) (P j) (hPorth i j (Ne.symm hji)) W (hWe _ _)
        (hWe _ _) hxW hi
    by_cases hB : ∃ i : Fin 2, polar Q x (P i).f ≠ 0
    · obtain ⟨i, hi⟩ := hB
      obtain ⟨j, hji⟩ := htwo i
      exact exists_singular_of_exchange (swapPair (P i)) (P j)
        (orth_swapPair_left (hPorth i j (Ne.symm hji))) W (hWe _ _) (hWe _ _) hxW hi
    push Not at hA hB
    obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hx0
    set w : V := y - (polar Q y (P 0).f) • (P 0).e - (polar Q y (P 0).e) • (P 0).f with hw
    have hwe : polar Q (P 0).e w = 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm Q y (P 0).e, polar_self_eq_zero (P 0).Q_e, (P 0).polar_ef]
      ring
    have hwf : polar Q (P 0).f w = 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        polar_comm Q y (P 0).f, (P 0).polar_fe, polar_self_eq_zero (P 0).Q_f]
      ring
    have hxw : polar Q x w ≠ 0 := by
      rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        hA 0, hB 0]
      simpa using hy
    exact exists_singular_of_perp (P 0) W hxW (hA 0) (HypPair.mem_perp.2 ⟨hwe, hwf⟩)
      (hWe (P 0).e w x hxW) hxw
  obtain ⟨u₀, hu₀W, hu₀0, hu₀Q⟩ := hsing
  have hall : ∀ v : V, Q v = 0 → v ∈ W := by
    intro v hv
    by_cases hv0 : v = 0
    · rw [hv0]; exact W.zero_mem
    obtain ⟨g, hg, hgv⟩ :=
      exists_mem_elementaryGroup_apply_eq hQ (hPorth 0 1 (by decide)) hu₀0 hv0
        (by rw [hu₀Q, hv])
    rw [← hgv]
    exact hW g hg u₀ hu₀W
  rw [eq_top_iff]
  intro v _
  have hv : v ∈ Submodule.span K {u : V | Q u = 0} := by
    rw [span_singular_eq_top (P 0)]
    exact Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp hv
  rw [← hfg]
  refine W.sum_mem fun i _ => hall _ ?_
  have hg : Q (g i : V) = 0 := (g i).2
  rw [QuadraticMap.map_smul, hg]
  simp

end Abstract

section Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}

theorem addSubgroup_eq_bot_or_top_of_elemMatrixIso (E : ElemMatrixIso Q X)
    (hQ : (polarBilin Q).Nondegenerate)
    (hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j))
    (U : AddSubgroup (ι → K))
    (hU : ∀ A ∈ X, ∀ v ∈ U, ((A : GL ι K) : Matrix ι ι K) *ᵥ v ∈ U) : U = ⊥ ∨ U = ⊤ := by
  refine addSubgroup_eq_bot_or_top_of_elementaryGroup_invariant hQ hP U ?_
  intro g hg x hx
  have h1 := E.app (E.equiv.symm ⟨g, hg⟩) x
  rw [MulEquiv.apply_symm_apply] at h1
  have h3 := hU _ (E.equiv.symm ⟨g, hg⟩).2 x hx
  rw [← h1] at h3
  exact h3

end Matrix

end CFSG.RankThree.GF2n.Stroth80
