module

public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthRat
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBasic
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.SignalizerFunctorTheorem.NonLocal.Engine

public section

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.RankThree.Classical2

namespace CFSG.SignalizerFunctorTheorem.NonLocal.Orth

section Data

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

@[expose] noncomputable def orthProjData :
    ProjData K (Fin d) (matrixDerived Q) (matrixProjectiveDerived Q) where
  ρ := (matrixDerived Q).subtype
  hρ := Subtype.val_injective
  π := matrixProjectiveProjection Q
  hπ := matrixProjectiveProjection_surjective Q
  hker := by
    intro h
    rw [matrixProjectiveProjection, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_matrixDerivedScalars_iff]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have := congrArg (fun x : GL (Fin d) K => (x : Matrix (Fin d) (Fin d) K)) hc
      simpa using this.symm
    · rintro ⟨c, hc⟩
      exact ⟨c, Units.ext (by simpa using hc.symm)⟩

end Data

section Compat

variable {K : Type} [Field K] (k : Subfield K) {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem polar_vecIncl' (hext : IsExtension k Q₀ Q) (v w : Fin d → k) :
    polar Q (vecIncl k v) (vecIncl k w) = ((polar Q₀ v w : k) : K) := by
  unfold QuadraticMap.polar
  rw [← vecIncl_add, hext, hext, hext]
  push_cast
  rfl

theorem vecIncl_smul' (c : k) (v : Fin d → k) :
    vecIncl k (c • v) = (c : K) • vecIncl k v := by
  funext i
  simp [vecIncl]

theorem vecIncl_sub' (v w : Fin d → k) : vecIncl k (v - w) = vecIncl k v - vecIncl k w := by
  funext i
  simp [vecIncl]

theorem linearEquiv_ext_vecIncl' {f g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (h : ∀ w : Fin d → k, f (vecIncl k w) = g (vecIncl k w)) : f = g := by
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin d)).ext
  intro i
  have := h (Pi.single i 1)
  rw [vecIncl_single] at this
  simpa using this

theorem eichler_vecIncl' (hext : IsExtension k Q₀ Q) {u w : Fin d → k} (hu : Q₀ u = 0)
    (huw : polar Q₀ u w = 0) (v : Fin d → k) :
    eichler Q (vecIncl k u) (vecIncl k w) (vecIncl k v) = vecIncl k (eichler Q₀ u w v) := by
  have hu' : Q (vecIncl k u) = 0 := by rw [hext, hu]; rfl
  have huw' : polar Q (vecIncl k u) (vecIncl k w) = 0 := by
    rw [polar_vecIncl' k hext, huw]
    rfl
  have hQw : Q (vecIncl k w) = ((Q₀ w : k) : K) := hext w
  have h1 : polar Q (vecIncl k v) (vecIncl k u) = ((polar Q₀ v u : k) : K) :=
    polar_vecIncl' k hext v u
  have h2 : polar Q (vecIncl k v) (vecIncl k w) = ((polar Q₀ v w : k) : K) :=
    polar_vecIncl' k hext v w
  rw [eichler_apply hu' huw', eichler_apply hu huw, hQw, h1, h2]
  funext i
  simp [vecIncl]

theorem matrixLinearEquiv_glIncl_eichler' (hext : IsExtension k Q₀ Q) {u w : Fin d → k}
    (hu : Q₀ u = 0) (huw : polar Q₀ u w = 0) {x : GL (Fin d) k}
    (hx : matrixLinearIso x = eichler Q₀ u w) :
    matrixLinearEquiv (glIncl k x) = eichler Q (vecIncl k u) (vecIncl k w) := by
  apply linearEquiv_ext_vecIncl' k
  intro v
  rw [matrixLinearEquiv_apply, mulVec_vecIncl, eichler_vecIncl' k hext hu huw]
  congr 1
  have := congrArg (fun F => F v) hx
  simpa [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixLinearIso_apply] using this

@[expose] def hypIncl (hext : IsExtension k Q₀ Q) (P : HypPair Q₀) : HypPair Q where
  e := vecIncl k P.e
  f := vecIncl k P.f
  Q_e := by rw [hext, P.Q_e]; rfl
  Q_f := by rw [hext, P.Q_f]; rfl
  polar_ef := by rw [polar_vecIncl' k hext, P.polar_ef]; rfl

theorem hypIncl_orth (hext : IsExtension k Q₀ Q) {P P' : HypPair Q₀} (h : P.Orth P') :
    (hypIncl k hext P).Orth (hypIncl k hext P') where
  ee := by
    show polar Q (vecIncl k P.e) (vecIncl k P'.e) = 0
    rw [polar_vecIncl' k hext, h.ee]; rfl
  ef := by
    show polar Q (vecIncl k P.e) (vecIncl k P'.f) = 0
    rw [polar_vecIncl' k hext, h.ef]; rfl
  fe := by
    show polar Q (vecIncl k P.f) (vecIncl k P'.e) = 0
    rw [polar_vecIncl' k hext, h.fe]; rfl
  ff := by
    show polar Q (vecIncl k P.f) (vecIncl k P'.f) = 0
    rw [polar_vecIncl' k hext, h.ff]; rfl

end Compat

section Triple

variable {k : Type} [Field k] {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}

theorem exists_hyp_triple' (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0) :
    ∃ P : Fin 3 → HypPair Q₀, ∀ i j, i ≠ j → (P i).Orth (P j) := by
  obtain ⟨U, hU3, hUQ⟩ := hT₀
  obtain ⟨P₁, P₂, P₃, h12, h13, h23⟩ := exists_three_hypPairs hnd₀ (T := U) hU3.ge hUQ
  refine ⟨![P₁, P₂, P₃], fun i j hij => ?_⟩
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simp [h12, h13, h23, h12.symm,
    h13.symm, h23.symm]

theorem exists_matrixDerived_eichler [Finite k] (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (u w : Fin d → k) :
    ∃ x : matrixDerived Q₀, matrixLinearIso (d := d) (K := k) x.val = eichler Q₀ u w := by
  have hmem : eichler Q₀ u w ∈ orthDerived Q₀ := by
    rw [(CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hnd₀ hT₀).1]
    exact eichler_mem_elementaryGroup _ _ _
  obtain ⟨x, hxd⟩ := CFSG.RankThree.PartOne.KCOrthogonalAut.exists_matrixDerived Q₀ ⟨_, hmem⟩
  exact ⟨x, hxd.symm⟩

end Triple

section Irr

variable {K : Type} [Field K] [Finite K] (k : Subfield K) {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem exists_singular_mem (hext : IsExtension k Q₀ Q) (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hnd : (polarBilin Q).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (W : Submodule K (Fin d → K))
    (hW : ∀ g : matrixDerived Q₀, ∀ n ∈ W,
      ((glIncl k g.val : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ n ∈ W) (hbot : W ≠ ⊥) :
    ∃ u : Fin d → k, u ≠ 0 ∧ Q₀ u = 0 ∧ vecIncl k u ∈ W := by
  classical
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨P, hP⟩ := exists_hyp_triple' hnd₀ hT₀
  have hE : ∀ u w : Fin d → k, Q₀ u = 0 → polar Q₀ u w = 0 → ∀ y ∈ W,
      eichler Q (vecIncl k u) (vecIncl k w) y ∈ W := by
    intro u w hu huw y hy
    obtain ⟨g, hg⟩ := exists_matrixDerived_eichler hnd₀ hT₀ u w
    rw [← matrixLinearEquiv_glIncl_eichler' k hext hu huw hg, matrixLinearEquiv_apply]
    exact hW g y hy
  have hOK : ∀ i j, i ≠ j → (hypIncl k hext (P i)).Orth (hypIncl k hext (P j)) :=
    fun i j hij => hypIncl_orth k hext (hP i j hij)
  have hne : ∀ i : Fin 3, ∃ j : Fin 3, j ≠ i := fun i => ⟨i + 1, by fin_cases i <;> decide⟩
  by_cases hA : ∃ i, polar Q x (hypIncl k hext (P i)).e ≠ 0
  · obtain ⟨i, hi⟩ := hA
    obtain ⟨j, hj⟩ := hne i
    refine ⟨(P i).e, (P i).e_ne_zero, (P i).Q_e, ?_⟩
    exact exchange_mem (hypIncl k hext (P i)) (hypIncl k hext (P j)) (hOK i j hj.symm) W
      (hE (P i).e (P j).e (P i).Q_e (hP i j hj.symm).ee)
      (hE (P i).e (P j).f (P i).Q_e (hP i j hj.symm).ef) hxW hi
  by_cases hB : ∃ i, polar Q x (hypIncl k hext (P i)).f ≠ 0
  · obtain ⟨i, hi⟩ := hB
    obtain ⟨j, hj⟩ := hne i
    refine ⟨(P i).f, (P i).f_ne_zero, (P i).Q_f, ?_⟩
    exact exchange_mem (swapPair (hypIncl k hext (P i))) (hypIncl k hext (P j))
      (orth_swapPair_left (hOK i j hj.symm)) W
      (hE (P i).f (P j).e (P i).Q_f (hP i j hj.symm).fe)
      (hE (P i).f (P j).f (P i).Q_f (hP i j hj.symm).ff) hxW hi
  push Not at hA hB
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hnd hx0
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin d, polar Q x (Pi.single i 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hy
    have hzero : polarBilin Q x = 0 := (Pi.basisFun K (Fin d)).ext fun i => by
      simpa [Pi.basisFun_apply, polarBilin_apply_apply] using hcon i
    simpa [polarBilin_apply_apply] using LinearMap.congr_fun hzero y
  set v : Fin d → k := Pi.single i₀ 1 with hv
  have hvK : vecIncl k v = Pi.single i₀ 1 := vecIncl_single k i₀
  have hproj : vecIncl k ((P 0).proj v) = vecIncl k v - ((polar Q₀ v (P 0).f : k) : K) •
      (hypIncl k hext (P 0)).e - ((polar Q₀ v (P 0).e : k) : K) • (hypIncl k hext (P 0)).f := by
    show vecIncl k (v - polar Q₀ v (P 0).f • (P 0).e - polar Q₀ v (P 0).e • (P 0).f) = _
    rw [vecIncl_sub', vecIncl_sub', vecIncl_smul', vecIncl_smul']
    rfl
  have hperp : (P 0).proj v ∈ (P 0).perp := (P 0).proj_mem_perp v
  have hwperp : vecIncl k ((P 0).proj v) ∈ (hypIncl k hext (P 0)).perp := by
    rw [HypPair.mem_perp]
    obtain ⟨h1, h2⟩ := HypPair.mem_perp.mp hperp
    constructor
    · show polar Q (vecIncl k (P 0).e) (vecIncl k ((P 0).proj v)) = 0
      rw [polar_vecIncl' k hext, h1]; rfl
    · show polar Q (vecIncl k (P 0).f) (vecIncl k ((P 0).proj v)) = 0
      rw [polar_vecIncl' k hext, h2]; rfl
  have hxw : polar Q x (vecIncl k ((P 0).proj v)) ≠ 0 := by
    rw [hproj, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      hA 0, hB 0, hvK]
    simpa using hi₀
  refine ⟨(P 0).e, (P 0).e_ne_zero, (P 0).Q_e, ?_⟩
  exact perp_extract_mem (hypIncl k hext (P 0)) W hxW (hA 0) hwperp
    (hE (P 0).e ((P 0).proj v) (P 0).Q_e (HypPair.mem_perp.mp hperp).1 x hxW) hxw

theorem orth_irreducible (hext : IsExtension k Q₀ Q) (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hnd : (polarBilin Q).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (W : Submodule K (Fin d → K))
    (hW : ∀ g : matrixDerived Q₀, ∀ n ∈ W,
      ((glIncl k g.val : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ n ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨u₀, hu₀0, hu₀Q, hu₀W⟩ := exists_singular_mem k hext hnd₀ hnd hT₀ W hW hbot
  obtain ⟨P, hP⟩ := exists_hyp_triple' hnd₀ hT₀
  have hzero : vecIncl k (0 : Fin d → k) = 0 := by
    funext i
    simp [vecIncl]
  have hsing : ∀ u : Fin d → k, Q₀ u = 0 → vecIncl k u ∈ W := by
    intro u hu
    by_cases hu0 : u = 0
    · rw [hu0, hzero]; exact W.zero_mem
    obtain ⟨g, hg, hgu⟩ := exists_mem_elementaryGroup_apply_eq hnd₀ (hP 0 1 (by decide)) hu₀0 hu0
      (by rw [hu₀Q, hu])
    have hgd : g ∈ orthDerived Q₀ := by
      rw [(CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hnd₀ hT₀).1]; exact hg
    obtain ⟨A, hA⟩ := CFSG.RankThree.PartOne.KCOrthogonalAut.exists_matrixDerived Q₀ ⟨g, hgd⟩
    have h1 := hW A (vecIncl k u₀) hu₀W
    rw [mulVec_vecIncl] at h1
    have h2 : (A.val : Matrix (Fin d) (Fin d) k) *ᵥ u₀ = u := by
      have : matrixLinearIso (d := d) (K := k) A.val u₀ = g u₀ := by rw [← hA]
      rw [← hgu, ← this]
      rfl
    rw [h2] at h1
    exact h1
  have hall : ∀ v : Fin d → k, vecIncl k v ∈ W := by
    intro v
    have hv : v ∈ Submodule.span k {u : Fin d → k | Q₀ u = 0} := by
      rw [span_singular_eq_top (P 0)]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem u hu => exact hsing u hu
    | zero => rw [hzero]; exact W.zero_mem
    | add a b _ _ ha hb => rw [vecIncl_add]; exact W.add_mem ha hb
    | smul c a _ ha => rw [vecIncl_smul']; exact W.smul_mem _ ha
  refine eq_top_iff.mpr fun y _ => ?_
  rw [← (Pi.basisFun K (Fin d)).sum_repr y]
  refine Submodule.sum_mem _ fun i _ => W.smul_mem _ ?_
  rw [Pi.basisFun_apply, ← vecIncl_single k i]
  exact hall _

end Irr

end CFSG.SignalizerFunctorTheorem.NonLocal.Orth
