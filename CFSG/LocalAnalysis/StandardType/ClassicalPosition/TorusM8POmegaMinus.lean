module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import CFSG.LieType.Universal.Spin.Twisted.Torus
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs
public import CFSG.LieType.Universal.Spin.Twisted.Unipotent

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private lemma torM8M_conj_longRoot (n : ℕ) {F : Type} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {h : ↥(spinGroup (Spin.quadMinus n F b c))}
    (hh : h ∈ ggTorus (Spin.Twisted.minusDatum n hirr))
    {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    ∃ a : F,
      ((Spin.spinAction (Spin.quadMinus n F b c)) h *
          CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadMinus n F b c)
            (Spin.Twisted.minusVec n j t) (Spin.Twisted.minusVec n i s) *
          ((Spin.spinAction (Spin.quadMinus n F b c)) h)⁻¹ =
        CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadMinus n F b c)
          (Spin.Twisted.minusVec n j t) (a • Spin.Twisted.minusVec n i s)) := by
  let γ : Fin (n - 1) → ℤ := Spin.ofStdB (n - 1)
    (Pi.single i (Spin.boolSign s) + Pi.single j (Spin.boolSign t))
  have hγ : Spin.toStdB (n - 1) γ =
      Pi.single i (Spin.boolSign s) + Pi.single j (Spin.boolSign t) := by
    simpa [γ] using (Spin.toStdB_ofStdB (n := n - 1)
      (Pi.single i (Spin.boolSign s) + Pi.single j (Spin.boolSign t)))
  have hγroots : γ ∈ (Spin.Twisted.minusDatum n hirr).roots := by
    rw [Spin.Twisted.minusDatum_roots]
    exact Spin.Twisted.mem_roots_of_toStdB_eq_long (n := n) hij s t hγ
  have hnorm := mem_normalizer_of_mem_ggTorus hh hγroots
  have hroot : (Spin.Twisted.minusDatum n hirr).rootGroup γ =
      ((Spin.Twisted.minusFrame n b c).longRoot hij s t).range :=
    Spin.Twisted.minusRootGroup_eq_long (n := n) hirr hij s t hγ
  have hmem : h * (Spin.Twisted.minusFrame n b c).longRoot hij s t (Multiplicative.ofAdd 1) * h⁻¹ ∈
      ((Spin.Twisted.minusFrame n b c).longRoot hij s t).range := by
    rw [← hroot]
    exact (Subgroup.mem_normalizer_iff.mp hnorm
      ((Spin.Twisted.minusFrame n b c).longRoot hij s t (Multiplicative.ofAdd 1))).mp (by
        rw [hroot]
        exact ⟨Multiplicative.ofAdd 1, rfl⟩)
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨y.toAdd, ?_⟩
  have hEqTarget : h * (Spin.Twisted.minusFrame n b c).longRoot hij s t
        (Multiplicative.ofAdd 1) * h⁻¹ =
      (Spin.Twisted.minusFrame n b c).longRoot hij s t (Multiplicative.ofAdd y.toAdd) := hy.symm
  have happ := congrArg (Spin.spinAction (Spin.quadMinus n F b c)) hEqTarget
  simp only [map_mul, map_inv] at happ
  rw [Spin.HypFrame.spinAction_longRoot_eq_eichler
    (F := (Spin.Twisted.minusFrame n b c).toHypFrame)] at happ
  have hRy : (Spin.spinAction (Spin.quadMinus n F b c))
        ((Spin.Twisted.minusFrame n b c).longRoot hij s t (Multiplicative.ofAdd y.toAdd)) =
      CFSG.ClassicalGroups.Orthogonal.eichler (Spin.quadMinus n F b c)
        (Spin.Twisted.minusVec n j t) (y.toAdd • Spin.Twisted.minusVec n i s) :=
    Spin.HypFrame.spinAction_longRoot_eq_eichler (F := (Spin.Twisted.minusFrame n b c).toHypFrame)
      hij s t y.toAdd
  rw [hRy] at happ
  simpa [Spin.Twisted.minusFrame_vec, one_smul] using happ

private lemma torM8M_mem_span_pair (n : ℕ) {F : Type} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {h : ↥(spinGroup (Spin.quadMinus n F b c))}
    (hh : h ∈ ggTorus (Spin.Twisted.minusDatum n hirr))
    {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    ((Spin.spinAction (Spin.quadMinus n F b c)) h) (Spin.Twisted.minusVec n i s) ∈
      Submodule.span F
        ({Spin.Twisted.minusVec n j t, Spin.Twisted.minusVec n i s} :
          Set (Spin.Twisted.Vm n F)) := by
  let Q := Spin.quadMinus n F b c
  let B : Spin.Twisted.Vm n F ≃ₗ[F] Spin.Twisted.Vm n F := (Spin.spinAction Q) h
  obtain ⟨a, ha⟩ := torM8M_conj_longRoot (n := n) hirr hh hij s t
  have hBmem : B ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (Spin.map_spinAction (Q := Q) h)
  have hE : CFSG.ClassicalGroups.Orthogonal.eichler Q
        (B (Spin.Twisted.minusVec n j t)) (B (Spin.Twisted.minusVec n i s)) =
      CFSG.ClassicalGroups.Orthogonal.eichler Q
        (Spin.Twisted.minusVec n j t) (a • Spin.Twisted.minusVec n i s) := by
    have hc := CFSG.ClassicalGroups.Orthogonal.eichler_conj (Q := Q) hBmem
      (Spin.Twisted.minusVec n j t) (Spin.Twisted.minusVec n i s)
    exact hc.symm.trans (by simpa [Q, B] using ha)
  have hu0 : Q (B (Spin.Twisted.minusVec n j t)) = 0 := by
    simp [Q, B, Spin.map_spinAction, Spin.Twisted.quadMinus_minusVec]
  have hw0 : Q (B (Spin.Twisted.minusVec n i s)) = 0 := by
    simp [Q, B, Spin.map_spinAction, Spin.Twisted.quadMinus_minusVec]
  have huw : QuadraticMap.polar Q (B (Spin.Twisted.minusVec n j t))
      (B (Spin.Twisted.minusVec n i s)) = 0 := by
    simp [Q, B, Spin.polar_spinAction, Spin.Twisted.polar_minusVec_minusVec, hij.symm]
  have hyu : QuadraticMap.polar Q (B (Spin.Twisted.minusVec n j (!t)))
      (B (Spin.Twisted.minusVec n j t)) = 1 := by
    simp [Q, B, Spin.polar_spinAction, Spin.Twisted.polar_minusVec_minusVec]
  have hyw : QuadraticMap.polar Q (B (Spin.Twisted.minusVec n j (!t)))
      (B (Spin.Twisted.minusVec n i s)) = 0 := by
    simp [Q, B, Spin.polar_spinAction, Spin.Twisted.polar_minusVec_minusVec, hij.symm]
  have hu0' : Q (Spin.Twisted.minusVec n j t) = 0 := by
    simp [Q, Spin.Twisted.quadMinus_minusVec]
  have hw0' : Q (Spin.Twisted.minusVec n i s) = 0 := by
    simp [Q, Spin.Twisted.quadMinus_minusVec]
  have huw' : QuadraticMap.polar Q (Spin.Twisted.minusVec n j t)
      (a • Spin.Twisted.minusVec n i s) = 0 := by
    rw [QuadraticMap.polar_smul_right]
    simp [Q, Spin.Twisted.polar_minusVec_minusVec, hij.symm]
  have hEqEval := congrArg (fun f : Spin.Twisted.Vm n F ≃ₗ[F] Spin.Twisted.Vm n F =>
      f (B (Spin.Twisted.minusVec n j (!t)))) hE
  rw [show CFSG.ClassicalGroups.Orthogonal.eichler Q
        (B (Spin.Twisted.minusVec n j t)) (B (Spin.Twisted.minusVec n i s))
        (B (Spin.Twisted.minusVec n j (!t))) = _ from
      CFSG.ClassicalGroups.Orthogonal.eichler_apply (Q := Q) hu0 huw _,
    show CFSG.ClassicalGroups.Orthogonal.eichler Q
        (Spin.Twisted.minusVec n j t) (a • Spin.Twisted.minusVec n i s)
        (B (Spin.Twisted.minusVec n j (!t))) = _ from
      CFSG.ClassicalGroups.Orthogonal.eichler_apply (Q := Q) hu0' huw' _] at hEqEval
  have hQaw : Q (a • Spin.Twisted.minusVec n i s) = 0 := by
    rw [QuadraticMap.map_smul, hw0']
    simp
  simp only [hyu, hyw, hw0, hQaw, one_smul, zero_mul, add_zero, zero_add, mul_one,
    smul_eq_mul] at hEqEval
  have hEqEval' := hEqEval
  simp only [zero_smul, sub_eq_add_neg, add_assoc] at hEqEval'
  have hcancel : B (Spin.Twisted.minusVec n i s) =
      QuadraticMap.polar Q (B (Spin.Twisted.minusVec n j (!t)))
          (Spin.Twisted.minusVec n j t) • (a • Spin.Twisted.minusVec n i s) -
        QuadraticMap.polar Q (B (Spin.Twisted.minusVec n j (!t)))
          (a • Spin.Twisted.minusVec n i s) •
            Spin.Twisted.minusVec n j t := by
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using
      add_left_cancel hEqEval'
  rw [Submodule.mem_span_pair]
  refine ⟨-QuadraticMap.polar Q (B (Spin.Twisted.minusVec n j (!t)))
        (a • Spin.Twisted.minusVec n i s),
      QuadraticMap.polar Q (B (Spin.Twisted.minusVec n j (!t)))
        (Spin.Twisted.minusVec n j t) * a, ?_⟩
  change -QuadraticMap.polar Q (B (Spin.Twisted.minusVec n j (!t)))
        (a • Spin.Twisted.minusVec n i s) • Spin.Twisted.minusVec n j t +
      (QuadraticMap.polar Q (B (Spin.Twisted.minusVec n j (!t)))
        (Spin.Twisted.minusVec n j t) * a) • Spin.Twisted.minusVec n i s =
    B (Spin.Twisted.minusVec n i s)
  rw [hcancel, ← smul_smul, neg_smul, sub_eq_add_neg]
  abel

private lemma torM8M_mem_span_single (n : ℕ) {F : Type} [Field F]
    {i j j' : Fin (n - 1)} {s : Bool}
    (hji : j ≠ i) (hjj' : j' ≠ j)
    {v : Spin.Twisted.Vm n F}
    (hv1 : v ∈ Submodule.span F
      ({Spin.Twisted.minusVec n j true, Spin.Twisted.minusVec n i s} :
        Set (Spin.Twisted.Vm n F)))
    (hv2 : v ∈ Submodule.span F
      ({Spin.Twisted.minusVec n j' true, Spin.Twisted.minusVec n i s} :
        Set (Spin.Twisted.Vm n F))) :
    v ∈ Submodule.span F ({Spin.Twisted.minusVec n i s} : Set (Spin.Twisted.Vm n F)) := by
  rw [Submodule.mem_span_pair] at hv1 hv2
  obtain ⟨a1, b1, h1⟩ := hv1
  obtain ⟨a2, b2, h2⟩ := hv2
  have hzero : v (Sum.inl j) = 0 := by
    have h2j := congrFun h2 (Sum.inl j)
    cases s <;>
      simpa [Spin.Twisted.minusVec_eq_single, Spin.Twisted.minusPos, Pi.single_apply,
        hji, hjj'.symm] using h2j.symm
  have ha1 : a1 = 0 := by
    have h1j := congrFun h1 (Sum.inl j)
    have h1j' : a1 = v (Sum.inl j) := by
      cases s <;>
        simpa [Spin.Twisted.minusVec_eq_single, Spin.Twisted.minusPos, Pi.single_apply,
          hji] using h1j
    rw [hzero] at h1j'
    exact h1j'
  rw [Submodule.mem_span_singleton]
  refine ⟨b1, ?_⟩
  rw [ha1, zero_smul, zero_add] at h1
  exact h1

private lemma torM8M_exists_two_ne {m : ℕ} (hm : 2 < m) (i : Fin m) :
    ∃ j j' : Fin m, j ≠ i ∧ j' ≠ i ∧ j' ≠ j := by
  obtain ⟨j, hji, -⟩ := Fin.exists_ne_and_ne_of_two_lt (n := m) i i hm
  obtain ⟨j', hj'i, hj'j⟩ := Fin.exists_ne_and_ne_of_two_lt (n := m) i j hm
  exact ⟨j, j', hji, hj'i, hj'j⟩

theorem exists_spinAction_minusVec_eq_smul_POmegaMinus (n : ℕ) {F : Type} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {h : ↥(spinGroup (Spin.quadMinus n F b c))}
    (hh : h ∈ ggTorus (Spin.Twisted.minusDatum n hirr)) (hn : 4 ≤ n)
    (l : Fin (n - 1)) (r : Bool) :
    ∃ μ : F, ((Spin.spinAction (Spin.quadMinus n F b c)) h) (Spin.Twisted.minusVec n l r) =
      μ • Spin.Twisted.minusVec n l r := by
  have hm : 2 < n - 1 := by omega
  obtain ⟨j, j', hjl, hj'l, hj'j⟩ := torM8M_exists_two_ne hm l
  have hv1 := torM8M_mem_span_pair (n := n) hirr hh (hij := hjl.symm) r true
  have hv2 := torM8M_mem_span_pair (n := n) hirr hh (hij := hj'l.symm) r true
  have hsingle := torM8M_mem_span_single (n := n) (j := j) (j' := j') (s := r)
    hjl hj'j hv1 hv2
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hsingle
  exact ⟨μ, hμ.symm⟩

theorem exists_spinAction_planeVec_eq_POmegaMinus (n : ℕ) {F : Type} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {h : ↥(spinGroup (Spin.quadMinus n F b c))}
    (hh : h ∈ ggTorus (Spin.Twisted.minusDatum n hirr)) (hn : 4 ≤ n)
    (p : Fin 2 → F) :
    ∃ q : Fin 2 → F,
      ((Spin.spinAction (Spin.quadMinus n F b c)) h) (Spin.Twisted.planeVec n p) =
        Spin.Twisted.planeVec n q := by
  let Q := Spin.quadMinus n F b c
  let B : Spin.Twisted.Vm n F ≃ₗ[F] Spin.Twisted.Vm n F := (Spin.spinAction Q) h
  let w : Spin.Twisted.Vm n F := Spin.Twisted.planeVec n p
  have hhinv : h⁻¹ ∈ ggTorus (Spin.Twisted.minusDatum n hirr) := inv_mem hh
  have hperp : ∀ (l : Fin (n - 1)) (s : Bool),
      QuadraticMap.polar Q (B w) (Spin.Twisted.minusVec n l s) = 0 := by
    intro l s
    obtain ⟨μ, hμ⟩ := exists_spinAction_minusVec_eq_smul_POmegaMinus (n := n) hirr hhinv hn l s
    have hBinv : ((Spin.spinAction Q) h)⁻¹ = (Spin.spinAction Q) h⁻¹ :=
      (map_inv (Spin.spinAction Q) h).symm
    have hp : QuadraticMap.polar Q (B w) (Spin.Twisted.minusVec n l s) =
        QuadraticMap.polar Q w (((Spin.spinAction Q) h⁻¹) (Spin.Twisted.minusVec n l s)) := by
      rw [← hBinv]
      simpa [B] using (Spin.polar_spinAction (Q := Q) h w
        (((Spin.spinAction Q) h)⁻¹ (Spin.Twisted.minusVec n l s)))
    rw [hp, hμ, QuadraticMap.polar_smul_right]
    have hz : QuadraticMap.polar Q w (Spin.Twisted.minusVec n l s) = 0 := by
      rw [QuadraticMap.polar_comm]
      simpa [Q, w] using Spin.Twisted.polar_minusVec_planeVec (n := n) (b := b) (c := c) l s p
    rw [hz, smul_zero]
  refine ⟨fun t => B w (Sum.inr (Sum.inr t)), ?_⟩
  funext x
  rcases x with l | l | t
  · have h0 : B w (Sum.inl l) = 0 := by
      have h := hperp l false
      rw [Spin.Twisted.minusVec_eq_single, Spin.Twisted.minusPos] at h
      rw [← Spin.polar_quadMinus_single_inr_inl (n := n) (K := F) (b := b) (c := c) (v := B w) l]
      simpa [Q] using h
    simpa [Q, B, w, Spin.Twisted.planeVec] using h0
  · have h0 : B w (Sum.inr (Sum.inl l)) = 0 := by
      have h := hperp l true
      rw [Spin.Twisted.minusVec_eq_single, Spin.Twisted.minusPos] at h
      rw [← Spin.polar_quadMinus_single_inl (n := n) (K := F) (b := b) (c := c) (v := B w) l]
      simpa [Q] using h
    simpa [Q, B, w, Spin.Twisted.planeVec] using h0
  · simp [Q, B, w, Spin.Twisted.planeVec]

theorem ggTorus_apply_eq_zero_POmegaMinus (n : ℕ) {F : Type} [Field F]
    {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    {h : ↥(spinGroup (Spin.quadMinus n F bq cq))}
    (hh : h ∈ ggTorus (Spin.Twisted.minusDatum n hirr)) {i j : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2}
    (hij : i ≠ j ∧ ¬ ((∃ a, i = Sum.inr (Sum.inr a)) ∧ ∃ a, j = Sum.inr (Sum.inr a))) :
    (((Spin.spinMatrix (Spin.quadMinus n F bq cq)) h : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) i j = 0 :=
      by
  let Q := Spin.quadMinus n F bq cq
  have hv : ∀ (l : Fin (n - 1)) (r : Bool),
      ∃ μ : F, ((Spin.spinAction Q) h) (Spin.Twisted.minusVec n l r) =
        μ • Spin.Twisted.minusVec n l r :=
    fun l r => exists_spinAction_minusVec_eq_smul_POmegaMinus (n := n) hirr hh hn l r
  have hA : ∀ p : Fin 2 → F,
      ∃ q : Fin 2 → F,
        ((Spin.spinAction Q) h) (Spin.Twisted.planeVec n p) = Spin.Twisted.planeVec n q :=
    fun p => exists_spinAction_planeVec_eq_POmegaMinus (n := n) hirr hh hn p
  have hblock := Spin.Twisted.blockDiag_mat_of (n := n) hv hA
  by_contra hne
  refine hij.2 (hblock i j hij.1 ?_)
  simpa [Q, Spin.Twisted.mat] using hne

end CFSG.StandardType.ClassicalPosition
