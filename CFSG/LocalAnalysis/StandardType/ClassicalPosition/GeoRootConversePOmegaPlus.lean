module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoSiegelConj

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

private lemma grcPOp_L1_rootGroup_classification (k f : ℕ) (hn : 3 ≤ k + 3)
    {γ : Fin (k + 3) → ℤ}
    (hγ : γ ∈ (Spin.plusDatum (k + 3) (GaloisField 2 f) hn).roots) :
    ∃ (i j : Fin (k + 3)) (hij : i ≠ j) (s t : Bool),
      Spin.plusRootGroup (k + 3) (GaloisField 2 f) hn γ =
        (((Spin.plusFrame (k + 3) (GaloisField 2 f) hn).longRoot hij s t).range) := by
  obtain ⟨i, j, hij, s, t, -, hX⟩ := Spin.exists_plusRootGroup_eq (K := GaloisField 2 f) hn hγ
  exact ⟨i, j, hij, s, t, hX⟩

private lemma grcPOp_L2_framePair_nonsingular (k f : ℕ) (hn : 3 ≤ k + 3)
    {i j : Fin (k + 3)} (hij : i ≠ j) (s t : Bool) :
    (Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec j t ≠ 0 ∧
      (Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec i s ≠ 0 ∧
      Spin.quadPlus (k + 3) (GaloisField 2 f)
        ((Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec j t) = 0 ∧
      Spin.quadPlus (k + 3) (GaloisField 2 f)
        ((Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec i s) = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))
        ((Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec j t)
        ((Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec i s) = 0 := by
  let Fr := Spin.plusFrame (k + 3) (GaloisField 2 f) hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := Fr.polar_vec_not j t
    rw [h, QuadraticMap.polar_zero_left] at h1
    exact zero_ne_one h1
  · intro h
    have h1 := Fr.polar_vec_not i s
    rw [h, QuadraticMap.polar_zero_left] at h1
    exact zero_ne_one h1
  · exact Fr.map_vec j t
  · exact Fr.map_vec i s
  · exact Fr.polar_vec_of_ne (i := j) (j := i) hij.symm t s

private lemma grcPOp_L3_framePair_independent (k f : ℕ) (hn : 3 ≤ k + 3)
    {i j : Fin (k + 3)} (hij : i ≠ j) (s t : Bool) :
    LinearIndependent (GaloisField 2 f)
      ![(Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec j t,
        (Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec i s] := by
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  let Fr := Spin.plusFrame (k + 3) (GaloisField 2 f) hn
  rw [LinearIndependent.pair_iff]
  intro c d hcd
  have hc : c = 0 := by
    have h := congrArg (QuadraticMap.polarBilin Q (Fr.vec j (!t))) hcd
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero] at h
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply] at h
    rw [Fr.polar_vec_of_ne (i := j) (j := i) hij.symm (!t) s,
      QuadraticMap.polar_comm, Fr.polar_vec_not j t] at h
    simpa using h
  have hd : d = 0 := by
    have h := congrArg (QuadraticMap.polarBilin Q (Fr.vec i (!s))) hcd
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero] at h
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply] at h
    rw [Fr.polar_vec_of_ne (i := i) (j := j) hij (!s) t,
      QuadraticMap.polar_comm, Fr.polar_vec_not i s] at h
    simpa using h
  exact ⟨hc, hd⟩

private lemma grcPOp_L4_spinAction_nonsingular (k f : ℕ)
    (u : spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)))
    {x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : LinearIndependent (GaloisField 2 f) ![x, y]) :
    Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u x ≠ 0 ∧
      Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u y ≠ 0 ∧
      LinearIndependent (GaloisField 2 f)
        ![Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u x,
          Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u y] := by
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hx ((Spin.spinAction Q u).injective (by simpa using h))
  · intro h
    exact hy ((Spin.spinAction Q u).injective (by simpa using h))
  · rw [LinearIndependent.pair_iff] at hxy ⊢
    intro a b hab
    apply hxy a b
    apply (Spin.spinAction Q u).injective
    rw [map_add, map_smul, map_smul, hab, map_zero]

private lemma grcPOp_L5_spinAction_form (k f : ℕ)
    (u : spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)))
    {x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f}
    (hxQ : Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0)
    (hyQ : Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0)
    (hxypol : QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0) :
    Spin.quadPlus (k + 3) (GaloisField 2 f)
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u x) = 0 ∧
      Spin.quadPlus (k + 3) (GaloisField 2 f)
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u y) = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f))
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u x)
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u y) = 0 := by
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  exact ⟨(Spin.map_spinAction (Q := Q) u x).trans hxQ,
    (Spin.map_spinAction (Q := Q) u y).trans hyQ,
    (Spin.polar_spinAction (Q := Q) u x y).trans hxypol⟩

private lemma grcPOp_L6_conj_rootGroup_eq_siegelGroup (k f : ℕ) (hn : 3 ≤ k + 3)
    (u : spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)))
    {γ : Fin (k + 3) → ℤ} {i j : Fin (k + 3)} (hij : i ≠ j) (s t : Bool)
    (hX : Spin.plusRootGroup (k + 3) (GaloisField 2 f) hn γ =
      (((Spin.plusFrame (k + 3) (GaloisField 2 f) hn).longRoot hij s t).range)) :
    (((Spin.plusDatum (k + 3) (GaloisField 2 f) hn).rootGroup γ).map
        (MulAut.conj u).toMonoidHom).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
      siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u
          ((Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec j t))
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u
          ((Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec i s)) := by
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  let Fr : Spin.HypFrame Q (k + 3) := Spin.plusFrame (k + 3) (GaloisField 2 f) hn
  have hroot : (Spin.plusDatum (k + 3) (GaloisField 2 f) hn).rootGroup γ =
      (Fr.longRoot hij s t).range := by
    rw [show (Spin.plusDatum (k + 3) (GaloisField 2 f) hn).rootGroup γ =
        Spin.plusRootGroup (k + 3) (GaloisField 2 f) hn γ from rfl, hX]
  rw [hroot]
  exact Geo.map_conj_range_longRoot_eq_siegelGroup Fr hij s t u

theorem exists_siegelGroup_eq_rootGroup_POmegaPlus
    (k f
        : ℕ)
    {γ : Fin (ggU .POmegaPlus (k + 3) f).D.rank → ℤ}
    (hγ : γ ∈ (ggU .POmegaPlus (k + 3) f).D.roots)
    (u : (ggU .POmegaPlus (k + 3) f).K) :
    ∃ a₁ a₂ : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
      Spin.quadPlus (k + 3) (GaloisField 2 f) a₁ = 0 ∧
      Spin.quadPlus (k + 3) (GaloisField 2 f) a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 ∧
      (((ggU .POmegaPlus (k + 3) f).D.rootGroup γ).map (MulAut.conj u).toMonoidHom).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
        siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ := by
  have hn : 3 ≤ k + 3 := by omega
  change γ ∈ (Spin.plusDatum (k + 3) (GaloisField 2 f) hn).roots at hγ
  change ∃ a₁ a₂ : (Fin (k + 3) ⊕ Fin (k + 3)) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
      Spin.quadPlus (k + 3) (GaloisField 2 f) a₁ = 0 ∧
      Spin.quadPlus (k + 3) (GaloisField 2 f) a₂ = 0 ∧
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂ = 0 ∧
      (((Spin.plusDatum (k + 3) (GaloisField 2 f) hn).rootGroup γ).map
        (MulAut.conj u).toMonoidHom).map
        (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f))) =
        siegelGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)) a₁ a₂
  obtain ⟨i, j, hij, s, t, hX⟩ := grcPOp_L1_rootGroup_classification k f hn hγ
  obtain ⟨hx, hy, hxQ, hyQ, hxypol⟩ := grcPOp_L2_framePair_nonsingular k f hn hij s t
  have hxy : LinearIndependent (GaloisField 2 f)
      ![(Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec j t,
        (Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec i s] :=
    grcPOp_L3_framePair_independent k f hn hij s t
  obtain ⟨ha, hb, hab⟩ := grcPOp_L4_spinAction_nonsingular k f u hx hy hxy
  obtain ⟨haQ, hbQ, hab_pol⟩ := grcPOp_L5_spinAction_form k f u hxQ hyQ hxypol
  exact ⟨Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u
          ((Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec j t),
    Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 f)) u
          ((Spin.plusFrame (k + 3) (GaloisField 2 f) hn).vec i s),
    ha, hb, hab, haQ, hbQ, hab_pol,
    grcPOp_L6_conj_rootGroup_eq_siegelGroup k f hn u hij s t hX⟩

end CFSG.StandardType.ClassicalPosition
