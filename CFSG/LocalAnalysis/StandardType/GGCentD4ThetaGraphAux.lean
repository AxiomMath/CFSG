module

public import CFSG.LocalAnalysis.StandardType.GGCentD4HomExt
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.ParabolicWeylStabilizer
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Lang.D4Three

theorem ntpTG_d4Idx_mem (k : Fin Tag.D4.rank) : d4Idx k ∈ d4Nodes Tag.E6 := by
  have hk : k.val < 4 := by simpa only [Tag.rank] using k.2
  have h6 : Tag.E6.rank = 6 := rfl
  simp only [d4Nodes, Set.mem_setOf_eq, d4Idx]
  omega

theorem ntpTG_exists_d4Idx_eq {i : Fin Tag.E6.rank} (hi : i ∈ d4Nodes Tag.E6) :
    ∃ k : Fin Tag.D4.rank, d4Idx k = i := by
  have hi' : 1 ≤ i.val ∧ i.val ≤ 4 := by
    simpa only [d4Nodes, Set.mem_setOf_eq] using hi
  have h6 : Tag.E6.rank = 6 := rfl
  have h4 : Tag.D4.rank = 4 := rfl
  refine ⟨⟨i.val - 1, by omega⟩, Fin.ext ?_⟩
  simp only [d4Idx]
  omega

theorem ntpTG_smul_mem_parabolicRoots {w : WeylGroup Tag.E6}
    {σ : Fin Tag.D4.rank → Fin Tag.D4.rank}
    (hw : ∀ k : Fin Tag.D4.rank,
      w • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) = Pi.single (d4Idx (σ k)) 1)
    {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6)) :
    w • α ∈ parabolicRoots Tag.E6 (d4Nodes Tag.E6) := by
  refine ⟨IsRoot.smul hα.1 w, fun i hi => ?_⟩
  rw [CFSG.LieType.Chevalley.smul_eq_sum_smul_single, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j ∈ d4Nodes Tag.E6
  · obtain ⟨k, hk⟩ := ntpTG_exists_d4Idx_eq hj
    subst hk
    rw [hw k, Pi.single_eq_of_ne]
    · ring
    · intro h
      exact hi (h ▸ ntpTG_d4Idx_mem (σ k))
  · rw [hα.2 j hj, zero_mul]

theorem ntpTG_conj_rootSpan_eq
    {L : Type} [Field L] (v z : WeylGroup Tag.E6) (ε : ℕ)
    (hz : ∀ k : Fin Tag.D4.rank,
      z • (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) =
        v • (Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1)) :
    (rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L z)).toMonoidHom =
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) := by
  set Φ := parabolicRoots Tag.E6 (d4Nodes Tag.E6) with hΦ
  set S0 := (fun α => v • α) '' Φ with hS0
  set w : WeylGroup Tag.E6 := v⁻¹ * z * v with hw
  have hw_smul : ∀ k : Fin Tag.D4.rank,
      w • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) =
        Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1 := by
    intro k
    have e1 : (v⁻¹ * z * v) • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) =
        v⁻¹ • (z • (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ))) := by
      rw [mul_smul, mul_smul]
    rw [e1, hz k, inv_smul_smul]
  have hw_inv_smul : ∀ k : Fin Tag.D4.rank,
      w⁻¹ • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ) =
        Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε).symm k)) 1 := by
    intro k
    have h := hw_smul ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε).symm k)
    have e : (CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε).symm k) = k :=
      Equiv.apply_symm_apply (CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k
    rw [e] at h
    rw [← h]
    exact inv_smul_smul w _
  have hsub : ∀ α ∈ Φ, w • α ∈ Φ :=
    fun α hα => ntpTG_smul_mem_parabolicRoots (w := w) hw_smul hα
  have hsub_inv : ∀ α ∈ Φ, w⁻¹ • α ∈ Φ :=
    fun α hα => ntpTG_smul_mem_parabolicRoots (w := w⁻¹) hw_inv_smul hα
  have hz_image : (fun γ => z • γ) '' S0 = S0 := by
    ext β
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨α, hα, rfl⟩ := hγ
      have e : z • (v • α) = v • (w • α) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        rw [hw]
        group
      exact ⟨w • α, hsub α hα, e.symm⟩
    · rintro ⟨α, hα, rfl⟩
      have h1 : z • (v • (w⁻¹ • α)) = (v * w) • (w⁻¹ • α) := by
        rw [← mul_smul]
        congr 1
        rw [hw]
        group
      have e : z • (v • (w⁻¹ • α)) = v • α := by
        rw [h1, mul_smul, smul_inv_smul]
      exact ⟨v • (w⁻¹ • α), ⟨w⁻¹ • α, hsub_inv α hα, rfl⟩, e⟩
  have hmap := map_conj_rootSpan (L := L) z (S := S0) (fun γ hγ => by
    obtain ⟨α, hα, rfl⟩ := hγ
    exact IsRoot.smul hα.1 v)
  rw [hmap, hz_image]

theorem ntpTG_conj_xUnit
    {L : Type} [Field L] (h2 : (2 : L) = 0)
    (v z : WeylGroup Tag.E6) (ε : ℕ)
    (hz : ∀ k : Fin Tag.D4.rank,
      z • (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) =
        v • (Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1))
    (k : Fin Tag.D4.rank) (c : L) :
    canonicalRep (coxeterSystem Tag.E6) L z *
        (canonicalRep (coxeterSystem Tag.E6) L v * xUnit Tag.E6 L (d4Idx k) c *
          (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹ =
      canonicalRep (coxeterSystem Tag.E6) L v *
        xUnit Tag.E6 L (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ := by
  have hroot : IsRoot Tag.E6 (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) :=
    IsRoot.smul (isRoot_single Tag.E6 (d4Idx k)) v
  have h1 : canonicalRep (coxeterSystem Tag.E6) L v * xUnit Tag.E6 L (d4Idx k) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ =
      pinnedX Tag.E6 L (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) c := by
    rw [← pinnedX_single]
    exact canonicalRep_mul_pinnedX_mul_inv_of_two h2 v (isRoot_single Tag.E6 (d4Idx k)) c
  have h2' : canonicalRep (coxeterSystem Tag.E6) L z *
        pinnedX Tag.E6 L (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) c *
        (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹ =
      pinnedX Tag.E6 L (v • (Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1 :
        Fin Tag.E6.rank → ℤ)) c := by
    rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 z hroot c, hz k]
  have h3 : canonicalRep (coxeterSystem Tag.E6) L v *
        xUnit Tag.E6 L (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ =
      pinnedX Tag.E6 L (v • (Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1 :
        Fin Tag.E6.rank → ℤ)) c := by
    rw [← pinnedX_single]
    exact canonicalRep_mul_pinnedX_mul_inv_of_two h2 v
      (isRoot_single Tag.E6 (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k))) c
  calc canonicalRep (coxeterSystem Tag.E6) L z *
        (canonicalRep (coxeterSystem Tag.E6) L v * xUnit Tag.E6 L (d4Idx k) c *
          (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹
      = canonicalRep (coxeterSystem Tag.E6) L z *
          (pinnedX Tag.E6 L (v • (Pi.single (d4Idx k) 1 :
            Fin Tag.E6.rank → ℤ)) c) *
          (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹ := by rw [h1]
    _ = pinnedX Tag.E6 L (v • (Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1 :
          Fin Tag.E6.rank → ℤ)) c := h2'
    _ = canonicalRep (coxeterSystem Tag.E6) L v *
          xUnit Tag.E6 L (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) c *
          (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ := h3.symm

theorem ntpTG_conj_yUnit
    {L : Type} [Field L] (h2 : (2 : L) = 0)
    (v z : WeylGroup Tag.E6) (ε : ℕ)
    (hz : ∀ k : Fin Tag.D4.rank,
      z • (v • (Pi.single (d4Idx k) 1 : Fin Tag.E6.rank → ℤ)) =
        v • (Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1))
    (k : Fin Tag.D4.rank) (c : L) :
    canonicalRep (coxeterSystem Tag.E6) L z *
        (canonicalRep (coxeterSystem Tag.E6) L v * yUnit Tag.E6 L (d4Idx k) c *
          (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹ =
      canonicalRep (coxeterSystem Tag.E6) L v *
        yUnit Tag.E6 L (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ := by
  have hroot : IsRoot Tag.E6
      (v • (-Pi.single (d4Idx k) 1) : Fin Tag.E6.rank → ℤ) :=
    IsRoot.smul (IsRoot.neg (isRoot_single Tag.E6 (d4Idx k))) v
  have h1 : canonicalRep (coxeterSystem Tag.E6) L v * yUnit Tag.E6 L (d4Idx k) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ =
      pinnedX Tag.E6 L (v • (-Pi.single (d4Idx k) 1) :
        Fin Tag.E6.rank → ℤ) c := by
    rw [← pinnedX_neg_single]
    exact canonicalRep_mul_pinnedX_mul_inv_of_two h2 v
      (IsRoot.neg (isRoot_single Tag.E6 (d4Idx k))) c
  have hzneg : z • (v • (-Pi.single (d4Idx k) 1) : Fin Tag.E6.rank → ℤ) =
      v • (-Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1) := by
    rw [smul_neg, smul_neg, hz k, ← smul_neg]
  have h2' : canonicalRep (coxeterSystem Tag.E6) L z *
        pinnedX Tag.E6 L (v • (-Pi.single (d4Idx k) 1) :
          Fin Tag.E6.rank → ℤ) c *
        (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹ =
      pinnedX Tag.E6 L (v • (-Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1) :
        Fin Tag.E6.rank → ℤ) c := by
    rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 z hroot c, hzneg]
  have h3 : canonicalRep (coxeterSystem Tag.E6) L v *
        yUnit Tag.E6 L (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) c *
        (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ =
      pinnedX Tag.E6 L (v • (-Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1) :
        Fin Tag.E6.rank → ℤ) c := by
    rw [← pinnedX_neg_single]
    exact canonicalRep_mul_pinnedX_mul_inv_of_two h2 v
      (IsRoot.neg (isRoot_single Tag.E6 (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)))) c
  calc canonicalRep (coxeterSystem Tag.E6) L z *
        (canonicalRep (coxeterSystem Tag.E6) L v * yUnit Tag.E6 L (d4Idx k) c *
          (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹) *
        (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹
      = canonicalRep (coxeterSystem Tag.E6) L z *
          (pinnedX Tag.E6 L (v • (-Pi.single (d4Idx k) 1) :
            Fin Tag.E6.rank → ℤ) c) *
          (canonicalRep (coxeterSystem Tag.E6) L z)⁻¹ := by rw [h1]
    _ = pinnedX Tag.E6 L (v • (-Pi.single (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) 1) :
          Fin Tag.E6.rank → ℤ) c := h2'
    _ = canonicalRep (coxeterSystem Tag.E6) L v *
          yUnit Tag.E6 L (d4Idx ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ ε) k)) c *
          (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ := h3.symm

end CFSG.StandardType.NTPlane
