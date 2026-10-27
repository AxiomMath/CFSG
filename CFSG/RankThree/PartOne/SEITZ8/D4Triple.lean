module

public import CFSG.RankThree.PartOne.SEITZ8.D4Form

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4

variable {K : Type} [Field K]

noncomputable abbrev xe (p : ℕ) (c : K) : adjointGroup d4 K :=
  xPar (rootOperatorFamily d4) (d4Root p) c

section Smul


theorem xe_smul_simple (i : Fin d4.rank) {p : ℕ} (hp : d4Root p = Pi.single i 1) (c : K)
    (x : RootModule d4 K) : (xe p c : adjointGroup d4 K) • x = xOp d4 K i c x := by
  simp only [xe, hp, xPar_simple]
  show ((rootOperatorFamily d4).elt K (simpleRoot d4 i) c) x = _
  rw [(rootOperatorFamily d4).elt_simple]

theorem xe_smul_neg_simple (i : Fin d4.rank) {p : ℕ} (hp : d4Root p = -Pi.single i 1) (c : K)
    (x : RootModule d4 K) : (xe p c : adjointGroup d4 K) • x = yOp d4 K i c x := by
  simp only [xe, hp, xPar_neg_simple]
  show ((rootOperatorFamily d4).elt K (-simpleRoot d4 i) c) x = _
  rw [(rootOperatorFamily d4).elt_neg_simple]

theorem d4Root_simple_0 : d4Root 0 = Pi.single (nd 0) 1 := by decide
theorem d4Root_simple_1 : d4Root 1 = Pi.single (nd 1) 1 := by decide
theorem d4Root_simple_2 : d4Root 2 = Pi.single (nd 2) 1 := by decide
theorem d4Root_simple_3 : d4Root 3 = Pi.single (nd 3) 1 := by decide
theorem d4Root_neg_0 : d4Root 4 = -Pi.single (nd 0) 1 := by decide
theorem d4Root_neg_1 : d4Root 6 = -Pi.single (nd 1) 1 := by decide
theorem d4Root_neg_2 : d4Root 8 = -Pi.single (nd 2) 1 := by decide
theorem d4Root_neg_3 : d4Root 10 = -Pi.single (nd 3) 1 := by decide

end Smul

@[expose] def xg (i : Fin d4.rank) (k : ℕ) : DIdx → Col (Tag.rootCertificate d4) :=
  xCol (Tag.rootCertificate d4) (Tag.stringData d4) i k

@[expose] def yg (i : Fin d4.rank) (k : ℕ) : DIdx → Col (Tag.rootCertificate d4) :=
  yCol (Tag.rootCertificate d4) (Tag.stringData d4) i k

@[expose] def comp3 (F : Fin d4.rank → ℕ → DIdx → Col (Tag.rootCertificate d4))
    (m₀ m₁ m₃ : ℕ) (c : DIdx) : Col (Tag.rootCertificate d4) :=
  bindCol (Tag.rootCertificate d4) (F (nd 0) m₀) (bindCol (Tag.rootCertificate d4) (F (nd 1) m₁)
    (bindCol (Tag.rootCertificate d4) (F (nd 3) m₃) (some (c, 1))))

section Expand


theorem op_toVec (Op : Fin d4.rank → K → Module.End K (RootModule d4 K))
    (Co : Fin d4.rank → ℕ → Module.End K (RootModule d4 K))
    (F : Fin d4.rank → ℕ → DIdx → Col (Tag.rootCertificate d4))
    (hOp : ∀ i c, Op i c = ∑ k ∈ Finset.range 4, c ^ k • Co i k)
    (hCo : ∀ i k b, Co i k (Finsupp.single (toLabel (Tag.rootCertificate_check d4) b) 1) =
      toVec (Tag.rootCertificate_check d4) K (F i k b))
    (i : Fin d4.rank) (t : K) (u : Col (Tag.rootCertificate d4)) :
    Op i t (toVec (Tag.rootCertificate_check d4) K u) =
      ∑ k ∈ Finset.range 4, t ^ k • toVec (Tag.rootCertificate_check d4) K
        (bindCol (Tag.rootCertificate d4) (F i k) u) := by
  rw [hOp]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_toVec (Tag.rootCertificate_check d4) K (hCo i k)]

theorem triple_expand (Op : Fin d4.rank → K → Module.End K (RootModule d4 K))
    (Co : Fin d4.rank → ℕ → Module.End K (RootModule d4 K))
    (F : Fin d4.rank → ℕ → DIdx → Col (Tag.rootCertificate d4))
    (hOp : ∀ i c, Op i c = ∑ k ∈ Finset.range 4, c ^ k • Co i k)
    (hCo : ∀ i k b, Co i k (Finsupp.single (toLabel (Tag.rootCertificate_check d4) b) 1) =
      toVec (Tag.rootCertificate_check d4) K (F i k b))
    (t₀ t₁ t₃ : K) (c : DIdx) :
    Op (nd 0) t₀ (Op (nd 1) t₁ (Op (nd 3) t₃
      (Finsupp.single (toLabel (Tag.rootCertificate_check d4) c) 1))) =
      ∑ m ∈ Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 4,
        (t₃ ^ m.1 * t₁ ^ m.2.1 * t₀ ^ m.2.2) • toVec (Tag.rootCertificate_check d4) K
          (comp3 F m.2.2 m.2.1 m.1 c) := by
  have e1 : Finsupp.single (toLabel (Tag.rootCertificate_check d4) c) (1 : K) =
      toVec (Tag.rootCertificate_check d4) K (some (c, 1)) := by
    rw [toVec_some, Int.cast_one, one_smul]
  have step : ∀ (j : Fin d4.rank) (s : K) (u : Col (Tag.rootCertificate d4)),
      Op j s (toVec (Tag.rootCertificate_check d4) K u) =
        ∑ k ∈ Finset.range 4, s ^ k • toVec (Tag.rootCertificate_check d4) K
          (bindCol (Tag.rootCertificate d4) (F j k) u) := fun j s u =>
    op_toVec Op Co F hOp hCo j s u
  calc Op (nd 0) t₀ (Op (nd 1) t₁ (Op (nd 3) t₃
        (Finsupp.single (toLabel (Tag.rootCertificate_check d4) c) 1)))
      = ∑ k₃ ∈ Finset.range 4, t₃ ^ k₃ • Op (nd 0) t₀ (Op (nd 1) t₁
          (toVec (Tag.rootCertificate_check d4) K
            (bindCol (Tag.rootCertificate d4) (F (nd 3) k₃) (some (c, 1))))) := by
        rw [e1, step (nd 3) t₃]
        simp only [map_sum, map_smul]
    _ = ∑ k₃ ∈ Finset.range 4, t₃ ^ k₃ • ∑ k₁ ∈ Finset.range 4, t₁ ^ k₁ •
          ∑ k₀ ∈ Finset.range 4, t₀ ^ k₀ • toVec (Tag.rootCertificate_check d4) K
            (comp3 F k₀ k₁ k₃ c) := by
        refine Finset.sum_congr rfl fun k₃ _ => ?_
        congr 1
        rw [step (nd 1) t₁]
        simp only [map_sum, map_smul]
        refine Finset.sum_congr rfl fun k₁ _ => ?_
        congr 1
        rw [step (nd 0) t₀]
        rfl
    _ = ∑ m ∈ Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 4,
        (t₃ ^ m.1 * t₁ ^ m.2.1 * t₀ ^ m.2.2) • toVec (Tag.rootCertificate_check d4) K
          (comp3 F m.2.2 m.2.1 m.1 c) := by
        rw [Finset.sum_product]
        simp only [Finset.sum_product]
        refine Finset.sum_congr rfl fun k₃ _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun k₁ _ => ?_
        simp only [Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun k₀ _ => ?_
        congr 1
        ring

theorem triple_expand_x (t₀ t₁ t₃ : K) (c : DIdx) :
    xOp d4 K (nd 0) t₀ (xOp d4 K (nd 1) t₁ (xOp d4 K (nd 3) t₃
      (Finsupp.single (toLabel (Tag.rootCertificate_check d4) c) 1))) =
      ∑ m ∈ Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 4,
        (t₃ ^ m.1 * t₁ ^ m.2.1 * t₀ ^ m.2.2) • toVec (Tag.rootCertificate_check d4) K
          (comp3 xg m.2.2 m.2.1 m.1 c) :=
  triple_expand (xOp d4 K) (xCoeff d4 K) xg (fun i c => xOp_eq_sum_xCoeff i c)
    (fun i k b => xCoeff_toLabel (Tag.rootCertificate_check d4) K (Tag.stringData_check d4) i k b)
    t₀ t₁ t₃ c

theorem triple_expand_y (t₀ t₁ t₃ : K) (c : DIdx) :
    yOp d4 K (nd 0) t₀ (yOp d4 K (nd 1) t₁ (yOp d4 K (nd 3) t₃
      (Finsupp.single (toLabel (Tag.rootCertificate_check d4) c) 1))) =
      ∑ m ∈ Finset.range 4 ×ˢ Finset.range 4 ×ˢ Finset.range 4,
        (t₃ ^ m.1 * t₁ ^ m.2.1 * t₀ ^ m.2.2) • toVec (Tag.rootCertificate_check d4) K
          (comp3 yg m.2.2 m.2.1 m.1 c) :=
  triple_expand (yOp d4 K) (yCoeff d4 K) yg (fun i c => yOp_eq_sum_yCoeff i c)
    (fun i k b => yCoeff_toLabel (Tag.rootCertificate_check d4) K (Tag.stringData_check d4) i k b)
    t₀ t₁ t₃ c

end Expand

end CFSG.RankThree.PartOne.SEITZ8
