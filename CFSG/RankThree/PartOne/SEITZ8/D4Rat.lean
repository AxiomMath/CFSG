module

public import CFSG.RankThree.PartOne.SEITZ7.D4AB
public import CFSG.RankThree.PartOne.SEITZ8.D4Span

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7

variable {K : Type} [Field K]

section Entrywise


theorem coe_xe_simple_end (i : Fin d4.rank) {p : ℕ} (hp : d4Root p = Pi.single i 1)
    (c : K) : (((xe p c : adjointGroup d4 K) : ModGL d4 K) : Module.End K (RootModule d4 K)) =
      xOp d4 K i c :=
  LinearMap.ext fun x => xe_smul_simple i hp c x

theorem coe_xe_neg_end (i : Fin d4.rank) {p : ℕ} (hp : d4Root p = -Pi.single i 1) (c : K) :
    (((xe p c : adjointGroup d4 K) : ModGL d4 K) : Module.End K (RootModule d4 K)) =
      yOp d4 K i c :=
  LinearMap.ext fun x => xe_smul_neg_simple i hp c x

theorem entrywise_xe_simple (δ : K →+* K) (i : Fin d4.rank) {p : ℕ}
    (hp : d4Root p = Pi.single i 1) (c : K) :
    Units.map (entrywiseHom δ) ((xe p c : adjointGroup d4 K) : ModGL d4 K) =
      ((xe p (δ c) : adjointGroup d4 K) : ModGL d4 K) := by
  apply Units.ext
  rw [Units.coe_map]
  show entrywise δ _ = _
  rw [coe_xe_simple_end i hp, coe_xe_simple_end i hp, CFSG.LieType.Chevalley.entrywise_xOp]

theorem entrywise_xe_neg (δ : K →+* K) (i : Fin d4.rank) {p : ℕ}
    (hp : d4Root p = -Pi.single i 1) (c : K) :
    Units.map (entrywiseHom δ) ((xe p c : adjointGroup d4 K) : ModGL d4 K) =
      ((xe p (δ c) : adjointGroup d4 K) : ModGL d4 K) := by
  apply Units.ext
  rw [Units.coe_map]
  show entrywise δ _ = _
  rw [coe_xe_neg_end i hp, coe_xe_neg_end i hp, CFSG.LieType.Chevalley.entrywise_yOp]

theorem entrywise_weylElement (δ : K →+* K) (i : Fin d4.rank) :
    Units.map (entrywiseHom δ) ((weylElement d4 K i : adjointGroup d4 K) : ModGL d4 K) =
      ((weylElement d4 K i : adjointGroup d4 K) : ModGL d4 K) := by
  apply Units.ext
  rw [Units.coe_map]
  show entrywise δ ((weylElt d4 K i 1 : ModGL d4 K) : Module.End K (RootModule d4 K)) = _
  rw [coe_weylElt, entrywise_mul, entrywise_mul, CFSG.LieType.Chevalley.entrywise_xOp,
    CFSG.LieType.Chevalley.entrywise_yOp]
  simp
  rfl

end Entrywise

@[expose] def Rδ (σ δ : K →+* K) : Subgroup (adjointGroup d4 K) where
  carrier := {g | g ∈ twistedGroup σ ∧
    Units.map (entrywiseHom δ) (g : ModGL d4 K) = (g : ModGL d4 K)}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(twistedGroup σ).mul_mem ha hb, ?_⟩
    rw [Subgroup.coe_mul, map_mul, ha', hb']
  one_mem' := ⟨(twistedGroup σ).one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(twistedGroup σ).inv_mem ha, ?_⟩
    rw [Subgroup.coe_inv, map_inv, ha']

section Hyp

variable [CharP K 2] {σ δ : K →+* K} {k : Subfield K}

omit [CharP K 2] in
theorem xe_mem_twistedGroup (hσ : ∀ c, σ (σ (σ c)) = c) {p : ℕ} (hp : p < 24)
    (hfix : rho (d4Root p) = d4Root p) {c : K} (hc : σ c = c) :
    (xe p c : adjointGroup d4 K) ∈ twistedGroup σ :=
  twistedRootSubgroupD4_le_twistedGroup σ (isRoot_proj (isRoot_d4 hp))
    (xPar_mem_of_fixed hσ (isRoot_d4 hp) hfix hc)

theorem spanHyp_Rδ (hσ : ∀ c, σ (σ (σ c)) = c) (hcomm : ∀ c, δ (σ c) = σ (δ c))
    (hk : ∀ c ∈ k, δ c = c) (hRat : Rat3 σ k) : SpanHyp σ k (Rδ σ δ) := by
  refine ⟨hRat, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have := (slShort σ hσ (sl2Upper a)).2
      rw [slShort_upper_xA σ hσ] at this
      exact this
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul,
        entrywise_xe_simple δ (nd 0) d4Root_simple_0, entrywise_xe_simple δ (nd 1) d4Root_simple_1,
        entrywise_xe_simple δ (nd 3) d4Root_simple_3, hk a ha, hcomm, hk a ha, hcomm, hcomm,
        hk a ha]
  · refine ⟨?_, ?_⟩
    · have := (slShort σ hσ (sl2Lower a)).2
      rw [slShort_lower_xAm σ hσ] at this
      exact this
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul,
        entrywise_xe_neg δ (nd 0) d4Root_neg_0, entrywise_xe_neg δ (nd 1) d4Root_neg_1,
        entrywise_xe_neg δ (nd 3) d4Root_neg_3, hk a ha, hcomm, hk a ha, hcomm, hcomm,
        hk a ha]
  · refine ⟨xe_mem_twistedGroup hσ (by norm_num) (by decide) (map_one σ), ?_⟩
    rw [entrywise_xe_simple δ (nd 2) d4Root_simple_2, map_one]
  · refine ⟨xe_mem_twistedGroup hσ (by norm_num) (by decide) (map_one σ), ?_⟩
    rw [entrywise_xe_neg δ (nd 2) d4Root_neg_2, map_one]
  · refine ⟨?_, entrywise_weylElement δ (nd 2)⟩
    have h := (nHat σ (ng 0)).2
    rw [nHat_val, nHatE_zero] at h
    exact h
  · refine ⟨?_, ?_⟩
    · have h := (nHat σ (ng 1)).2
      rw [nHat_val, nHatE_one] at h
      exact h
    rw [show ((weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) :
      adjointGroup d4 K) : ModGL d4 K) = (weylElement d4 K (nd 0) : ModGL d4 K) *
        (weylElement d4 K (nd 1) : ModGL d4 K) * (weylElement d4 K (nd 3) : ModGL d4 K) from rfl,
      map_mul, map_mul, entrywise_weylElement, entrywise_weylElement, entrywise_weylElement]

end Hyp

end CFSG.RankThree.PartOne.SEITZ8
