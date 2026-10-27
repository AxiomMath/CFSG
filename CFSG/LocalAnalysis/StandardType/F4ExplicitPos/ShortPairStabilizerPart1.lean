module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PairStabilizerNativePart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3AlgebraicPart2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.ShortPairStabilizer

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.SeitzReduction CFSG.LieType.AlgebraicGroups WithConv
  CFSG.LieType.Ree.ReeTag

open scoped CFSG.ConvolutionPoints

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.StandardType.F4ExplicitPos.BruhatNo117 CFSG.StandardType.F4ExplicitPos.UnipotentNo117

open CFSG.StandardType.F4ExplicitPos.PairNormalizerNo117

open CFSG.StandardType.F4ExplicitPos.PairStabilizerNative

open CFSG.StandardType.F4ExplicitPos.B3Algebraic

open scoped Pointwise

variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

abbrev A : Subgroup (ModGL Tag.F4 Ω) := adjointGroup Tag.F4 Ω

abbrev sigmaA
    {Ω : Type} [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] : A Ω →* A Ω := sigmaΩ Ω

abbrev weylA
    {Ω : Type} [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] (j : Fin Tag.F4.rank) (v : Ωˣ) : A Ω :=
  ⟨weylElt Tag.F4 Ω j v, weylElt_mem_adjointGroup j v⟩

abbrev UA
    (α : Fin Tag.F4.rank → ℤ) : Subgroup (A Ω) :=
  Subgroup.closure (Set.range fun c : Ω =>
    (⟨pinnedX Tag.F4 Ω α c, pinnedX_mem_adjointGroup α c⟩ : A Ω))

abbrev TA : Subgroup (A Ω) :=
  Subgroup.closure (Set.range fun p : Fin Tag.F4.rank × Ωˣ =>
    torusElement Tag.F4 Ω p.1 p.2)

abbrev RSA
    (S : Set (Fin Tag.F4.rank → ℤ)) : Subgroup (A Ω) :=
  ⨆ α ∈ S, UA Ω α

abbrev δ : Fin Tag.F4.rank → ℤ := F4.dualRoot (highRoot Tag.F4)

abbrev Sstar : Set (Fin Tag.F4.rank → ℤ) := F4.dualRoot '' S_J

abbrev LA
    : Subgroup (A Ω) := TA Ω ⊔ RSA Ω S_J

abbrev MstarA
    : Subgroup (A Ω) := TA Ω ⊔ RSA Ω (Sstar)

abbrev Mstar
    : Subgroup (ModGL Tag.F4 Ω) :=
  torusGroup Tag.F4 Ω ⊔ rootSpan Tag.F4 Ω (Sstar)

theorem UA_map_incl
    (α : Fin Tag.F4.rank → ℤ) :
    (UA Ω α).map (A Ω).subtype = rootSubgroup Tag.F4 Ω α := by
  rw [UA, MonoidHom.map_closure]
  congr 1
  rw [← Set.range_comp]
  rfl

theorem TA_map_incl :
    (TA Ω).map (A Ω).subtype = torusGroup Tag.F4 Ω := by
  rw [TA, MonoidHom.map_closure]
  congr 1
  rw [← Set.range_comp]
  rfl

theorem RSA_map_incl
    (S : Set (Fin Tag.F4.rank → ℤ)) :
    (RSA Ω S).map (A Ω).subtype = rootSpan Tag.F4 Ω S := by
  unfold RSA rootSpan
  simp_rw [Subgroup.map_iSup, UA_map_incl]

theorem UA_subgroupOf
    (α : Fin Tag.F4.rank → ℤ) :
    (rootSubgroup Tag.F4 Ω α).subgroupOf (A Ω) = UA Ω α := by
  apply Subgroup.map_injective (f := (A Ω).subtype) (A Ω).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, UA_map_incl,
    inf_eq_left.2 (rootSubgroup_le_adjointGroup α)]

theorem normalizer_UA_map_incl
    (α : Fin Tag.F4.rank → ℤ) :
    (Subgroup.normalizer (UA Ω α)).map (A Ω).subtype =
      Subgroup.normalizer (rootSubgroup Tag.F4 Ω α : Set (ModGL Tag.F4 Ω)) ⊓ A Ω := by
  conv_lhs => rw [← UA_subgroupOf Ω α]
  rw [← Subgroup.subgroupOf_normalizer_eq (rootSubgroup_le_adjointGroup α),
    Subgroup.subgroupOf_map_subtype]

theorem sigmaΩ_xElement
    (i : Fin Tag.F4.rank) (c : Ω) :
    sigmaA (xElement i c) = xElement (F4.perm i) (c ^ F4.exponent i) :=
  CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exceptionalEndoNarrow_xElement
    (CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.F4_prime_cast_eq_zero Ω)
    (f4_shortFaithful_algebraic Ω) i c

theorem sigmaΩ_yElement
    (i : Fin Tag.F4.rank) (c : Ω) :
    sigmaA (yElement i c) = yElement (F4.perm i) (c ^ F4.exponent i) :=
  CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exceptionalEndoNarrow_yElement
    (CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.F4_prime_cast_eq_zero Ω)
    (f4_shortFaithful_algebraic Ω) i c

theorem sigmaΩ_weylElementOf
    (i : Fin Tag.F4.rank) (u : Ωˣ) :
    sigmaA (weylA i u) =
      weylA (F4.perm i) (u ^ F4.exponent i) := by
  have hdecomp (j : Fin Tag.F4.rank) (v : Ωˣ) :
      weylA j v =
        xElement j (v : Ω) * yElement j
            (-(((v⁻¹ : Ωˣ)) : Ω)) * xElement j (v : Ω) :=
    Subtype.ext (CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul j v)
  have hx : (u : Ω) ^ F4.exponent i = (((u ^ F4.exponent i : Ωˣ) : Ω)) :=
    (Units.val_pow_eq_pow_val _ _).symm
  have hnegK : (-1 : Ω) ^ F4.exponent i = -1 := by
    rw [CharTwo.neg_eq 1, one_pow]
  have hy : (-(((u⁻¹ : Ωˣ)) : Ω)) ^ F4.exponent i =
      -((((u ^ F4.exponent i)⁻¹ : Ωˣ)) : Ω) := by
    rw [neg_pow, hnegK, neg_one_mul, ← inv_pow, Units.val_pow_eq_pow_val]
  simp only [hdecomp, map_mul, sigmaΩ_xElement, sigmaΩ_yElement, hx, hy]
  exact (hdecomp (F4.perm i) (u ^ F4.exponent i)).symm

theorem sigmaΩ_torusElement
    (i : Fin Tag.F4.rank) (u : Ωˣ) :
    sigmaA (torusElement Tag.F4 Ω i u) =
      torusElement Tag.F4 Ω (F4.perm i) (u ^ F4.exponent i) := by
  have h : ∀ (j : Fin Tag.F4.rank) (v : Ωˣ),
      torusElement Tag.F4 Ω j v = weylA j v * weylA j (-1) :=
    fun _ _ => rfl
  have hneg : ((-1 : Ωˣ) ^ F4.exponent i) = -1 := by
    have h1 : (-1 : Ωˣ) = 1 :=
      Units.ext (by rw [Units.val_neg, Units.val_one, CharTwo.neg_eq])
    rw [h1, one_pow]
  rw [h i u]
  simp only [map_mul, sigmaΩ_weylElementOf, hneg]
  exact (h (F4.perm i) (u ^ F4.exponent i)).symm

theorem exists_unit_sq_charTwo (s : Ωˣ) : ∃ u : Ωˣ, u ^ 2 = s := by
  obtain ⟨d, hd⟩ := exists_sq_eq_charTwo_algebraic Ω (s : Ω)
  have hd0 : d ≠ 0 := by
    intro h0
    subst h0
    exact s.ne_zero (by simpa [pow_two] using hd.symm)
  exact ⟨Units.mk0 d hd0, Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hd])⟩

theorem TA_map_sigma :
    (TA Ω).map sigmaA = TA Ω := by
  have hTA : TA Ω = Subgroup.closure (Set.range fun p : Fin Tag.F4.rank × Ωˣ =>
      torusElement Tag.F4 Ω p.1 p.2) := rfl
  rw [hTA, MonoidHom.map_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, ⟨p, rfl⟩, rfl⟩
    rw [sigmaΩ_torusElement]
    exact Subgroup.subset_closure ⟨(F4.perm p.1, p.2 ^ F4.exponent p.1), rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨q, rfl⟩
    set i := F4.perm.symm q.1
    rcases CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exponent_F4_eq_one_or_two i with he | he
    · refine Subgroup.subset_closure
        ⟨torusElement Tag.F4 Ω i q.2, ⟨⟨(i, q.2), rfl⟩, ?_⟩⟩
      rw [sigmaΩ_torusElement Ω i q.2, he, pow_one]
      exact congrArg (fun j => torusElement Tag.F4 Ω j q.2) (F4.perm.apply_symm_apply q.1)
    · obtain ⟨u, hu⟩ := exists_unit_sq_charTwo Ω q.2
      refine Subgroup.subset_closure
        ⟨torusElement Tag.F4 Ω i u, ⟨⟨(i, u), rfl⟩, ?_⟩⟩
      rw [sigmaΩ_torusElement Ω i u, he, hu]
      exact congrArg (fun j => torusElement Tag.F4 Ω j q.2) (F4.perm.apply_symm_apply q.1)

theorem UA_map_sigma
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α) :
    (UA Ω α).map sigmaA = UA Ω (F4.dualRoot α) := by
  have hUA : ∀ β, UA Ω β = Subgroup.closure (Set.range fun c : Ω =>
      (⟨pinnedX Tag.F4 Ω β c, pinnedX_mem_adjointGroup β c⟩ : A Ω)) := fun _ => rfl
  rw [hUA α, hUA (F4.dualRoot α), MonoidHom.map_closure]
  congr 1
  rw [← Set.range_comp]
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c ^ F4.exponent (pinnedData F4.tag α).1, ?_⟩
    exact (sigmaΩ_pinnedX Ω hα c).symm
  · rintro ⟨d, rfl⟩
    rcases CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exponent_F4_eq_one_or_two
        (pinnedData F4.tag α).1 with he | he
    · refine ⟨d, ?_⟩
      refine Subtype.ext ?_
      have h := congrArg Subtype.val (sigmaΩ_pinnedX Ω hα d)
      rw [he, pow_one] at h
      exact h
    · obtain ⟨c, hc⟩ := exists_sq_eq_charTwo_algebraic Ω d
      refine ⟨c, ?_⟩
      refine Subtype.ext ?_
      have h := congrArg Subtype.val (sigmaΩ_pinnedX Ω hα c)
      rw [he, hc] at h
      exact h

theorem isRoot_of_mem_S_J {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ S_J) :
    IsRoot Tag.F4 α := by
  rcases hα with ⟨j, -, h | h⟩
  · rw [h]; exact isRoot_single Tag.F4 j
  · rw [h]; exact IsRoot.neg (isRoot_single Tag.F4 j)

theorem RSA_map_sigma :
    (RSA Ω S_J).map sigmaA = RSA Ω Sstar := by
  have hRS : ∀ S : Set (Fin Tag.F4.rank → ℤ), RSA Ω S = ⨆ α ∈ S, UA Ω α := fun _ => rfl
  rw [hRS S_J, hRS Sstar]
  simp_rw [Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le; intro α
    apply iSup_le; intro hα
    rw [UA_map_sigma Ω (isRoot_of_mem_S_J hα)]
    exact le_iSup₂_of_le (F4.dualRoot α) ⟨α, hα, rfl⟩ le_rfl
  · apply iSup_le; intro β
    apply iSup_le; intro hβ
    obtain ⟨α, hα, rfl⟩ := hβ
    rw [← UA_map_sigma Ω (isRoot_of_mem_S_J hα)]
    exact le_iSup₂_of_le α hα le_rfl

theorem LA_map_sigma :
    (LA Ω).map sigmaA = MstarA Ω := by
  have hLA : LA Ω = TA Ω ⊔ RSA Ω S_J := rfl
  have hMs : MstarA Ω = TA Ω ⊔ RSA Ω Sstar := rfl
  rw [hLA, hMs, Subgroup.map_sup, TA_map_sigma, RSA_map_sigma]

theorem LA_map_incl
    : (LA Ω).map (A Ω).subtype = Lθ Tag.F4 Ω := by
  have hLA : LA Ω = TA Ω ⊔ RSA Ω S_J := rfl
  have hsup : (TA Ω ⊔ RSA Ω S_J).map (A Ω).subtype =
      (TA Ω).map (A Ω).subtype ⊔ (RSA Ω S_J).map (A Ω).subtype :=
    Subgroup.map_sup (TA Ω) (RSA Ω S_J) (A Ω).subtype
  rw [hLA, hsup, TA_map_incl Ω, RSA_map_incl Ω S_J]
  exact (f4_Lθ_eq_torus_sup_rootSpan (K := Ω)).symm

theorem MstarA_map_incl
    : (MstarA Ω).map (A Ω).subtype = Mstar Ω := by
  have hMs : MstarA Ω = TA Ω ⊔ RSA Ω Sstar := rfl
  have hsup : (TA Ω ⊔ RSA Ω Sstar).map (A Ω).subtype =
      (TA Ω).map (A Ω).subtype ⊔ (RSA Ω Sstar).map (A Ω).subtype :=
    Subgroup.map_sup (TA Ω) (RSA Ω Sstar) (A Ω).subtype
  rw [hMs, hsup, TA_map_incl Ω, RSA_map_incl Ω Sstar]

abbrev KlongA : Subgroup (A Ω) :=
  Subgroup.normalizer (UA Ω (highRoot Tag.F4)) ⊓
    Subgroup.normalizer (UA Ω (-highRoot Tag.F4))

abbrev KshortA : Subgroup (A Ω) :=
  Subgroup.normalizer (UA Ω (δ)) ⊓ Subgroup.normalizer (UA Ω (-δ))

theorem KlongA_eq_LA :
    KlongA Ω = LA Ω := by
  have hKl : KlongA Ω = Subgroup.normalizer (UA Ω (highRoot Tag.F4)) ⊓
      Subgroup.normalizer (UA Ω (-highRoot Tag.F4)) := rfl
  apply Subgroup.map_injective (f := (A Ω).subtype) (A Ω).subtype_injective
  rw [hKl, Subgroup.map_inf _ _ (A Ω).subtype (A Ω).subtype_injective,
    normalizer_UA_map_incl Ω (highRoot Tag.F4), normalizer_UA_map_incl Ω (-highRoot Tag.F4),
    LA_map_incl Ω]
  trans (adjointGroup Tag.F4 Ω ⊓
      Subgroup.normalizer (rootSubgroup Tag.F4 Ω (highRoot Tag.F4) : Set (ModGL Tag.F4 Ω)) ⊓
      Subgroup.normalizer (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4) : Set (ModGL Tag.F4 Ω)))
  · ac_rfl
  · exact f4_pair_stabilizer_eq_Lθ (K := Ω)

end CFSG.StandardType.F4ExplicitPos.ShortPairStabilizer
end

end
