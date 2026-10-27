module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart7
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart26
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCenter
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCartanAdj
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart15

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart25

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.C3Comm

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.Universal.Symplectic
      CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.Timmesfeld.LieEmbed

open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem eq_one_of_nsmul_mem_roots_without117
    {α : Fin 3 → ℤ} {k : ℕ}
    (h : k • α ∈ roots (isFiniteType_cartanC 3) ∅) : k = 1 := by
  rw [← isRoot_c3ToF4_iff, map_nsmul] at h
  exact eq_one_of_isRoot_nsmul_without117 h

theorem stringNorm_eq_one_or_two (β γ : Fin (Tag.rank .F4) → ℤ) :
    stringNorm β γ = 1 ∨ stringNorm β γ = 2 := by
  unfold stringNorm
  split <;> simp

theorem intCast_eq_nat_of_natAbs {z : ℤ} {n : ℕ} (h : z.natAbs = n) (hn : n = 1 ∨ n = 2) :
    (z : K) = (n : K) := by
  rcases hn with rfl | rfl
  · simpa using intCast_eq_one_of_natAbs (K := K) h
  · rw [intCast_eq_zero_of_natAbs (K := K) h, CharP.cast_eq_zero K 2]

theorem coeff11_without117_eq_spCommC
    {α β : Fin 3 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC 3) ∅) (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅)
    (hne : α ≠ β) (hαβ : α + β ≠ 0) (hr : α + β ∈ roots (isFiniteType_cartanC 3) ∅) :
    (RootOperatorFamily'.coeff11_without117 (rootOperatorFamily .F4)
        CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117
        ⟨c3ToF4 α, isRoot_c3ToF4 hα⟩ ⟨c3ToF4 β, isRoot_c3ToF4 hβ⟩ : K)
      = (Sp.commC α β (1, 1) : K) := by
  have hra : (1 : ℕ) • α + 1 • β ∈ roots (isFiniteType_cartanC 3) ∅ := by simpa using hr
  have hroot : CFSG.Blueprint.Chevalley.IsRoot .F4 (c3ToF4 α + c3ToF4 β) := by
    rw [← map_add]
    exact isRoot_c3ToF4 (by simpa only [one_smul] using hr)
  have hγ : c3ToF4 β ≠ -c3ToF4 α := by
    intro h
    refine hαβ ?_
    have h1 : c3ToF4 β = c3ToF4 (-α) := h.trans (map_neg _ _).symm
    rw [c3ToF4_injective h1, add_neg_cancel]
  rw [C3Exact.cast_spCommC_eq_f4C3Coeff (p := (1, 1)) hα hβ hne hαβ (by decide) hra,
    C3Exact.f4C3Coeff_one_one, RootOperatorFamily'.coeff11_without117]
  push_cast
  exact intCast_eq_nat_of_natAbs
    (RootOperatorFamily'.bracketCoeff_natAbs_without117 (rootOperatorFamily .F4)
      CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117 hγ hroot)
    (stringNorm_eq_one_or_two _ _)

theorem coeff12_without117_eq_spCommC
    {α β : Fin 3 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC 3) ∅) (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅)
    (hne : α ≠ β) (hαβ : α + β ≠ 0) (hr : α + 2 • β ∈ roots (isFiniteType_cartanC 3) ∅) :
    (RootOperatorFamily'.coeff12_without117 (rootOperatorFamily .F4)
        CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117
        ⟨c3ToF4 α, isRoot_c3ToF4 hα⟩ ⟨c3ToF4 β, isRoot_c3ToF4 hβ⟩ : K)
      = (Sp.commC α β (1, 2) : K) := by
  have hra : (1 : ℕ) • α + 2 • β ∈ roots (isFiniteType_cartanC 3) ∅ := by simpa using hr
  have hroot : CFSG.Blueprint.Chevalley.IsRoot .F4 (c3ToF4 α + 2 • c3ToF4 β) := by
    rw [← map_nsmul, ← map_add]
    exact isRoot_c3ToF4 (by simpa only [one_smul] using hr)
  have hne1 : c3ToF4 α ≠ c3ToF4 β := fun h => hne (c3ToF4_injective h)
  have hne2 : c3ToF4 α ≠ -c3ToF4 β := by
    intro h
    refine hαβ ?_
    have h1 : c3ToF4 α = c3ToF4 (-β) := h.trans (map_neg _ _).symm
    rw [c3ToF4_injective h1, neg_add_cancel]
  rw [C3Exact.cast_spCommC_eq_f4C3Coeff (p := (1, 2)) hα hβ hne hαβ (by decide) hra,
    CFSG.StandardType.F4ExplicitPos.C3Exact.f4C3Coeff_one_two]
  simpa using intCast_eq_one_of_natAbs (K := K)
    (RootOperatorFamily'.natAbs_coeff12_without117 (rootOperatorFamily .F4)
      CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117 noG2_F4
      (α := ⟨c3ToF4 α, isRoot_c3ToF4 hα⟩) (β := ⟨c3ToF4 β, isRoot_c3ToF4 hβ⟩) hne1 hne2 hroot)

theorem coeff21_without117_eq_spCommC
    {α β : Fin 3 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC 3) ∅) (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅)
    (hne : α ≠ β) (hαβ : α + β ≠ 0) (hr : 2 • α + β ∈ roots (isFiniteType_cartanC 3) ∅) :
    (RootOperatorFamily'.coeff21_without117 (rootOperatorFamily .F4)
        CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117
        ⟨c3ToF4 α, isRoot_c3ToF4 hα⟩ ⟨c3ToF4 β, isRoot_c3ToF4 hβ⟩ : K)
      = (Sp.commC α β (2, 1) : K) := by
  have hra : (2 : ℕ) • α + 1 • β ∈ roots (isFiniteType_cartanC 3) ∅ := by simpa using hr
  have hroot : CFSG.Blueprint.Chevalley.IsRoot .F4 (2 • c3ToF4 α + c3ToF4 β) := by
    rw [← map_nsmul, ← map_add]
    exact isRoot_c3ToF4 (by simpa only [one_smul] using hr)
  have hne1 : c3ToF4 α ≠ c3ToF4 β := fun h => hne (c3ToF4_injective h)
  have hne2 : c3ToF4 α ≠ -c3ToF4 β := by
    intro h
    refine hαβ ?_
    have h1 : c3ToF4 α = c3ToF4 (-β) := h.trans (map_neg _ _).symm
    rw [c3ToF4_injective h1, neg_add_cancel]
  rw [C3Exact.cast_spCommC_eq_f4C3Coeff (p := (2, 1)) hα hβ hne hαβ (by decide) hra,
    CFSG.StandardType.F4ExplicitPos.C3Exact.f4C3Coeff_two_one]
  simpa using intCast_eq_one_of_natAbs (K := K)
    (RootOperatorFamily'.natAbs_coeff21_without117 (rootOperatorFamily .F4)
      CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117 noG2_F4
      (α := ⟨c3ToF4 α, isRoot_c3ToF4 hα⟩) (β := ⟨c3ToF4 β, isRoot_c3ToF4 hβ⟩) hne1 hne2 hroot)

theorem spF4Par_pair_11_without117
    {α β : Fin 3 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC 3) ∅) (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅)
    (hne : α ≠ β) (hαβ : α + β ≠ 0) (c d : K) :
    spF4Par K (1 • α + 1 • β) ((Sp.commC α β (1, 1) : K) * c ^ 1 * d ^ 1) =
      xPar (rootOperatorFamily .F4) (1 • c3ToF4 α + 1 • c3ToF4 β)
        ((RootOperatorFamily'.coeff11_without117 (rootOperatorFamily .F4)
          CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117
          ⟨c3ToF4 α, isRoot_c3ToF4 hα⟩ ⟨c3ToF4 β, isRoot_c3ToF4 hβ⟩ : K) * c ^ 1 * d ^ 1) := by
  have hv : c3ToF4 (1 • α + 1 • β) = 1 • c3ToF4 α + 1 • c3ToF4 β := by
    rw [map_add, map_nsmul, map_nsmul]
  by_cases hr : 1 • α + 1 • β ∈ roots (isFiniteType_cartanC 3) ∅
  · rw [spF4Par, f4Par, hv,
      ← coeff11_without117_eq_spCommC hα hβ hne hαβ (by simpa using hr)]
  · rw [C3Exact.spF4Par_of_not_exact hr,
      show 1 • c3ToF4 α + 1 • c3ToF4 β = c3ToF4 (1 • α + 1 • β) from hv.symm,
      xPar, dif_neg (by rwa [isRoot_c3ToF4_iff])]

theorem spF4Par_pair_12_without117
    {α β : Fin 3 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC 3) ∅) (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅)
    (hne : α ≠ β) (hαβ : α + β ≠ 0) (c d : K) :
    spF4Par K (1 • α + 2 • β) ((Sp.commC α β (1, 2) : K) * c ^ 1 * d ^ 2) =
      xPar (rootOperatorFamily .F4) (1 • c3ToF4 α + 2 • c3ToF4 β)
        ((RootOperatorFamily'.coeff12_without117 (rootOperatorFamily .F4)
          CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117
          ⟨c3ToF4 α, isRoot_c3ToF4 hα⟩ ⟨c3ToF4 β, isRoot_c3ToF4 hβ⟩ : K) * c ^ 1 * d ^ 2) := by
  have hv : c3ToF4 (1 • α + 2 • β) = 1 • c3ToF4 α + 2 • c3ToF4 β := by
    rw [map_add, map_nsmul, map_nsmul]
  by_cases hr : 1 • α + 2 • β ∈ roots (isFiniteType_cartanC 3) ∅
  · rw [spF4Par, f4Par, hv,
      ← coeff12_without117_eq_spCommC hα hβ hne hαβ (by simpa using hr)]
  · rw [C3Exact.spF4Par_of_not_exact hr,
      show 1 • c3ToF4 α + 2 • c3ToF4 β = c3ToF4 (1 • α + 2 • β) from hv.symm,
      xPar, dif_neg (by rwa [isRoot_c3ToF4_iff])]

theorem spF4Par_pair_21_without117
    {α β : Fin 3 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC 3) ∅) (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅)
    (hne : α ≠ β) (hαβ : α + β ≠ 0) (c d : K) :
    spF4Par K (2 • α + 1 • β) ((Sp.commC α β (2, 1) : K) * c ^ 2 * d ^ 1) =
      xPar (rootOperatorFamily .F4) (2 • c3ToF4 α + 1 • c3ToF4 β)
        ((RootOperatorFamily'.coeff21_without117 (rootOperatorFamily .F4)
          CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117
          ⟨c3ToF4 α, isRoot_c3ToF4 hα⟩ ⟨c3ToF4 β, isRoot_c3ToF4 hβ⟩ : K) * c ^ 2 * d ^ 1) := by
  have hv : c3ToF4 (2 • α + 1 • β) = 2 • c3ToF4 α + 1 • c3ToF4 β := by
    rw [map_add, map_nsmul, map_nsmul]
  by_cases hr : 2 • α + 1 • β ∈ roots (isFiniteType_cartanC 3) ∅
  · rw [spF4Par, f4Par, hv,
      ← coeff21_without117_eq_spCommC hα hβ hne hαβ (by simpa using hr)]
  · rw [C3Exact.spF4Par_of_not_exact hr,
      show 2 • c3ToF4 α + 1 • c3ToF4 β = c3ToF4 (2 • α + 1 • β) from hv.symm,
      xPar, dif_neg (by rwa [isRoot_c3ToF4_iff])]

theorem commutator_spF4Par_without117
    (O : CommOrder (Sp.Φ 3 K)) {α β : Fin 3 → ℤ}
    (hα : α ∈ roots (isFiniteType_cartanC 3) ∅) (hβ : β ∈ roots (isFiniteType_cartanC 3) ∅)
    (hαβ : α + β ≠ 0) (c d : K) :
    ⁅spF4Par K α c, spF4Par K β d⁆ =
      ((O.list α β).map fun p => spF4Par K (p.1 • α + p.2 • β)
        ((Sp.commC α β p : K) * c ^ p.1 * d ^ p.2)).prod := by
  classical
  by_cases hne : α = β
  · subst hne
    have hnil : O.list α α = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => by
      obtain ⟨h1, h2, h3⟩ := (O.mem_iff α hα α hα hαβ p).1 hp
      rw [← add_nsmul] at h3
      have := eq_one_of_nsmul_mem_roots_without117 (show (p.1 + p.2) • α ∈ roots
          (isFiniteType_cartanC 3) ∅ from h3)
      omega
    rw [hnil, List.map_nil, List.prod_nil, commutatorElement_eq_one_iff_commute, Commute,
      SemiconjBy, spF4Par, f4Par, ← xPar_add_without117 (rootOperatorFamily .F4),
      ← xPar_add_without117 (rootOperatorFamily .F4), add_comm]
  have hne' : α ≠ -β := fun h => hαβ (by rw [h, neg_add_cancel])
  have hα' := isRoot_c3ToF4 hα
  have hβ' := isRoot_c3ToF4 hβ
  have hne₁ : c3ToF4 α ≠ c3ToF4 β := fun h => hne (c3ToF4_injective h)
  have hne₂ : c3ToF4 α ≠ -c3ToF4 β := fun h => hne' (c3ToF4_injective (by rw [h, map_neg]))
  have hsum : c3ToF4 α + c3ToF4 β ≠ 0 := fun h => hne₂ (eq_neg_of_add_eq_zero_left h)
  have hperm : (O.list α β).Perm (pairs₀.filter fun p =>
      decide (p.1 • α + p.2 • β ∈ roots (isFiniteType_cartanC 3) ∅)) := by
    refine (List.perm_ext_iff_of_nodup (O.nodup α β) ((by decide : pairs₀.Nodup).filter _)).2
      fun p => ?_
    rw [O.mem_iff α hα β hβ hαβ, Sp.mem_expPairs_iff hα hβ hαβ]
    simp only [List.mem_filter, decide_eq_true_eq, pairs₀, Sp.expS, Finset.mem_insert,
      Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have hcomm : ∀ p ∈ O.list α β, ∀ q ∈ O.list α β,
      Commute (spF4Par K (p.1 • α + p.2 • β) ((Sp.commC α β p : K) * c ^ p.1 * d ^ p.2))
        (spF4Par K (q.1 • α + q.2 • β) ((Sp.commC α β q : K) * c ^ q.1 * d ^ q.2)) := by
    intro p hp q hq
    obtain ⟨hp1, hp2, -⟩ := (O.mem_iff α hα β hβ hαβ p).1 hp
    obtain ⟨hq1, hq2, -⟩ := (O.mem_iff α hα β hβ hαβ q).1 hq
    simp only [spF4Par, f4Par, map_add, map_nsmul]
    exact commute_xPar_pairs_without117 (rootOperatorFamily .F4)
      DataValid.f4Data_valid_without117 noG2_F4 hα' hβ' hne₁ hne₂ hp1 hp2 hq1 hq2 _ _
  rw [(hperm.map _).prod_eq' (List.pairwise_map.2 (List.pairwise_of_forall_mem_list hcomm)),
    prod_map_filter_of_eq_one_without117 _ _ _ fun p _ hp => C3Exact.spF4Par_of_not_exact
        (by simpa using hp) _]
  simp only [pairs₀, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [spF4Par_pair_11_without117 hα hβ hne hαβ, spF4Par_pair_12_without117 hα hβ hne hαβ,
    spF4Par_pair_21_without117 hα hβ hne hαβ, spF4Par, spF4Par, f4Par,
    commutator_xPar_without117 (F := rootOperatorFamily .F4)
      CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117 noG2_F4 hα' hβ' hne₁ hne₂]
  simp only [one_smul, pow_one, mul_assoc]

theorem f4C3_exists_pinned_unconditional
    (O : CommOrder (Sp.Φ 3 K)) :
    ∃ ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K), Function.Injective ι ∧
      ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c :=
  CFSG.StandardType.F4ExplicitPos.C3Exact.f4C3_exists_pinned_of_comm_only O
    (fun {α β} hα hβ hαβ c d => commutator_spF4Par_without117 O hα hβ hαβ c d)

end CFSG.StandardType.F4ExplicitPos.C3Comm

end

public noncomputable section

variable {K : Type} [Field K] [CharP K 2]

namespace CFSG.StandardType.F4ExplicitPos.PerfectC3

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed

theorem xPar_of_isRoot_exact
    {γ : Fin (Tag.rank .F4) → ℤ} (h : IsRoot .F4 γ) (c : K) :
    xPar (rootOperatorFamily .F4) γ c
      = (rootOperatorFamily .F4).eltElement ⟨γ, h⟩ c := by
  classical
  unfold xPar
  exact dif_pos h

theorem f4Par_single_eq_eltElement
    (j : Fin (Tag.rank .F4)) (c : K) :
    f4Par K (Pi.single j 1) c
      = (rootOperatorFamily .F4).eltElement (simpleRoot .F4 j) c := by
  classical
  change xPar (rootOperatorFamily .F4) (Pi.single j 1) c = _
  rw [xPar_of_isRoot_exact (isRoot_single .F4 j)]
  rfl

theorem f4Par_neg_single_eq_eltElement
    (j : Fin (Tag.rank .F4)) (c : K) :
    f4Par K (-Pi.single j 1) c
      = (rootOperatorFamily .F4).eltElement (-simpleRoot .F4 j) c := by
  classical
  change xPar (rootOperatorFamily .F4) (-Pi.single j 1) c = _
  rw [xPar_of_isRoot_exact (isRoot_neg_single .F4 j)]
  rfl

theorem isPerfect_of_pinnedC3Hom
    (ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K))
    (hform : ∀ γ c, ι (Sp.x 3 K γ c) = f4Par K (c3ToF4 γ) c)
    (hperfSp : Group.IsPerfect ↥(StatedSp 3 K)) :
    Group.IsPerfect ↥(adjointGroup .F4 K) := by
  classical
  let D : Subgroup ↥(adjointGroup .F4 K) :=
    ⁅(⊤ : Subgroup ↥(adjointGroup .F4 K)), ⊤⁆
  have hDnormal : D.Normal := by
    dsimp only [D]
    infer_instance
  have hrange : MonoidHom.range ι ≤ D := by
    have : Group.IsPerfect ↥(StatedSp 3 K) := hperfSp
    have hperf_range : Group.IsPerfect ↥(MonoidHom.range ι) := Group.IsPerfect.range ι
    have hcomm : ⁅MonoidHom.range ι, MonoidHom.range ι⁆ = MonoidHom.range ι :=
      Subgroup.isPerfect_iff.1 hperf_range
    calc MonoidHom.range ι = ⁅MonoidHom.range ι, MonoidHom.range ι⁆ := hcomm.symm
      _ ≤ D := by
        dsimp only [D]
        exact Subgroup.commutator_mono le_top le_top
  have hc3 : ∀ (k : Fin 3) (c : K),
      (rootOperatorFamily .F4).eltElement (simpleRoot .F4 (c3Node k)) c ∈ D := by
    intro k c
    have hmem : ι (Sp.x 3 K (Pi.single k 1) c) ∈ D :=
      hrange ⟨_, rfl⟩
    rw [hform, c3ToF4_single] at hmem
    rwa [f4Par_single_eq_eltElement] at hmem
  have hc3neg : ∀ (k : Fin 3) (c : K),
      (rootOperatorFamily .F4).eltElement (-simpleRoot .F4 (c3Node k)) c ∈ D := by
    intro k c
    have hmem : ι (Sp.x 3 K (-Pi.single k 1) c) ∈ D :=
      hrange ⟨_, rfl⟩
    rw [hform, map_neg, c3ToF4_single] at hmem
    rwa [f4Par_neg_single_eq_eltElement] at hmem
  have hc3sub : ∀ k : Fin 3,
      (rootOperatorFamily .F4).rootSubgroup K (simpleRoot .F4 (c3Node k)) ≤ D := by
    intro k g hg
    rw [RootOperatorFamily.mem_rootSubgroup] at hg
    obtain ⟨c, rfl⟩ := hg
    exact hc3 k c
  have hc3subneg : ∀ k : Fin 3,
      (rootOperatorFamily .F4).rootSubgroup K (-simpleRoot .F4 (c3Node k)) ≤ D := by
    intro k g hg
    rw [RootOperatorFamily.mem_rootSubgroup] at hg
    obtain ⟨c, rfl⟩ := hg
    exact hc3neg k c
  have hweyl : ∀ (i : Fin (Tag.rank .F4)) (α : Root .F4),
      (rootOperatorFamily .F4).rootSubgroup K α ≤ D →
        (rootOperatorFamily .F4).rootSubgroup K (simple .F4 i • α) ≤ D := by
    intro i α hα x hx
    rw [← (rootOperatorFamily .F4).map_conj_weylElement i α] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change (MulAut.conj (weylElement .F4 K i)) y ∈ D
    rw [MulAut.conj_apply]
    exact hDnormal.conj_mem y (hα hy) (weylElement .F4 K i)
  let j0 : Fin (Tag.rank .F4) := ⟨0, by decide⟩
  let j1 : Fin (Tag.rank .F4) := ⟨1, by decide⟩
  have h1 : (rootOperatorFamily .F4).rootSubgroup K (simpleRoot .F4 j1) ≤ D :=
    hc3sub 2
  have h1neg : (rootOperatorFamily .F4).rootSubgroup K (-simpleRoot .F4 j1) ≤ D :=
    hc3subneg 2
  have h0 : (rootOperatorFamily .F4).rootSubgroup K (simpleRoot .F4 j0) ≤ D := by
    have hroot : simple .F4 j1 • (simple .F4 j0 • simpleRoot .F4 j1) = simpleRoot .F4 j0 := by
      apply Subtype.ext
      simp only [coe_smul_root, simple_smul]
      decide
    have hstep : (rootOperatorFamily .F4).rootSubgroup K
        (simple .F4 j1 • (simple .F4 j0 • simpleRoot .F4 j1)) ≤ D :=
      hweyl j1 _ (hweyl j0 _ h1)
    rwa [hroot] at hstep
  have h0neg : (rootOperatorFamily .F4).rootSubgroup K (-simpleRoot .F4 j0) ≤ D := by
    have hroot : simple .F4 j1 • (simple .F4 j0 • (-simpleRoot .F4 j1))
        = -simpleRoot .F4 j0 := by
      apply Subtype.ext
      simp only [coe_smul_root, simple_smul]
      decide
    have hstep : (rootOperatorFamily .F4).rootSubgroup K
        (simple .F4 j1 • (simple .F4 j0 • (-simpleRoot .F4 j1))) ≤ D :=
      hweyl j1 _ (hweyl j0 _ h1neg)
    rwa [hroot] at hstep
  have hsimple : ∀ j : Fin (Tag.rank .F4),
      (rootOperatorFamily .F4).rootSubgroup K (simpleRoot .F4 j) ≤ D ∧
      (rootOperatorFamily .F4).rootSubgroup K (-simpleRoot .F4 j) ≤ D := by
    intro j
    fin_cases j
    · exact ⟨h0, h0neg⟩
    · exact ⟨h1, h1neg⟩
    · exact ⟨hc3sub 1, hc3subneg 1⟩
    · exact ⟨hc3sub 0, hc3subneg 0⟩
  rw [Group.isPerfect_def, eq_top_iff]
  set S : Set (ModGL .F4 K) :=
    {g | ∃ (i : Fin (Tag.rank .F4)) (c : K),
      (g : Module.End K (RootModule .F4 K)) = xOp .F4 K i c ∨
        (g : Module.End K (RootModule .F4 K)) = yOp .F4 K i c}
  have hcl : Subgroup.closure (((↑) : ↥(adjointGroup .F4 K) → ModGL .F4 K) ⁻¹' S) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [← hcl, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩
  · have hg' : g = (rootOperatorFamily .F4).eltElement (simpleRoot .F4 i) c := by
      apply Subtype.ext
      apply Units.ext
      rw [RootOperatorFamily.coe_eltElement, hg, RootOperatorFamily.coe_eltUnit]
      exact ((rootOperatorFamily .F4).elt_simple i c).symm
    rw [hg']
    exact (hsimple i).1 ((RootOperatorFamily.mem_rootSubgroup (F := rootOperatorFamily .F4)).mpr
      ⟨c, rfl⟩)
  · have hg' : g = (rootOperatorFamily .F4).eltElement (-simpleRoot .F4 i) c := by
      apply Subtype.ext
      apply Units.ext
      rw [RootOperatorFamily.coe_eltElement, hg, RootOperatorFamily.coe_eltUnit]
      exact ((rootOperatorFamily .F4).elt_neg_simple i c).symm
    rw [hg']
    exact (hsimple i).2 ((RootOperatorFamily.mem_rootSubgroup (F := rootOperatorFamily .F4)).mpr
      ⟨c, rfl⟩)

theorem finiteF4perfection
    [Finite K] : Group.IsPerfect ↥(adjointGroup .F4 K) := by
  obtain ⟨ι, _hinj, hform⟩ :=
    CFSG.StandardType.F4ExplicitPos.C3Comm.f4C3_exists_pinned_unconditional
      (CFSG.Timmesfeld.Transvection.Pres.spOrder 3 K)
  have hperfSp : Group.IsPerfect ↥(StatedSp 3 K) := by
    have hcard : 2 ≤ Nat.card K := Finite.one_lt_card
    exact (CFSG.LieType.Universal.Symplectic.isQuasisimple 3 K (by norm_num) (by
      rcases (show Nat.card K = 2 ∨ Nat.card K = 3 ∨ 4 ≤ Nat.card K by omega) with h | h | h
      · exact Or.inr (Or.inr ⟨h, le_rfl⟩)
      · exact Or.inr (Or.inl ⟨h, by norm_num⟩)
      · exact Or.inl (Or.inr h))).1
  exact isPerfect_of_pinnedC3Hom ι hform hperfSp

end CFSG.StandardType.F4ExplicitPos.PerfectC3

end

end
