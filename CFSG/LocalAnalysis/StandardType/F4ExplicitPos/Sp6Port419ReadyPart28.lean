module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PerfectC3

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart25
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart27

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.FiniteAction
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.F4ExplicitPos.CentralizerGuard

theorem exists_finiteSubfield_quotientAction
    (Ω : Type*) [Field Ω] [CharP Ω 2] [IsSepClosed Ω]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω)
    {Ψ : Set (Fin Tag.F4.rank → ℤ)}
    {B : Type*} [Group B] [Finite B]
    (α : B →* MulAut (rootSpan Tag.F4 Ω Ψ))
    (hinner : ∀ b : B, ∃ g : rootSpan Tag.F4 Ω Ψ, MulAut.conj g = α b) :
    ∃ k : ℕ, k ≠ 0 ∧ 4 ≤ Nat.card (TauCeti.frobeniusFixedSubfield Ω 2 k) ∧
      ∃ β : B →* (rootSpanOver Ω (TauCeti.frobeniusFixedSubfield Ω 2 k) Ψ) ⧸
          Subgroup.center (rootSpanOver Ω (TauCeti.frobeniusFixedSubfield Ω 2 k) Ψ),
        β.ker = α.ker := by
  classical
  choose g hg using hinner
  obtain ⟨k, hk, hmem, hk4⟩ :=
    exists_frobeniusFixedSubfield_subfieldRootSpan Ω halg
      (fun b : B => (g b : ModGL Tag.F4 Ω)) (fun b => (g b).2)
  have : Finite (TauCeti.frobeniusFixedSubfield Ω 2 k) :=
    TauCeti.finite_frobeniusFixedSubfield Ω 2 k hk
  have : Fintype (TauCeti.frobeniusFixedSubfield Ω 2 k) :=
    Fintype.ofFinite (TauCeti.frobeniusFixedSubfield Ω 2 k)
  have hE : 4 ≤ Fintype.card (TauCeti.frobeniusFixedSubfield Ω 2 k) := by
    rw [← Nat.card_eq_fintype_card]
    exact hk4
  let H0 : Subgroup (ModGL Tag.F4 Ω) :=
    rootSpanOver Ω (TauCeti.frobeniusFixedSubfield Ω 2 k) Ψ
  have h0H : H0 ≤ rootSpan Tag.F4 Ω Ψ := rootSpanOver_le_rootSpan Ω _ Ψ
  have hguard : (Subgroup.center H0).map H0.subtype ≤
      Subgroup.centralizer ((rootSpan Tag.F4 Ω Ψ : Subgroup (ModGL Tag.F4 Ω)) :
        Set (ModGL Tag.F4 Ω)) :=
    (le_of_eq (center_rootSpanOver_eq Ω (TauCeti.frobeniusFixedSubfield Ω 2 k) hE Ψ)).trans
      inf_le_right
  have hinner' : ∀ b : B, ∃ g' : H0, conjAction h0H g' = α b := by
    intro b
    refine ⟨⟨(g b : ModGL Tag.F4 Ω), hmem b⟩, ?_⟩
    have hcoe : Subgroup.inclusion h0H ⟨(g b : ModGL Tag.F4 Ω), hmem b⟩ = g b := by
      apply Subtype.ext
      rfl
    rw [conjAction, MonoidHom.comp_apply, hcoe]
    exact hg b
  exact ⟨k, hk, hk4, quotientAction h0H hguard α hinner',
    quotientAction_ker h0H hguard α hinner'⟩

end CFSG.StandardType.F4ExplicitPos.FiniteAction

end

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof

open scoped MatrixGroups Matrix

theorem rootsOf_eq_parabolicRoots_narrow
    {τ : Tag} (K : KacData τ) (hK : K.Facts)
    {C : Finset (Option (Fin τ.rank))} {J : Set (Fin τ.rank)} (hnone : none ∉ C)
    (hCJ : ∀ j, some j ∈ C ↔ j ∈ J) :
    K.rootsOf (C : Set (Option (Fin τ.rank))) = parabolicRoots τ J := by
  ext γ
  rw [mem_rootsOf_iff K hK ⟨none, hnone⟩]
  constructor
  · rintro ⟨hγ, htest⟩
    refine ⟨hγ, fun i hi => ?_⟩
    rcases htest with h | ⟨h, -⟩
    · exact h i (fun hc => hi ((hCJ i).1 hc))
    · exact absurd h hnone
  · rintro ⟨hγ, hJ⟩
    exact ⟨hγ, Or.inl fun j hj => hJ j (fun hj' => hj ((hCJ j).2 hj'))⟩

theorem eq_one_of_simple_mem_class_narrow {τ : Tag} {L : Type} [Field L]
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (h : ∀ j, (Pi.single j 1 : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) i) :
    rootDiagUnit τ a = 1 := by
  have ha : a = 1 := by
    funext j
    obtain ⟨hker, -⟩ := h j
    have h1 : rootChar a (Pi.single j 1) = 1 := hker.2
    rw [CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single] at h1
    exact h1
  rw [ha]
  exact rootDiagUnit_one

theorem mem_f4LeviB3_narrow (j : Fin (Tag.rank .F4)) : j ∈ f4LeviB3 ↔ j.val ≤ 2 := by
  unfold f4LeviB3
  rw [Set.mem_range]
  revert j
  decide

theorem mem_f4LeviC3_narrow (j : Fin (Tag.rank .F4)) : j ∈ f4LeviC3 ↔ 1 ≤ j.val := by
  unfold f4LeviC3
  rw [Set.mem_range]
  revert j
  decide

theorem f4_rank_ge_three_component_is_levi
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {p : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1) (hpΩ : (p : Ω) ≠ 0)
    {a : Fin Tag.F4.rank → Ωˣ}
    (hap : rootDiagUnit Tag.F4 a ^ p = 1)
    (ha1 : rootDiagUnit Tag.F4 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i)) :
    ∃ (v : WeylGroup Tag.F4) (J : Set (Fin Tag.F4.rank)),
      (J = f4LeviB3 ∨ J = f4LeviC3) ∧
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 J ∧
      compRank (componentRoots (rootCharHom a) i) = 3 ∧
      (componentRoots (rootCharHom a) i).ncard = 18 := by
  classical
  have hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) := by
    rintro ⟨-, hn⟩
    have hle := f4_typeA_rank_le_two hp hpΩ hap i hn
    omega
  obtain ⟨v, μ, hμ, hall⟩ := exists_kacT_of_pos hp.pos hpΩ facts_F4 hap
  obtain ⟨x, hx, hi⟩ := hall i
  obtain ⟨c, hc, hcomp⟩ := kacF4.exists_comp_eq_of_check f4_tree f4_adj (adm := fun _ => true)
    f4_check rfl hx
  set C : Finset (Option (Fin Tag.F4.rank)) := (c.map (idxNode (r := Tag.F4.rank))).toFinset
    with hCdef
  have hCset : kacF4.comp p μ x = (C : Set (Option (Fin Tag.F4.rank))) := by
    rw [hcomp]
    ext y
    simp only [Set.mem_ofPred_eq, hCdef, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨w, hw, rfl⟩
      rw [nodeIdx_idxNode (f4_lt c hc w hw)]
      exact hw
  have hCp : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacF4 hp.pos μ x
    exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
  have hlen : c.length ≤ 4 := by
    obtain ⟨y, hy⟩ := hCp
    have h1 : C.card < Fintype.card (Option (Fin Tag.F4.rank)) :=
      Finset.card_lt_univ_of_notMem hy
    have h2 : Fintype.card (Option (Fin Tag.F4.rank)) = 5 := by
      rw [Fintype.card_option, Fintype.card_fin]
      rfl
    rw [h2, f4_card c hc] at h1
    omega
  have hi' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) := by
    rw [hi, hCset]
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hi', compRank_image, compRank_rootsOf kacF4 facts_F4 hCp, f4_card c hc]
  have hncard : (componentRoots (rootCharHom a) i).ncard =
      kacCount Tag.F4 kacF4.θ (c.map (idxNode (r := Tag.F4.rank))).toFinset := by
    rw [hi', ncard_image_smul, ncard_rootsOf kacF4 facts_F4 hCp]
  have hnonA' : ¬ (1 ≤ c.length ∧ kacCount Tag.F4 ![2, 3, 4, 2]
      (c.map (idxNode (r := Tag.F4.rank))).toFinset = c.length * (c.length + 1)) := by
    rw [hrank, hncard] at hnonA
    exact hnonA
  rcases f4_nonA_cases c hc hlen hnonA' with rfl | rfl | rfl | rfl | rfl
  · exfalso
    rw [hrank] at h3
    simp only [List.length_cons, List.length_nil] at h3
    omega
  · refine ⟨v, f4LeviB3, Or.inl rfl, ?_,
      by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_B3⟩
    rw [hi', rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4LeviB3)
      (by rw [hCdef]; decide)
      (fun j => by rw [hCdef, mem_f4LeviB3_narrow]; revert j; decide)]
  · refine ⟨v, f4LeviC3, Or.inr rfl, ?_,
      by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_C3⟩
    rw [hi', rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4LeviC3)
      (by rw [hCdef]; decide)
      (fun j => by rw [hCdef, mem_f4LeviC3_narrow]; revert j; decide)]
  · exact (not_comp_eq_B4_F4_odd hp2 hμ hcomp).elim
  · exfalso
    apply ha1
    refine eq_one_of_simple_mem_class_narrow i (fun j => ?_)
    rw [hi', rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := Set.univ) (by rw [hCdef]; decide)
      (fun j => by simp only [Set.mem_univ, iff_true]; rw [hCdef]; revert j; decide)]
    exact ⟨v⁻¹ • Pi.single j 1, ⟨IsRoot.smul (isRoot_single _ j) v⁻¹, fun i hi =>
      (hi (Set.mem_univ i)).elim⟩, smul_inv_smul v _⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar

end

public noncomputable section

variable {K : Type} [Field K] [CharP K 2] [Finite K]

namespace CFSG.StandardType.F4ExplicitPos.C3Range

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed

def c3RootSet : Set (Fin (Tag.rank .F4) → ℤ) :=
  {α | ∃ γ ∈ roots (isFiniteType_cartanC 3) ∅, c3ToF4 γ = α}

theorem isRoot_of_mem_c3RootSet
    {α : Fin (Tag.rank .F4) → ℤ} (hα : α ∈ c3RootSet) :
    CFSG.Blueprint.Chevalley.IsRoot .F4 α := by
  obtain ⟨γ, hγ, rfl⟩ := hα
  exact isRoot_c3ToF4 hγ

theorem f4Par_coe_eq_pinnedX
    {α : Fin (Tag.rank .F4) → ℤ}
    (hα : CFSG.Blueprint.Chevalley.IsRoot .F4 α) (c : K) :
    ((Adjoint.f4Par K α c : ↥(adjointGroup .F4 K)) : ModGL .F4 K)
      = pinnedX .F4 K α (((rootOperatorFamily .F4).pinnedFamilySign α : K) * c) := by
  rw [show Adjoint.f4Par K α c = xPar (rootOperatorFamily .F4) α c from rfl,
    xPar, dif_pos hα, RootOperatorFamily.coe_eltElement]
  symm
  rw [(rootOperatorFamily .F4).pinnedX_eq_eltUnit K hα, ← mul_assoc,
    (rootOperatorFamily .F4).pinnedFamilySign_mul_self K α, one_mul]

theorem iota_x_eq_pinnedX
    (ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K))
    (hι : ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c)
    {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) (c : K) :
    ((ι (Sp.x 3 K γ c) : ↥(adjointGroup .F4 K)) : ModGL .F4 K)
      = pinnedX .F4 K (c3ToF4 γ) (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) *
          c) := by
  rw [hι, f4Par_coe_eq_pinnedX (isRoot_c3ToF4 hγ)]

def c3RootSubgroup (γ : Fin 3 → ℤ) : Subgroup (StatedSp 3 K) :=
  Subgroup.closure (Set.range (Sp.x 3 K γ))

theorem range_iota_x_eq_range_pinnedX
    (ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K))
    (hι : ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c)
    {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    Set.range (fun c : K => ((ι (Sp.x 3 K γ c) : ↥(adjointGroup .F4 K)) : ModGL .F4 K))
      = Set.range (pinnedX .F4 K (c3ToF4 γ)) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) * c,
      (iota_x_eq_pinnedX ι hι hγ c).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) * c, ?_⟩
    change ((ι (Sp.x 3 K γ (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) * c)) :
      ↥(adjointGroup .F4 K)) : ModGL .F4 K) = pinnedX .F4 K (c3ToF4 γ) c
    rw [iota_x_eq_pinnedX ι hι hγ (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) * c),
      show ((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K)
          * (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) * c) = c from by
        rw [← mul_assoc, (rootOperatorFamily .F4).pinnedFamilySign_mul_self K (c3ToF4 γ), one_mul]]

theorem map_c3RootSubgroup_eq_rootSubgroup
    (ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K))
    (hι : ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c)
    {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    (c3RootSubgroup (K := K) γ).map ((adjointGroup .F4 K).subtype.comp ι)
      = CFSG.Blueprint.Chevalley.rootSubgroup .F4 K (c3ToF4 γ) := by
  rw [c3RootSubgroup, MonoidHom.map_closure, CFSG.Blueprint.Chevalley.rootSubgroup]
  congr 1
  rw [← Set.range_comp]
  exact range_iota_x_eq_range_pinnedX ι hι hγ

end CFSG.StandardType.F4ExplicitPos.C3Range
end

end
