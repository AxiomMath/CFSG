module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Induction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Proper
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7Final

namespace CFSG
end CFSG
open CFSG

/-!
# The induction assembly for Proposition 8.4

This file supplies the checked induction glue between the two source leaves
`Proposition84BaseStep` and `Proposition84ProperStep`.  The main induction is
strong induction on the cardinality of `Y`; the only recursive call is made
at a proper normal predecessor supplied by the subnormal chain from `Y₁` to
`Y`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u v

/-- Subnormality is preserved by a group isomorphism. -/
private theorem isSubnormal_map_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) {K : Subgroup G} (hK : K.IsSubnormal) :
    (K.map e.toMonoidHom).IsSubnormal := by
  induction hK with
  | top =>
      simp
  | step A B hAB hBsub hAnormal ih =>
      refine Subgroup.IsSubnormal.step _ _ (Subgroup.map_mono hAB) ih ?_
      rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hAB)]
      intro a b ha hb
      rcases ha with ⟨a0, ha0, rfl⟩
      rcases hb with ⟨b0, hb0, rfl⟩
      refine ⟨b0 * a0 * b0⁻¹, ?_, by simp⟩
      exact (Subgroup.normal_subgroupOf_iff hAB).mp hAnormal
        a0 b0 ha0 hb0

/-- Normality of `H` in `K` is unchanged when both are viewed inside an
intermediate overgroup `L`. -/
private theorem normal_subgroupOf_subgroupOf
    {G : Type u} [Group G] {H K L : Subgroup G}
    (hHK : H ≤ K) (_hKL : K ≤ L)
    (hN : (H.subgroupOf K).Normal) :
    ((H.subgroupOf L).subgroupOf (K.subgroupOf L)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono L hHK)]
  intro h k hh hk
  exact (Subgroup.normal_subgroupOf_iff hHK).mp hN
    (h : G) (k : G) hh hk

/-- Internal form of the penultimate-subgroup lemma: a proper subnormal
subgroup lies subnormally inside a proper subgroup that is normal in the
ambient group. -/
private theorem exists_normal_predecessor_internal
    {G : Type u} [Group G] {H : Subgroup G}
    (hH : H.IsSubnormal) (hHne : H ≠ ⊤) :
    ∃ K : Subgroup G,
      H ≤ K ∧ K < ⊤ ∧ K.Normal ∧
        (H.subgroupOf K).IsSubnormal := by
  induction hH with
  | top => exact (hHne rfl).elim
  | step H K hHK hKsub hHnormal ih =>
      by_cases hKtop : K = ⊤
      · subst K
        have hHnormalG : H.Normal := by
          have hmap := hHnormal.map (⊤ : Subgroup G).subtype (by
            intro x
            exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
          simpa [Subgroup.map_subgroupOf_eq_of_le le_top] using hmap
        refine ⟨H, le_rfl, hHne.lt_top, hHnormalG, ?_⟩
        rw [Subgroup.subgroupOf_self]
        exact Subgroup.IsSubnormal.top
      · obtain ⟨L, hKL, hLlt, hLnormal, hKsubL⟩ := ih hKtop
        refine ⟨L, hHK.trans hKL, hLlt, hLnormal, ?_⟩
        exact Subgroup.IsSubnormal.step _ _
          (Subgroup.subgroupOf_mono L hHK) hKsubL
          (normal_subgroupOf_subgroupOf hHK hKL hHnormal)

/-- Exact proper normal predecessor used by the Proposition 8.4 induction.
If `Y₁` is proper and subnormal in `Y`, there is a proper `Y₀ ◁ Y`
containing `Y₁`, and `Y₁` remains subnormal in `Y₀`. -/
public theorem exists_proper_normal_predecessor_of_isSubnormal
    {X : Type u} [Group X] {Y1 Y : Subgroup X}
    (hY1Y : Y1 < Y)
    (hsubnormal : (Y1.subgroupOf Y).IsSubnormal) :
    ∃ Y0 : Subgroup X,
      Y1 ≤ Y0 ∧ Y0 < Y ∧
        (Y0.subgroupOf Y).Normal ∧
        (Y1.subgroupOf Y0).IsSubnormal := by
  have hne : Y1.subgroupOf Y ≠ ⊤ := by
    intro htop
    exact hY1Y.2 (Subgroup.subgroupOf_eq_top.mp htop)
  obtain ⟨K, hY1K, hKlt, hKnormal, hY1subK⟩ :=
    exists_normal_predecessor_internal hsubnormal hne
  let Y0 : Subgroup X := K.map Y.subtype
  have hY1Y0 : Y1 ≤ Y0 := by
    calc
      Y1 = (Y1.subgroupOf Y).map Y.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hY1Y.le).symm
      _ ≤ K.map Y.subtype := Subgroup.map_mono hY1K
  have hY0lt : Y0 < Y := by
    have hmaplt : K.map Y.subtype < (⊤ : Subgroup Y).map Y.subtype :=
      (Subgroup.map_lt_map_iff_of_injective Y.subtype_injective).2 hKlt
    simpa only [Y0, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hmaplt
  have hY0normal : (Y0.subgroupOf Y).Normal := by
    have heq : Y0.subgroupOf Y = K :=
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective K
    rw [heq]
    exact hKnormal
  let eK : K ≃* Y0 :=
    K.equivMapOfInjective Y.subtype Y.subtype_injective
  have hmapSub :
      ((Y1.subgroupOf Y).subgroupOf K).map eK.toMonoidHom |>.IsSubnormal :=
    isSubnormal_map_mulEquiv eK hY1subK
  have heqSub :
      ((Y1.subgroupOf Y).subgroupOf K).map eK.toMonoidHom =
        Y1.subgroupOf Y0 := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      refine ⟨eK.symm z, ?_, eK.apply_symm_apply z⟩
      change ((((eK.symm z : K) : Y) : X) ∈ Y1)
      have hval : (((eK.symm z : K) : Y) : X) = (z : X) := by
        have heq : ((eK (eK.symm z) : Y0) : X) = (z : X) :=
          congrArg (fun q : Y0 => (q : X)) (eK.apply_symm_apply z)
        change (((eK.symm z : K) : Y) : X) = (z : X) at heq
        exact heq
      change (z : X) ∈ Y1 at hz
      simpa [hval] using hz
  refine ⟨Y0, hY1Y0, hY0lt, hY0normal, ?_⟩
  rwa [← heqSub]

/-- The two independent source steps assemble to the full quantified
Proposition 8.4 statement by strong induction on `Nat.card Y`. -/
public theorem proposition84Statement_of_steps
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u0 : X)
    (hbase : Proposition84BaseStep M t u0)
    (hproper : Proposition84ProperStep M t u0) :
    Proposition84Statement M t u0 := by
  let D := M ⊓ rightConjugate M t
  let V := D ⊓ Subgroup.centralizer ({u0} : Set X)
  let P : ℕ → Prop := fun n =>
    ∀ (Y Y1 : Subgroup X), Nat.card Y = n →
      Y ≤ V → Y1 ≠ ⊥ → Y1 ≤ Y →
      (Y1.subgroupOf Y).IsSubnormal →
      HasNontrivialPeterfalviNormalizer D t Y1 →
        Proposition84Conclusion M t u0 Y
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Y Y1 hcard hYV hY1ne hY1Y hsubnormal hIY1
        by_cases hIY : HasNontrivialPeterfalviNormalizer D t Y
        · have hYne : Y ≠ ⊥ := by
            intro hYbot
            apply hY1ne
            apply bot_unique
            simpa [hYbot] using hY1Y
          exact hbase Y hYV hYne hIY
        · by_cases hY1eq : Y1 = Y
          · subst Y1
            exact (hIY hIY1).elim
          · have hY1lt : Y1 < Y := hY1Y.lt_of_ne hY1eq
            obtain ⟨Y0, hY1Y0, hY0lt, hY0normal, hY1subY0⟩ :=
              exists_proper_normal_predecessor_of_isSubnormal
                hY1lt hsubnormal
            have hY0V : Y0 ≤ V := hY0lt.le.trans hYV
            have hY0ne : Y0 ≠ ⊥ := by
              intro hY0bot
              apply hY1ne
              apply bot_unique
              simpa [hY0bot] using hY1Y0
            have hcardlt : Nat.card Y0 < n := by
              have hlt := natCard_lt_of_subgroup_lt hY0lt
              simpa [hcard] using hlt
            have hconclusionY0 : Proposition84Conclusion M t u0 Y0 :=
              ih (Nat.card Y0) hcardlt Y0 Y1 rfl hY0V hY1ne
                hY1Y0 hY1subY0 hIY1
            have hAB : Proposition84ABConclusion M t u0 Y :=
              hproper Y0 Y hYV hY0ne hY0lt hY0normal
                hconclusionY0 hIY
            exact ⟨hAB, fun h => (hIY h).elim⟩
  intro Y Y1 hYV hY1ne hY1Y hsubnormal hIY1
  exact hP (Nat.card Y) Y Y1 rfl hYV hY1ne hY1Y hsubnormal hIY1

namespace Proposition84Statement

/-- Namespace-form wrapper for the checked Proposition 8.4 induction
assembly. -/
public theorem of_steps
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u0 : X)
    (hbase : Proposition84BaseStep M t u0)
    (hproper : Proposition84ProperStep M t u0) :
    Proposition84Statement M t u0 :=
  proposition84Statement_of_steps M t u0 hbase hproper

end Proposition84Statement

/-- Proposition 8.4, its retained model support, and the selected Lemma 8.3
involution, from the standing simple minimal-counterexample source
endpoints. -/
public theorem IsStronglyEmbedded.exists_proposition84_with_modelSupport_of_source_endpoints
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hXsimple : IsSimpleGroup X)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    {t : X} (ht : IsInvolution t) (htM : t ∉ M) :
    ∃ d83 : Lemma83Data M t,
      Proposition84Statement M t d83.u ∧
        Proposition84ModelSupportStatement M t d83.u := by
  let hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X) :=
    hM.theorem4bProposition63Theorem2
  let h4b : Theorem4bAtBase M :=
    hM.theorem4bAtBase_of_section7 hXsimple hrank hT2 hinduction
  let h82 : Proposition82aAtBase M :=
    hM.proposition82aAtBase_of_theorem4b hXsimple h4b hT2 hinduction
  let d83 : Lemma83Data M t := hM.lemma_8_3_data h82 ht htM
  let hbaseFull : Proposition84BaseFullStep M t d83.u :=
    hM.proposition_8_4_base_full_of_source_endpoints
      hXsimple ht htM h82 d83 h4b hinduction
  refine ⟨d83, ?_, ?_⟩
  · apply Proposition84Statement.of_steps M t d83.u
    · intro Y hYV hYne hI
      exact (hbaseFull Y hYV hYne hI).1
    · exact hM.proposition84ProperStep_of_source ht htM d83
  · intro Y hYV hYne hI
    exact (hbaseFull Y hYV hYne hI).2

/-- Source-facing wrapper that forgets the proof-support fields retained for
Lemma 11.4. -/
public theorem IsStronglyEmbedded.exists_proposition84_of_source_endpoints
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hXsimple : IsSimpleGroup X)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    {t : X} (ht : IsInvolution t) (htM : t ∉ M) :
    ∃ d83 : Lemma83Data M t,
      Proposition84Statement M t d83.u := by
  obtain ⟨d83, h84, _hsupport⟩ :=
    hM.exists_proposition84_with_modelSupport_of_source_endpoints
      hXsimple hrank hinduction ht htM
  exact ⟨d83, h84⟩

end CFSG.BenderSuzuki
