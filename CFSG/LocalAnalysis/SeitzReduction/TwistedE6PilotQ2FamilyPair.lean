module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyModel
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowTriRoots
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyCover
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

local instance twistedE6PilotQ2FamilyPairNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Image

variable {G M : Type*} [Group G] [Group M]

@[expose] def QCover.image (c : QCover G M) (Q : Subgroup G) : Subgroup M :=
  (Q.subgroupOf c.E).map c.p

theorem QCover.mem_image (c : QCover G M) {Q : Subgroup G} {y : G} (hy : y ∈ Q)
    (hyE : y ∈ c.E) : c.p ⟨y, hyE⟩ ∈ c.image Q :=
  ⟨⟨y, hyE⟩, mem_subgroupOf.2 hy, rfl⟩

theorem QCover.image_perfect (c : QCover G M) {Q : Subgroup G} (hQ : ⁅Q, Q⁆ = Q) (hQE : Q ≤ c.E) :
    ⁅c.image Q, c.image Q⁆ = c.image Q := by
  have h : ⁅Q.subgroupOf c.E, Q.subgroupOf c.E⁆ = Q.subgroupOf c.E := by
    apply Subgroup.map_injective c.E.subtype_injective
    rw [Subgroup.map_commutator, subgroupOf_map_subtype, inf_of_le_left hQE, hQ]
  rw [QCover.image, ← Subgroup.map_commutator, h]

theorem QCover.image_le_centralizer (c : QCover G M) {Q X : Subgroup G}
    (hQX : Q ≤ centralizer (X : Set G)) :
    c.image Q ≤ centralizer (c.image X : Set M) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_centralizer_iff.1 (hQX (mem_subgroupOf.1 hy)) _ (mem_subgroupOf.1 hx)

end Image

section Covers

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]
  {σ : K →+* K}

theorem center_le_ker_realize [CharP K 2] (h2 : (2 : K) = 0) :
    center (SpecialLinearGroup (Fin 6) K) ≤ (realize h2).ker := by
  rw [← LinearFlag.scalars_eq_center, ← ker_realizeA_eq_scalars h2]
  intro B hB
  rw [MonoidHom.mem_ker] at hB ⊢
  exact congrArg Subtype.val hB

theorem ker_conj_comp {S H : Type*} [Group S] [Group H] (g : H) (f : S →* H) :
    ((MulAut.conj g).toMonoidHom.comp f).ker = f.ker := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, conj_eq_one_iff]

variable [CharP K 2]

noncomputable abbrev nbElt (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (m : graphFixedRootGroup TwistTag.E6 K σ) : G :=
  ((e.symm m : L) : G)

@[expose] noncomputable def nbParam (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (Φ : SpecialLinearGroup (Fin 6) K →* G) (m : graphFixedRootGroup TwistTag.E6 K σ) :
    SpecialLinearGroup (Fin 6) K →* G :=
  (MulAut.conj (nbElt e m)).toMonoidHom.comp Φ

@[expose] noncomputable def nbModel (h2 : (2 : K) = 0) (m : graphFixedRootGroup TwistTag.E6 K σ) :
    SpecialLinearGroup (Fin 6) K →* ModGL TwistTag.E6.tag K :=
  (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom.comp (realize h2)

theorem ker_nbModel (h2 : (2 : K) = 0) (m : graphFixedRootGroup TwistTag.E6 K σ) :
    (nbModel h2 m).ker = (realize h2).ker :=
  ker_conj_comp _ _

theorem ker_realize_le_center' (h2 : (2 : K) = 0) :
    (realize h2).ker ≤ center (SpecialLinearGroup (Fin 6) K) := by
  rw [← LinearFlag.scalars_eq_center, ← ker_realizeA_eq_scalars h2]
  intro B hB
  rw [MonoidHom.mem_ker] at hB ⊢
  exact Subtype.ext hB

theorem ker_nbParam_le (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0)
    (Φ : SpecialLinearGroup (Fin 6) K →* G) (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (m : graphFixedRootGroup TwistTag.E6 K σ) : (nbParam e Φ m).ker ≤ (nbModel h2 m).ker := by
  rw [nbParam, ker_conj_comp, ker_nbModel]
  exact hΦ.trans (center_le_ker_realize h2)

theorem ker_nbModel_le (h2 : (2 : K) = 0) (m : graphFixedRootGroup TwistTag.E6 K σ) :
    (nbModel h2 m).ker ≤ center (SpecialLinearGroup (Fin 6) K) := by
  rw [ker_nbModel]
  exact ker_realize_le_center' h2

@[expose] noncomputable def highCover (h2 : (2 : K) = 0) (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K)) : QCover G (ModGL TwistTag.E6.tag K) :=
  QCover.ofParam Φ (realize h2) (hΦ.trans (center_le_ker_realize h2)) (ker_realize_le_center' h2)

@[expose] noncomputable def nbCover (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (h2 : (2 : K) = 0) (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K)) (m : graphFixedRootGroup TwistTag.E6 K σ) :
    QCover G (ModGL TwistTag.E6.tag K) :=
  QCover.ofParam (nbParam e Φ m) (nbModel h2 m) (ker_nbParam_le e h2 Φ hΦ m) (ker_nbModel_le h2 m)

theorem unitaryTwist_mem_center_iff (hσσ : ∀ c, σ (σ c) = c) {B : SpecialLinearGroup (Fin 6) K} :
    unitaryTwist σ B ∈ center (SpecialLinearGroup (Fin 6) K) ↔
      B ∈ center (SpecialLinearGroup (Fin 6) K) := by
  have key : ∀ C : SpecialLinearGroup (Fin 6) K, C ∈ center (SpecialLinearGroup (Fin 6) K) →
      unitaryTwist σ C ∈ center (SpecialLinearGroup (Fin 6) K) := by
    intro C hC
    rw [mem_center_iff] at hC ⊢
    intro D
    rw [← unitaryTwist_unitaryTwist hσσ D, ← map_mul, ← map_mul, hC]
  refine ⟨fun h => ?_, key B⟩
  rw [← unitaryTwist_unitaryTwist hσσ B]
  exact key _ h

theorem ker_nbParamF_le (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0)
    (Φ : SpecialLinearGroup (Fin 6) K →* G) (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (hσσ : ∀ c, σ (σ c) = c) (m : graphFixedRootGroup TwistTag.E6 K σ) :
    ((nbParam e Φ m).comp (unitaryTwist σ)).ker ≤ (nbModel h2 m).ker := by
  intro B hB
  have h1 : unitaryTwist σ B ∈ (nbParam e Φ m).ker := hB
  rw [nbParam, ker_conj_comp] at h1
  have h2' := (unitaryTwist_mem_center_iff hσσ).1 (hΦ h1)
  rw [ker_nbModel]
  exact center_le_ker_realize h2 h2'

@[expose] noncomputable def nbCoverF (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (h2 : (2 : K) = 0) (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K)) (hσσ : ∀ c, σ (σ c) = c)
    (m : graphFixedRootGroup TwistTag.E6 K σ) : QCover G (ModGL TwistTag.E6.tag K) :=
  QCover.ofParam ((nbParam e Φ m).comp (unitaryTwist σ)) (nbModel h2 m)
    (ker_nbParamF_le e h2 Φ hΦ hσσ m) (ker_nbModel_le h2 m)

theorem highCover_E (h2 : (2 : K) = 0) (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K)) : (highCover h2 Φ hΦ).E = Φ.range :=
  rfl

theorem nbCover_E (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0)
    (Φ : SpecialLinearGroup (Fin 6) K →* G) (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (m : graphFixedRootGroup TwistTag.E6 K σ) :
    (nbCover e h2 Φ hΦ m).E = Φ.range.map (MulAut.conj (nbElt e m)).toMonoidHom := by
  change (nbParam e Φ m).range = _
  rw [nbParam, MonoidHom.range_comp]

end Covers

section Normal

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {σ : K →+* K}

theorem QCover.ofParam_p' {S M : Type*} [Group S] [Group M] (Φ : S →* G) (ρ : S →* M)
    (hker : Φ.ker ≤ ρ.ker) (hZ : ρ.ker ≤ center S) {x : S} {y : G} (hxy : Φ x = y)
    (hy : y ∈ (QCover.ofParam Φ ρ hker hZ).E) : (QCover.ofParam Φ ρ hker hZ).p ⟨y, hy⟩ = ρ x := by
  subst hxy
  exact QCover.ofParam_p Φ ρ hker hZ x hy

theorem twistHom_coe_C0 (m : graphFixedRootGroup TwistTag.E6 K σ) :
    twistHom TwistTag.E6 K σ (m : ModGL TwistTag.E6.tag K) = m :=
  ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ).1
    (graphFixedRootGroup_le TwistTag.E6 K σ m.2)).2

theorem twistOn_nbCover_nbCoverF (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0)
    (Φ : SpecialLinearGroup (Fin 6) K →* G) (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (hσσ : ∀ c, σ (σ c) = c) (m : graphFixedRootGroup TwistTag.E6 K σ) :
    (nbCover e h2 Φ hΦ m).TwistOn (nbCoverF e h2 Φ hΦ hσσ m) (nbCover e h2 Φ hΦ m).E
      (twistHom TwistTag.E6 K σ) := by
  have hE : (nbCover e h2 Φ hΦ m).E ≤ (nbCoverF e h2 Φ hΦ hσσ m).E := by
    rintro _ ⟨B, rfl⟩
    exact ⟨unitaryTwist σ B, by
      simp only [MonoidHom.comp_apply, unitaryTwist_unitaryTwist hσσ]⟩
  refine ⟨le_rfl, hE, fun y hy => ?_⟩
  obtain ⟨B, hB⟩ := hy
  have e1 : ((nbParam e Φ m).comp (unitaryTwist σ)) (unitaryTwist σ B) = y := by
    simp only [MonoidHom.comp_apply, unitaryTwist_unitaryTwist hσσ, hB]
  have h1 := QCover.ofParam_p' ((nbParam e Φ m).comp (unitaryTwist σ)) (nbModel h2 m)
    (ker_nbParamF_le e h2 Φ hΦ hσσ m) (ker_nbModel_le h2 m) e1 (hE ⟨B, hB⟩)
  have h3 := QCover.ofParam_p' (nbParam e Φ m) (nbModel h2 m) (ker_nbParam_le e h2 Φ hΦ m)
    (ker_nbModel_le h2 m) hB ⟨B, hB⟩
  refine h1.trans (Eq.trans ?_ (congrArg (twistHom TwistTag.E6 K σ) h3.symm))
  simp only [nbModel, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    map_inv, twistHom_coe_C0, E6GraphLevi.twistHom_realize σ h2]

theorem symm_conj_eq_nbParam (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0)
    (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hN1 : ∀ B : SpecialLinearGroup (Fin 6) K, B ∈ unitarySL σ →
      ∀ hC : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ,
        Φ B = ((e.symm ⟨realize h2 B, hC⟩ : L) : G))
    (m : graphFixedRootGroup TwistTag.E6 K σ) {B : SpecialLinearGroup (Fin 6) K}
    (hB : B ∈ unitarySL σ)
    (hC : (m : ModGL TwistTag.E6.tag K) * realize h2 B * (m : ModGL TwistTag.E6.tag K)⁻¹ ∈
      graphFixedRootGroup TwistTag.E6 K σ) :
    ((e.symm ⟨_, hC⟩ : L) : G) = nbParam e Φ m B := by
  have hC' : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ := by
    have h1 : realize h2 B = (m : ModGL TwistTag.E6.tag K)⁻¹ *
        ((m : ModGL TwistTag.E6.tag K) * realize h2 B * (m : ModGL TwistTag.E6.tag K)⁻¹) *
          (m : ModGL TwistTag.E6.tag K) := by group
    rw [h1]
    exact mul_mem (mul_mem (inv_mem m.2) hC) m.2
  have h1 : (⟨_, hC⟩ : graphFixedRootGroup TwistTag.E6 K σ) = m * ⟨_, hC'⟩ * m⁻¹ :=
    Subtype.ext rfl
  rw [h1, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv, ← hN1 B hB hC']
  rfl

end Normal

section Symm

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {σ : K →+* K}

@[expose] noncomputable def symmOn (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    {U : Subgroup (ModGL TwistTag.E6.tag K)} (hU : U ≤ graphFixedRootGroup TwistTag.E6 K σ) :
    U →* G :=
  L.subtype.comp (e.symm.toMonoidHom.comp (Subgroup.inclusion hU))

theorem isSection_symmOn_nbCover (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (h2 : (2 : K) = 0) (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (hN1 : ∀ B : SpecialLinearGroup (Fin 6) K, B ∈ unitarySL σ →
      ∀ hC : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ,
        Φ B = ((e.symm ⟨realize h2 B, hC⟩ : L) : G))
    (m : graphFixedRootGroup TwistTag.E6 K σ) {U : Subgroup (ModGL TwistTag.E6.tag K)}
    (hU : U ≤ graphFixedRootGroup TwistTag.E6 K σ)
    (hUD : ∀ u ∈ U, ∃ B ∈ unitarySL σ,
      (m : ModGL TwistTag.E6.tag K) * realize h2 B * (m : ModGL TwistTag.E6.tag K)⁻¹ = u) :
    (nbCover e h2 Φ hΦ m).IsSection (symmOn e hU) := by
  intro u
  obtain ⟨B, hB, hBu⟩ := hUD u u.2
  have hC : (m : ModGL TwistTag.E6.tag K) * realize h2 B * (m : ModGL TwistTag.E6.tag K)⁻¹ ∈
      graphFixedRootGroup TwistTag.E6 K σ := hBu ▸ hU u.2
  have hval : symmOn e hU u = nbParam e Φ m B := by
    rw [← symm_conj_eq_nbParam e h2 Φ hN1 m hB hC]
    change ((e.symm ⟨(u : ModGL TwistTag.E6.tag K), hU u.2⟩ : L) : G) = _
    congr 2
    exact Subtype.ext hBu.symm
  refine ⟨⟨nbParam e Φ m B, B, rfl⟩, hval.symm, ?_⟩
  exact (QCover.ofParam_p' (nbParam e Φ m) (nbModel h2 m) (ker_nbParam_le e h2 Φ hΦ m)
    (ker_nbModel_le h2 m) rfl _).trans hBu

theorem isSection_symmOn_highCover (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (h2 : (2 : K) = 0) (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (hN1 : ∀ B : SpecialLinearGroup (Fin 6) K, B ∈ unitarySL σ →
      ∀ hC : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ,
        Φ B = ((e.symm ⟨realize h2 B, hC⟩ : L) : G))
    {U : Subgroup (ModGL TwistTag.E6.tag K)} (hU : U ≤ graphFixedRootGroup TwistTag.E6 K σ)
    (hUD : ∀ u ∈ U, ∃ B ∈ unitarySL σ, realize h2 B = u) :
    (highCover h2 Φ hΦ).IsSection (symmOn e hU) := by
  intro u
  obtain ⟨B, hB, hBu⟩ := hUD u u.2
  have hC : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ := hBu ▸ hU u.2
  have hval : symmOn e hU u = Φ B := by
    rw [hN1 B hB hC]
    change ((e.symm ⟨(u : ModGL TwistTag.E6.tag K), hU u.2⟩ : L) : G) = _
    congr 2
    exact Subtype.ext hBu.symm
  refine ⟨⟨Φ B, B, rfl⟩, hval.symm, ?_⟩
  exact (QCover.ofParam_p' Φ (realize h2) (hΦ.trans (center_le_ker_realize h2))
    (ker_realize_le_center' h2) rfl _).trans hBu

end Symm

section PairFacts

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {σ : K →+* K}

abbrev ovlRoot (p : Fin 3) : Fin TwistTag.E6.tag.rank → ℤ :=
  matRoot (ovlPt p) (Fin.rev (ovlPt p))

theorem ovlRoot_facts (p : Fin 3) : IsRoot TwistTag.E6.tag (ovlRoot p) ∧ ovlRoot p 1 = 0 ∧
    permLattice TwistTag.E6.perm (ovlRoot p) = ovlRoot p := by
  obtain ⟨-, -, -, -, -, -, -, hpp⟩ := ovl_check p
  refine ⟨isRoot_matRoot hpp, matRoot_one _ _, ?_⟩
  rw [(rho_matRoot_check_ovl _ _).1, Fin.rev_rev]

theorem rootRankOneGroup_ovlRoot_le_su6Levi {k : Type} [Field k] {ι : k →+* K}
    (hι : ∀ c, σ (ι c) = ι c) (p : Fin 3) :
    TwistedE6Pilot.rootRankOneGroup ι (ovlRoot p) ≤ su6Levi σ := by
  obtain ⟨h1, h2, h3⟩ := ovlRoot_facts p
  exact rootRankOneGroup_le_su6Levi_tri hι h1 h2 h3

theorem realize_comp_blockSL_injective (h2 : (2 : K) = 0) (p : Fin 3) :
    Function.Injective ((realize h2).comp (LinearPilot.blockSpecialLinear (K := K)
      (ovlSet p)).subtype) := by
  intro x y hxy
  obtain ⟨x', hx'⟩ : (x : SpecialLinearGroup (Fin 6) K) ∈ (ovlEmbed (K := K) p).range := by
    rw [range_ovlEmbed]
    exact x.2
  obtain ⟨y', hy'⟩ : (y : SpecialLinearGroup (Fin 6) K) ∈ (ovlEmbed (K := K) p).range := by
    rw [range_ovlEmbed]
    exact y.2
  have h := realize_ovlEmbed_injective h2 p (a₁ := x') (a₂ := y') (by
    simp only [MonoidHom.comp_apply] at hxy ⊢
    rw [hx', hy']
    exact hxy)
  apply Subtype.ext
  rw [← hx', ← hy', h]

theorem mem_highCover_of_mem_modelToG [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (h2 : (2 : K) = 0) (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (hN1 : ∀ B : SpecialLinearGroup (Fin 6) K, B ∈ unitarySL σ →
      ∀ hC : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ,
        Φ B = ((e.symm ⟨realize h2 B, hC⟩ : L) : G))
    {Y : Subgroup (ModGL TwistTag.E6.tag K)} (hYD : Y ≤ su6Levi σ) {x : G}
    (hx : x ∈ modelToG e Y) :
    ∃ hxE : x ∈ (highCover h2 Φ hΦ).E, (highCover h2 Φ hΦ).p ⟨x, hxE⟩ ∈ Y := by
  obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hx
  have hy' := hYD hy
  rw [su6Levi, (subsystemGroup_inf_eq_map_realize hK hσ h2).1] at hy'
  obtain ⟨B, hB, hBy⟩ := hy'
  have hC : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ := hBy ▸ y.2
  have hval : ((e.symm y : L) : G) = Φ B := by
    rw [hN1 B hB hC]
    congr 2
    exact Subtype.ext hBy.symm
  refine ⟨hval ▸ ⟨B, rfl⟩, ?_⟩
  have h1 := QCover.ofParam_p' Φ (realize h2) (hΦ.trans (center_le_ker_realize h2))
    (ker_realize_le_center' h2) hval.symm (hval ▸ ⟨B, rfl⟩)
  rw [show (highCover h2 Φ hΦ).p ⟨_, hval ▸ ⟨B, rfl⟩⟩ = realize h2 B from h1, hBy]
  exact hy

theorem mem_nbCover_of_mem_modelToG [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (h2 : (2 : K) = 0) (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (hN1 : ∀ B : SpecialLinearGroup (Fin 6) K, B ∈ unitarySL σ →
      ∀ hC : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ,
        Φ B = ((e.symm ⟨realize h2 B, hC⟩ : L) : G))
    (m : graphFixedRootGroup TwistTag.E6 K σ) {Y : Subgroup (ModGL TwistTag.E6.tag K)}
    (hYD : Y.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom ≤ su6Levi σ) {x : G}
    (hx : x ∈ modelToG e Y) :
    ∃ hxE : x ∈ (nbCover e h2 Φ hΦ m).E, (nbCover e h2 Φ hΦ m).p ⟨x, hxE⟩ ∈ Y := by
  obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hx
  have hy' : (m : ModGL TwistTag.E6.tag K)⁻¹ * y * (m : ModGL TwistTag.E6.tag K) ∈ su6Levi σ := by
    have := hYD ⟨y, hy, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  rw [su6Levi, (subsystemGroup_inf_eq_map_realize hK hσ h2).1] at hy'
  obtain ⟨B, hB, hBy⟩ := hy'
  have hmy : (m : ModGL TwistTag.E6.tag K) * realize h2 B * (m : ModGL TwistTag.E6.tag K)⁻¹ =
      y := by
    rw [hBy]
    group
  have hC : (m : ModGL TwistTag.E6.tag K) * realize h2 B * (m : ModGL TwistTag.E6.tag K)⁻¹ ∈
      graphFixedRootGroup TwistTag.E6 K σ := hmy ▸ y.2
  have hval : ((e.symm y : L) : G) = nbParam e Φ m B := by
    rw [← symm_conj_eq_nbParam e h2 Φ hN1 m hB hC]
    congr 2
    exact Subtype.ext hmy.symm
  refine ⟨hval ▸ ⟨B, rfl⟩, ?_⟩
  have h1 := QCover.ofParam_p' (nbParam e Φ m) (nbModel h2 m) (ker_nbParam_le e h2 Φ hΦ m)
    (ker_nbModel_le h2 m) hval.symm (hval ▸ ⟨B, rfl⟩)
  rw [show (nbCover e h2 Φ hΦ m).p ⟨_, hval ▸ ⟨B, rfl⟩⟩ = nbModel h2 m B from h1]
  change (m : ModGL TwistTag.E6.tag K) * realize h2 B * (m : ModGL TwistTag.E6.tag K)⁻¹ ∈ Y
  rw [hmy]
  exact hy

theorem highCover_image_le (h2 : (2 : K) = 0) (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K)) (H : Subgroup G) :
    (highCover h2 Φ hΦ).image H ≤ subsystemGroup TwistTag.E6.tag K setA := by
  rintro _ ⟨⟨y, B, rfl⟩, -, rfl⟩
  rw [← E6GraphLevi.range_realize h2]
  exact ⟨B, (QCover.ofParam_p' Φ (realize h2) (hΦ.trans (center_le_ker_realize h2))
    (ker_realize_le_center' h2) rfl _).symm⟩

theorem nbCover_image_le (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0)
    (Φ : SpecialLinearGroup (Fin 6) K →* G) (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (m : graphFixedRootGroup TwistTag.E6 K σ) (H : Subgroup G) :
    (nbCover e h2 Φ hΦ m).image H ≤ (subsystemGroup TwistTag.E6.tag K setA).map
      (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom := by
  rintro _ ⟨⟨y, B, rfl⟩, -, rfl⟩
  refine ⟨realize h2 B, by rw [← E6GraphLevi.range_realize h2]; exact ⟨B, rfl⟩, ?_⟩
  exact (QCover.ofParam_p' (nbParam e Φ m) (nbModel h2 m) (ker_nbParam_le e h2 Φ hΦ m)
    (ker_nbModel_le h2 m) rfl _).symm

theorem subsystemGroup_le_centralizer_thetaRankOneGroup (h2 : (2 : K) = 0) {k : Type} [Field k]
    (ι : k →+* K) :
    subsystemGroup TwistTag.E6.tag K setA ≤
      centralizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag K)) :=
  (subsystemGroup_le_centralizer_thetaSL2 h2).trans
    (centralizer_le (thetaRankOneGroup_le_range h2 ι))

end PairFacts

section Pair

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem range_perfect_of_perfect {M H : Type*} [Group M] [Group H] {P : Subgroup M}
    (hP : ⁅P, P⁆ = P) (s : P →* H) : ⁅s.range, s.range⁆ = s.range := by
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem conj_inv_comp_conj {M : Type*} [Group M] (g : M) :
    (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id M := by
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.id_apply]
  group

theorem pair_image_facts [Finite K] [CharP K 2] (hk : Nat.card k = 2)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (hA : Nat.card A = 3) (h2 : (2 : K) = 0)
    (hX : FieldCoverParamX σ h2 e t (modelToG e A)) (m : graphFixedRootGroup TwistTag.E6 K σ)
    (p p' : Fin 3)
    (hm1 : A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom ≤
      TwistedE6Pilot.rootRankOneGroup (algebraMap k K) (ovlRoot p))
    (hm2 : A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom ≤
      TwistedE6Pilot.rootRankOneGroup (algebraMap k K) (ovlRoot p'))
    {Q : Subgroup G} (hQperf : ⁅Q, Q⁆ = Q) (hQc : Q ≤ (highCover h2 hX.Φ hX.ker_le).E)
    (hQc' : Q ≤ (nbCover e h2 hX.Φ hX.ker_le m).E)
    (hQX : Q ≤ centralizer (modelToG e A : Set G))
    (hQXm : Q ≤ centralizer (modelToG e
      (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G)) :
    (highCover h2 hX.Φ hX.ker_le).image Q ≤ ovlLevi h2 p ∧
      (nbCover e h2 hX.Φ hX.ker_le m).image Q ≤ ovlLevi h2 p := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hι : ∀ c, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card (f := 1) (by rw [hk]; rfl) hσ)
  have hYcard : Nat.card (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) = 3 := by
    rw [card_map_of_injective (MulAut.conj _).injective, hA]
  have hY'card :
      Nat.card (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom) = 3 := by
    rw [card_map_of_injective (MulAut.conj _).injective, hA]
  have hYD := hm1.trans (rootRankOneGroup_ovlRoot_le_su6Levi hι p)
  have hY'D := hm2.trans (rootRankOneGroup_ovlRoot_le_su6Levi hι p')
  have hLA := subsystemGroup_le_centralizer_thetaRankOneGroup h2 (algebraMap k K)
  have hLAadj := subsystemGroup_le_adjointGroup_E6 (K := K) setA
  have hmadj : (m : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    ((graphFixedRootGroup_le TwistTag.E6 K σ).trans inf_le_left) m.2
  have hYimg : A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom ≤
      (highCover h2 hX.Φ hX.ker_le).image
        (modelToG e (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom)) := by
    intro y hy
    have hyC : y ∈ graphFixedRootGroup TwistTag.E6 K σ := (hYD hy).2
    have hx := symm_mem_modelToG e (x := ⟨y, hyC⟩) hy
    obtain ⟨hyE, -⟩ := mem_highCover_of_mem_modelToG hK hσ e h2 hX.Φ hX.ker_le hX.N1 hYD hx
    have h1 := (highCover h2 hX.Φ hX.ker_le).mem_image hx hyE
    have hy' := hYD hy
    rw [su6Levi, (subsystemGroup_inf_eq_map_realize hK hσ h2).1] at hy'
    obtain ⟨B, hB, hBy⟩ := hy'
    have hC : realize h2 B ∈ graphFixedRootGroup TwistTag.E6 K σ := hBy ▸ hyC
    have hval : ((e.symm ⟨y, hyC⟩ : L) : G) = hX.Φ B := by
      rw [hX.N1 B hB hC]
      congr 2
      exact Subtype.ext hBy.symm
    have h3 := QCover.ofParam_p' hX.Φ (realize h2) (hX.ker_le.trans (center_le_ker_realize h2))
      (ker_realize_le_center' h2) hval.symm hyE
    have h4 : (highCover h2 hX.Φ hX.ker_le).p ⟨_, hyE⟩ = y := h3.trans hBy
    rwa [h4] at h1
  have hAimg : A ≤ (nbCover e h2 hX.Φ hX.ker_le m).image (modelToG e A) := by
    intro a ha
    have haC : a ∈ graphFixedRootGroup TwistTag.E6 K σ := by
      have := hAJ ha
      exact thetaRankOneGroup_le_graphFixedRootGroup h2
        (sigma_eq_pow_card (f := 1) (by rw [hk]; rfl) hσ) this
    have hx := symm_mem_modelToG e (x := ⟨a, haC⟩) ha
    have hD : A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom ≤ su6Levi σ := hY'D
    obtain ⟨haE, -⟩ := mem_nbCover_of_mem_modelToG hK hσ e h2 hX.Φ hX.ker_le hX.N1 m hD hx
    have h1 := (nbCover e h2 hX.Φ hX.ker_le m).mem_image hx haE
    have ha' : (m : ModGL TwistTag.E6.tag K)⁻¹ * a * (m : ModGL TwistTag.E6.tag K) ∈ su6Levi σ := by
      have := hD ⟨a, ha, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
    rw [su6Levi, (subsystemGroup_inf_eq_map_realize hK hσ h2).1] at ha'
    obtain ⟨B, hB, hBa⟩ := ha'
    have hma :
        (m : ModGL TwistTag.E6.tag K) * realize h2 B * (m : ModGL TwistTag.E6.tag K)⁻¹ = a := by
      rw [hBa]
      group
    have hC : (m : ModGL TwistTag.E6.tag K) * realize h2 B * (m : ModGL TwistTag.E6.tag K)⁻¹ ∈
        graphFixedRootGroup TwistTag.E6 K σ := hma ▸ haC
    have hval : ((e.symm ⟨a, haC⟩ : L) : G) = nbParam e hX.Φ m B := by
      rw [← symm_conj_eq_nbParam e h2 hX.Φ hX.N1 m hB hC]
      congr 2
      exact Subtype.ext hma.symm
    have h3 := QCover.ofParam_p' (nbParam e hX.Φ m) (nbModel h2 m)
      (ker_nbParam_le e h2 hX.Φ hX.ker_le m) (ker_nbModel_le h2 m) hval.symm haE
    have h4 : (nbCover e h2 hX.Φ hX.ker_le m).p ⟨_, haE⟩ = a := h3.trans hma
    rwa [h4] at h1
  refine ⟨?_, ?_⟩
  ·
    have hP := (highCover h2 hX.Φ hX.ker_le).image_perfect hQperf hQc
    have hPL := highCover_image_le h2 hX.Φ hX.ker_le Q
    refine le_ovlLevi_of_perfect hk hK' h2 (algebraMap k K) p hAJ hA hm1 hYcard hP
      (hPL.trans hLAadj) (hPL.trans (hLA.trans (centralizer_le hAJ))) ?_
    exact ((highCover h2 hX.Φ hX.ker_le).image_le_centralizer hQXm).trans (centralizer_le hYimg)
  ·
    have hP := (nbCover e h2 hX.Φ hX.ker_le m).image_perfect hQperf hQc'
    have hPL := nbCover_image_le e h2 hX.Φ hX.ker_le m Q
    refine le_ovlLevi_of_perfect hk hK' h2 (algebraMap k K) p hAJ hA hm1 hYcard hP ?_ ?_ ?_
    · refine hPL.trans ?_
      rintro _ ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem hmadj (hLAadj hx)) (inv_mem hmadj)
    · exact ((nbCover e h2 hX.Φ hX.ker_le m).image_le_centralizer hQX).trans (centralizer_le hAimg)
    · refine hPL.trans ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      have h1 := mem_centralizer_iff.1 (hLA hx) a (hAJ ha)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc (m : ModGL TwistTag.E6.tag K) * a * (m : ModGL TwistTag.E6.tag K)⁻¹ *
            ((m : ModGL TwistTag.E6.tag K) * x * (m : ModGL TwistTag.E6.tag K)⁻¹) =
          (m : ModGL TwistTag.E6.tag K) * (a * x) * (m : ModGL TwistTag.E6.tag K)⁻¹ := by group
        _ = (m : ModGL TwistTag.E6.tag K) * (x * a) * (m : ModGL TwistTag.E6.tag K)⁻¹ := by rw [h1]
        _ = _ := by group

theorem twistOn_high_nbCover [Finite K] [CharP K 2] (hk : Nat.card k = 2)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (hA : Nat.card A = 3) (h2 : (2 : K) = 0)
    (hX : FieldCoverParamX σ h2 e t (modelToG e A)) (m : graphFixedRootGroup TwistTag.E6 K σ)
    (p p' : Fin 3)
    (hm1 : A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom ≤
      TwistedE6Pilot.rootRankOneGroup (algebraMap k K) (ovlRoot p))
    (hm2 : A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom ≤
      TwistedE6Pilot.rootRankOneGroup (algebraMap k K) (ovlRoot p')) :
    (highCover h2 hX.Φ hX.ker_le).TwistOn (nbCover e h2 hX.Φ hX.ker_le m)
        (perfectCore (centralizer (modelToG e A : Set G) ⊓
          centralizer (modelToG e (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) :
            Set G))) (MonoidHom.id _) ∨
      (highCover h2 hX.Φ hX.ker_le).TwistOn (nbCover e h2 hX.Φ hX.ker_le m)
        (perfectCore (centralizer (modelToG e A : Set G) ⊓
          centralizer (modelToG e (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) :
            Set G))) (twistHom TwistTag.E6 K σ) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ]
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  have hι : ∀ c, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card (f := 1) (by rw [hk]; rfl) hσ)
  have hYD := hm1.trans (rootRankOneGroup_ovlRoot_le_su6Levi hι p)
  have hY'D := hm2.trans (rootRankOneGroup_ovlRoot_le_su6Levi hι p')
  have hYcard : Nat.card (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) = 3 := by
    rw [card_map_of_injective (MulAut.conj _).injective, hA]
  have hY'card :
      Nat.card (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom) = 3 := by
    rw [card_map_of_injective (MulAut.conj _).injective, hA]
  have hLA := subsystemGroup_le_centralizer_thetaRankOneGroup h2 (algebraMap k K)
  have hLAadj := subsystemGroup_le_adjointGroup_E6 (K := K) setA
  have hmadj : (m : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    ((graphFixedRootGroup_le TwistTag.E6 K σ).trans inf_le_left) m.2
  have hAC : A ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    hAJ.trans (thetaRankOneGroup_le_graphFixedRootGroup h2 (sigma_eq_pow_card (f := 1)
      (by rw [hk]; rfl) hσ))
  have hcE : (highCover h2 hX.Φ hX.ker_le).E = centralizerPerfectCore (modelToG e A) :=
    hX.range_eq
  have hc'E : (nbCover e h2 hX.Φ hX.ker_le m).E = centralizerPerfectCore
      (modelToG e (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom)) := by
    rw [nbCover_E, hX.range_eq, F4Pilot.map_centralizerPerfectCore, modelToG_map_conj]
  set Q := perfectCore (centralizer (modelToG e A : Set G) ⊓
    centralizer (modelToG e (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) :
      Set G)) with hQ
  have hQperf : ⁅Q, Q⁆ = Q := perfectCore_perfect _
  have hQc : Q ≤ (highCover h2 hX.Φ hX.ker_le).E := by
    rw [hcE]
    exact CFSG.Quasithin.perfectCore_mono inf_le_left
  have hQc' : Q ≤ (nbCover e h2 hX.Φ hX.ker_le m).E := by
    rw [hc'E]
    exact CFSG.Quasithin.perfectCore_mono inf_le_right
  have hQX : Q ≤ centralizer (modelToG e A : Set G) := (perfectCore_le _).trans inf_le_left
  have hQXm : Q ≤ centralizer (modelToG e (A.map (MulAut.conj
      (m : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G) := (perfectCore_le _).trans inf_le_right
  have hEX' : (highCover h2 hX.Φ hX.ker_le).E ≤ centralizer (modelToG e A : Set G) := by
    rw [hcE]
    exact F4Pilot.centralizerPerfectCore_le_centralizer _
  have hEXm' : (nbCover e h2 hX.Φ hX.ker_le m).E ≤ centralizer (modelToG e (A.map (MulAut.conj
      (m : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G) := by
    rw [hc'E]
    exact F4Pilot.centralizerPerfectCore_le_centralizer _
  obtain ⟨hP, hP'⟩ := pair_image_facts hk hK hσ e hAJ hA h2 hX m p p' hm1 hm2 hQperf hQc hQc'
    hQX hQXm
  have hΛA : ovlLevi h2 p ≤ centralizer (A : Set (ModGL TwistTag.E6.tag K)) :=
    (ovlLevi_le_subsystemGroup h2 p).trans (hLA.trans (centralizer_le hAJ))
  have hΛY : ovlLevi h2 p ≤ centralizer
      (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom :
        Set (ModGL TwistTag.E6.tag K)) :=
    (ovlLevi_le_centralizer_rootRankOneGroup h2 p (algebraMap k K)).trans (centralizer_le hm1)
  have hΛperf := ovlLevi_perfect h2 p
  have hΛ' : (ovlLevi h2 p).map (MulAut.conj (m : ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom ≤
      ovlLevi h2 p' := by
    refine le_ovlLevi_of_perfect hk hK' h2 (algebraMap k K) p' hAJ hA hm2 hY'card ?_ ?_ ?_ ?_
    · rw [← Subgroup.map_commutator, hΛperf]
    · rintro _ ⟨x, hx, rfl⟩
      have hxa := hLAadj (ovlLevi_le_subsystemGroup h2 p hx)
      exact mul_mem (mul_mem (inv_mem hmadj) hxa) (inv_inv (m : ModGL TwistTag.E6.tag K) ▸ hmadj)
    · rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_iff]
      intro a ha
      have h1 := mem_centralizer_iff.1 (hΛY hx) ((m : ModGL TwistTag.E6.tag K) * a *
        (m : ModGL TwistTag.E6.tag K)⁻¹) ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1 ⊢
      calc a * ((m : ModGL TwistTag.E6.tag K)⁻¹ * x * (m : ModGL TwistTag.E6.tag K)) =
          (m : ModGL TwistTag.E6.tag K)⁻¹ * ((m : ModGL TwistTag.E6.tag K) * a *
            (m : ModGL TwistTag.E6.tag K)⁻¹ * x) * (m : ModGL TwistTag.E6.tag K) := by group
        _ = (m : ModGL TwistTag.E6.tag K)⁻¹ * (x * ((m : ModGL TwistTag.E6.tag K) * a *
            (m : ModGL TwistTag.E6.tag K)⁻¹)) * (m : ModGL TwistTag.E6.tag K) := by rw [h1]
        _ = _ := by group
    · rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      have h1 := mem_centralizer_iff.1 (hΛA hx) a ha
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc (m : ModGL TwistTag.E6.tag K)⁻¹ * a * (m : ModGL TwistTag.E6.tag K) *
            ((m : ModGL TwistTag.E6.tag K)⁻¹ * x * (m : ModGL TwistTag.E6.tag K)) =
          (m : ModGL TwistTag.E6.tag K)⁻¹ * (a * x) * (m : ModGL TwistTag.E6.tag K) := by group
        _ = (m : ModGL TwistTag.E6.tag K)⁻¹ * (x * a) * (m : ModGL TwistTag.E6.tag K) := by rw [h1]
        _ = _ := by group
  have hXmE := fun x hx => mem_highCover_of_mem_modelToG hK hσ e h2 hX.Φ hX.ker_le hX.N1 hYD
    (x := x) hx
  have hXE' := fun x hx => mem_nbCover_of_mem_modelToG hK hσ e h2 hX.Φ hX.ker_le hX.N1 m hY'D
    (x := x) hx
  obtain ⟨s, hs, -⟩ := QCover.exists_isSection_ofParam hX.Φ (realize h2)
    (hX.ker_le.trans (center_le_ker_realize h2)) (ker_realize_le_center' h2)
    (realize_comp_blockSL_injective h2 p) (H := ovlLevi h2 p) le_rfl
  have hs' : (highCover h2 hX.Φ hX.ker_le).IsSection s := hs
  have hsQ : ∀ h, s h ∈ Q := by
    have hle : s.range ≤ centralizer (modelToG e A : Set G) ⊓ centralizer
        (modelToG e (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G) := by
      rintro _ ⟨h, rfl⟩
      refine ⟨?_, ?_⟩
      · exact hEX' (hs'.mem h)
      · exact hs'.mem_centralizer hΛperf (X := modelToG e (A.map (MulAut.conj
          (m : ModGL TwistTag.E6.tag K)).toMonoidHom)) (fun x hx => (hXmE x hx).1)
          (fun x hx h' => mem_centralizer_iff.1 (hΛY h'.2) _ (hXmE x hx).2) h
    intro h
    exact le_perfectCore_of_perfect hle (range_perfect_of_perfect hΛperf s) ⟨h, rfl⟩
  have hΛT : ovlLevi h2 p ≤ (LinearPilot.blockSpecialLinear (K := K) (ovlSet p')).map
      (nbModel h2 m) := by
    intro y hy
    obtain ⟨B, hB, hBy⟩ := hΛ' ⟨y, hy, rfl⟩
    refine ⟨B, hB, ?_⟩
    change (m : ModGL TwistTag.E6.tag K) * realize h2 B * (m : ModGL TwistTag.E6.tag K)⁻¹ = y
    rw [hBy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  obtain ⟨sN, hsN0, -⟩ := QCover.exists_isSection_ofParam (nbParam e hX.Φ m) (nbModel h2 m)
    (ker_nbParam_le e h2 hX.Φ hX.ker_le m) (ker_nbModel_le h2 m)
    ((MulAut.conj (m : ModGL TwistTag.E6.tag K)).injective.comp
      (realize_comp_blockSL_injective h2 p')) hΛT
  have hsN : (nbCover e h2 hX.Φ hX.ker_le m).IsSection sN := hsN0
  have hsNQ : ∀ h, sN h ∈ Q := by
    have hle : sN.range ≤ centralizer (modelToG e A : Set G) ⊓ centralizer
        (modelToG e (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G) := by
      rintro _ ⟨h, rfl⟩
      refine ⟨?_, hEXm' (hsN.mem h)⟩
      exact hsN.mem_centralizer hΛperf (X := modelToG e A) (fun x hx => (hXE' x hx).1)
        (fun x hx h' => mem_centralizer_iff.1 (hΛA h'.2) _ (hXE' x hx).2) h
    intro h
    exact le_perfectCore_of_perfect hle (range_perfect_of_perfect hΛperf sN) ⟨h, rfl⟩
  have hUC : ovlGroup h2 σ p ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    (ovlGroup_le_su6Levi hK h2 hσ p).trans inf_le_right
  have hr := isSection_symmOn_highCover e h2 hX.Φ hX.ker_le hX.N1 hUC (fun u hu => by
    obtain ⟨B, hB, rfl⟩ := hu
    exact ⟨B, hB.1, rfl⟩)
  have hr' := isSection_symmOn_nbCover e h2 hX.Φ hX.ker_le hX.N1 m hUC (fun u hu => by
    have h1 : (m : ModGL TwistTag.E6.tag K)⁻¹ * u * (m : ModGL TwistTag.E6.tag K) ∈
        subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
      refine Subgroup.mem_inf.2
        ⟨ovlLevi_le_subsystemGroup h2 p' (hΛ' ⟨u, ovlGroup_le_ovlLevi h2 σ p hu, ?_⟩), ?_⟩
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      · exact mul_mem (mul_mem (inv_mem m.2) (hUC hu)) m.2
    rw [(subsystemGroup_inf_eq_map_realize hK hσ h2).1] at h1
    obtain ⟨B, hB, hBu⟩ := h1
    refine ⟨B, hB, ?_⟩
    rw [hBu]
    group)
  rcases QCover.eq_or_eq_of_overlap hQc hQc' (center_ovlLevi h2 p)
      (fun y hy => hP ((highCover h2 hX.Φ hX.ker_le).mem_image hy (hQc hy)))
      (fun y hy => hP' ((nbCover e h2 hX.Φ hX.ker_le m).mem_image hy (hQc' hy)))
      hs' hsN hsQ hsNQ (ovlGroup_le_ovlLevi h2 σ p) (ovlGroup_perfect hK h2 hσ p) hr hr'
      (ovlLeviTwist h2 hσσ p) (ovlLevi_rigid hK h2 hσ hσσ p) with h | h
  · left
    exact ⟨hQc, hQc', fun y hy => by rw [h y hy]; rfl⟩
  · right
    exact ⟨hQc, hQc', fun y hy => by rw [h y hy, ovlLeviTwist_coe]⟩

end Pair

end CFSG.SeitzReduction.TwistedE6Pilot
