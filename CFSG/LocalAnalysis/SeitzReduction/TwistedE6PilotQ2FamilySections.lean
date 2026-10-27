module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyMembers
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyTriangle

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.E6Pilot (adjDatumE6 E6Neighbour amalgamRoots amalgamPlacement)

local instance twistedE6PilotQ2FamilySectionsNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Transfer

variable {G M : Type*} [Group G] [Group M]

theorem QCover.IsSection.of_overlap {c c' : QCover G M} {X X' : Subgroup G}
    (hagr : c.TwistOn c' (perfectCore (centralizer (X : Set G) ⊓ centralizer (X' : Set G)))
      (MonoidHom.id M))
    (hcE : c.E ≤ centralizer (X : Set G)) {H : Subgroup M} (hH : ⁅H, H⁆ = H) {s : H →* G}
    (hs : c.IsSection s) (hX'E : X' ≤ c.E)
    (hcomm : ∀ x (hx : x ∈ X') (h : H), Commute (c.p ⟨x, hX'E hx⟩) (h : M)) :
    c'.IsSection s := by
  refine hs.of_twistOn hagr fun h => ?_
  have hrange : s.range ≤ centralizer (X : Set G) ⊓ centralizer (X' : Set G) := by
    rintro _ ⟨h', rfl⟩
    exact ⟨hcE (hs.mem h'), hs.mem_centralizer hH hX'E hcomm h'⟩
  have hperf : ⁅s.range, s.range⁆ = s.range := by
    have : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  exact le_perfectCore_of_perfect hrange hperf ⟨h, rfl⟩

end Transfer

section Sections


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem triN2_conj_pinnedX_matRoot (σ : K →+* K) {a b : Fin 6} (hab : a ≠ b) (c : K) :
    (triN2 σ : ModGL TwistTag.E6.tag K) * pinnedX TwistTag.E6.tag K (matRoot a b) c *
        (triN2 σ : ModGL TwistTag.E6.tag K)⁻¹ =
      pinnedX TwistTag.E6.tag K (nbAct .six (matRoot a b)) c :=
  twistedE6RelWeyl_conj_pinnedX triWord2 (isRoot_matRoot hab) c

theorem triN3_conj_pinnedX_matRoot (σ : K →+* K) {a b : Fin 6} (hab : a ≠ b) (c : K) :
    (triN3 σ : ModGL TwistTag.E6.tag K) * pinnedX TwistTag.E6.tag K (matRoot a b) c *
        (triN3 σ : ModGL TwistTag.E6.tag K)⁻¹ =
      pinnedX TwistTag.E6.tag K (nbAct .three (matRoot a b)) c :=
  twistedE6RelWeyl_conj_pinnedX triWord3 (isRoot_matRoot hab) c

theorem exists_isSection_highCover (h2 : (2 : K) = 0) (Φ : SpecialLinearGroup (Fin 6) K →* G)
    (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K)) {J : Finset (Fin (Tag.rank .E6))}
    (hJ : J ⊆ E6Neighbour.high.nodes) (hJ2 : J.card ≤ 2) :
    ∃ s : memModel K J →* G, (highCover h2 Φ hΦ).IsSection s := by
  obtain ⟨x, hx⟩ := exists_not_mem_memCoords .high hJ2
  obtain ⟨s, hs, -⟩ := QCover.exists_isSection_ofParam Φ (realize h2)
    (hΦ.trans (center_le_ker_realize h2)) (ker_realize_le_center' h2)
    (realize_comp_blockSL_injective_of_not_mem h2 hx)
    (memModel_le_map_blockSL .high hJ (realize h2) fun hab c => realize_transvection_ovl h2 hab c)
  exact ⟨s, hs⟩

variable {σ : K →+* K}

theorem exists_isSection_nbCover (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0)
    (Φ : SpecialLinearGroup (Fin 6) K →* G) (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (hσσ : ∀ c, σ (σ c) = c) (m : graphFixedRootGroup TwistTag.E6 K σ) (N : E6Neighbour)
    (hm : ∀ {a b : Fin 6}, a ≠ b → ∀ c : K, (m : ModGL TwistTag.E6.tag K) *
      pinnedX TwistTag.E6.tag K (matRoot a b) c * (m : ModGL TwistTag.E6.tag K)⁻¹ =
        pinnedX TwistTag.E6.tag K (nbAct N (matRoot a b)) c)
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2) :
    (∃ s : memModel K J →* G, (nbCover e h2 Φ hΦ m).IsSection s) ∧
      ∃ s : memModel K J →* G, (nbCoverF e h2 Φ hΦ hσσ m).IsSection s := by
  obtain ⟨x, hx⟩ := exists_not_mem_memCoords N hJ2
  have hinj : Function.Injective ((nbModel h2 m).comp
      (LinearPilot.blockSpecialLinear (K := K) (memCoords N J)).subtype) :=
    (MulAut.conj (m : ModGL TwistTag.E6.tag K)).injective.comp
      (realize_comp_blockSL_injective_of_not_mem h2 hx)
  have hle := memModel_le_map_blockSL N hJ (nbModel h2 m) fun hab c => by
    rw [nbModel, MonoidHom.comp_apply, realize_transvection_ovl h2 hab c]
    exact hm hab c
  obtain ⟨s, hs, -⟩ := QCover.exists_isSection_ofParam (nbParam e Φ m) (nbModel h2 m)
    (ker_nbParam_le e h2 Φ hΦ m) (ker_nbModel_le h2 m) hinj hle
  obtain ⟨s', hs', -⟩ := QCover.exists_isSection_ofParam ((nbParam e Φ m).comp (unitaryTwist σ))
    (nbModel h2 m) (ker_nbParamF_le e h2 Φ hΦ hσσ m) (ker_nbModel_le h2 m) hinj hle
  exact ⟨⟨s, hs⟩, s', hs'⟩

theorem nbCoverF_E (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0)
    (Φ : SpecialLinearGroup (Fin 6) K →* G) (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (hσσ : ∀ c, σ (σ c) = c) (m : graphFixedRootGroup TwistTag.E6 K σ) :
    (nbCoverF e h2 Φ hΦ hσσ m).E = (nbCover e h2 Φ hΦ m).E := by
  change ((nbParam e Φ m).comp (unitaryTwist σ)).range = (nbParam e Φ m).range
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 fun B =>
    ⟨unitaryTwist σ B, unitaryTwist_unitaryTwist hσσ B⟩, ← MonoidHom.range_eq_map]

end Sections

section Transfers


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem nbCover_E_eq_centralizerPerfectCore [CharP K 2] {σ : K →+* K}
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0) {t : G}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hX : FieldCoverParamX σ h2 e t (modelToG e A))
    (m : graphFixedRootGroup TwistTag.E6 K σ) :
    (nbCover e h2 hX.Φ hX.ker_le m).E = centralizerPerfectCore
      (modelToG e (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom)) := by
  rw [nbCover_E, hX.range_eq, F4Pilot.map_centralizerPerfectCore, modelToG_map_conj]

theorem isSection_of_highCover [Finite K] [CharP K 2] (hk : Nat.card k = 2)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (h2 : (2 : K) = 0) (hX : FieldCoverParamX σ h2 e t (modelToG e A))
    (m : graphFixedRootGroup TwistTag.E6 K σ) (p : Fin 3)
    (hm1 : A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom ≤
      TwistedE6Pilot.rootRankOneGroup (algebraMap k K) (ovlRoot p))
    {c' : QCover G (ModGL TwistTag.E6.tag K)}
    (hagr : (highCover h2 hX.Φ hX.ker_le).TwistOn c'
      (perfectCore (centralizer (modelToG e A : Set G) ⊓ centralizer (modelToG e
        (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G)))
      (MonoidHom.id _))
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ E6Neighbour.high.nodes)
    (hJp : memCoords .high J ⊆ ovlSet p) (hH : ⁅memModel K J, memModel K J⁆ = memModel K J)
    {s : memModel K J →* G} (hs : (highCover h2 hX.Φ hX.ker_le).IsSection s) :
    c'.IsSection s := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have hι : ∀ c, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card (f := 1) (by rw [hk]; rfl) hσ)
  have hYD := hm1.trans (rootRankOneGroup_ovlRoot_le_su6Levi hι p)
  have hcE : (highCover h2 hX.Φ hX.ker_le).E ≤ centralizer (modelToG e A : Set G) := by
    rw [highCover_E, hX.range_eq]
    exact F4Pilot.centralizerPerfectCore_le_centralizer _
  have hmem := fun x (hx : x ∈ modelToG e
      (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom)) =>
    mem_highCover_of_mem_modelToG hK hσ e h2 hX.Φ hX.ker_le hX.N1 hYD hx
  have hΛ : memModel K J ≤ ovlLevi h2 p :=
    (memModel_le_map_blockSL .high hJ (realize h2) fun hab c =>
      realize_transvection_ovl h2 hab c).trans
        (Subgroup.map_mono (LinearPilot.blockSpecialLinear_mono hJp))
  refine hs.of_overlap hagr hcE hH (fun x hx => (hmem x hx).1) fun x hx h => ?_
  exact mem_centralizer_iff.1 (ovlLevi_le_centralizer_rootRankOneGroup h2 p (algebraMap k K)
    (hΛ h.2)) _ (hm1 (hmem x hx).2)

theorem isSection_of_nbCover [Finite K] [CharP K 2] (hk : Nat.card k = 2)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (h2 : (2 : K) = 0)
    (hX : FieldCoverParamX σ h2 e t (modelToG e A)) (hσσ : ∀ c, σ (σ c) = c)
    (m m' : graphFixedRootGroup TwistTag.E6 K σ) (N : E6Neighbour)
    (hm : ∀ {a b : Fin 6}, a ≠ b → ∀ c : K, (m : ModGL TwistTag.E6.tag K) *
      pinnedX TwistTag.E6.tag K (matRoot a b) c * (m : ModGL TwistTag.E6.tag K)⁻¹ =
        pinnedX TwistTag.E6.tag K (nbAct N (matRoot a b)) c)
    (p : Fin 3)
    (hmm : A.map (MulAut.conj ((m⁻¹ * m' : graphFixedRootGroup TwistTag.E6 K σ) :
      ModGL TwistTag.E6.tag K)).toMonoidHom ≤
        TwistedE6Pilot.rootRankOneGroup (algebraMap k K) (ovlRoot p))
    {c c' : QCover G (ModGL TwistTag.E6.tag K)}
    (hc : c = nbCover e h2 hX.Φ hX.ker_le m ∨ c = nbCoverF e h2 hX.Φ hX.ker_le hσσ m)
    (hagr : c.TwistOn c'
      (perfectCore (centralizer (modelToG e
        (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G) ⊓
        centralizer (modelToG e
          (A.map (MulAut.conj (m' : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G)))
      (MonoidHom.id _))
    {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) (hJp : memCoords N J ⊆ ovlSet p)
    (hH : ⁅memModel K J, memModel K J⁆ = memModel K J) {s : memModel K J →* G}
    (hs : c.IsSection s) : c'.IsSection s := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have hι : ∀ c, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card (f := 1) (by rw [hk]; rfl) hσ)
  have hAC : A ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    hAJ.trans (thetaRankOneGroup_le_graphFixedRootGroup h2 (sigma_eq_pow_card (f := 1)
      (by rw [hk]; rfl) hσ))
  set Y := A.map (MulAut.conj (m' : ModGL TwistTag.E6.tag K)).toMonoidHom with hY
  have hYC : Y ≤ graphFixedRootGroup TwistTag.E6 K σ := by
    rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem m'.2 (hAC ha)) (inv_mem m'.2)
  have hYm : Y.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom =
      A.map (MulAut.conj ((m⁻¹ * m' : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K)).toMonoidHom := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_conj_mul]
  have hYD : Y.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom ≤ su6Levi σ := by
    rw [hYm]
    exact hmm.trans (rootRankOneGroup_ovlRoot_le_su6Levi hι p)
  have hmem : ∀ x (hx : x ∈ modelToG e Y), ∃ hxE : x ∈ c.E, c.p ⟨x, hxE⟩ ∈ Y := by
    intro x hx
    obtain ⟨hxE, hpx⟩ := mem_nbCover_of_mem_modelToG hK hσ e h2 hX.Φ hX.ker_le hX.N1 m hYD hx
    rcases hc with rfl | rfl
    · exact ⟨hxE, hpx⟩
    · have hxE' : x ∈ (nbCoverF e h2 hX.Φ hX.ker_le hσσ m).E := by
        rw [nbCoverF_E]
        exact hxE
      refine ⟨hxE', ?_⟩
      rw [(twistOn_nbCover_nbCoverF e h2 hX.Φ hX.ker_le hσσ m).apply hxE hxE hxE',
        show twistHom TwistTag.E6 K σ ((nbCover e h2 hX.Φ hX.ker_le m).p ⟨x, hxE⟩) =
          (nbCover e h2 hX.Φ hX.ker_le m).p ⟨x, hxE⟩ from twistHom_coe_C0 ⟨_, hYC hpx⟩]
      exact hpx
  have hcE : c.E ≤ centralizer (modelToG e
      (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G) := by
    have h := nbCover_E_eq_centralizerPerfectCore e h2 hX m
    rcases hc with rfl | rfl
    · rw [h]
      exact F4Pilot.centralizerPerfectCore_le_centralizer _
    · rw [nbCoverF_E, h]
      exact F4Pilot.centralizerPerfectCore_le_centralizer _
  have hρ : ∀ {a b : Fin 6} (hab : a ≠ b) (c : K), nbModel h2 m
      (SpecialLinearGroup.transvection hab c) =
        pinnedX TwistTag.E6.tag K (nbAct N (matRoot a b)) c := fun hab c => by
    rw [nbModel, MonoidHom.comp_apply, realize_transvection_ovl h2 hab c]
    exact hm hab c
  have hΛ : memModel K J ≤
      (ovlLevi h2 p).map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom := by
    refine (memModel_le_map_blockSL N hJ (nbModel h2 m) hρ).trans ?_
    rw [ovlLevi, Subgroup.map_map]
    exact Subgroup.map_mono (LinearPilot.blockSpecialLinear_mono hJp)
  refine hs.of_overlap hagr hcE hH (fun x hx => (hmem x hx).1) fun x hx h => ?_
  obtain ⟨z, hz, hzh⟩ := hΛ h.2
  set y := c.p ⟨x, (hmem x hx).1⟩ with hy
  have hyY : y ∈ Y := (hmem x hx).2
  have h4 : (m : ModGL TwistTag.E6.tag K)⁻¹ * y * (m : ModGL TwistTag.E6.tag K) ∈
      TwistedE6Pilot.rootRankOneGroup (algebraMap k K) (ovlRoot p) := by
    refine hmm ?_
    rw [← hYm]
    exact ⟨y, hyY, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have h5 := mem_centralizer_iff.1 (ovlLevi_le_centralizer_rootRankOneGroup h2 p (algebraMap k K)
    hz) _ h4
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzh
  change y * (h : ModGL TwistTag.E6.tag K) = (h : ModGL TwistTag.E6.tag K) * y
  rw [← hzh]
  calc y * ((m : ModGL TwistTag.E6.tag K) * z * (m : ModGL TwistTag.E6.tag K)⁻¹) =
      (m : ModGL TwistTag.E6.tag K) * (((m : ModGL TwistTag.E6.tag K)⁻¹ * y *
        (m : ModGL TwistTag.E6.tag K)) * z) * (m : ModGL TwistTag.E6.tag K)⁻¹ := by group
    _ = (m : ModGL TwistTag.E6.tag K) * (z * ((m : ModGL TwistTag.E6.tag K)⁻¹ * y *
        (m : ModGL TwistTag.E6.tag K))) * (m : ModGL TwistTag.E6.tag K)⁻¹ := by rw [h5]
    _ = ((m : ModGL TwistTag.E6.tag K) * z * (m : ModGL TwistTag.E6.tag K)⁻¹) * y := by group

end Transfers

end CFSG.SeitzReduction.TwistedE6Pilot
