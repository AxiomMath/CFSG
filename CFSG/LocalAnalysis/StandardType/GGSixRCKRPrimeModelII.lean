module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Basic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitCyclicCore
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6Components

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

@[expose] def RCKRPRootSubOf (M : LieUniversal) (R' : Subgroup M.K) : Prop :=
  ∃ γ ∈ M.D.roots, (GGLongRoot M.D γ ∨ 2 • γ ∉ M.D.roots) ∧
    ∃ u : M.K, R' = (M.D.rootGroup γ).map (MulAut.conj u).toMonoidHom

theorem rckRPRootSubOf_map_conj {M : LieUniversal} {R' : Subgroup M.K}
    (h : RCKRPRootSubOf M R') (x : M.K) :
    RCKRPRootSubOf M (R'.map (MulAut.conj x).toMonoidHom) := by
  obtain ⟨γ, hγ, hdisj, u, rfl⟩ := h
  exact ⟨γ, hγ, hdisj, x * u, CFSG.GroupTheory.map_conj_map_conj x u _⟩

@[expose] def RCKRPModelII
    {G : Type} [Group G] (P : Subgroup G → Prop) (J' : Subgroup G) : Prop :=
  ∃ (t : StatedLieTag) (k g : ℕ) (κ : (ggU t k g).K →* G), RCKNormalizedModel t k g ∧
    κ.range = J' ∧ (∀ y, κ y ∈ Subgroup.center G → y ∈ Subgroup.center (ggU t k g).K) ∧
    ∀ β ∈ (ggU t k g).D.roots,
      (GGLongRoot (ggU t k g).D β ∨
        (((t = .PSp ∧ k = 2) ∨ t = .F4) ∧ 2 • β ∉ (ggU t k g).D.roots)) →
      ∀ u : (ggU t k g).K,
        P (ggRootSub (ggU t k g).D κ β u) ∨ 2 < Nat.card ((ggU t k g).D.rootGroup β)

@[expose] def RCKRPModelBig
    {G : Type} [Group G] (J' : Subgroup G) : Prop :=
  ∃ (t : StatedLieTag) (k g : ℕ) (κ : (ggU t k g).K →* G), RCKNormalizedModel t k g ∧
    ¬ ((t = .PSp ∧ k = 2) ∨ t = .F4) ∧ κ.range = J' ∧
    (∀ y, κ y ∈ Subgroup.center G → y ∈ Subgroup.center (ggU t k g).K) ∧
    ∀ γ ∈ (ggU t k g).D.roots, GGLongRoot (ggU t k g).D γ →
      2 < Nat.card ((ggU t k g).D.rootGroup γ)

theorem rckRP_modelBig_of_PSL
    {G : Type} [Group G] {J' : Subgroup G} {k q : ℕ} (hq : 2 ≤ q)
    (κ : (ggU .PSL (k + 1) q).K →* G) (hnorm : RCKNormalizedModel .PSL (k + 1) q)
    (hrange : κ.range = J')
    (hcent : ∀ y, κ y ∈ Subgroup.center G → y ∈ Subgroup.center (ggU .PSL (k + 1) q).K) :
    RCKRPModelBig J' := by
  refine ⟨.PSL, k + 1, q, κ, hnorm, by simp, hrange, hcent, fun γ hγ _ => ?_⟩
  have hroot : Nat.card ((ggU .PSL (k + 1) q).D.rootGroup γ) = 2 ^ q :=
    card_rootGroup_specialLinear_galoisField (p := 2) (k := k) (q := q) (by omega) hγ
  rw [hroot]
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq

theorem rckRP_modelII_of_big
    {G : Type} [Group G] (P : Subgroup G → Prop) {J' : Subgroup G} (h : RCKRPModelBig J') :
    RCKRPModelII P J' := by
  obtain ⟨t, k, g, κ, hnorm, hnot, hκr, hκz, hcard⟩ := h
  refine ⟨t, k, g, κ, hnorm, hκr, hκz, ?_⟩
  intro β hβ hclause u
  rcases hclause with hlong | ⟨hshort, -⟩
  · exact Or.inr (hcard β hβ hlong)
  · exact absurd hshort hnot

theorem rckRP_modelII_of_long
    {G : Type} [Group G] {P : Subgroup G → Prop} {J' : Subgroup G} {t : StatedLieTag} {k g : ℕ}
    (hnorm : RCKNormalizedModel t k g) (hnot : ¬ ((t = .PSp ∧ k = 2) ∨ t = .F4))
    (κ : (ggU t k g).K →* G) (hκr : κ.range = J')
    (hκz : ∀ y, κ y ∈ Subgroup.center G → y ∈ Subgroup.center (ggU t k g).K)
    (hP : ∀ (R' : Subgroup G) (y : (ggU t k g).K), P R' →
      P (R'.map (MulAut.conj (κ y)).toMonoidHom))
    {β₀ : Fin (ggU t k g).D.rank → ℤ} (hl₀ : GGLongRoot (ggU t k g).D β₀)
    (hP₀ : P (((ggU t k g).D.rootGroup β₀).map κ)) :
    RCKRPModelII P J' := by
  refine ⟨t, k, g, κ, hnorm, hκr, hκz, ?_⟩
  intro β hβ hclause u
  have hlong : GGLongRoot (ggU t k g).D β := by
    rcases hclause with h | ⟨hshort, -⟩
    · exact h
    · exact absurd hshort hnot
  obtain ⟨w, hw⟩ := CFSG.StandardType.RCKK1I.rckK1I_longRootConj hnorm.1 hnorm.2
    (ggLongRoot_mem_roots hl₀) hl₀ hβ hlong
  refine Or.inl ?_
  simp only [ggRootSub]
  rw [← hw, CFSG.GroupTheory.map_conj_map_conj, CFSG.Timmesfeld.RankOne.map_map_conj]
  exact hP _ (u * w) hP₀

theorem rckRP_exists_of_modelII
    (hIRG : RCKIntrinsicRoot) {X : Type} [Group X] [Finite X] {G : Type} [Group G]
    (φ : G →* X) (hφk : φ.ker ≤ Subgroup.center G)
    {J' : Subgroup G} {J R Rm : Subgroup X} (hJ : J'.map φ = J)
    (hJq : CFSG.Assembly.IsQuasisimple ↥J) (hpos : GGRootPosJ J R Rm) (hR2 : Nat.card R = 2)
    {P : Subgroup G → Prop} (hM : RCKRPModelII P J') :
    ∃ R' : Subgroup G, R'.map φ = R ∧ P R' := by
  obtain ⟨t, k, g, κ, hnorm, hκr, hκz, hcond⟩ := hM
  obtain ⟨β, hβ, hclause, u, hR⟩ :=
    rckRP_exists_rootSub_of_model hIRG φ hφk hJ hJq hpos κ hnorm hκr hκz
  have hker : (φ.comp κ).ker ≤ Subgroup.center (ggU t k g).K := by
    intro y hy
    exact hκz y (hφk (by simpa using hy))
  rcases hcond β hβ hclause u with hP | hgt
  · exact ⟨_, hR, hP⟩
  · exfalso
    have hcard := rckRP_card_map_ggRootSub hnorm κ φ hker hβ u
    rw [hR, hR2] at hcard
    omega

theorem ggRootPosNbr_of_rootSubOf
    {X : Type} [Group X] {K R : Subgroup X} {t : StatedLieTag} {n f : ℕ}
    (htag : GGPosTag t) (hshort : GGShortTag t) (hf : 1 ≤ f) (φ : (ggU t n f).K →* X)
    (hφr : φ.range = K) (hφk : φ.ker ≤ Subgroup.center (ggU t n f).K)
    {R' : Subgroup (ggU t n f).K} (hR : R'.map φ = R) (hQ : RCKRPRootSubOf (ggU t n f) R') :
    GGRootPosNbr K R := by
  obtain ⟨γ, hγ, hdisj, u, hR'⟩ := hQ
  have hRγ : R = ggRootSub (ggU t n f).D φ γ u := by
    rw [← hR, hR']
    rfl
  refine Or.inl ⟨t, n, f, γ, htag, hf, hγ, ?_, φ, hφr, hφk, u, hRγ⟩
  rcases hdisj with hlong | h2
  · exact Or.inl hlong
  · exact Or.inr ⟨hshort, h2⟩

theorem ggRootPosNbr_of_rootPosJ
    {X : Type} [Group X] {K R Rm : Subgroup X} (h : GGRootPosJ K R Rm) : GGRootPosNbr K R := by
  rcases h with ⟨t, m, g, β, htag, hg, hl, φ, hφr, hφk, u, hR, -⟩ |
    ⟨F, hF, hFin, σ, g, β, htri, hl, φ, hφr, hφk, u, hR, -⟩
  · exact Or.inl ⟨t, m, g, β, htag, hg, ggLongRoot_mem_roots hl, Or.inl hl, φ, hφr, hφk, u, hR⟩
  · exact Or.inr ⟨F, hF, hFin, σ, g, β, htri, hl, φ, hφr, hφk, u, hR⟩

theorem exists_rootPairCover_of_normalizing_actor
    {X Y U : Type} [Group X] [Group Y] [Group U]
    (D : UniversalRootDatum U)
    {G₀ J K L R Rm : Subgroup X} [Finite G₀]
    {e₀ x₀ : G₀} {p : ℕ}
    (hp : p.Prime) (hx : orderOf x₀ = p) (he : e₀ ≠ 1)
    (hK : CFSG.Assembly.IsComponentOf K
      (G₀ ⊓ Subgroup.centralizer ({(e₀ : X)} : Set X)))
    (hL : CFSG.Assembly.IsComponentOf L
      (G₀ ⊓ Subgroup.centralizer ({(x₀ : X)} : Set X)))
    (hJ : CFSG.Assembly.IsQuasisimple J)
    (hJK : J ≤ K) (hJL : J ≤ L)
    (hRJ : R ≤ J) (hRmJ : Rm ≤ J)
    (ιT : G₀ →* Y) (hιT : Function.Injective ιT)
    {y : Y} (hy : y ∈ Subgroup.normalizer (ιT.range : Set Y))
    (hyJ : ∀ j : G₀, (j : X) ∈ J → y * ιT j = ιT j * y)
    (hye : y * ιT e₀ * y⁻¹ ∈ Subgroup.zpowers (ιT x₀))
    (φL : U →* X) (hφL : φL.range = L)
    (β : Fin D.rank → ℤ) (r : U)
    (hR : R = ggRootSub D φL β r)
    (hRm : Rm = ggRootSub D φL (-β) r) :
    ∃ φK : U →* X,
      φK.range = K ∧ φK.ker = φL.ker ∧
      R = ggRootSub D φK β r ∧
      Rm = ggRootSub D φK (-β) r := by
  obtain ⟨α, hα⟩ :=
    CFSG.StandardType.ExcFieldAutCentRankF4.exists_aut_of_mem_normalizer ιT hιT hy
  have hKG₀ : K ≤ G₀ := hK.1.trans inf_le_left
  have hLG₀ : L ≤ G₀ := hL.1.trans inf_le_left
  have hJG₀ : J ≤ G₀ := hJK.trans hKG₀
  have hαJ : ∀ j : G₀, (j : X) ∈ J → α j = j := by
    intro j hj
    apply hιT
    rw [hα]
    rw [hyJ j hj, mul_assoc, mul_inv_cancel, mul_one]
  have hαsymmJ : ∀ j : G₀, (j : X) ∈ J → α.symm j = j := by
    intro j hj
    calc α.symm j = α.symm (α j) := by rw [hαJ j hj]
      _ = j := α.symm_apply_apply j
  have hαe_mem : α e₀ ∈ Subgroup.zpowers x₀ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hye
    refine ⟨k, ?_⟩
    apply hιT
    rw [map_zpow, hα, hk]
  have hαe_ne : α e₀ ≠ 1 := by
    intro h
    exact he (α.injective (by simpa using h))
  have hCe : Subgroup.centralizer ({α e₀} : Set G₀) =
      Subgroup.centralizer ({x₀} : Set G₀) :=
    CFSG.StandardType.ExcNonsplit.centralizer_eq_of_mem_zpowers hp hx hαe_mem hαe_ne
  have hce : (G₀ ⊓ Subgroup.centralizer ({(e₀ : X)} : Set X)).subgroupOf G₀ =
      Subgroup.centralizer ({(e₀ : G₀)} : Set G₀) := by
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      apply Subtype.ext
      simpa using h
    · intro h
      exact ⟨g.2, by simpa using congrArg Subtype.val h⟩
  have hcx : (G₀ ⊓ Subgroup.centralizer ({(x₀ : X)} : Set X)).subgroupOf G₀ =
      Subgroup.centralizer ({(x₀ : G₀)} : Set G₀) := by
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      apply Subtype.ext
      simpa using h
    · intro h
      exact ⟨g.2, by simpa using congrArg Subtype.val h⟩
  have hK₀ : CFSG.Assembly.IsComponentOf (K.subgroupOf G₀)
      (Subgroup.centralizer ({(e₀ : G₀)} : Set G₀)) := by
    have h := CFSG.StandardType.ggIsComponentOf_subgroupOf_of_le G₀ hKG₀ hK
    rwa [hce] at h
  have hL₀ : CFSG.Assembly.IsComponentOf (L.subgroupOf G₀)
      (Subgroup.centralizer ({(x₀ : G₀)} : Set G₀)) := by
    have h := CFSG.StandardType.ggIsComponentOf_subgroupOf_of_le G₀ hLG₀ hL
    rwa [hcx] at h
  have hJ₀ : CFSG.Assembly.IsQuasisimple (J.subgroupOf G₀) :=
    CFSG.StandardType.ggIsQuasisimple_subgroupOf hJG₀ hJ
  have hKmap : CFSG.Assembly.IsComponentOf ((K.subgroupOf G₀).map α.toMonoidHom)
      (Subgroup.centralizer ({(x₀ : G₀)} : Set G₀)) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := α.toMonoidHom) α.injective).2 hK₀
    rwa [CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv α e₀, hCe] at h
  have hJmapK : J.subgroupOf G₀ ≤ (K.subgroupOf G₀).map α.toMonoidHom := by
    intro j hj
    have hjK : j ∈ K.subgroupOf G₀ := Subgroup.subgroupOf_mono G₀ hJK hj
    rw [Subgroup.mem_map]
    refine ⟨α.symm j, ?_, α.apply_symm_apply j⟩
    rwa [hαsymmJ j hj]
  have hJmapL : J.subgroupOf G₀ ≤ L.subgroupOf G₀ :=
    Subgroup.subgroupOf_mono G₀ hJL
  have hKL : (K.subgroupOf G₀).map α.toMonoidHom = L.subgroupOf G₀ :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hJ₀ hKmap hL₀ hJmapK hJmapL
  have hKLsymm : (L.subgroupOf G₀).map α.symm.toMonoidHom = K.subgroupOf G₀ := by
    rw [← hKL, Subgroup.map_map]
    simp
  have hφL_le : φL.range ≤ G₀ := by rw [hφL]; exact hLG₀
  let φL₀ : U →* G₀ := φL.codRestrict G₀ (fun u => hφL_le ⟨u, rfl⟩)
  let φK : U →* X := G₀.subtype.comp (α.symm.toMonoidHom.comp φL₀)
  have hφL₀range : φL₀.range = L.subgroupOf G₀ := by
    rw [← MonoidHom.subgroupOf_range_eq_of_le φL hφL_le, hφL]
  have hφKrange : φK.range = K := by
    rw [show φK = G₀.subtype.comp (α.symm.toMonoidHom.comp φL₀) from rfl,
      MonoidHom.range_comp, MonoidHom.range_comp, hφL₀range, hKLsymm,
      Subgroup.map_subgroupOf_eq_of_le hKG₀]
  have hφKker : φK.ker = φL.ker := by
    rw [show φK = G₀.subtype.comp (α.symm.toMonoidHom.comp φL₀) from rfl,
      MonoidHom.ker_comp_of_injective _ _ G₀.subtype_injective,
      MonoidHom.ker_comp_of_injective _ _ α.symm.injective]
    exact MonoidHom.ker_codRestrict φL G₀ _
  have hfix {γ : Fin D.rank → ℤ}
      (hγ : ∀ u ∈ (D.rootGroup γ).map (MulAut.conj r).toMonoidHom,
        (φL u : X) ∈ J) :
      ∀ u ∈ (D.rootGroup γ).map (MulAut.conj r).toMonoidHom,
        α.symm (φL₀ u) = φL₀ u := by
    intro u hu
    apply hαsymmJ
    change (φL u : X) ∈ J
    exact hγ u hu
  have hroot {γ : Fin D.rank → ℤ}
      (hγ : ∀ u ∈ (D.rootGroup γ).map (MulAut.conj r).toMonoidHom,
        (φL u : X) ∈ J) :
      ggRootSub D φK γ r = ggRootSub D φL γ r := by
    simp only [ggRootSub]
    apply le_antisymm
    · rintro y ⟨u, hu, rfl⟩
      exact ⟨u, hu, by
        show φL u = ((α.symm (φL₀ u) : G₀) : X)
        rw [hfix hγ u hu]
        rfl⟩
    · rintro y ⟨u, hu, rfl⟩
      exact ⟨u, hu, by
        show ((α.symm (φL₀ u) : G₀) : X) = φL u
        rw [hfix hγ u hu]
        rfl⟩
  have hβJ : ∀ u ∈ (D.rootGroup β).map (MulAut.conj r).toMonoidHom, (φL u : X) ∈ J := by
    intro u hu
    have hmem : (φL u : X) ∈ ggRootSub D φL β r := Subgroup.mem_map_of_mem φL hu
    rw [← hR] at hmem
    exact hRJ hmem
  have hmβJ : ∀ u ∈ (D.rootGroup (-β)).map (MulAut.conj r).toMonoidHom, (φL u : X) ∈ J := by
    intro u hu
    have hmem : (φL u : X) ∈ ggRootSub D φL (-β) r := Subgroup.mem_map_of_mem φL hu
    rw [← hRm] at hmem
    exact hRmJ hmem
  refine ⟨φK, hφKrange, hφKker, ?_, ?_⟩
  · rw [hR]
    exact (hroot hβJ).symm
  · rw [hRm]
    exact (hroot hmβJ).symm

end CFSG.StandardType.RCKRP
