module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsCfg
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgForward
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem isTypeEps_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) (h : IsTypeEps Y) :
    IsTypeEps X := by
  obtain ⟨p, f, hp, hp3, hf, ⟨hq, ⟨ψ⟩⟩ | ⟨hq, hq2, ⟨ψ⟩⟩⟩ := h
  · exact ⟨p, f, hp, hp3, hf, Or.inl ⟨hq, ⟨φ.trans ψ⟩⟩⟩
  · exact ⟨p, f, hp, hp3, hf, Or.inr ⟨hq, hq2, ⟨φ.trans ψ⟩⟩⟩

theorem center_eq_bot_of_isTypeEps {X : Type} [Group X] (h : IsTypeEps X) :
    Subgroup.center X = ⊥ := by
  obtain ⟨p, f, hp, -, hf, ⟨-, ⟨ψ⟩⟩ | ⟨-, hq2, ⟨ψ⟩⟩⟩ := h
  · obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField p f)
    exact center_eq_bot_of_mulEquiv (ψ.trans φ)
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot le_rfl)
  · have hK : UnitaryFieldData p f (GaloisField p (2 * f)) :=
      ⟨hp.out, hf, GaloisField.card p (2 * f) (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU hK
    exact center_eq_bot_of_mulEquiv (ψ.trans φ.symm) (center_unitaryPSU_three_eq_bot hK hq2)

section Cfg

variable {G : Type} [Group G] [Finite G]

theorem inf_center_eq_bot_eps {L K' : Subgroup G} (hK'L : K' ≤ L) (hK'q : IsQuasisimple K')
    (hK'type : IsTypeEps (K' ⧸ CFSG.pCore 2 K')) (hZ : IsPGroup 3 (Subgroup.center L)) :
    K'.subgroupOf L ⊓ Subgroup.center L = ⊥ := by
  set e : K'.subgroupOf L ≃* K' := Subgroup.subgroupOfEquivOfLe hK'L
  exact inf_eq_bot_of_center_eq_bot (Γ := L)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hK'q)
    (center_eq_bot_of_mulEquiv (quotPCoreTwoCongr e) (center_eq_bot_of_isTypeEps hK'type)) le_rfl
    hZ

theorem cfgSEps_of (hθ : aschbacherSolvableCore 3 G = ⊥)
    {A : Subgroup G} (hA : Late.IsE27 A) {c : G} (hc : c ∈ A)
    {L : Subgroup G} (hL : IsComponent L) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hAC : A ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hLc : ¬ L ≤ Subgroup.centralizer {c})
    {K' : Subgroup G} (hK'M : K' ≤ L ⊓ Subgroup.centralizer {c}) (hK'q : IsQuasisimple K')
    (hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal)
    (hK'type : IsTypeEps (K' ⧸ CFSG.pCore 2 K')) (hAK' : A ≤ Subgroup.normalizer (K' : Set G))
    (hcent : Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K' : Set G)) :
    K'.subgroupOf L ⊓ Subgroup.center L = ⊥ ∧
      CfgSEps (L ⧸ Subgroup.center L) (aBar hAN) (descAut L ⟨c, hAN hc⟩)
        ((K'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L))) := by
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hLp : Group.IsPerfect L := hL.1.1
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hinf := inf_center_eq_bot_eps hK'L hK'q hK'type hZ3
  set K₁ : Subgroup L := K'.subgroupOf L with hK₁
  set Kb : Subgroup (L ⧸ Subgroup.center L) := K₁.map (QuotientGroup.mk' (Subgroup.center L))
    with hKb
  have hinj := mk_comp_injective_of_inf_eq_bot hinf
  refine ⟨hinf, ?_⟩
  refine
    { isE27 := isE27_aBar hLp hAN hAC hA
      mem := descAut_mem_aBar hAN hc
      ne_one := ?_
      le_autFix := map_le_autFix (hAN hc) (hK'M.trans inf_le_right)
      isSubnormal := isSubnormal_bar (hAN hc) hK'M hK'sn
      isPerfect := ?_
      map_mem := fun x hx y hy => descAut_mem_bar hK'L hAN hAK' hx hy
      isType := ?_
      faithful := ?_ }
  ·
    intro h1
    rw [descAut_eq_one_iff hLp] at h1
    apply hLc
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp h1 l hl)
  ·
    haveI : Group.IsPerfect K' := hK'q.1
    haveI : Group.IsPerfect K₁ := Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hK'L).symm.toMonoidHom) (MulEquiv.surjective _)
    exact Group.IsPerfect.map _
  ·
    exact isTypeEps_of_mulEquiv (quotPCoreTwoCongr (equivBar hK'L hinf)).symm hK'type
  ·
    intro x hx hxK
    obtain ⟨a, ha, rfl⟩ := (mem_aBar_iff hAN).mp hx
    have haK' : a ∈ Subgroup.centralizer (K' : Set G) := by
      refine mem_centralizer_of_conj_mem_pCoreOf hK'q (hAK' ha) fun k hk => ?_
      set l : L := ⟨k, hK'L hk⟩ with hl
      have hlK₁ : l ∈ K₁ := hk
      have hak : a * k * a⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp (hAK' ha) k).mp hk
      set l' : L := L.normalizerMonoidHom ⟨a, hAN ha⟩ l * l⁻¹ with hl'
      have hl'K₁ : l' ∈ K₁ := by
        change a * k * a⁻¹ * k⁻¹ ∈ K'
        exact Subgroup.mul_mem _ hak (Subgroup.inv_mem _ hk)
      have h1 := hxK (l : L ⧸ Subgroup.center L) ⟨l, hlK₁, rfl⟩
      have h2 : QuotientGroup.mk' (Subgroup.center L) l' ∈ CFSG.Open.pCoreOf 2 Kb := h1
      rw [map_mem_pCoreOf_map_iff 2 _ hinj hl'K₁] at h2
      have h3 : L.subtype l' ∈ CFSG.Open.pCoreOf 2 (K₁.map L.subtype) := by
        rw [pCoreOf_map_of_injective 2 L.subtype (L.subtype_injective.comp K₁.subtype_injective)]
        exact ⟨l', h2, rfl⟩
      rw [hK₁, Subgroup.map_subgroupOf_eq_of_le hK'L] at h3
      exact h3
    have haz : a ∈ Subgroup.zpowers c := by
      rw [hcent]
      exact ⟨ha, haK'⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp haz
    have hN : (⟨a, hAN ha⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨c, hAN hc⟩ : Subgroup.normalizer (L : Set G)) ^ m :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
    rw [hN, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ m

end Cfg

end CFSG.RankThree.PartTwo.Sec4.RonanEps
