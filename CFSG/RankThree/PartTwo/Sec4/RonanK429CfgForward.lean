module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTypes

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts

section Transport

@[expose] noncomputable def quotPCoreTwoCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ CFSG.pCore 2 X ≃* Y ⧸ CFSG.pCore 2 Y :=
  QuotientGroup.congr _ _ e (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e)

theorem isoLThreePi_of_mulEquiv {X Y : Type} [Group X] [Group Y] {p e : ℕ} [Fact p.Prime]
    (φ : X ≃* Y) (h : IsoLThreePi Y p e) : IsoLThreePi X p e := by
  rcases h with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
  · exact Or.inl ⟨hq, ⟨φ.trans ψ⟩⟩
  · exact Or.inr ⟨hq, ⟨φ.trans ψ⟩⟩

theorem isType429_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y) (h : IsType429 Y) :
    IsType429 X := by
  rcases h with ⟨p, e, hp, he, h⟩ | h | h | h | h
  · exact Or.inl ⟨p, e, hp, he, isoLThreePi_of_mulEquiv φ h⟩
  · obtain ⟨ψ⟩ := h
    exact Or.inr (Or.inl ⟨φ.trans ψ⟩)
  · obtain ⟨ψ⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩))
  · obtain ⟨ψ⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ.trans ψ⟩)))
  · obtain ⟨ψ⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨φ.trans ψ⟩)))

theorem nontrivial_quot_pCore_two {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K) :
    Nontrivial (K ⧸ CFSG.pCore 2 K) := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  obtain ⟨a, b, hab⟩ := hK.2.2
  apply hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      have ha : a ∈ Subgroup.center K := pCore_two_le_center hK
        ((QuotientGroup.eq_one_iff a).mp (Subsingleton.elim _ _))
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← Subgroup.mem_center_iff.mp ha b]

@[expose] noncomputable def equivMapOfInjOn {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (H : Subgroup X) (hf : Function.Injective (f.comp H.subtype)) : H ≃* H.map f :=
  (MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

end Transport

section Bar

variable {G : Type} [Group G] [Finite G]

theorem mk_comp_injective_of_inf_eq_bot {L : Subgroup G} {K₁ : Subgroup L}
    (h : K₁ ⊓ Subgroup.center L = ⊥) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center L)).comp K₁.subtype) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hkZ : (k : L) ∈ Subgroup.center L := (QuotientGroup.eq_one_iff _).mp hk
  have : (k : L) ∈ K₁ ⊓ Subgroup.center L := ⟨k.2, hkZ⟩
  rw [h, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem inf_center_eq_bot
    {L K' : Subgroup G} (hK'L : K' ≤ L) (hK'q : IsQuasisimple K')
    (hK'type : IsType429 (K' ⧸ CFSG.pCore 2 K')) (hZ : IsPGroup 3 (Subgroup.center L)) :
    K'.subgroupOf L ⊓ Subgroup.center L = ⊥ := by
  set e : K'.subgroupOf L ≃* K' := Subgroup.subgroupOfEquivOfLe hK'L
  haveI : Group.IsPerfect K' := hK'q.1
  haveI : Nontrivial (K' ⧸ CFSG.pCore 2 K') := nontrivial_quot_pCore_two hK'q
  have hZK' : Subgroup.center (K' ⧸ CFSG.pCore 2 K') = ⊥ := center_eq_bot_of_isType429 hK'type
  refine inf_eq_bot_of_center_eq_bot (Γ := L)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hK'q)
    (center_eq_bot_of_mulEquiv (quotPCoreTwoCongr e) hZK') le_rfl hZ

@[expose] noncomputable def equivBar {L K' : Subgroup G} (hK'L : K' ≤ L)
    (h : K'.subgroupOf L ⊓ Subgroup.center L = ⊥) :
    K' ≃* (K'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L)) :=
  (Subgroup.subgroupOfEquivOfLe hK'L).symm.trans
    (equivMapOfInjOn _ _ (mk_comp_injective_of_inf_eq_bot h))

theorem map_le_autFix {L K' : Subgroup G} {c : G} (hc : c ∈ Subgroup.normalizer (L : Set G))
    (hK'c : K' ≤ Subgroup.centralizer {c}) :
    (K'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L)) ≤
      autFix (descAut L ⟨c, hc⟩) := by
  rintro _ ⟨l, hl, rfl⟩
  change descAut L ⟨c, hc⟩ (l : L ⧸ Subgroup.center L) = (l : L ⧸ Subgroup.center L)
  rw [descAut_mk]
  congr 1
  apply Subtype.ext
  change c * (l : G) * c⁻¹ = l
  have hlc : (l : G) * c = c * l := Subgroup.mem_centralizer_singleton_iff.mp (hK'c hl)
  rw [← hlc, mul_inv_cancel_right]

theorem isSubnormal_bar {L K' : Subgroup G} {c : G} (hc : c ∈ Subgroup.normalizer (L : Set G))
    (hK'M : K' ≤ L ⊓ Subgroup.centralizer {c})
    (hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal) :
    (((K'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L))).subgroupOf
      (autFix (descAut L ⟨c, hc⟩))).IsSubnormal := by
  set M : Subgroup G := L ⊓ Subgroup.centralizer {c} with hM
  set σ := descAut L ⟨c, hc⟩ with hσ
  set C₁ : Subgroup L := M.subgroupOf L with hC₁
  set D : Subgroup L := (autFix σ).comap (QuotientGroup.mk' (Subgroup.center L)) with hD
  set K₁ : Subgroup L := K'.subgroupOf L with hK₁
  have hML : M ≤ L := inf_le_left
  have hK₁C₁ : K₁ ≤ C₁ := Subgroup.subgroupOf_mono L hK'M
  have hfix : ∀ l : L, (l : G) * c = c * l →
      ((L.normalizerMonoidHom ⟨c, hc⟩ l : L)) = l := by
    intro l hlc
    apply Subtype.ext
    change c * (l : G) * c⁻¹ = l
    rw [← hlc, mul_inv_cancel_right]
  have hC₁D : C₁ ≤ D := by
    intro l hl
    change σ (l : L ⧸ Subgroup.center L) = (l : L ⧸ Subgroup.center L)
    rw [hσ, descAut_mk, hfix l (Subgroup.mem_centralizer_singleton_iff.mp hl.2)]
  have h₁ : (K₁.subgroupOf C₁).IsSubnormal := by
    set e : C₁ ≃* M := Subgroup.subgroupOfEquivOfLe hML
    have heq : K₁.subgroupOf C₁ = (K'.subgroupOf M).comap e.toMonoidHom := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      rfl
    rw [heq]
    exact hK'sn.comap _
  have h₂ : (C₁.subgroupOf D).IsSubnormal := by
    apply Subgroup.Normal.isSubnormal
    constructor
    intro x hx d
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxM : ((x : L) : G) ∈ M := hx
    have hxc : ((x : L) : G) * c = c * ((x : L) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxM.2
    have hd : σ ((d : L) : L ⧸ Subgroup.center L) = ((d : L) : L ⧸ Subgroup.center L) := d.2
    rw [hσ, descAut_mk, QuotientGroup.eq] at hd
    set w : L := (L.normalizerMonoidHom ⟨c, hc⟩ (d : L))⁻¹ * (d : L) with hw
    have hwc : ∀ l : L, l * w = w * l := fun l => Subgroup.mem_center_iff.mp hd l
    have hwG : ((w : L) : G) = c * ((d : L) : G)⁻¹ * c⁻¹ * ((d : L) : G) := by
      rw [hw]
      change (c * ((d : L) : G) * c⁻¹)⁻¹ * ((d : L) : G) = _
      group
    have hwx : ((w : L) : G) * ((x : L) : G) = ((x : L) : G) * ((w : L) : G) :=
      congrArg Subtype.val (hwc (x : L)).symm
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (d : L).2 (x : L).2)
      (Subgroup.inv_mem _ (d : L).2), ?_⟩
    change (((d * x * d⁻¹ : D) : L) : G) ∈ Subgroup.centralizer {c}
    rw [Subgroup.mem_centralizer_singleton_iff]
    change ((d : L) : G) * ((x : L) : G) * ((d : L) : G)⁻¹ * c =
      c * (((d : L) : G) * ((x : L) : G) * ((d : L) : G)⁻¹)
    have hcd : c * ((d : L) : G) = ((d : L) : G) * ((w : L) : G)⁻¹ * c := by
      rw [hwG]
      group
    have hcdi : c * ((d : L) : G)⁻¹ = ((w : L) : G) * ((d : L) : G)⁻¹ * c := by
      rw [hwG]
      group
    calc ((d : L) : G) * ((x : L) : G) * ((d : L) : G)⁻¹ * c
        = ((d : L) : G) * ((w : L) : G)⁻¹ * (((w : L) : G) * ((x : L) : G)) *
            ((d : L) : G)⁻¹ * c := by group
      _ = ((d : L) : G) * ((w : L) : G)⁻¹ * (((x : L) : G) * ((w : L) : G)) *
            ((d : L) : G)⁻¹ * c := by rw [hwx]
      _ = ((d : L) : G) * ((w : L) : G)⁻¹ * ((x : L) : G) *
            (((w : L) : G) * ((d : L) : G)⁻¹ * c) := by group
      _ = ((d : L) : G) * ((w : L) : G)⁻¹ * ((x : L) : G) * (c * ((d : L) : G)⁻¹) := by
            rw [hcdi]
      _ = ((d : L) : G) * ((w : L) : G)⁻¹ * (((x : L) : G) * c) * ((d : L) : G)⁻¹ := by group
      _ = ((d : L) : G) * ((w : L) : G)⁻¹ * (c * ((x : L) : G)) * ((d : L) : G)⁻¹ := by
            rw [hxc]
      _ = (((d : L) : G) * ((w : L) : G)⁻¹ * c) * ((x : L) : G) * ((d : L) : G)⁻¹ := by group
      _ = (c * ((d : L) : G)) * ((x : L) : G) * ((d : L) : G)⁻¹ := by rw [hcd]
      _ = c * (((d : L) : G) * ((x : L) : G) * ((d : L) : G)⁻¹) := by group
  have h₃ := isSubnormal_subgroupOf_trans hK₁C₁ hC₁D h₁ h₂
  set ψ : D →* autFix σ := ((QuotientGroup.mk' (Subgroup.center L)).comp D.subtype).codRestrict
    (autFix σ) (fun d => d.2) with hψ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (y : L ⧸ Subgroup.center L)
    have hlD : l ∈ D := by
      change ((l : L ⧸ Subgroup.center L)) ∈ autFix σ
      rw [hl]
      exact y.2
    exact ⟨⟨l, hlD⟩, Subtype.ext hl⟩
  have heq : (K₁.subgroupOf D).map ψ =
      (K₁.map (QuotientGroup.mk' (Subgroup.center L))).subgroupOf (autFix σ) := by
    ext y
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d, hd, rfl⟩
    · rintro ⟨l, hl, hly⟩
      have hlD : l ∈ D := by
        change ((l : L ⧸ Subgroup.center L)) ∈ autFix σ
        rw [show ((l : L ⧸ Subgroup.center L)) = (y : L ⧸ Subgroup.center L) from hly]
        exact y.2
      exact ⟨⟨l, hlD⟩, hl, Subtype.ext hly⟩
  rw [← heq]
  exact h₃.map hψs

theorem descAut_mem_bar {L K' A : Subgroup G} (hK'L : K' ≤ L)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hAK' : A ≤ Subgroup.normalizer (K' : Set G))
    {x : MulAut (L ⧸ Subgroup.center L)} (hx : x ∈ aBar hAN) {y : L ⧸ Subgroup.center L}
    (hy : y ∈ (K'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L))) :
    x y ∈ (K'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L)) := by
  obtain ⟨a, ha, rfl⟩ := (mem_aBar_iff hAN).mp hx
  obtain ⟨l, hl, rfl⟩ := hy
  refine ⟨L.normalizerMonoidHom ⟨a, hAN ha⟩ l, ?_, rfl⟩
  change a * (l : G) * a⁻¹ ∈ K'
  exact (Subgroup.mem_normalizer_iff.mp (hAK' ha) l).mp hl

end Bar

section Cfg

variable {G : Type} [Group G] [Finite G]

theorem cfgS429_of
    (hθ : aschbacherSolvableCore 3 G = ⊥)
    {A : Subgroup G} (hA : Late.IsE27 A) {c : G} (hc : c ∈ A)
    {L : Subgroup G} (hL : IsComponent L) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hAC : A ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hLc : ¬ L ≤ Subgroup.centralizer {c})
    {K' : Subgroup G} (hK'M : K' ≤ L ⊓ Subgroup.centralizer {c}) (hK'q : IsQuasisimple K')
    (hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal)
    (hK'type : IsType429 (K' ⧸ CFSG.pCore 2 K')) (hAK' : A ≤ Subgroup.normalizer (K' : Set G))
    (hcent : Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K' : Set G)) :
    K'.subgroupOf L ⊓ Subgroup.center L = ⊥ ∧
      CfgS429 (L ⧸ Subgroup.center L) (aBar hAN) (descAut L ⟨c, hAN hc⟩)
        ((K'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L))) := by
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hLp : Group.IsPerfect L := hL.1.1
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hinf := inf_center_eq_bot hK'L hK'q hK'type hZ3
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
    exact isType429_of_mulEquiv (quotPCoreTwoCongr (equivBar hK'L hinf)).symm hK'type
  ·
    intro x hx hxK
    obtain ⟨a, ha, rfl⟩ := (mem_aBar_iff hAN).mp hx
    have haK' : a ∈ Subgroup.centralizer (K' : Set G) := by
      refine mem_centralizer_of_conj_mem_pCoreOf hK'q (hAK' ha) fun k hk => ?_
      set l : L := ⟨k, hK'L hk⟩ with hl
      have hlK₁ : l ∈ K₁ := hk
      have hak : a * k * a⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp (hAK' ha) k).mp hk
      set l' : L := L.normalizerMonoidHom ⟨a, hAN ha⟩ l * l⁻¹ with hl'
      have hl'G : (l' : G) = a * k * a⁻¹ * k⁻¹ := rfl
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

end CFSG.RankThree.PartTwo.Sec4.RonanK429
