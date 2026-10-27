module

public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item13Theta

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section ThetaC

variable {G : Type} [Group G] [Finite G]

theorem inSubgroup_theta_le_of_normal {Y X : Subgroup G} (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    inSubgroup (aschbacherSolvableCore 3) Y ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  have hn : (Y.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXY
  set e : Y.subgroupOf X ≃* Y := Subgroup.subgroupOfEquivOfLe hYX with he
  obtain ⟨hθs, hθc, hθp, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y.subgroupOf X) Nat.prime_three
  have hmax := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.2.1
  set N : Subgroup X := (aschbacherSolvableCore 3 (Y.subgroupOf X)).map (Y.subgroupOf X).subtype
  have hN : N.Normal := by
    have := hn
    have := hθc
    infer_instance
  set e1 := (aschbacherSolvableCore 3 (Y.subgroupOf X)).equivMapOfInjective
    (Y.subgroupOf X).subtype (Y.subgroupOf X).subtype_injective
  have hNs : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective (f := e1.symm.toMonoidHom) e1.symm.injective
  have hNp : ¬ 3 ∣ Nat.card N := by
    rw [← Nat.card_congr e1.toEquiv]
    exact hθp
  have hle := hmax N hN hNs hNp
  have hθe := aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  intro g hg
  obtain ⟨y, hy, rfl⟩ := hg
  have hy' : e.symm y ∈ aschbacherSolvableCore 3 (Y.subgroupOf X) := by
    rw [← hθe] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : e.symm y = z := (MulEquiv.symm_apply_eq e).mpr hzy.symm
    rw [this]
    exact hz
  have hmem : ((e.symm y : Y.subgroupOf X) : X) ∈ N := ⟨_, hy', rfl⟩
  exact ⟨_, hle hmem, rfl⟩

theorem inf_inSubgroup_theta_le {X H : Subgroup G} (hXH : X ≤ H) :
    X ⊓ inSubgroup (aschbacherSolvableCore 3) H ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  set W := X ⊓ inSubgroup (aschbacherSolvableCore 3) H with hW
  have hWX : W ≤ X := inf_le_left
  have hθH : inSubgroup (aschbacherSolvableCore 3) H ≤ H := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hθn : ∀ h ∈ H, ∀ w ∈ inSubgroup (aschbacherSolvableCore 3) H,
      h * w * h⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) H := by
    rintro h hh _ ⟨y, hy, rfl⟩
    refine ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹,
      (inferInstance : (aschbacherSolvableCore 3 H).Normal).conj_mem y hy _, ?_⟩
    simp
  have hnorm : X ≤ Subgroup.normalizer (W : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨hwX, hwθ⟩
      exact ⟨X.mul_mem (X.mul_mem hx hwX) (X.inv_mem hx), hθn x (hXH hx) w hwθ⟩
    · rintro ⟨hwX, hwθ⟩
      refine ⟨?_, ?_⟩
      · have : x⁻¹ * (x * w * x⁻¹) * x ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hx) hwX) hx
        simpa [mul_assoc] using this
      · have := hθn x⁻¹ (H.inv_mem (hXH hx)) _ hwθ
        simpa [mul_assoc] using this
  have hmax := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.2.1
  obtain ⟨hθs, -, hθp, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  have hWθ : W ≤ inSubgroup (aschbacherSolvableCore 3) H := inf_le_right
  set M : Subgroup X := W.subgroupOf X
  have hM : M.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWX).mpr hnorm
  have hmemθ : ∀ m : M, (⟨((m : X) : G), hθH (hWθ (Subgroup.mem_subgroupOf.mp m.2))⟩ : H) ∈
      aschbacherSolvableCore 3 H := by
    intro m
    obtain ⟨y, hy, hyw⟩ := hWθ (Subgroup.mem_subgroupOf.mp m.2)
    have : y = ⟨((m : X) : G), hθH (hWθ (Subgroup.mem_subgroupOf.mp m.2))⟩ := Subtype.ext hyw
    rw [← this]
    exact hy
  let f : M →* aschbacherSolvableCore 3 H :=
    { toFun := fun m => ⟨⟨((m : X) : G), hθH (hWθ (Subgroup.mem_subgroupOf.mp m.2))⟩, hmemθ m⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b h
    have := congrArg (fun z : aschbacherSolvableCore 3 H => ((z : H) : G)) h
    exact Subtype.ext (Subtype.ext this)
  have hMs : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective hf
  have hMdvd : Nat.card M ∣ Nat.card (aschbacherSolvableCore 3 H) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hMp : ¬ 3 ∣ Nat.card M := fun h3 => hθp (h3.trans hMdvd)
  have hle := hmax M hM hMs hMp
  intro w hw
  exact ⟨⟨w, hw.1⟩, hle (Subgroup.mem_subgroupOf.mpr hw), rfl⟩

theorem inSubgroup_theta_centralizer (c : G) :
    inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) =
      Subgroup.centralizer ({c} : Set G) ⊓
        inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.normalizer (Subgroup.zpowers c : Set G)) := by
  have hCH := centralizer_le_normalizer_zpowers c
  apply le_antisymm
  · refine le_inf ?_ (inSubgroup_theta_le_of_normal hCH ?_)
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · intro h hh
      have hn := centralizer_normal_in_normalizer_zpowers c
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have := hn.conj_mem ⟨x, hCH hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨h, hh⟩
        exact Subgroup.mem_subgroupOf.mp this
      · intro hx
        have := hn.conj_mem ⟨h * x * h⁻¹, hCH hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨h, hh⟩⁻¹
        have h2 := Subgroup.mem_subgroupOf.mp this
        simpa [mul_assoc] using h2
  · exact inf_inSubgroup_theta_le hCH

end ThetaC

section Images

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nonempty_map_mk_equiv {C H X : Subgroup G} (hXC : X ≤ C) (hXH : X ≤ H)
    (NC : Subgroup C) [NC.Normal] (NH : Subgroup H) [NH.Normal]
    (hker : ∀ x : X, (Subgroup.inclusion hXC x ∈ NC ↔ Subgroup.inclusion hXH x ∈ NH)) :
    Nonempty ((X.subgroupOf C).map (QuotientGroup.mk' NC) ≃*
      (X.subgroupOf H).map (QuotientGroup.mk' NH)) := by
  set φC : X →* C ⧸ NC := (QuotientGroup.mk' NC).comp (Subgroup.inclusion hXC)
  set φH : X →* H ⧸ NH := (QuotientGroup.mk' NH).comp (Subgroup.inclusion hXH)
  have hrC : (X.subgroupOf C).map (QuotientGroup.mk' NC) = φC.range := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hXC x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hrH : (X.subgroupOf H).map (QuotientGroup.mk' NH) = φH.range := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hXH x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hk : φC.ker = φH.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      QuotientGroup.eq_one_iff]
    exact hker x
  exact ⟨(MulEquiv.subgroupCongr hrC).trans ((QuotientGroup.quotientKerEquivRange φC).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans ((QuotientGroup.quotientKerEquivRange φH).trans
      (MulEquiv.subgroupCongr hrH.symm))))⟩

theorem nonempty_thetaImage_equiv_lBarA {c : G} {L A : Subgroup G}
    (hLC : L ≤ Subgroup.centralizer ({c} : Set G)) (hAC : A ≤ Subgroup.centralizer ({c} : Set G)) :
    Nonempty ((L.subgroupOf (Subgroup.centralizer ({c} : Set G)) ⊔
        A.subgroupOf (Subgroup.centralizer ({c} : Set G))).map (QuotientGroup.mk'
          (aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G)))) ≃* lBarA c L A) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hCH : C ≤ H := centralizer_le_normalizer_zpowers c
  have hXC : L ⊔ A ≤ C := sup_le hLC hAC
  have hθ := inSubgroup_theta_centralizer c
  rw [← Subgroup.subgroupOf_sup hLC hAC]
  refine nonempty_map_mk_equiv hXC (hXC.trans hCH) _ _ fun x => ?_
  have key : ((x : G) ∈ inSubgroup (aschbacherSolvableCore 3) C) ↔
      ((x : G) ∈ inSubgroup (aschbacherSolvableCore 3) H) := by
    rw [hθ]
    exact ⟨fun h => h.2, fun h => ⟨hXC x.2, h⟩⟩
  constructor
  · intro h
    have h1 : (x : G) ∈ inSubgroup (aschbacherSolvableCore 3) C := ⟨_, h, rfl⟩
    obtain ⟨y, hy, hyx⟩ := key.mp h1
    have : y = Subgroup.inclusion (hXC.trans hCH) x := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro h
    have h1 : (x : G) ∈ inSubgroup (aschbacherSolvableCore 3) H := ⟨_, h, rfl⟩
    obtain ⟨y, hy, hyx⟩ := key.mpr h1
    have : y = Subgroup.inclusion hXC x := Subtype.ext hyx
    rw [← this]
    exact hy

end Images

section AutIn

variable {G : Type} [Group G] (C : Subgroup G)

theorem map_autIn_subgroupOf {L A : Subgroup G} (hLC : L ≤ C) (hAC : A ≤ C) :
    (Sec4.autIn (L.subgroupOf C) (A.subgroupOf C)).map
        (MulAut.congr (Subgroup.subgroupOfEquivOfLe hAC)).toMonoidHom = Sec4.autIn L A := by
  set e := Subgroup.subgroupOfEquivOfLe hAC with he
  have hN : ∀ h : C, h ∈ Subgroup.normalizer ((A.subgroupOf C : Subgroup C) : Set C) ↔
      (h : G) ∈ Subgroup.normalizer (A : Set G) := by
    intro h
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hh x
      constructor
      · intro hx
        have := (hh ⟨x, hAC hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
        exact Subgroup.mem_subgroupOf.mp this
      · intro hx
        have hxC : x ∈ C := by
          have : (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * h ∈ C :=
            C.mul_mem (C.mul_mem (C.inv_mem h.2) (hAC hx)) h.2
          simpa [mul_assoc] using this
        have := (hh ⟨x, hxC⟩).mpr (Subgroup.mem_subgroupOf.mpr hx)
        exact Subgroup.mem_subgroupOf.mp this
    · intro hh x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hh x
  have hcongr : ∀ (h : C) (hh : h ∈ Subgroup.normalizer ((A.subgroupOf C : Subgroup C) : Set C)),
      MulAut.congr e ((A.subgroupOf C).normalizerMonoidHom ⟨h, hh⟩) =
        A.normalizerMonoidHom ⟨(h : G), (hN h).mp hh⟩ := by
    intro h hh
    ext x
    rfl
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨h, hh, hL, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
    exact Sec4.mem_autIn_iff.mpr ⟨(h : G), (hN h).mp hh, Subgroup.mem_subgroupOf.mp hL,
      (hcongr h hh).symm⟩
  · intro hσ
    obtain ⟨g, hg, hgL, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    have hh : (⟨g, hLC hgL⟩ : C) ∈ Subgroup.normalizer ((A.subgroupOf C : Subgroup C) : Set C) :=
      (hN ⟨g, hLC hgL⟩).mpr hg
    exact ⟨_, Sec4.mem_autIn_iff.mpr ⟨⟨g, hLC hgL⟩, hh, Subgroup.mem_subgroupOf.mpr hgL, rfl⟩,
      hcongr _ hh⟩

theorem nonempty_autIn_subgroupOf_equiv {L A : Subgroup G} (hLC : L ≤ C) (hAC : A ≤ C) :
    Nonempty (Sec4.autIn (L.subgroupOf C) (A.subgroupOf C) ≃* Sec4.autIn L A) :=
  ⟨((Sec4.autIn (L.subgroupOf C) (A.subgroupOf C)).equivMapOfInjective _
    (MulAut.congr (Subgroup.subgroupOfEquivOfLe hAC)).injective).trans
    (MulEquiv.subgroupCongr (map_autIn_subgroupOf C hLC hAC))⟩

end AutIn

section Induced

variable {G : Type} [Group G] [Finite G] (C : Subgroup G)

theorem thetaQuotMulAut_sub_apply (L' : Subgroup C) {h : C}
    (hN : h ∈ Subgroup.normalizer (L' : Set C))
    (hN' : (h : G) ∈ Subgroup.normalizer ((L'.map C.subtype : Subgroup G) : Set G))
    (z : L'.map C.subtype ⧸ aschbacherSolvableCore 3 (L'.map C.subtype)) :
    Sec4.thetaQuotMulAut (L'.map C.subtype) ((L'.map C.subtype).normalizerMonoidHom ⟨h, hN'⟩) z =
      thetaQuotEquivSub C L' (Sec4.thetaQuotMulAut L' (L'.normalizerMonoidHom ⟨h, hN⟩)
        ((thetaQuotEquivSub C L').symm z)) := by
  rw [← congr_thetaQuotMulAut_sub C L' hN hN']
  rfl

theorem inducedAutHom_sub {M : Type*} [Group M] (L' : Subgroup C)
    (e : L' ⧸ aschbacherSolvableCore 3 L' ≃* M) {h : C}
    (hN : h ∈ Subgroup.normalizer (L' : Set C))
    (hN' : (h : G) ∈ Subgroup.normalizer ((L'.map C.subtype : Subgroup G) : Set G)) :
    KFacts.inducedAutHom (L'.map C.subtype) ((thetaQuotEquivSub C L').symm.trans e) ⟨h, hN'⟩ =
      KFacts.inducedAutHom L' e ⟨h, hN⟩ := by
  ext m
  rw [KFacts.inducedAutHom_apply, KFacts.inducedAutHom_apply]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_symm]
  change e ((thetaQuotEquivSub C L').symm (Sec4.thetaQuotMulAut (L'.map C.subtype)
      ((L'.map C.subtype).normalizerMonoidHom ⟨h, hN'⟩) (thetaQuotEquivSub C L' (e.symm m)))) =
    e (Sec4.thetaQuotMulAut L' (L'.normalizerMonoidHom ⟨h, hN⟩) (e.symm m))
  rw [thetaQuotMulAut_sub_apply C L' hN hN', MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply]

theorem inducesKind_sub {M : Type*} [Group M] (L' : Subgroup C) (P : KFacts.PinnedAut M)
    (e : L' ⧸ aschbacherSolvableCore 3 L' ≃* M) {x : C} {k : KFacts.AutKind}
    (h : KFacts.InducesKind L' P e x k) :
    KFacts.InducesKind (L'.map C.subtype) P ((thetaQuotEquivSub C L').symm.trans e) (x : G) k := by
  obtain ⟨hx, hk⟩ := h
  have hx' := (coe_mem_normalizer_map_iff C).mpr hx
  exact ⟨hx', by rw [inducedAutHom_sub C L' e hx hx']; exact hk⟩

theorem inducesStdKind_sub (L' : Subgroup C) {x : C} {k : KFacts.AutKind}
    (h : KFacts.InducesStdKind L' x k) :
    KFacts.InducesStdKind (L'.map C.subtype) (x : G) k := by
  cases h with
  | psl2 K h =>
    obtain ⟨e, he⟩ := h
    exact .psl2 K ⟨_, inducesKind_sub C L' _ e he⟩
  | psl n K hn h =>
    obtain ⟨e, he⟩ := h
    exact .psl n K hn ⟨_, inducesKind_sub C L' _ e he⟩
  | sl n K hn h =>
    obtain ⟨e, hx, he⟩ := h
    have hx' := (coe_mem_normalizer_map_iff C).mpr hx
    exact .sl n K hn ⟨(thetaQuotEquivSub C L').symm.trans e, hx',
      by rw [inducedAutHom_sub C L' e hx hx']; exact he⟩
  | psu3 hK hq h =>
    obtain ⟨e, he⟩ := h
    exact .psu3 hK hq ⟨_, inducesKind_sub C L' _ e he⟩
  | su3 hK hq h =>
    obtain ⟨e, hx, he⟩ := h
    have hx' := (coe_mem_normalizer_map_iff C).mpr hx
    exact .su3 hK hq ⟨(thetaQuotEquivSub C L').symm.trans e, hx',
      by rw [inducedAutHom_sub C L' e hx hx']; exact he⟩
  | psp r K hr h =>
    obtain ⟨e, he⟩ := h
    exact .psp r K hr ⟨_, inducesKind_sub C L' _ e he⟩
  | psp4even F h =>
    obtain ⟨e, he⟩ := h
    exact .psp4even F ⟨_, inducesKind_sub C L' _ e he⟩
  | g2 K hK3 hK4 h =>
    obtain ⟨e, he⟩ := h
    exact .g2 K hK3 hK4 ⟨_, inducesKind_sub C L' _ e he⟩
  | sz a K ha hK h =>
    obtain ⟨e, he⟩ := h
    exact .sz a K ha hK ⟨_, inducesKind_sub C L' _ e he⟩
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, hx, he⟩ := h
    have hx' := (coe_mem_normalizer_map_iff C).mpr hx
    exact .triality f hf K hK σ hσ ⟨(thetaQuotEquivSub C L').symm.trans e, hx',
      by rw [inducedAutHom_sub C L' e hx hx']; exact he⟩
  | largeRee a ha K hK h =>
    obtain ⟨e, he⟩ := h
    exact .largeRee a ha K hK ⟨_, inducesKind_sub C L' _ e he⟩

theorem inducesTypeOn_sub (L' : Subgroup C) {x : C} {k : ℕ} (h : Sec4.InducesTypeOn L' x k) :
    Sec4.InducesTypeOn (L'.map C.subtype) (x : G) k := by
  obtain ⟨hx, π, p, f, K, _, hK, hq, e, y, hy, hyk, hconj⟩ := h
  have hx' := (coe_mem_normalizer_map_iff C).mpr hx
  refine ⟨hx', π, p, f, K, inferInstance, hK, hq, (thetaQuotEquivSub C L').symm.trans e, y, hy,
    hyk, fun z => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, thetaQuotMulAut_sub_apply C L' hx hx',
    MulEquiv.symm_apply_apply]
  exact hconj _

end Induced

section Invariance

theorem map_center_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg e (hx (e.symm z))
    simpa using this
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro z
    have := congrArg e.symm (hy (e z))
    simpa using this

theorem map_commutator_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (commutator X).map e.toMonoidHom = commutator Y := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem map_frattini_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (frattini X).map e.toMonoidHom = frattini Y := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom) e.surjective
  · intro y hy
    have h :=
      frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective hy
    exact ⟨e.symm y, h, by simp⟩

theorem isExtraspecialPGroup_of_mulEquiv {p : ℕ} {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsExtraspecialPGroup p X) : IsExtraspecialPGroup p Y := by
  obtain ⟨hp, hc, hf, hz⟩ := h
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← map_commutator_mulEquiv e, ← map_center_mulEquiv e, hc]
  · rw [← map_frattini_mulEquiv e, ← map_center_mulEquiv e, hf]
  · rw [← map_center_mulEquiv e, Subgroup.card_map_of_injective e.injective, hz]

theorem isHeisThree_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Sec4.IsHeisThree X) : Sec4.IsHeisThree Y := by
  obtain ⟨hx, hc, hexp⟩ := h
  exact ⟨isExtraspecialPGroup_of_mulEquiv e hx, by rw [← Nat.card_congr e.toEquiv, hc],
    by rw [← Monoid.exponent_eq_of_mulEquiv e, hexp]⟩

theorem isHeisCentral_of_mulEquiv {X X' Y Y' : Type} [Group X] [Group X'] [Group Y] [Group Y']
    (e : X ≃* X') (f : Y ≃* Y') (h : Sec4.IsHeisCentral X Y) : Sec4.IsHeisCentral X' Y' := by
  obtain ⟨U, V, hUV, hcomm, hU, ⟨eV⟩, hcard⟩ := h
  refine ⟨U.map e.toMonoidHom, V.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hUV, Subgroup.map_top_of_surjective _ e.surjective]
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hcomm u hu v hv]
  · exact isHeisThree_of_mulEquiv (U.equivMapOfInjective _ e.injective) hU
  · exact ⟨(V.equivMapOfInjective _ e.injective).symm.trans (eV.trans f)⟩
  · rw [← Subgroup.map_inf_eq U V e.toMonoidHom e.injective,
      Subgroup.card_map_of_injective e.injective, hcard]

theorem isTripleCover_of_mulEquiv {X X' Y : Type*} [Group X] [Group X'] [Group Y]
    (e : X ≃* X') (h : Sec4.IsTripleCover X Y) : Sec4.IsTripleCover X' Y := by
  obtain ⟨hcard, ⟨φ⟩⟩ := h
  refine ⟨by rw [← map_center_mulEquiv e, Subgroup.card_map_of_injective e.injective, hcard],
    ⟨(QuotientGroup.congr _ _ e (map_center_mulEquiv e)).symm.trans φ⟩⟩

theorem isSLThreePi_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : Sec4.IsSLThreePi X) : Sec4.IsSLThreePi X' := by
  obtain ⟨q, K, _, _, h⟩ := h
  refine ⟨q, K, inferInstance, inferInstance, ?_⟩
  rcases h with ⟨h1, h2, ⟨φ⟩⟩ | ⟨h1, h2, ⟨φ⟩⟩
  · exact Or.inl ⟨h1, h2, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr ⟨h1, h2, ⟨e.symm.trans φ⟩⟩

theorem isZ3LThreePi_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : Sec8.IsZ3LThreePi X) : Sec8.IsZ3LThreePi X' := by
  obtain ⟨p, f, hp, hf, h⟩ := h
  refine ⟨p, f, hp, hf, ?_⟩
  rcases h with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact Or.inl ⟨hq, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr ⟨hq, ⟨e.symm.trans φ⟩⟩

theorem isZ3PGLThreePi_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : Sec8.IsZ3PGLThreePi X) : Sec8.IsZ3PGLThreePi X' := by
  obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := h
  exact ⟨π, p, f, K, inferInstance, hK, hq, ⟨e.symm.trans φ⟩⟩

theorem isSLThreePiTwo_of_mulEquiv {X X' : Type} [Group X] [Group X'] (φ : X ≃* X')
    (h : Sec4.IsSLThreePiTwo X) : Sec4.IsSLThreePiTwo X' := by
  obtain ⟨L₀, hL, u, a, hSL, hu, huL, hou, ha3, hgen, hne, hmem, π, p, f, K, _, hK, hq, e, y, hy,
    hy3, hconj⟩ := h
  set L₁ := L₀.map φ.toMonoidHom with hL₁
  have hL₁n : L₁.Normal := hL.map φ.toMonoidHom φ.surjective
  set ψ : L₀ ≃* L₁ := L₀.equivMapOfInjective _ φ.injective with hψ
  refine ⟨L₁, hL₁n, φ u, φ a, isSLThreePi_of_mulEquiv ψ hSL, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    π, p, f, K, inferInstance, hK, hq, ψ.symm.trans e, y, hy, hy3, fun z => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hu z hz
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, this]
  · rintro ⟨z, hz, hzu⟩
    exact huL (φ.injective hzu ▸ hz)
  · have := orderOf_injective φ.toMonoidHom φ.injective u
    simp only [MulEquiv.coe_toMonoidHom] at this
    rw [this, hou]
  · rw [← map_pow, ha3, map_one]
  · rw [show ({φ u, φ a} : Set X') = φ.toMonoidHom '' {u, a} by
      simp [Set.image_insert_eq, Set.image_singleton], ← MonoidHom.map_closure, hL₁,
      ← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ φ.surjective]
  · intro h1
    apply hne
    apply φ.injective
    simpa [map_mul, map_inv] using h1
  · have hφc : φ u * φ a * (φ u)⁻¹ * (φ a)⁻¹ = φ (u * a * u⁻¹ * a⁻¹) := by
      simp [map_mul, map_inv]
    rw [hφc]
    refine ⟨⟨_, hmem.1, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hmem.2 z hz
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, this]
  · obtain ⟨z₀, rfl⟩ := ψ.surjective z
    have h1 : (⟨φ a * ((ψ z₀ : L₁) : X') * (φ a)⁻¹,
        hL₁n.conj_mem _ (ψ z₀).2 (φ a)⟩ : L₁) =
        ψ ⟨a * z₀ * a⁻¹, hL.conj_mem z₀ z₀.2 a⟩ := by
      apply Subtype.ext
      change φ a * φ (z₀ : X) * (φ a)⁻¹ = φ (a * (z₀ : X) * a⁻¹)
      simp [map_mul, map_inv]
    rw [MulEquiv.trans_apply, h1, MulEquiv.symm_apply_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    exact hconj z₀

end Invariance

end CFSG.RankThree.PartTwo.Sec13
