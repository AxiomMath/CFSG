module

public import CFSG.Timmesfeld.Bridge.RootStructWTIRadical

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem map_mk_conj {R : Subgroup G} {N : Subgroup R} [N.Normal] {H : Subgroup G} (hH : H ≤ R)
    (x : R) :
    ((H.subgroupOf R).map (QuotientGroup.mk' N)).map
        (MulAut.conj (QuotientGroup.mk' N x)).toMonoidHom =
      ((H.map (MulAut.conj (x : G)).toMonoidHom).subgroupOf R).map (QuotientGroup.mk' N) := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨x * h * x⁻¹, ⟨h, hh, by simp⟩, by simp⟩
  · rintro ⟨y, ⟨h, hh, hhy⟩, rfl⟩
    have hhR : h ∈ R := hH hh
    refine ⟨QuotientGroup.mk' N ⟨h, hhR⟩, ⟨⟨h, hhR⟩, hh, rfl⟩, ?_⟩
    have e : y = x * ⟨h, hhR⟩ * x⁻¹ := Subtype.ext (by simpa using hhy.symm)
    simp [e]

theorem lineGroup_le_centralizer (D : Set G) (a d : G) :
    lineGroup D a d ≤ Subgroup.centralizer ({a} : Set G) := by
  have hK : (nCore D d ⊓ Subgroup.centralizer {a}) ⊔ nCore D a ≤
      Subgroup.centralizer ({a} : Set G) :=
    sup_le inf_le_right fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem_nCore hy).eq
  refine iSup_le fun g => ?_
  rintro _ ⟨x, hx, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 (hK hx)) (Subgroup.inv_mem _ g.2)

@[expose] noncomputable def lineRadicalBar (D : Set G) (a d : G)
    [((nCore D a).subgroupOf (lineGroup D a d)).Normal] (L : Subgroup G) :
    Subgroup (lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)) :=
  ((lineRadical D a L).subgroupOf (lineGroup D a d)).map (QuotientGroup.mk' _)

theorem exists_mem_rootLines_ne_ne {a : G} {L₁ L₂ : Subgroup G} (h3 : 3 ≤ (rootLines D a).ncard) :
    ∃ L₃ ∈ rootLines D a, L₃ ≠ L₁ ∧ L₃ ≠ L₂ := by
  by_contra! hno
  have hsub : rootLines D a ⊆ {L₁, L₂} := fun L₃ hL₃ => by
    by_cases h : L₃ = L₁
    · exact Or.inl h
    · exact Or.inr (hno L₃ hL₃ h)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({L₁, L₂} : Set (Subgroup G)).ncard ≤ 2 :=
    (Set.ncard_insert_le L₁ {L₂}).trans (by rw [Set.ncard_singleton])
  omega

namespace LineSetting

variable (hL : LineSetting G D) {a : G} (ha : a ∈ D)
include hL ha

theorem lineRadical_le_lineGroup {d : G} (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard) {L : Subgroup G}
    (hL' : L ∈ rootLines D a) : lineRadical D a L ≤ lineGroup D a d := by
  have hclass := hL.hyp.isClass
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  by_cases hLT : L = rootGroup D a ⊔ rootGroup D d
  · obtain ⟨T', hT', hne⟩ := hL.exists_ne_mem_rootLines ha hT
    rw [hL.lineGroup_eq ha hd had hadD hdT hT' hne h3, hLT]
    exact le_sup_left
  · rw [hL.lineGroup_eq ha hd had hadD hdT hL' hLT h3]
    exact le_sup_right

theorem nCore_le_lineGroup {d : G} (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard) : nCore D a ≤ lineGroup D a d :=
  (nCore_le_lineRadical a _).trans
    (hL.lineRadical_le_lineGroup ha hd had hadD hdT h3 ⟨d, hd, had, hadD, hdT, rfl⟩)

omit ha in
theorem nCore_subgroupOf_lineGroup_normal (d : G) :
    ((nCore D a).subgroupOf (lineGroup D a d)).Normal := by
  have hclass := hL.hyp.isClass
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact conj_mem_nCore hclass (Subgroup.mem_centralizer_singleton_iff.1
    (lineGroup_le_centralizer D a d g.2)) hn

omit ha in
theorem lineGroup_le_normalizer (d : G) :
    lineGroup D a d ≤ Subgroup.normalizer (rootGroup D a : Set G) :=
  (lineGroup_le_centralizer D a d).trans
    (centralizer_le_normalizer_rootGroup hL.hyp.isClass a)

@[expose] noncomputable def lineGroupAction (d : G) :
    lineGroup D a d →* Equiv.Perm (rootLines D a) :=
  (hL.lineAction ha).comp (Subgroup.inclusion (hL.lineGroup_le_normalizer d))

theorem lineGroupAction_eq_one {d : G} {g : lineGroup D a d} (hg : (g : G) ∈ nCore D a) :
    hL.lineGroupAction ha d g = 1 :=
  hL.lineAction_eq_one ha (g := Subgroup.inclusion (hL.lineGroup_le_normalizer d) g)
    (nCore_le_closure_commute D a hg)

@[expose] noncomputable def lineGroupBarAction (d : G)
    [((nCore D a).subgroupOf (lineGroup D a d)).Normal] :
    lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d) →* Equiv.Perm (rootLines D a) :=
  QuotientGroup.lift _ (hL.lineGroupAction ha d) fun _ hg =>
    hL.lineGroupAction_eq_one ha (Subgroup.mem_subgroupOf.1 hg)

section Bar

variable {d : G} [((nCore D a).subgroupOf (lineGroup D a d)).Normal]

omit hL ha in
theorem mem_lineRadicalBar {L : Subgroup G}
    {z : lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)} :
    z ∈ lineRadicalBar D a d L ↔ ∃ x : lineGroup D a d, (x : G) ∈ lineRadical D a L ∧
      QuotientGroup.mk' _ x = z := by
  simp only [lineRadicalBar, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem lineGroupBarAction_mk (x : lineGroup D a d) (L : rootLines D a) :
    ((hL.lineGroupBarAction ha d (QuotientGroup.mk' _ x)) L : Subgroup G) =
      L.1.map (MulAut.conj (x : G)).toMonoidHom :=
  rfl

theorem lineGroupBarAction_apply_self {L : Subgroup G} (hL' : L ∈ rootLines D a)
    {z : lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)}
    (hz : z ∈ lineRadicalBar D a d L) : hL.lineGroupBarAction ha d z ⟨L, hL'⟩ = ⟨L, hL'⟩ := by
  obtain ⟨x, hx, rfl⟩ := mem_lineRadicalBar.1 hz
  exact Subtype.ext (by
    rw [lineGroupBarAction_mk]
    exact RankOne.map_conj_eq_self_iff.2 (hL.lineRadical_le_normalizer ha hL' hx))

theorem eq_one_of_lineGroupBarAction_apply_eq {L L' : Subgroup G} (hL' : L ∈ rootLines D a)
    (hL'' : L' ∈ rootLines D a) (hne : L' ≠ L)
    {z : lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)}
    (hz : z ∈ lineRadicalBar D a d L)
    (hzL : hL.lineGroupBarAction ha d z ⟨L', hL''⟩ = ⟨L', hL''⟩) : z = 1 := by
  obtain ⟨x, hx, rfl⟩ := mem_lineRadicalBar.1 hz
  have h1 : L'.map (MulAut.conj (x : G)).toMonoidHom = L' := by
    have := congrArg Subtype.val hzL
    rwa [lineGroupBarAction_mk] at this
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hL.mem_nCore_of_mem_lineRadical ha hL' hL'' hne hx h1

theorem exists_mem_lineRadicalBar_apply_eq (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard) {L L₁ L₂ : Subgroup G}
    (hL' : L ∈ rootLines D a) (h₁ : L₁ ∈ rootLines D a) (h₂ : L₂ ∈ rootLines D a)
    (h₁L : L₁ ≠ L) (h₂L : L₂ ≠ L) :
    ∃ z ∈ lineRadicalBar D a d L, hL.lineGroupBarAction ha d z ⟨L₁, h₁⟩ = ⟨L₂, h₂⟩ := by
  obtain ⟨x, hx, hxL⟩ := hL.exists_mem_lineRadical_map_conj_eq ha hL' h₁ h₂ h₁L h₂L
  have hxR := hL.lineRadical_le_lineGroup ha hd had hadD hdT h3 hL' hx
  exact ⟨QuotientGroup.mk' _ ⟨x, hxR⟩, mem_lineRadicalBar.2 ⟨⟨x, hxR⟩, hx, rfl⟩,
    Subtype.ext (by rw [lineGroupBarAction_mk]; exact hxL)⟩

theorem exists_mem_nCore_mk_eq {L : Subgroup G} {e : G} (he : e ∈ D) (hae : Commute a e)
    (haeD : a * e ∈ D) (heT : e ∉ rootSet D a)
    (hLe : L = rootGroup D a ⊔ rootGroup D e) (hR : nCore D a ≤ lineGroup D a d)
    {x : lineGroup D a d} (hx : (x : G) ∈ lineRadical D a L) :
    ∃ k : lineGroup D a d, (k : G) ∈ nCore D e ∧
      QuotientGroup.mk' ((nCore D a).subgroupOf (lineGroup D a d)) x =
        QuotientGroup.mk' ((nCore D a).subgroupOf (lineGroup D a d)) k := by
  have := hL.hyp.finite
  have hclass := hL.hyp.isClass
  subst hLe
  rw [hL.lineRadical_eq ha ⟨e, he, hae, haeD, heT, rfl⟩ he (right_mem_line he)
    (fun h' => heT (mem_rootSet_of_mem_rootGroup hclass ha he h'))] at hx
  have hle : nCore D e ⊓ Subgroup.centralizer ((rootGroup D a ⊔ rootGroup D e : Subgroup G) :
      Set G) ≤ Subgroup.normalizer (nCore D a : Set G) := fun k hk => by
    rw [Subgroup.mem_normalizer_iff]
    have hka : Commute k a :=
      ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hk).2) a (left_mem_line ha)).symm
    intro y
    refine ⟨fun hy => conj_mem_nCore hclass hka hy, fun hy => ?_⟩
    have := conj_mem_nCore hclass hka.inv_left hy
    rwa [show k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y by group] at this
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx
  obtain ⟨k, hk, m, hm, hkm⟩ := hx
  have hmR : m ∈ lineGroup D a d := hR hm
  have hkR : k ∈ lineGroup D a d := by
    have := Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ hmR)
    rwa [← hkm, mul_inv_cancel_right] at this
  refine ⟨⟨k, hkR⟩, (Subgroup.mem_inf.1 hk).1, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hkm, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  exact Subgroup.inv_mem _ hm

theorem lineRadicalBar_commute_and_sq {L : Subgroup G} (hL' : L ∈ rootLines D a)
    (hR : nCore D a ≤ lineGroup D a d)
    {z z' : lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)}
    (hz : z ∈ lineRadicalBar D a d L) (hz' : z' ∈ lineRadicalBar D a d L) :
    Commute z z' ∧ z * z = 1 := by
  obtain ⟨e, he, hae, haeD, heT, hLe⟩ := hL'
  obtain ⟨x, hx, rfl⟩ := mem_lineRadicalBar.1 hz
  obtain ⟨x', hx', rfl⟩ := mem_lineRadicalBar.1 hz'
  obtain ⟨k, hk, hxk⟩ := hL.exists_mem_nCore_mk_eq ha he hae haeD heT hLe hR hx
  obtain ⟨k', hk', hxk'⟩ := hL.exists_mem_nCore_mk_eq ha he hae haeD heT hLe hR hx'
  rw [hxk, hxk']
  have hAe : rootGroup D e ≤ nCore D a :=
    le_sup_right.trans (hL.sup_rootGroup_le_nCore ha he hae)
  have hR' := nCoreCommutatorInRoot_of_hyp hL.hyp hL.closure
  refine ⟨?_, ?_⟩
  · show QuotientGroup.mk' _ k * QuotientGroup.mk' _ k' =
      QuotientGroup.mk' _ k' * QuotientGroup.mk' _ k
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    have := hR' e he _ (Subgroup.inv_mem _ hk') _ (Subgroup.inv_mem _ hk)
    rw [inv_inv, inv_inv] at this
    convert hAe this using 1
    group
  · rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_mul]
    exact hAe (mul_self_mem_rootGroup_of_mem_nCore hL.hyp hL.closure he hk)

theorem map_conj_lineRadicalBar (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard) {L : Subgroup G}
    (hL' : L ∈ rootLines D a) (x : lineGroup D a d) :
    (lineRadicalBar D a d L).map (MulAut.conj (QuotientGroup.mk' _ x)).toMonoidHom =
      lineRadicalBar D a d (L.map (MulAut.conj (x : G)).toMonoidHom) := by
  rw [lineRadicalBar, map_mk_conj (hL.lineRadical_le_lineGroup ha hd had hadD hdT h3 hL'),
    map_conj_lineRadical hL.hyp.isClass
      (Subgroup.mem_centralizer_singleton_iff.1 (lineGroup_le_centralizer D a d x.2))]
  rfl

theorem lineRadicalBar_le_sup (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard) {L L₁ L₂ : Subgroup G}
    (hL' : L ∈ rootLines D a) (h₁ : L₁ ∈ rootLines D a) (h₂ : L₂ ∈ rootLines D a)
    (h12 : L₁ ≠ L₂) :
    lineRadicalBar D a d L ≤ lineRadicalBar D a d L₁ ⊔ lineRadicalBar D a d L₂ := by
  by_cases hL1 : L = L₁
  · rw [hL1]; exact le_sup_left
  by_cases hL2 : L = L₂
  · rw [hL2]; exact le_sup_right
  obtain ⟨z, hz, hzL⟩ := hL.exists_mem_lineRadicalBar_apply_eq ha hd had hadD hdT h3 h₂ h₁ hL'
    h12 hL2
  obtain ⟨x, hx, rfl⟩ := mem_lineRadicalBar.1 hz
  have hxL : L₁.map (MulAut.conj (x : G)).toMonoidHom = L := by
    have := congrArg Subtype.val hzL
    rwa [lineGroupBarAction_mk] at this
  rw [← hxL, ← hL.map_conj_lineRadicalBar ha hd had hadD hdT h3 h₁]
  rintro _ ⟨w, hw, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hz' : QuotientGroup.mk' _ x ∈ lineRadicalBar D a d L₁ ⊔ lineRadicalBar D a d L₂ :=
    Subgroup.mem_sup_right hz
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hz' (Subgroup.mem_sup_left hw))
    (Subgroup.inv_mem _ hz')

theorem lineRadicalBar_sup_eq_top (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ rootLines D a) (h₂ : L₂ ∈ rootLines D a) (h12 : L₁ ≠ L₂) :
    lineRadicalBar D a d L₁ ⊔ lineRadicalBar D a d L₂ = ⊤ := by
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨T', hT', hne⟩ := hL.exists_ne_mem_rootLines ha hT
  have hR := hL.lineGroup_eq ha hd had hadD hdT hT' hne h3
  have htop : lineRadicalBar D a d (rootGroup D a ⊔ rootGroup D d) ⊔
      lineRadicalBar D a d T' = ⊤ := by
    rw [lineRadicalBar, lineRadicalBar, ← Subgroup.map_sup,
      ← Subgroup.subgroupOf_sup (hL.lineRadical_le_lineGroup ha hd had hadD hdT h3 hT)
        (hL.lineRadical_le_lineGroup ha hd had hadD hdT h3 hT'), ← hR,
      Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rw [eq_top_iff, ← htop]
  exact sup_le (hL.lineRadicalBar_le_sup ha hd had hadD hdT h3 hT h₁ h₂ h12)
    (hL.lineRadicalBar_le_sup ha hd had hadD hdT h3 hT' h₁ h₂ h12)

theorem moufang_lineRadicalBar (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ rootLines D a) (h₂ : L₂ ∈ rootLines D a) (h12 : L₁ ≠ L₂)
    {z : lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)}
    (hz : z ∈ lineRadicalBar D a d L₁) (hz1 : z ≠ 1) :
    ∃ w ∈ lineRadicalBar D a d L₂, w ≠ 1 ∧
      (lineRadicalBar D a d L₁).map (MulAut.conj w).toMonoidHom =
        (lineRadicalBar D a d L₂).map (MulAut.conj z).toMonoidHom := by
  obtain ⟨x, hx, rfl⟩ := mem_lineRadicalBar.1 hz
  have hxN := hL.lineGroup_le_normalizer d x.2
  set L := L₂.map (MulAut.conj (x : G)).toMonoidHom with hLdef
  have hL' : L ∈ rootLines D a := hL.map_conj_mem_rootLines ha hxN h₂
  have hLL₂ : L ≠ L₂ := fun h' => hz1 (hL.eq_one_of_lineGroupBarAction_apply_eq ha h₁ h₂
    (Ne.symm h12) hz (Subtype.ext (by rw [lineGroupBarAction_mk]; exact h')))
  have hLL₁ : L ≠ L₁ := fun h' => by
    have h1 : L₁.map (MulAut.conj (x : G)).toMonoidHom = L₁ :=
      RankOne.map_conj_eq_self_iff.2 (hL.lineRadical_le_normalizer ha h₁ hx)
    exact h12 (Subgroup.map_injective (MulAut.conj (x : G)).injective (h1.trans h'.symm))
  obtain ⟨w, hw, hwL⟩ := hL.exists_mem_lineRadicalBar_apply_eq ha hd had hadD hdT h3 h₂ h₁ hL'
    h12 hLL₂
  obtain ⟨y, hy, rfl⟩ := mem_lineRadicalBar.1 hw
  have hyL : L₁.map (MulAut.conj (y : G)).toMonoidHom = L := by
    have := congrArg Subtype.val hwL
    rwa [lineGroupBarAction_mk] at this
  refine ⟨_, hw, fun h' => hLL₁ ?_, ?_⟩
  · rw [← hyL]
    have : hL.lineGroupBarAction ha d (QuotientGroup.mk' _ y) ⟨L₁, h₁⟩ = ⟨L₁, h₁⟩ := by
      rw [h', map_one, Equiv.Perm.one_apply]
    have := congrArg Subtype.val this
    rwa [lineGroupBarAction_mk] at this
  · rw [hL.map_conj_lineRadicalBar ha hd had hadD hdT h3 h₁,
      hL.map_conj_lineRadicalBar ha hd had hadD hdT h3 h₂, hyL]

theorem isElemAbRankOne_lineRadicalBar (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ rootLines D a) (h₂ : L₂ ∈ rootLines D a) (h12 : L₁ ≠ L₂) :
    IsElemAbRankOne (lineRadicalBar D a d L₁) (lineRadicalBar D a d L₂) := by
  have hR := hL.nCore_le_lineGroup ha hd had hadD hdT h3
  refine ⟨hL.lineRadicalBar_sup_eq_top ha hd had hadD hdT h3 h₁ h₂ h12, fun heq => ?_,
    fun z hz z' hz' => (hL.lineRadicalBar_commute_and_sq ha h₁ hR hz hz').1,
    fun z hz => (hL.lineRadicalBar_commute_and_sq ha h₁ hR hz hz).2,
    fun z hz hz1 => hL.moufang_lineRadicalBar ha hd had hadD hdT h3 h₁ h₂ h12 hz hz1,
    fun z hz hz1 => hL.moufang_lineRadicalBar ha hd had hadD hdT h3 h₂ h₁ (Ne.symm h12) hz hz1⟩
  obtain ⟨L₃, hL₃, h31, h32⟩ := exists_mem_rootLines_ne_ne (L₁ := L₁) (L₂ := L₂) h3
  obtain ⟨z, hz, hzL⟩ := hL.exists_mem_lineRadicalBar_apply_eq ha hd had hadD hdT h3 h₂ h₁ hL₃
    h12 h32
  rw [← heq] at hz
  rw [hL.lineGroupBarAction_apply_self ha h₁ hz] at hzL
  exact h31 (congrArg Subtype.val hzL).symm

theorem card_lineRadicalBar (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard) {L : Subgroup G}
    (hL' : L ∈ rootLines D a) :
    Nat.card (lineRadicalBar D a d L) + 1 = (rootLines D a).ncard := by
  have := hL.hyp.finite
  obtain ⟨L₀, hL₀, hL₀L⟩ := hL.exists_ne_mem_rootLines ha hL'
  set ψ := hL.lineGroupBarAction ha d
  have hne : ∀ z ∈ lineRadicalBar D a d L, (ψ z ⟨L₀, hL₀⟩).1 ≠ L := fun z hz h' => by
    have h1 : ψ z ⟨L₀, hL₀⟩ = ψ z ⟨L, hL'⟩ := by
      rw [hL.lineGroupBarAction_apply_self ha hL' hz]; exact Subtype.ext h'
    exact hL₀L (congrArg Subtype.val ((ψ z).injective h1))
  let f : lineRadicalBar D a d L → ↥(rootLines D a \ {L}) := fun z =>
    ⟨(ψ z.1 ⟨L₀, hL₀⟩).1, (ψ z.1 ⟨L₀, hL₀⟩).2, hne z.1 z.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun z w hzw => ?_, fun L' => ?_⟩
    · have h1 : ψ z.1 ⟨L₀, hL₀⟩ = ψ w.1 ⟨L₀, hL₀⟩ :=
        Subtype.ext (by simpa [f] using congrArg Subtype.val hzw)
      have h2 : ψ (w.1⁻¹ * z.1) ⟨L₀, hL₀⟩ = ⟨L₀, hL₀⟩ := by
        rw [map_mul, map_inv, Equiv.Perm.mul_apply, h1, ← Equiv.Perm.mul_apply, inv_mul_cancel,
          Equiv.Perm.one_apply]
      have h3 := hL.eq_one_of_lineGroupBarAction_apply_eq ha hL' hL₀ hL₀L
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ w.2) z.2) h2
      exact Subtype.ext (inv_mul_eq_one.1 h3).symm
    · obtain ⟨z, hz, hzL⟩ := hL.exists_mem_lineRadicalBar_apply_eq ha hd had hadD hdT h3 hL' hL₀
        L'.2.1 hL₀L L'.2.2
      exact ⟨⟨z, hz⟩, Subtype.ext (by simp only [f]; exact congrArg Subtype.val hzL)⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_coe_set_eq,
    Set.ncard_sdiff_singleton_of_mem hL']
  have hpos : 0 < (rootLines D a).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨L, hL'⟩
  omega

theorem ker_lineGroupBarAction_le_center (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h3 : 3 ≤ (rootLines D a).ncard) {L₁ L₂ : Subgroup G}
    (h₁ : L₁ ∈ rootLines D a) (h₂ : L₂ ∈ rootLines D a) (h12 : L₁ ≠ L₂) :
    (hL.lineGroupBarAction ha d).ker ≤ Subgroup.center _ := by
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective _ k
  have hnorm : ∀ L (hL' : L ∈ rootLines D a),
      (lineRadicalBar D a d L).map (MulAut.conj (QuotientGroup.mk' _ r)).toMonoidHom =
        lineRadicalBar D a d L := by
    intro L hL'
    rw [hL.map_conj_lineRadicalBar ha hd had hadD hdT h3 hL' r]
    have : hL.lineGroupBarAction ha d (QuotientGroup.mk' _ r) ⟨L, hL'⟩ = ⟨L, hL'⟩ := by
      rw [hk, Equiv.Perm.one_apply]
    have := congrArg Subtype.val this
    rw [lineGroupBarAction_mk] at this
    rw [this]
  have hcomm : ∀ L (hL' : L ∈ rootLines D a), ∀ z ∈ lineRadicalBar D a d L,
      z * QuotientGroup.mk' _ r = QuotientGroup.mk' _ r * z := by
    intro L hL' z hz
    obtain ⟨L₀, hL₀, hL₀L⟩ := hL.exists_ne_mem_rootLines ha hL'
    set k := QuotientGroup.mk' ((nCore D a).subgroupOf (lineGroup D a d)) r
    have h1 : k * z * k⁻¹ * z⁻¹ ∈ lineRadicalBar D a d L := by
      have : k * z * k⁻¹ ∈ lineRadicalBar D a d L := by
        rw [← hnorm L hL']
        exact ⟨z, hz, rfl⟩
      exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hz)
    have h2 : hL.lineGroupBarAction ha d (k * z * k⁻¹ * z⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hk, one_mul, inv_one, mul_one,
        mul_inv_cancel]
    have h3' := hL.eq_one_of_lineGroupBarAction_apply_eq ha hL' hL₀ hL₀L h1
      (by rw [h2, Equiv.Perm.one_apply])
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3'
    exact h3'.symm
  have hle : lineRadicalBar D a d L₁ ⊔ lineRadicalBar D a d L₂ ≤
      Subgroup.centralizer ({QuotientGroup.mk' _ r} : Set _) :=
    sup_le (fun z hz => Subgroup.mem_centralizer_singleton_iff.2 (hcomm L₁ h₁ z hz))
      (fun z hz => Subgroup.mem_centralizer_singleton_iff.2 (hcomm L₂ h₂ z hz))
  rw [hL.lineRadicalBar_sup_eq_top ha hd had hadD hdT h3 h₁ h₂ h12] at hle
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))

end Bar

end LineSetting

namespace LineSetting

section TypeZero

variable {G : Type} [Group G] {D : Set G} (hL : LineSetting G D) {a : G} (ha : a ∈ D)
include hL ha
variable {d : G} [((nCore D a).subgroupOf (lineGroup D a d)).Normal]

theorem exists_mulEquiv_lineGroupBar (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ rootLines D a)
    (h₂ : L₂ ∈ rootLines D a) (h12 : L₁ ≠ L₂) (h5 : 5 ≤ (rootLines D a).ncard) :
    ∃ n : ℕ, 2 ≤ n ∧ (rootLines D a).ncard = 2 ^ n + 1 ∧
      ∃ φ : (lineGroup D a d ⧸ (nCore D a).subgroupOf (lineGroup D a d)) ≃*
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        (lineRadicalBar D a d L₁).map φ.toMonoidHom = upperUnipotent (GaloisField 2 n) ∧
        (lineRadicalBar D a d L₂).map φ.toMonoidHom = lowerUnipotent (GaloisField 2 n) := by
  have := hL.hyp.finite
  have h3 : 3 ≤ (rootLines D a).ncard := by omega
  have hcard := hL.card_lineRadicalBar ha hd had hadD hdT h3 h₁
  obtain ⟨n, hn2, hn, φ, hφ1, hφ2⟩ := rankOne_mulEquiv_SL2
    (hL.isElemAbRankOne_lineRadicalBar ha hd had hadD hdT h3 h₁ h₂ h12) (by omega)
  exact ⟨n, hn2, by omega, φ, hφ1, hφ2⟩

theorem lineGroupBarAction_injective (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D)
    (hdT : d ∉ rootSet D a) (h5 : 5 ≤ (rootLines D a).ncard) :
    Function.Injective (hL.lineGroupBarAction ha d) := by
  have := hL.hyp.finite
  have h3 : 3 ≤ (rootLines D a).ncard := by omega
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨T', hT', hne⟩ := hL.exists_ne_mem_rootLines ha hT
  obtain ⟨n, -, -, φ, -, -⟩ := hL.exists_mulEquiv_lineGroupBar ha hd had hadD hdT hT hT'
    (Ne.symm hne) h5
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro z hz
  have hzc := hL.ker_lineGroupBarAction_le_center ha hd had hadD hdT h3 hT hT' (Ne.symm hne) hz
  have hφz : φ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hzc g']
  rw [RankOne.center_SL2_eq_bot, Subgroup.mem_bot] at hφz
  rw [Subgroup.mem_bot]
  exact φ.injective (hφz.trans φ.map_one.symm)

end TypeZero

end LineSetting

end CFSG.Timmesfeld.Bridge
