module

public import CFSG.Quasithin.Background.D216Restrict
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.Quasithin

open CFSG.Open

section Transfer

variable {V : Type*} [CommGroup V]

theorem centralizer_fittingOf_le_of_solvable [Finite V] {X : Subgroup (MulAut V)}
    (hX : Group.IsSolvable ↥X) :
    X ⊓ Subgroup.centralizer (fittingOf X : Set (MulAut V)) ≤ fittingOf X := by
  have hle := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := ↥X) hX
  rintro g ⟨hgX, hg⟩
  have : (⟨g, hgX⟩ : ↥X) ∈ Subgroup.centralizer (CFSG.fittingSubgroup ↥X : Set ↥X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have := Subgroup.mem_centralizer_iff.mp hg (f : MulAut V) ⟨f, hf, rfl⟩
    exact Subtype.ext this
  exact ⟨_, hle this, rfl⟩

theorem le_fittingOf_of_normal_nilpotent [Finite V] {X N : Subgroup (MulAut V)} (hNX : N ≤ X)
    (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hnil : Group.IsNilpotent N) : N ≤ fittingOf X := by
  have hN : (N.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm g g.2 n hn
  have hnil' : Group.IsNilpotent (N.subgroupOf X) :=
    Group.nilpotent_of_mulEquiv (G := N) (Subgroup.subgroupOfEquivOfLe hNX).symm
  have hle : N.subgroupOf X ≤ CFSG.fittingSubgroup ↥X := le_sSup ⟨hN, hnil'⟩
  intro n hn
  exact ⟨⟨n, hNX hn⟩, hle (Subgroup.mem_subgroupOf.mpr hn), rfl⟩

theorem isQuotientOfSQTK_of_le {X K : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hX : IsQuotientOfSQTKTC ↥X) : IsQuotientOfSQTKTC ↥K := by
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hX
  let K' : Subgroup ↥X := K.subgroupOf X
  refine ⟨↥(K'.comap φ), inferInstance, inferInstance, ?_, hK.subgroup _, ?_⟩
  · intro p hp hp2
    exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (K'.comap φ).subtype
      (K'.comap φ).subtype_injective).trans (hSQT p hp hp2)
  · refine ⟨(Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom.comp (φ.subgroupComap K'), ?_⟩
    exact (Subgroup.subgroupOfEquivOfLe hKX).surjective.comp
      (MonoidHom.subgroupComap_surjective φ K' hφ)

theorem isQuotientOfSQTK_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hX : IsQuotientOfSQTKTC X) : IsQuotientOfSQTKTC Y := by
  obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hX
  exact ⟨S, inferInstance, inferInstance, hSQT, hK, e.toMonoidHom.comp φ, e.surjective.comp hφ⟩

end Transfer

section Restrict2

variable {V : Type*} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U W : Subgroup V}

@[expose] noncomputable def SuppData.restrictEquiv (h : SuppData G U W) : ↥G ≃* ↥(autSub G U) :=
  MulEquiv.ofBijective
    (((resHom U).comp (Subgroup.inclusion h.stab)).codRestrict (autSub G U)
      (fun g => mem_autSub.mpr ⟨Subgroup.inclusion h.stab g, g.2, rfl⟩))
    ⟨fun g k hgk => Subtype.ext (h.eq_of_resHom_eq g.2 k.2 (congrArg Subtype.val hgk)),
      fun φ => by
        obtain ⟨g, hg, hgφ⟩ := mem_autSub.mp φ.2
        exact ⟨⟨g, hg⟩, Subtype.ext hgφ⟩⟩

omit [Finite V] in
theorem SuppData.isSolvable_autSub (h : SuppData G U W) (hG : Group.IsSolvable ↥G) :
    Group.IsSolvable ↥(autSub G U) :=
  Group.isSolvable_of_surjective (f := h.restrictEquiv.toMonoidHom) h.restrictEquiv.surjective

omit [Finite V] in
theorem SuppData.eq_bot_of_normal_two (h : SuppData G U W)
    (hG : ∀ A : Subgroup (MulAut V), A ≤ G → (∀ g ∈ G, ∀ a ∈ A, g * a * g⁻¹ ∈ A) →
      IsPGroup 2 A → A = ⊥)
    {Q : Subgroup (MulAut U)} (hQ : Q ≤ autSub G U)
    (hnorm : ∀ φ ∈ autSub G U, ∀ q ∈ Q, φ * q * φ⁻¹ ∈ Q) (hQ2 : IsPGroup 2 Q) : Q = ⊥ := by
  have hAG : G ⊓ extAutSub U Q ≤ G := inf_le_left
  have hAQ : autSub (G ⊓ extAutSub U Q) U = Q := autSub_lift hQ
  have hAnorm : ∀ g ∈ G, ∀ a ∈ G ⊓ extAutSub U Q, g * a * g⁻¹ ∈ G ⊓ extAutSub U Q := by
    intro g hg a ha
    have hgag : g * a * g⁻¹ ∈ G := G.mul_mem (G.mul_mem hg ha.1) (G.inv_mem hg)
    refine ⟨hgag, mem_extAutSub.mpr ⟨h.stab hgag, ?_⟩⟩
    obtain ⟨has, haQ⟩ := mem_extAutSub.mp ha.2
    have hgφ : resHom U ⟨g, h.stab hg⟩ ∈ autSub G U := mem_autSub.mpr ⟨⟨g, h.stab hg⟩, hg, rfl⟩
    have := hnorm _ hgφ _ haQ
    have e : resHom U ⟨g * a * g⁻¹, h.stab hgag⟩ =
        resHom U ⟨g, h.stab hg⟩ * resHom U ⟨a, has⟩ * (resHom U ⟨g, h.stab hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact this
  have hA2 : IsPGroup 2 ↥(G ⊓ extAutSub U Q) := by
    rintro ⟨a, ha⟩
    have haG : a ∈ G := ha.1
    obtain ⟨has, haQ⟩ := mem_extAutSub.mp ha.2
    obtain ⟨k, hk⟩ := hQ2 ⟨_, haQ⟩
    refine ⟨k, Subtype.ext ?_⟩
    show a ^ 2 ^ k = 1
    have hk' : (resHom U ⟨a, has⟩) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine h.eq_of_resHom_eq (G.pow_mem haG _) G.one_mem ?_
    have e : resHom U ⟨a ^ 2 ^ k, h.stab (G.pow_mem haG _)⟩ = (resHom U ⟨a, has⟩) ^ 2 ^ k := by
      rw [← map_pow]
      rfl
    rw [e, hk']
    exact (map_one (resHom U)).symm
  have hbot := hG _ hAG hAnorm hA2
  rw [← hAQ, hbot]
  unfold autSub
  rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem fittingOf_autSub_le {Y : Subgroup (MulAut V)} {U : Subgroup V} (hY : Y ≤ stabSub U) :
    autSub (fittingOf Y) U ≤ fittingOf (autSub Y U) := by
  have hFs : fittingOf Y ≤ stabSub U := (fittingOf_le Y).trans hY
  refine le_fittingOf_of_normal_nilpotent (autSub_mono (fittingOf_le Y) U) ?_ ?_
  · intro x hx n hn
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
    obtain ⟨f, hf, rfl⟩ := mem_autSub.mp hn
    have hgf : (g : MulAut V) * (f : MulAut V) * (g : MulAut V)⁻¹ ∈ fittingOf Y :=
      conj_mem_fittingOf hg hf
    refine mem_autSub.mpr ⟨g * f * g⁻¹, hgf, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · have hnil : Group.IsNilpotent ↥((fittingOf Y).subgroupOf (stabSub U)) :=
      Group.nilpotent_of_mulEquiv (G := ↥(fittingOf Y))
        (Subgroup.subgroupOfEquivOfLe hFs).symm
        (_h := fittingOf_nilpotent Y)
    exact Group.nilpotent_of_surjective ((resHom U).subgroupMap _)
      (MonoidHom.subgroupMap_surjective _ _)

omit [Finite V] in
theorem isNilpotent_of_injective_range216 {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (Φ : Subgroup B) [Group.IsNilpotent Φ] (hΦ : f.range ≤ Φ) :
    Group.IsNilpotent A := by
  have h2 : Group.IsNilpotent ↥(f.range) :=
    Group.nilpotent_of_mulEquiv (G := ↥(f.range.subgroupOf Φ)) (Subgroup.subgroupOfEquivOfLe hΦ)
  exact Group.nilpotent_of_mulEquiv (G := ↥(f.range)) (MonoidHom.ofInjective hf).symm

theorem SuppData.fittingOf_autSub_le_autSub (h : SuppData G U W) :
    fittingOf (autSub G U) ≤ autSub (fittingOf G) U := by
  let ρ : ↥G →* MulAut U := (resHom U).comp (Subgroup.inclusion h.stab)
  have hρinj : Function.Injective ρ := fun g k hgk =>
    Subtype.ext (h.eq_of_resHom_eq g.2 k.2 hgk)
  have hρmem : ∀ g : ↥G, ρ g ∈ autSub G U := fun g => mem_autSub.mpr ⟨Subgroup.inclusion h.stab g, g.2, rfl⟩
  let Φ := fittingOf (autSub G U)
  let N : Subgroup (MulAut V) := (Φ.comap ρ).map G.subtype
  have hNG : N ≤ G := by
    rintro x ⟨g, -, rfl⟩
    exact g.2
  have hmemN : ∀ g : ↥G, (g : MulAut V) ∈ N ↔ ρ g ∈ Φ := by
    intro g
    constructor
    · rintro ⟨g', hg', hx⟩
      have : g' = g := Subtype.ext hx
      rw [this] at hg'
      exact hg'
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hnorm : ∀ x ∈ G, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    intro x hx n hn
    have h1 := (hmemN ⟨n, hNG hn⟩).mp hn
    have h2 := conj_mem_fittingOf (hρmem ⟨x, hx⟩) h1
    refine (hmemN ⟨x * n * x⁻¹, G.mul_mem (G.mul_mem hx (hNG hn)) (G.inv_mem hx)⟩).mpr ?_
    have e : ρ ⟨x * n * x⁻¹, G.mul_mem (G.mul_mem hx (hNG hn)) (G.inv_mem hx)⟩ =
        ρ ⟨x, hx⟩ * ρ ⟨n, hNG hn⟩ * (ρ ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact h2
  have hnil : Group.IsNilpotent ↥N := by
    let f : ↥N →* MulAut U := ρ.comp (Subgroup.inclusion hNG)
    have hfinj : Function.Injective f := fun a b hab => by
      exact Subgroup.inclusion_injective hNG (hρinj hab)
    have : Group.IsNilpotent ↥Φ := fittingOf_nilpotent _
    refine isNilpotent_of_injective_range216 f hfinj Φ ?_
    rintro _ ⟨n, rfl⟩
    exact (hmemN ⟨n, hNG n.2⟩).mp n.2
  have hle := le_fittingOf_of_normal_nilpotent hNG hnorm hnil
  intro φ hφ
  have hφY : φ ∈ autSub G U := fittingOf_le _ hφ
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφY
  have hgN : (g : MulAut V) ∈ N := by
    have := (hmemN ⟨g, hg⟩).mpr hφ
    exact this
  exact mem_autSub.mpr ⟨g, hle hgN, rfl⟩

theorem SuppData.autSub_fittingOf (h : SuppData G U W) :
    autSub (fittingOf G) U = fittingOf (autSub G U) :=
  le_antisymm (fittingOf_autSub_le h.stab) h.fittingOf_autSub_le_autSub

omit [Finite V] in
theorem SuppData.restrictEquiv_coe (h : SuppData G U W) (g : ↥G) :
    ((h.restrictEquiv g : ↥(autSub G U)) : MulAut U) = resHom U ⟨(g : MulAut V), h.stab g.2⟩ :=
  rfl

omit [Finite V] in
theorem SuppData.index_autSub (h : SuppData G U W) {A : Subgroup (MulAut V)} (hA : A ≤ G) :
    ((autSub A U).subgroupOf (autSub G U)).index = (A.subgroupOf G).index := by
  have hmap : (A.subgroupOf G).map (h.restrictEquiv : ↥G →* ↥(autSub G U)) =
      (autSub A U).subgroupOf (autSub G U) := by
    ext ψ
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      show (h.restrictEquiv g : MulAut U) ∈ autSub A U
      rw [h.restrictEquiv_coe]
      exact mem_autSub.mpr ⟨⟨(g : MulAut V), h.stab g.2⟩, Subgroup.mem_subgroupOf.mp hg, rfl⟩
    · intro hψ
      obtain ⟨a, ha, haψ⟩ := mem_autSub.mp (Subgroup.mem_subgroupOf.mp hψ)
      refine ⟨⟨(a : MulAut V), hA ha⟩, Subgroup.mem_subgroupOf.mpr ha, ?_⟩
      apply Subtype.ext
      show (h.restrictEquiv ⟨(a : MulAut V), hA ha⟩ : MulAut U) = ψ
      rw [h.restrictEquiv_coe]
      exact haψ
  rw [← hmap]
  exact Subgroup.index_map_equiv _ h.restrictEquiv

omit [Finite V] in
theorem isPGroup_of_mem_QhatStar_aux {X A : Subgroup (MulAut V)} [Finite V] (hA : A ∈ QhatStar X) :
    IsPGroup 2 A := by
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  exact hA2.isElemAbelian2.isPGroup

end Restrict2

end CFSG.Quasithin
