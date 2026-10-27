module

public import CFSG.RankThree.PartTwo.Sec13.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G G' : Type*} [Group G] [Group G']

@[expose] noncomputable def centralizerEquiv (φ : G ≃* G') (a : G) :
    Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({φ a} : Set G') :=
  ((Subgroup.centralizer ({a} : Set G)).equivMapOfInjective φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_singleton φ a))

theorem coe_centralizerEquiv_apply (φ : G ≃* G') (a : G) (x : Subgroup.centralizer ({a} : Set G)) :
    ((centralizerEquiv φ a x : Subgroup.centralizer ({φ a} : Set G')) : G') = φ x :=
  rfl

theorem map_centralLine_centralizerEquiv (φ : G ≃* G') (a : G) :
    (centralLine a).map (centralizerEquiv φ a : Subgroup.centralizer ({a} : Set G) →*
      Subgroup.centralizer ({φ a} : Set G')) = centralLine (φ a) := by
  rw [centralLine, centralLine, MonoidHom.map_zpowers]
  rfl

@[expose] noncomputable def centralQuotEquiv (φ : G ≃* G') (a : G) :
    Subgroup.centralizer ({a} : Set G) ⧸ centralLine a ≃*
      Subgroup.centralizer ({φ a} : Set G') ⧸ centralLine (φ a) :=
  QuotientGroup.congr _ _ (centralizerEquiv φ a) (map_centralLine_centralizerEquiv φ a)

theorem map_centralQuotEquiv (φ : G ≃* G') (A : Subgroup G) (a : G) :
    ((A.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
        (QuotientGroup.mk' (centralLine a))).map (centralQuotEquiv φ a).toMonoidHom =
      ((A.map φ.toMonoidHom).subgroupOf (Subgroup.centralizer ({φ a} : Set G'))).map
        (QuotientGroup.mk' (centralLine (φ a))) := by
  ext q
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨centralizerEquiv φ a x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, coe_centralizerEquiv_apply]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hx)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨QuotientGroup.mk' _ ((centralizerEquiv φ a).symm y),
      ⟨(centralizerEquiv φ a).symm y, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_subgroupOf.mp hy
      have hz' : ((centralizerEquiv φ a).symm y : G) = z := by
        apply φ.injective
        rw [← coe_centralizerEquiv_apply, MulEquiv.apply_symm_apply]
        exact hzy.symm
      rw [hz']
      exact hz
    · change centralQuotEquiv φ a ((centralizerEquiv φ a).symm y : _ ⧸ centralLine a) = _
      rw [centralQuotEquiv, QuotientGroup.congr_mk, MulEquiv.apply_symm_apply]
      rfl

theorem starConditionAt_map_iff [Finite G] (φ : G ≃* G') (A : Subgroup G) (a : G) :
    StarConditionAt (A.map φ.toMonoidHom) (φ a) ↔ StarConditionAt A a := by
  have : Finite G' := Finite.of_equiv G φ.toEquiv
  unfold StarConditionAt
  rw [← map_centralQuotEquiv φ A a, ← thetaAlpha_map_equiv Nat.prime_three,
    ← aschbacherSolvableCore_map_mulEquiv Nat.prime_three (centralQuotEquiv φ a),
    Subgroup.map_le_map_iff_of_injective (f := (centralQuotEquiv φ a).toMonoidHom)
      (centralQuotEquiv φ a).injective]

theorem map_symm_map (φ : G ≃* G') (K : Subgroup G) :
    (K.map φ.toMonoidHom).map φ.symm.toMonoidHom = K := by
  rw [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G from
    MonoidHom.ext φ.symm_apply_apply, Subgroup.map_id]

theorem map_mem_omegaA [Finite G] (φ : G ≃* G') {A F : Subgroup G} (hF : F ∈ omegaA A) :
    F.map φ.toMonoidHom ∈ omegaA (A.map φ.toMonoidHom) := by
  obtain ⟨hFA, hF3, a, rfl, ha⟩ := hF
  refine ⟨Subgroup.map_mono hFA, ?_, φ a, MonoidHom.map_zpowers _ _, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.injective, hF3]
  · rwa [starConditionAt_map_iff]

theorem mem_omegaA_map_iff [Finite G] (φ : G ≃* G') {A F : Subgroup G} :
    F.map φ.toMonoidHom ∈ omegaA (A.map φ.toMonoidHom) ↔ F ∈ omegaA A := by
  refine ⟨fun h => ?_, map_mem_omegaA φ⟩
  have : Finite G' := Finite.of_equiv G φ.toEquiv
  have h' := map_mem_omegaA φ.symm h
  rwa [map_symm_map, map_symm_map] at h'

theorem mem_omegaA_map_conj_iff [Finite G] (g : G) {A F : Subgroup G} :
    F.map (MulAut.conj g).toMonoidHom ∈ omegaA (A.map (MulAut.conj g).toMonoidHom) ↔
      F ∈ omegaA A :=
  mem_omegaA_map_iff (MulAut.conj g)

theorem map_conj_eq_of_mem_normalizer {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : A.map (MulAut.conj g).toMonoidHom = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa [mul_assoc] using this

theorem map_conj_mem_omegaA_iff [Finite G] {A F : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    F.map (MulAut.conj g).toMonoidHom ∈ omegaA A ↔ F ∈ omegaA A := by
  conv_lhs => rw [← map_conj_eq_of_mem_normalizer hg]
  exact mem_omegaA_map_conj_iff g

theorem image_sectionCentralizer (φ : G ≃* G') (A X Y : Subgroup G) :
    φ '' Late.sectionCentralizer A X Y =
      Late.sectionCentralizer (A.map φ.toMonoidHom) (X.map φ.toMonoidHom)
        (Y.map φ.toMonoidHom) := by
  ext b
  constructor
  · rintro ⟨a, ⟨ha, hX⟩, rfl⟩
    refine ⟨⟨a, ha, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, hX x hx, by simp [map_mul, map_inv]⟩
  · rintro ⟨⟨a, ha, rfl⟩, hX⟩
    refine ⟨a, ⟨ha, fun x hx => ?_⟩, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hX (φ x) ⟨x, hx, rfl⟩
    have : y = a * x * a⁻¹ * x⁻¹ := φ.injective (by simpa [map_mul, map_inv] using hxy)
    exact this ▸ hy

@[expose] noncomputable def thetaQuotEquiv [Finite G] (φ : G ≃* G') (L : Subgroup G) :
    L ⧸ aschbacherSolvableCore 3 L ≃*
      (L.map φ.toMonoidHom) ⧸ aschbacherSolvableCore 3 (L.map φ.toMonoidHom) :=
  QuotientGroup.congr _ _ (L.equivMapOfInjective φ.toMonoidHom φ.injective)
    (aschbacherSolvableCore_map_mulEquiv Nat.prime_three _)

theorem thetaQuotEquiv_mk [Finite G] (φ : G ≃* G') (L : Subgroup G) (x : L) :
    thetaQuotEquiv φ L (x : L ⧸ aschbacherSolvableCore 3 L) =
      ((L.equivMapOfInjective φ.toMonoidHom φ.injective x : L.map φ.toMonoidHom) :
        (L.map φ.toMonoidHom) ⧸ aschbacherSolvableCore 3 (L.map φ.toMonoidHom)) :=
  rfl

theorem map_mem_normalizer_iff (φ : G ≃* G') {L : Subgroup G} {h : G} :
    φ h ∈ Subgroup.normalizer ((L.map φ.toMonoidHom : Subgroup G') : Set G') ↔
      h ∈ Subgroup.normalizer (L : Set G) := by
  rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem congr_thetaQuotMulAut [Finite G] [Finite G'] (φ : G ≃* G') (L : Subgroup G) {h : G}
    (hN : h ∈ Subgroup.normalizer (L : Set G))
    (hN' : φ h ∈ Subgroup.normalizer ((L.map φ.toMonoidHom : Subgroup G') : Set G')) :
    MulAut.congr (thetaQuotEquiv φ L) (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨h, hN⟩)) =
      Sec4.thetaQuotMulAut (L.map φ.toMonoidHom)
        ((L.map φ.toMonoidHom).normalizerMonoidHom ⟨φ h, hN'⟩) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    obtain ⟨x, rfl⟩ := (L.equivMapOfInjective φ.toMonoidHom φ.injective).surjective y
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, ← thetaQuotEquiv_mk,
      MulEquiv.symm_apply_apply, Sec4.thetaQuotMulAut_mk, thetaQuotEquiv_mk, thetaQuotEquiv_mk,
      Sec4.thetaQuotMulAut_mk]
    congr 1
    apply Subtype.ext
    change φ ((L.normalizerMonoidHom ⟨h, hN⟩ x : L) : G) = φ h * φ (x : G) * (φ h)⁻¹
    rw [Sec4.normalizerMonoidHom_apply_coe, map_mul, map_mul, map_inv]

theorem map_autThetaQuot [Finite G] [Finite G'] (φ : G ≃* G') (H L : Subgroup G) :
    (Sec4.autThetaQuot H L).map (MulAut.congr (thetaQuotEquiv φ L)).toMonoidHom =
      Sec4.autThetaQuot (H.map φ.toMonoidHom) (L.map φ.toMonoidHom) := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨h, hN, hH, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    have hN' := (map_mem_normalizer_iff φ).mpr hN
    exact Sec4.mem_autThetaQuot_iff.mpr ⟨φ h, hN', Subgroup.mem_map_of_mem _ hH,
      (congr_thetaQuotMulAut φ L hN hN').symm⟩
  · intro hσ
    obtain ⟨h', hN', ⟨h, hH, rfl⟩, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
    have hN := (map_mem_normalizer_iff φ).mp hN'
    exact ⟨_, Sec4.mem_autThetaQuot_iff.mpr ⟨h, hN, hH, rfl⟩, congr_thetaQuotMulAut φ L hN hN'⟩

theorem thetaAlpha_subgroupOf_map_ne_bot_iff {M M' : Type*} [Group M] [Group M'] [Finite M]
    (Ψ : M ≃* M') (X Y : Subgroup M) :
    thetaAlpha 3 ((X.map Ψ.toMonoidHom).subgroupOf (Y.map Ψ.toMonoidHom)) ≠ ⊥ ↔
      thetaAlpha 3 (X.subgroupOf Y) ≠ ⊥ := by
  have : Finite M' := Finite.of_equiv M Ψ.toEquiv
  let ρ := Y.equivMapOfInjective Ψ.toMonoidHom Ψ.injective
  have hρ : (X.subgroupOf Y).map ρ.toMonoidHom =
      (X.map Ψ.toMonoidHom).subgroupOf (Y.map Ψ.toMonoidHom) := by
    ext z
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
    · intro hz
      obtain ⟨y, rfl⟩ := ρ.surjective z
      refine ⟨y, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hz
      have : x = y := Ψ.injective hxy
      exact this ▸ hx
  rw [← hρ, ← thetaAlpha_map_equiv Nat.prime_three, Ne, Ne,
    Subgroup.map_eq_bot_iff_of_injective _ ρ.injective]

theorem map_mem_lA [Finite G] [Finite G'] (φ : G ≃* G') {A L : Subgroup G} {c : G}
    (hL : L ∈ lA A c) : L.map φ.toMonoidHom ∈ lA (A.map φ.toMonoidHom) (φ c) := by
  obtain ⟨hLc, hAN, hC, hα⟩ := hL
  refine ⟨map_mem_thetaComponentsAt φ hLc, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hAN
  · have hθ := map_inSubgroup_aschbacherSolvableCore φ L
    simp only [inSubgroup] at hθ
    rw [← hθ, ← image_sectionCentralizer, hC]
    ext y
    simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (map_zpow φ c k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨c ^ k, ⟨k, rfl⟩, map_zpow φ c k⟩
  · have hN : (Subgroup.normalizer (Subgroup.zpowers c : Set G)).map φ.toMonoidHom =
        Subgroup.normalizer (Subgroup.zpowers (φ c) : Set G') := by
      rw [Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers]
      rfl
    rw [← map_autThetaQuot, ← hN, ← map_autThetaQuot]
    exact (thetaAlpha_subgroupOf_map_ne_bot_iff _ _ _).mpr hα

theorem mem_lA_map_iff [Finite G] [Finite G'] (φ : G ≃* G') {A L : Subgroup G} {c : G} :
    L.map φ.toMonoidHom ∈ lA (A.map φ.toMonoidHom) (φ c) ↔ L ∈ lA A c := by
  refine ⟨fun h => ?_, map_mem_lA φ⟩
  have h' := map_mem_lA φ.symm h
  rwa [map_symm_map, map_symm_map, MulEquiv.symm_apply_apply] at h'

theorem mem_lA_map_conj_iff [Finite G] (g : G) {A L : Subgroup G} {c : G} :
    L.map (MulAut.conj g).toMonoidHom ∈ lA (A.map (MulAut.conj g).toMonoidHom) (g * c * g⁻¹) ↔
      L ∈ lA A c :=
  mem_lA_map_iff (MulAut.conj g)

theorem map_conj_mem_lA_iff [Finite G] {A L : Subgroup G} {c g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    L.map (MulAut.conj g).toMonoidHom ∈ lA A (g * c * g⁻¹) ↔ L ∈ lA A c := by
  conv_lhs => rw [← map_conj_eq_of_mem_normalizer hg]
  exact mem_lA_map_conj_iff g

theorem map_mem_partTwoT [Finite G] [Finite G'] (φ : G ≃* G') {E : Subgroup G}
    (hE : E ∈ partTwoT G) : E.map φ.toMonoidHom ∈ partTwoT G' := by
  obtain ⟨hE, H, ⟨P, hP, hP2, rfl⟩, hle⟩ := hE
  have hE' := map_mem_partTwoE φ hE
  refine ⟨hE', (Subgroup.normalizer (P : Set G)).map φ.toMonoidHom,
    ⟨P.map φ.toMonoidHom, ?_, hP2.map _, Subgroup.map_equiv_normalizer_eq P φ⟩, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective P φ.injective]
  · rw [aschCore_eq_gamma_of_mem_partTwoE hE', ← map_gamma,
      ← aschCore_eq_gamma_of_mem_partTwoE hE]
    exact Subgroup.map_mono hle

theorem map_mem_partTwoT_iff [Finite G] [Finite G'] (φ : G ≃* G') {E : Subgroup G} :
    E.map φ.toMonoidHom ∈ partTwoT G' ↔ E ∈ partTwoT G := by
  refine ⟨fun h => ?_, map_mem_partTwoT φ⟩
  have h' := map_mem_partTwoT φ.symm h
  rwa [map_symm_map] at h'

theorem map_mem_partTwoE_iff (φ : G ≃* G') {E : Subgroup G} :
    E.map φ.toMonoidHom ∈ partTwoE G' ↔ E ∈ partTwoE G := by
  refine ⟨fun h => ?_, map_mem_partTwoE φ⟩
  have h' := map_mem_partTwoE φ.symm h
  rwa [map_symm_map] at h'

theorem HypS.of_map [Finite G] [Finite G'] (φ : G ≃* G') {A : Subgroup G}
    (h : HypS (A.map φ.toMonoidHom)) : HypS A := by
  obtain ⟨hE, hT, hS⟩ := h
  refine ⟨(map_mem_partTwoE_iff φ).mp hE, fun hA => hT ((map_mem_partTwoT_iff φ).mpr hA),
    fun a ha K hK haK => ?_⟩
  rw [← mem_omegaA_map_iff φ, MonoidHom.map_zpowers] at ha
  exact hS (φ a) ha _ ((mem_lA_map_iff φ).mpr hK) (Subgroup.mem_map_of_mem _ haK)

theorem hypS_map_iff [Finite G] [Finite G'] (φ : G ≃* G') {A : Subgroup G} :
    HypS (A.map φ.toMonoidHom) ↔ HypS A := by
  refine ⟨HypS.of_map φ, fun h => HypS.of_map φ.symm ?_⟩
  rwa [map_symm_map]

theorem hypS_map_conj_iff [Finite G] (g : G) {A : Subgroup G} :
    HypS (A.map (MulAut.conj g).toMonoidHom) ↔ HypS A :=
  hypS_map_iff (MulAut.conj g)

theorem collectionIn_partTwoT_centralizer_map_eq_empty_iff [Finite G] [Finite G'] (φ : G ≃* G')
    (a : G) :
    collectionIn (partTwoT G') (Subgroup.centralizer ({φ a} : Set G')) = ∅ ↔
      collectionIn (partTwoT G) (Subgroup.centralizer ({a} : Set G)) = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem]
  constructor
  · rintro h E ⟨hE, hEC⟩
    refine h (E.map φ.toMonoidHom) ⟨map_mem_partTwoT φ hE, ?_⟩
    rw [← map_centralizer_singleton]
    exact Subgroup.map_mono hEC
  · rintro h E ⟨hE, hEC⟩
    refine h (E.map φ.symm.toMonoidHom) ⟨map_mem_partTwoT φ.symm hE, ?_⟩
    have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hEC
    rwa [map_centralizer_singleton, MulEquiv.symm_apply_apply] at this

theorem HypT.of_map [Finite G] [Finite G'] (φ : G ≃* G') {A : Subgroup G}
    (h : HypT (A.map φ.toMonoidHom)) : HypT A := by
  obtain ⟨hE, hT, hC⟩ := h
  refine ⟨(map_mem_partTwoE_iff φ).mp hE, fun hA => hT ((map_mem_partTwoT_iff φ).mpr hA),
    fun a ha => ?_⟩
  rw [← mem_omegaA_map_iff φ, MonoidHom.map_zpowers] at ha
  exact (collectionIn_partTwoT_centralizer_map_eq_empty_iff φ a).mp (hC (φ a) ha)

theorem hypT_map_iff [Finite G] [Finite G'] (φ : G ≃* G') {A : Subgroup G} :
    HypT (A.map φ.toMonoidHom) ↔ HypT A := by
  refine ⟨HypT.of_map φ, fun h => HypT.of_map φ.symm ?_⟩
  rwa [map_symm_map]

theorem hypT_map_conj_iff [Finite G] (g : G) {A : Subgroup G} :
    HypT (A.map (MulAut.conj g).toMonoidHom) ↔ HypT A :=
  hypT_map_iff (MulAut.conj g)

end CFSG.RankThree.PartTwo.Sec13
