module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

variable {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']

noncomputable abbrev thetaQuotMapHom (φ : G →* G') (L : Subgroup G) :
    L →* L.map φ ⧸ aschbacherSolvableCore 3 (L.map φ) :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 (L.map φ))).comp (φ.subgroupMap L)

omit [Finite G] [Finite G'] in
theorem thetaQuotMapHom_surjective (φ : G →* G') (L : Subgroup G) :
    Function.Surjective (thetaQuotMapHom φ L) :=
  (QuotientGroup.mk'_surjective _).comp (φ.subgroupMap_surjective L)

omit [Finite G] [Finite G'] in
theorem ker_thetaQuotMapHom (φ : G →* G') (L : Subgroup G)
    (h : ∀ l : L, φ.subgroupMap L l ∈ aschbacherSolvableCore 3 (L.map φ) ↔
      l ∈ aschbacherSolvableCore 3 L) :
    (thetaQuotMapHom φ L).ker = aschbacherSolvableCore 3 L := by
  ext l
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, h]

noncomputable def thetaQuotEquivOfMap (φ : G →* G') (L : Subgroup G)
    (h : ∀ l : L, φ.subgroupMap L l ∈ aschbacherSolvableCore 3 (L.map φ) ↔
      l ∈ aschbacherSolvableCore 3 L) :
    L ⧸ aschbacherSolvableCore 3 L ≃* L.map φ ⧸ aschbacherSolvableCore 3 (L.map φ) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_thetaQuotMapHom φ L h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (thetaQuotMapHom_surjective φ L))

omit [Finite G] [Finite G'] in
theorem thetaQuotEquivOfMap_mk (φ : G →* G') (L : Subgroup G)
    (h : ∀ l : L, φ.subgroupMap L l ∈ aschbacherSolvableCore 3 (L.map φ) ↔
      l ∈ aschbacherSolvableCore 3 L) (l : L) :
    thetaQuotEquivOfMap φ L h (l : L ⧸ aschbacherSolvableCore 3 L) =
      ((φ.subgroupMap L l : L.map φ) : L.map φ ⧸ aschbacherSolvableCore 3 (L.map φ)) := by
  show QuotientGroup.quotientKerEquivOfSurjective _ (thetaQuotMapHom_surjective φ L)
    (QuotientGroup.quotientMulEquivOfEq (ker_thetaQuotMapHom φ L h).symm
      (l : L ⧸ aschbacherSolvableCore 3 L)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

omit [Finite G'] in
theorem thetaQuotMap_iff_of_injective (φ : G →* G') (hφ : Function.Injective φ)
    (L : Subgroup G) (l : L) :
    φ.subgroupMap L l ∈ aschbacherSolvableCore 3 (L.map φ) ↔ l ∈ aschbacherSolvableCore 3 L := by
  set e := L.equivMapOfInjective φ hφ
  have hmap := aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  have he : φ.subgroupMap L l = e l := rfl
  rw [he, ← hmap]
  constructor
  · rintro ⟨l', hl', hl'e⟩
    have : l' = l := e.injective hl'e
    rwa [← this]
  · intro hl
    exact ⟨l, hl, rfl⟩

omit [Finite G] [Finite G'] in
theorem map_mem_normalizer_map (φ : G →* G') {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    φ x ∈ Subgroup.normalizer ((L.map φ : Subgroup G') : Set G') :=
  Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ hx)

theorem inducedAutHom_map (φ : G →* G') (L : Subgroup G)
    (h : ∀ l : L, φ.subgroupMap L l ∈ aschbacherSolvableCore 3 (L.map φ) ↔
      l ∈ aschbacherSolvableCore 3 L)
    {M : Type*} [Group M] (e : L.map φ ⧸ aschbacherSolvableCore 3 (L.map φ) ≃* M) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hx' : φ x ∈ Subgroup.normalizer ((L.map φ : Subgroup G') : Set G')) :
    inducedAutHom (L.map φ) e ⟨φ x, hx'⟩ =
      inducedAutHom L ((thetaQuotEquivOfMap φ L h).trans e) ⟨x, hx⟩ := by
  ext m
  obtain ⟨q, rfl⟩ : ∃ q, e (thetaQuotEquivOfMap φ L h q) = m :=
    ⟨(thetaQuotEquivOfMap φ L h).symm (e.symm m), by simp⟩
  change e (thetaQuotMulAut _ (compAction _ ⟨φ x, hx'⟩)
      (e.symm (e (thetaQuotEquivOfMap φ L h q)))) =
    e (thetaQuotEquivOfMap φ L h (thetaQuotMulAut _ (compAction L ⟨x, hx⟩)
      (((thetaQuotEquivOfMap φ L h).trans e).symm (e (thetaQuotEquivOfMap φ L h q)))))
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply,
    MulEquiv.symm_apply_apply]
  congr 1
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [thetaQuotEquivOfMap_mk, thetaQuotMulAut_mk, thetaQuotMulAut_mk,
      thetaQuotEquivOfMap_mk]
    congr 1
    apply Subtype.ext
    change φ x * φ (l : G) * (φ x)⁻¹ = φ (x * (l : G) * x⁻¹)
    rw [map_mul, map_mul, map_inv]

theorem inducedAutHom_eq_of_conj_eq {L : Subgroup G} {M : Type*} [Group M]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) {x y : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hxy : ∀ l ∈ L, x * l * x⁻¹ = y * l * y⁻¹) :
    inducedAutHom L e ⟨x, hx⟩ = inducedAutHom L e ⟨y, hy⟩ := by
  have hc : compAction L ⟨x, hx⟩ = compAction L ⟨y, hy⟩ :=
    MulEquiv.ext fun l => Subtype.ext (by
      simpa [compAction, normalizerMonoidHom_apply_coe] using hxy l l.2)
  rw [inducedAutHom_apply, inducedAutHom_apply, hc]

section Transport

variable (φ : G →* G') (L : Subgroup G)
  (h : ∀ l : L, φ.subgroupMap L l ∈ aschbacherSolvableCore 3 (L.map φ) ↔
    l ∈ aschbacherSolvableCore 3 L)

include h in
theorem inducedAutHom_map_symm {M : Type*} [Group M] (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hx' : φ x ∈ Subgroup.normalizer ((L.map φ : Subgroup G') : Set G')) :
    inducedAutHom (L.map φ) ((thetaQuotEquivOfMap φ L h).symm.trans e) ⟨φ x, hx'⟩ =
      inducedAutHom L e ⟨x, hx⟩ := by
  have he : (thetaQuotEquivOfMap φ L h).trans ((thetaQuotEquivOfMap φ L h).symm.trans e) = e :=
    MulEquiv.ext fun q => by simp
  rw [inducedAutHom_map φ L h _ hx hx', he]

include h in
theorem InducesKind.map {M : Type*} [Group M] {P : PinnedAut M}
    {e : L ⧸ aschbacherSolvableCore 3 L ≃* M} {x : G} {k : AutKind}
    (hk : InducesKind L P e x k) :
    InducesKind (L.map φ) P ((thetaQuotEquivOfMap φ L h).symm.trans e) (φ x) k := by
  obtain ⟨hx, hP⟩ := hk
  exact ⟨map_mem_normalizer_map φ hx, by rwa [inducedAutHom_map_symm φ L h e hx]⟩

include h in
theorem InducesKind.of_map {M : Type*} [Group M] {P : PinnedAut M}
    {e : L.map φ ⧸ aschbacherSolvableCore 3 (L.map φ) ≃* M} {x : G} {k : AutKind}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hk : InducesKind (L.map φ) P e (φ x) k) :
    InducesKind L P ((thetaQuotEquivOfMap φ L h).trans e) x k := by
  obtain ⟨hx', hP⟩ := hk
  exact ⟨hx, by rwa [← inducedAutHom_map φ L h e hx hx']⟩

include h in
theorem InducesStdKind.map {x : G} {k : AutKind} (hk : InducesStdKind L x k) :
    InducesStdKind (L.map φ) (φ x) k := by
  cases hk with
  | psl2 K hK => obtain ⟨e, he⟩ := hK; exact .psl2 K ⟨_, he.map φ L h⟩
  | psl n K hn hK => obtain ⟨e, he⟩ := hK; exact .psl n K hn ⟨_, he.map φ L h⟩
  | sl n K hn hK =>
    obtain ⟨e, hx, hR⟩ := hK
    exact .sl n K hn ⟨_, map_mem_normalizer_map φ hx, by rwa [inducedAutHom_map_symm φ L h e hx]⟩
  | psu3 hK hq hK' => obtain ⟨e, he⟩ := hK'; exact .psu3 hK hq ⟨_, he.map φ L h⟩
  | su3 hK hq hK' =>
    obtain ⟨e, hx, hR⟩ := hK'
    exact .su3 hK hq ⟨_, map_mem_normalizer_map φ hx, by rwa [inducedAutHom_map_symm φ L h e hx]⟩
  | psp r K hr hK => obtain ⟨e, he⟩ := hK; exact .psp r K hr ⟨_, he.map φ L h⟩
  | psp4even F hK => obtain ⟨e, he⟩ := hK; exact .psp4even F ⟨_, he.map φ L h⟩
  | g2 K hK3 hK4 hK => obtain ⟨e, he⟩ := hK; exact .g2 K hK3 hK4 ⟨_, he.map φ L h⟩
  | sz a K ha hK hK' => obtain ⟨e, he⟩ := hK'; exact .sz a K ha hK ⟨_, he.map φ L h⟩
  | triality f hf K hK σ hσ hK' =>
    obtain ⟨e, hx, hR⟩ := hK'
    exact .triality f hf K hK σ hσ
      ⟨_, map_mem_normalizer_map φ hx, by rwa [inducedAutHom_map_symm φ L h e hx]⟩
  | largeRee a ha K hK hK' => obtain ⟨e, he⟩ := hK'; exact .largeRee a ha K hK ⟨_, he.map φ L h⟩

include h in
theorem InducesStdKind.of_map {x : G} {k : AutKind} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hk : InducesStdKind (L.map φ) (φ x) k) : InducesStdKind L x k := by
  cases hk with
  | psl2 K hK => obtain ⟨e, he⟩ := hK; exact .psl2 K ⟨_, he.of_map φ L h hx⟩
  | psl n K hn hK => obtain ⟨e, he⟩ := hK; exact .psl n K hn ⟨_, he.of_map φ L h hx⟩
  | sl n K hn hK =>
    obtain ⟨e, hx', hR⟩ := hK
    exact .sl n K hn ⟨_, hx, by rwa [← inducedAutHom_map φ L h e hx hx']⟩
  | psu3 hK hq hK' => obtain ⟨e, he⟩ := hK'; exact .psu3 hK hq ⟨_, he.of_map φ L h hx⟩
  | su3 hK hq hK' =>
    obtain ⟨e, hx', hR⟩ := hK'
    exact .su3 hK hq ⟨_, hx, by rwa [← inducedAutHom_map φ L h e hx hx']⟩
  | psp r K hr hK => obtain ⟨e, he⟩ := hK; exact .psp r K hr ⟨_, he.of_map φ L h hx⟩
  | psp4even F hK => obtain ⟨e, he⟩ := hK; exact .psp4even F ⟨_, he.of_map φ L h hx⟩
  | g2 K hK3 hK4 hK => obtain ⟨e, he⟩ := hK; exact .g2 K hK3 hK4 ⟨_, he.of_map φ L h hx⟩
  | sz a K ha hK hK' => obtain ⟨e, he⟩ := hK'; exact .sz a K ha hK ⟨_, he.of_map φ L h hx⟩
  | triality f hf K hK σ hσ hK' =>
    obtain ⟨e, hx', hR⟩ := hK'
    exact .triality f hf K hK σ hσ ⟨_, hx, by rwa [← inducedAutHom_map φ L h e hx hx']⟩
  | largeRee a ha K hK hK' =>
    obtain ⟨e, he⟩ := hK'; exact .largeRee a ha K hK ⟨_, he.of_map φ L h hx⟩

end Transport

theorem InducesKind.of_conj_eq {L : Subgroup G} {M : Type*} [Group M] {P : PinnedAut M}
    {e : L ⧸ aschbacherSolvableCore 3 L ≃* M} {x y : G} {k : AutKind}
    (hk : InducesKind L P e x k) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hxy : ∀ l ∈ L, x * l * x⁻¹ = y * l * y⁻¹) : InducesKind L P e y k := by
  obtain ⟨hx, hP⟩ := hk
  exact ⟨hy, by rwa [← inducedAutHom_eq_of_conj_eq e hx hy hxy]⟩

theorem InducesStdKind.of_conj_eq {L : Subgroup G} {x y : G} {k : AutKind}
    (hk : InducesStdKind L x k) (hy : y ∈ Subgroup.normalizer (L : Set G))
    (hxy : ∀ l ∈ L, x * l * x⁻¹ = y * l * y⁻¹) : InducesStdKind L y k := by
  cases hk with
  | psl2 K hK => obtain ⟨e, he⟩ := hK; exact .psl2 K ⟨e, he.of_conj_eq hy hxy⟩
  | psl n K hn hK => obtain ⟨e, he⟩ := hK; exact .psl n K hn ⟨e, he.of_conj_eq hy hxy⟩
  | sl n K hn hK =>
    obtain ⟨e, hx, hR⟩ := hK
    exact .sl n K hn ⟨e, hy, by rwa [← inducedAutHom_eq_of_conj_eq e hx hy hxy]⟩
  | psu3 hK hq hK' => obtain ⟨e, he⟩ := hK'; exact .psu3 hK hq ⟨e, he.of_conj_eq hy hxy⟩
  | su3 hK hq hK' =>
    obtain ⟨e, hx, hR⟩ := hK'
    exact .su3 hK hq ⟨e, hy, by rwa [← inducedAutHom_eq_of_conj_eq e hx hy hxy]⟩
  | psp r K hr hK => obtain ⟨e, he⟩ := hK; exact .psp r K hr ⟨e, he.of_conj_eq hy hxy⟩
  | psp4even F hK => obtain ⟨e, he⟩ := hK; exact .psp4even F ⟨e, he.of_conj_eq hy hxy⟩
  | g2 K hK3 hK4 hK => obtain ⟨e, he⟩ := hK; exact .g2 K hK3 hK4 ⟨e, he.of_conj_eq hy hxy⟩
  | sz a K ha hK hK' => obtain ⟨e, he⟩ := hK'; exact .sz a K ha hK ⟨e, he.of_conj_eq hy hxy⟩
  | triality f hf K hK σ hσ hK' =>
    obtain ⟨e, hx, hR⟩ := hK'
    exact .triality f hf K hK σ hσ ⟨e, hy, by rwa [← inducedAutHom_eq_of_conj_eq e hx hy hxy]⟩
  | largeRee a ha K hK hK' =>
    obtain ⟨e, he⟩ := hK'; exact .largeRee a ha K hK ⟨e, he.of_conj_eq hy hxy⟩

end CFSG.RankThree.PartTwo.KFacts
