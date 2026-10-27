module

public import CFSG.RankThree.PartTwo.Sec21.Item211
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item211Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Intertwine

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']

theorem inducedAutHom_trans_eq {L : Subgroup G} {L₁ : Subgroup G'}
    (Φ : L ⧸ aschbacherSolvableCore 3 L ≃* L₁ ⧸ aschbacherSolvableCore 3 L₁)
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) {a₁ : G'}
    (ha₁ : a₁ ∈ Subgroup.normalizer (L₁ : Set G'))
    (hΦ : ∀ z, Φ (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, ha⟩) z) =
      Sec4.thetaQuotMulAut L₁ (L₁.normalizerMonoidHom ⟨a₁, ha₁⟩) (Φ z))
    {M : Type*} [Group M] (e₁ : L₁ ⧸ aschbacherSolvableCore 3 L₁ ≃* M) :
    KFacts.inducedAutHom L (Φ.trans e₁) ⟨a, ha⟩ = KFacts.inducedAutHom L₁ e₁ ⟨a₁, ha₁⟩ := by
  ext m
  change e₁ (Φ (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, ha⟩) (Φ.symm (e₁.symm m)))) =
    e₁ (Sec4.thetaQuotMulAut L₁ (L₁.normalizerMonoidHom ⟨a₁, ha₁⟩) (e₁.symm m))
  rw [hΦ, MulEquiv.apply_symm_apply]

theorem inducesStdKind_of_intertwine
    {L : Subgroup G}
    {L₁ : Subgroup G'} (Φ : L ⧸ aschbacherSolvableCore 3 L ≃* L₁ ⧸ aschbacherSolvableCore 3 L₁)
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) {a₁ : G'}
    (hΦ : ∀ (ha₁ : a₁ ∈ Subgroup.normalizer (L₁ : Set G')) z,
      Φ (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, ha⟩) z) =
        Sec4.thetaQuotMulAut L₁ (L₁.normalizerMonoidHom ⟨a₁, ha₁⟩) (Φ z))
    {k : KFacts.AutKind} (h : KFacts.InducesStdKind L₁ a₁ k) : KFacts.InducesStdKind L a k := by
  cases h with
  | psl2 K h =>
    obtain ⟨e, hx, he⟩ := h
    exact .psl2 K ⟨Φ.trans e, ha, by rw [inducedAutHom_trans_eq Φ ha hx (hΦ hx)]; exact he⟩
  | psl n K hn h =>
    obtain ⟨e, hx, he⟩ := h
    exact .psl n K hn ⟨Φ.trans e, ha, by rw [inducedAutHom_trans_eq Φ ha hx (hΦ hx)]; exact he⟩
  | sl n K hn h =>
    obtain ⟨e, hx, he⟩ := h
    exact .sl n K hn ⟨Φ.trans e, ha, by rw [inducedAutHom_trans_eq Φ ha hx (hΦ hx)]; exact he⟩
  | psu3 hK hq h =>
    obtain ⟨e, hx, he⟩ := h
    exact .psu3 hK hq ⟨Φ.trans e, ha, by rw [inducedAutHom_trans_eq Φ ha hx (hΦ hx)]; exact he⟩
  | su3 hK hq h =>
    obtain ⟨e, hx, he⟩ := h
    exact .su3 hK hq ⟨Φ.trans e, ha, by rw [inducedAutHom_trans_eq Φ ha hx (hΦ hx)]; exact he⟩
  | psp r K hr h =>
    obtain ⟨e, hx, he⟩ := h
    exact .psp r K hr ⟨Φ.trans e, ha, by rw [inducedAutHom_trans_eq Φ ha hx (hΦ hx)]; exact he⟩
  | psp4even F h =>
    obtain ⟨e, hx, he⟩ := h
    exact .psp4even F ⟨Φ.trans e, ha, by rw [inducedAutHom_trans_eq Φ ha hx (hΦ hx)]; exact he⟩
  | g2 K hK3 hK4 h =>
    obtain ⟨e, hx, he⟩ := h
    exact .g2 K hK3 hK4 ⟨Φ.trans e, ha, by rw [inducedAutHom_trans_eq Φ ha hx (hΦ hx)]; exact he⟩
  | sz a' K ha' hK h =>
    obtain ⟨e, hx, he⟩ := h
    exact .sz a' K ha' hK ⟨Φ.trans e, ha, by rw [inducedAutHom_trans_eq Φ ha hx (hΦ hx)]; exact he⟩
  | triality f hf K hK σ hσ h =>
    obtain ⟨e, hx, he⟩ := h
    exact .triality f hf K hK σ hσ ⟨Φ.trans e, ha,
      by rw [inducedAutHom_trans_eq Φ ha hx (hΦ hx)]; exact he⟩
  | largeRee a' ha' K hK h =>
    obtain ⟨e, hx, he⟩ := h
    exact .largeRee a' ha' K hK ⟨Φ.trans e, ha,
      by rw [inducedAutHom_trans_eq Φ ha hx (hΦ hx)]; exact he⟩

theorem isTypeCOn_of_intertwine {A L : Subgroup G} {A₁ L₁ : Subgroup G'}
    (Φ : L ⧸ aschbacherSolvableCore 3 L ≃* L₁ ⧸ aschbacherSolvableCore 3 L₁)
    (h₁ : ∀ τ ∈ Sec4.autThetaQuot A L, ∃ τ₁ ∈ Sec4.autThetaQuot A₁ L₁, ∀ z, Φ (τ z) = τ₁ (Φ z))
    (h₂ : ∀ τ₁ ∈ Sec4.autThetaQuot A₁ L₁, ∃ τ ∈ Sec4.autThetaQuot A L, ∀ z, Φ (τ z) = τ₁ (Φ z))
    (h : Sec4.IsTypeCOn A₁ L₁) : Sec4.IsTypeCOn A L := by
  obtain ⟨π, p, f, K, _, hK, hq, e, D, hD, hD1, hD2⟩ := h
  refine ⟨π, p, f, K, inferInstance, hK, hq, Φ.trans e, D, hD, fun τ hτ => ?_, fun y hy => ?_⟩
  · obtain ⟨τ₁, hτ₁, hτΦ⟩ := h₁ τ hτ
    obtain ⟨y, hy, hy'⟩ := hD1 τ₁ hτ₁
    refine ⟨y, hy, fun z => ?_⟩
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hτΦ]
    exact hy' (Φ z)
  · obtain ⟨τ₁, hτ₁, hτ₁'⟩ := hD2 y hy
    obtain ⟨τ, hτ, hτΦ⟩ := h₂ τ₁ hτ₁
    refine ⟨τ, hτ, fun z => ?_⟩
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hτΦ]
    exact hτ₁' (Φ z)

omit [Finite G'] in
theorem isTypeCOnBarSL_of_intertwine {A L : Subgroup G} {A₁ L₁ : Subgroup G'}
    (Φ₀ : L ⧸ aschbacherSolvableCore 3 L ≃* L₁)
    (h₁ : ∀ τ ∈ Sec4.autThetaQuot A L, ∃ x ∈ A₁, ∃ hx : x ∈ Subgroup.normalizer (L₁ : Set G'),
      ∀ z, Φ₀ (τ z) = L₁.normalizerMonoidHom ⟨x, hx⟩ (Φ₀ z))
    (h₂ : ∀ x ∈ A₁, ∀ hx : x ∈ Subgroup.normalizer (L₁ : Set G'),
      ∃ τ ∈ Sec4.autThetaQuot A L, ∀ z, Φ₀ (τ z) = L₁.normalizerMonoidHom ⟨x, hx⟩ (Φ₀ z))
    (h : Sec4.IsTypeCOnSL A₁ L₁) : IsTypeCOnBarSL A L := by
  obtain ⟨hE, π, p, f, K, _, hK, hq, e, D, hD, hD1, hD2⟩ := h
  refine ⟨π, p, f, K, inferInstance, hK, hq, Φ₀.trans e, D, hD, fun τ hτ => ?_, fun y hy => ?_⟩
  · obtain ⟨x, hxA, hx, hτΦ⟩ := h₁ τ hτ
    obtain ⟨y, hy, hy'⟩ := hD1 ⟨x, hxA⟩
    refine ⟨y, hy, fun z => ?_⟩
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hτΦ]
    exact hy' (Φ₀ z)
  · obtain ⟨⟨x, hxA⟩, hx'⟩ := hD2 y hy
    obtain ⟨τ, hτ, hτΦ⟩ := h₂ x hxA (hE hxA)
    refine ⟨τ, hτ, fun z => ?_⟩
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hτΦ]
    exact hx' (Φ₀ z)

end Intertwine

section Invariance

variable {X Y : Type} [Group X] [Group Y]

theorem isSLThreePiAt_of_mulEquiv (e : X ≃* Y) {q : ℕ} (h : Sec4.IsSLThreePiAt X q) :
    Sec4.IsSLThreePiAt Y q := by
  obtain ⟨K, _, _, h⟩ := h
  rcases h with ⟨hK, hq, ⟨f⟩⟩ | ⟨hK, hq, ⟨f⟩⟩
  · exact ⟨K, inferInstance, inferInstance, Or.inl ⟨hK, hq, ⟨e.symm.trans f⟩⟩⟩
  · exact ⟨K, inferInstance, inferInstance, Or.inr ⟨hK, hq, ⟨e.symm.trans f⟩⟩⟩

theorem isoLThreePi_of_mulEquiv (e : X ≃* Y) {p f : ℕ} [Fact p.Prime]
    (h : Sec4.IsoLThreePi X p f) : Sec4.IsoLThreePi Y p f := by
  rcases h with ⟨hq, ⟨g⟩⟩ | ⟨hq, ⟨g⟩⟩
  · exact Or.inl ⟨hq, ⟨e.symm.trans g⟩⟩
  · exact Or.inr ⟨hq, ⟨e.symm.trans g⟩⟩

theorem isExtOf_of_mulEquiv (e : X ≃* Y) {S B : Type*} [Group S] [Group B]
    (h : Sec4.IsExtOf X S B) : Sec4.IsExtOf Y S B := by
  obtain ⟨K, hK, ⟨eK⟩, ⟨eQ⟩⟩ := h
  have hK' : (K.map (e : X →* Y)).Normal := hK.map _ e.surjective
  exact ⟨K.map (e : X →* Y), hK',
    ⟨((K.equivMapOfInjective _ e.injective).symm.trans eK)⟩,
    ⟨(QuotientGroup.congr K (K.map (e : X →* Y)) e rfl).symm.trans eQ⟩⟩

end Invariance

end CFSG.RankThree.PartTwo.Sec21.Item211Proof
