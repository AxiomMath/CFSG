module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

private theorem k1566l2a_mem_secondCenter_iff {K : Type} [Group K] (S : Subgroup K) (z : K) :
    z ∈ secondCenterSubgroup S ↔ z ∈ S ∧ ∀ s ∈ S, ∀ t ∈ S,
      (z * s * z⁻¹ * s⁻¹) * t = t * (z * s * z⁻¹ * s⁻¹) := by
  unfold secondCenterSubgroup
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun s hs t ht => ?_⟩
    have h1 := Subgroup.mem_upperCentralSeries_succ_iff.mp hx ⟨s, hs⟩
    rw [Subgroup.upperCentralSeries_one] at h1
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨t, ht⟩)
    simpa [commutatorElement_def] using h2.symm
  · rintro ⟨hz, h⟩
    refine ⟨⟨z, hz⟩, (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).mpr fun y => ?_, rfl⟩
    rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    simpa [commutatorElement_def] using (h y y.2 w w.2).symm

private theorem k1566l2a_mem_center_map_iff {K : Type} [Group K] (S : Subgroup K) (z : K) :
    z ∈ (Subgroup.center ↥S).map S.subtype ↔ z ∈ S ∧ ∀ h ∈ S, h * z = z * h := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.2, fun h hh => ?_⟩
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.1 hu ⟨h, hh⟩)
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (h g g.2), rfl⟩

private theorem k1566l2a_mem_secondCenter_map_iff {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') (S : Subgroup K) (z' : K') :
    z' ∈ secondCenterSubgroup (S.map e.toMonoidHom) ↔
      e.symm z' ∈ secondCenterSubgroup S := by
  rw [k1566l2a_mem_secondCenter_iff, k1566l2a_mem_secondCenter_iff]
  constructor
  · rintro ⟨hz', h⟩
    refine ⟨Subgroup.mem_map_equiv.mp hz', fun s hs t ht => ?_⟩
    apply e.injective
    simpa [map_mul, map_inv] using
      h (e s) (Subgroup.mem_map_of_mem e.toMonoidHom hs)
        (e t) (Subgroup.mem_map_of_mem e.toMonoidHom ht)
  · rintro ⟨hz, h⟩
    refine ⟨Subgroup.mem_map_equiv.mpr hz, fun s' hs' t' ht' => ?_⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hs'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 ht'
    simpa [map_mul, map_inv] using congrArg e (h s hs t ht)

private theorem k1566l2a_mem_center_map_iff_map {K K' : Type} [Group K] [Group K']
    (e : K ≃* K') (S : Subgroup K) (z' : K') :
    z' ∈ (Subgroup.center ↥(S.map e.toMonoidHom)).map (S.map e.toMonoidHom).subtype ↔
      e.symm z' ∈ (Subgroup.center ↥S).map S.subtype := by
  rw [k1566l2a_mem_center_map_iff, k1566l2a_mem_center_map_iff]
  constructor
  · rintro ⟨hz', h⟩
    refine ⟨Subgroup.mem_map_equiv.mp hz', fun s hs => ?_⟩
    apply e.injective
    simpa [map_mul, map_inv] using h (e s) (Subgroup.mem_map_of_mem e.toMonoidHom hs)
  · rintro ⟨hz, h⟩
    refine ⟨?_, fun s' hs' => ?_⟩
    · exact Subgroup.mem_map_equiv.mpr hz
    · obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hs'
      simpa [map_mul, map_inv] using congrArg e (h s hs)

theorem ok69_map_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') {a : K}
    (h : Ok69 a) : Ok69 (e a) := by
  intro R' hR' hnorm
  set R : Subgroup K := R'.comap e.toMonoidHom with hRdef
  have hR : IsPGroup 3 R := by
    rw [hRdef]
    exact hR'.comap_of_injective e.toMonoidHom e.injective
  have hnormR : a ∈ normalizer (R : Set K) := by
    rw [Subgroup.mem_normalizer_iff] at hnorm
    rw [hRdef, Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hnorm (e x)
  obtain ⟨h1, h2⟩ := h R hR hnormR
  have hsup : (R ⊔ zpowers a).map e.toMonoidHom = R' ⊔ zpowers (e a) := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hRdef,
      Subgroup.map_comap_eq_self_of_surjective e.surjective R']
    rfl
  constructor
  · intro z' hz'
    rw [← hsup] at hz'
    rw [k1566l2a_mem_secondCenter_map_iff] at hz'
    simpa [map_mul, map_inv] using congrArg e (h1 (e.symm z') hz')
  · intro hz2
    rw [← hsup] at hz2
    have ha2 : a ∈ secondCenterSubgroup (R ⊔ zpowers a) := by
      simpa using (k1566l2a_mem_secondCenter_map_iff e (R ⊔ zpowers a) (e a)).1 hz2
    have hc := h2 ha2
    rw [← hsup]
    rw [k1566l2a_mem_center_map_iff_map]
    simpa using hc

theorem ok69_conj {K : Type} [Group K] (g : K) {a : K} (h : Ok69 a) : Ok69 (g * a * g⁻¹) := by
  have h' := ok69_map_mulEquiv (MulAut.conj g) h
  simpa [MulAut.conj_apply] using h'

private theorem k1566l2b_isMulCommutative_map {H H' : Type*} [Group H] [Group H']
    (φ : H →* H') {T : Subgroup H} (h : IsMulCommutative ↥T) :
    IsMulCommutative ↥(T.map φ) := by
  refine IsMulCommutative.of_setLike_mul_comm fun u hu v hv => ?_
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu
  obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.1 hv
  rw [← map_mul, ← map_mul]
  exact congrArg (⇑φ) (congrArg Subtype.val (h.is_comm.comm ⟨u₀, hu₀⟩ ⟨v₀, hv₀⟩))

private theorem k1566l2b_isElemAbelian_map {H H' : Type*} [Group H] [Group H'] (p : ℕ)
    (φ : H →* H') {V : Subgroup H} (h : IsElemAbelian p V) :
    IsElemAbelian p (V.map φ) := by
  obtain ⟨hc, hp⟩ := h
  refine ⟨k1566l2b_isMulCommutative_map φ hc, fun z hz => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
  rw [← map_pow, hp x hx, map_one]

private theorem k1566l2b_normal_subgroupOf_map {H H' : Type*} [Group H] [Group H']
    (φ : H →* H') {T Q : Subgroup H} (hTQ : T ≤ Q) (h : (T.subgroupOf Q).Normal) :
    ((T.map φ).subgroupOf (Q.map φ)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hTQ)]
  intro t g ht hg
  obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.1 ht
  obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.1 hg
  have hmem : g₀ * t₀ * g₀⁻¹ ∈ T :=
    (Subgroup.normal_subgroupOf_iff hTQ).1 h t₀ g₀ ht₀ hg₀
  simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem φ hmem

private theorem k1566l2b_pow_three_mem_map {H H' : Type*} [Group H] [Group H']
    (φ : H →* H') (hφ : Function.Injective φ) {T V : Subgroup H}
    (h : ∀ t ∈ T, t ^ 3 = 1 → t ∈ V) :
    ∀ t ∈ T.map φ, t ^ 3 = 1 → t ∈ V.map φ := by
  intro t ht ht3
  obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.1 ht
  have ht0 : t₀ ^ 3 = 1 := hφ (by rw [map_pow, ht3, map_one])
  exact Subgroup.mem_map_of_mem φ (h t₀ ht₀ ht0)

private theorem k1566l2b_transvection_map {H H' : Type*} [Group H] [Group H']
    (φ : H →* H') {V : Subgroup H} {y : H}
    (h : ∀ v ∈ V, (y * v * y⁻¹ * v⁻¹) ∈ V ∧
      y * (y * v * y⁻¹ * v⁻¹) * y⁻¹ = y * v * y⁻¹ * v⁻¹) :
    ∀ v ∈ V.map φ,
      (φ y * v * (φ y)⁻¹ * v⁻¹) ∈ V.map φ ∧
      φ y * (φ y * v * (φ y)⁻¹ * v⁻¹) * (φ y)⁻¹ = φ y * v * (φ y)⁻¹ * v⁻¹ := by
  intro v hv
  obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.1 hv
  obtain ⟨h1, h2⟩ := h v₀ hv₀
  exact ⟨by simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem φ h1,
    by simpa only [map_mul, map_inv] using congrArg (⇑φ) h2⟩

private theorem k1566l2b_nontrivial_action_map {H H' : Type*} [Group H] [Group H']
    (φ : H →* H') (hφ : Function.Injective φ) {V : Subgroup H} {y : H}
    (h : ∃ v ∈ V, y * v * y⁻¹ ≠ v) :
    ∃ v ∈ V.map φ, φ y * v * (φ y)⁻¹ ≠ v := by
  obtain ⟨v, hv, hne⟩ := h
  refine ⟨φ v, Subgroup.mem_map_of_mem φ hv, ?_⟩
  intro heq
  apply hne
  apply hφ
  simpa only [map_mul, map_inv] using heq

private theorem k1566l2b_action_nontrivial_map {H H' : Type*} [Group H] [Group H']
    (φ : H →* H') (hφ : Function.Injective φ) {Q T V : Subgroup H}
    (h : ∀ g ∈ Q, g ∉ T → ∃ v ∈ V, g * v * g⁻¹ ≠ v) :
    ∀ g ∈ Q.map φ, g ∉ T.map φ → ∃ v ∈ V.map φ, g * v * g⁻¹ ≠ v := by
  intro g hg hgT
  obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.1 hg
  have hg₀T : g₀ ∉ T := fun hT => hgT (Subgroup.mem_map_of_mem φ hT)
  obtain ⟨v, hv, hne⟩ := h g₀ hg₀ hg₀T
  refine ⟨φ v, Subgroup.mem_map_of_mem φ hv, ?_⟩
  intro heq
  apply hne
  apply hφ
  simpa only [map_mul, map_inv] using heq

theorem sd3_map_mulEquiv {H H' : Type*} [Group H] [Group H'] [Finite H] [Finite H']
    (e : H ≃* H') {Q T V : Subgroup H} {y : H} {e1 e2 : ℕ} (h : SD3 H Q T V y e1 e2) :
    SD3 H' (Q.map e.toMonoidHom) (T.map e.toMonoidHom) (V.map e.toMonoidHom) (e y) e1 e2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h1.map e.toMonoidHom
  · rw [show (Q.map e.toMonoidHom).index = Q.index from Subgroup.index_map_equiv Q e]
    exact h2
  · exact Subgroup.map_mono h3
  · exact k1566l2b_normal_subgroupOf_map e.toMonoidHom h3 h4
  · exact k1566l2b_isMulCommutative_map e.toMonoidHom h5
  · exact Subgroup.map_mono h6
  · exact k1566l2b_isElemAbelian_map 3 e.toMonoidHom h7
  · exact k1566l2b_pow_three_mem_map e.toMonoidHom e.injective h8
  · rw [h9, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  · exact k1566l2b_transvection_map e.toMonoidHom h10
  · exact k1566l2b_nontrivial_action_map e.toMonoidHom e.injective h11
  · exact k1566l2b_action_nontrivial_map e.toMonoidHom e.injective h12
  · rw [Subgroup.card_map_of_injective e.injective]; exact h13
  · rw [MulEquiv.orderOf_eq e y]; exact h14
  · obtain ⟨f⟩ := h15
    exact ⟨f.trans (Subgroup.equivMapOfInjective T e.toMonoidHom e.injective)⟩

theorem scalarAction_map_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    {T : Subgroup H} {φ : MulAut H} {y : H} {k : ℤ} (h : ScalarAction T φ y k) :
    ScalarAction (T.map e.toMonoidHom) (MulAut.congr e φ) (e y) k := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · simp [MulAut.congr_apply, h1]
  · rintro _ ⟨t, ht, rfl⟩
    simp [MulAut.congr_apply, h2 t ht, map_zpow]

theorem outOrderThree_map_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    {φ : MulAut Y} (h : OutOrderThree Y φ) : OutOrderThree Y' (MulAut.congr e φ) := by
  intro α' hα'1 hα'3
  have hmem : ∀ β : MulAut Y, β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Y ↔
      MulAut.congr e β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Y' := by
    intro β
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e]
    constructor
    · exact fun hb => ⟨β, hb, rfl⟩
    · rintro ⟨β₀, hβ₀, hβ⟩
      have : β₀ = β := (MulAut.congr e).injective hβ
      rwa [this] at hβ₀
  set α : MulAut Y := (MulAut.congr e).symm α' with hα
  have hαα : MulAut.congr e α = α' := (MulAut.congr e).apply_symm_apply α'
  have h1 : α ∉ (MulAut.conj : Y →* MulAut Y).range := fun hh =>
    hα'1 (hαα ▸ (hmem α).1 hh)
  have h3 : α ^ 3 ∈ (MulAut.conj : Y →* MulAut Y).range := by
    refine (hmem (α ^ 3)).2 ?_
    rw [map_pow, hαα]
    exact hα'3
  obtain ⟨g, hg | hg⟩ := h α h1 h3
  · refine ⟨e g, Or.inl ?_⟩
    rw [← hαα, hg, map_mul, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  · refine ⟨e g, Or.inr ?_⟩
    rw [← hαα, hg, map_mul, map_pow, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]

private theorem mem_center_map_iff {H : Type*} [Group H] (R : Subgroup H) (z : H) :
    z ∈ (Subgroup.center ↥R).map R.subtype ↔ z ∈ R ∧ ∀ h ∈ R, h * z = z * h := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.2, fun h hh => ?_⟩
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.1 hu ⟨h, hh⟩)
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (h g g.2), rfl⟩

theorem fusion27_map_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') {z : H}
    (h : Fusion27 z) : Fusion27 (e z) := by
  obtain ⟨R, hcard, hzR, hznc⟩ := h
  refine ⟨R.map e.toMonoidHom, ?_, Subgroup.mem_map_of_mem _ hzR, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hcard
  · intro hc
    obtain ⟨-, hcomm⟩ := (mem_center_map_iff _ _).1 hc
    apply hznc
    refine (mem_center_map_iff _ _).2 ⟨hzR, fun r hr => ?_⟩
    apply e.injective
    simpa using hcomm (e r) (Subgroup.mem_map_of_mem _ hr)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
