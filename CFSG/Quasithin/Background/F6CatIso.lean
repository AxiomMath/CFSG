module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace F6

noncomputable def quotientPCoreCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ Open.pCore 2 X ≃* Y ⧸ Open.pCore 2 Y :=
  QuotientGroup.congr _ _ e (map_pCore_mulEquiv 2 e)

noncomputable def pCoreCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    ↥(Open.pCore 2 X) ≃* ↥(Open.pCore 2 Y) :=
  ((Open.pCore 2 X).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_pCore_mulEquiv 2 e))

noncomputable def pCoreOfEquiv {D : Type*} [Group D] (H : Subgroup D) :
    ↥(Open.pCore 2 ↥H) ≃* ↥(pCoreOf 2 H) :=
  (Open.pCore 2 ↥H).equivMapOfInjective H.subtype H.subtype_injective

noncomputable def pCoreOfCongr {D E : Type*} [Group D] [Group E] {H : Subgroup D}
    {K : Subgroup E} (e : ↥H ≃* ↥K) : ↥(pCoreOf 2 H) ≃* ↥(pCoreOf 2 K) :=
  ((pCoreOfEquiv H).symm.trans (pCoreCongr e)).trans (pCoreOfEquiv K)

theorem quotientPCoreIsL22_of_mulEquiv {D E : Type*} [Group D] [Group E] {H : Subgroup D}
    {K : Subgroup E} (e : ↥H ≃* ↥K) (h : QuotientPCoreIsL22 H) : QuotientPCoreIsL22 K :=
  ⟨(quotientPCoreCongr e).symm.trans h.some⟩

noncomputable def kerCompMulEquiv {X Y A : Type*} [Group X] [Group Y] [Group A] (e : X ≃* Y)
    (φ : Y →* A) : ↥(φ.comp e.toMonoidHom).ker ≃* ↥φ.ker := by
  have hker : (φ.comp e.toMonoidHom).ker = φ.ker.comap e.toMonoidHom :=
    Subgroup.ext fun _ => Iff.rfl
  exact (MulEquiv.subgroupCongr hker).trans
    (((φ.ker.comap e.toMonoidHom).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective _)))

theorem isExtensionOf_of_mulEquiv {X Y A N : Type*} [Group X] [Group Y] [Group A] [Group N]
    (e : X ≃* Y) (h : IsExtensionOf Y A N) : IsExtensionOf X A N := by
  obtain ⟨φ, hφ, ⟨eN⟩⟩ := h
  exact ⟨φ.comp e.toMonoidHom, hφ.comp e.surjective, ⟨(kerCompMulEquiv e φ).trans eN⟩⟩

theorem isCentralProduct₂_of_mulEquiv {R R' A B : Type*} [Group R] [Group R'] [Group A]
    [Group B] (e : R ≃* R') (h : IsCentralProduct₂ R' A B) : IsCentralProduct₂ R A B := by
  obtain ⟨A', B', hAB, hc, ⟨eA⟩, ⟨eB⟩, h2⟩ := h
  refine ⟨A'.map e.symm.toMonoidHom, B'.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hAB, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr e.symm.surjective
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    change e.symm a * e.symm b = e.symm b * e.symm a
    rw [← map_mul, ← map_mul, hc a ha b hb]
  · exact ⟨(A'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans eA⟩
  · exact ⟨(B'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans eB⟩
  · rw [← Subgroup.map_inf_eq _ _ _ e.symm.injective, ← h2]
    exact Nat.card_congr ((A' ⊓ B').equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective).toEquiv.symm

theorem map_frattini_mulEquiv {R R' : Type*} [Group R] [Group R'] (e : R ≃* R') :
    (frattini R).map e.toMonoidHom = frattini R' := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro x hx
    refine ⟨e.symm x, frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom)
      e.symm.surjective hx, ?_⟩
    simp

theorem map_commutator_mulEquiv {R R' : Type*} [Group R] [Group R'] (e : R ≃* R') :
    (commutator R).map e.toMonoidHom = commutator R' := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective, _root_.commutator_def]

theorem isSpecialTwoOnePlusFour_of_mulEquiv {R R' : Type*} [Group R] [Group R'] (e : R ≃* R')
    (h : IsSpecialTwoOnePlusFour R') : IsSpecialTwoOnePlusFour R := by
  obtain ⟨hc, hz, hcomm, hfr⟩ := h
  have hZ : (Subgroup.center R).map e.toMonoidHom = Subgroup.center R' :=
    Subgroup.map_center_eq e
  refine ⟨(Nat.card_congr e.toEquiv).trans hc, ?_, ?_, ?_⟩
  · rw [← hz, ← hZ]
    exact Nat.card_congr ((Subgroup.center R).equivMapOfInjective _ e.injective).toEquiv
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hZ, ← hcomm, map_commutator_mulEquiv]
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hZ, ← hfr, map_frattini_mulEquiv]

theorem isExtensionWith_centralProduct_of_mulEquiv {X Y A B C : Type*} [Group X] [Group Y]
    [Group A] [Group B] [Group C] (e : X ≃* Y)
    (h : IsExtensionWith Y A (fun N => IsCentralProduct₂ ↥N B C)) :
    IsExtensionWith X A (fun N => IsCentralProduct₂ ↥N B C) := by
  obtain ⟨φ, hφ, hker⟩ := h
  exact ⟨φ.comp e.toMonoidHom, hφ.comp e.surjective,
    isCentralProduct₂_of_mulEquiv (kerCompMulEquiv e φ) hker⟩

theorem isExtensionOf₃_of_mulEquiv {X Y A B C : Type*} [Group X] [Group Y] [Group A] [Group B]
    [Group C] (e : X ≃* Y) (h : IsExtensionOf₃ Y A B C) : IsExtensionOf₃ X A B C := by
  obtain ⟨N, hN, ⟨eN⟩, hQ⟩ := h
  let N' := N.comap e.toMonoidHom
  have hN' : N'.Normal := hN.comap _
  have hmap : N'.map e.toMonoidHom = N := Subgroup.map_comap_eq_self_of_surjective e.surjective N
  have eN' : ↥N' ≃* C :=
    ((N'.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hmap)).trans
      eN
  have eQ : X ⧸ N' ≃* Y ⧸ N := QuotientGroup.congr N' N e hmap
  exact ⟨N', hN', ⟨eN'⟩, isExtensionOf_of_mulEquiv eQ hQ⟩

noncomputable def infMulEquivOfAmalgamIso {D E : Type*} [Group D] [Group E]
    {H₁ H₂ : Subgroup D} {K₁ K₂ : Subgroup E} (φ₁ : ↥H₁ ≃* ↥K₁) (φ₂ : ↥H₂ ≃* ↥K₂)
    (h₁ : ∀ (x : D) (hx₁ : x ∈ H₁) (hx₂ : x ∈ H₂), (φ₁ ⟨x, hx₁⟩ : E) = φ₂ ⟨x, hx₂⟩)
    (h₂ : ∀ (y : E) (hy₁ : y ∈ K₁) (hy₂ : y ∈ K₂), (φ₁.symm ⟨y, hy₁⟩ : D) = φ₂.symm ⟨y, hy₂⟩) :
    ↥(H₁ ⊓ H₂) ≃* ↥(K₁ ⊓ K₂) where
  toFun x := ⟨φ₁ (Subgroup.inclusion inf_le_left x), Subgroup.mem_inf.mpr ⟨(φ₁ _).2, by
    rw [show Subgroup.inclusion inf_le_left x = ⟨x, (Subgroup.mem_inf.mp x.2).1⟩ from rfl,
      h₁ x (Subgroup.mem_inf.mp x.2).1 (Subgroup.mem_inf.mp x.2).2]
    exact (φ₂ _).2⟩⟩
  invFun y := ⟨φ₁.symm (Subgroup.inclusion inf_le_left y), Subgroup.mem_inf.mpr ⟨(φ₁.symm _).2, by
    rw [show Subgroup.inclusion inf_le_left y = ⟨y, (Subgroup.mem_inf.mp y.2).1⟩ from rfl,
      h₂ y (Subgroup.mem_inf.mp y.2).1 (Subgroup.mem_inf.mp y.2).2]
    exact (φ₂.symm _).2⟩⟩
  left_inv x := by
    apply Subtype.ext
    change ((φ₁.symm (φ₁ (Subgroup.inclusion inf_le_left x)) : ↥H₁) : D) = x
    rw [MulEquiv.symm_apply_apply]
    rfl
  right_inv y := by
    apply Subtype.ext
    change ((φ₁ (φ₁.symm (Subgroup.inclusion inf_le_left y)) : ↥K₁) : E) = y
    rw [MulEquiv.apply_symm_apply]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]

theorem ker_quotientPCore {X A : Type*} [Group X] [Group A] (e : X ⧸ Open.pCore 2 X ≃* A) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Open.pCore 2 X))).ker = Open.pCore 2 X := by
  ext x
  simp

theorem isExtensionOf_of_quotientPCore {D : Type*} [Group D] {H : Subgroup D} {A N : Type*}
    [Group A] [Group N] (e : ↥H ⧸ Open.pCore 2 ↥H ≃* A) (eN : ↥(pCoreOf 2 H) ≃* N) :
    IsExtensionOf ↥H A N :=
  ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), e.surjective.comp (QuotientGroup.mk'_surjective _),
    ⟨((MulEquiv.subgroupCongr (ker_quotientPCore e)).trans (pCoreOfEquiv H)).trans eN⟩⟩

theorem isExtensionWith_of_quotientPCore {D : Type*} [Group D] {H : Subgroup D} {A : Type*}
    [Group A] {P : Subgroup ↥H → Prop} (e : ↥H ⧸ Open.pCore 2 ↥H ≃* A)
    (hP : P (Open.pCore 2 ↥H)) : IsExtensionWith ↥H A P :=
  ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), e.surjective.comp (QuotientGroup.mk'_surjective _),
    (ker_quotientPCore e).symm ▸ hP⟩

theorem map_center_eq_centerOf {D : Type*} [Group D] (R : Subgroup D) :
    (Subgroup.center ↥R).map R.subtype = centerOf R := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  · intro hx
    obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hxR⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hxc y y.2

theorem card_centerOf_eq_card_center {D : Type*} [Group D] (R : Subgroup D) :
    Nat.card ↥(centerOf R) = Nat.card ↥(Subgroup.center ↥R) := by
  rw [← map_center_eq_centerOf]
  exact Nat.card_congr ((Subgroup.center ↥R).equivMapOfInjective _ R.subtype_injective).toEquiv.symm

theorem card_centerOf_eq {D E : Type*} [Group D] [Group E] {R : Subgroup D} {R' : Subgroup E}
    (e : ↥R ≃* ↥R') : Nat.card ↥(centerOf R) = Nat.card ↥(centerOf R') := by
  rw [card_centerOf_eq_card_center, card_centerOf_eq_card_center, ← Subgroup.map_center_eq e]
  exact Nat.card_congr ((Subgroup.center ↥R).equivMapOfInjective _ e.injective).toEquiv

end F6

end CFSG.Quasithin
