module

public import CFSG.Quasithin.Background.F7TwoInvDefs

public section

namespace CFSG.Quasithin.F7Two

section Hom

variable {A B : Type*} [Group A] [Group B]

theorem isPGroup_zpowers_map_iff (f : A →* B) (hf : Function.Injective f) (y : A) :
    IsPGroup 2 ↥(Subgroup.zpowers (f y)) ↔ IsPGroup 2 ↥(Subgroup.zpowers y) := by
  let e : ↥(Subgroup.zpowers y) ≃* ↥(Subgroup.zpowers (f y)) :=
    (Subgroup.equivMapOfInjective _ f hf).trans
      (MulEquiv.subgroupCongr (MonoidHom.map_zpowers f y))
  exact ⟨fun h => h.of_equiv e.symm, fun h => h.of_equiv e⟩

theorem InvAutGen.congr (e : A ≃* B) {φ : MulAut A} (h : InvAutGen A φ) :
    InvAutGen B ((e.symm.trans φ).trans e) := by
  unfold InvAutGen at h ⊢
  have hS : {y : B | ¬ IsPGroup 2 ↥(Subgroup.zpowers ((e.symm.trans φ).trans e y * y⁻¹))} =
      e.toMonoidHom '' {x : A | ¬ IsPGroup 2 ↥(Subgroup.zpowers (φ x * x⁻¹))} := by
    ext y
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      intro hP
      apply hy
      have h1 : (e.symm.trans φ).trans e y * y⁻¹ = e.toMonoidHom (φ (e.symm y) * (e.symm y)⁻¹) := by
        simp
      rw [h1, isPGroup_zpowers_map_iff e.toMonoidHom e.injective]
      exact hP
    · rintro ⟨x, hx, rfl⟩
      intro hP
      apply hx
      have h1 : (e.symm.trans φ).trans e (e.toMonoidHom x) * (e.toMonoidHom x)⁻¹ =
          e.toMonoidHom (φ x * x⁻¹) := by
        simp
      rw [h1, isPGroup_zpowers_map_iff e.toMonoidHom e.injective] at hP
      exact hP
  rw [hS, ← MonoidHom.map_closure, h, Subgroup.map_top_of_surjective _ e.surjective]

end Hom

section Conj

variable {Γ : Type*} [Group Γ]

@[expose] def conjRes (L : Subgroup Γ) (a : Γ) (ha : a ∈ Subgroup.normalizer (L : Set Γ)) :
    MulAut ↥L where
  toFun x := ⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha x).mp x.2⟩
  invFun x := ⟨a⁻¹ * x * a, (Subgroup.mem_normalizer_iff.mp ha _).mpr (by
    have e : a * (a⁻¹ * (x : Γ) * a) * a⁻¹ = x := by group
    rw [e]
    exact x.2)⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[simp] theorem conjRes_apply_coe {L : Subgroup Γ} {a : Γ}
    (ha : a ∈ Subgroup.normalizer (L : Set Γ)) (x : ↥L) :
    ((conjRes L a ha x : ↥L) : Γ) = a * x * a⁻¹ := rfl

theorem conjRes_mul_self {L : Subgroup Γ} {a : Γ} (ha : a ∈ Subgroup.normalizer (L : Set Γ))
    (ha2 : a * a = 1) : conjRes L a ha * conjRes L a ha = 1 := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  refine MulEquiv.ext fun x => Subtype.ext ?_
  show a * (a * (x : Γ) * a⁻¹) * a⁻¹ = x
  rw [hai]
  calc a * (a * (x : Γ) * a) * a = (a * a) * x * (a * a) := by group
    _ = x := by rw [ha2]; group

theorem conjRes_ne_one {L : Subgroup Γ} {a : Γ} (ha : a ∈ Subgroup.normalizer (L : Set Γ))
    (hac : ∃ x ∈ L, a * x ≠ x * a) : conjRes L a ha ≠ 1 := by
  obtain ⟨x, hx, hax⟩ := hac
  intro h1
  apply hax
  have h2 := congrArg Subtype.val (MulEquiv.congr_fun h1 ⟨x, hx⟩)
  simp only [conjRes_apply_coe, MulAut.one_apply] at h2
  calc a * x = a * x * a⁻¹ * a := by group
    _ = x * a := by rw [h2]

theorem invGen_of_invAutGen {L : Subgroup Γ} {a : Γ} (ha : a ∈ Subgroup.normalizer (L : Set Γ))
    (h : InvAutGen ↥L (conjRes L a ha)) : InvGen L a := by
  unfold InvAutGen at h
  have hS : invXi L a = L.subtype ''
      {x : ↥L | ¬ IsPGroup 2 ↥(Subgroup.zpowers (conjRes L a ha x * x⁻¹))} := by
    ext y
    constructor
    · rintro ⟨hyL, hy⟩
      refine ⟨⟨y, hyL⟩, fun hP => hy ?_, rfl⟩
      have e : a * y * a⁻¹ * y⁻¹ = L.subtype (conjRes L a ha ⟨y, hyL⟩ * (⟨y, hyL⟩ : ↥L)⁻¹) :=
        rfl
      rw [e, isPGroup_zpowers_map_iff L.subtype L.subtype_injective]
      exact hP
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.2, fun hP => hx ?_⟩
      have e : a * L.subtype x * a⁻¹ * (L.subtype x)⁻¹ = L.subtype (conjRes L a ha x * x⁻¹) :=
        rfl
      rw [e, isPGroup_zpowers_map_iff L.subtype L.subtype_injective] at hP
      exact hP
  unfold InvGen
  rw [hS, ← MonoidHom.map_closure, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Conj

section Section

variable {Q : Type*} [Group Q] (R : Subgroup Q) [R.Normal] (L : Subgroup (Q ⧸ R))

@[expose] def secHom : ↥(L.comap (QuotientGroup.mk' R)) →* ↥L where
  toFun h := ⟨QuotientGroup.mk' R h, h.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem secHom_surjective : Function.Surjective (secHom R L) := by
  rintro ⟨l, hl⟩
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective R l
  exact ⟨⟨q, hl⟩, rfl⟩

theorem secHom_ker : (secHom R L).ker = R.subgroupOf (L.comap (QuotientGroup.mk' R)) := by
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    have h2 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  · intro h1
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h1)

noncomputable def secEquiv :
    ↥(L.comap (QuotientGroup.mk' R)) ⧸ R.subgroupOf (L.comap (QuotientGroup.mk' R)) ≃* ↥L :=
  (QuotientGroup.quotientMulEquivOfEq (secHom_ker R L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (secHom_surjective R L))

end Section

theorem invGen_of_invAutGenSQTK (hP : InvAutGenSQTK) {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.SectionRank.IsSQTKCat Q) (R : Subgroup Q) [R.Normal] {L : Subgroup (Q ⧸ R)}
    (hsimple : IsSimpleGroup ↥L) (hnonab : ∃ x y : ↥L, x * y ≠ y * x) {a : Q ⧸ R}
    (ha2 : a * a = 1) (ha : a ∈ Subgroup.normalizer (L : Set (Q ⧸ R)))
    (hac : ∃ x ∈ L, a * x ≠ x * a) : InvGen L a := by
  let e := secEquiv R L
  have : IsSimpleGroup ↥L := hsimple
  have hsH : IsSimpleGroup (↥(L.comap (QuotientGroup.mk' R)) ⧸
      R.subgroupOf (L.comap (QuotientGroup.mk' R))) := e.isSimpleGroup
  have hnH : ∃ x y : ↥(L.comap (QuotientGroup.mk' R)) ⧸
      R.subgroupOf (L.comap (QuotientGroup.mk' R)), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnonab
    refine ⟨e.symm x, e.symm y, fun h => hxy ?_⟩
    have := congrArg e h
    simpa using this
  set φ := conjRes L a ha with hφ
  let ψ : MulAut (↥(L.comap (QuotientGroup.mk' R)) ⧸
      R.subgroupOf (L.comap (QuotientGroup.mk' R))) := (e.trans φ).trans e.symm
  have hψ2 : ψ * ψ = 1 := by
    refine MulEquiv.ext fun x => ?_
    have h1 : φ (φ (e x)) = e x := MulEquiv.congr_fun (conjRes_mul_self ha ha2) (e x)
    simp only [MulAut.mul_apply, MulAut.one_apply]
    simp [ψ, h1]
  have hψ1 : ψ ≠ 1 := by
    intro h1
    apply conjRes_ne_one ha hac
    refine MulEquiv.ext fun x => ?_
    have h2 := MulEquiv.congr_fun h1 (e.symm x)
    simp only [MulAut.one_apply] at h2 ⊢
    have h3 := congrArg e h2
    simpa [ψ] using h3
  have h1 := hP Q hQ (L.comap (QuotientGroup.mk' R)) (R.subgroupOf (L.comap (QuotientGroup.mk' R)))
    hsH hnH ψ hψ2 hψ1
  have h2 := InvAutGen.congr e h1
  have h3 : (e.symm.trans ψ).trans e = φ := by
    refine MulEquiv.ext fun x => ?_
    simp [ψ]
  rw [h3] at h2
  exact invGen_of_invAutGen ha h2

section Inn

variable {L : Type*} [Group L]

theorem mulAut_mul_conj_mul_inv (φ : MulAut L) (x : L) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  refine MulEquiv.ext fun y => ?_
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem conj_injective_of_center_eq_bot (h : Subgroup.center L = ⊥) :
    Function.Injective (MulAut.conj (G := L)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← h]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 := MulEquiv.congr_fun hx y
  rw [MulAut.conj_apply, MulAut.one_apply] at h1
  calc y * x = x * y * x⁻¹ * x := by rw [h1]
    _ = x * y := by group

end Inn

end CFSG.Quasithin.F7Two
