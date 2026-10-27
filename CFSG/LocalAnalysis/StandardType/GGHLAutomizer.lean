module

public import CFSG.LocalAnalysis.StandardType.GGHLFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

lemma ggHLA_fixes_x {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hxB : x ∈ Bs) :
    ∀ χ ∈ ggAutomizer L Bs, χ (⟨x, hxB⟩ : ↥Bs) = ⟨x, hxB⟩ := by
  intro χ hχ
  obtain ⟨g, hgL, -, hgconj⟩ := mem_ggAutomizer_iff.mp hχ
  apply Subtype.ext
  rw [hgconj]
  change g * x * g⁻¹ = x
  calc g * x * g⁻¹ = x * g * g⁻¹ := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)]
    _ = x := by group

lemma ggHLA_pres {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hxB : x ∈ Bs) :
    ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := by
  intro χ hχ z hz
  have hfix := ggHLA_fixes_x hLx hxB χ hχ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hzk : χ z = (⟨x, hxB⟩ : ↥Bs) ^ k := by
    rw [← hk, map_zpow, hfix]
  rw [hzk]
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩

lemma ggHLA_rangeRestrict_eq_one {G : Type} [Group G] {Bs L : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (b : ↥Bs) :
    (ggGamma L hBsN).rangeRestrict b = 1 ↔ ggGamma L hBsN b = 1 := by
  constructor
  · intro h
    have h' := congrArg (fun a : ↥(ggGamma L hBsN).range => (a : MulAut L)) h
    simpa using h'
  · intro h
    apply Subtype.ext
    simpa using h

lemma ggHLA_desc_exists {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : MulAut ↥Bs) (hχ : χ ∈ ggAutomizer L Bs) (a : ↥(ggGamma L hBsN).range) :
    ∃ c : ↥(ggGamma L hBsN).range,
      ∀ b : ↥Bs, (ggGamma L hBsN).rangeRestrict b = a →
        (ggGamma L hBsN).rangeRestrict (χ b) = c := by
  have hker_r : ∀ b : ↥Bs, (ggGamma L hBsN).rangeRestrict b = 1 ↔
      b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := fun b =>
    (ggHLA_rangeRestrict_eq_one hBsN b).trans (hker b)
  obtain ⟨b0, hb0⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
  refine ⟨(ggGamma L hBsN).rangeRestrict (χ b0), fun b hb => ?_⟩
  have hmem : b0⁻¹ * b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := by
    apply (hker_r (b0⁻¹ * b)).mp
    rw [map_mul, map_inv, hb, hb0, inv_mul_cancel]
  have hχmem : χ (b0⁻¹ * b) ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := hpres χ hχ _ hmem
  have h1 : (ggGamma L hBsN).rangeRestrict (χ (b0⁻¹ * b)) = 1 := (hker_r _).mpr hχmem
  calc (ggGamma L hBsN).rangeRestrict (χ b)
      = (ggGamma L hBsN).rangeRestrict (χ (b0 * (b0⁻¹ * b))) := by rw [mul_inv_cancel_left]
    _ = (ggGamma L hBsN).rangeRestrict (χ b0 * χ (b0⁻¹ * b)) := by rw [map_mul]
    _ = (ggGamma L hBsN).rangeRestrict (χ b0) *
        (ggGamma L hBsN).rangeRestrict (χ (b0⁻¹ * b)) := by rw [map_mul]
    _ = (ggGamma L hBsN).rangeRestrict (χ b0) := by rw [h1, mul_one]

@[expose] noncomputable def ggHLA_descFun {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : MulAut ↥Bs) (hχ : χ ∈ ggAutomizer L Bs) (a : ↥(ggGamma L hBsN).range) :
    ↥(ggGamma L hBsN).range :=
  Classical.choose (ggHLA_desc_exists hBsN hxB hker hpres χ hχ a)

lemma ggHLA_descFun_spec {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : MulAut ↥Bs) (hχ : χ ∈ ggAutomizer L Bs) (b : ↥Bs) :
    ggHLA_descFun hBsN hxB hker hpres χ hχ ((ggGamma L hBsN).rangeRestrict b) =
      (ggGamma L hBsN).rangeRestrict (χ b) :=
  (Classical.choose_spec (ggHLA_desc_exists hBsN hxB hker hpres χ hχ _) b rfl).symm

@[expose] noncomputable def ggHLA_descHom {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : MulAut ↥Bs) (hχ : χ ∈ ggAutomizer L Bs) :
    ↥(ggGamma L hBsN).range →* ↥(ggGamma L hBsN).range where
  toFun := ggHLA_descFun hBsN hxB hker hpres χ hχ
  map_one' := by
    have h := ggHLA_descFun_spec hBsN hxB hker hpres χ hχ (1 : ↥Bs)
    rw [map_one, map_one] at h
    simpa using h
  map_mul' := by
    intro a a'
    obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
    obtain ⟨b', rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a'
    rw [← map_mul, ggHLA_descFun_spec, map_mul, map_mul,
      ggHLA_descFun_spec, ggHLA_descFun_spec]

lemma ggHLA_descHom_bijective {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : MulAut ↥Bs) (hχ : χ ∈ ggAutomizer L Bs) :
    Function.Bijective (ggHLA_descHom hBsN hxB hker hpres χ hχ) := by
  have hχ' : χ⁻¹ ∈ ggAutomizer L Bs := Subgroup.inv_mem _ hχ
  have hleft : Function.LeftInverse
      (ggHLA_descHom hBsN hxB hker hpres χ⁻¹ hχ')
      (ggHLA_descHom hBsN hxB hker hpres χ hχ) := by
    intro a
    obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
    show ggHLA_descFun hBsN hxB hker hpres χ⁻¹ hχ'
      (ggHLA_descFun hBsN hxB hker hpres χ hχ
        ((ggGamma L hBsN).rangeRestrict b)) = (ggGamma L hBsN).rangeRestrict b
    rw [ggHLA_descFun_spec, ggHLA_descFun_spec, MulAut.inv_apply_self]
  have hright : Function.RightInverse
      (ggHLA_descHom hBsN hxB hker hpres χ⁻¹ hχ')
      (ggHLA_descHom hBsN hxB hker hpres χ hχ) := by
    intro a
    obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
    show ggHLA_descFun hBsN hxB hker hpres χ hχ
      (ggHLA_descFun hBsN hxB hker hpres χ⁻¹ hχ'
        ((ggGamma L hBsN).rangeRestrict b)) = (ggGamma L hBsN).rangeRestrict b
    rw [ggHLA_descFun_spec, ggHLA_descFun_spec, MulAut.apply_inv_self]
  exact ⟨hleft.injective, hright.surjective⟩

@[expose] noncomputable def ggHLA_descAut {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : MulAut ↥Bs) (hχ : χ ∈ ggAutomizer L Bs) :
    MulAut ↥(ggGamma L hBsN).range :=
  MulEquiv.ofBijective (ggHLA_descHom hBsN hxB hker hpres χ hχ)
    (ggHLA_descHom_bijective hBsN hxB hker hpres χ hχ)

lemma ggHLA_descAut_apply {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : MulAut ↥Bs) (hχ : χ ∈ ggAutomizer L Bs) (a : ↥(ggGamma L hBsN).range) :
    ggHLA_descAut hBsN hxB hker hpres χ hχ a =
      ggHLA_descFun hBsN hxB hker hpres χ hχ a := rfl

@[expose] noncomputable def ggHLA_descOn {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : ↥(ggAutomizer L Bs)) : MulAut ↥(ggGamma L hBsN).range :=
  ggHLA_descAut hBsN hxB hker hpres (χ : MulAut ↥Bs) χ.2

lemma ggHLA_descOn_apply {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : ↥(ggAutomizer L Bs)) (a : ↥(ggGamma L hBsN).range) :
    ggHLA_descOn hBsN hxB hker hpres χ a =
      ggHLA_descAut hBsN hxB hker hpres (χ : MulAut ↥Bs) χ.2 a := rfl

@[expose] noncomputable def ggHLA_desc {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs)) :
    ↥(ggAutomizer L Bs) →* MulAut ↥(ggGamma L hBsN).range where
  toFun := ggHLA_descOn hBsN hxB hker hpres
  map_one' := by
    apply MulEquiv.ext
    intro a
    obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
    rw [ggHLA_descOn_apply, ggHLA_descAut_apply, ggHLA_descFun_spec]
    simp
  map_mul' := by
    intro χ ψ
    apply MulEquiv.ext
    intro a
    obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
    rw [MulAut.mul_apply, ggHLA_descOn_apply, ggHLA_descOn_apply, ggHLA_descOn_apply,
      ggHLA_descAut_apply, ggHLA_descAut_apply, ggHLA_descAut_apply,
      ggHLA_descFun_spec, ggHLA_descFun_spec, ggHLA_descFun_spec]
    rfl

lemma ggHLA_desc_apply {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : ↥(ggAutomizer L Bs)) (a : ↥(ggGamma L hBsN).range) :
    ggHLA_desc hBsN hxB hker hpres χ a =
      ggHLA_descAut hBsN hxB hker hpres (χ : MulAut ↥Bs) χ.2 a := rfl

lemma ggHLA_desc_spec {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : ↥(ggAutomizer L Bs)) (b : ↥Bs) :
    ggHLA_desc hBsN hxB hker hpres χ ((ggGamma L hBsN).rangeRestrict b) =
      (ggGamma L hBsN).rangeRestrict ((χ : MulAut ↥Bs) b) := by
  rw [ggHLA_desc_apply, ggHLA_descAut_apply, ggHLA_descFun_spec]

lemma ggHLA_closure_desc {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    {Λ : Type} (φ : Λ → MulAut ↥Bs) (hφ : ∀ i, φ i ∈ ggAutomizer L Bs)
    (hgen : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    Subgroup.closure (Set.range (fun i =>
      ggHLA_desc hBsN hxB hker hpres ⟨φ i, hφ i⟩)) =
      (ggHLA_desc hBsN hxB hker hpres).range := by
  have hcl : Subgroup.closure (Set.range (fun i =>
      (⟨φ i, hφ i⟩ : ↥(ggAutomizer L Bs)))) = ⊤ := by
    apply Subgroup.map_injective (f := (ggAutomizer L Bs).subtype)
      (ggAutomizer L Bs).subtype_injective
    rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
    conv_rhs => rw [hgen]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨φ i, hφ i⟩, ⟨i, rfl⟩, rfl⟩
  have himage : ggHLA_desc hBsN hxB hker hpres ''
      Set.range (fun i => (⟨φ i, hφ i⟩ : ↥(ggAutomizer L Bs))) =
      Set.range (fun i => ggHLA_desc hBsN hxB hker hpres ⟨φ i, hφ i⟩) := by
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨φ i, hφ i⟩, ⟨i, rfl⟩, rfl⟩
  calc Subgroup.closure (Set.range (fun i =>
          ggHLA_desc hBsN hxB hker hpres ⟨φ i, hφ i⟩))
      = Subgroup.closure (ggHLA_desc hBsN hxB hker hpres ''
          Set.range (fun i => (⟨φ i, hφ i⟩ : ↥(ggAutomizer L Bs)))) := by rw [himage]
    _ = (Subgroup.closure (Set.range (fun i =>
          (⟨φ i, hφ i⟩ : ↥(ggAutomizer L Bs))))).map
          (ggHLA_desc hBsN hxB hker hpres) := (MonoidHom.map_closure _ _).symm
    _ = (⊤ : Subgroup ↥(ggAutomizer L Bs)).map
          (ggHLA_desc hBsN hxB hker hpres) := by rw [hcl]
    _ = (ggHLA_desc hBsN hxB hker hpres).range := Subgroup.map_top _

lemma ggHLA_desc_mem {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔ b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (hpres : ∀ χ ∈ ggAutomizer L Bs, ∀ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs),
      χ z ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs))
    (χ : ↥(ggAutomizer L Bs)) :
    ggHLA_desc hBsN hxB hker hpres χ ∈
      ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range (ggGamma L hBsN).range := by
  obtain ⟨g, hgL, hgN, hg⟩ := mem_ggAutomizer_iff.mp χ.2
  rw [mem_ggAutomizer_iff]
  refine ⟨MulAut.conj (⟨g, hgL⟩ : ↥L), ⟨⟨g, hgL⟩, rfl⟩,
    conj_mem_normalizer_range_ggGamma hBsN hgL hgN, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
  have hgb : g * (b : G) * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hgN b).mp b.2
  have h2 : ((χ : MulAut ↥Bs) b) = ⟨g * (b : G) * g⁻¹, hgb⟩ := Subtype.ext (hg b)
  have h3 := ggGamma_conj L hBsN ⟨g, hgL⟩ b hgb
  rw [ggHLA_desc_spec, MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, h2]
  exact h3

@[expose] def GGAutomizerLift {G : Type} [Group G] (L Bs : Subgroup G)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) : Prop :=
  ∀ g ∈ ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range (ggGamma L hBsN).range,
    ∃ φ ∈ ggAutomizer L Bs, ∀ b : ↥Bs,
      g ((ggGamma L hBsN).rangeRestrict b) = (ggGamma L hBsN).rangeRestrict (φ b)

theorem ggAutomizerLift_of_system {G : Type} [Group G] {Bs L : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Λ₁ : Type} (φ₁ : Λ₁ → MulAut ↥Bs) (ψ₁ : Λ₁ → MulAut ↥(ggGamma L hBsN).range)
    (hcompat₁ : ∀ i (b : ↥Bs), ψ₁ i ((ggGamma L hBsN).rangeRestrict b) =
      (ggGamma L hBsN).rangeRestrict (φ₁ i b))
    (hA₁ : ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range =
      Subgroup.closure (Set.range ψ₁))
    (hgen₁ : ggAutomizer L Bs = Subgroup.closure (Set.range φ₁)) :
    GGAutomizerLift L Bs hBsN := by
  intro g hg
  rw [hA₁] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact ⟨φ₁ i, hgen₁ ▸ Subgroup.subset_closure (Set.mem_range_self i), hcompat₁ i⟩
  | one => exact ⟨1, Subgroup.one_mem _, fun b => by simp⟩
  | mul g g' _ _ ihg ihg' =>
      obtain ⟨φ, hφ, hgφ⟩ := ihg
      obtain ⟨φ', hφ', hgφ'⟩ := ihg'
      refine ⟨φ * φ', Subgroup.mul_mem _ hφ hφ', fun b => ?_⟩
      rw [MulAut.mul_apply, hgφ', hgφ, MulAut.mul_apply]
  | inv g _ ih =>
      obtain ⟨φ, hφ, hgφ⟩ := ih
      refine ⟨φ⁻¹, Subgroup.inv_mem _ hφ, fun b => ?_⟩
      have h1 := hgφ (φ⁻¹ b)
      rw [MulAut.apply_inv_self] at h1
      rw [← h1, MulAut.inv_apply_self]

theorem ggHL_lines_of_lift {G : Type} [Group G] [Finite G] {S : ℕ → LargeEvenLabel → Prop}
    (hW : GGTBWNormInputOn S) {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hM : GGInnerDiagOnLab S p Bs L)
    (hnc : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup p T ∧ ¬ IsCyclic T)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    (hlift : GGAutomizerLift L Bs hBsN)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hMw : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hgen : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (t : MulAut ↥Bs) (ht : t ∈ ggInduced ⊤ Bs) (htr : GGIsReflection p t)
    (htx : t ⟨x, hxB⟩ = ⟨x, hxB⟩) :
    GGHLLines (ggHLRoots (fun i => ggLin (p := p) ι (φ i)) h) (ι (Additive.ofMul ⟨x, hxB⟩))
      (ggLin (p := p) ι t) := by
  obtain ⟨hp, hBs, -, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hker : ∀ b : ↥Bs, ggGamma L hBsN b = 1 ↔
      b ∈ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := by
    intro b
    rw [ggGamma_eq_one_iff L hBsN b]
    constructor
    · intro hc
      have h2 : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨b.2, hc⟩
      rw [inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxB hS.2.2.1 hLx hS.2.2.2.2] at h2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    · intro hb
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hbG : (b : G) = x ^ k := by
        have h := congrArg Subtype.val hk
        rw [Subgroup.coe_zpow] at h
        exact h.symm
      have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
      have hbcent : (b : G) ∈ Subgroup.centralizer (L : Set G) := by
        rw [hbG]
        exact Subgroup.zpow_mem (Subgroup.centralizer (L : Set G)) hxcent k
      exact hbcent
  have hpres := ggHLA_pres (Bs := Bs) (L := L) (x := x) hLx hxB
  let desc : ↥(ggAutomizer L Bs) →* MulAut ↥(ggGamma L hBsN).range :=
    ggHLA_desc hBsN hxB hker hpres
  have hφmem : ∀ i, φ i ∈ ggAutomizer L Bs := fun i =>
    hgen.symm ▸ Subgroup.subset_closure (Set.mem_range_self i)
  let ψ : Λ → MulAut ↥(ggGamma L hBsN).range := fun i => desc ⟨φ i, hφmem i⟩
  have hcompat : ∀ i (b : ↥Bs), ψ i ((ggGamma L hBsN).rangeRestrict b) =
      (ggGamma L hBsN).rangeRestrict (φ i b) := by
    intro i b
    show ggHLA_desc hBsN hxB hker hpres ⟨φ i, hφmem i⟩
      ((ggGamma L hBsN).rangeRestrict b) =
      (ggGamma L hBsN).rangeRestrict (φ i b)
    rw [ggHLA_desc_spec]
  have hψrange : Subgroup.closure (Set.range ψ) =
      (ggHLA_desc hBsN hxB hker hpres).range := by
    show Subgroup.closure (Set.range (fun i =>
      ggHLA_desc hBsN hxB hker hpres ⟨φ i, hφmem i⟩)) = _
    exact ggHLA_closure_desc hBsN hxB hker hpres φ hφmem hgen
  have hA' : ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range =
      Subgroup.closure (Set.range ψ) := by
    rw [hψrange]
    refine le_antisymm (fun g hg => ?_) ?_
    · obtain ⟨χ, hχ, hgχ⟩ := hlift g hg
      refine ⟨⟨χ, hχ⟩, ?_⟩
      apply MulEquiv.ext
      intro a
      obtain ⟨b, rfl⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
      rw [ggHLA_desc_spec, hgχ]
    · rintro _ ⟨χ, rfl⟩
      exact ggHLA_desc_mem hBsN hxB hker hpres χ
  have hxker : ∀ i, α i (ι (Additive.ofMul ⟨x, hxB⟩)) = 0 := by
    intro i
    have hfixi : φ i (⟨x, hxB⟩ : ↥Bs) = ⟨x, hxB⟩ :=
      ggHLA_fixes_x hLx hxB (φ i) (hφmem i)
    have hfixL : ggLin (p := p) ι (φ i) (ι (Additive.ofMul ⟨x, hxB⟩)) =
        ι (Additive.ofMul ⟨x, hxB⟩) :=
      (ggLin_fix_iff ι (φ i) ⟨x, hxB⟩).mp hfixi
    have hzero : α i (ι (Additive.ofMul ⟨x, hxB⟩)) • h i = 0 := by
      have h1 := hlin i (ι (Additive.ofMul ⟨x, hxB⟩))
      rw [hfixL] at h1
      exact (sub_eq_self.mp h1.symm)
    have h2 : α i (α i (ι (Additive.ofMul ⟨x, hxB⟩)) • h i) = 0 := by
      rw [hzero, map_zero]
    rw [map_smul] at h2
    rw [hpair i i] at h2
    have hz : (C i i : ZMod p) ≠ 0 := by
      rw [hC.1 i]
      simpa using zmod_two_ne_zero hcfg.1.2.2.2.2.2.1.2.1
    rw [smul_eq_mul] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hz
  exact ggHL_lines_of_compat hW hcfg hM hnc hBsN hxB hMw hC ι φ h α hlin hrefl hpair hxker
    ψ hcompat hA' t ht htr htx

theorem ggHL_lines_of_automizer {G : Type} [Group G] [Finite G] {S : ℕ → LargeEvenLabel → Prop}
    (hW : GGTBWNormInputOn S) {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hM : GGInnerDiagOnLab S p Bs L)
    (hnc : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup p T ∧ ¬ IsCyclic T)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hxB : x ∈ Bs)
    {Λ₁ : Type} (φ₁ : Λ₁ → MulAut ↥Bs) (ψ₁ : Λ₁ → MulAut ↥(ggGamma L hBsN).range)
    (hcompat₁ : ∀ i (b : ↥Bs), ψ₁ i ((ggGamma L hBsN).rangeRestrict b) =
      (ggGamma L hBsN).rangeRestrict (φ₁ i b))
    (hA₁ : ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range =
      Subgroup.closure (Set.range ψ₁))
    (hgen₁ : ggAutomizer L Bs = Subgroup.closure (Set.range φ₁))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hMw : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hgen : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (t : MulAut ↥Bs) (ht : t ∈ ggInduced ⊤ Bs) (htr : GGIsReflection p t)
    (htx : t ⟨x, hxB⟩ = ⟨x, hxB⟩) :
    GGHLLines (ggHLRoots (fun i => ggLin (p := p) ι (φ i)) h) (ι (Additive.ofMul ⟨x, hxB⟩))
      (ggLin (p := p) ι t) :=
  ggHL_lines_of_lift hW hcfg hM hnc hBsN hxB
    (ggAutomizerLift_of_system hBsN φ₁ ψ₁ hcompat₁ hA₁ hgen₁) hMw hC ι φ h α hlin hrefl hpair hgen
    t ht htr htx

end CFSG.StandardType
