module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.Quasithin.H.SecQ

open scoped IsMulCommutative

variable {G : Type*} [Group G] {A B : Subgroup G}

@[expose] def conjA {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) : ↥A ≃* ↥A where
  toFun a := ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg a).1 a.2⟩
  invFun a := ⟨g⁻¹ * a * g, by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) a).1 a.2
    simpa using this⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem coe_conjA {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) (a : ↥A) :
    ((conjA hg a : ↥A) : G) = g * a * g⁻¹ := rfl

theorem map_conjA {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) :
    (B.subgroupOf A).map (conjA hgA).toMonoidHom = B.subgroupOf A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hgB y).1 hy
  · intro hx
    refine ⟨(conjA hgA).symm x, ?_, (conjA hgA).apply_symm_apply x⟩
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgB) x).1 hx
    show g⁻¹ * (x : G) * g ∈ B
    simpa using this

section Quot

variable [hN : (B.subgroupOf A).Normal]

@[expose] noncomputable def conjW {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) : MulAut (↥A ⧸ B.subgroupOf A) :=
  QuotientGroup.congr (B.subgroupOf A) (B.subgroupOf A) (conjA hgA) (map_conjA hgA hgB)

theorem conjW_mk {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) (a : ↥A) :
    conjW hgA hgB (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) = QuotientGroup.mk (conjA hgA a) :=
  QuotientGroup.congr_mk _ _ _ _ a

@[expose] noncomputable def conjHom :
    ↥(Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G)) →*
      MulAut (↥A ⧸ B.subgroupOf A) where
  toFun g := conjW g.2.1 g.2.2
  map_one' := by
    ext w
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective w
    rw [conjW_mk]
    congr 1
    exact Subtype.ext (by simp [coe_conjA])
  map_mul' g h := by
    ext w
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective w
    rw [MulAut.mul_apply, conjW_mk, conjW_mk, conjW_mk]
    congr 1
    exact Subtype.ext (by simp [coe_conjA, mul_assoc])

theorem conjHom_mk (g : ↥(Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G)))
    (a : ↥A) : conjHom g (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) =
      QuotientGroup.mk (conjA g.2.1 a) := conjW_mk g.2.1 g.2.2 a

end Quot

theorem relIndex_mul_eq (hBA : B ≤ A) (C : Subgroup G) :
    B.relIndex (C ⊓ A) * C.relIndex A = C.relIndex B * B.relIndex A := by
  have h1 := Subgroup.relIndex_inf_mul_relIndex B C A
  have h2 := Subgroup.relIndex_inf_mul_relIndex C B A
  rw [inf_eq_left.2 hBA] at h2
  rw [h1, h2, inf_comm]

section Fix

variable [hN : (B.subgroupOf A).Normal]

theorem relIndex_le_card_fix [Finite G] {θ : G} (hθA : θ ∈ Subgroup.normalizer (A : Set G))
    (hθB : θ ∈ Subgroup.normalizer (B : Set G)) :
    B.relIndex (Subgroup.centralizer ({θ} : Set G) ⊓ A) ≤
      Nat.card {w : ↥A ⧸ B.subgroupOf A // conjW hθA hθB w = w} := by
  classical
  set C := Subgroup.centralizer ({θ} : Set G) with hC
  set f : ↥(C ⊓ A) →* ↥A ⧸ B.subgroupOf A :=
    (QuotientGroup.mk' (B.subgroupOf A)).comp (Subgroup.inclusion inf_le_right) with hf
  have hker : f.ker = B.subgroupOf (C ⊓ A) := by
    ext c
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have h1 : B.relIndex (C ⊓ A) = Nat.card f.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  rw [h1]
  refine Nat.card_le_card_of_injective (fun w => ⟨w.1, ?_⟩) fun w₁ w₂ h => by
    have := congrArg (fun x : {w : ↥A ⧸ B.subgroupOf A // conjW hθA hθB w = w} => x.1) h
    exact Subtype.ext this
  obtain ⟨c, hc⟩ := w.2
  rw [← hc, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, conjW_mk]
  congr 1
  apply Subtype.ext
  rw [coe_conjA]
  have h2 : (c : G) * θ = θ * c := Subgroup.mem_centralizer_singleton_iff.1 c.2.1
  show θ * (c : G) * θ⁻¹ = c
  rw [← h2, mul_inv_cancel_right]

end Fix

@[expose] def centSub (A B Y : Subgroup G) (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Subgroup G where
  carrier := {a | a ∈ A ∧ ∀ y ∈ Y, y * a * y⁻¹ * a⁻¹ ∈ B}
  one_mem' := ⟨A.one_mem, fun y _ => by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, fun y hy => by
    have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
        (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact B.mul_mem (ha.2 y hy) ((Subgroup.mem_normalizer_iff.1 (hAB ha.1) _).1 (hb.2 y hy))⟩
  inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, fun y hy => by
    have e : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hAB (A.inv_mem ha.1)) _).1 (B.inv_mem (ha.2 y hy))⟩

theorem le_centSub {Y : Subgroup G} (hBA : B ≤ A) (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hYB : Y ≤ Subgroup.normalizer (B : Set G)) : B ≤ centSub A B Y hAB := fun b hb =>
  ⟨hBA hb, fun _y hy => B.mul_mem ((Subgroup.mem_normalizer_iff.1 (hYB hy) b).1 hb) (B.inv_mem hb)⟩

theorem centSub_le {Y : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    centSub A B Y hAB ≤ A := fun _ ha => ha.1

theorem le_normalizer_centSub [Finite G] {X Y : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    X ≤ Subgroup.normalizer (centSub A B Y hAB : Set G) := by
  intro x hx
  refine Subgroup.mem_normalizer_fintype fun a ha => ⟨(Subgroup.mem_normalizer_iff.1 (hXA hx) a).1
    ha.1, fun y hy => ?_⟩
  have hy' : x⁻¹ * y * x⁻¹⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.1 (hXY (Subgroup.inv_mem _ hx)) y).1 hy
  have h1 := ha.2 _ hy'
  have e : y * (x * a * x⁻¹) * y⁻¹ * (x * a * x⁻¹)⁻¹ =
      x * ((x⁻¹ * y * x⁻¹⁻¹) * a * (x⁻¹ * y * x⁻¹⁻¹)⁻¹ * a⁻¹) * x⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 (hXB hx) _).1 h1

theorem exists_mem_centSub [Finite G] (hBA : B ≤ A) (hAB : A ≤ Subgroup.normalizer (B : Set G))
    {Y : Subgroup G} (hYA : Y ≤ Subgroup.normalizer (A : Set G))
    (hYB : Y ≤ Subgroup.normalizer (B : Set G)) (hY2 : IsPGroup 2 Y) (hA2 : IsPGroup 2 A)
    (hlt : B < A) : ∃ a ∈ centSub A B Y hAB, a ∉ B := by
  classical
  have : (B.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBA).2 hAB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := ↥A ⧸ B.subgroupOf A
  let φ : ↥Y →* MulAut W := conjHom.comp (Subgroup.inclusion (le_inf hYA hYB))
  let _ : MulAction ↥Y W := MulAction.compHom W φ
  have h1 := hY2.card_modEq_card_fixedPoints W
  obtain ⟨a₀, ha₀A, ha₀B⟩ := IsConcreteLE.exists_of_lt hlt
  have hW2 : IsPGroup 2 W := hA2.to_quotient _
  have hWnt : Nontrivial W := ⟨⟨QuotientGroup.mk ⟨a₀, ha₀A⟩, 1, fun h => ha₀B (by
    rw [QuotientGroup.eq_one_iff] at h
    exact h)⟩⟩
  have h2 : 2 ∣ Nat.card W := by
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      have := Finite.one_lt_card_iff_nontrivial.2 hWnt
      omega
    rw [hk]
    exact dvd_pow_self 2 hk0
  have h3 : 2 ∣ Nat.card (MulAction.fixedPoints ↥Y W) := by
    have := (Nat.modEq_zero_iff_dvd.2 h2).symm.trans h1
    exact Nat.modEq_zero_iff_dvd.1 this.symm
  have h1fix : (1 : W) ∈ MulAction.fixedPoints ↥Y W := fun y => by
    show φ y 1 = 1
    exact map_one _
  obtain ⟨w, hwfix, hw1⟩ : ∃ w ∈ MulAction.fixedPoints ↥Y W, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h4 : Nat.card (MulAction.fixedPoints ↥Y W) ≤ 1 := by
      have : Subsingleton (MulAction.fixedPoints ↥Y W) := ⟨fun x y => Subtype.ext
        ((hcon x.1 x.2).trans (hcon y.1 y.2).symm)⟩
      exact Finite.card_le_one_iff_subsingleton.2 this
    have h5 : 0 < Nat.card (MulAction.fixedPoints ↥Y W) := Nat.card_pos_iff.2
      ⟨⟨⟨1, h1fix⟩⟩, inferInstance⟩
    omega
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective w
  refine ⟨a, ⟨a.2, fun y hy => ?_⟩, fun haB => hw1 ((QuotientGroup.eq_one_iff _).2 haB)⟩
  have h6 : φ ⟨y, hy⟩ (QuotientGroup.mk a) = QuotientGroup.mk a := hwfix ⟨y, hy⟩
  rw [show φ ⟨y, hy⟩ = conjHom ⟨y, hYA hy, hYB hy⟩ from rfl, conjHom_mk,
    QuotientGroup.eq] at h6
  have h7 : (y * a * y⁻¹ : G)⁻¹ * a ∈ B := h6
  have e : y * (a : G) * y⁻¹ * (a : G)⁻¹ =
      (a : G) * ((y * a * y⁻¹ : G)⁻¹ * a)⁻¹ * (a : G)⁻¹ := by group
  show y * (a : G) * y⁻¹ * (a : G)⁻¹ ∈ B
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 (hAB a.2) _).1 (B.inv_mem h7)

theorem comm_mem_of_irr [Finite G] (hBA : B ≤ A) (hAB : A ≤ Subgroup.normalizer (B : Set G))
    {X Y : Subgroup G} (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hXB : X ≤ Subgroup.normalizer (B : Set G)) (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hY2 : IsPGroup 2 Y) (hA2 : IsPGroup 2 A)
    (hlt : B < A)
    (hirr : ∀ D : Subgroup G, B ≤ D → D ≤ A → X ≤ Subgroup.normalizer (D : Set G) →
      D = B ∨ D = A) :
    ∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ B := by
  rcases hirr (centSub A B Y hAB) (le_centSub hBA hAB (hYX.trans hXB)) (centSub_le hAB)
    (le_normalizer_centSub hAB hXA hXB hXY) with h | h
  · exfalso
    obtain ⟨a, ha, haB⟩ := exists_mem_centSub hBA hAB (hYX.trans hXA) (hYX.trans hXB) hY2 hA2 hlt
    rw [h] at ha
    exact haB ha
  · intro y hy a ha
    rw [← h] at ha
    exact ha.2 y hy

theorem isElementaryAbelian_of_irr [Finite G] (hBA : B ≤ A)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) {X Y : Subgroup G}
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) (hXB : X ≤ Subgroup.normalizer (B : Set G))
    (hYX : Y ≤ X) (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hY2 : IsPGroup 2 Y) (hAY : A ≤ Y)
    (hlt : B < A)
    (hirr : ∀ D : Subgroup G, B ≤ D → D ≤ A → X ≤ Subgroup.normalizer (D : Set G) →
      D = B ∨ D = A) :
    haveI : (B.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBA).2 hAB
    IsElementaryAbelian 2 (↥A ⧸ B.subgroupOf A) := by
  classical
  have : (B.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBA).2 hAB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := hY2.to_le hAY
  have hcomm := comm_mem_of_irr hBA hAB hXA hXB hYX hXY hY2 hA2 hlt hirr
  have hcommW : ∀ x y : ↥A ⧸ B.subgroupOf A, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 := hcomm _ (hAY b.2) _ a.2
    have e : (((a * b)⁻¹ * (b * a) : ↥A) : G) =
        ((a * b : ↥A) : G)⁻¹ * ((b : G) * a * (b : G)⁻¹ * (a : G)⁻¹) * ((a * b : ↥A) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    show ((a * b)⁻¹ * (b * a) : ↥A) ∈ B.subgroupOf A
    rw [Subgroup.mem_subgroupOf, e]
    have := (Subgroup.mem_normalizer_iff.1 (hAB (A.inv_mem (a * b).2)) _).1 h1
    simpa using this
  set D₂ : Subgroup G :=
    { carrier := {a | a ∈ A ∧ a ^ 2 ∈ B}
      one_mem' := ⟨A.one_mem, by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
        have hc := hcomm _ (hAY (A.inv_mem ha.1)) _ hb.1
        have e : (a * b) ^ 2 = a ^ 2 * (a⁻¹ * b * a⁻¹⁻¹ * b⁻¹) * b ^ 2 := by
          rw [sq, sq, sq]
          group
        rw [e]
        exact B.mul_mem (B.mul_mem ha.2 hc) hb.2⟩
      inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by
        rw [inv_pow]
        exact B.inv_mem ha.2⟩ } with hD₂
  have hsq : ∀ a ∈ A, a ^ 2 ∈ B := by
    rcases hirr D₂ (fun b hb => ⟨hBA hb, B.pow_mem hb 2⟩) (fun a ha => ha.1) (by
      intro x hx
      refine Subgroup.mem_normalizer_fintype fun a ha => ⟨(Subgroup.mem_normalizer_iff.1
        (hXA hx) a).1 ha.1, ?_⟩
      have e : (x * a * x⁻¹) ^ 2 = x * a ^ 2 * x⁻¹ := by
        rw [sq, sq]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hXB hx) _).1 ha.2) with h | h
    · exfalso
      obtain ⟨a₀, ha₀A, ha₀B⟩ := IsConcreteLE.exists_of_lt hlt
      have hW2 : IsPGroup 2 (↥A ⧸ B.subgroupOf A) := hA2.to_quotient _
      have hWnt : Nontrivial (↥A ⧸ B.subgroupOf A) := ⟨⟨QuotientGroup.mk ⟨a₀, ha₀A⟩, 1,
        fun h => ha₀B ((QuotientGroup.eq_one_iff (⟨a₀, ha₀A⟩ : ↥A)).1 h)⟩⟩
      have h2 : 2 ∣ Nat.card (↥A ⧸ B.subgroupOf A) := by
        obtain ⟨k, hk⟩ := hW2.exists_card_eq
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [pow_zero] at hk
          have := Finite.one_lt_card_iff_nontrivial.2 hWnt
          omega
        rw [hk]
        exact dvd_pow_self 2 hk0
      let _ : Fintype (↥A ⧸ B.subgroupOf A) := Fintype.ofFinite _
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card (G := ↥A ⧸ B.subgroupOf A) 2
        (by rwa [← Nat.card_eq_fintype_card])
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective w
      have ha1 : (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hw
        exact absurd hw (by norm_num)
      have ha2 : (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) ^ 2 = 1 := by
        rw [← hw]
        exact pow_orderOf_eq_one _
      have haD : (a : G) ∈ D₂ := ⟨a.2, by
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at ha2
        have := Subgroup.mem_subgroupOf.1 ha2
        simpa using this⟩
      rw [h] at haD
      exact ha1 ((QuotientGroup.eq_one_iff _).2 haD)
    · intro a ha
      rw [← h] at ha
      exact ha.2
  have hpow : ∀ x : ↥A ⧸ B.subgroupOf A, x ^ 2 = 1 := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hsq a a.2
  exact { toIsMulCommutative := ⟨⟨hcommW⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }

end CFSG.Quasithin.H.SecQ
