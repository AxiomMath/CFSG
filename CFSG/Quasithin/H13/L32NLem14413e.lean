module

public import CFSG.Quasithin.H13.L32NLem14413d
public import CFSG.Quasithin.H13.Sp62Over
public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteenZ
public import CFSG.Quasithin.H13.L32ARuOne

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6
open CFSG.Quasithin.H13.L32A
open scoped IsMulCommutative

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem val_one_two : (1 : ZMod 2).val = 1 := rfl

theorem pow_val_add {W : Type*} [Monoid W] {w : W} (hw : w ^ 2 = 1) (c d : ZMod 2) :
    w ^ (c + d).val = w ^ c.val * w ^ d.val := by
  rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 + 1 : ZMod 2) = 0 by decide, ZMod.val_zero, val_one_two, pow_zero, pow_one,
      ← pow_two, hw]

@[expose] def coordInv {W : Type*} [CommGroup W] (h2 : ∀ w : W, w ^ 2 = 1) (z a b : W) :
    Multiplicative (Fin 3 → ZMod 2) →* W where
  toFun x := z ^ (Multiplicative.toAdd x 0).val * a ^ (Multiplicative.toAdd x 1).val *
    b ^ (Multiplicative.toAdd x 2).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Pi.add_apply, pow_val_add (h2 _)]
    ac_rfl

theorem inv_eq_self_of_sq {W : Type*} [Group W] {w : W} (hw : w ^ 2 = 1) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, hw])

theorem coordInv_injective {W : Type*} [CommGroup W] (h2 : ∀ w : W, w ^ 2 = 1) {z a b : W}
    (hz : z ≠ 1) (ha : a ≠ 1) (haz : a ≠ z) (hb : b ≠ 1) (hbz : b ≠ z) (hba : b ≠ a)
    (hbza : b ≠ z * a) : Function.Injective (coordInv h2 z a b) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  simp only [coordInv, MonoidHom.coe_mk, OneHom.coe_mk] at hx
  suffices h : Multiplicative.toAdd x = 0 from h
  rcases zmod2_cases (Multiplicative.toAdd x 0) with h0 | h0 <;>
    rcases zmod2_cases (Multiplicative.toAdd x 1) with h1 | h1 <;>
    rcases zmod2_cases (Multiplicative.toAdd x 2) with h3 | h3 <;>
    simp only [h0, h1, h3, ZMod.val_zero, val_one_two, pow_zero, pow_one, one_mul,
      mul_one] at hx
  · funext i; fin_cases i <;> assumption
  · exact absurd hx hb
  · exact absurd hx ha
  · exact absurd (by rw [eq_inv_of_mul_eq_one_right hx, inv_eq_self_of_sq (h2 a)]) hba
  · exact absurd hx hz
  · exact absurd (by rw [eq_inv_of_mul_eq_one_right hx, inv_eq_self_of_sq (h2 z)]) hbz
  · exact absurd (by rw [eq_inv_of_mul_eq_one_right hx, inv_eq_self_of_sq (h2 z)]) haz
  · exact absurd (by rw [eq_inv_of_mul_eq_one_right hx, inv_eq_self_of_sq (h2 _)]) hbza

theorem exists_coords {W : Type*} [CommGroup W] [Finite W] (h2 : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 8) {z a b : W} (hz : z ≠ 1) (ha : a ≠ 1) (haz : a ≠ z) (hb : b ≠ 1)
    (hbz : b ≠ z) (hba : b ≠ a) (hbza : b ≠ z * a) :
    ∃ e : W ≃* Multiplicative (Fin 3 → ZMod 2), e z = Multiplicative.ofAdd (Pi.single 0 1) ∧
      e a = Multiplicative.ofAdd (Pi.single 1 1) ∧ e b = Multiplicative.ofAdd (Pi.single 2 1) := by
  have hbij : Function.Bijective (coordInv h2 z a b) :=
    (coordInv_injective h2 hz ha haz hb hbz hba hbza).bijective_of_nat_card_le
      (by rw [hcard, Nat.card_eq_fintype_card]; rfl)
  refine ⟨(MulEquiv.ofBijective _ hbij).symm, ?_, ?_, ?_⟩ <;>
    rw [MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply] <;>
    simp [coordInv, val_one_two]

variable {G : Type} [Group G]

theorem exists_transv {U : Subgroup G} {z a b : G} (hzU : ∀ u ∈ U, u * z = z * u)
    (hz2 : z * z = 1)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ = 1 ∨ u * v * u⁻¹ * v⁻¹ = z)
    (haU : a ∈ U) (hbU : b ∈ U) (ha : ∃ u ∈ U, u * a * u⁻¹ * a⁻¹ ≠ 1)
    (hb : ∃ u ∈ U, u * b * u⁻¹ * b⁻¹ ≠ 1)
    (hab : ∃ u ∈ U, u * (a * b) * u⁻¹ * (a * b)⁻¹ ≠ 1) :
    ∃ u ∈ U, u * a * u⁻¹ * a⁻¹ = z ∧ u * b * u⁻¹ * b⁻¹ = 1 := by
  have hc_mul : ∀ u ∈ U, ∀ u' ∈ U, ∀ w ∈ U, (u * u') * w * (u * u')⁻¹ * w⁻¹ =
      (u' * w * u'⁻¹ * w⁻¹) * (u * w * u⁻¹ * w⁻¹) := by
    intro u hu u' hu' w hw
    have hcz : u * (u' * w * u'⁻¹ * w⁻¹) = (u' * w * u'⁻¹ * w⁻¹) * u := by
      rcases hcomm u' hu' w hw with h | h <;> rw [h]
      · group
      · exact hzU u hu
    calc (u * u') * w * (u * u')⁻¹ * w⁻¹
        = u * (u' * w * u'⁻¹ * w⁻¹) * (w * u⁻¹ * w⁻¹) := by group
      _ = (u' * w * u'⁻¹ * w⁻¹) * u * (w * u⁻¹ * w⁻¹) := by rw [hcz]
      _ = (u' * w * u'⁻¹ * w⁻¹) * (u * w * u⁻¹ * w⁻¹) := by group
  have hc_ab : ∀ u ∈ U, u * (a * b) * u⁻¹ * (a * b)⁻¹ =
      (u * a * u⁻¹ * a⁻¹) * (u * b * u⁻¹ * b⁻¹) := by
    intro u hu
    have hca : (u * b * u⁻¹ * b⁻¹) * a = a * (u * b * u⁻¹ * b⁻¹) := by
      rcases hcomm u hu b hbU with h | h <;> rw [h]
      · group
      · exact (hzU a haU).symm
    calc u * (a * b) * u⁻¹ * (a * b)⁻¹
        = (u * a * u⁻¹ * a⁻¹) * (a * (u * b * u⁻¹ * b⁻¹)) * a⁻¹ := by group
      _ = (u * a * u⁻¹ * a⁻¹) * ((u * b * u⁻¹ * b⁻¹) * a) * a⁻¹ := by rw [hca]
      _ = (u * a * u⁻¹ * a⁻¹) * (u * b * u⁻¹ * b⁻¹) := by group
  obtain ⟨u₁, hu₁, h₁⟩ := ha
  have e₁ := (hcomm u₁ hu₁ a haU).resolve_left h₁
  rcases hcomm u₁ hu₁ b hbU with f₁ | f₁
  · exact ⟨u₁, hu₁, e₁, f₁⟩
  obtain ⟨u₂, hu₂, h₂⟩ := hb
  have f₂ := (hcomm u₂ hu₂ b hbU).resolve_left h₂
  rcases hcomm u₂ hu₂ a haU with e₂ | e₂
  · refine ⟨u₂ * u₁, U.mul_mem hu₂ hu₁, ?_, ?_⟩
    · rw [hc_mul u₂ hu₂ u₁ hu₁ a haU, e₁, e₂, mul_one]
    · rw [hc_mul u₂ hu₂ u₁ hu₁ b hbU, f₁, f₂, hz2]
  obtain ⟨u₃, hu₃, h₃⟩ := hab
  rw [hc_ab u₃ hu₃] at h₃
  rcases hcomm u₃ hu₃ a haU with e₃ | e₃ <;> rcases hcomm u₃ hu₃ b hbU with f₃ | f₃
  · exact absurd (by rw [e₃, f₃, one_mul]) h₃
  · refine ⟨u₃ * u₁, U.mul_mem hu₃ hu₁, ?_, ?_⟩
    · rw [hc_mul u₃ hu₃ u₁ hu₁ a haU, e₁, e₃, mul_one]
    · rw [hc_mul u₃ hu₃ u₁ hu₁ b hbU, f₁, f₃, hz2]
  · exact ⟨u₃, hu₃, e₃, f₃⟩
  · exact absurd (by rw [e₃, f₃, hz2]) h₃

variable [Finite G]

namespace XCtx

variable {T L V V₂ X : Subgroup G} {g : G}

omit [Finite G] in
theorem X_le_H3 : X ≤ lOne L V₂ ⊔ X ⊔ T := le_sup_right.trans le_sup_left

omit [Finite G] in
theorem T_le_H3 : T ≤ lOne L V₂ ⊔ X ⊔ T := le_sup_right

section Basic

variable (C : XCtx G T L V V₂ X g)
include C

theorem W_sq {w : G} (hw : w ∈ ⁅V₂, X⁆) : w ^ 2 = 1 := C.elemE.2 w (C.VXE hw)

theorem W_comm {v w : G} (hv : v ∈ ⁅V₂, X⁆) (hw : w ∈ ⁅V₂, X⁆) : v * w = w * v :=
  congrArg Subtype.val (C.elemE.1.is_comm.comm ⟨v, C.VXE hv⟩ ⟨w, C.VXE hw⟩)

theorem isMulCommutative_W : IsMulCommutative ↥⁅V₂, X⁆ :=
  ⟨⟨fun v w => Subtype.ext (C.W_comm v.2 w.2)⟩⟩

theorem exists_z : ∃ z ∈ fsuV1 T V, z ≠ 1 ∧ ∀ y ∈ fsuV1 T V, y = 1 ∨ y = z := by
  have h2 : Nat.card ↥(fsuV1 T V) = 2 := by simpa using C.s1282.v1.2.1
  obtain ⟨⟨z, hz⟩, hz1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp h2
  refine ⟨z, hz, fun h => hz1 (Subtype.ext h), fun y hy => ?_⟩
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  · exact Or.inr (congrArg Subtype.val
      (huniq ⟨y, hy⟩ fun h => hy1 (congrArg Subtype.val h)))

theorem conj_mem_V₂ {v : G} (hv : v ∈ V₂) : g⁻¹ * v * g ∈ V₂ := by
  have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem C.gV₂) v).mp hv
  simpa using this

theorem conj_z_not_mem {z : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (hV1 : ∀ y ∈ fsuV1 T V, y = 1 ∨ y = z) : g⁻¹ * z * g ∉ fsuV1 T V := by
  intro h
  have h2 : Nat.card ↥(fsuV1 T V) = 2 := by simpa using C.s1282.v1.2.1
  rcases hV1 _ h with h1 | h1
  · apply hz1
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · apply C.gH
    show g ∈ Subgroup.normalizer (fsuV1 T V : Set G)
    rw [normalizer_eq_centralizer_of_card_two h2 hz hz1, Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    calc x * g = g * (g⁻¹ * x * g) := by group
      _ = g * x := by rw [h1]

theorem exists_b : ∃ b ∈ ⁅V₂, X⁆, b ∉ V₂ := by
  by_contra h
  push Not at h
  have := Subgroup.card_le_of_le (show ⁅V₂, X⁆ ≤ V₂ from h)
  rw [C.Y.2.2.2.2.1, C.plane.1.2.1] at this
  norm_num at this

theorem U_le_H3 : fsuU T V ≤ lOne L V₂ ⊔ X ⊔ T := C.UT.trans le_sup_right

theorem oTwoUpper_p128_le : oTwoUpper (p128 T L V) ≤ lOne L V₂ := by
  rw [← oTwoUpper_oTwoUpper (p128 T L V)]
  exact oTwoUpper_mono (le_inf (L128P.oTwoUpper_p128_le C.s1282.hyp)
    ((oTwoUpper_le _).trans (L128P.p128_le_normalizer le_rfl C.plane.1)))

theorem conjU_le_H3 : CFSG.conjugate (fsuU T V) g ≤ lOne L V₂ ⊔ X ⊔ T :=
  le_sup_right.trans (C.sup_conj_eq.le.trans (sup_le
    (C.oTwoUpper_p128_le.trans (le_sup_left.trans le_sup_left)) C.U_le_H3))

end Basic

structure Coords (C : XCtx G T L V V₂ X g) where
  z : G
  b : G
  e : ↥⁅V₂, X⁆ ≃* Multiplicative (Fin 3 → ZMod 2)
  hz : z ∈ fsuV1 T V
  hz1 : z ≠ 1
  hV1 : ∀ y ∈ fsuV1 T V, y = 1 ∨ y = z
  hb : b ∈ ⁅V₂, X⁆
  hbV₂ : b ∉ V₂
  ez : e ⟨z, C.V1X hz⟩ = Multiplicative.ofAdd (Pi.single 0 1)
  ea : e ⟨g⁻¹ * z * g, C.V2X (C.conj_mem_V₂ (C.plane.2 hz))⟩ =
    Multiplicative.ofAdd (Pi.single 1 1)
  eb : e ⟨b, hb⟩ = Multiplicative.ofAdd (Pi.single 2 1)

theorem nonempty_coords (C : XCtx G T L V V₂ X g) : Nonempty C.Coords := by
  obtain ⟨z, hz, hz1, hV1⟩ := C.exists_z
  obtain ⟨b, hb, hbV₂⟩ := C.exists_b
  have : IsMulCommutative ↥⁅V₂, X⁆ := C.isMulCommutative_W
  have haV₂ : g⁻¹ * z * g ∈ V₂ := C.conj_mem_V₂ (C.plane.2 hz)
  have haV₁ := C.conj_z_not_mem hz hz1 hV1
  have hzV₂ : z ∈ V₂ := C.plane.2 hz
  have h2 : ∀ w : ↥⁅V₂, X⁆, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using C.W_sq w.2)
  have hne : ∀ {x y : G} (hx : x ∈ ⁅V₂, X⁆) (hy : y ∈ ⁅V₂, X⁆), x ≠ y →
      (⟨x, hx⟩ : ↥⁅V₂, X⁆) ≠ ⟨y, hy⟩ := fun _ _ h h' => h (congrArg Subtype.val h')
  obtain ⟨e, ez, ea, eb⟩ := exists_coords (W := ↥⁅V₂, X⁆) h2 C.Y.2.2.2.2.1
    (z := ⟨z, C.V1X hz⟩) (a := ⟨g⁻¹ * z * g, C.V2X haV₂⟩) (b := ⟨b, hb⟩)
    (fun h => hz1 (congrArg Subtype.val h))
    (fun h => haV₁ (by rw [show g⁻¹ * z * g = 1 from congrArg Subtype.val h]; exact one_mem _))
    (hne _ _ fun h => haV₁ (by rw [h]; exact hz))
    (fun h => hbV₂ (by rw [show b = 1 from congrArg Subtype.val h]; exact one_mem _))
    (hne _ _ fun h => hbV₂ (h ▸ hzV₂)) (hne _ _ fun h => hbV₂ (h ▸ haV₂))
    (fun h => hbV₂ (by
      rw [show b = z * (g⁻¹ * z * g) from congrArg Subtype.val h]
      exact mul_mem hzV₂ haV₂))
  exact ⟨⟨z, b, e, hz, hz1, hV1, hb, hbV₂, ez, ea, eb⟩⟩

variable {C : XCtx G T L V V₂ X g} (K : C.Coords)

@[expose] def conjW (C : XCtx G T L V V₂ X g) (h : ↥(lOne L V₂ ⊔ X ⊔ T)) (w : ↥⁅V₂, X⁆) :
    ↥⁅V₂, X⁆ :=
  ⟨h * w * (h : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (C.H3_le_normalizer h.2) w).mp w.2⟩

@[expose] def Coords.zW : ↥⁅V₂, X⁆ := ⟨K.z, C.V1X K.hz⟩

@[expose] def Coords.aW : ↥⁅V₂, X⁆ := ⟨g⁻¹ * K.z * g, C.V2X (C.conj_mem_V₂ (C.plane.2 K.hz))⟩

@[expose] def Coords.bW : ↥⁅V₂, X⁆ := ⟨K.b, K.hb⟩

@[expose] noncomputable def Coords.φ : ↥(lOne L V₂ ⊔ X ⊔ T) →* SL3.S :=
  repV C.H3_le_normalizer K.e

theorem Coords.toAdd_e_conjW (h : ↥(lOne L V₂ ⊔ X ⊔ T)) (w : ↥⁅V₂, X⁆) :
    Multiplicative.toAdd (K.e (conjW C h w)) =
      ((K.φ h : SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
        (Multiplicative.toAdd (K.e w)) := by
  rw [repV_mulVec C.H3_le_normalizer K.e h w (conjW C h w) rfl, toAdd_ofAdd]
  rfl

theorem Coords.φ_apply (h : ↥(lOne L V₂ ⊔ X ⊔ T)) {j : Fin 3} {w : ↥⁅V₂, X⁆}
    (hw : K.e w = Multiplicative.ofAdd (Pi.single j 1)) (i : Fin 3) :
    ((K.φ h : SL3.S) : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j =
      Multiplicative.toAdd (K.e (conjW C h w)) i := by
  rw [K.toAdd_e_conjW h w, hw, toAdd_ofAdd, Matrix.mulVec_single_one]
  rfl

theorem Coords.φ_eq (h : ↥(lOne L V₂ ⊔ X ⊔ T)) (A : SL3.S)
    (h0 : Multiplicative.toAdd (K.e (conjW C h K.zW)) =
      fun i => (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) i 0)
    (h1 : Multiplicative.toAdd (K.e (conjW C h K.aW)) =
      fun i => (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) i 1)
    (h2 : Multiplicative.toAdd (K.e (conjW C h K.bW)) =
      fun i => (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) i 2) :
    K.φ h = A := by
  ext i j
  rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) j with rfl | rfl | rfl
  · rw [K.φ_apply h K.ez i]; exact congrFun h0 i
  · rw [K.φ_apply h K.ea i]; exact congrFun h1 i
  · rw [K.φ_apply h K.eb i]; exact congrFun h2 i

theorem Coords.V₂_cases {v : G} (hv : v ∈ V₂) :
    v = 1 ∨ v = K.z ∨ v = g⁻¹ * K.z * g ∨ v = K.z * (g⁻¹ * K.z * g) :=
  C.abs.V_cases K.hz K.hz1 (C.conj_mem_V₂ (C.plane.2 K.hz)) (C.conj_z_not_mem K.hz K.hz1 K.hV1)
    v hv

theorem Coords.mem_V₂_iff (w : ↥⁅V₂, X⁆) :
    (w : G) ∈ V₂ ↔ Multiplicative.toAdd (K.e w) 2 = 0 := by
  have hz := K.ez
  have ha := K.ea
  constructor
  · intro hw
    rcases K.V₂_cases hw with h | h | h | h
    · rw [show w = 1 from Subtype.ext h, map_one]; rfl
    · rw [show w = K.zW from Subtype.ext h]; simp [Coords.zW, hz]
    · rw [show w = K.aW from Subtype.ext h]; simp [Coords.aW, ha]
    · rw [show w = K.zW * K.aW from Subtype.ext h, map_mul]
      simp [Coords.zW, Coords.aW, hz, ha]
  · intro hw
    have hzV₂ : K.z ∈ V₂ := C.plane.2 K.hz
    have haV₂ : g⁻¹ * K.z * g ∈ V₂ := C.conj_mem_V₂ hzV₂
    have hcase : ∀ c₀ c₁ : ZMod 2, Multiplicative.toAdd (K.e w) = ![c₀, c₁, 0] →
        (w : G) ∈ V₂ := by
      intro c₀ c₁ hc
      rcases zmod2_cases c₀ with rfl | rfl <;> rcases zmod2_cases c₁ with rfl | rfl
      · have : w = 1 := K.e.injective (by
          rw [map_one]; apply Multiplicative.toAdd.injective; rw [hc]; decide)
        rw [this]; exact one_mem _
      · have : w = K.aW := K.e.injective (by
          apply Multiplicative.toAdd.injective; rw [hc, Coords.aW, ha]; decide)
        rw [this]; exact haV₂
      · have : w = K.zW := K.e.injective (by
          apply Multiplicative.toAdd.injective; rw [hc, Coords.zW, hz]; decide)
        rw [this]; exact hzV₂
      · have : w = K.zW * K.aW := K.e.injective (by
          apply Multiplicative.toAdd.injective
          rw [hc, map_mul, toAdd_mul, Coords.zW, Coords.aW, hz, ha]; decide)
        rw [this]; exact mul_mem hzV₂ haV₂
    refine hcase (Multiplicative.toAdd (K.e w) 0) (Multiplicative.toAdd (K.e w) 1) ?_
    funext i
    rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i with rfl | rfl | rfl
    · rfl
    · rfl
    · exact hw

theorem Coords.inX1_of (h : ↥(lOne L V₂ ⊔ X ⊔ T))
    (hN : (h : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G)) : SL3.InX1 (K.φ h) := by
  have hfix : conjW C h K.zW = K.zW := by
    apply Subtype.ext
    have hmem : (h : G) * K.z * (h : G)⁻¹ ∈ fsuV1 T V :=
      (Subgroup.mem_normalizer_iff.mp hN K.z).mp K.hz
    rcases K.hV1 _ hmem with h1 | h1
    · exfalso
      apply K.hz1
      calc K.z = (h : G)⁻¹ * ((h : G) * K.z * (h : G)⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have h10 := K.φ_apply h K.ez 1
  have h20 := K.φ_apply h K.ez 2
  rw [show conjW C h ⟨K.z, C.V1X K.hz⟩ = K.zW from hfix] at h10 h20
  refine And.intro ?_ ?_
  · rw [h10, Coords.zW, K.ez]; rfl
  · rw [h20, Coords.zW, K.ez]; rfl

theorem Coords.inX2_of (h : ↥(lOne L V₂ ⊔ X ⊔ T))
    (hN : (h : G) ∈ Subgroup.normalizer (V₂ : Set G)) : SL3.InX2 (K.φ h) := by
  have hz : ((conjW C h K.zW : ↥⁅V₂, X⁆) : G) ∈ V₂ :=
    (Subgroup.mem_normalizer_iff.mp hN K.z).mp (C.plane.2 K.hz)
  have ha : ((conjW C h K.aW : ↥⁅V₂, X⁆) : G) ∈ V₂ :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp (C.conj_mem_V₂ (C.plane.2 K.hz))
  refine And.intro ?_ ?_
  · rw [K.φ_apply h K.ez 2]
    exact (K.mem_V₂_iff _).mp hz
  · rw [K.φ_apply h K.ea 2]
    exact (K.mem_V₂_iff _).mp ha

theorem Coords.exists_not_inX2 : ∃ h : ↥(lOne L V₂ ⊔ X ⊔ T), (h : G) ∈ X ∧
    ¬ SL3.InX2 (K.φ h) := by
  by_contra hno
  push Not at hno
  have hle : ⁅V₂, X⁆ ≤ V₂ := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    have hxH : x ∈ lOne L V₂ ⊔ X ⊔ T := X_le_H3 hx
    obtain ⟨h20, h21⟩ := hno ⟨x, hxH⟩ hx
    have hvW : v⁻¹ ∈ ⁅V₂, X⁆ := C.V2X (inv_mem hv)
    have hcoord : Multiplicative.toAdd (K.e (conjW C ⟨x, hxH⟩ ⟨v⁻¹, hvW⟩)) 2 = 0 := by
      rw [K.toAdd_e_conjW]
      have hv2 : Multiplicative.toAdd (K.e ⟨v⁻¹, hvW⟩) 2 = 0 :=
        (K.mem_V₂_iff ⟨v⁻¹, hvW⟩).mp (inv_mem hv)
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h20, h21, hv2, zero_mul,
        mul_zero, add_zero]
    have hx' := (K.mem_V₂_iff _).mpr hcoord
    rw [commutatorElement_def, show v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) by group]
    exact mul_mem hv hx'
  have := Subgroup.card_le_of_le hle
  rw [C.Y.2.2.2.2.1, C.plane.1.2.1] at this
  norm_num at this

end XCtx

end CFSG.Quasithin.H13.L14413
