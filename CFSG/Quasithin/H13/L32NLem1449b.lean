module

public import CFSG.Quasithin.H13.L32N1447Inputs
public import CFSG.Quasithin.H13.L32N1449Inputs
public import CFSG.Quasithin.H13.L32NLem1447g
public import CFSG.Quasithin.H13.L32NO3Model2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L1449

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B L1442M Mat8Cert
  O3Cert Q1447Cert Q1449Cert L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)}

theorem add_self_V {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (v : W) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 by decide, zero_smul]

theorem b5V_comm (v w : Fin 8 → ZMod 2) : G5Cert.b5V v w = G5Cert.b5V w v := by
  unfold G5Cert.b5V
  rw [add_comm v w]
  ring

structure Inv (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
    (Y : GL (Fin 8) (ZMod 2)) (y : G) : Prop where
  base : Base G T L V V₂ g
  form : ∀ x z : D.V, D.B x z = G5Cert.b5V (e x) (e z)
  yH : y ∈ l32nH T V
  yy : y * y = 1
  yStar : matOf e (D.ρ ⟨y, HN yH⟩) = Y
  full : fullImgB (colsOf (Y : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true
  alt : ∀ v, G5Cert.b5V ((Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) v = 0

@[expose] def rI (T V : Subgroup G) (y : G) : Subgroup G :=
  fsuU T V ⊓ Subgroup.centralizer ({y} : Set G)

@[expose] def dI (T V : Subgroup G) (y : G) : Subgroup G := rI T V y ⊔ Subgroup.zpowers y

section Basic

variable {y : G}

omit [Finite G] in
theorem rI_comm_y {r : G} (hr : r ∈ rI T V y) : r * y = y * r :=
  Subgroup.mem_centralizer_singleton_iff.mp hr.2

omit [Finite G] in
theorem y_mem_dI : y ∈ dI T V y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

omit [Finite G] in
theorem rI_le_dI : rI T V y ≤ dI T V y := le_sup_left

omit [Finite G] in
theorem rI_le_U : rI T V y ≤ fsuU T V := inf_le_left

omit [Finite G] in
theorem y_comm_rI {x : G} (hx : x * y ∈ rI T V y) : y * x = x * y := by
  have h1 := rI_comm_y hx
  calc y * x = y * (x * y) * y⁻¹ := by group
    _ = (x * y) * y * y⁻¹ := by rw [← h1]
    _ = x * y := by group

end Basic

namespace Inv

variable {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {Y : GL (Fin 8) (ZMod 2)} {y : G}
  (C : Inv G T L V V₂ g D e Y y)
include C

theorem yN : y ∈ Subgroup.normalizer (fsuU T V : Set G) := HN C.yH

theorem y_inv : y⁻¹ = y := inv_eq_of_mul_eq_one_right C.yy

theorem e_rho (v : D.V) : e (D.ρ ⟨y, C.yN⟩ v) =
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e v) := by
  have h := matOf_mulVec e (D.ρ ⟨y, C.yN⟩) v
  rw [C.yStar] at h
  exact h.symm

theorem Y_sq : Y * Y = 1 := by
  rw [← C.yStar, ← map_mul, ← map_mul]
  have e1 : (⟨y, C.yN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) * ⟨y, C.yN⟩ = 1 :=
    Subtype.ext C.yy
  rw [e1, map_one, map_one]

theorem fix_iff (v : Fin 8 → ZMod 2) :
    (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v ↔
      ∃ w, (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w + w = v := by
  refine ⟨(full_image C.full).2.1 v, ?_⟩
  rintro ⟨w, rfl⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Units.val_mul, C.Y_sq, Units.val_one,
    Matrix.one_mulVec, add_comm]

theorem rho_U {u : G} (hu : u ∈ fsuU T V) (huN : u ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨u, huN⟩ = 1 :=
  L128A.HatU.rho_eq_one_of_mem D C.base.comm_center hu huN

theorem Y_ne_one : Y ≠ 1 := by
  intro h
  have h1 := (full_image C.full).1
  rw [h] at h1
  have h2 : (Finset.univ.image fun v : Fin 8 → ZMod 2 =>
      ((1 : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v) = {0} := by
    ext w
    simp [add_self_V, eq_comm]
  rw [h2] at h1
  simp at h1

theorem y_not_mem_U : y ∉ fsuU T V := by
  intro hy
  apply C.Y_ne_one
  rw [← C.yStar, C.rho_U hy C.yN, map_one]

theorem comm_V1 {h z : G} (hh : h ∈ l32nH T V) (hz : z ∈ fsuV1 T V) : h * z = z * h := by
  obtain ⟨_, S⟩ := C.base.set14
  have hh' := hh
  rw [l32nH, normalizer_eq_centralizer_of_card_eq_two S.card_V1] at hh'
  exact (Subgroup.mem_centralizer_iff.mp hh' z hz).symm

theorem conj_mem {u : G} (hu : u ∈ fsuU T V) : y * u * y⁻¹ ∈ fsuU T V :=
  L128A.HatU.conj_mem C.yN hu

theorem comm_mem {u : G} (hu : u ∈ fsuU T V) : u * y * u⁻¹ * y⁻¹ ∈ fsuU T V := by
  have h1 := C.conj_mem ((fsuU T V).inv_mem hu)
  have := (fsuU T V).mul_mem hu h1
  simpa [mul_assoc] using this

theorem pi_comm {u : G} (hu : u ∈ fsuU T V) :
    D.π (u * y * u⁻¹ * y⁻¹) = D.π u - D.ρ ⟨y, C.yN⟩ (D.π u) := by
  have h1 := C.conj_mem ((fsuU T V).inv_mem hu)
  have e1 : u * y * u⁻¹ * y⁻¹ = u * (y * u⁻¹ * y⁻¹) := by group
  rw [e1, D.π_mul _ hu _ h1, ← D.ρ_π ⟨y, C.yN⟩ _ ((fsuU T V).inv_mem hu),
    L128A.HatU.π_inv D hu, map_neg, sub_eq_add_neg]

theorem e_pi_comm {u : G} (hu : u ∈ fsuU T V) :
    e (D.π (u * y * u⁻¹ * y⁻¹)) =
      e (D.π u) + (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π u)) := by
  rw [C.pi_comm hu, map_sub, C.e_rho]
  exact sub_eq_add_vec _ _

theorem comm_sq {u : G} (hu : u ∈ fsuU T V) :
    (u * y * u⁻¹ * y⁻¹) * (u * y * u⁻¹ * y⁻¹) = 1 := by
  set u' := y * u * y⁻¹ with hu'
  have hu'U : u' ∈ fsuU T V := C.conj_mem hu
  have hB : D.B (D.π u) (D.π u') = 0 := by
    have h1 : D.π u' = D.ρ ⟨y, C.yN⟩ (D.π u) := (D.ρ_π ⟨y, C.yN⟩ u hu).symm
    rw [C.form, h1, C.e_rho, b5V_comm]
    exact C.alt _
  have hcomm : u * u' = u' * u := by
    have h2 := (D.B_spec u hu u' hu'U).mp hB
    calc u * u' = u * u' * u⁻¹ * u'⁻¹ * (u' * u) := by group
      _ = u' * u := by rw [h2, one_mul]
  have hsq : u * u ∈ fsuV1 T V := by
    rw [← C.base.zU, ← L128A.HatU.π_eq_zero_iff D ((fsuU T V).mul_mem hu hu),
      D.π_mul _ hu _ hu]
    exact add_self_V _
  have hu'sq : u' * u' = u * u := by
    have h3 := C.comm_V1 C.yH hsq
    calc u' * u' = y * (u * u) * y⁻¹ := by rw [hu']; group
      _ = u * u * y * y⁻¹ := by rw [h3]
      _ = u * u := by group
  have hc' : u'⁻¹ * u = u * u'⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * u') * u'⁻¹ := by group
      _ = u'⁻¹ * (u' * u) * u'⁻¹ := by rw [hcomm]
      _ = u * u'⁻¹ := by group
  have hw : u * y * u⁻¹ * y⁻¹ = u * u'⁻¹ := by rw [hu']; group
  rw [hw]
  calc u * u'⁻¹ * (u * u'⁻¹) = u * (u'⁻¹ * u) * u'⁻¹ := by group
    _ = u * (u * u'⁻¹) * u'⁻¹ := by rw [hc']
    _ = (u * u) * (u' * u')⁻¹ := by group
    _ = 1 := by rw [hu'sq]; group

theorem comm_comm {u : G} (hu : u ∈ fsuU T V) :
    (u * y * u⁻¹ * y⁻¹) * y = y * (u * y * u⁻¹ * y⁻¹) := by
  have hinv : (u * y * u⁻¹ * y⁻¹)⁻¹ = u * y * u⁻¹ * y⁻¹ :=
    inv_eq_of_mul_eq_one_right (C.comm_sq hu)
  have hyy : y⁻¹ = y := C.y_inv
  have h1 : y * (u * y * u⁻¹ * y⁻¹) * y⁻¹ = (u * y * u⁻¹ * y⁻¹)⁻¹ := by
    calc y * (u * y * u⁻¹ * y⁻¹) * y⁻¹ = y * u * y * u⁻¹ * (y⁻¹ * y⁻¹) := by group
      _ = y * u * y * u⁻¹ := by rw [hyy, C.yy, mul_one]
      _ = y * u * y⁻¹ * u⁻¹ := by rw [hyy]
      _ = (u * y * u⁻¹ * y⁻¹)⁻¹ := by group
  rw [hinv] at h1
  calc (u * y * u⁻¹ * y⁻¹) * y = y * (u * y * u⁻¹ * y⁻¹) * y⁻¹ * y := by rw [h1]
    _ = y * (u * y * u⁻¹ * y⁻¹) := by group

theorem exists_comm_of_fix {u : G} (hu : u ∈ fsuU T V)
    (hfix : (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π u)) = e (D.π u)) :
    ∃ u₀ ∈ fsuU T V, ∃ ζ ∈ fsuV1 T V, u = (u₀ * y * u₀⁻¹ * y⁻¹) * ζ := by
  obtain ⟨w, hw⟩ := (C.fix_iff _).mp hfix
  obtain ⟨u₀, hu₀, hu₀w⟩ := D.π_surj (e.symm w)
  have h1 : D.π (u₀ * y * u₀⁻¹ * y⁻¹) = D.π u := by
    apply e.injective
    rw [C.e_pi_comm hu₀, hu₀w, LinearEquiv.apply_symm_apply, add_comm, hw]
  have h2 := (D.π_eq_iff _ (C.comm_mem hu₀) _ hu).mp h1
  rw [C.base.zU] at h2
  exact ⟨u₀, hu₀, _, h2, by group⟩

theorem mem_rI_iff {u : G} (hu : u ∈ fsuU T V) :
    u ∈ rI T V y ↔ (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π u)) = e (D.π u) := by
  constructor
  · rintro ⟨-, hcen⟩
    have h1 : y * u * y⁻¹ = u := by
      rw [← Subgroup.mem_centralizer_singleton_iff.mp hcen]
      group
    rw [← C.e_rho, D.ρ_π _ u hu]
    show e (D.π (y * u * y⁻¹)) = _
    rw [h1]
  · intro hfix
    refine ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    obtain ⟨u₀, hu₀, ζ, hζ, rfl⟩ := C.exists_comm_of_fix hu hfix
    have hc1 := C.comm_comm hu₀
    have hc2 := C.comm_V1 C.yH hζ
    calc (u₀ * y * u₀⁻¹ * y⁻¹) * ζ * y = (u₀ * y * u₀⁻¹ * y⁻¹) * (y * ζ) := by
          rw [mul_assoc, ← hc2]
      _ = ((u₀ * y * u₀⁻¹ * y⁻¹) * y) * ζ := by group
      _ = (y * (u₀ * y * u₀⁻¹ * y⁻¹)) * ζ := by rw [hc1]
      _ = y * ((u₀ * y * u₀⁻¹ * y⁻¹) * ζ) := by group

theorem V1_le_rI : fsuV1 T V ≤ rI T V y := fun _ hz =>
  ⟨V_le_U (C.base.plane.1.1 (C.base.plane.2 hz)),
    Subgroup.mem_centralizer_singleton_iff.mpr (C.comm_V1 C.yH hz).symm⟩

theorem rI_sq {r : G} (hr : r ∈ rI T V y) : r * r = 1 := by
  obtain ⟨_, S⟩ := C.base.set14
  have hrU := hr.1
  obtain ⟨u₀, hu₀, ζ, hζ, rfl⟩ := C.exists_comm_of_fix hrU ((C.mem_rI_iff hrU).mp hr)
  have hζU : ζ ∈ centerOf (fsuU T V) := by rw [C.base.zU]; exact hζ
  have hc := Subgroup.mem_centralizer_iff.mp hζU.2 _ (C.comm_mem hu₀)
  have hζζ : ζ * ζ = 1 := S.mul_self_V (Subgroup.mem_inf.mp hζ).1
  calc u₀ * y * u₀⁻¹ * y⁻¹ * ζ * (u₀ * y * u₀⁻¹ * y⁻¹ * ζ) =
      (u₀ * y * u₀⁻¹ * y⁻¹) * (ζ * (u₀ * y * u₀⁻¹ * y⁻¹)) * ζ := by group
    _ = (u₀ * y * u₀⁻¹ * y⁻¹) * ((u₀ * y * u₀⁻¹ * y⁻¹) * ζ) * ζ := by rw [hc]
    _ = ((u₀ * y * u₀⁻¹ * y⁻¹) * (u₀ * y * u₀⁻¹ * y⁻¹)) * (ζ * ζ) := by group
    _ = 1 := by rw [C.comm_sq hu₀, hζζ, one_mul]

theorem rI_comm {r r' : G} (hr : r ∈ rI T V y) (hr' : r' ∈ rI T V y) : r * r' = r' * r := by
  have hrU := hr.1
  have hr'U := hr'.1
  have hρρ : ∀ v, D.ρ ⟨y, C.yN⟩ (D.ρ ⟨y, C.yN⟩ v) = v := fun v => by
    apply e.injective
    rw [C.e_rho, C.e_rho, Matrix.mulVec_mulVec, ← Units.val_mul, C.Y_sq, Units.val_one,
      Matrix.one_mulVec]
  have hB : D.B (D.π r) (D.π r') = 0 := by
    obtain ⟨u₀, hu₀, ζ, hζ, hr0⟩ := C.exists_comm_of_fix hrU ((C.mem_rI_iff hrU).mp hr)
    obtain ⟨u₁, hu₁, ζ', hζ', hr1⟩ := C.exists_comm_of_fix hr'U ((C.mem_rI_iff hr'U).mp hr')
    have hz0 : ∀ {w ζ : G}, w ∈ fsuU T V → ζ ∈ fsuV1 T V → D.π (w * ζ) = D.π w := by
      intro w ζ hw hζ
      have hζU : ζ ∈ fsuU T V := V_le_U (C.base.plane.1.1 (C.base.plane.2 hζ))
      rw [D.π_mul _ hw _ hζU, (L128A.HatU.π_eq_zero_iff D hζU).mpr (by rw [C.base.zU]; exact hζ),
        add_zero]
    rw [hr0, hr1, hz0 (C.comm_mem hu₀) hζ, hz0 (C.comm_mem hu₁) hζ', C.pi_comm hu₀,
      C.pi_comm hu₁]
    set a := D.π u₀
    set b := D.π u₁
    set ρy := D.ρ ⟨y, C.yN⟩
    have h1 : D.B (ρy a) (ρy b) = D.B a b := L128A.HatU.B_rho D _ a b
    have h2 : D.B a (ρy b) = D.B (ρy a) b := by
      rw [← L128A.HatU.B_rho D ⟨y, C.yN⟩ a (ρy b), hρρ]
    have e1 : D.B (a - ρy a) (b - ρy b) =
        D.B a b - D.B a (ρy b) - (D.B (ρy a) b - D.B (ρy a) (ρy b)) := by
      rw [LinearMap.map_sub₂, map_sub, map_sub]
    rw [e1, h1, h2]
    exact (by decide : ∀ p q : ZMod 2, p - q - (q - p) = 0) _ _
  have h2 := (D.B_spec r hrU r' hr'U).mp hB
  calc r * r' = r * r' * r⁻¹ * r'⁻¹ * (r' * r) := by group
    _ = r' * r := by rw [h2, one_mul]

theorem mem_dI_iff {x : G} : x ∈ dI T V y ↔ x ∈ rI T V y ∨ x * y ∈ rI T V y := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ rI T V y ∨ x * y ∈ rI T V y}
      one_mem' := Or.inl (one_mem _)
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (mul_mem ha hb)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact mul_mem ha hb
        · refine Or.inr ?_
          have e1 : a * b * y = (a * y) * b := by
            rw [mul_assoc, rI_comm_y hb, ← mul_assoc]
          rw [e1]
          exact mul_mem ha hb
        · refine Or.inl ?_
          have e1 : a * b = (a * y) * (b * y) := by
            calc a * b = (a * y) * (y⁻¹ * b) := by group
              _ = (a * y) * (y * b) := by rw [C.y_inv]
              _ = (a * y) * (b * y) := by rw [y_comm_rI hb]
          rw [e1]
          exact mul_mem ha hb
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (inv_mem ha)
        · refine Or.inr ?_
          have e1 : a⁻¹ * y = (a * y)⁻¹ := by
            calc a⁻¹ * y = (y⁻¹ * a)⁻¹ := by group
              _ = (y * a)⁻¹ := by rw [C.y_inv]
              _ = (a * y)⁻¹ := by rw [y_comm_rI ha]
          rw [e1]
          exact inv_mem ha }
  have hyS : y ∈ S := Or.inr (by rw [C.yy]; exact one_mem _)
  have hle : dI T V y ≤ S :=
    sup_le (fun r hr => Or.inl hr) ((Subgroup.zpowers_le).mpr hyS)
  constructor
  · exact fun hx => hle hx
  · rintro (hx | hx)
    · exact Subgroup.mem_sup_left hx
    · have e1 : x = (x * y) * y⁻¹ := by group
      rw [e1]
      exact mul_mem (Subgroup.mem_sup_left hx)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)))

theorem exists_rI_of_dI {w : G} (hw : w ∈ dI T V y) :
    ∃ r ∈ rI T V y, w = r ∨ w = r * y := by
  rcases C.mem_dI_iff.mp hw with h | h
  · exact ⟨w, h, Or.inl rfl⟩
  · exact ⟨w * y, h, Or.inr (by rw [mul_assoc, C.yy, mul_one])⟩

theorem dI_comm {x x' : G} (hx : x ∈ dI T V y) (hx' : x' ∈ dI T V y) : x * x' = x' * x := by
  have hy : ∀ r ∈ rI T V y, Commute r y := fun r hr => rI_comm_y hr
  have hcr : ∀ w ∈ dI T V y, ∀ r ∈ rI T V y, Commute w r := by
    intro w hw r hr
    obtain ⟨r₀, hr₀, h | h⟩ := C.exists_rI_of_dI hw
    · rw [h]
      exact C.rI_comm hr₀ hr
    · rw [h]
      exact (show Commute r₀ r from C.rI_comm hr₀ hr).mul_left (hy r hr).symm
  have hcy : ∀ w ∈ dI T V y, Commute w y := by
    intro w hw
    obtain ⟨r₀, hr₀, h | h⟩ := C.exists_rI_of_dI hw
    · rw [h]
      exact hy r₀ hr₀
    · rw [h]
      exact (hy r₀ hr₀).mul_left (Commute.refl y)
  obtain ⟨r', hr', h | h⟩ := C.exists_rI_of_dI hx'
  · rw [h]
    exact (hcr x hx r' hr').eq
  · rw [h]
    exact ((hcr x hx r' hr').mul_right (hcy x hx)).eq

theorem dI_sq {x : G} (hx : x ∈ dI T V y) : x * x = 1 := by
  rcases C.mem_dI_iff.mp hx with h | h
  · exact C.rI_sq h
  · have e1 : x = (x * y) * y⁻¹ := by group
    rw [e1, C.y_inv]
    calc x * y * y * (x * y * y) = (x * y) * (y * (x * y)) * y := by group
      _ = (x * y) * ((x * y) * y) * y := by rw [rI_comm_y h]
      _ = ((x * y) * (x * y)) * (y * y) := by group
      _ = 1 := by rw [C.rI_sq h, C.yy, one_mul]

theorem U_le_normalizer_dI : fsuU T V ≤ Subgroup.normalizer (dI T V y : Set G) := by
  have key : ∀ u ∈ fsuU T V, ∀ x ∈ dI T V y, u * x * u⁻¹ ∈ dI T V y := by
    intro u hu x hx
    have hR : ∀ r ∈ rI T V y, u * r * u⁻¹ ∈ rI T V y := by
      intro r hr
      have hrU := hr.1
      have h1 : u * r * u⁻¹ ∈ fsuU T V :=
        (fsuU T V).mul_mem ((fsuU T V).mul_mem hu hrU) ((fsuU T V).inv_mem hu)
      refine (C.mem_rI_iff h1).mpr ?_
      have h2 : D.π (u * r * u⁻¹) = D.π r := by
        rw [← D.ρ_π ⟨u, Subgroup.le_normalizer hu⟩ r hrU, C.rho_U hu _]
        rfl
      rw [h2]
      exact (C.mem_rI_iff hrU).mp hr
    rcases C.mem_dI_iff.mp hx with h | h
    · exact rI_le_dI (hR x h)
    · have hw : u * y * u⁻¹ * y⁻¹ ∈ rI T V y :=
        ⟨C.comm_mem hu, Subgroup.mem_centralizer_singleton_iff.mpr (C.comm_comm hu)⟩
      refine C.mem_dI_iff.mpr (Or.inr ?_)
      have e1 : u * x * u⁻¹ * y = (u * (x * y) * u⁻¹) * (u * y * u⁻¹ * y⁻¹) := by
        calc u * x * u⁻¹ * y = u * (x * y) * u⁻¹ * (u * y⁻¹ * u⁻¹) * y := by group
          _ = u * (x * y) * u⁻¹ * (u * y * u⁻¹) * y := by rw [C.y_inv]
          _ = (u * (x * y) * u⁻¹) * (u * y * u⁻¹ * y⁻¹) := by rw [C.y_inv]; group
      rw [e1]
      exact mul_mem (hR _ h) hw
  intro u hu
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key u hu x, fun hx => ?_⟩
  have := key u⁻¹ ((fsuU T V).inv_mem hu) _ hx
  simpa [mul_assoc] using this

end Inv

@[expose] noncomputable def piHom {U : Subgroup G} (D : HatModelU U) :
    ↥U →* Multiplicative D.V where
  toFun u := Multiplicative.ofAdd (D.π u)
  map_one' := by
    show Multiplicative.ofAdd (D.π 1) = 1
    rw [L128A.HatU.π_one]
    rfl
  map_mul' u v := by
    show Multiplicative.ofAdd (D.π (u * v)) =
      Multiplicative.ofAdd (D.π u) * Multiplicative.ofAdd (D.π v)
    rw [D.π_mul _ u.2 _ v.2]
    rfl

omit [Finite G] in
theorem card_eq_mul_card_range {U X : Subgroup G} (D : HatModelU U) (hXU : X ≤ U)
    (hZX : centerOf U ≤ X) :
    Nat.card X = Nat.card (centerOf U) *
      Nat.card ((piHom D).comp (Subgroup.inclusion hXU)).range := by
  set f := (piHom D).comp (Subgroup.inclusion hXU) with hf
  have hker : f.ker = (centerOf U).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (D.π (x : G)) = 1 ↔ _
    rw [← L128A.HatU.π_eq_zero_iff D (hXU x.2)]
    exact ⟨fun h => by simpa using congrArg Multiplicative.toAdd h,
      fun h => by rw [h]; rfl⟩
  rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX).toEquiv]

omit [Finite G] in
theorem mem_range_piHom {U X : Subgroup G} (D : HatModelU U) (hXU : X ≤ U) (v : D.V) :
    Multiplicative.ofAdd v ∈ ((piHom D).comp (Subgroup.inclusion hXU)).range ↔
      ∃ x ∈ X, D.π x = v := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, x.2, congrArg Multiplicative.toAdd hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem card_fix_Y {Y : GL (Fin 8) (ZMod 2)}
    (hfull : fullImgB (colsOf (Y : Matrix (Fin 8) (Fin 8) (ZMod 2))) = true)
    (hYY : Y * Y = 1) :
    Nat.card {w : Fin 8 → ZMod 2 // (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w = w} = 16 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 := (full_image hfull).1
  refine Eq.trans ?_ h1
  refine congrArg Finset.card ?_
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hw
    exact (full_image hfull).2.1 w hw
  · rintro ⟨v, rfl⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Units.val_mul, hYY, Units.val_one,
      Matrix.one_mulVec, add_comm]

namespace Inv

variable {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {Y : GL (Fin 8) (ZMod 2)} {y : G}
  (C : Inv G T L V V₂ g D e Y y)
include C

theorem card_rI : Nat.card (rI T V y) = 32 := by
  have hZ : centerOf (fsuU T V) ≤ rI T V y := by
    rw [C.base.zU]
    exact C.V1_le_rI
  have hrU : rI T V y ≤ fsuU T V := rI_le_U
  rw [card_eq_mul_card_range D hrU hZ]
  have hZ2 : Nat.card (centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact C.base.ext.2.2.2
  rw [hZ2]
  have h16 : Nat.card ((piHom D).comp (Subgroup.inclusion hrU)).range = 16 := by
    rw [← card_fix_Y C.full C.Y_sq]
    refine Nat.card_congr ?_
    refine
      { toFun := fun m => ⟨e (Multiplicative.toAdd (m : Multiplicative D.V)), ?_⟩
        invFun := fun w => ⟨Multiplicative.ofAdd (e.symm w), ?_⟩
        left_inv := fun m => by ext; simp
        right_inv := fun w => by ext; simp }
    · obtain ⟨x, hx, hxv⟩ := (mem_range_piHom D hrU _).mp
        (show Multiplicative.ofAdd (Multiplicative.toAdd (m : Multiplicative D.V)) ∈ _ from m.2)
      rw [← hxv]
      exact (C.mem_rI_iff hx.1).mp hx
    · obtain ⟨u, hu, hue⟩ := D.π_surj (e.symm (w : Fin 8 → ZMod 2))
      have hfix : (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π u)) = e (D.π u) := by
        rw [hue, LinearEquiv.apply_symm_apply]
        exact w.2
      exact (mem_range_piHom D hrU _).mpr ⟨u, (C.mem_rI_iff hu).mpr hfix, hue⟩
  rw [h16]

theorem card_dI : Nat.card (dI T V y) = 64 := by
  have hN : Subgroup.zpowers y ≤ Subgroup.normalizer (rI T V y : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun r => ⟨fun hr => ?_, fun hr => ?_⟩
    · rw [show y * r * y⁻¹ = r by rw [← rI_comm_y hr]; group]
      exact hr
    · have h2 := rI_comm_y hr
      have h3 : r = y * r * y⁻¹ := by
        calc r = y⁻¹ * ((y * r * y⁻¹) * y) := by group
          _ = y⁻¹ * (y * (y * r * y⁻¹)) := by rw [h2]
          _ = y * r * y⁻¹ := by group
      rw [h3]
      exact hr
  have h1 := L32NSet14.card_sup_mul_card_inf hN
  rw [sup_comm] at h1
  have hinf : Subgroup.zpowers y ⊓ rI T V y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx1
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [Subgroup.mem_bot, show m + m = 2 * m by ring, zpow_mul]
      rw [show y ^ (2 : ℤ) = 1 by rw [zpow_two, C.yy], one_zpow]
    · exfalso
      rw [zpow_add, zpow_mul, show y ^ (2 : ℤ) = 1 by rw [zpow_two, C.yy], one_zpow, one_mul,
        zpow_one] at hx2
      exact C.y_not_mem_U hx2.1
  have hy2 : Nat.card (Subgroup.zpowers y) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq, C.yy]) (fun h => C.y_not_mem_U (h ▸ one_mem _))
  rw [hinf, Subgroup.card_bot, mul_one, hy2, C.card_rI] at h1
  show Nat.card ↥(rI T V y ⊔ Subgroup.zpowers y) = 64
  omega

end Inv

end CFSG.Quasithin.H13.L1449
