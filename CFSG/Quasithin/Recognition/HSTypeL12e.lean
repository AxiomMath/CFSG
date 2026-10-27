module

public import CFSG.Quasithin.Recognition.HSTypeL12b

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem mul_self_eq_one_or_z [Finite G] (h : HSSetting z V) {q : G} (hq : q ∈ hsQ z) :
    q * q = 1 ∨ q * q = z := by
  rcases sq_eq_of_isZ4Q8Q8 h.one.fstar (z := ⟨z, h.mem_Q⟩)
      (fun x => Subtype.ext (h.comm_z_of_mem_Q x.2).symm)
      (Subtype.ext (by simpa [sq] using h.sq_z))
      (fun h1 => h.z_ne_one (congrArg Subtype.val h1)) ⟨q, hq⟩ with hc | hc
  · exact Or.inl (congrArg Subtype.val hc)
  · exact Or.inr (congrArg Subtype.val hc)

theorem z_mul_z (h : HSSetting z V) : z * z = 1 := by
  rw [← sq]
  exact h.sq_z

theorem comm_of_eq_one_or_z {c g : G} (hc : c = 1 ∨ c = z) (hg : g ∈ hsH z) :
    c * g = g * c := by
  rcases hc with rfl | rfl
  · group
  · exact (Subgroup.mem_centralizer_singleton_iff.mp hg).symm

theorem mul_self_of_eq_one_or_z (h : HSSetting z V) {c : G} (hc : c = 1 ∨ c = z) :
    c * c = 1 := by
  rcases hc with rfl | rfl
  · group
  · exact h.z_mul_z

theorem mem_ZQ_of_eq_one_or_z [Finite G] (h : HSSetting z V) {c : G} (hc : c = 1 ∨ c = z) :
    c ∈ hsZQ z := by
  rcases hc with rfl | rfl
  · exact (hsZQ z).one_mem
  · exact h.z_mem_ZQ

theorem comm_eq_one_or_z [Finite G] (h : HSSetting z V) {x y : G} (hx : x ∈ hsQ z)
    (hy : y ∈ hsQ z) : x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z := by
  have hzy : y * z = z * y := h.comm_z_of_mem_Q hy
  have hzx : x * z = z * x := h.comm_z_of_mem_Q hx
  rcases h.mul_comm_or_mul_z hx hy with hc | hc
  · left
    rw [hc]
    group
  · right
    rw [hc]
    calc y * x * z * x⁻¹ * y⁻¹ = y * (x * z * x⁻¹) * y⁻¹ := by group
      _ = y * z * y⁻¹ := by rw [hzx, mul_inv_cancel_right]
      _ = z := by rw [hzy, mul_inv_cancel_right]

theorem comm_central [Finite G] (h : HSSetting z V) {x y w : G} (hx : x ∈ hsQ z)
    (hy : y ∈ hsQ z) (hw : w ∈ hsH z) :
    x * y * x⁻¹ * y⁻¹ * w = w * (x * y * x⁻¹ * y⁻¹) :=
  comm_of_eq_one_or_z (h.comm_eq_one_or_z hx hy) hw

theorem comm_mul_left [Finite G] (h : HSSetting z V) {x₁ x₂ y : G} (hx₁ : x₁ ∈ hsQ z)
    (hx₂ : x₂ ∈ hsQ z) (hy : y ∈ hsQ z) :
    x₁ * x₂ * y * (x₁ * x₂)⁻¹ * y⁻¹ =
      (x₁ * y * x₁⁻¹ * y⁻¹) * (x₂ * y * x₂⁻¹ * y⁻¹) := by
  have hc := h.comm_central hx₂ hy (h.Q_le_H
    ((hsQ z).mul_mem ((hsQ z).mul_mem hy ((hsQ z).inv_mem hx₁)) ((hsQ z).inv_mem hy)))
  calc x₁ * x₂ * y * (x₁ * x₂)⁻¹ * y⁻¹
      = x₁ * ((x₂ * y * x₂⁻¹ * y⁻¹) * (y * x₁⁻¹ * y⁻¹)) := by group
    _ = x₁ * ((y * x₁⁻¹ * y⁻¹) * (x₂ * y * x₂⁻¹ * y⁻¹)) := by rw [hc]
    _ = (x₁ * y * x₁⁻¹ * y⁻¹) * (x₂ * y * x₂⁻¹ * y⁻¹) := by group

theorem comm_inv [Finite G] (h : HSSetting z V) {x y : G} (hx : x ∈ hsQ z) (hy : y ∈ hsQ z) :
    (x * y * x⁻¹ * y⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ :=
  inv_eq_of_mul_eq_one_left (h.mul_self_of_eq_one_or_z (h.comm_eq_one_or_z hx hy))

theorem comm_symm [Finite G] (h : HSSetting z V) {x y : G} (hx : x ∈ hsQ z) (hy : y ∈ hsQ z) :
    y * x * y⁻¹ * x⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  rw [← h.comm_inv hx hy]
  group

theorem comm_mul_right [Finite G] (h : HSSetting z V) {x y₁ y₂ : G} (hx : x ∈ hsQ z)
    (hy₁ : y₁ ∈ hsQ z) (hy₂ : y₂ ∈ hsQ z) :
    x * (y₁ * y₂) * x⁻¹ * (y₁ * y₂)⁻¹ =
      (x * y₁ * x⁻¹ * y₁⁻¹) * (x * y₂ * x⁻¹ * y₂⁻¹) := by
  rw [← h.comm_symm hx ((hsQ z).mul_mem hy₁ hy₂), h.comm_mul_left hy₁ hy₂ hx,
    h.comm_symm hy₁ hx, h.comm_symm hy₂ hx]

theorem comm_mul_central [Finite G] (h : HSSetting z V) {x y c : G} (hx : x ∈ hsQ z)
    (hy : y ∈ hsQ z) (hc : c = 1 ∨ c = z) :
    x * (c * y) * x⁻¹ * (c * y)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hcx : c * x = x * c := comm_of_eq_one_or_z hc (h.Q_le_H hx)
  have hcw := comm_of_eq_one_or_z hc (h.Q_le_H ((hsQ z).mul_mem ((hsQ z).mul_mem
    ((hsQ z).mul_mem hx hy) ((hsQ z).inv_mem hx)) ((hsQ z).inv_mem hy)))
  calc x * (c * y) * x⁻¹ * (c * y)⁻¹ = (x * c) * y * x⁻¹ * y⁻¹ * c⁻¹ := by group
    _ = c * (x * y * x⁻¹ * y⁻¹) * c⁻¹ := by rw [← hcx]; group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [hcw, mul_inv_cancel_right]

theorem comm_conj_Q [Finite G] (h : HSSetting z V) {x y b : G} (hx : x ∈ hsQ z)
    (hy : y ∈ hsQ z) (hb : b ∈ hsQ z) :
    x * (b * y * b⁻¹) * x⁻¹ * (b * y * b⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hby : b * y * b⁻¹ = (b * y * b⁻¹ * y⁻¹) * y := by group
  rw [hby]
  exact h.comm_mul_central hx hy (h.comm_eq_one_or_z hb hy)

theorem comm_conj [Finite G] (h : HSSetting z V) {a x y : G} (ha : a ∈ hsH z)
    (hx : x ∈ hsQ z) (hy : y ∈ hsQ z) :
    (a * x * a⁻¹) * (a * y * a⁻¹) * (a * x * a⁻¹)⁻¹ * (a * y * a⁻¹)⁻¹ =
      x * y * x⁻¹ * y⁻¹ := by
  have hc := h.comm_central hx hy ha
  calc (a * x * a⁻¹) * (a * y * a⁻¹) * (a * x * a⁻¹)⁻¹ * (a * y * a⁻¹)⁻¹
      = a * (x * y * x⁻¹ * y⁻¹) * a⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [← hc, mul_inv_cancel_right]

theorem conj_mem_Q {a q : G} (ha : a ∈ hsH z) (hq : q ∈ hsQ z) : a * q * a⁻¹ ∈ hsQ z :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_quasithinGenFitting (hsH z) ha) q).mp hq

theorem comm_conj_of_three [Finite G] (h : HSSetting z V) {a y : G} (ha : a ∈ hsH z)
    (ha2 : a * a ∈ hsQ z) (hyH : y ∈ hsH z) (hy : orderOf y = 3)
    (hay : y * a * y⁻¹ * a⁻¹ ∈ hsQ z) {q : G} (hq : q ∈ hsQ z) :
    q * (a * q * a⁻¹) = (a * q * a⁻¹) * q := by
  set β : G → G := fun x => x * (a * x * a⁻¹) * x⁻¹ * (a * x * a⁻¹)⁻¹ with hβdef
  have hσQ : ∀ x ∈ hsQ z, a * x * a⁻¹ ∈ hsQ z := fun x hx => conj_mem_Q ha hx
  have hβ01 : ∀ x ∈ hsQ z, β x = 1 ∨ β x = z := fun x hx => h.comm_eq_one_or_z hx (hσQ x hx)
  have hβmul : ∀ x ∈ hsQ z, ∀ x' ∈ hsQ z, β (x * x') = β x * β x' := by
    intro x hx x' hx'
    have hσx := hσQ x hx
    have hσx' := hσQ x' hx'
    have hσ : a * (x * x') * a⁻¹ = (a * x * a⁻¹) * (a * x' * a⁻¹) := by group
    have hcross : x' * (a * x * a⁻¹) * x'⁻¹ * (a * x * a⁻¹)⁻¹ =
        x * (a * x' * a⁻¹) * x⁻¹ * (a * x' * a⁻¹)⁻¹ := by
      have h1 := h.comm_conj ha hx' (hσQ x hx)
      have h2 : a * (a * x * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
      rw [h2, h.comm_conj_Q hσx' hx ha2] at h1
      rw [← h1, h.comm_symm hσx' hx]
    have hc1 := h.comm_eq_one_or_z hx hσx'
    show x * x' * (a * (x * x') * a⁻¹) * (x * x')⁻¹ * (a * (x * x') * a⁻¹)⁻¹ =
      (x * (a * x * a⁻¹) * x⁻¹ * (a * x * a⁻¹)⁻¹) *
        (x' * (a * x' * a⁻¹) * x'⁻¹ * (a * x' * a⁻¹)⁻¹)
    rw [hσ, h.comm_mul_left hx hx' ((hsQ z).mul_mem hσx hσx'), h.comm_mul_right hx hσx hσx',
      h.comm_mul_right hx' hσx hσx', hcross]
    have hcc := h.mul_self_of_eq_one_or_z hc1
    set c := x * (a * x' * a⁻¹) * x⁻¹ * (a * x' * a⁻¹)⁻¹
    set d := x' * (a * x' * a⁻¹) * x'⁻¹ * (a * x' * a⁻¹)⁻¹
    calc x * (a * x * a⁻¹) * x⁻¹ * (a * x * a⁻¹)⁻¹ * c * (c * d)
        = x * (a * x * a⁻¹) * x⁻¹ * (a * x * a⁻¹)⁻¹ * (c * c) * d := by group
      _ = x * (a * x * a⁻¹) * x⁻¹ * (a * x * a⁻¹)⁻¹ * d := by rw [hcc, mul_one]
  have hp : a * y * a⁻¹ * y⁻¹ ∈ hsQ z := by
    have := (hsQ z).inv_mem hay
    rwa [show (y * a * y⁻¹ * a⁻¹)⁻¹ = a * y * a⁻¹ * y⁻¹ by group] at this
  have hβy : ∀ x ∈ hsQ z, β (y * x * y⁻¹) = β x := by
    intro x hx
    have hyx := conj_mem_Q hyH hx
    have hyσx := conj_mem_Q hyH (hσQ x hx)
    have hσy : a * (y * x * y⁻¹) * a⁻¹ =
        (a * y * a⁻¹ * y⁻¹) * (y * (a * x * a⁻¹) * y⁻¹) * (a * y * a⁻¹ * y⁻¹)⁻¹ := by group
    show y * x * y⁻¹ * (a * (y * x * y⁻¹) * a⁻¹) * (y * x * y⁻¹)⁻¹ *
      (a * (y * x * y⁻¹) * a⁻¹)⁻¹ = x * (a * x * a⁻¹) * x⁻¹ * (a * x * a⁻¹)⁻¹
    rw [hσy, h.comm_conj_Q hyx hyσx hp, h.comm_conj hyH hx (hσQ x hx)]
  have hy3 : y * y * y = 1 := by
    calc y * y * y = y ^ 3 := by simp only [pow_succ, pow_zero, one_mul]
      _ = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hyq := conj_mem_Q hyH hq
  have hyyq := conj_mem_Q hyH hyq
  set m := (y * q * y⁻¹) * (y * (y * q * y⁻¹) * y⁻¹) with hm
  have hmQ : m ∈ hsQ z := (hsQ z).mul_mem hyq hyyq
  set r := q * m with hr
  have hrQ : r ∈ hsQ z := (hsQ z).mul_mem hq hmQ
  have hyr : y * r * y⁻¹ = m * q := by
    rw [hr, hm]
    calc y * (q * (y * q * y⁻¹ * (y * (y * q * y⁻¹) * y⁻¹))) * y⁻¹ =
        y * q * y⁻¹ * (y * (y * q * y⁻¹) * y⁻¹) * ((y * y * y) * q * (y * y * y)⁻¹) := by group
      _ = y * q * y⁻¹ * (y * (y * q * y⁻¹) * y⁻¹) * q := by rw [hy3]; group
  have hrZ : r ∈ hsZQ z := by
    refine h.mem_ZQ_of_mem_stabQ_three hrQ hy ⟨hyH, ?_⟩
    rw [hyr, hr]
    have : m * q * (q * m)⁻¹ = m * q * m⁻¹ * q⁻¹ := by group
    rw [this]
    exact h.mem_ZQ_of_eq_one_or_z (h.comm_eq_one_or_z hmQ hq)
  have hβr : β r = 1 := by
    show r * (a * r * a⁻¹) * r⁻¹ * (a * r * a⁻¹)⁻¹ = 1
    rw [(Subgroup.mem_centralizer_iff.mp hrZ.2 _ (hσQ r hrQ)).symm]
    group
  have hβr' : β r = β q * β q * β q := by
    rw [hr, hβmul q hq m hmQ, hm, hβmul _ hyq _ hyyq, hβy _ hyq, hβy _ hq]
    exact (mul_assoc _ _ _).symm
  have hq1 : β q = 1 := by
    rcases hβ01 q hq with h1 | h1
    · exact h1
    · rw [hβr', h1, h.z_mul_z, one_mul] at hβr
      exact absurd hβr h.z_ne_one
  have : q * (a * q * a⁻¹) * q⁻¹ * (a * q * a⁻¹)⁻¹ = 1 := hq1
  calc q * (a * q * a⁻¹) = q * (a * q * a⁻¹) * q⁻¹ * (a * q * a⁻¹)⁻¹ * ((a * q * a⁻¹) * q) := by
        group
    _ = (a * q * a⁻¹) * q := by rw [this, one_mul]

end HSSetting

instance normal_ZQ_subgroupOf_fixQ (z a : G) : ((hsZQ z).subgroupOf (hsFixQ z a)).Normal where
  conj_mem := fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : G) * n = n * g := Subgroup.mem_centralizer_iff.mp hn.2 g g.2.1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hc, mul_inv_cancel_right]
    exact hn

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem comm_mem_fixQ [Finite G] (h : HSSetting z V) {a q : G} (ha : a ∈ hsH z)
    (ha2 : a * a ∈ hsQ z) (hq : q ∈ hsQ z) : a * q * a⁻¹ * q⁻¹ ∈ hsFixQ z a := by
  have hσq := conj_mem_Q ha hq
  have hx : a * q * a⁻¹ * q⁻¹ ∈ hsQ z := (hsQ z).mul_mem hσq ((hsQ z).inv_mem hq)
  refine ⟨hx, ?_⟩
  have heq : a * (a * q * a⁻¹ * q⁻¹) * a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ =
      ((a * a) * q * (a * a)⁻¹ * q⁻¹) * ((q * (a * q * a⁻¹)⁻¹) * (q * (a * q * a⁻¹)⁻¹)) := by
    group
  rw [heq]
  have hy : q * (a * q * a⁻¹)⁻¹ ∈ hsQ z := (hsQ z).mul_mem hq ((hsQ z).inv_mem hσq)
  exact (hsZQ z).mul_mem (h.mem_ZQ_of_eq_one_or_z (h.comm_eq_one_or_z ha2 hq))
    (h.mem_ZQ_of_eq_one_or_z (h.mul_self_eq_one_or_z hy))

@[expose] noncomputable def commHom [Finite G] (h : HSSetting z V) {a : G} (ha : a ∈ hsH z)
    (ha2 : a * a ∈ hsQ z) :
    ↥(hsQ z) →* ↥(hsFixQ z a) ⧸ (hsZQ z).subgroupOf (hsFixQ z a) :=
  MonoidHom.mk' (fun q => QuotientGroup.mk ⟨a * q * a⁻¹ * q⁻¹, h.comm_mem_fixQ ha ha2 q.2⟩)
    (by
      intro q q'
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hq'c : a * (q' : G) * a⁻¹ * (q' : G)⁻¹ ∈ hsQ z :=
        (hsQ z).mul_mem (conj_mem_Q ha q'.2) ((hsQ z).inv_mem q'.2)
      have hmem : (a * ((q : G) * q') * a⁻¹ * ((q : G) * q')⁻¹)⁻¹ *
          (a * (q : G) * a⁻¹ * (q : G)⁻¹ * (a * (q' : G) * a⁻¹ * (q' : G)⁻¹)) ∈ hsZQ z := by
        have heq : (a * ((q : G) * q') * a⁻¹ * ((q : G) * q')⁻¹)⁻¹ *
            (a * (q : G) * a⁻¹ * (q : G)⁻¹ * (a * (q' : G) * a⁻¹ * (q' : G)⁻¹)) =
            ((a * (q' : G) * a⁻¹ * (q' : G)⁻¹)⁻¹ * q * (a * (q' : G) * a⁻¹ * (q' : G)⁻¹) *
              (q : G)⁻¹)⁻¹ := by group
        rw [heq]
        have hc := h.comm_eq_one_or_z ((hsQ z).inv_mem hq'c) q.2
        rw [inv_inv] at hc
        exact (hsZQ z).inv_mem (h.mem_ZQ_of_eq_one_or_z hc)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] using hmem)

theorem commHom_apply [Finite G] (h : HSSetting z V) {a : G} (ha : a ∈ hsH z)
    (ha2 : a * a ∈ hsQ z) (q : ↥(hsQ z)) :
    h.commHom ha ha2 q = QuotientGroup.mk ⟨a * q * a⁻¹ * q⁻¹, h.comm_mem_fixQ ha ha2 q.2⟩ :=
  rfl

theorem ker_commHom [Finite G] (h : HSSetting z V) {a : G} (ha : a ∈ hsH z)
    (ha2 : a * a ∈ hsQ z) :
    (h.commHom ha ha2).ker = (hsFixQ z a).subgroupOf (hsQ z) := by
  ext q
  rw [MonoidHom.mem_ker, commHom_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf]
  exact ⟨fun hq => ⟨q.2, hq⟩, fun hq => hq.2⟩

theorem card_fixQ_eq_and_surjective [Finite G] (h : HSSetting z V) {a : G} (ha : a ∈ hsH z)
    (haQ : a ∉ hsQ z) (ha2 : a * a ∈ hsQ z) :
    Nat.card (hsFixQ z a) = 16 ∧ Function.Surjective (h.commHom ha ha2) := by
  set D := hsFixQ z a with hD
  have hDQ : D ≤ hsQ z := fun d hd => hd.1
  have hZD : hsZQ z ≤ D := h.ZQ_le_fixQ ha
  have hle := h.card_fixQ_le ha haQ ha2
  have hker := h.ker_commHom ha ha2
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (h.commHom ha ha2).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDQ).toEquiv, h.card_Q] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((hsZQ z).subgroupOf D)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv, h.card_ZQ] at h2
  have h3 : Nat.card (h.commHom ha ha2).range ≤
      Nat.card (↥D ⧸ (hsZQ z).subgroupOf D) := Subgroup.card_le_card_group _
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have h16 : Nat.card D = 16 := by
    by_contra hne
    have hlt : Nat.card D < 16 := lt_of_le_of_ne hle hne
    have : Nat.card (↥D ⧸ (hsZQ z).subgroupOf D) < 4 := by omega
    have : Nat.card (h.commHom ha ha2).range < 4 := by omega
    nlinarith
  have hr4 : Nat.card (h.commHom ha ha2).range = 4 := by rw [h16] at h1; omega
  have hq4 : Nat.card (↥D ⧸ (hsZQ z).subgroupOf D) = 4 := by rw [h16] at h2; omega
  refine ⟨h16, ?_⟩
  rw [← MonoidHom.range_eq_top]
  exact Subgroup.eq_top_of_card_eq _ (by rw [hr4, hq4])

theorem card_fixQ_eq [Finite G] (h : HSSetting z V) {a : G} (ha : a ∈ hsH z)
    (haQ : a ∉ hsQ z) (ha2 : a * a ∈ hsQ z) : Nat.card (hsFixQ z a) = 16 :=
  (h.card_fixQ_eq_and_surjective ha haQ ha2).1

theorem exists_comm_mul_of_mem_fixQ [Finite G] (h : HSSetting z V) {a : G} (ha : a ∈ hsH z)
    (haQ : a ∉ hsQ z) (ha2 : a * a ∈ hsQ z) {d : G} (hd : d ∈ hsFixQ z a) :
    ∃ q ∈ hsQ z, ∃ u ∈ hsZQ z, d = a * q * a⁻¹ * q⁻¹ * u := by
  obtain ⟨q, hq⟩ := (h.card_fixQ_eq_and_surjective ha haQ ha2).2 (QuotientGroup.mk ⟨d, hd⟩)
  rw [commHom_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
  refine ⟨q, q.2, _, hq, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

end HSSetting

end CFSG.Quasithin.HSType
