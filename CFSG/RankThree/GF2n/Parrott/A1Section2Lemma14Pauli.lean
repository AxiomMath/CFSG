module

public import CFSG.Quasithin.Recognition.U33Defs
import all CFSG.Quasithin.Recognition.U33Defs
public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma13Sylow

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

open CFSG CFSG.Open QuotientV CFSG.Quasithin
open Subgroup (zpowers)
open scoped commutatorElement

section Pauli

variable {K : Type*} [Group K] {i X Y : K}

theorem pauli_Y_mul_X_pow (hiX : i * X = X * i) (hYX : Y * X = i ^ 2 * X * Y) (n : ℕ) :
    Y * X ^ n = i ^ (2 * n) * X ^ n * Y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hiXn : i ^ 2 * X ^ n = X ^ n * i ^ 2 :=
      ((Commute.pow_left (show Commute i X from hiX) 2).pow_right n).eq
    calc Y * X ^ (n + 1) = (Y * X ^ n) * X := by rw [pow_succ, mul_assoc]
      _ = i ^ (2 * n) * X ^ n * (Y * X) := by rw [ih]; group
      _ = i ^ (2 * n) * X ^ n * (i ^ 2 * X * Y) := by rw [hYX]
      _ = i ^ (2 * n) * (X ^ n * i ^ 2) * X * Y := by group
      _ = i ^ (2 * n) * (i ^ 2 * X ^ n) * X * Y := by rw [hiXn]
      _ = i ^ (2 * (n + 1)) * X ^ (n + 1) * Y := by group

theorem pauli_Y_pow_mul_X_pow (hiX : i * X = X * i) (hiY : i * Y = Y * i)
    (hYX : Y * X = i ^ 2 * X * Y) (c b : ℕ) :
    Y ^ c * X ^ b = i ^ (2 * (c * b)) * X ^ b * Y ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hYi : Y * i ^ (2 * (c * b)) = i ^ (2 * (c * b)) * Y :=
      ((Commute.pow_left (show Commute i Y from hiY) _).eq).symm
    have hiXb : i ^ (2 * b) * X ^ b = X ^ b * i ^ (2 * b) :=
      ((Commute.pow_left (show Commute i X from hiX) _).pow_right b).eq
    calc Y ^ (c + 1) * X ^ b = Y * (Y ^ c * X ^ b) := by rw [pow_succ', mul_assoc]
      _ = Y * (i ^ (2 * (c * b)) * X ^ b * Y ^ c) := by rw [ih]
      _ = (Y * i ^ (2 * (c * b))) * X ^ b * Y ^ c := by group
      _ = (i ^ (2 * (c * b)) * Y) * X ^ b * Y ^ c := by rw [hYi]
      _ = i ^ (2 * (c * b)) * (Y * X ^ b) * Y ^ c := by group
      _ = i ^ (2 * (c * b)) * (i ^ (2 * b) * X ^ b * Y) * Y ^ c := by
          rw [pauli_Y_mul_X_pow hiX hYX b]
      _ = i ^ (2 * ((c + 1) * b)) * X ^ b * Y ^ (c + 1) := by
          rw [show 2 * ((c + 1) * b) = 2 * (c * b) + 2 * b by ring]
          group

theorem pauli_word_mul (hiX : i * X = X * i) (hiY : i * Y = Y * i)
    (hYX : Y * X = i ^ 2 * X * Y) (A B C A' B' C' : ℕ) :
    (i ^ A * X ^ B * Y ^ C) * (i ^ A' * X ^ B' * Y ^ C') =
      i ^ (A + A' + 2 * (C * B')) * X ^ (B + B') * Y ^ (C + C') := by
  have h1 : Y ^ C * i ^ A' = i ^ A' * Y ^ C :=
    ((Commute.pow_pow (show Commute i Y from hiY) A' C).eq).symm
  have h2 := pauli_Y_pow_mul_X_pow hiX hiY hYX C B'
  have h3 : X ^ B * i ^ (A' + 2 * (C * B')) = i ^ (A' + 2 * (C * B')) * X ^ B :=
    ((Commute.pow_pow (show Commute i X from hiX) _ B).eq).symm
  calc (i ^ A * X ^ B * Y ^ C) * (i ^ A' * X ^ B' * Y ^ C')
      = i ^ A * X ^ B * (Y ^ C * i ^ A') * X ^ B' * Y ^ C' := by group
    _ = i ^ A * X ^ B * (i ^ A' * Y ^ C) * X ^ B' * Y ^ C' := by rw [h1]
    _ = i ^ A * X ^ B * i ^ A' * (Y ^ C * X ^ B') * Y ^ C' := by group
    _ = i ^ A * X ^ B * i ^ A' * (i ^ (2 * (C * B')) * X ^ B' * Y ^ C) * Y ^ C' := by rw [h2]
    _ = i ^ A * (X ^ B * i ^ (A' + 2 * (C * B'))) * X ^ B' * (Y ^ C * Y ^ C') := by group
    _ = i ^ A * (i ^ (A' + 2 * (C * B')) * X ^ B) * X ^ B' * (Y ^ C * Y ^ C') := by rw [h3]
    _ = i ^ (A + A' + 2 * (C * B')) * X ^ (B + B') * Y ^ (C + C') := by group

@[expose] noncomputable def pauliHom (hi4 : i ^ 4 = 1) (hX2 : X ^ 2 = 1) (hY2 : Y ^ 2 = 1)
    (hiX : i * X = X * i) (hiY : i * Y = Y * i) (hYX : Y * X = i ^ 2 * X * Y) :
    Z4StarQ8Model →* K :=
  MonoidHom.mk' (fun m => i ^ m.a.val * X ^ m.b.val * Y ^ m.c.val) (fun m m' => by
    change i ^ (m.a + m'.a + 2 * ((m.c.val * m'.b.val : ℕ) : ZMod 4)).val *
        X ^ (m.b + m'.b).val * Y ^ (m.c + m'.c).val =
      (i ^ m.a.val * X ^ m.b.val * Y ^ m.c.val) * (i ^ m'.a.val * X ^ m'.b.val * Y ^ m'.c.val)
    rw [pauli_word_mul hiX hiY hYX]
    have ea : (m.a + m'.a + 2 * ((m.c.val * m'.b.val : ℕ) : ZMod 4)).val =
        (m.a.val + m'.a.val + 2 * (m.c.val * m'.b.val)) % 4 := by
      rw [ZMod.val_add, ZMod.val_add, ZMod.val_mul, ZMod.val_natCast,
        show (2 : ZMod 4).val = 2 from rfl]
      generalize m.c.val * m'.b.val = k
      omega
    rw [ea, ZMod.val_add, ZMod.val_add, ← pow_eq_pow_mod _ hi4, ← pow_eq_pow_mod _ hX2,
      ← pow_eq_pow_mod _ hY2])

theorem pauliHom_apply (hi4 : i ^ 4 = 1) (hX2 : X ^ 2 = 1) (hY2 : Y ^ 2 = 1)
    (hiX : i * X = X * i) (hiY : i * Y = Y * i) (hYX : Y * X = i ^ 2 * X * Y)
    (m : Z4StarQ8Model) :
    pauliHom hi4 hX2 hY2 hiX hiY hYX m = i ^ m.a.val * X ^ m.b.val * Y ^ m.c.val := rfl

theorem pauli_cases_of_ne_one : ∀ m : Z4StarQ8Model, m ≠ 1 →
    m = ⟨2, 0, 0⟩ ∨ m * m = ⟨2, 0, 0⟩ ∨ ∃ m' : Z4StarQ8Model, m * m' * m⁻¹ * m'⁻¹ = ⟨2, 0, 0⟩ := by
  decide +kernel

theorem pauliHom_injective (hi4 : i ^ 4 = 1) (hX2 : X ^ 2 = 1) (hY2 : Y ^ 2 = 1)
    (hiX : i * X = X * i) (hiY : i * Y = Y * i) (hYX : Y * X = i ^ 2 * X * Y)
    (hi2 : i ^ 2 ≠ 1) : Function.Injective (pauliHom hi4 hX2 hY2 hiX hiY hYX) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  by_contra hm1
  have hz : pauliHom hi4 hX2 hY2 hiX hiY hYX ⟨2, 0, 0⟩ = i ^ 2 := by
    rw [pauliHom_apply]
    simp
    rfl
  rcases pauli_cases_of_ne_one m hm1 with h | h | ⟨m', h⟩
  · rw [h, hz] at hm
    exact hi2 hm
  · have h' := congrArg (pauliHom hi4 hX2 hY2 hiX hiY hYX) h
    rw [map_mul, hm, one_mul, hz] at h'
    exact hi2 h'.symm
  · have h' := congrArg (pauliHom hi4 hX2 hY2 hiX hiY hYX) h
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hm, hz] at h'
    simp only [one_mul, inv_one, mul_one, mul_inv_cancel] at h'
    exact hi2 h'.symm

theorem range_pauliHom_le (hi4 : i ^ 4 = 1) (hX2 : X ^ 2 = 1) (hY2 : Y ^ 2 = 1)
    (hiX : i * X = X * i) (hiY : i * Y = Y * i) (hYX : Y * X = i ^ 2 * X * Y)
    {S : Subgroup K} (hi : i ∈ S) (hX : X ∈ S) (hY : Y ∈ S) :
    (pauliHom hi4 hX2 hY2 hiX hiY hYX).range ≤ S := by
  rintro _ ⟨m, rfl⟩
  rw [pauliHom_apply]
  exact S.mul_mem (S.mul_mem (S.pow_mem hi _) (S.pow_mem hX _)) (S.pow_mem hY _)

end Pauli

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] def centModZ (z w : G) : Subgroup G where
  carrier := {b | b ∈ H z ∧ b * w * b⁻¹ * w⁻¹ ∈ zpowers z}
  one_mem' := ⟨(H z).one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
    refine ⟨(H z).mul_mem haH hbH, ?_⟩
    set d := b * w * b⁻¹ * w⁻¹ with hd
    have had : a * d * a⁻¹ = d := conj_eq_of_mem_zpowers haH hb
    have e : a * b * w * (a * b)⁻¹ * w⁻¹ = (a * d * a⁻¹) * (a * w * a⁻¹ * w⁻¹) := by
      rw [hd]; group
    rw [e, had]
    exact (zpowers z).mul_mem hb ha
  inv_mem' := by
    rintro b ⟨hbH, hb⟩
    refine ⟨(H z).inv_mem hbH, ?_⟩
    have e : b⁻¹ * w * b⁻¹⁻¹ * w⁻¹ = b⁻¹ * (b * w * b⁻¹ * w⁻¹)⁻¹ * b⁻¹⁻¹ := by group
    rw [e, conj_eq_of_mem_zpowers ((H z).inv_mem hbH) ((zpowers z).inv_mem hb)]
    exact (zpowers z).inv_mem hb

omit [Finite G] in
theorem mem_centModZ {w b : G} : b ∈ centModZ z w ↔ b ∈ H z ∧ b * w * b⁻¹ * w⁻¹ ∈ zpowers z :=
  Iff.rfl

namespace Hyp

variable {s1 s2 : G} (hy : Hyp z s1 s2)
include hy

theorem exists_pauli {M : Subgroup G} (hMJ : M ≤ J z) (hM : 32 ≤ Nat.card M)
    (hZ : ∀ a ∈ M, (∀ b ∈ M, a * b = b * a) → a ∈ zpowers z) :
    ∃ i ∈ M, ∃ X ∈ M, ∃ Y ∈ M, i * i = z ∧ X * X = 1 ∧ Y * Y = 1 ∧ i * X = X * i ∧
      i * Y = Y * i ∧ X * Y * X⁻¹ * Y⁻¹ = z := by
  have hi : ∃ i ∈ M, i * i = z := by
    by_contra hcon
    push Not at hcon
    have hsq : ∀ a ∈ M, a * a = 1 := fun a ha =>
      (hy.mem_zpowers_z_iff.mp (hy.sq_mem (hMJ ha))).resolve_right (hcon a ha)
    have hle : M ≤ zpowers z := by
      intro a ha
      apply hZ a ha
      intro b hb
      have h1 := hsq _ (M.mul_mem ha hb)
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
      have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
      calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [ha', hb']
    have := Subgroup.card_le_of_le hle
    rw [hy.card_zpowers_z] at this
    omega
  obtain ⟨i, hiM, hi2⟩ := hi
  have hiJ : i ∈ J z := hMJ hiM
  obtain ⟨a, haM, b, hbM, hai, hbi, hab⟩ := hy.exists_not_commute_of_le_J hMJ hM hZ hiJ
  have haJ : a ∈ J z := hMJ haM
  have hbJ : b ∈ J z := hMJ hbM
  have hcomm : a * b * a⁻¹ * b⁻¹ = z := by
    rcases hy.mem_zpowers_z_iff.mp (hy.comm_mem haJ hbJ) with h | h
    · exfalso
      apply hab
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h, one_mul]
    · exact h
  have hia : i * a = a * i := hai.symm
  have hib : i * b = b * i := hbi.symm
  have hfix : ∀ c : G, c ∈ M → c ∈ J z → i * c = c * i →
      ∃ c' ∈ M, c' * c' = 1 ∧ i * c' = c' * i ∧ (c' = c ∨ c' = c * i) := by
    intro c hcM hcJ hic
    rcases hy.mem_zpowers_z_iff.mp (hy.sq_mem hcJ) with h | h
    · exact ⟨c, hcM, h, hic, Or.inl rfl⟩
    · refine ⟨c * i, M.mul_mem hcM hiM, ?_, ?_, Or.inr rfl⟩
      · calc c * i * (c * i) = c * (i * c) * i := by group
          _ = c * (c * i) * i := by rw [hic]
          _ = (c * c) * (i * i) := by group
          _ = 1 := by rw [h, hi2, hy.z_sq]
      · calc i * (c * i) = (i * c) * i := by group
          _ = (c * i) * i := by rw [hic]
  obtain ⟨X, hXM, hX2, hiX, hXa⟩ := hfix a haM haJ hia
  obtain ⟨Y, hYM, hY2, hiY, hYb⟩ := hfix b hbM hbJ hib
  refine ⟨i, hiM, X, hXM, Y, hYM, hi2, hX2, hY2, hiX, hiY, ?_⟩
  have hia' : i⁻¹ * a = a * i⁻¹ := by
    calc i⁻¹ * a = i⁻¹ * (a * i) * i⁻¹ := by group
      _ = i⁻¹ * (i * a) * i⁻¹ := by rw [hia]
      _ = a * i⁻¹ := by group
  have hib' : i⁻¹ * b = b * i⁻¹ := by
    calc i⁻¹ * b = i⁻¹ * (b * i) * i⁻¹ := by group
      _ = i⁻¹ * (i * b) * i⁻¹ := by rw [hib]
      _ = b * i⁻¹ := by group
  rcases hXa with rfl | rfl <;> rcases hYb with rfl | rfl
  · exact hcomm
  · calc X * (b * i) * X⁻¹ * (b * i)⁻¹ = X * b * (i * X⁻¹ * i⁻¹) * b⁻¹ := by group
      _ = X * b * X⁻¹ * b⁻¹ := by
          rw [show i * X⁻¹ * i⁻¹ = X⁻¹ from by
            calc i * X⁻¹ * i⁻¹ = (i * X * i⁻¹)⁻¹ := by group
              _ = X⁻¹ := by rw [hia, mul_inv_cancel_right]]
      _ = z := hcomm
  · calc a * i * Y * (a * i)⁻¹ * Y⁻¹ = a * (i * Y * i⁻¹) * a⁻¹ * Y⁻¹ := by group
      _ = a * Y * a⁻¹ * Y⁻¹ := by rw [hib, mul_inv_cancel_right]
      _ = z := hcomm
  · calc a * i * (b * i) * (a * i)⁻¹ * (b * i)⁻¹
        = a * (i * b * i⁻¹) * (i * a⁻¹ * i⁻¹) * b⁻¹ := by group
      _ = a * b * a⁻¹ * b⁻¹ := by
          rw [hib, mul_inv_cancel_right]
          rw [show i * a⁻¹ * i⁻¹ = a⁻¹ from by
            calc i * a⁻¹ * i⁻¹ = (i * a * i⁻¹)⁻¹ := by group
              _ = a⁻¹ := by rw [hia, mul_inv_cancel_right]]
      _ = z := hcomm

theorem mem_CJs_sup_zpowers_cases {r : G} (hrC : ∀ c ∈ CJ z (s1 * s2⁻¹), r * c = c * r)
    (hr2 : r * r = z) {m : G} (hm : m ∈ CJ z (s1 * s2⁻¹) ⊔ zpowers r) :
    m ∈ CJ z (s1 * s2⁻¹) ∨ ∃ c ∈ CJ z (s1 * s2⁻¹), m = c * r := by
  have hn : zpowers r ≤ Subgroup.normalizer (CJ z (s1 * s2⁻¹) : Set G) := by
    apply le_normalizer_of_commute
    intro ρ hρ c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hρ
    exact (Commute.zpow_left (show Commute r c from hrC c hc) k).eq
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hm
  obtain ⟨c, hc, ρ, hρ, rfl⟩ := hm
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hρ
  have hzC : ∀ j : ℤ, z ^ j ∈ CJ z (s1 * s2⁻¹) := fun j =>
    hy.zpowers_le_CJs (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) j)
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    obtain ⟨j, rfl⟩ : (2 : ℤ) ∣ k := Int.dvd_of_emod_eq_zero hk
    rw [zpow_mul, show r ^ (2 : ℤ) = z by rw [zpow_two, hr2]]
    exact (CJ z (s1 * s2⁻¹)).mul_mem hc (hzC j)
  · right
    refine ⟨c * z ^ (k / 2), (CJ z (s1 * s2⁻¹)).mul_mem hc (hzC _), ?_⟩
    have hk' : k = 2 * (k / 2) + 1 := by omega
    conv_lhs => rw [hk', zpow_add, zpow_mul, show r ^ (2 : ℤ) = z by rw [zpow_two, hr2],
      zpow_one]
    group

theorem exists_z4q8 {c₁ r e : G} (hc₁H : c₁ ∈ H z)
    (hc₁C : ∀ c ∈ CJ z (s1 * s2⁻¹), c₁ * c = c * c₁) (hrR : r ∈ hy.R) (hr2 : r * r = z)
    (hc₁r : c₁ * r * c₁⁻¹ * r⁻¹ = z) (he : e ∈ CJ z (s1 * s2⁻¹)) :
    ∃ K : Subgroup G, K ≤ J z ∧ K ≤ Subgroup.centralizer ({c₁ * e} : Set G) ∧
      ∃ eK : ↥K ≃* Z4StarQ8Model, ((eK.symm ⟨2, 0, 0⟩ : ↥K) : G) = z := by
  set C := CJ z (s1 * s2⁻¹) with hC
  set x := c₁ * e with hx
  have hrJ : r ∈ J z := hy.R_le_J hrR
  have heJ : e ∈ J z := (CJ_le_J _) he
  have hxH : x ∈ H z := (H z).mul_mem hc₁H (J_le_H heJ)
  have hrC : ∀ c ∈ C, r * c = c * r := fun c hc => (hy.commute_CJs_R c hc r hrR).symm
  have hz1 : z ≠ 1 := by
    intro h
    have := hy.orderOf_z
    rw [h, orderOf_one] at this
    omega
  have hc₁r' : c₁ * r * c₁⁻¹ = z * r := by
    calc c₁ * r * c₁⁻¹ = (c₁ * r * c₁⁻¹ * r⁻¹) * r := by group
      _ = z * r := by rw [hc₁r]
  have hzc : ∀ g ∈ H z, g * z = z * g := fun g hg => commute_z_of_mem_H hg
  have hxc : ∀ c ∈ C, x * c * x⁻¹ = e * c * e⁻¹ := by
    intro c hc
    have hc₁ec : c₁ * (e * c * e⁻¹) = (e * c * e⁻¹) * c₁ :=
      hc₁C _ ((CJ z (s1 * s2⁻¹)).mul_mem ((CJ z (s1 * s2⁻¹)).mul_mem he hc)
        ((CJ z (s1 * s2⁻¹)).inv_mem he))
    calc x * c * x⁻¹ = c₁ * (e * c * e⁻¹) * c₁⁻¹ := by rw [hx]; group
      _ = (e * c * e⁻¹) * c₁ * c₁⁻¹ := by rw [hc₁ec]
      _ = e * c * e⁻¹ := by group
  have hxr : x * r * x⁻¹ = z * r := by
    have her : e * r = r * e := (hrC e he).symm
    calc x * r * x⁻¹ = c₁ * (e * r) * e⁻¹ * c₁⁻¹ := by rw [hx]; group
      _ = c₁ * (r * e) * e⁻¹ * c₁⁻¹ := by rw [her]
      _ = c₁ * r * c₁⁻¹ := by group
      _ = z * r := hc₁r'
  have hxcr : ∀ c ∈ C, x * (c * r) * x⁻¹ = (e * c * e⁻¹) * (z * r) := by
    intro c hc
    calc x * (c * r) * x⁻¹ = (x * c * x⁻¹) * (x * r * x⁻¹) := by group
      _ = (e * c * e⁻¹) * (z * r) := by rw [hxc c hc, hxr]
  set B := C ⊔ zpowers r with hB
  have hBJ : B ≤ J z := sup_le (CJ_le_J _) (Subgroup.zpowers_le.mpr hrJ)
  have hBw : B ≤ centModZ z x := by
    apply sup_le
    · intro c hc
      refine mem_centModZ.mpr ⟨J_le_H ((CJ_le_J _) hc), ?_⟩
      have e1 : c * x * c⁻¹ * x⁻¹ = c * (x * c * x⁻¹)⁻¹ := by group
      rw [e1, hxc c hc]
      have e2 : c * (e * c * e⁻¹)⁻¹ = c * e * c⁻¹ * e⁻¹ := by group
      rw [e2]
      exact hy.comm_mem ((CJ_le_J _) hc) heJ
    · rw [Subgroup.zpowers_le]
      refine mem_centModZ.mpr ⟨J_le_H hrJ, ?_⟩
      have e1 : r * x * r⁻¹ * x⁻¹ = r * (x * r * x⁻¹)⁻¹ := by group
      rw [e1, hxr]
      have e2 : r * (z * r)⁻¹ = r * r⁻¹ * z⁻¹ := by group
      rw [e2, mul_inv_cancel, one_mul]
      exact (zpowers z).inv_mem (Subgroup.mem_zpowers z)
  have hrnC : r ∉ C := by
    intro h
    have hrz := hy.mem_zpowers_of_mem_CJs_of_mem_R h hrR
    rcases hy.mem_zpowers_z_iff.mp hrz with h1 | h1
    · apply hz1
      rw [← hr2, h1, one_mul]
    · apply hz1
      calc z = r * r := hr2.symm
        _ = z * z := by rw [h1]
        _ = 1 := hy.z_sq
  have hC32 : Nat.card C = 32 := hy.card_Cs
  have hB64 : 64 ≤ Nat.card B := by
    obtain ⟨m, hm⟩ : Nat.card C ∣ Nat.card B := Subgroup.card_dvd_of_le le_sup_left
    rw [hC32] at hm
    have hpos : 0 < Nat.card B := Nat.card_pos
    have hm1 : m ≠ 1 := by
      rintro rfl
      apply hrnC
      have hCB : C = B := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hm, hC32])
      rw [hCB]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m <;> omega
    · omega
  set M := B ⊓ Subgroup.centralizer ({x} : Set G) with hM
  have hMcard : 32 ≤ Nat.card M := by
    have h : Nat.card B ≤ 2 * Nat.card M :=
      hy.card_le_two_mul_card_inf_centralizer (hBJ.trans J_le_H) hxH
        (fun b hb => (mem_centModZ.mp (hBw hb)).2)
    omega
  have hMJ : M ≤ J z := inf_le_left.trans hBJ
  have hmemM : ∀ y, y ∈ B → y * x = x * y → y ∈ M := fun y hyB hyx =>
    ⟨hyB, Subgroup.mem_centralizer_singleton_iff.mpr hyx⟩
  have heM : e ∈ M := by
    refine hmemM e (Subgroup.mem_sup_left he) ?_
    rw [hx]
    calc e * (c₁ * e) = (e * c₁) * e := by group
      _ = (c₁ * e) * e := by rw [(hc₁C e he).symm]
  have hZ : ∀ a ∈ M, (∀ b ∈ M, a * b = b * a) → a ∈ zpowers z := by
    intro a haM hcent
    rcases hy.mem_CJs_sup_zpowers_cases hrC hr2 haM.1 with haC | ⟨c, hc, rfl⟩
    · apply hy.mem_zpowers_of_mem_CJs_of_commute haC
      intro d hd
      rcases hy.mem_zpowers_z_iff.mp (hy.comm_mem heJ ((CJ_le_J _) hd)) with h | h
      ·
        have hed : e * d * e⁻¹ = d := by
          calc e * d * e⁻¹ = (e * d * e⁻¹ * d⁻¹) * d := by group
            _ = d := by rw [h, one_mul]
        have hdM : d ∈ M := by
          refine hmemM d (Subgroup.mem_sup_left hd) ?_
          have := hxc d hd
          rw [hed] at this
          calc d * x = x * (x⁻¹ * d * x) := by group
            _ = x * d := by
              rw [show x⁻¹ * d * x = d from by
                calc x⁻¹ * d * x = x⁻¹ * (x * d * x⁻¹) * x := by rw [this]
                  _ = d := by group]
        exact hcent d hdM
      ·
        have hed : e * d * e⁻¹ = z * d := by
          calc e * d * e⁻¹ = (e * d * e⁻¹ * d⁻¹) * d := by group
            _ = z * d := by rw [h]
        have hdrM : d * r ∈ M := by
          refine hmemM (d * r) (B.mul_mem (Subgroup.mem_sup_left hd)
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers r))) ?_
          have h1 := hxcr d hd
          rw [hed] at h1
          have h2 : x * (d * r) * x⁻¹ = d * r := by
            rw [h1]
            calc z * d * (z * r) = z * (d * z) * r := by group
              _ = z * (z * d) * r := by
                  rw [hzc d (J_le_H ((CJ_le_J _) hd))]
              _ = (z * z) * d * r := by group
              _ = d * r := by rw [hy.z_sq, one_mul]
          calc d * r * x = x * (x⁻¹ * (d * r) * x) := by group
            _ = x * (d * r) := by
              rw [show x⁻¹ * (d * r) * x = d * r from by
                calc x⁻¹ * (d * r) * x = x⁻¹ * (x * (d * r) * x⁻¹) * x := by rw [h2]
                  _ = d * r := by group]
        have h1 := hcent (d * r) hdrM
        have har : a * r = r * a := (hrC a haC).symm
        calc a * d = a * d * r * r⁻¹ := by group
          _ = (a * (d * r)) * r⁻¹ := by group
          _ = ((d * r) * a) * r⁻¹ := by rw [h1]
          _ = d * (r * a) * r⁻¹ := by group
          _ = d * (a * r) * r⁻¹ := by rw [har]
          _ = d * a := by group
    ·
      exfalso
      have h1 := hcent e heM
      have hec : e * c = c * e := by
        have her : r * e = e * r := hrC e he
        calc e * c = e * (c * r) * r⁻¹ := by group
          _ = (c * r * e) * r⁻¹ := by rw [← h1]
          _ = c * (r * e) * r⁻¹ := by group
          _ = c * (e * r) * r⁻¹ := by rw [her]
          _ = c * e := by group
      have hece : e * c * e⁻¹ = c := by
        calc e * c * e⁻¹ = c * e * e⁻¹ := by rw [hec]
          _ = c := by group
      have h2 := hxcr c hc
      rw [hece] at h2
      have hcx : c * r * x = x * (c * r) := Subgroup.mem_centralizer_singleton_iff.mp haM.2
      have h3 : x * (c * r) * x⁻¹ = c * r := by
        calc x * (c * r) * x⁻¹ = c * r * x * x⁻¹ := by rw [hcx]
          _ = c * r := by group
      rw [h3] at h2
      have h4 : r = z * r := mul_left_cancel h2
      apply hz1
      have h5 : 1 * r = z * r := by rw [one_mul]; exact h4
      exact (mul_right_cancel h5).symm
  obtain ⟨i, hiM, X, hXM, Y, hYM, hi2, hX2, hY2, hiX, hiY, hXY⟩ := hy.exists_pauli hMJ hMcard hZ
  have hiJ := hMJ hiM
  have hXJ := hMJ hXM
  have hYJ := hMJ hYM
  have hi4 : i ^ 4 = 1 := by
    calc i ^ 4 = (i * i) * (i * i) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hi2, hy.z_sq]
  have hX2' : X ^ 2 = 1 := by rw [pow_two]; exact hX2
  have hY2' : Y ^ 2 = 1 := by rw [pow_two]; exact hY2
  have hYX : Y * X = i ^ 2 * X * Y := by
    rw [pow_two, hi2]
    calc Y * X = (X * Y * X⁻¹ * Y⁻¹)⁻¹ * (X * Y) := by group
      _ = z⁻¹ * (X * Y) := by rw [hXY]
      _ = z * X * Y := by
          rw [show z⁻¹ = z from inv_eq_of_mul_eq_one_right hy.z_sq]
          group
  have hinj := pauliHom_injective hi4 hX2' hY2' hiX hiY hYX (by rw [pow_two, hi2]; exact hz1)
  set φ := pauliHom hi4 hX2' hY2' hiX hiY hYX with hφ
  refine ⟨φ.range, ?_, ?_, (MonoidHom.ofInjective hinj).symm, ?_⟩
  · exact range_pauliHom_le hi4 hX2' hY2' hiX hiY hYX hiJ hXJ hYJ
  · exact range_pauliHom_le hi4 hX2' hY2' hiX hiY hYX hiM.2 hXM.2 hYM.2
  · rw [MulEquiv.symm_symm, MonoidHom.ofInjective_apply, hφ, pauliHom_apply]
    change i ^ (2 : ZMod 4).val * X ^ (0 : ZMod 2).val * Y ^ (0 : ZMod 2).val = z
    rw [show (2 : ZMod 4).val = 2 from rfl, show (0 : ZMod 2).val = 0 from rfl, pow_zero,
      pow_zero, mul_one, mul_one, pow_two, hi2]

end Hyp

end CFSG.RankThree.GF2n.Parrott.A1Section2Local
