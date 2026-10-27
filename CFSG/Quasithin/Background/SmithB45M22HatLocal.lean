module

public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.FixVZPowersMem
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.HatM22

variable {V : Type} [CommGroup V]

theorem mem_fixV_zpowers_iff {g : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

@[expose] def nrm3 (w : MulAut V) (v : V) : V := v * w v * w (w v)

theorem nrm3_mul (w : MulAut V) (a b : V) : nrm3 w (a * b) = nrm3 w a * nrm3 w b := by
  simp only [nrm3, map_mul]
  ac_rfl

theorem nrm3_congr {a b : MulAut V} (hab : Commute a b) {c : V} (h : a c = b c) :
    nrm3 a c = nrm3 b c := by
  have h2 : a (a c) = b (b c) := by
    calc a (a c) = a (b c) := by rw [h]
      _ = (a * b) c := rfl
      _ = (b * a) c := by rw [hab.eq]
      _ = b (a c) := rfl
      _ = b (b c) := by rw [h]
  rw [nrm3, nrm3, h2, h]

theorem nrm3_eq_one {u : MulAut V} (hu : u ^ 3 = 1) (hfix : fixV (Subgroup.zpowers u) = ⊥)
    (v : V) : nrm3 u v = 1 := by
  have h3 : u (u (u v)) = v := by
    have := congrArg (fun f : MulAut V => f v) hu
    simpa [pow_succ, MulAut.mul_apply] using this
  have hmem : nrm3 u v ∈ fixV (Subgroup.zpowers u) := by
    rw [mem_fixV_zpowers_iff, nrm3, map_mul, map_mul, h3]
    ac_rfl
  rw [hfix, Subgroup.mem_bot] at hmem
  exact hmem

theorem fixV_zpowers_sq_eq_bot {z : MulAut V} (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) : fixV (Subgroup.zpowers (z ^ 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [mem_fixV_zpowers_iff] at hw
  have hzw : z w = w := by
    have h4 : z = z ^ 2 * z ^ 2 := by
      rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hz, one_mul]
    rw [h4, MulAut.mul_apply, hw, hw]
  have : w ∈ fixV (Subgroup.zpowers z) := mem_fixV_zpowers_iff.2 hzw
  rwa [hfix] at this

theorem nrm3_pow (hV : ∀ v : V, v * v = 1) {z : MulAut V} (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) (m : ℕ) (v : V) :
    nrm3 (z ^ m) v = if m % 3 = 0 then v else 1 := by
  rw [pow_eq_pow_mod m hz]
  have hm : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : m % 3
  · simp [nrm3, hV]
  · simpa using nrm3_eq_one hz hfix v
  · simpa using nrm3_eq_one (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow])
      (fixV_zpowers_sq_eq_bot hz hfix) v

@[expose] def eigSp (y z : MulAut V) (k : ℕ) : Subgroup V where
  carrier := {v | y v = (z ^ k) v}
  one_mem' := by simp
  mul_mem' {a b} (ha : y a = (z ^ k) a) (hb : y b = (z ^ k) b) := by
    show y (a * b) = (z ^ k) (a * b)
    rw [map_mul, map_mul, ha, hb]
  inv_mem' {a} (ha : y a = (z ^ k) a) := by
    show y a⁻¹ = (z ^ k) a⁻¹
    rw [map_inv, map_inv, ha]

theorem mem_eigSp {y z : MulAut V} {k : ℕ} {v : V} : v ∈ eigSp y z k ↔ y v = (z ^ k) v :=
  Iff.rfl

theorem nrm3_eigSp {y z : MulAut V} (hyz : Commute y z) (i k : ℕ) {v : V}
    (hv : v ∈ eigSp y z k) : nrm3 (z ^ i * y) v = nrm3 (z ^ (i + k)) v := by
  refine nrm3_congr ((Commute.pow_pow_self z i (i + k)).mul_left (hyz.pow_right (i + k))) ?_
  rw [MulAut.mul_apply, mem_eigSp.1 hv, pow_add, MulAut.mul_apply]

theorem mem_eigSp_succ {x y z : MulAut V} (hyz : Commute y z) (hxz : Commute x z)
    (hxy : x⁻¹ * y * x = y * z) {k : ℕ} {v : V} (hv : v ∈ eigSp y z k) :
    x v ∈ eigSp y z (k + 1) := by
  have hyx : y * x = x * (z * y) := by
    rw [← hyz.eq, ← hxy]
    group
  rw [mem_eigSp]
  calc y (x v) = (y * x) v := rfl
    _ = (x * (z * y)) v := by rw [hyx]
    _ = x (z (y v)) := rfl
    _ = x (z ((z ^ k) v)) := by rw [mem_eigSp.1 hv]
    _ = (x * z ^ (k + 1)) v := by rw [pow_succ', MulAut.mul_apply, MulAut.mul_apply]
    _ = (z ^ (k + 1) * x) v := by rw [(hxz.pow_right (k + 1)).eq]
    _ = (z ^ (k + 1)) (x v) := rfl

theorem conj_eq_of_cube {G : Type*} [Group G] {t s : G} (ht : t * t = 1) (hs : s * s = 1)
    (h3 : (t * s) ^ 3 = 1) : (t * s) * t * (t * s)⁻¹ = s := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have e : (t * s) * t * (t * s)⁻¹ = (t * s) ^ 3 * s := by
    rw [mul_inv_rev, hti, hsi]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc, hs, mul_one]
  rw [e, h3, one_mul]

theorem eigSp_three {y z : MulAut V} (hz : z ^ 3 = 1) : eigSp y z 3 = eigSp y z 0 := by
  ext v
  rw [mem_eigSp, mem_eigSp, hz, pow_zero]

theorem eigSp_zero {y z : MulAut V} : eigSp y z 0 = fixV (Subgroup.zpowers y) := by
  ext v
  rw [mem_eigSp, mem_fixV_zpowers_iff, pow_zero, MulAut.one_apply]

section Finite

variable [Finite V]

theorem card_eigSp_le_succ {x y z : MulAut V} (hyz : Commute y z) (hxz : Commute x z)
    (hxy : x⁻¹ * y * x = y * z) (k : ℕ) :
    Nat.card (eigSp y z k) ≤ Nat.card (eigSp y z (k + 1)) :=
  Nat.card_le_card_of_injective
    (fun v => ⟨x v.1, mem_eigSp_succ hyz hxz hxy v.2⟩)
    (fun _ _ h => Subtype.ext (x.injective (congrArg Subtype.val h)))

theorem card_fixV_cube_le (hV : ∀ v : V, v * v = 1) {x y z : MulAut V} (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) (hyz : Commute y z) (hxz : Commute x z)
    (hxy : x⁻¹ * y * x = y * z) :
    Nat.card (fixV (Subgroup.zpowers y)) ^ 3 ≤ Nat.card V := by
  set E : ℕ → Subgroup V := eigSp y z with hE
  have h01 := card_eigSp_le_succ hyz hxz hxy 0
  have h12 := card_eigSp_le_succ hyz hxz hxy 1
  have h23 := card_eigSp_le_succ hyz hxz hxy 2
  rw [eigSp_three hz] at h23
  have e1 : Nat.card (E 1) = Nat.card (E 0) := le_antisymm (h12.trans h23) h01
  have e2 : Nat.card (E 2) = Nat.card (E 0) := le_antisymm h23 (h01.trans h12)
  have np : ∀ (i k : ℕ) (v : V), v ∈ E k →
      nrm3 (z ^ i * y) v = if (i + k) % 3 = 0 then v else 1 := fun i k v hv => by
    rw [nrm3_eigSp hyz i k hv, nrm3_pow hV hz hfix]
  have hinj : Function.Injective
      (fun p : ↥(E 0) × ↥(E 1) × ↥(E 2) => (p.1 : V) * p.2.1 * p.2.2) := by
    rintro ⟨a₀, a₁, a₂⟩ ⟨b₀, b₁, b₂⟩ h
    simp only at h
    have hc : ((a₀ * b₀⁻¹ : ↥(E 0)) : V) * ((a₁ * b₁⁻¹ : ↥(E 1)) : V) *
        ((a₂ * b₂⁻¹ : ↥(E 2)) : V) = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (a₀ : V) * (b₀ : V)⁻¹ * ((a₁ : V) * (b₁ : V)⁻¹) * ((a₂ : V) * (b₂ : V)⁻¹)
          = ((a₀ : V) * a₁ * a₂) * ((b₀ : V) * b₁ * b₂)⁻¹ := by
            simp only [mul_inv_rev]
            ac_rfl
        _ = 1 := by rw [h, mul_inv_cancel]
    have proj : ∀ i : ℕ, nrm3 (z ^ i * y) (((a₀ * b₀⁻¹ : ↥(E 0)) : V) *
        ((a₁ * b₁⁻¹ : ↥(E 1)) : V) * ((a₂ * b₂⁻¹ : ↥(E 2)) : V)) = 1 := fun i => by
      rw [hc]
      simp [nrm3]
    have k0 := proj 0
    have k1 := proj 2
    have k2 := proj 1
    rw [nrm3_mul, nrm3_mul, np 0 0 _ (a₀ * b₀⁻¹).2, np 0 1 _ (a₁ * b₁⁻¹).2,
      np 0 2 _ (a₂ * b₂⁻¹).2] at k0
    rw [nrm3_mul, nrm3_mul, np 2 0 _ (a₀ * b₀⁻¹).2, np 2 1 _ (a₁ * b₁⁻¹).2,
      np 2 2 _ (a₂ * b₂⁻¹).2] at k1
    rw [nrm3_mul, nrm3_mul, np 1 0 _ (a₀ * b₀⁻¹).2, np 1 1 _ (a₁ * b₁⁻¹).2,
      np 1 2 _ (a₂ * b₂⁻¹).2] at k2
    norm_num at k0 k1 k2
    have q0 : a₀ * b₀⁻¹ = 1 := Subtype.ext k0
    have q1 : a₁ * b₁⁻¹ = 1 := Subtype.ext k1
    have q2 : a₂ * b₂⁻¹ = 1 := Subtype.ext k2
    rw [mul_inv_eq_one] at q0 q1 q2
    rw [q0, q1, q2]
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_prod, e1, e2] at hle
  rw [← eigSp_zero]
  calc Nat.card (E 0) ^ 3 = Nat.card (E 0) * (Nat.card (E 0) * Nat.card (E 0)) := by ring
    _ ≤ Nat.card V := hle

theorem index_fixV_conj (g h : MulAut V) :
    (fixV (Subgroup.zpowers (g * h * g⁻¹))).index = (fixV (Subgroup.zpowers h)).index :=
  CFSG.Quasithin.FixVLat.index_fixV_zpowers_conj g h

theorem index_fixV_mul_le_sq {t s : MulAut V} (ht : t * t = 1) (hs : s * s = 1)
    (h3 : (t * s) ^ 3 = 1) :
    (fixV (Subgroup.zpowers (t * s))).index ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
  have hle : fixV (Subgroup.zpowers t) ⊓ fixV (Subgroup.zpowers s) ≤
      fixV (Subgroup.zpowers (t * s)) := by
    rintro v ⟨hvt, hvs⟩
    rw [SetLike.mem_coe, mem_fixV_zpowers_iff] at *
    rw [MulAut.mul_apply, mem_fixV_zpowers_iff.1 hvs, mem_fixV_zpowers_iff.1 hvt]
  have hss : (fixV (Subgroup.zpowers s)).index = (fixV (Subgroup.zpowers t)).index := by
    rw [← conj_eq_of_cube ht hs h3, index_fixV_conj]
  calc (fixV (Subgroup.zpowers (t * s))).index
      ≤ (fixV (Subgroup.zpowers t) ⊓ fixV (Subgroup.zpowers s)).index :=
        Subgroup.index_antitone hle
    _ ≤ (fixV (Subgroup.zpowers t)).index * (fixV (Subgroup.zpowers s)).index :=
        Subgroup.index_inf_le
    _ = (fixV (Subgroup.zpowers t)).index ^ 2 := by rw [hss, sq]

theorem card_le_index_cube (hV : ∀ v : V, v * v = 1) {x t s z : MulAut V} (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) (ht : t * t = 1) (hs : s * s = 1)
    (h3 : (t * s) ^ 3 = 1) (hyz : Commute (t * s) z) (hxz : Commute x z)
    (hxy : x⁻¹ * (t * s) * x = (t * s) * z) :
    Nat.card V ≤ (fixV (Subgroup.zpowers t)).index ^ 3 := by
  have hc := card_fixV_cube_le hV hz hfix hyz hxz hxy
  have hi := index_fixV_mul_le_sq ht hs h3
  have hm := Subgroup.card_mul_index (fixV (Subgroup.zpowers (t * s)))
  set c := Nat.card (fixV (Subgroup.zpowers (t * s)))
  set i := (fixV (Subgroup.zpowers (t * s))).index
  set j := (fixV (Subgroup.zpowers t)).index
  set N := Nat.card V
  have hN : 0 < N := Nat.card_pos
  have h1 : N ^ 3 ≤ N * (j ^ 3) ^ 2 := by
    calc N ^ 3 = c ^ 3 * i ^ 3 := by rw [← hm]; ring
      _ ≤ N * (j ^ 2) ^ 3 := Nat.mul_le_mul hc (Nat.pow_le_pow_left hi 3)
      _ = N * (j ^ 3) ^ 2 := by ring
  have h2 : N ^ 2 ≤ (j ^ 3) ^ 2 := by
    have : N * N ^ 2 ≤ N * (j ^ 3) ^ 2 := by
      calc N * N ^ 2 = N ^ 3 := by ring
        _ ≤ N * (j ^ 3) ^ 2 := h1
    exact Nat.le_of_mul_le_mul_left this hN
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h2

theorem card_le_index_sq_of_inverts {t z : MulAut V} (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) (htz : t * z * t⁻¹ = z⁻¹) :
    Nat.card V ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
  set C := fixV (Subgroup.zpowers t) with hC
  have hfix2 := fixV_zpowers_sq_eq_bot hz hfix
  have key : ∀ c : V, t c = c → t (z c) = z c → c = 1 := by
    intro c hc hzc
    have htz' : t * z = z⁻¹ * t := by
      rw [← htz]
      group
    have h1 : t (z c) = z⁻¹ c := by
      calc t (z c) = (t * z) c := rfl
        _ = (z⁻¹ * t) c := by rw [htz']
        _ = z⁻¹ (t c) := rfl
        _ = z⁻¹ c := by rw [hc]
    rw [h1] at hzc
    have h2 : (z ^ 2) c = c := by
      calc (z ^ 2) c = z (z c) := by rw [sq]; rfl
        _ = z (z⁻¹ c) := by rw [hzc]
        _ = c := MulAut.apply_inv_self _ _ _
    have : c ∈ fixV (Subgroup.zpowers (z ^ 2)) := mem_fixV_zpowers_iff.2 h2
    rwa [hfix2, Subgroup.mem_bot] at this
  have hinj : Function.Injective (fun p : ↥C × ↥C => (p.1 : V) * z p.2) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only at h
    have hcC : (b : V) * (b' : V)⁻¹ ∈ C := C.mul_mem b.2 (C.inv_mem b'.2)
    have hzc : z ((b : V) * (b' : V)⁻¹) = (a' : V) * (a : V)⁻¹ := by
      rw [map_mul, map_inv]
      calc z b * (z b')⁻¹ = ((a : V) * z b) * ((a : V)⁻¹ * (z b')⁻¹) := by
            rw [mul_mul_mul_comm, mul_inv_cancel, one_mul]
        _ = ((a' : V) * z b') * ((a : V)⁻¹ * (z b')⁻¹) := by rw [h]
        _ = (a' : V) * (a : V)⁻¹ * (z b' * (z b')⁻¹) := by ac_rfl
        _ = (a' : V) * (a : V)⁻¹ := by rw [mul_inv_cancel, mul_one]
    have hzcC : z ((b : V) * (b' : V)⁻¹) ∈ C := by
      rw [hzc]
      exact C.mul_mem a'.2 (C.inv_mem a.2)
    have hc1 := key _ (mem_fixV_zpowers_iff.1 hcC) (mem_fixV_zpowers_iff.1 hzcC)
    have hbb : (b : V) = b' := mul_inv_eq_one.1 hc1
    have haa : (a : V) = a' := by
      rw [hc1, map_one] at hzc
      exact (mul_inv_eq_one.1 hzc.symm).symm
    exact Prod.ext (Subtype.ext haa) (Subtype.ext hbb)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hle
  have hm := Subgroup.card_mul_index C
  set c := Nat.card C
  set j := C.index
  set N := Nat.card V
  have hN : 0 < N := Nat.card_pos
  have h1 : N * N ≤ N * j ^ 2 := by
    calc N * N = (c * c) * (j * j) := by rw [← hm]; ring
      _ ≤ N * (j * j) := Nat.mul_le_mul_right _ hle
      _ = N * j ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_left h1 hN

end Finite

end CFSG.Quasithin.HatM22
