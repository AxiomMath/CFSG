module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26a

public section

namespace CFSG.Quasithin.H13.S126Crd

variable {G : Type*} [Group G]

theorem mem_or_inv_mul_mem' {Vp V : Subgroup G} (hidx : Vp.relIndex V = 2) {v w : G}
    (hv : v ∈ V) (hvp : v ∉ Vp) (hw : w ∈ V) : w ∈ Vp ∨ v⁻¹ * w ∈ Vp := by
  by_cases hwp : w ∈ Vp
  · exact Or.inl hwp
  right
  have key := Subgroup.mul_mem_iff_of_index_two (H := Vp.subgroupOf V) hidx
    (a := (⟨v, hv⟩ : ↥V)⁻¹) (b := ⟨w, hw⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at key
  refine key.2 (iff_of_false (fun h => hvp ?_) hwp)
  have := Vp.inv_mem h
  rwa [inv_inv] at this

namespace Setup

variable {Z A B : Subgroup G} {v i : G} (h : Setup Z A B v i)
include h

theorem inv_eq_A {a : G} (ha : a ∈ A) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h.sq_A a ha)

theorem conj_u {a : G} (ha : a ∈ A) :
    v * i * a * (v * i)⁻¹ = v * (i * a * i⁻¹ * a⁻¹) * v⁻¹ * (i * a * i⁻¹ * a⁻¹)⁻¹ *
      (i * a * i⁻¹ * a⁻¹) * a := by
  have e : v⁻¹ * a = a * v⁻¹ := (show Commute v a from h.v_A a ha).inv_left.eq
  calc v * i * a * (v * i)⁻¹ = v * (i * a * i⁻¹ * a⁻¹) * (a * v⁻¹) := by group
    _ = v * (i * a * i⁻¹ * a⁻¹) * (v⁻¹ * a) := by rw [e]
    _ = _ := by group

theorem conj_inv_u {a : G} (ha : a ∈ A) :
    (v * i)⁻¹ * a * (v * i) = (i * a * i⁻¹ * a⁻¹)⁻¹ * a := by
  have hb : i * a * i⁻¹ * a⁻¹ ∈ B := h.i_A a ha
  have e1 : v⁻¹ * a * v = a := by
    rw [mul_assoc, ← h.v_A a ha, ← mul_assoc, inv_mul_cancel, one_mul]
  have e2 : i⁻¹ * (i * a * i⁻¹ * a⁻¹) * i = i * a * i⁻¹ * a⁻¹ := by
    rw [mul_assoc, ← h.i_B _ hb, ← mul_assoc, inv_mul_cancel, one_mul]
  calc (v * i)⁻¹ * a * (v * i) = i⁻¹ * (v⁻¹ * a * v) * i := by group
    _ = i⁻¹ * a * i := by rw [e1]
    _ = (i⁻¹ * (i * a * i⁻¹ * a⁻¹) * i)⁻¹ * a := by group
    _ = _ := by rw [e2]

theorem exists_mem_not_mem_Z [Finite G] : ∃ a ∈ A, a ∉ Z := by
  by_contra hall
  push Not at hall
  have h1 := Subgroup.card_le_of_le (show A ≤ Z from hall)
  rw [h.card_A, h.card_Z] at h1
  omega

theorem not_sq_triv [Finite G]
    (hA2 : ∀ a ∈ A, (v * i) ^ 2 * a * ((v * i) ^ 2)⁻¹ * a⁻¹ ∈ Z)
    (hB2 : ∀ b ∈ B, (v * i) ^ 2 * b * ((v * i) ^ 2)⁻¹ * b⁻¹ ∈ Z) : False := by
  obtain ⟨a, ha, haZ⟩ := h.exists_mem_not_mem_Z
  set u := v * i with hu
  have hb : i * a * i⁻¹ * a⁻¹ ∈ B := h.i_A a ha
  generalize hbdef : i * a * i⁻¹ * a⁻¹ = b at hb
  have hc : v * b * v⁻¹ * b⁻¹ ∈ A := h.v_B b hb
  generalize hcdef : v * b * v⁻¹ * b⁻¹ = c at hc
  have h1 : u * a * u⁻¹ = c * b * a := by
    rw [hu, h.conj_u ha, hbdef, hcdef]
  have h2 : u⁻¹ * a * u = b⁻¹ * a := by
    rw [hu, h.conj_inv_u ha, hbdef]
  have hza := hA2 a ha
  have hzb := hB2 b⁻¹ (B.inv_mem hb)
  generalize hzadef : u ^ 2 * a * (u ^ 2)⁻¹ * a⁻¹ = za at hza
  generalize hzbdef : u ^ 2 * b⁻¹ * (u ^ 2)⁻¹ * b⁻¹⁻¹ = zb at hzb
  have e : c * b * a = zb * b⁻¹ * (za * a) := by
    rw [← h1, ← hzadef, ← hzbdef]
    calc u * a * u⁻¹ = u ^ 2 * (u⁻¹ * a * u) * (u ^ 2)⁻¹ := by group
      _ = _ := by rw [h2]; group
  have hzab : za * b⁻¹ = b⁻¹ * za := h.Z_comm_B hza (B.inv_mem hb)
  have hcZ : c ∈ Z := by
    have e2 : c = zb * za * b⁻¹ * b⁻¹ := by
      calc c = c * b * a * a⁻¹ * b⁻¹ := by group
        _ = zb * b⁻¹ * (za * a) * a⁻¹ * b⁻¹ := by rw [e]
        _ = zb * (za * b⁻¹) * b⁻¹ := by rw [hzab]; group
        _ = zb * za * b⁻¹ * b⁻¹ := by group
    rw [e2, mul_assoc, ← mul_inv_rev, h.sq_B b hb, inv_one, mul_one]
    exact Z.mul_mem hzb hza
  rw [← hcdef] at hcZ
  have hbZ := h.v_inj b hb hcZ
  rw [← hbdef] at hbZ
  exact haZ (h.i_inj a ha hbZ)

theorem conj_u_Z {z : G} (hz : z ∈ Z) : v * i * z * (v * i)⁻¹ = z := by
  calc v * i * z * (v * i)⁻¹ = v * (i * z * i⁻¹) * v⁻¹ := by group
    _ = z := by rw [h.i_Z hz, h.v_Z hz]

theorem conj_pow_five {a : G} (ha : a ∈ A)
    (hfix : a⁻¹ * (v * (i * a * i⁻¹ * a⁻¹) * v⁻¹ * (i * a * i⁻¹ * a⁻¹)⁻¹) ∈ Z) :
    ∃ z ∈ Z, (v * i) ^ 5 * a * ((v * i) ^ 5)⁻¹ = z * (a * (i * a * i⁻¹ * a⁻¹)) := by
  have hb : i * a * i⁻¹ * a⁻¹ ∈ B := h.i_A a ha
  have hφ : ∀ x : G, MulAut.conj (v * i) x = v * i * x * (v * i)⁻¹ := fun x => rfl
  have hφa := h.conj_u ha
  generalize hbdef : i * a * i⁻¹ * a⁻¹ = b at hb hφa hfix ⊢
  have hc : v * b * v⁻¹ * b⁻¹ ∈ A := h.v_B b hb
  generalize hcdef : v * b * v⁻¹ * b⁻¹ = c at hc hφa hfix
  generalize hz0def : a⁻¹ * c = z₀ at hfix
  have hz0 := hfix
  have hcz : c = a * z₀ := by rw [← hz0def]; group
  have hw : a * b * a⁻¹ * b⁻¹ ∈ Z := h.comm_AB a ha b hb
  generalize hwdef : a * b * a⁻¹ * b⁻¹ = w at hw
  have hpow : (v * i) ^ 5 * a * ((v * i) ^ 5)⁻¹ = MulAut.conj (v * i) (MulAut.conj (v * i)
      (MulAut.conj (v * i) (MulAut.conj (v * i) (MulAut.conj (v * i) a)))) := by
    rw [← MulAut.conj_apply, map_pow]
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
  set φ := MulAut.conj (v * i) with hφdef
  have hφZ : ∀ z ∈ Z, ∀ x : G, φ (z * x) = z * φ x := by
    intro z hz x
    rw [map_mul, hφ z, h.conj_u_Z hz]
  have e1 : φ a = z₀ * w * b := by
    rw [hφ, hφa, hcz]
    have hza : a * z₀ = z₀ * a := (h.Z_comm_A hz0 ha).symm
    calc a * z₀ * b * a = z₀ * (a * b * a) := by rw [hza]; group
      _ = z₀ * (a * b * a⁻¹ * b⁻¹) * b := by rw [h.inv_eq_A ha]; group
      _ = z₀ * w * b := by rw [hwdef]
  have e2 : φ b = z₀ * (a * b) := by
    rw [hφ]
    have hib : i * b * i⁻¹ = b := by rw [h.i_B b hb, mul_inv_cancel_right]
    calc v * i * b * (v * i)⁻¹ = v * (i * b * i⁻¹) * v⁻¹ := by group
      _ = v * b * v⁻¹ * b⁻¹ * b := by rw [hib]; group
      _ = a * z₀ * b := by rw [hcdef, hcz]
      _ = z₀ * (a * b) := by rw [← h.Z_comm_A hz0 ha]; group
  have e3 : φ (a * b) = z₀ * w * z₀ * w⁻¹ * a := by
    rw [map_mul, e1, e2]
    have hzb : z₀ * b = b * z₀ := h.Z_comm_B hz0 hb
    have hba : b * a = w⁻¹ * (a * b) := by rw [← hwdef]; group
    calc z₀ * w * b * (z₀ * (a * b)) = z₀ * w * (b * z₀) * (a * b) := by group
      _ = z₀ * w * (z₀ * b) * (a * b) := by rw [hzb]
      _ = z₀ * w * z₀ * (b * a) * b := by group
      _ = z₀ * w * z₀ * (w⁻¹ * (a * b)) * b := by rw [hba]
      _ = z₀ * w * z₀ * w⁻¹ * a * (b * b) := by group
      _ = z₀ * w * z₀ * w⁻¹ * a := by rw [h.sq_B b hb, mul_one]
  have hz1 : z₀ * w ∈ Z := Z.mul_mem hz0 hw
  have hz3 : z₀ * w * z₀ * w⁻¹ ∈ Z := Z.mul_mem (Z.mul_mem hz1 hz0) (Z.inv_mem hw)
  generalize hz1def : z₀ * w = z₁ at hz1 hz3 e1 e3
  generalize hz3def : z₁ * z₀ * w⁻¹ = z₃ at hz3 e3
  refine ⟨z₁ * (z₀ * (z₃ * (z₁ * z₀))), ?_, ?_⟩
  · exact Z.mul_mem hz1 (Z.mul_mem hz0 (Z.mul_mem hz3 (Z.mul_mem hz1 hz0)))
  rw [hpow, e1, hφZ _ hz1, e2, hφZ _ hz1, hφZ _ hz0, e3, hφZ _ hz1, hφZ _ hz0, hφZ _ hz3, e1,
    hφZ _ hz1, hφZ _ hz0, hφZ _ hz3, hφZ _ hz1, e2]
  group

@[expose] def fixA (p : G) : Subgroup G where
  carrier := {a | a ∈ A ∧ p * a * p⁻¹ * a⁻¹ ∈ Z}
  one_mem' := ⟨A.one_mem, by simp⟩
  mul_mem' := by
    rintro a a' ⟨ha, hz⟩ ⟨ha', hz'⟩
    refine ⟨A.mul_mem ha ha', ?_⟩
    have e : p * (a * a') * p⁻¹ * (a * a')⁻¹ =
        (p * a * p⁻¹ * a⁻¹) * (a * (p * a' * p⁻¹ * a'⁻¹) * a⁻¹) := by group
    rw [e, ← h.Z_comm_A hz' ha, mul_inv_cancel_right]
    exact Z.mul_mem hz hz'
  inv_mem' := by
    rintro a ⟨ha, hz⟩
    refine ⟨A.inv_mem ha, ?_⟩
    have e : p * a⁻¹ * p⁻¹ * a⁻¹⁻¹ = a⁻¹ * (p * a * p⁻¹ * a⁻¹)⁻¹ * a := by group
    rw [e, ← h.Z_comm_A (Z.inv_mem hz) (A.inv_mem ha), mul_assoc, inv_mul_cancel, mul_one]
    exact Z.inv_mem hz

@[expose] def fixB (p : G) : Subgroup G where
  carrier := {b | b ∈ B ∧ p * b * p⁻¹ * b⁻¹ ∈ Z}
  one_mem' := ⟨B.one_mem, by simp⟩
  mul_mem' := by
    rintro b b' ⟨hb, hz⟩ ⟨hb', hz'⟩
    refine ⟨B.mul_mem hb hb', ?_⟩
    have e : p * (b * b') * p⁻¹ * (b * b')⁻¹ =
        (p * b * p⁻¹ * b⁻¹) * (b * (p * b' * p⁻¹ * b'⁻¹) * b⁻¹) := by group
    rw [e, ← h.Z_comm_B hz' hb, mul_inv_cancel_right]
    exact Z.mul_mem hz hz'
  inv_mem' := by
    rintro b ⟨hb, hz⟩
    refine ⟨B.inv_mem hb, ?_⟩
    have e : p * b⁻¹ * p⁻¹ * b⁻¹⁻¹ = b⁻¹ * (p * b * p⁻¹ * b⁻¹)⁻¹ * b := by group
    rw [e, ← h.Z_comm_B (Z.inv_mem hz) (B.inv_mem hb), mul_assoc, inv_mul_cancel, mul_one]
    exact Z.inv_mem hz

theorem Z_le_fixA {p : G} (hpZ : ∀ z ∈ Z, p * z * p⁻¹ = z) : Z ≤ h.fixA p := fun z hz =>
  ⟨h.Z_le_A hz, by rw [hpZ z hz, mul_inv_cancel]; exact Z.one_mem⟩

theorem pair_conj {p a b : G} (hpZ : ∀ z ∈ Z, p * z * p⁻¹ = z) (ha : a ∈ A)
    (hpa : p * a * p⁻¹ ∈ A) (hb : b ∈ h.fixB p) : pair (p * a * p⁻¹) b = pair a b := by
  obtain ⟨hbB, hzb⟩ := hb
  generalize hzdef : p * b * p⁻¹ * b⁻¹ = z at hzb
  have hpb : p * b * p⁻¹ = z * b := by rw [← hzdef]; group
  have hc := h.comm_AB a ha b hbB
  have e1 : (p * a * p⁻¹) * (p * b * p⁻¹) * (p * a * p⁻¹)⁻¹ * (p * b * p⁻¹)⁻¹ =
      a * b * a⁻¹ * b⁻¹ := by
    rw [← hpZ _ hc]
    group
  have e2 : (p * a * p⁻¹) * (z * b) * (p * a * p⁻¹)⁻¹ * (z * b)⁻¹ =
      (p * a * p⁻¹) * b * (p * a * p⁻¹)⁻¹ * b⁻¹ := by
    have hxz : (p * a * p⁻¹) * z = z * (p * a * p⁻¹) := (h.Z_comm_A hzb hpa).symm
    have hcomm := h.comm_AB _ hpa b hbB
    have hzc : z * ((p * a * p⁻¹) * b * (p * a * p⁻¹)⁻¹ * b⁻¹) =
        ((p * a * p⁻¹) * b * (p * a * p⁻¹)⁻¹ * b⁻¹) * z :=
      h.comm_A _ (h.Z_le_A hzb) _ (h.Z_le_A hcomm)
    calc (p * a * p⁻¹) * (z * b) * (p * a * p⁻¹)⁻¹ * (z * b)⁻¹ =
        ((p * a * p⁻¹) * z) * b * (p * a * p⁻¹)⁻¹ * b⁻¹ * z⁻¹ := by group
      _ = z * ((p * a * p⁻¹) * b * (p * a * p⁻¹)⁻¹ * b⁻¹) * z⁻¹ := by rw [hxz]; group
      _ = _ := by rw [hzc]; group
  unfold pair
  rw [← e2, ← hpb, e1]

theorem exists_fix [Finite G] {p : G} (hpZ : ∀ z ∈ Z, p * z * p⁻¹ = z)
    (hpA : ∀ a ∈ A, p * a * p⁻¹ ∈ A) (hp3 : ∀ a ∈ A, p ^ 3 * a * (p ^ 3)⁻¹ * a⁻¹ ∈ Z)
    (hpi : ∀ a ∈ h.fixA p, i * a * i⁻¹ * a⁻¹ ∈ h.fixB p)
    (hpv : ∀ b ∈ h.fixB p, v * b * v⁻¹ * b⁻¹ ∈ h.fixA p)
    (hW : Nat.card (h.fixA p) ≤ 8) {a : G} (haW : a ∈ h.fixA p) (haZ : a ∉ Z) :
    a⁻¹ * (v * (i * a * i⁻¹ * a⁻¹) * v⁻¹ * (i * a * i⁻¹ * a⁻¹)⁻¹) ∈ Z := by
  have haA := haW.1
  have hbW := hpi a haW
  have hab0 := h.pair_self_ya ⟨a, haA⟩
  have hbZ' : i * a * i⁻¹ * a⁻¹ ∉ Z := fun hb => haZ (h.i_inj a haA hb)
  simp only [ya] at hab0
  generalize hbdef : i * a * i⁻¹ * a⁻¹ = b at hbW hab0 hbZ' ⊢
  have hbB := hbW.1
  have hcW := hpv b hbW
  have hcb0 := h.pair_xb_self ⟨b, hbB⟩
  have hcZ' : v * b * v⁻¹ * b⁻¹ ∉ Z := fun hc => hbZ' (h.v_inj b hbB hc)
  simp only [xb] at hcb0
  generalize hcdef : v * b * v⁻¹ * b⁻¹ = c at hcW hcb0 hcZ' ⊢
  have hne : ∃ w ∈ h.fixA p, pair w b = 1 := by
    by_contra hall
    push Not at hall
    have h01 : ∀ t : ZMod 2, t ≠ 1 → t = 0 := by decide
    apply hbZ'
    refine h.nondeg b hbB fun x hx => ?_
    have hx1 := hpA x hx
    have hx2 := hpA _ hx1
    have hx3A := hpA _ hx2
    have hwA : x * (p * x * p⁻¹) * (p * (p * x * p⁻¹) * p⁻¹) ∈ h.fixA p := by
      refine ⟨A.mul_mem (A.mul_mem hx hx1) hx2, ?_⟩
      have hcomm := h.comm_A _ (A.mul_mem hx1 hx2) _ hx3A
      have e : p * (x * (p * x * p⁻¹) * (p * (p * x * p⁻¹) * p⁻¹)) * p⁻¹ *
          (x * (p * x * p⁻¹) * (p * (p * x * p⁻¹) * p⁻¹))⁻¹ =
          ((p * x * p⁻¹) * (p * (p * x * p⁻¹) * p⁻¹)) * (p * (p * (p * x * p⁻¹) * p⁻¹) * p⁻¹) *
            ((p * x * p⁻¹) * (p * (p * x * p⁻¹) * p⁻¹))⁻¹ * x⁻¹ := by group
      rw [e, hcomm, mul_inv_cancel_right]
      have e3 : p * (p * (p * x * p⁻¹) * p⁻¹) * p⁻¹ = p ^ 3 * x * (p ^ 3)⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      rw [e3]
      exact hp3 x hx
    have hw0 := h01 _ (hall _ hwA)
    rw [h.pair_mul_left (A.mul_mem hx hx1) hx2 hbB, h.pair_mul_left hx hx1 hbB,
      h.pair_conj hpZ hx1 hx2 hbW, h.pair_conj hpZ hx hx1 hbW] at hw0
    have h3 : ∀ t : ZMod 2, t + t + t = 0 → t = 0 := by decide
    exact pair_eq_zero_iff.1 (h3 _ hw0)
  obtain ⟨w₀, hw₀, hw₀1⟩ := hne
  let f : ↥(h.fixA p) →* Multiplicative (ZMod 2) :=
    { toFun := fun w => Multiplicative.ofAdd (pair (w : G) b)
      map_one' := by
        show Multiplicative.ofAdd (pair 1 b) = 1
        rw [h.pair_Z_left Z.one_mem hbB]
        rfl
      map_mul' := fun w w' => by
        show Multiplicative.ofAdd (pair ((w : G) * w') b) = _
        rw [h.pair_mul_left w.2.1 w'.2.1 hbB, ofAdd_add] }
  have hfw : ∀ w : ↥(h.fixA p), f w = Multiplicative.ofAdd (pair (w : G) b) := fun w => rfl
  have hf : Function.Surjective f := by
    intro t
    have ht : ∀ t : Multiplicative (ZMod 2), t = Multiplicative.ofAdd 0 ∨
        t = Multiplicative.ofAdd 1 := by decide
    rcases ht t with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨w₀, hw₀⟩, by rw [hfw]; exact congrArg _ hw₀1⟩
  have hcardK : Nat.card f.ker * 2 = Nat.card (h.fixA p) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h1
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    rw [h2] at h1
    omega
  let K : Subgroup G := f.ker.map (h.fixA p).subtype
  have hKcard : Nat.card K = Nat.card f.ker :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hmemK : ∀ x, x ∈ h.fixA p → pair x b = 0 → x ∈ K := fun x hx hx0 =>
    ⟨⟨x, hx⟩, show f ⟨x, hx⟩ = 1 by rw [hfw]; exact congrArg _ hx0, rfl⟩
  have hZK : Z ≤ K := fun z hz => hmemK z (h.Z_le_fixA hpZ hz) (h.pair_Z_left hz hbB)
  have haK : a ∈ K := hmemK a haW hab0
  have hcK : c ∈ K := hmemK c hcW hcb0
  have hidx : Z.relIndex K = 2 := by
    have h1 := Subgroup.card_mul_index (Z.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv, h.card_Z] at h1
    have hne1 : (Z.subgroupOf K).index ≠ 1 := by
      intro h1'
      rw [Subgroup.index_eq_one] at h1'
      apply haZ
      have : (⟨a, haK⟩ : ↥K) ∈ Z.subgroupOf K := h1' ▸ Subgroup.mem_top _
      exact this
    have hKpos : 0 < Nat.card K := Nat.card_pos
    show (Z.subgroupOf K).index = 2
    omega
  rcases mem_or_inv_mul_mem' hidx haK haZ hcK with h1 | h1
  · exact absurd h1 hcZ'
  · exact h1

theorem not_pow_five_triv [Finite G] {p : G} (hpZ : ∀ z ∈ Z, p * z * p⁻¹ = z)
    (hpA : ∀ a ∈ A, p * a * p⁻¹ ∈ A) (hp3 : ∀ a ∈ A, p ^ 3 * a * (p ^ 3)⁻¹ * a⁻¹ ∈ Z)
    (hpi : ∀ a ∈ h.fixA p, i * a * i⁻¹ * a⁻¹ ∈ h.fixB p)
    (hpv : ∀ b ∈ h.fixB p, v * b * v⁻¹ * b⁻¹ ∈ h.fixA p)
    (hW : Nat.card (h.fixA p) ≤ 8) (hW' : ¬ h.fixA p ≤ Z)
    (h5 : ∀ a ∈ A, (v * i) ^ 5 * a * ((v * i) ^ 5)⁻¹ * a⁻¹ ∈ Z) : False := by
  obtain ⟨a, haW, haZ⟩ := Set.not_subset.mp hW'
  have haA : a ∈ A := haW.1
  have hfix := h.exists_fix hpZ hpA hp3 hpi hpv hW haW haZ
  obtain ⟨z, hz, hz5⟩ := h.conj_pow_five haA hfix
  have h5a := h5 a haA
  rw [hz5] at h5a
  have hb : i * a * i⁻¹ * a⁻¹ ∈ Z := by
    generalize i * a * i⁻¹ * a⁻¹ = b at h5a ⊢
    have h2 : a * b * a⁻¹ ∈ Z := by
      have := Z.mul_mem (Z.inv_mem hz) h5a
      rwa [show z⁻¹ * (z * (a * b) * a⁻¹) = a * b * a⁻¹ by group] at this
    have e := h.Z_comm_A h2 haA
    have : b = a * b * a⁻¹ := by
      calc b = a⁻¹ * ((a * b * a⁻¹) * a) := by group
        _ = a⁻¹ * (a * (a * b * a⁻¹)) := by rw [e]
        _ = a * b * a⁻¹ := by group
    rw [this]
    exact h2
  exact haZ (h.i_inj a haA hb)

end Setup

end CFSG.Quasithin.H13.S126Crd
