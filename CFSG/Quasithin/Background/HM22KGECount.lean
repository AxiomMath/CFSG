module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

variable {W : Type*} [CommGroup W]

@[expose] def commHom (φ : MulAut W) : W →* W where
  toFun w := w⁻¹ * φ w
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_inv, mul_mul_mul_comm]

theorem commHom_apply (φ : MulAut W) (w : W) : commHom φ w = w⁻¹ * φ w := rfl

@[expose] def commImg (A : Subgroup W) (φ : MulAut W) : Subgroup W := A.map (commHom φ)

theorem mem_commImg {A : Subgroup W} {φ : MulAut W} {x : W} :
    x ∈ commImg A φ ↔ ∃ a ∈ A, a⁻¹ * φ a = x := Iff.rfl

@[expose] def fixIn (A : Subgroup W) (φ : MulAut W) : Subgroup W where
  carrier := {a | a ∈ A ∧ φ a = a}
  mul_mem' {a b} ha hb := ⟨A.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
  one_mem' := ⟨A.one_mem, map_one φ⟩
  inv_mem' {a} ha := ⟨A.inv_mem ha.1, by rw [map_inv, ha.2]⟩

theorem mem_fixIn {A : Subgroup W} {φ : MulAut W} {a : W} : a ∈ fixIn A φ ↔ a ∈ A ∧ φ a = a :=
  Iff.rfl

@[expose] def kerSum (z : MulAut W) : Subgroup W where
  carrier := {w | w * z w * z (z w) = 1}
  mul_mem' {a b} (ha : a * z a * z (z a) = 1) (hb : b * z b * z (z b) = 1) := by
    show a * b * z (a * b) * z (z (a * b)) = 1
    rw [map_mul, map_mul]
    calc a * b * (z a * z b) * (z (z a) * z (z b)) = (a * z a * z (z a)) * (b * z b * z (z b)) := by
          simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = 1 := by rw [ha, hb, one_mul]
  one_mem' := by show (1 : W) * z 1 * z (z 1) = 1; simp
  inv_mem' {a} (ha : a * z a * z (z a) = 1) := by
    show a⁻¹ * z a⁻¹ * z (z a⁻¹) = 1
    rw [map_inv, map_inv, ← mul_inv, ← mul_inv, ha, inv_one]

theorem mem_kerSum {z : MulAut W} {w : W} : w ∈ kerSum z ↔ w * z w * z (z w) = 1 := Iff.rfl

theorem card_eq_fix_mul_comm [Finite W] (A : Subgroup W) (φ : MulAut W) :
    Nat.card ↥A = Nat.card ↥(fixIn A φ) * Nat.card ↥(commImg A φ) := by
  let f : ↥A →* W := (commHom φ).comp A.subtype
  have hker : f.ker = (fixIn A φ).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_fixIn]
    simp only [f, MonoidHom.comp_apply, Subgroup.coe_subtype, commHom_apply]
    constructor
    · intro h
      exact ⟨a.2, (inv_mul_eq_one.mp h).symm⟩
    · rintro ⟨-, h⟩
      rw [h, inv_mul_cancel]
  have hrange : f.range = commImg A φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show fixIn A φ ≤ A from fun _ h => (mem_fixIn.mp h).1)).toEquiv] at h1
  rw [h1, mul_comm]

theorem card_sup_le [Finite W] (H K : Subgroup W) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card ↥H * Nat.card ↥K := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective (fun p => ⟨p.1.1 * p.2.1,
    Subgroup.mul_mem_sup p.1.2 p.2.2⟩) ?_
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem card_mul_le_sup [Finite W] {H K : Subgroup W} (hHK : ∀ x ∈ H, x ∈ K → x = 1) :
    Nat.card ↥H * Nat.card ↥K ≤ Nat.card ↥(H ⊔ K) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p => ⟨p.1.1 * p.2.1,
    Subgroup.mul_mem_sup p.1.2 p.2.2⟩) ?_
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
  have h1 : a * b = a' * b' := congrArg Subtype.val h
  have h2 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
      _ = b' * b⁻¹ := by group
  have h3 := hHK _ (H.mul_mem (H.inv_mem ha') ha) (h2 ▸ K.mul_mem hb' (K.inv_mem hb))
  have haa : a = a' := (inv_mul_eq_one.mp h3).symm
  have hbb : b = b' := by
    rw [h3] at h2
    exact (mul_inv_eq_one.mp h2.symm).symm
  subst haa hbb
  rfl

theorem card_map_mulAut [Finite W] (H : Subgroup W) (φ : MulAut W) :
    Nat.card ↥(H.map φ.toMonoidHom) = Nat.card ↥H :=
  Subgroup.card_map_of_injective φ.injective

variable (hW2 : ∀ w : W, w ^ 2 = 1)
include hW2

theorem inv_eq_self_of (w : W) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, hW2])

theorem fix_kerSum {z : MulAut W} {u : W} (hu : u ∈ kerSum z) (hzu : z u = u) : u = 1 := by
  rw [mem_kerSum, hzu, hzu] at hu
  have h2 : u * u = 1 := by rw [← pow_two, hW2]
  rwa [h2, one_mul] at hu

theorem card_sq_le_comm_pow_six [Finite W] {z y y' t : MulAut W}
    (hz3 : ∀ w, z (z (z w)) = w) (hy3 : ∀ w, y (y (y w)) = w) (hyz : ∀ w, y (z w) = z (y w))
    (hy'z : ∀ w, y' (z w) = z (y' w)) (hy' : ∀ w, y' (y w) = y (z (y' w)))
    (ht2 : ∀ w, t (t w) = w) (hty : ∀ w, t (y w) = y (y (t w))) :
    Nat.card ↥(kerSum z) ^ 2 ≤ Nat.card ↥(commImg (kerSum z) t) ^ 6 := by
  have hinv := inv_eq_self_of hW2
  set U := kerSum z with hUdef
  have hpres : ∀ φ : MulAut W, (∀ w, φ (z w) = z (φ w)) → ∀ u ∈ U, φ u ∈ U := by
    intro φ hφ u hu
    rw [mem_kerSum] at hu ⊢
    rw [← hφ, ← hφ, ← map_mul, ← map_mul, hu, map_one]
  have hyU := hpres y hyz
  have hy'U := hpres y' hy'z
  have hy'iU : ∀ u ∈ U, y'⁻¹ u ∈ U := hpres y'⁻¹ fun w => by
    apply y'.injective
    rw [MulAut.apply_inv_self, hy'z, MulAut.apply_inv_self]
  have h1 := card_eq_fix_mul_comm U y
  set C₁ := fixIn U (y * z)
  set C₂ := fixIn U (y * (z * z))
  have hC₁ : C₁ ≤ commImg U y := by
    intro a ha
    obtain ⟨haU, hya⟩ := mem_fixIn.mp ha
    simp only [MulAut.mul_apply] at hya
    refine mem_commImg.mpr ⟨z (z a), hpres z (fun _ => rfl) _ (hpres z (fun _ => rfl) _ haU), ?_⟩
    rw [hyz, hya, hinv]
    have hU := mem_kerSum.mp haU
    calc z (z a) * z a = z (z a) * z a * (a * z a * z (z a)) := by rw [hU, mul_one]
      _ = a * (z a * z a) * (z (z a) * z (z a)) := by simp only [mul_comm, mul_left_comm]
      _ = a := by rw [← pow_two, ← pow_two, hW2, hW2, mul_one, mul_one]
  have hC₂ : C₂ ≤ commImg U y := by
    intro a ha
    obtain ⟨haU, hya⟩ := mem_fixIn.mp ha
    simp only [MulAut.mul_apply] at hya
    refine mem_commImg.mpr ⟨z a, hpres z (fun _ => rfl) _ haU, ?_⟩
    have hya' : y a = z a := by
      have h6 := congrArg z hya
      rwa [← hyz, hz3] at h6
    rw [hyz, hya', hinv]
    have hU := mem_kerSum.mp haU
    calc z a * z (z a) = z a * z (z a) * (a * z a * z (z a)) := by rw [hU, mul_one]
      _ = a * (z a * z a) * (z (z a) * z (z a)) := by simp only [mul_comm, mul_left_comm]
      _ = a := by rw [← pow_two, ← pow_two, hW2, hW2, mul_one, mul_one]
  have hdisj : ∀ x ∈ C₁, x ∈ C₂ → x = 1 := by
    intro x hx₁ hx₂
    obtain ⟨hxU, h₁⟩ := mem_fixIn.mp hx₁
    obtain ⟨-, h₂⟩ := mem_fixIn.mp hx₂
    simp only [MulAut.mul_apply] at h₁ h₂
    have h3 : z x = z (z x) := y.injective (h₁.trans h₂.symm)
    have h4 : x = z x := z.injective h3
    exact fix_kerSum hW2 hxU h4.symm
  have h2 : Nat.card ↥C₁ * Nat.card ↥C₂ ≤ Nat.card ↥(commImg U y) :=
    (card_mul_le_sup hdisj).trans (Subgroup.card_le_of_le (sup_le hC₁ hC₂))
  have hmap : ∀ φ ψ : MulAut W, (∀ w, y' (φ w) = ψ (y' w)) →
      (fixIn U φ).map y'.toMonoidHom = fixIn U ψ := by
    intro φ ψ hφψ
    ext b
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, mem_fixIn]
    constructor
    · rintro ⟨a, ⟨haU, hφa⟩, rfl⟩
      exact ⟨hy'U a haU, by rw [← hφψ, hφa]⟩
    · rintro ⟨hbU, hψb⟩
      refine ⟨y'⁻¹ b, ⟨hy'iU b hbU, ?_⟩, MulAut.apply_inv_self W y' b⟩
      apply y'.injective
      rw [hφψ, MulAut.apply_inv_self, hψb]
  have e₁ : Nat.card ↥(fixIn U y) = Nat.card ↥C₁ := by
    rw [← card_map_mulAut (fixIn U y) y', hmap y (y * z) fun w => by
      rw [MulAut.mul_apply, hy']]
  have e₂ : Nat.card ↥C₁ = Nat.card ↥C₂ := by
    rw [← card_map_mulAut C₁ y', hmap (y * z) (y * (z * z)) fun w => by
      simp only [MulAut.mul_apply]
      rw [hy', hy'z]]
  set s := t * y
  have hsy : ∀ w, s (y w) = y (t w) := fun w => by
    simp only [s, MulAut.mul_apply]
    rw [hty, hty, hy3]
  have h3 : commImg U y ≤ commImg U t ⊔ (commImg U s).map t.toMonoidHom := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_commImg.mp hx
    have hmem : u⁻¹ * y u = (u⁻¹ * t u) * t (u⁻¹ * s u) := by
      simp only [s, MulAut.mul_apply, map_mul, map_inv, ht2]
      rw [mul_assoc, ← mul_assoc (t u), mul_inv_cancel, one_mul]
    rw [hmem]
    exact Subgroup.mul_mem_sup (mem_commImg.mpr ⟨u, hu, rfl⟩) ⟨_, mem_commImg.mpr ⟨u, hu, rfl⟩, rfl⟩
  have h4 : commImg U s = (commImg U t).map y.toMonoidHom := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, mem_commImg]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(y⁻¹ u)⁻¹ * t (y⁻¹ u), ⟨y⁻¹ u, hpres y⁻¹ (fun w => by
        apply y.injective
        rw [MulAut.apply_inv_self, hyz, MulAut.apply_inv_self]) u hu, rfl⟩, ?_⟩
      rw [map_mul, map_inv, ← hsy, MulAut.apply_inv_self]
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨y v, hyU v hv, by rw [hsy, map_mul, map_inv]⟩
  have h5 : Nat.card ↥(commImg U y) ≤ Nat.card ↥(commImg U t) ^ 2 := by
    calc Nat.card ↥(commImg U y)
        ≤ Nat.card ↥(commImg U t ⊔ (commImg U s).map t.toMonoidHom) := Subgroup.card_le_of_le h3
      _ ≤ Nat.card ↥(commImg U t) * Nat.card ↥((commImg U s).map t.toMonoidHom) :=
          card_sup_le _ _
      _ = Nat.card ↥(commImg U t) ^ 2 := by
          rw [card_map_mulAut, h4, card_map_mulAut, pow_two]
  set c := Nat.card ↥(fixIn U y)
  set m := Nat.card ↥(commImg U y)
  have hc2 : c * c ≤ m := by rw [e₁]; nth_rw 2 [e₂]; exact h2
  calc Nat.card ↥U ^ 2 = c * c * (m * m) := by rw [h1]; ring
    _ ≤ m * (m * m) := Nat.mul_le_mul_right _ hc2
    _ = m ^ 3 := by ring
    _ ≤ (Nat.card ↥(commImg U t) ^ 2) ^ 3 := Nat.pow_le_pow_left h5 3
    _ = Nat.card ↥(commImg U t) ^ 6 := by ring

theorem card_le_comm_sq [Finite W] {z t : MulAut W} (hz3 : ∀ w, z (z (z w)) = w)
    (htz : ∀ w, t (z w) = z (z (t w))) :
    Nat.card ↥(kerSum z) ≤ Nat.card ↥(commImg (kerSum z) t) ^ 2 := by
  set U := kerSum z
  have h1 := card_eq_fix_mul_comm U t
  set C := fixIn U t
  have hzU : ∀ u ∈ U, z u ∈ U := by
    intro u hu
    rw [mem_kerSum] at hu ⊢
    rw [← map_mul, ← map_mul, hu, map_one]
  have h2 : Nat.card ↥C * Nat.card ↥C ≤ Nat.card ↥U := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun p => ⟨p.1.1 * z p.2.1,
      U.mul_mem p.1.2.1 (hzU _ p.2.2.1)⟩) ?_
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h1 : a * z b = a' * z b' := congrArg Subtype.val h
    obtain ⟨-, hta⟩ := mem_fixIn.mp ha
    obtain ⟨-, hta'⟩ := mem_fixIn.mp ha'
    obtain ⟨hbU, htb⟩ := mem_fixIn.mp hb
    obtain ⟨hb'U, htb'⟩ := mem_fixIn.mp hb'
    set d := b' * b⁻¹
    have hdU : d ∈ U := U.mul_mem hb'U (U.inv_mem hbU)
    have htd : t d = d := by simp only [d, map_mul, map_inv, htb, htb']
    have hc : a'⁻¹ * a = z d := by
      simp only [d, map_mul, map_inv]
      calc a'⁻¹ * a = a'⁻¹ * (a * z b) * (z b)⁻¹ := by group
        _ = a'⁻¹ * (a' * z b') * (z b)⁻¹ := by rw [h1]
        _ = z b' * (z b)⁻¹ := by group
    have htc : t (a'⁻¹ * a) = a'⁻¹ * a := by rw [map_mul, map_inv, hta, hta']
    rw [hc, htz, htd] at htc
    have h5 : z d = d := by
      have h6 := congrArg z htc
      rw [hz3] at h6
      exact (h6.trans htc).symm
    have hd1 : d = 1 := fix_kerSum hW2 hdU h5
    have hb'b : b' = b := by rw [← mul_inv_eq_one]; exact hd1
    have ha'a : a = a' := by
      rw [hd1, map_one] at hc
      exact (inv_mul_eq_one.mp hc).symm
    subst hb'b ha'a
    rfl
  have hc : Nat.card ↥C ≤ Nat.card ↥(commImg U t) := by
    have hpos : 0 < Nat.card ↥C := Nat.card_pos
    rw [h1] at h2
    exact Nat.le_of_mul_le_mul_left h2 hpos
  calc Nat.card ↥U = Nat.card ↥C * Nat.card ↥(commImg U t) := h1
    _ ≤ Nat.card ↥(commImg U t) * Nat.card ↥(commImg U t) := Nat.mul_le_mul_right _ hc
    _ = Nat.card ↥(commImg U t) ^ 2 := (pow_two _).symm

end CFSG.Quasithin.H.Mathieu.M22Link
