module

public import CFSG.RankThree.PartOne.S12.Sec13Base
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne

namespace RefFacts

open CFSG.RankThree.PartOne.Torsion37

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G}

structure ElemData (p : ℕ) (E : Subgroup G) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  comm : ∀ a b : E, a * b = b * a
  pow : ∀ a : E, a ^ p = 1

omit [Finite G] in
theorem ElemData.of_isElementaryAbelian (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : IsElementaryAbelian p ↥E) : ElemData p E :=
  ⟨hp, hp2, fun a b => hE.is_comm.comm a b, fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p ↥E) a⟩

omit [Finite G] in
theorem mul_self_eq_one {t : MulAut E} (ht : IsAutReflection p E t) : t * t = 1 := by
  have h2 : t ^ 2 = 1 := ht.1 ▸ pow_orderOf_eq_one t
  rwa [pow_two] at h2

theorem autMoved_le_of_move (hd : ElemData p E) {t : MulAut E} (ht : IsAutReflection p E t)
    {B : Subgroup E} {b : E} (hbB : b ∈ B) (htb : t b ∈ B) (hne : t b ≠ b) :
    autMoved E t ≤ B := by
  have hx : t b * b⁻¹ ∈ autMoved E t := Subgroup.subset_closure ⟨b, rfl⟩
  have hxB : t b * b⁻¹ ∈ B := B.mul_mem htb (B.inv_mem hbB)
  have hx1 : t b * b⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  have hdvd : orderOf (t b * b⁻¹) ∣ p := by
    have h1 := Subgroup.orderOf_dvd_natCard (autMoved E t) hx
    rwa [ht.2] at h1
  have hord : orderOf (t b * b⁻¹) = p := by
    rcases (Nat.dvd_prime hd.prime).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hz : Subgroup.zpowers (t b * b⁻¹) = autMoved E t :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx)
      (by rw [ht.2, Nat.card_zpowers, hord])
  rw [← hz]
  exact Subgroup.zpowers_le.mpr hxB

omit [Finite G] in
theorem t_apply_inv_of_mem_autMoved (hd : ElemData p E) {t : MulAut E}
    (ht : IsAutReflection p E t) {m : E} (hm : m ∈ autMoved E t) : t m = m⁻¹ := by
  have htt := mul_self_eq_one ht
  have hm' : m ∈ (Sec13Base.moveHom hd.comm t).range := by
    rw [Sec13Base.range_moveHom hd.comm t]
    exact hm
  obtain ⟨e, rfl⟩ := hm'
  have htte : t (t e) = e := by simpa using congrArg (fun m : MulAut E => m e) htt
  rw [Sec13Base.moveHom_apply, map_mul, map_inv, htte, mul_inv_rev, inv_inv, hd.comm]

theorem inf_fixed_sup_autMoved (hd : ElemData p E) {t : MulAut E} (ht : IsAutReflection p E t)
    {B : Subgroup E} (hB : autMoved E t ≤ B) : (B ⊓ autFixed E t) ⊔ autMoved E t = B := by
  have htt := mul_self_eq_one ht
  have hsup := Sec13Base.fixed_sup_moved hd.comm t hd.prime hd.ne_two hd.pow htt
  apply le_antisymm
  · exact sup_le inf_le_left hB
  · intro b hb
    have hbtop : b ∈ autFixed E t ⊔ autMoved E t := by rw [hsup]; trivial
    obtain ⟨f, hf, m, hm, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun k _ l _ => hd.comm k l) hbtop
    have hfB : f ∈ B := by
      have : f = (f * m) * m⁻¹ := by group
      rw [this]
      exact B.mul_mem hb (B.inv_mem (hB hm))
    exact Subgroup.mul_mem_sup ⟨hfB, hf⟩ hm

theorem card_eq_inf_fixed_mul (hd : ElemData p E) {t : MulAut E} (ht : IsAutReflection p E t)
    {B : Subgroup E} (hB : autMoved E t ≤ B) :
    Nat.card B = Nat.card ↥(B ⊓ autFixed E t) * p := by
  have htt := mul_self_eq_one ht
  have hinf := Sec13Base.fixed_inf_moved hd.comm t hd.prime hd.ne_two hd.pow htt
  have hdisj : Disjoint (B ⊓ autFixed E t) (autMoved E t) :=
    disjoint_iff.mpr (le_bot_iff.mp (by
      calc B ⊓ autFixed E t ⊓ autMoved E t ≤ autFixed E t ⊓ autMoved E t :=
            inf_le_inf_right _ inf_le_right
        _ = ⊥ := hinf))
  have h := card_sup_of_commute_disjoint (fun k _ l _ => hd.comm k l) hdisj
  rw [inf_fixed_sup_autMoved hd ht hB, ht.2] at h
  exact h

theorem relIndex_inf_fixed (hd : ElemData p E) {t : MulAut E} (ht : IsAutReflection p E t)
    {B : Subgroup E} (hB : autMoved E t ≤ B) : (B ⊓ autFixed E t).relIndex B = p := by
  have h1 := Subgroup.relIndex_mul_card (H := B ⊓ autFixed E t) (K := B)
  have h2 := card_eq_inf_fixed_mul hd ht hB
  have h3 : (B ⊓ autFixed E t) ⊓ B = B ⊓ autFixed E t := inf_eq_left.mpr inf_le_left
  rw [h3] at h1
  have hpos : 0 < Nat.card ↥(B ⊓ autFixed E t) := Nat.card_pos
  have h4 : (B ⊓ autFixed E t).relIndex B * Nat.card ↥(B ⊓ autFixed E t) =
      p * Nat.card ↥(B ⊓ autFixed E t) := by
    rw [h1, h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h4

theorem pow_prime_fixes_of_same_fixed (hd : ElemData p E) {t s : MulAut E}
    (ht : IsAutReflection p E t) (hs : IsAutReflection p E s) {B : Subgroup E}
    (hmt : autMoved E t ≤ B) (hms : autMoved E s ≤ B)
    (hH : B ⊓ autFixed E t = B ⊓ autFixed E s) : ∀ b ∈ B, ((t * s) ^ p) b = b := by
  have hcomm := hd.comm
  let _ : CommGroup E := { (inferInstance : Group ↥E) with mul_comm := hcomm }
  set H : Subgroup E := B ⊓ autFixed E t with hHdef
  have hHt : ∀ u ∈ H, t u = u := fun u hu => hu.2
  have hHs : ∀ u ∈ H, s u = u := fun u hu => by
    have : u ∈ B ⊓ autFixed E s := hH ▸ hu
    exact this.2
  have hdec : ∀ (r : MulAut E), IsAutReflection p E r → autMoved E r ≤ B →
      B ⊓ autFixed E r = H → ∀ b ∈ B, ∃ h ∈ H, r b = h * h * b⁻¹ := by
    intro r hr hmr hBH b hb
    have hb' : b ∈ (B ⊓ autFixed E r) ⊔ autMoved E r := by
      rw [inf_fixed_sup_autMoved hd hr hmr]; exact hb
    obtain ⟨h, hh, m, hm, rfl⟩ := exists_mul_of_mem_sup_of_commute
      (fun k _ l _ => hcomm k l) hb'
    have hhH : h ∈ H := hBH ▸ hh
    have hrh : r h = h := hh.2
    have hrm := t_apply_inv_of_mem_autMoved hd hr hm
    refine ⟨h, hhH, ?_⟩
    rw [map_mul, hrh, hrm]
    simp [mul_comm]
  have key : ∀ b ∈ B, ∃ u ∈ H, (t * s) b = u * b := by
    intro b hb
    obtain ⟨ht', hht, htb⟩ := hdec t ht hmt rfl b hb
    obtain ⟨hs', hhs, hsb⟩ := hdec s hs hms hH.symm b hb
    refine ⟨hs' * hs' * (ht' * ht')⁻¹,
      H.mul_mem (H.mul_mem hhs hhs) (H.inv_mem (H.mul_mem hht hht)), ?_⟩
    show t (s b) = _
    rw [hsb]
    simp only [map_mul, map_inv, hHt _ hhs, htb]
    simp [mul_comm, mul_left_comm]
  have fixH : ∀ (k : ℕ) (u : E), u ∈ H → ((t * s) ^ k) u = u := by
    intro k u hu
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : (t * s) u = u := by
        show t (s u) = u
        rw [hHs u hu, hHt u hu]
      rw [pow_succ, MulAut.mul_apply, h1, ih]
  have hpow : ∀ (k : ℕ) (b u : E), u ∈ H → (t * s) b = u * b →
      ((t * s) ^ k) b = u ^ k * b := by
    intro k b u hu hg
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, MulAut.mul_apply, hg, map_mul, fixH k u hu, ih, pow_succ]
      simp [mul_comm, mul_left_comm]
  intro b hb
  obtain ⟨u, hu, hg⟩ := key b hb
  rw [hpow p b u hu hg, hd.pow u, one_mul]

omit [Finite G] in
theorem relIndex_inf_inf_of_ne (hd : ElemData p E) {B H₁ H₂ : Subgroup E} (h1 : H₁ ≤ B)
    (h2 : H₂ ≤ B) (hi1 : H₁.relIndex B = p) (hi2 : H₂.relIndex B = p) (hne : H₁ ≠ H₂) :
    (H₁ ⊓ H₂).relIndex B = p ^ 2 := by
  have hp := hd.prime
  have hnormal : H₂.Normal := ⟨fun n hn g => by
    rw [hd.comm g n, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  have hle : H₁ ⊔ H₂ ≤ B := sup_le h1 h2
  have hmul := Subgroup.relIndex_mul_relIndex H₂ (H₁ ⊔ H₂) B le_sup_right hle
  rw [hi2] at hmul
  have hb : (H₁ ⊔ H₂).relIndex B ∣ p := Dvd.intro_left _ hmul
  have hsup : H₁ ⊔ H₂ = B := by
    rcases (Nat.dvd_prime hp).mp hb with hb1 | hbp
    · exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hb1)
    · exfalso
      rw [hbp] at hmul
      have ha : H₂.relIndex (H₁ ⊔ H₂) = 1 := by
        have hp0 : 0 < p := hp.pos
        exact Nat.eq_of_mul_eq_mul_right hp0 (by rw [hmul, one_mul])
      have hH1H2 : H₁ ≤ H₂ := le_sup_left.trans (Subgroup.relIndex_eq_one.mp ha)
      have hmul' := Subgroup.relIndex_mul_relIndex H₁ H₂ B hH1H2 h2
      rw [hi1, hi2] at hmul'
      have hone : H₁.relIndex H₂ = 1 := by
        have hp0 : 0 < p := hp.pos
        exact Nat.eq_of_mul_eq_mul_right hp0 (by rw [hmul', one_mul])
      exact hne (le_antisymm hH1H2 (Subgroup.relIndex_eq_one.mp hone))
  have hcomp : H₂.relIndex H₁ = p := by
    have := @Subgroup.relIndex_sup_right _ _ H₁ H₂ hnormal
    rw [hsup, hi2] at this
    exact this.symm
  have hmain := Subgroup.relIndex_inf_mul_relIndex (H := H₂) (K := H₁) (L := B)
  rw [inf_eq_left.mpr h1, hcomp, hi1, inf_comm] at hmain
  rw [← hmain]
  ring

end RefFacts

end CFSG.RankThree.PartOne
