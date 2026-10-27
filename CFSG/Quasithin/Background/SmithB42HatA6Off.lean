module

public import CFSG.Quasithin.Background.SmithB42HatA6Dim
public import CFSG.Quasithin.Background.SmithB42HatA6Norm

public section

namespace CFSG.Quasithin.HatA6

open CFSG.Open

variable {V : Type} [CommGroup V]

theorem card_sq_le_of_semilinear [Finite V] {z t : MulAut V} (hfp : ∀ v, z v = v → v = 1)
    (htz : ∀ v, t (z v) = z (z (t v))) {U : Subgroup V} (hzU : ∀ u ∈ U, z u ∈ U) :
    Nat.card ↥(U ⊓ fixV (Subgroup.zpowers t)) ^ 2 ≤ Nat.card U := by
  set C := U ⊓ fixV (Subgroup.zpowers t) with hC
  have htC : ∀ c ∈ C, t c = c := fun c hc => (mem_fixV_zpowers_iff).1 hc.2
  let f : ↥C × ↥C → ↥U := fun p => ⟨(p.1 : V) * z (p.2 : V), U.mul_mem p.1.2.1 (hzU _ p.2.2.1)⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : V) * z (b : V) = (a' : V) * z (b' : V) := congrArg Subtype.val h
    set c : V := (b' : V) * (b : V)⁻¹ with hc
    have hcC : c ∈ C := C.mul_mem b'.2 (C.inv_mem b.2)
    have hzc : z c = (a : V) * (a' : V)⁻¹ := by
      have key : (a : V) / (a' : V) = z (b' : V) / z (b : V) := by
        rw [div_eq_div_iff_mul_eq_mul, h1, mul_comm]
      rw [hc, ← div_eq_mul_inv, map_div, ← key, div_eq_mul_inv]
    have hzcC : z c ∈ C := hzc ▸ C.mul_mem a.2 (C.inv_mem a'.2)
    have h2 : z c = z (z c) := by
      have e1 := htC _ hzcC
      rw [htz, htC c hcC] at e1
      exact e1.symm
    have h3 : c = z c := z.injective h2
    have hc1 : c = 1 := hfp c h3.symm
    have hb : (b : V) = (b' : V) := by
      have := hc1
      rw [hc, mul_inv_eq_one] at this
      exact this.symm
    have ha : (a : V) = (a' : V) := by
      rw [hb] at h1
      exact mul_right_cancel h1
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  calc Nat.card ↥C ^ 2 = Nat.card (↥C × ↥C) := by rw [Nat.card_prod, pow_two]
    _ ≤ Nat.card ↥U := Nat.card_le_card_of_injective f hinj

section B4

variable [Finite V] {G L : Subgroup (MulAut V)}

theorem conj_z_cases {zL : ↥L} (hcen : Subgroup.center ↥L = Subgroup.zpowers zL)
    (h3 : (zL : MulAut V) ^ 3 = 1) (hz1 : (zL : MulAut V) ≠ 1) {b : MulAut V}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut V))) :
    b * zL = zL * b ∨ b * zL = zL * zL * b := by
  have hbN := Subgroup.mem_normalizer_iff.1 hb
  have hcL : b * (zL : MulAut V) * b⁻¹ ∈ L := (hbN _).1 zL.2
  have hzc : zL ∈ Subgroup.center ↥L := hcen ▸ Subgroup.mem_zpowers zL
  have hcc : (⟨b * (zL : MulAut V) * b⁻¹, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have hl' : b⁻¹ * (l : MulAut V) * b ∈ L := by
      have := (hbN (b⁻¹ * (l : MulAut V) * b)).2 (by simp [mul_assoc])
      exact this
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨_, hl'⟩)
    change b⁻¹ * (l : MulAut V) * b * zL = zL * (b⁻¹ * (l : MulAut V) * b) at h1
    change (l : MulAut V) * (b * zL * b⁻¹) = b * zL * b⁻¹ * l
    calc (l : MulAut V) * (b * zL * b⁻¹) = b * (b⁻¹ * l * b * zL) * b⁻¹ := by group
      _ = b * (zL * (b⁻¹ * l * b)) * b⁻¹ := by rw [h1]
      _ = b * zL * b⁻¹ * l := by group
  rw [hcen] at hcc
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).2 hcc
  have hn' : ((zL ^ n : ↥L) : MulAut V) = b * zL * b⁻¹ := congrArg Subtype.val hn
  have hz3 : (zL : MulAut V) ^ n = (zL : MulAut V) ^ (n % 3) := by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [Subgroup.coe_pow, hz3] at hn'
  have hn3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (n % 3)
  · exfalso
    apply hz1
    have h1 : b * (zL : MulAut V) * b⁻¹ = 1 := by rw [← hn', pow_zero]
    calc (zL : MulAut V) = b⁻¹ * (b * zL * b⁻¹) * b := by group
      _ = 1 := by rw [h1]; group
  · left
    rw [pow_one] at hn'
    calc b * (zL : MulAut V) = (b * zL * b⁻¹) * b := by group
      _ = zL * b := by rw [← hn']
  · right
    rw [pow_two] at hn'
    calc b * (zL : MulAut V) = (b * zL * b⁻¹) * b := by group
      _ = zL * zL * b := by rw [← hn']


theorem offender_facts (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L) (hP : B42TypeHatA6 ↥L)
    {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B) :
    B ≤ L ∧ Nat.card B = 4 ∧ Nat.card (fixV B) = 16 ∧
      ∀ b ∈ B, ∀ v : V, b v * v⁻¹ ∈ fixV B := by
  classical
  have hcard := card_V hV hHyp hP hB
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨r, m, hr, hr1, hr3, hmr, l, -, hle⟩ := short_generation hHyp hP hB.1 hB.2.1 hB.2.2.1
  have hB8 : Nat.card B ≤ 8 := by
    rw [hr]
    calc 2 ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hr3
      _ = 8 := by norm_num
  obtain ⟨zL, hcen, h3, hz1, hfp⟩ := exists_center_gen hHyp hP
  set z : MulAut V := (zL : MulAut V) with hzdef
  have hGN := le_normalizer_of_b4Hyp hHyp
  have hoff : Nat.card V ≤ Nat.card B * Nat.card (fixV B) := by
    have h := hB.2.2.2 ⊥ bot_le
    rwa [Subgroup.card_bot, one_mul, B1.fixV_bot, Subgroup.card_top] at h
  have hcomm : ∀ b ∈ B, b * z = z * b := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t, htB, htz⟩ := hcon
    have ht2 : t * z = z * z * t :=
      (conj_z_cases hcen h3 hz1 (hGN (hB.1 htB))).resolve_left htz
    have htz' : ∀ v, t (z v) = z (z (t v)) := fun v =>
      congrArg (fun y : MulAut V => y v) ht2
    set B₀ := B ⊓ Subgroup.centralizer ({z} : Set (MulAut V)) with hB₀
    have hB₀B : B₀ ≤ B := inf_le_left
    have hbt : ∀ b ∈ B, b ∉ B₀ → b * t ∈ B₀ := by
      intro b hb hb0
      have hbz : b * z = z * z * b := by
        rcases conj_z_cases hcen h3 hz1 (hGN (hB.1 hb)) with h | h
        · exact absurd ⟨hb, Subgroup.mem_centralizer_singleton_iff.2 h⟩ hb0
        · exact h
      refine ⟨B.mul_mem hb htB, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hz3 : z * z * z = 1 := by rw [← pow_three']; exact h3
      calc b * t * z = b * (t * z) := by group
        _ = b * (z * z * t) := by rw [ht2]
        _ = (b * z) * z * t := by group
        _ = (z * z * b) * z * t := by rw [hbz]
        _ = z * z * (b * z) * t := by group
        _ = z * z * (z * z * b) * t := by rw [hbz]
        _ = z * (z * z * z) * b * t := by group
        _ = z * (b * t) := by rw [hz3]; group
    have hcardB₀ : Nat.card B ≤ 2 * Nat.card B₀ := by
      let f : ↥B → ↥B₀ ⊕ ↥B₀ := fun b =>
        if hb : (b : MulAut V) ∈ B₀ then Sum.inl ⟨b, hb⟩
        else Sum.inr ⟨b * t, hbt b b.2 hb⟩
      have hf : Function.Injective f := by
        intro b b' h
        by_cases h1 : (b : MulAut V) ∈ B₀ <;> by_cases h2 : (b' : MulAut V) ∈ B₀
        · simp only [f, h1, h2, dite_true, Sum.inl.injEq, Subtype.mk.injEq] at h
          exact Subtype.ext h
        · simp [f, h1, h2] at h
        · simp [f, h1, h2] at h
        · simp only [f, h1, h2, dite_false, Sum.inr.injEq, Subtype.mk.injEq] at h
          exact Subtype.ext (mul_right_cancel h)
      have := Nat.card_le_card_of_injective f hf
      rwa [Nat.card_sum, ← two_mul] at this
    have hfixB : fixV B = fixV B₀ ⊓ fixV (Subgroup.zpowers t) := by
      ext v
      constructor
      · intro hv
        exact ⟨fun b hb => hv b (hB₀B hb), (mem_fixV_zpowers_iff).2 (hv t htB)⟩
      · rintro ⟨hv0, hvt⟩ b hb
        have hvt' : t v = v := (mem_fixV_zpowers_iff).1 hvt
        by_cases hb0 : b ∈ B₀
        · exact hv0 b hb0
        · have ht22 : t * t = 1 := by rw [← pow_two]; exact hB.2.2.1.2 t htB
          have h1 := hv0 _ (hbt b hb hb0)
          calc b v = (b * t * t) v := by rw [mul_assoc, ht22, mul_one]
            _ = (b * t) (t v) := rfl
            _ = v := by rw [hvt', h1]
    have hzU : ∀ u ∈ fixV B₀, z u ∈ fixV B₀ := by
      intro u hu b hb
      have hbz : b * z = z * b := Subgroup.mem_centralizer_singleton_iff.1 hb.2
      have := congrArg (fun y : MulAut V => y u) hbz
      change b (z u) = z (b u) at this
      rw [this, hu b hb]
    have hdesc := card_sq_le_of_semilinear hfp htz' hzU
    rw [← hfixB] at hdesc
    have hff := hB.2.2.2 B₀ hB₀B
    have hpos : 0 < Nat.card B₀ := Nat.card_pos
    have h2 : Nat.card (fixV B₀) ≤ 2 * Nat.card (fixV B) := by
      have h3' : Nat.card B₀ * Nat.card (fixV B₀) ≤ Nat.card B₀ * (2 * Nat.card (fixV B)) := by
        calc Nat.card B₀ * Nat.card (fixV B₀) ≤ Nat.card B * Nat.card (fixV B) := hff
          _ ≤ (2 * Nat.card B₀) * Nat.card (fixV B) := Nat.mul_le_mul_right _ hcardB₀
          _ = Nat.card B₀ * (2 * Nat.card (fixV B)) := by ring
      exact Nat.le_of_mul_le_mul_left h3' hpos
    have h4 : Nat.card (fixV B) ≤ 2 := by
      have h5 : Nat.card (fixV B) ^ 2 ≤ 2 * Nat.card (fixV B) := hdesc.trans h2
      have hpos' : 0 < Nat.card (fixV B) := Nat.card_pos
      nlinarith
    rw [hcard] at hoff
    have : Nat.card B * Nat.card (fixV B) ≤ 8 * 2 := Nat.mul_le_mul hB8 h4
    omega
  have hirr := irr_of_b4Hyp hHyp
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hP
  have hBL : B ≤ L := by
    intro b hb
    refine mem_of_normalizes hV hcard hq.1 hZ e hirr
      (Subgroup.mem_normalizer_iff.1 (hGN (hB.1 hb))) ?_
    intro k hk
    rw [hcen] at hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    rw [Subgroup.coe_zpow]
    exact (Commute.zpow_right (hcomm b hb) n).eq
  have hzfix : ∀ v ∈ fixV B, z v ∈ fixV B := by
    intro v hv b hb
    have := congrArg (fun y : MulAut V => y v) (hcomm b hb)
    change b (z v) = z (b v) at this
    rw [this, hv b hb]
  have hcases := card_cases_of_inv hcard h3 hfp hzfix
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hfix16 : Nat.card (fixV B) = 16 := by
    rcases hcases with h | h | h | h
    · rw [hcard, h] at hoff; omega
    · rw [hcard, h] at hoff; omega
    · exact h
    · exfalso
      apply hB.2.1
      rw [eq_bot_iff]
      intro b hb
      rw [Subgroup.mem_bot]
      refine MulEquiv.ext fun v => ?_
      have htop : fixV B = ⊤ := Subgroup.eq_top_of_card_eq _ (h.trans hcard.symm)
      exact (htop ▸ Subgroup.mem_top v : v ∈ fixV B) b hb
  have hidx : (fixV B).index = 4 := by
    have := (fixV B).card_mul_index
    rw [hfix16, hcard] at this
    omega
  have hB4 : Nat.card B = 4 := by
    have h4 : 4 ≤ Nat.card B := by
      rw [hcard, hfix16] at hoff; omega
    rcases Nat.lt_or_ge (Nat.card B) 5 with h | h
    · omega
    · exfalso
      have hr3' : r = 3 := by
        by_contra hne
        have : r ≤ 2 := by omega
        have : Nat.card B ≤ 4 := by
          rw [hr]
          calc 2 ^ r ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
            _ = 4 := by norm_num
        omega
      subst hr3'
      have hm2 : m ≤ 2 := by omega
      have h1 := card_le_pow_of_le_closure (fixV_eq_bot_of_b4Hyp hHyp) l hle
      rw [hidx, hcard] at h1
      have : 4 ^ m ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      omega
  refine ⟨hBL, hB4, hfix16, ?_⟩
  intro b hb v
  have hbz : ∀ w, b (z w) = z (b w) := fun w => congrArg (fun y : MulAut V => y w) (hcomm b hb)
  have hzb : ∀ w ∈ fixV (Subgroup.zpowers b), z w ∈ fixV (Subgroup.zpowers b) := by
    intro w hw
    rw [mem_fixV_zpowers_iff] at hw ⊢
    rw [hbz, hw]
  have hle' : fixV B ≤ fixV (Subgroup.zpowers b) := by
    intro w hw
    exact (mem_fixV_zpowers_iff).2 (hw b hb)
  have hb2 : ∀ w, b (b w) = w := fun w => by
    have := congrArg (fun y : MulAut V => y w) (hB.2.2.1.2 b hb)
    simpa [pow_two, MulAut.mul_apply] using this
  have hcomm_mem : b v * v⁻¹ ∈ fixV (Subgroup.zpowers b) := by
    rw [mem_fixV_zpowers_iff, map_mul, map_inv, hb2]
    have hsq' : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hsq w)
    rw [hsq' (b v), hsq' v, mul_comm]
  rcases card_cases_of_inv hcard h3 hfp hzb with h | h | h | h
  · exfalso
    have := Subgroup.card_le_of_le hle'
    rw [h, hfix16] at this; omega
  · exfalso
    have := Subgroup.card_le_of_le hle'
    rw [h, hfix16] at this; omega
  · have heq : fixV B = fixV (Subgroup.zpowers b) :=
      Subgroup.eq_of_le_of_card_ge hle' (by rw [h, hfix16])
    rw [heq]
    exact hcomm_mem
  · have htop : fixV (Subgroup.zpowers b) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (h.trans hcard.symm)
    have hbv : b v = v := (mem_fixV_zpowers_iff).1 (htop ▸ Subgroup.mem_top v)
    rw [hbv, mul_inv_cancel]
    exact (fixV B).one_mem

end B4

end CFSG.Quasithin.HatA6
