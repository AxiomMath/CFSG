module

public import CFSG.Quasithin.Background.C58Pairs

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 CFSG.Quasithin.C58 Subgroup

variable {G : Type*} [Group G]

structure PairDataZ (B Q U W D : Subgroup G) (x : G) (q : ℕ) : Prop where
  rank1 : Rank1 B Q U W q
  hq : 2 ≤ q
  hU2 : ∀ u ∈ U, u ^ 2 = 1
  hx : x ∈ normalizer (B : Set G)
  hx1 : ¬ conjSubgroup U x ≤ Q
  hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q
  hQ : Q = U ⊔ D
  hDU : ∀ u ∈ U, ∀ d ∈ D, u * d = d * u
  hDUx : ∀ u ∈ conjSubgroup U x, ∀ d ∈ D, u * d = d * u
  hZW : U ⊓ D ≤ W
  cent_mod : ∀ y ∈ B, y ∉ Q → ∀ u ∈ U, y * u * y⁻¹ * u⁻¹ ∈ U ⊓ D → u ∈ W

namespace PairDataZ

variable {B Q U W D : Subgroup G} {x : G} {q : ℕ} (h : PairDataZ B Q U W D x q)
include h

theorem D_le_Q : D ≤ Q := h.hQ ▸ le_sup_right

theorem mem_UD {q' : G} (hq : q' ∈ Q) : ∃ u ∈ U, ∃ d ∈ D, q' = u * d := by
  rw [h.hQ] at hq
  exact mem_sup_of_commute h.hDU hq

omit h in
theorem mem_Z_of_mem_sqSub {v : G} (hvU : v ∈ U) (hvF : v ∈ sqSub D) : v ∈ U ⊓ D :=
  ⟨hvU, sqSub_le_self hvF⟩

theorem conj_le_B : conjSubgroup U x ≤ B := h.rank1.conj_le_B h.hx

theorem sup_eq_B [Finite G] : conjSubgroup U x ⊔ Q = B := h.rank1.sup_Q_conj h.hx h.hx2

theorem W_le_conj [Finite G] : W ≤ conjSubgroup U x := by
  rw [← (h.rank1.commutator_conj h.hx h.hx1 h.hx2).2]; exact inf_le_right

theorem sq_conj {u : G} (hu : u ∈ conjSubgroup U x) : u ^ 2 = 1 := by
  rw [mem_conjSubgroup_iff] at hu
  have h1 := h.hU2 _ hu
  have h2 : x * u ^ 2 * x⁻¹ = (x * u * x⁻¹) ^ 2 := by simp [pow_two, mul_assoc]
  have h3 : x * u ^ 2 * x⁻¹ = 1 := by rw [h2, h1]
  have h4 : u ^ 2 = x⁻¹ * (x * u ^ 2 * x⁻¹) * x := by group
  rw [h4, h3]; group

theorem comm_B_D [Finite G] {b d : G} (hb : b ∈ B) (hd : d ∈ D) :
    b * d * b⁻¹ * d⁻¹ ∈ sqSub D := by
  have hUxN : conjSubgroup U x ≤ normalizer (Q : Set G) :=
    h.conj_le_B.trans h.rank1.B_le_normQ
  rw [← h.sup_eq_B] at hb
  obtain ⟨u', hu', q', hq', rfl⟩ := mem_sup_of_le_normalizer hUxN hb
  obtain ⟨u, hu, d', hd', rfl⟩ := h.mem_UD hq'
  have hc1 : d' * d * d'⁻¹ ∈ D := mul_mem (mul_mem hd' hd) (inv_mem hd')
  have e1 : u * (d' * d * d'⁻¹) = (d' * d * d'⁻¹) * u := h.hDU u hu _ hc1
  have e2 : u' * (d' * d * d'⁻¹) = (d' * d * d'⁻¹) * u' := h.hDUx u' hu' _ hc1
  have e : u' * (u * d') * d * (u' * (u * d'))⁻¹ * d⁻¹ = d' * d * d'⁻¹ * d⁻¹ := by
    calc u' * (u * d') * d * (u' * (u * d'))⁻¹ * d⁻¹
        = u' * (u * (d' * d * d'⁻¹)) * u⁻¹ * u'⁻¹ * d⁻¹ := by group
      _ = u' * ((d' * d * d'⁻¹) * u) * u⁻¹ * u'⁻¹ * d⁻¹ := by rw [e1]
      _ = (u' * (d' * d * d'⁻¹)) * u'⁻¹ * d⁻¹ := by group
      _ = ((d' * d * d'⁻¹) * u') * u'⁻¹ * d⁻¹ := by rw [e2]
      _ = d' * d * d'⁻¹ * d⁻¹ := by group
  rw [e]
  exact commutator_mem_sqSub hd' hd

theorem modElem_Q : ModElem B (sqSub D) Q := by
  refine ⟨h.rank1.Q_le_B, fun q' hq => ?_, fun q' hq q'' hq' => ?_⟩
  · obtain ⟨u, hu, d, hd, rfl⟩ := h.mem_UD hq
    have hc : u * d = d * u := h.hDU u hu d hd
    have e : (u * d) ^ 2 = u ^ 2 * d ^ 2 := by
      calc (u * d) ^ 2 = u * (d * u) * d := by simp [pow_two, mul_assoc]
        _ = u * (u * d) * d := by rw [← hc]
        _ = u ^ 2 * d ^ 2 := by simp [pow_two, mul_assoc]
    rw [e, h.hU2 u hu, one_mul]
    exact sq_mem_sqSub hd
  · obtain ⟨u, hu, d, hd, rfl⟩ := h.mem_UD hq
    obtain ⟨u', hu', d', hd', rfl⟩ := h.mem_UD hq'
    have huu : u * u' = u' * u := h.rank1.U_comm u hu u' hu'
    have c1 : ∀ v ∈ U, ∀ e ∈ D, v * e = e * v := h.hDU
    have e : u * d * (u' * d') * (u * d)⁻¹ * (u' * d')⁻¹ =
        (u * u' * u⁻¹ * u'⁻¹) * (d * d' * d⁻¹ * d'⁻¹) := by
      have k1 := c1 u' hu' d hd
      have k2' := c1 u⁻¹ (inv_mem hu) d' hd'
      have k4' := c1 u⁻¹ (inv_mem hu) d hd
      have k8 := c1 u⁻¹ (inv_mem hu) d⁻¹ (inv_mem hd)
      calc u * d * (u' * d') * (u * d)⁻¹ * (u' * d')⁻¹
          = u * (d * u') * d' * d⁻¹ * u⁻¹ * d'⁻¹ * u'⁻¹ := by group
        _ = u * (u' * d) * d' * d⁻¹ * u⁻¹ * d'⁻¹ * u'⁻¹ := by rw [k1]
        _ = u * u' * d * d' * (d⁻¹ * u⁻¹) * d'⁻¹ * u'⁻¹ := by group
        _ = u * u' * d * d' * (u⁻¹ * d⁻¹) * d'⁻¹ * u'⁻¹ := by rw [k8]
        _ = u * u' * d * (d' * u⁻¹) * d⁻¹ * d'⁻¹ * u'⁻¹ := by group
        _ = u * u' * d * (u⁻¹ * d') * d⁻¹ * d'⁻¹ * u'⁻¹ := by rw [k2']
        _ = u * u' * (d * u⁻¹) * d' * d⁻¹ * d'⁻¹ * u'⁻¹ := by group
        _ = u * u' * (u⁻¹ * d) * d' * d⁻¹ * d'⁻¹ * u'⁻¹ := by rw [k4']
        _ = u * u' * u⁻¹ * (d * d' * d⁻¹ * d'⁻¹) * u'⁻¹ := by group
        _ = u * u' * u⁻¹ * u'⁻¹ * (d * d' * d⁻¹ * d'⁻¹) := by
            have hm : d * d' * d⁻¹ * d'⁻¹ ∈ D :=
              mul_mem (mul_mem (mul_mem hd hd') (inv_mem hd)) (inv_mem hd')
            have := c1 u'⁻¹ (inv_mem hu') _ hm
            rw [mul_assoc (u * u' * u⁻¹), ← this, ← mul_assoc]
    rw [e]
    have e2 : u * u' * u⁻¹ * u'⁻¹ = 1 := by rw [huu]; group
    rw [e2, one_mul]
    exact commutator_mem_sqSub hd hd'

theorem inf_le [Finite G] {A : Subgroup G} (hA : ModElem B (sqSub D) A) {a : G} (haA : a ∈ A)
    (haQ : a ∉ Q) : A ⊓ Q ≤ W ⊔ D := by
  intro q' ⟨hqA, hqQ⟩
  have haB : a ∈ B := hA.1 haA
  obtain ⟨u, hu, d, hd, rfl⟩ := h.mem_UD hqQ
  have hcomm := hA.2.2 a haA (u * d) hqA
  set e := a * d * a⁻¹ * d⁻¹ with he
  have heF : e ∈ sqSub D := h.comm_B_D haB hd
  have heD : e ∈ D := sqSub_le_self heF
  have hue : u * e = e * u := h.hDU u hu e heD
  have key : a * (u * d) * a⁻¹ * (u * d)⁻¹ = (a * u * a⁻¹ * u⁻¹) * (u * e * u⁻¹) := by
    rw [he]; group
  have hue' : u * e * u⁻¹ = e := by rw [hue]; group
  rw [key, hue'] at hcomm
  have hc : a * u * a⁻¹ * u⁻¹ ∈ sqSub D := by
    have := mul_mem hcomm (inv_mem heF)
    simpa [mul_assoc] using this
  have hcU : a * u * a⁻¹ * u⁻¹ ∈ U := by
    have h1 : a * u * a⁻¹ ∈ U := (mem_normalizer_iff.mp (h.rank1.B_le_normU haB) u).mp hu
    exact mul_mem h1 (inv_mem hu)
  have huW : u ∈ W := h.cent_mod a haB haQ u hu (mem_Z_of_mem_sqSub hcU hc)
  exact mul_mem (mem_sup_left huW) (mem_sup_right hd)

theorem mem_sup_conj [Finite G] {A : Subgroup G} (hA : ModElem B (sqSub D) A) {a : G}
    (haA : a ∈ A) (haQ : a ∉ Q) : a ∈ conjSubgroup U x ⊔ D := by
  have haB : a ∈ B := hA.1 haA
  have hUxN : conjSubgroup U x ≤ normalizer (Q : Set G) :=
    h.conj_le_B.trans h.rank1.B_le_normQ
  have haB' := haB
  rw [← h.sup_eq_B] at haB'
  obtain ⟨u', hu', q', hq', rfl⟩ := mem_sup_of_le_normalizer hUxN haB'
  obtain ⟨u, hu, d, hd, rfl⟩ := h.mem_UD hq'
  have hsq := hA.2.1 _ haA
  have hdu' : u' * d = d * u' := h.hDUx u' hu' d hd
  have hdu : u * d = d * u := h.hDU u hu d hd
  have e : (u' * (u * d)) ^ 2 = (u' * u * u' * u) * d ^ 2 := by
    calc (u' * (u * d)) ^ 2 = u' * u * (d * u') * u * d := by simp [pow_two, mul_assoc]
      _ = u' * u * (u' * d) * u * d := by rw [hdu']
      _ = u' * u * u' * (d * u) * d := by simp [mul_assoc]
      _ = u' * u * u' * (u * d) * d := by rw [hdu]
      _ = (u' * u * u' * u) * d ^ 2 := by simp [pow_two, mul_assoc]
  rw [e] at hsq
  have hcF : u' * u * u' * u ∈ sqSub D := by
    have := mul_mem hsq (inv_mem (sq_mem_sqSub hd))
    simpa [mul_assoc] using this
  have hu'2 : u' ^ 2 = 1 := h.sq_conj hu'
  have hu'inv : u'⁻¹ = u' := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hu'2]
  have hu2 : u ^ 2 = 1 := h.hU2 u hu
  have huinv : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hu2]
  have hu'B : u' ∈ B := h.conj_le_B hu'
  have hcU : u' * u * u' * u ∈ U := by
    have h1 : u' * u * u'⁻¹ ∈ U := (mem_normalizer_iff.mp (h.rank1.B_le_normU hu'B) u).mp hu
    rw [hu'inv] at h1
    exact mul_mem h1 hu
  have hu'Q : u' ∉ Q := by
    intro hu'Q
    exact haQ (mul_mem hu'Q (h.hQ ▸ hq'))
  have hc' : u' * u * u'⁻¹ * u⁻¹ ∈ U ⊓ D := by
    rw [hu'inv, huinv]
    exact mem_Z_of_mem_sqSub hcU hcF
  have huW : u ∈ W := h.cent_mod u' hu'B hu'Q u hu hc'
  have huUx : u ∈ conjSubgroup U x := h.W_le_conj huW
  rw [← mul_assoc]
  exact mul_mem (mem_sup_left (mul_mem hu' huUx)) (mem_sup_right hd)

theorem card_Q [Finite G] : Nat.card Q * Nat.card ↥(U ⊓ D) = Nat.card U * Nat.card D := by
  have hN : U ≤ normalizer (D : Set G) := le_normalizer_of_commute h.hDU
  have := card_sup_mul_card_inf_of_le_normalizer hN
  rwa [← h.hQ] at this

theorem conj_inf_D [Finite G] : conjSubgroup U x ⊓ D = U ⊓ D := by
  apply le_antisymm
  · rintro v ⟨hvx, hvD⟩
    have hvQ : v ∈ conjSubgroup U x ⊓ Q := ⟨hvx, h.D_le_Q hvD⟩
    rw [h.rank1.inf_Q_conj h.hx h.hx2, h.rank1.conj_W h.hx h.hx1 h.hx2] at hvQ
    exact ⟨h.rank1.W_le_U hvQ, hvD⟩
  · rintro v ⟨hvU, hvD⟩
    exact ⟨h.W_le_conj (h.hZW ⟨hvU, hvD⟩), hvD⟩

theorem card_conj_sup [Finite G] : Nat.card ↥(conjSubgroup U x ⊔ D) = Nat.card Q := by
  have hN : conjSubgroup U x ≤ normalizer (D : Set G) := le_normalizer_of_commute h.hDUx
  have h1 := card_sup_mul_card_inf_of_le_normalizer hN
  rw [h.conj_inf_D, card_conjSubgroup] at h1
  have h2 := h.card_Q
  have hpos : 0 < Nat.card ↥(U ⊓ D) := Nat.card_pos
  have h3 : Nat.card ↥(conjSubgroup U x ⊔ D) * Nat.card ↥(U ⊓ D) =
      Nat.card Q * Nat.card ↥(U ⊓ D) := by rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_right hpos h3

theorem eq_of_modElem [Finite G] {A : Subgroup G} (hA : ModElem B (sqSub D) A)
    (hcard : Nat.card Q ≤ Nat.card A) : A = Q ∨ A = conjSubgroup U x ⊔ D := by
  by_cases hAQ : A ≤ Q
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hAQ hcard)
  · right
    obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
    have hle : A ≤ conjSubgroup U x ⊔ D := by
      intro b hb
      by_cases hbQ : b ∈ Q
      · exact (sup_le_sup_right h.W_le_conj D) (h.inf_le hA haA haQ ⟨hb, hbQ⟩)
      · exact h.mem_sup_conj hA hb hbQ
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_conj_sup]; exact hcard)

theorem mem_normalizer_sqSub [Finite G] : x ∈ normalizer ((sqSub D : Subgroup G) : Set G) :=
  conjSubgroup_eq_iff_mem_normalizer.mp
    (h.rank1.conj_sqSub h.hU2 h.hQ h.hDU h.hx h.hx1 h.hx2)

theorem conj_Q [Finite G] {y : G} (hyB : y ∈ normalizer (B : Set G))
    (hyF : y ∈ normalizer ((sqSub D : Subgroup G) : Set G)) (hyU : ¬ conjSubgroup U y ≤ Q) :
    conjSubgroup Q y = conjSubgroup U x ⊔ D ∧ conjSubgroup Q (y * y) = Q := by
  have hQy := h.modElem_Q.conj hyB hyF
  have hne : conjSubgroup Q y ≠ Q := fun he =>
    hyU (he ▸ conjSubgroup_mono h.rank1.U_le_Q y)
  have h1 : conjSubgroup Q y = conjSubgroup U x ⊔ D :=
    (h.eq_of_modElem hQy (by rw [card_conjSubgroup])).resolve_left hne
  refine ⟨h1, ?_⟩
  have hQyy := hQy.conj hyB hyF
  rw [conjSubgroup_conjSubgroup] at hQyy
  rcases h.eq_of_modElem hQyy (by rw [card_conjSubgroup]) with h2 | h2
  · exact h2
  · exfalso
    apply hne
    have h3 : conjSubgroup (conjSubgroup Q y) y = conjSubgroup Q y := by
      rw [conjSubgroup_conjSubgroup, h2, h1]
    have h4 := congrArg (fun A => conjSubgroup A y⁻¹) h3
    simp only [conjSubgroup_conjSubgroup_inv] at h4
    exact h4

theorem conj_le_of_odd [Finite G] {y : G} (hyB : y ∈ normalizer (B : Set G))
    (hyF : y ∈ normalizer ((sqSub D : Subgroup G) : Set G)) (hodd : Odd (orderOf y)) :
    conjSubgroup U y ≤ Q := by
  by_contra hyU
  have hyy : y * y ∈ normalizer (Q : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp (h.conj_Q hyB hyF hyU).2
  obtain ⟨k, hk⟩ := hodd
  have hy : y = (y * y) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul]
    have : y ^ (2 * (k + 1)) = y ^ (orderOf y) * y := by
      rw [hk, ← pow_succ]; ring_nf
    rw [this, pow_orderOf_eq_one, one_mul]
  have hyQ : y ∈ normalizer (Q : Set G) := by rw [hy]; exact pow_mem hyy _
  exact hyU ((conjSubgroup_eq_iff_mem_normalizer.mpr hyQ) ▸ conjSubgroup_mono h.rank1.U_le_Q y)

theorem mem_or_mem [Finite G] {m : G} (hmB : m ∈ normalizer (B : Set G))
    (hmF : m ∈ normalizer ((sqSub D : Subgroup G) : Set G)) :
    m ∈ normalizer (Q : Set G) ∨ m * x⁻¹ ∈ normalizer (Q : Set G) := by
  have hQm := h.modElem_Q.conj hmB hmF
  have hQx := (h.conj_Q h.hx h.mem_normalizer_sqSub h.hx1).1
  rcases h.eq_of_modElem hQm (by rw [card_conjSubgroup]) with h1 | h1
  · exact Or.inl (conjSubgroup_eq_iff_mem_normalizer.mp h1)
  · right
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_conjSubgroup, h1, ← hQx,
      conjSubgroup_conjSubgroup_inv]

theorem mem_Q_of_comm [Finite G] {z : G} (hzB : z ∈ B)
    (hz : ∀ b ∈ B, z * b * z⁻¹ * b⁻¹ ∈ sqSub D) : z ∈ Q := by
  by_contra hzQ
  have hWU : ¬ U ≤ W := by
    intro hle
    have h1 := h.rank1.idx_W
    rw [Subgroup.relIndex_eq_one.mpr hle] at h1
    have := h.hq
    omega
  obtain ⟨u, hu, huW⟩ := IsConcreteLE.not_le_iff_exists.mp hWU
  have hc := hz u (h.rank1.U_le_B hu)
  have hcU : z * u * z⁻¹ * u⁻¹ ∈ U := by
    have h1 : z * u * z⁻¹ ∈ U := (mem_normalizer_iff.mp (h.rank1.B_le_normU hzB) u).mp hu
    exact mul_mem h1 (inv_mem hu)
  exact huW (h.cent_mod z hzB hzQ u hu (mem_Z_of_mem_sqSub hcU hc))

theorem conj_D_le [Finite G] {g : G} (hgB : g ∈ normalizer (B : Set G))
    (hgF : g ∈ normalizer ((sqSub D : Subgroup G) : Set G)) : conjSubgroup D g ≤ Q := by
  intro e he
  have heD : g * e * g⁻¹ ∈ D := mem_conjSubgroup_iff.mp he
  have heB : e ∈ B := by
    have h1 : conjSubgroup D g ≤ conjSubgroup B g := conjSubgroup_mono
      (h.D_le_Q.trans h.rank1.Q_le_B) g
    rw [conjSubgroup_eq_iff_mem_normalizer.mpr hgB] at h1
    exact h1 he
  refine h.mem_Q_of_comm heB fun b hb => ?_
  have hb' : g * b * g⁻¹ ∈ B := (mem_normalizer_iff.mp hgB b).mp hb
  have h1 := h.comm_B_D hb' heD
  have h2 : g * e * g⁻¹ * (g * b * g⁻¹) * (g * e * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ ∈ sqSub D := by
    have := inv_mem h1
    have e2 : (g * b * g⁻¹ * (g * e * g⁻¹) * (g * b * g⁻¹)⁻¹ * (g * e * g⁻¹)⁻¹)⁻¹ =
        g * e * g⁻¹ * (g * b * g⁻¹) * (g * e * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by group
    rwa [e2] at this
  have hF : conjSubgroup (sqSub D) g = sqSub D := conjSubgroup_eq_iff_mem_normalizer.mpr hgF
  rw [← hF, mem_conjSubgroup_iff]
  have e3 : g * (e * b * e⁻¹ * b⁻¹) * g⁻¹ =
      g * e * g⁻¹ * (g * b * g⁻¹) * (g * e * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ := by group
  rwa [e3]

end PairDataZ

end CFSG.Quasithin.C58NS
