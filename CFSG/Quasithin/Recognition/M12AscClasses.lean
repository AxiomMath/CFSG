module

public import CFSG.Quasithin.Recognition.M12AscCountH
public import CFSG.Quasithin.Recognition.M12AscI1
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.Quasithin

open Subgroup CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {G : Type*} [Group G] {z : G}

open CFSG.GH74.M12 (Asc03Hyp)

theorem exists_conj_data [Finite G] (hyp : Asc03Hyp G z) :
    ∃ g : G, g * z * g⁻¹ ≠ z ∧ g * z * g⁻¹ ∈ ascQ z := by
  obtain ⟨g, hgz, q, hqP, hq⟩ := hyp.not_weakly_closed
  refine ⟨g, hgz, ?_⟩
  rw [← hq]
  exact (mem_ascQ_iff z _).2 ⟨q.2, hqP⟩

namespace AscModel

variable (m : AscModel z)

include m

theorem tb_pow {g : G} (hg : g ∈ ascH z) (k : ℕ) : m.tb (g ^ k) = tpow (m.tb g) k := by
  induction k with
  | zero => rw [pow_zero, m.tb_one]; rfl
  | succ k ih =>
    rw [pow_succ', m.tb_mul hg (Subgroup.pow_mem _ hg k), ih]
    rfl

theorem outInv_isConj [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) {b : G}
    (hbH : b ∈ ascH z) (hbQ : b ∉ ascQ z) (hb2 : b * b = 1) : IsConj z b := by
  obtain ⟨g, hgz, hsQ⟩ := exists_conj_data hyp
  have hEF := m.E_ne_fSub hyp hgz hsQ
  obtain ⟨-, -, -, -, v₀, hv₀, hv₀o, hv₀Q⟩ := config_of_conj hyp hgz hsQ
  have hv₀2 : v₀ * v₀ = 1 := by
    have := pow_orderOf_eq_one v₀
    rwa [hv₀o, pow_two] at this
  obtain ⟨x₀, hx₀⟩ := m.outer_involution_conj_z hyp hgz hsQ hEF hv₀ hv₀2 hv₀Q
  obtain ⟨h, hh, hhv⟩ := m.outInv_orbit_G hyp hv₀.1 hv₀Q hv₀2 hbH hbQ hb2
  refine isConj_iff.2 ⟨h * x₀, ?_⟩
  calc h * x₀ * z * (h * x₀)⁻¹ = h * (x₀ * z * x₀⁻¹) * h⁻¹ := by group
    _ = h * v₀ * h⁻¹ := by rw [hx₀]
    _ = b := by rw [hhv]; group

theorem involution_classes [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) {t : G}
    (htQ : t ∈ ascQ z) (htF : t ∉ m.fSub) (ht2 : t * t = 1) {x : G} (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : IsConj z x ∨ IsConj t x := by
  obtain ⟨g, hgz, hsQ⟩ := exists_conj_data hyp
  have hEF := m.E_ne_fSub hyp hgz hsQ
  have htq : t ∈ m.qSub := by rwa [m.ascQ_eq_qSub hyp] at htQ
  rcases m.involution_conj_z_or_t hyp hgz hsQ hEF htq htF ht2 hx2 hx1 with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact Or.inl (isConj_iff.2 ⟨c, hc⟩)
  · exact Or.inr (isConj_iff.2 ⟨c, hc⟩)

theorem isConj_t_iff [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) {t : G}
    (htQ : t ∈ ascQ z) (htF : t ∉ m.fSub) (ht2 : t * t = 1) {a : G} (haH : a ∈ ascH z) :
    IsConj t a ↔ a ∈ ascQ z ∧ a ∉ m.fSub ∧ a * a = 1 := by
  have hnc := m.not_isConj_of_notMem_fSub hyp htQ htF
  have ht1 : t ≠ 1 := fun e => htF (e ▸ one_mem _)
  constructor
  · intro hta
    obtain ⟨c, hc⟩ := isConj_iff.1 hta
    have ha2 : a * a = 1 := by
      rw [← hc]
      calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have ha1 : a ≠ 1 := by
      intro e
      apply ht1
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [hc, e]; group
    by_cases haQ : a ∈ ascQ z
    · refine ⟨haQ, fun haF => ?_, ha2⟩
      obtain ⟨d, hd⟩ := (m.conj_mem_Q_iff hyp haQ ha1).2 haF
      exact hnc ((isConj_iff.2 ⟨d, hd⟩).trans hta.symm)
    · exact absurd ((m.outInv_isConj hyp haH haQ ha2).trans hta.symm) hnc
  · rintro ⟨haQ, haF, ha2⟩
    have htq : t ∈ m.qSub := by rwa [m.ascQ_eq_qSub hyp] at htQ
    have haq : a ∈ m.qSub := by rwa [m.ascQ_eq_qSub hyp] at haQ
    obtain ⟨h, -, hht⟩ := m.qSub_outF_orbit htq htF ht2 haq haF ha2
    exact isConj_iff.2 ⟨h, by rw [hht]; group⟩

theorem isConj_z_iff [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) {b : G}
    (hbH : b ∈ ascH z) :
    IsConj z b ↔ b * b = 1 ∧ b ≠ 1 ∧ (b ∉ ascQ z ∨ b ∈ m.fSub) := by
  constructor
  · intro hzb
    obtain ⟨c, hc⟩ := isConj_iff.1 hzb
    refine ⟨by rw [← hc]; exact asc_conj_sq hyp c, by rw [← hc]; exact asc_conj_ne_one hyp c, ?_⟩
    by_cases hbQ : b ∈ ascQ z
    · exact Or.inr (m.zconj_mem_fSub hyp hbQ hzb)
    · exact Or.inl hbQ
  · rintro ⟨hb2, hb1, hbQ | hbF⟩
    · exact m.outInv_isConj hyp hbH hbQ hb2
    · obtain ⟨c, hc⟩ := (m.conj_mem_Q_iff hyp (m.fSub_le_ascQ hyp hbF) hb1).2 hbF
      exact isConj_iff.2 ⟨c, hc⟩

theorem card_thompsonPairs_z [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) {t : G}
    (htQ : t ∈ ascQ z) (htF : t ∉ m.fSub) (ht2 : t * t = 1) :
    thompsonPairCount t z z = 240 := by
  classical
  have hz2 : z * z = 1 := asc_z_sq hyp
  have hmemP : ∀ p ∈ thompsonPairs t z z, p.1 ∈ ascH z ∧ p.2 ∈ ascH z := fun p hp =>
    mem_centralizer_of_mem_thompsonPairs ht2 hz2 hz2 hp
  have key : ∀ p ∈ thompsonPairs t z z, (m.tb p.1, m.tb p.2) ∈ pairTabsZ := by
    intro p hp
    obtain ⟨haH, hbH⟩ := hmemP p hp
    obtain ⟨hta, hzb, hmem⟩ := mem_thompsonPairs.1 hp
    obtain ⟨haQ, haF, ha2⟩ := (m.isConj_t_iff hyp htQ htF ht2 haH).1 hta
    obtain ⟨hb2, hb1, hbQF⟩ := (m.isConj_z_iff hyp hbH).1 hzb
    rw [mem_pairTabsZ]
    have hab : p.1 * p.2 ∈ ascH z := mul_mem haH hbH
    refine ⟨⟨((m.mem_ascQ_iff_tb hyp).1 haQ).2, fun h => haF (m.mem_fSub_iff.2 ⟨haH, h⟩),
      (m.mul_self_eq_one_iff haH).1 ha2⟩, ⟨m.tb_mem hbH, (m.mul_self_eq_one_iff hbH).1 hb2,
      fun h => hb1 ((m.eq_one_iff hbH).2 h), ?_⟩, ?_⟩
    · rcases hbQF with h | h
      · exact Or.inl fun h' => h ((m.mem_ascQ_iff_tb hyp).2 ⟨hbH, h'⟩)
      · exact Or.inr (m.mem_fSub_iff.1 h).2
    · have h24 : (p.1 * p.2) ^ 24 = 1 := by
        apply m.tb_inj (Subgroup.pow_mem _ hab 24) (one_mem _)
        rw [m.tb_pow hab, m.tb_one]
        exact tpow_24 _ (m.tb_mem hab)
      obtain ⟨k, hk, hkz⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1 hmem)
      have hk24 : k < 24 := by
        have h1 : orderOf (p.1 * p.2) ∣ 24 := orderOf_dvd_of_pow_eq_one h24
        have h2 := Nat.le_of_dvd (by norm_num) h1
        have h3 := Finset.mem_range.1 hk
        omega
      refine ⟨k, hk24, ?_⟩
      have := congrArg m.tb hkz
      rw [m.tb_pow hab, m.tb_mul haH hbH, m.tb_z] at this
      exact this
  let f : thompsonPairs t z z → {q : List (Fin 12) × List (Fin 12) // q ∈ pairTabsZ} :=
    fun p => ⟨(m.tb p.1.1, m.tb p.1.2), key p.1 p.2⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, b⟩, hp⟩ ⟨⟨a', b'⟩, hp'⟩ h
      obtain ⟨haH, hbH⟩ := hmemP _ hp
      obtain ⟨haH', hbH'⟩ := hmemP _ hp'
      have h1 := congrArg (fun q => q.1.1) h
      have h2 := congrArg (fun q => q.1.2) h
      simp only [f] at h1 h2
      exact Subtype.ext (Prod.ext (m.tb_inj haH haH' h1) (m.tb_inj hbH hbH' h2))
    · rintro ⟨⟨qa, qb⟩, hq⟩
      rw [mem_pairTabsZ] at hq
      obtain ⟨⟨hqa, hqaF, hqa2⟩, ⟨hqb, hqb2, hqb1, hqbQF⟩, k, hk, hkz⟩ := hq
      obtain ⟨a, haH, ha⟩ := m.exists_tb (qTabs_sub qa hqa)
      obtain ⟨b, hbH, hb⟩ := m.exists_tb hqb
      have haQ : a ∈ ascQ z := (m.mem_ascQ_iff_tb hyp).2 ⟨haH, by rw [ha]; exact hqa⟩
      have haF : a ∉ m.fSub := fun h => hqaF (by rw [← ha]; exact (m.mem_fSub_iff.1 h).2)
      have ha2 : a * a = 1 := (m.mul_self_eq_one_iff haH).2 (by rw [ha]; exact hqa2)
      have hta := (m.isConj_t_iff hyp htQ htF ht2 haH).2 ⟨haQ, haF, ha2⟩
      have hb2 : b * b = 1 := (m.mul_self_eq_one_iff hbH).2 (by rw [hb]; exact hqb2)
      have hb1 : b ≠ 1 := fun h => hqb1 (by rw [← hb]; exact (m.eq_one_iff hbH).1 h)
      have hbQF : b ∉ ascQ z ∨ b ∈ m.fSub := by
        rcases hqbQF with h | h
        · exact Or.inl fun h' => h (by rw [← hb]; exact ((m.mem_ascQ_iff_tb hyp).1 h').2)
        · exact Or.inr (m.mem_fSub_iff.2 ⟨hbH, by rw [hb]; exact h⟩)
      have hzb := (m.isConj_z_iff hyp hbH).2 ⟨hb2, hb1, hbQF⟩
      have hab : a * b ∈ ascH z := mul_mem haH hbH
      have hpow : (a * b) ^ k = z := by
        apply m.tb_inj (Subgroup.pow_mem _ hab k) (z_mem_ascH z)
        rw [m.tb_pow hab, m.tb_mul haH hbH, ha, hb, m.tb_z]
        exact hkz
      have hmem : z ∈ Subgroup.zpowers (a * b) := hpow ▸ Subgroup.npow_mem_zpowers (a * b) k
      exact ⟨⟨(a, b), mem_thompsonPairs.2 ⟨hta, hzb, hmem⟩⟩, Subtype.ext (by simp [f, ha, hb])⟩
  have hcardL : Nat.card {q : List (Fin 12) × List (Fin 12) // q ∈ pairTabsZ} =
      pairTabsZ.length := by
    have h2 : Nat.card {q : List (Fin 12) × List (Fin 12) // q ∈ pairTabsZ} =
        Nat.card ↥pairTabsZ.toFinset := Nat.card_congr (Equiv.subtypeEquivRight (by simp))
    rw [h2, Nat.card_eq_fintype_card, Fintype.card_coe,
      List.toFinset_card_of_nodup pairTabsZ_nodup]
  show Nat.card (thompsonPairs t z z) = 240
  rw [Nat.card_congr (Equiv.ofBijective f hbij), hcardL, pairTabsZ_length]

end AscModel

end CFSG.Quasithin
