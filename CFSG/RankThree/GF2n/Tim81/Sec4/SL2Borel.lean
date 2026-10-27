module

public import CFSG.RankThree.GF2n.Tim81.Sec4.SL2WeaklyClosed
public import CFSG.CGT.Timmesfeld75.L2Basic

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec4

open scoped MatrixGroups
open CFSG.CGT.Timmesfeld75

section BorelFacts

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem exists_conj_eq_utri {T : Subgroup SL(2, F)} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hwc : ∀ g : SL(2, F), conjSubgroup g T ≤ Subgroup.normalizer (T : Set SL(2, F)) →
      conjSubgroup g T = T) :
    ∃ x : SL(2, F), T = conjSubgroup x (utri F) := by
  have hcardT : Nat.card T = Nat.card F := by
    rw [Nat.card_eq_fintype_card (α := F)]
    exact (card_eq_of_weaklyClosed hT hT1 hwc).1
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  obtain ⟨x, hxP⟩ := exists_conjSubgroup_utri_eq_of_sylow P
  refine ⟨x, ?_⟩
  have hle : T ≤ conjSubgroup x (utri F) := by rw [hxP]; exact hTP
  have hcard : Nat.card (conjSubgroup x (utri F)) = Nat.card T := by
    rw [card_conjSubgroup, card_utri, hcardT]
  exact Subgroup.eq_of_le_of_card_ge hle hcard.le

theorem exists_frobeniusComplement {T : Subgroup SL(2, F)} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hwc : ∀ g : SL(2, F), conjSubgroup g T ≤ Subgroup.normalizer (T : Set SL(2, F)) →
      conjSubgroup g T = T) :
    ∃ D : Subgroup SL(2, F),
      D ≤ Subgroup.normalizer (T : Set SL(2, F)) ∧
      Nat.card D = Nat.card T - 1 ∧
      (∀ a ∈ D, ∀ b ∈ D, a * b = b * a) ∧
      (∀ d ∈ D, d ≠ 1 → ∀ x ∈ T, d * x * d⁻¹ = x → x = 1) := by
  obtain ⟨x, hT_eq⟩ := exists_conj_eq_utri hT hT1 hwc
  have hcardT : Nat.card T = Nat.card F := by
    rw [Nat.card_eq_fintype_card (α := F)]
    exact (card_eq_of_weaklyClosed hT hT1 hwc).1
  refine ⟨conjSubgroup x (torus F), ?_, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨t, ht, rfl⟩ := hd
    rw [hT_eq]
    have htn : t ∈ Subgroup.normalizer (utri F : Set SL(2, F)) := by
      rw [normalizer_utri]
      exact torus_le_borel ht
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom htn
    rw [Subgroup.map_equiv_normalizer_eq] at hmem
    simpa [conjSubgroup, MulAut.conj_apply] using hmem
  · rw [card_conjSubgroup, card_torus, hcardT]
  · intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨q, hq, rfl⟩ := hb
    obtain ⟨p', rfl⟩ := mem_torus_iff.1 hp
    obtain ⟨q', rfl⟩ := mem_torus_iff.1 hq
    change (x * torusElt p' * x⁻¹) * (x * torusElt q' * x⁻¹) =
      (x * torusElt q' * x⁻¹) * (x * torusElt p' * x⁻¹)
    calc (x * torusElt p' * x⁻¹) * (x * torusElt q' * x⁻¹)
        = x * (torusElt p' * torusElt q') * x⁻¹ := by group
      _ = x * torusElt (p' * q') * x⁻¹ := by rw [torusElt_mul]
      _ = x * torusElt (q' * p') * x⁻¹ := by rw [mul_comm]
      _ = x * (torusElt q' * torusElt p') * x⁻¹ := by rw [torusElt_mul]
      _ = (x * torusElt q' * x⁻¹) * (x * torusElt p' * x⁻¹) := by group
  · intro d hd hd1 y hy hfix
    obtain ⟨t, ht, rfl⟩ := hd
    obtain ⟨q, rfl⟩ := mem_torus_iff.1 ht
    rw [hT_eq] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    have hfix' : (MulAut.conj x) (torusElt q * u * (torusElt q)⁻¹) = (MulAut.conj x) u := by
      simpa [map_mul, map_inv] using hfix
    have hpu : torusElt q * u * (torusElt q)⁻¹ = u := (MulAut.conj x).injective hfix'
    have hu1 : u = 1 := by
      by_contra hu_ne
      obtain ⟨s, rfl⟩ := mem_utri_iff.1 hu
      have hs : s ≠ 0 := by
        rintro rfl
        exact hu_ne utriElt_zero
      have hcent : torusElt q ∈ Subgroup.centralizer ({utriElt s} : Set (SL(2, F))) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc torusElt q * utriElt s
            = (torusElt q * utriElt s * (torusElt q)⁻¹) * torusElt q := by group
          _ = utriElt s * torusElt q := by rw [hpu]
      rw [centralizer_utriElt hs] at hcent
      have hbot : torusElt q ∈ (⊥ : Subgroup SL(2, F)) := by
        rw [← inf_utri_torus]
        exact ⟨hcent, torusElt_mem_torus q⟩
      have hq1 : torusElt q = 1 := Subgroup.mem_bot.1 hbot
      exact hd1 (by simp [hq1])
    rw [hu1]
    exact (MulAut.conj x).map_one

theorem inf_eq_bot_of_weaklyClosed_ne {T T' : Subgroup SL(2, F)} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hwc : ∀ g : SL(2, F), conjSubgroup g T ≤ Subgroup.normalizer (T : Set SL(2, F)) →
      conjSubgroup g T = T)
    (hT' : IsPGroup 2 T') (hT1' : T' ≠ ⊥)
    (hwc' : ∀ g : SL(2, F), conjSubgroup g T' ≤ Subgroup.normalizer (T' : Set SL(2, F)) →
      conjSubgroup g T' = T')
    (hne : T ≠ T') : T ⊓ T' = ⊥ := by
  obtain ⟨x, hx⟩ := exists_conj_eq_utri hT hT1 hwc
  obtain ⟨y, hy⟩ := exists_conj_eq_utri hT' hT1' hwc'
  have hxy : conjSubgroup x (utri F) ≠ conjSubgroup y (utri F) := by
    intro h
    exact hne (by rw [hx, hy, h])
  rw [hx, hy]
  exact inf_conjSubgroup_utri_eq_bot hxy

theorem exists_involution_conj_eq_of_weaklyClosed_ne {T T' : Subgroup SL(2, F)}
    (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hwc : ∀ g : SL(2, F), conjSubgroup g T ≤ Subgroup.normalizer (T : Set SL(2, F)) →
      conjSubgroup g T = T)
    (hT' : IsPGroup 2 T') (hT1' : T' ≠ ⊥)
    (hwc' : ∀ g : SL(2, F), conjSubgroup g T' ≤ Subgroup.normalizer (T' : Set SL(2, F)) →
      conjSubgroup g T' = T')
    (hne : T ≠ T') :
    ∃ t : SL(2, F), t * t = 1 ∧ t ≠ 1 ∧ conjSubgroup t T = T' ∧ conjSubgroup t T' = T := by
  obtain ⟨a, ha⟩ := exists_conj_eq_utri hT hT1 hwc
  obtain ⟨b, hb⟩ := exists_conj_eq_utri hT' hT1' hwc'
  have hab : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F) := by
    intro h
    exact hne (by rw [ha, hb, h])
  obtain ⟨g, hP, hQ⟩ := exists_conj_utri_ltri_of_ne hab
  have hw2 : (wElt : SL(2, F)) * wElt = 1 := by
    have h := CFSG.Glauberman.Dickson.standardSplitWeylSL_sq_mem_center F
    rw [center_sl2_eq_bot, Subgroup.mem_bot] at h
    simpa [wElt] using h
  have hw1 : (wElt : SL(2, F)) ≠ 1 := by
    intro h
    have h01 := congrArg (fun z : SL(2, F) => z 0 1) h
    rw [wElt_apply_01, one_apply_01] at h01
    exact (neg_ne_zero.mpr one_ne_zero) h01
  let t : SL(2, F) := g * wElt * g⁻¹
  have htt : t * t = 1 := by
    change g * wElt * g⁻¹ * (g * wElt * g⁻¹) = 1
    calc g * wElt * g⁻¹ * (g * wElt * g⁻¹) = g * (wElt * wElt) * g⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  have ht1 : t ≠ 1 := by
    intro h
    apply hw1
    have := congrArg (fun z : SL(2, F) => g⁻¹ * z * g) h
    simpa [t, mul_assoc] using this
  have hconj : conjSubgroup t T = T' := by
    rw [ha, hb, hP, hQ]
    change conjSubgroup (g * wElt * g⁻¹) (conjSubgroup g (utri F)) = conjSubgroup g (ltri F)
    calc conjSubgroup (g * wElt * g⁻¹) (conjSubgroup g (utri F))
        = conjSubgroup ((g * wElt * g⁻¹) * g) (utri F) := conjSubgroup_conjSubgroup _ g _
      _ = conjSubgroup (g * wElt) (utri F) := by
            rw [show (g * wElt * g⁻¹) * g = g * wElt by group]
      _ = conjSubgroup g (conjSubgroup wElt (utri F)) :=
            (conjSubgroup_conjSubgroup g wElt (utri F)).symm
      _ = conjSubgroup g (ltri F) := by rw [conjSubgroup_wElt_utri]
  have hconj' : conjSubgroup t T' = T := by
    rw [← hconj, conjSubgroup_conjSubgroup, htt, conjSubgroup_one]
  exact ⟨t, htt, ht1, hconj, hconj'⟩

end BorelFacts

end CFSG.RankThree.GF2n.Tim81.Sec4
