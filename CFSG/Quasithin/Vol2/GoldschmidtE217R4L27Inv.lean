module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4L27
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4L27Psl

public section

namespace CFSG.Quasithin

open scoped MatrixGroups

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer

namespace E217R4

section Psl

variable {F : Type} [Field F] [Fintype F]

theorem not_isSquare_neg_one (hF7 : Fintype.card F = 7) : ¬ IsSquare (-1 : F) := by
  classical
  intro hsq
  obtain ⟨x, hxT, hx2⟩ := (CFSG.PSL2Table.exists_involution_splitTorus_iff
    (psl7_basic hF7).1).2 hsq
  have := Subgroup.orderOf_dvd_natCard (CFSG.PSL2Table.splitTorus F) hxT
  rw [hx2, card_splitTorus_seven hF7] at this
  omega

theorem cent2_psl (hF7 : Fintype.card F = 7) {z : PSL(2, F)} (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card (Subgroup.centralizer ({z} : Set PSL(2, F))) = 8 := by
  classical
  obtain ⟨hF2, hcard⟩ := psl7_basic hF7
  have hq : 5 ≤ Fintype.card F := by omega
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF2
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  obtain ⟨x, hxS, hzx⟩ := (CFSG.PSL2Table.involution_conj_torus hF2 hq hν hord).2
    (not_isSquare_neg_one hF7)
  obtain ⟨c, hc⟩ := isConj_iff.1 hzx
  have hxord : orderOf x = 2 := by
    rw [← hc]
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective z
    simpa [hord] using this
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hxord
  have hx2 : x ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxord] at this
  have hcx : Nat.card (Subgroup.centralizer ({x} : Set PSL(2, F))) = 8 := by
    rw [CFSG.PSL2Table.card_centralizer_nonsplitTorus hF2 hq hν hxS hx1]
    simp only [hx2, ↓reduceIte]
    rw [CFSG.Glauberman.Dickson.MaxStructure.card_nonsplitTorus_eq hF2 hν, hF7]
  rw [← hcx, ← hc, card_centralizer_conj]

theorem inv3_psl (hF7 : Fintype.card F = 7) {z : PSL(2, F)} (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ a : PSL(2, F), a ^ 3 = 1 ∧ a ≠ 1 ∧ z * a * z⁻¹ = a⁻¹ := by
  classical
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨7, 1, by norm_num, by decide, le_rfl, by rw [Nat.card_eq_fintype_card, hF7]; norm_num⟩
  have hw1 : CFSG.PSL2Table.splitWeyl F ≠ 1 := fun h1 => CFSG.PSL2Table.splitWeyl_not_mem
    (h1 ▸ (CFSG.PSL2Table.splitTorus F).one_mem)
  obtain ⟨g, hg⟩ := CFSG.GorensteinWalter.psl2_involutions_conjugate_of_odd_prime_power F hodd
    (CFSG.PSL2Table.splitWeyl F) z ⟨hw1, by rw [pow_two]; exact CFSG.PSL2Table.splitWeyl_mul_self⟩
    ⟨hz1, by rw [pow_two]; exact hz2⟩
  have hT : CFSG.PSL2Table.splitTorus F ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot _).1 (by rw [card_splitTorus_seven hF7]; omega)
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hT
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht3 : t ^ 3 = 1 := by
    have := pow_card_eq_one' (x := (⟨t, ht⟩ : ↥(CFSG.PSL2Table.splitTorus F)))
    rw [card_splitTorus_seven hF7] at this
    exact congrArg Subtype.val this
  refine ⟨g * t * g⁻¹, ?_, ?_, ?_⟩
  · rw [conj_pow, ht3]
    group
  · intro h1
    apply ht1'
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, h1]
    group
  · rw [← hg]
    have hc := CFSG.PSL2Table.splitWeyl_conj ht
    calc g * CFSG.PSL2Table.splitWeyl F * g⁻¹ * (g * t * g⁻¹) *
          (g * CFSG.PSL2Table.splitWeyl F * g⁻¹)⁻¹
        = g * (CFSG.PSL2Table.splitWeyl F * t * (CFSG.PSL2Table.splitWeyl F)⁻¹) * g⁻¹ := by group
      _ = g * t⁻¹ * g⁻¹ := by rw [hc]
      _ = (g * t * g⁻¹)⁻¹ := by group

omit [Fintype F] in
theorem card2_of_card {K : Type*} [Group K] (hcard : Nat.card K = 168) {D : Subgroup K}
    (hD : IsSylowTwoOf D ⊤) : Nat.card D = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hD.2.1
  have hidx : ¬ 2 ∣ D.index := by
    have h := hD.2.2
    rwa [show (D.subgroupOf ⊤).index = D.index from Subgroup.relIndex_top_right _] at h
  have h1 := Subgroup.card_mul_index D
  rw [hk, hcard] at h1
  have hk7 : k ≤ 7 := by
    by_contra hlt
    have : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 0 < D.index := Nat.pos_of_ne_zero fun h0 => by rw [h0] at h1; omega
    nlinarith
  have hk3 : k = 3 := by
    interval_cases k <;> omega
  rw [hk, hk3]
  norm_num

theorem l27_psl (hF7 : Fintype.card F = 7) : L27 PSL(2, F) :=
  ⟨fun _ _ ha ha1 ha' ha'1 => sylow3_elem (psl7_basic hF7).2 ha ha1 ha' ha'1,
   fun _ hx hx1 _ hy => cent3_psl hF7 hx hx1 hy,
   fun _ hz2 hz1 => cent2_psl hF7 hz2 hz1,
   fun _ hz2 hz1 => inv3_psl hF7 hz2 hz1,
   fun _ hD => card2_of_card (psl7_basic hF7).2 hD,
   Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
     (by rw [Nat.card_eq_fintype_card, hF7]; norm_num)⟩

end Psl

end E217R4

end CFSG.Quasithin
