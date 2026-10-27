module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsL3
public import CFSG.Quasithin.Background.HFL3Six
public import CFSG.Quasithin.Background.HFL3Four

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu

theorem hL3Nine82_holds : HL3Nine82 := by
  intro V _ _ L M hLM n hn hL
  obtain ⟨K, _, _, _, hK, e, hLe, hMN⟩ := exists_model_l3nine hLM hL
  have : Finite (L3Nine.HMod n K) := Finite.of_equiv V e.toEquiv
  have : Finite (MulAut V) := finite_mulAut V
  have hV : ∀ v : V, v ^ 2 = 1 := fun v => by
    have h := L3Nine.sq_eq_one_HMod (e v)
    rw [← map_pow] at h
    exact e.injective (h.trans (map_one e).symm)
  have hcardV : Nat.card V = 2 ^ (9 * n) := by
    rw [Nat.card_congr e.toEquiv, L3Nine.card_HMod hn hK]
  have hfixcard : ∀ X : Subgroup (MulAut V),
      Nat.card ↥(fixV (X.map (congrHom e))) = Nat.card ↥(fixV X) := by
    intro X
    rw [fixV_map_congrHom, Subgroup.card_map_of_injective e.injective]
  have hrk : ∀ U : Subgroup V, Nat.card U = 2 ^ rk ↥U := card_eq_two_pow hV
  have hrkV : ∀ U : Subgroup V, rk ↥U + rkIdx U = 9 * n := by
    intro U
    have h1 := rk_add_rkIdx U
    have h2 : rk V = 9 * n := by
      have := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
      rw [hcardV] at this
      exact (Nat.pow_right_injective (le_refl 2) this).symm
    omega
  have hzp : ∀ x : MulAut V, (Subgroup.zpowers x).map (congrHom e) =
      Subgroup.zpowers (congrHom e x) := fun x => MonoidHom.map_zpowers _ _
  have hAL : ∀ A : Subgroup (MulAut V), A ≤ L ↔ A.map (congrHom e) ≤ L3Nine.img hK := by
    intro A
    rw [← hLe]
    exact (map_congrHom_le_iff e).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hxM hx1 hodd hx4
    have hx'N : congrHom e x ∈ L3Nine.norm hK := hMN ⟨x, hxM, rfl⟩
    have hx'1 : congrHom e x ≠ 1 := fun h => hx1 (congrHom_injective e (h.trans (map_one _).symm))
    have hx'o : Odd (orderOf (congrHom e x)) := by
      rwa [orderOf_injective _ (congrHom_injective e)]
    have h5 := (L3Nine.card_fixV_odd_le hn hK hx'N hx'1 hx'o).1
    rw [← hzp, hfixcard, hrk] at h5
    have h6 : rk ↥(fixV (Subgroup.zpowers x)) ≤ 5 * n :=
      (Nat.pow_le_pow_iff_right (by norm_num)).mp h5
    have := hrkV (fixV (Subgroup.zpowers x))
    omega
  ·
    intro A hAM hAe hcase
    have hA'N : A.map (congrHom e) ≤ L3Nine.norm hK := (Subgroup.map_mono hAM).trans hMN
    have hA'e := (isElemAbelian2_map_congrHom e).2 hAe
    have hcardA : Nat.card ↥(A.map (congrHom e)) = 2 ^ rk ↥A := by
      rw [card_map_congrHom, card_eq_two_pow_rk_of hAe]
    have h1 := L3Nine.card_fixV_le_of_three hn hK hA'N hA'e (by
      rcases hcase with h | ⟨hL', h⟩
      · left
        rw [hcardA]
        exact Nat.pow_le_pow_right (by norm_num) h
      · right
        refine ⟨(hAL A).1 hL', ?_⟩
        rw [hcardA]
        exact Nat.pow_lt_pow_right (by norm_num) h)
    rw [hfixcard, hrk] at h1
    have h2 : rk ↥(fixV A) ≤ 4 * n := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    have := hrkV (fixV A)
    omega
  ·
    intro A hAL' hAe hA4 x ⟨hxM, hxN⟩ hxo
    have hA'L : A.map (congrHom e) ≤ L3Nine.img hK := (hAL A).1 hAL'
    have hA'e := (isElemAbelian2_map_congrHom e).2 hAe
    have hcardA : Nat.card ↥(A.map (congrHom e)) = Nat.card K ^ 2 := by
      rw [card_map_congrHom, card_eq_two_pow_rk_of hAe, hA4, hK, ← pow_mul, ← pow_mul]
      ring_nf
    have hx'N : congrHom e x ∈ L3Nine.norm hK := hMN ⟨x, hxM, rfl⟩
    have hx'A : congrHom e x ∈ Subgroup.normalizer
        ((A.map (congrHom e) : Subgroup (MulAut (L3Nine.HMod n K))) :
          Set (MulAut (L3Nine.HMod n K))) := by
      rw [← Subgroup.map_equiv_normalizer_eq A (MulAut.congr e)]
      exact ⟨x, hxN, rfl⟩
    have hx'o : Odd (orderOf (congrHom e x)) := by
      rw [orderOf_injective _ (congrHom_injective e), hxo]
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) (by
        rw [Nat.even_pow]
        exact ⟨even_two, by omega⟩) odd_one
    have h1 := L3Nine.card_fixV_sup_ne hn hK hA'L hA'e hcardA hx'N hx'A hx'o
    intro h3
    apply h1
    rw [← hzp, ← Subgroup.map_sup, hfixcard, hrk, h3]
  ·
    intro A hAM hAe hrkA
    rw [hAL]
    refine L3Nine.le_img_of_card hn hK ((Subgroup.map_mono hAM).trans hMN)
      ((isElemAbelian2_map_congrHom e).2 hAe) ?_
    rw [card_map_congrHom, card_eq_two_pow_rk_of hAe]
    exact Nat.pow_lt_pow_right (by norm_num) hrkA
  ·
    rintro rfl y hyM hodd hy5
    have hy'N : congrHom e y ∈ L3Nine.norm hK := hMN ⟨y, hyM, rfl⟩
    have hy'o : Odd (orderOf (congrHom e y)) := by
      rwa [orderOf_injective _ (congrHom_injective e)]
    have hfix5 : Nat.card ↥(fixV (Subgroup.zpowers (congrHom e y))) = 2 ^ 5 := by
      rw [← hzp, hfixcard, hrk, hy5]
    have h3 := L3Nine.card_centSub_fixV_le hK hy'N hy'o hfix5
    have hmap : (M ⊓ centSub (fixV (Subgroup.zpowers y))).map (congrHom e) ≤
        L3Nine.norm hK ⊓ centSub (fixV (Subgroup.zpowers (congrHom e y))) := by
      rw [inf_centSub_map_congrHom, ← hzp, fixV_map_congrHom]
      exact inf_le_inf_right _ hMN
    have hC3 : Nat.card ↥(M ⊓ centSub (fixV (Subgroup.zpowers y))) ≤ 3 := by
      rw [← card_map_congrHom e]
      exact (Subgroup.card_le_of_le hmap).trans h3
    have hyle : Subgroup.zpowers y ≤ M ⊓ centSub (fixV (Subgroup.zpowers y)) := by
      rw [Subgroup.zpowers_le]
      exact ⟨hyM, mem_centSub.mpr fun v hv => H.mem_fixV_zpowers_iff.mp hv⟩
    have hy1 : y ≠ 1 := by
      intro h
      rw [h] at hy5
      have htop : fixV (Subgroup.zpowers (1 : MulAut V)) = ⊤ :=
        eq_top_iff.2 fun v _ => H.mem_fixV_zpowers_iff.mpr rfl
      rw [htop] at hy5
      have := hrkV ⊤
      rw [hy5] at this
      have h0 : rkIdx (⊤ : Subgroup V) = 0 := by simp [rkIdx]
      omega
    have hyo3 : 3 ≤ orderOf y := by
      have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
      have h0 : 0 < orderOf y := orderOf_pos y
      obtain ⟨k, hk⟩ := hodd
      omega
    have hcz : Nat.card ↥(Subgroup.zpowers y) = orderOf y := Nat.card_zpowers y
    have hle := Subgroup.card_le_of_le hyle
    rw [hcz] at hle
    refine ⟨(Subgroup.eq_of_le_of_card_ge hyle (by omega)).symm, by omega⟩

end CFSG.Quasithin.H13
