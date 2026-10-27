module

public import CFSG.GroupTheory.BinaryFixedFreeRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {T : Type} [CommGroup T] [Finite T]

theorem s16t_blk_fixV_anti {X Y : Subgroup (MulAut T)} (h : X ≤ Y) : fixV Y ≤ fixV X :=
  fun _ hv x hx => hv x (h hx)

theorem s16t_blk_mem_fixV_map_conj (B : Subgroup (MulAut T)) (x : MulAut T) {v : T} :
    v ∈ fixV (B.map (MulAut.conj x).toMonoidHom) ↔ x⁻¹ v ∈ fixV B := by
  constructor
  · intro hv b hb
    have h1 : MulAut.conj x b ∈ B.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map.2 ⟨b, hb, rfl⟩
    have h3 : x (b (x⁻¹ v)) = x (x⁻¹ v) := by
      simpa [MulAut.conj_apply, MulAut.mul_apply] using hv (MulAut.conj x b) h1
    exact x.injective h3
  · intro hv b' hb'
    obtain ⟨b, hb, hbb'⟩ := Subgroup.mem_map.1 hb'
    rw [← hbb']
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply]
    rw [hv b hb]
    simp

theorem s16t_blk_fixV_map_conj (B : Subgroup (MulAut T)) (x : MulAut T) :
    fixV (B.map (MulAut.conj x).toMonoidHom) = (fixV B).map x.toMonoidHom := by
  apply le_antisymm
  · intro v hv
    refine Subgroup.mem_map.2 ⟨x⁻¹ v, (s16t_blk_mem_fixV_map_conj B x).1 hv, by simp⟩
  · rintro v ⟨u, hu, rfl⟩
    exact (s16t_blk_mem_fixV_map_conj B x).2 (by simpa using hu)

theorem s16t_blk_map_fixV_of_comm {B : Subgroup (MulAut T)} {a : MulAut T}
    (hcomm : ∀ b ∈ B, a * b = b * a) : (fixV B).map a.toMonoidHom = fixV B := by
  apply le_antisymm
  · rintro v ⟨u, hu, rfl⟩ b hb
    simp only [MulEquiv.coe_toMonoidHom]
    have h2 : a (b u) = b (a u) := by
      have := congrArg (fun f : MulAut T => f u) (hcomm b hb)
      simpa [MulAut.mul_apply] using this
    rw [← h2, hu b hb]
  · intro u hu
    refine Subgroup.mem_map.2 ⟨a⁻¹ u, ?_, by simp⟩
    intro b hb
    apply a.injective
    have h2 : a (b (a⁻¹ u)) = b (a (a⁻¹ u)) := by
      have := congrArg (fun f : MulAut T => f (a⁻¹ u)) (hcomm b hb)
      simpa [MulAut.mul_apply] using this
    rw [h2]
    simpa using hu b hb

theorem s16t_blk_mem_fixV_sup_iff {B C : Subgroup (MulAut T)} (v : T) :
    v ∈ fixV (B ⊔ C) ↔ v ∈ fixV B ∧ v ∈ fixV C := by
  constructor
  · intro hv
    exact ⟨fun b hb => hv b (Subgroup.mem_sup_left hb),
      fun c hc => hv c (Subgroup.mem_sup_right hc)⟩
  · intro h x hx
    obtain ⟨hB, hC⟩ := h
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction (p := fun y _ => y v = v) ?_ ?_ ?_ ?_ hx
    · rintro y (hy | hy)
      · exact hB y hy
      · exact hC y hy
    · simp
    · intro a b _ _ ha hb
      rw [MulAut.mul_apply, hb, ha]
    · intro a _ ha
      have h2 : a (a⁻¹ v) = v := by
        rw [← MulAut.mul_apply, mul_inv_cancel]
        simp
      exact a.injective (by rw [h2, ha])

theorem s16t_blk_eq_top_of_lt_card {P : Type*} [Group P] [Finite P]
    {A B C : Subgroup P} {p : ℕ} (hp : p.Prime) (hBA : B ≤ A) (hBC : B ≤ C) (hCA : C ≤ A)
    (hAcard : Nat.card A = p ^ 3) (hBcard : Nat.card B = p ^ 2) (hne : B ≠ C) : C = A := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBC
  have hkdvd : k ∣ p := by
    have h2 : Nat.card C ∣ Nat.card A := Subgroup.card_dvd_of_le hCA
    rw [hk, hAcard, hBcard] at h2
    have h3 : p ^ 2 * k ∣ p ^ 2 * p := by
      rw [show p ^ 2 * p = p ^ 3 from by ring]
      exact h2
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 2) h3
  have hkne : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    exact hne (Subgroup.eq_of_le_of_card_ge hBC (le_of_eq hk))
  have hkp : k = p := ((Nat.dvd_prime hp).1 hkdvd).resolve_left hkne
  refine Subgroup.eq_of_le_of_card_ge hCA ?_
  rw [hAcard, hk, hBcard, hkp]
  exact le_of_eq (by ring)

theorem s16t_blk_card_of_isElemAbelianOfRank {X : Type*} [Group X] {p r : ℕ} [NeZero p]
    (h : IsElemAbelianOfRank p r X) : Nat.card X = p ^ r := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem s16t_blk_comm_of_isElemAbelianOfRank {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

theorem s16t_blk_pow_of_isElemAbelianOfRank {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a : X, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  intro a
  apply e.injective
  rw [map_pow, map_one]
  have h3 : ∀ y : Multiplicative (Fin n → ZMod p), y ^ p = 1 := by
    intro y
    induction y using Multiplicative.rec with
    | ofAdd w =>
      rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p) p w, ZMod.natCast_self p,
        zero_smul, ofAdd_zero]
  exact h3 (e a)

theorem s16t_blk_dvd_rk_fixV (hT : ∀ t : T, t ^ 2 = 1)
    {p : ℕ} [Fact p.Prime] {A B : Subgroup (MulAut T)}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hfixA : fixV A = ⊥) (hBA : B ≤ A)
    (hAcard : Nat.card ↥A = p ^ 3) (hBcard : Nat.card ↥B = p ^ 2) :
    orderOf (2 : ZMod p) ∣ rk ↥(fixV B) := by
  have hp : p.Prime := Fact.out
  have hBAne : B ≠ A := by
    intro hEq
    rw [hEq, hAcard] at hBcard
    have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hnot : ¬ A ≤ B := fun h => hBAne (le_antisymm hBA h)
  obtain ⟨a, haA, haB⟩ := Set.not_subset.1 hnot
  have hzA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.2 haA
  have hCtop : B ⊔ Subgroup.zpowers a = A := by
    refine s16t_blk_eq_top_of_lt_card hp hBA le_sup_left (sup_le hBA hzA) hAcard hBcard ?_
    intro h
    apply haB
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hfixBC : fixV B ⊓ fixV (Subgroup.zpowers a) = ⊥ := by
    refine le_bot_iff.1 ?_
    rintro v ⟨hvB, hva⟩
    have hvs : v ∈ fixV (B ⊔ Subgroup.zpowers a) :=
      (s16t_blk_mem_fixV_sup_iff v).2 ⟨hvB, hva⟩
    rw [hCtop, hfixA] at hvs
    exact hvs
  have hYp : IsPGroup p ↥(Subgroup.zpowers a) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (hAp a haA)
  have hinv : ∀ y ∈ Subgroup.zpowers a, ∀ w ∈ fixV B, y w ∈ fixV B := by
    intro y hy w hw
    have hyA : y ∈ A := hzA hy
    have hmap := s16t_blk_map_fixV_of_comm (B := B) (a := y)
      (fun b hb => hAc y hyA b (hBA hb))
    have : y w ∈ (fixV B).map y.toMonoidHom := Subgroup.mem_map.2 ⟨w, hw, rfl⟩
    rwa [hmap] at this
  exact CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot hT hYp hinv hfixBC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
