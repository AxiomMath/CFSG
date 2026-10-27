module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

section GL32Orders

local notation "Mat3" => Matrix (Fin 3) (Fin 3) (ZMod 2)

private theorem s16e_d3_orders9 : ∀ a b c d e f g h i : ZMod 2,
    (!![a, b, c; d, e, f; g, h, i] : Mat3).det = 1 →
    (!![a, b, c; d, e, f; g, h, i] : Mat3) ^ 4 = 1 ∨
      (!![a, b, c; d, e, f; g, h, i] : Mat3) ^ 3 = 1 ∨
      (!![a, b, c; d, e, f; g, h, i] : Mat3) ^ 7 = 1 := by decide

private theorem s16e_d3_mat_orders (M : Mat3) (h : M.det = 1) :
    M ^ 4 = 1 ∨ M ^ 3 = 1 ∨ M ^ 7 = 1 := by
  have := s16e_d3_orders9 (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2)
    (M 2 0) (M 2 1) (M 2 2)
  rw [← Matrix.eta_fin_three M] at this
  exact this h

private theorem s16e_d3_det_GL32 (g : GL (Fin 3) (ZMod 2)) : (g : Mat3).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
  simpa using h2

private theorem s16e_d3_orders_GL32 (g : GL (Fin 3) (ZMod 2)) :
    g ^ 4 = 1 ∨ g ^ 3 = 1 ∨ g ^ 7 = 1 := by
  rcases s16e_d3_mat_orders (g : Mat3) (s16e_d3_det_GL32 g) with h | h | h
  · exact Or.inl (Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl))
  · exact Or.inr (Or.inl (Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl)))
  · exact Or.inr (Or.inr (Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl)))

end GL32Orders

section Abstract

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem s16e_d3_card_normalizer_seven (hsq : ∀ y : Y, y ^ 2 = 1) (hY : Nat.card Y = 8)
    {Q : Subgroup (MulAut Y)} (hQ : Nat.card Q = 7) :
    Nat.card (normalizer (Q : Set (MulAut Y))) = 21 := by
  have h2Y : ∀ v : Y, v * v = 1 := fun v => by rw [← pow_two]; exact hsq v
  obtain ⟨e⟩ := CFSG.OddStandard.ChengHeld.GL32Inv.mulAut_mulEquiv_GL3 hY h2Y
  have hPcard : Nat.card (Q.map e.toMonoidHom) = 7 := by
    rw [Subgroup.card_map_of_injective (K := Q) (f := e.toMonoidHom) e.injective, hQ]
  have hNcard : Nat.card (normalizer ((Q.map e.toMonoidHom) : Set (GL (Fin 3) (ZMod 2)))) = 21 :=
    CFSG.ComponentClassification.GMS78.card_normalizer_eq_of_card_eq_seven_GL32 hPcard
  have hmap : (normalizer (Q : Set (MulAut Y))).map e.toMonoidHom =
      normalizer ((Q.map e.toMonoidHom) : Set (GL (Fin 3) (ZMod 2))) :=
    Subgroup.map_equiv_normalizer_eq Q e
  have hcard : Nat.card (normalizer (Q : Set (MulAut Y))) =
      Nat.card (normalizer ((Q.map e.toMonoidHom) : Set (GL (Fin 3) (ZMod 2)))) := by
    rw [← Subgroup.card_map_of_injective (K := normalizer (Q : Set (MulAut Y)))
      (f := e.toMonoidHom) e.injective, hmap]
  rw [hcard, hNcard]

theorem s16e_d3_card_dvd_of_le_normalizer (hsq : ∀ y : Y, y ^ 2 = 1) (hY : Nat.card Y = 8)
    {Q N : Subgroup (MulAut Y)} (hQ : Nat.card Q = 7)
    (hN : N ≤ normalizer (Q : Set (MulAut Y))) :
    Nat.card N ∣ 21 := by
  rw [← s16e_d3_card_normalizer_seven hsq hY hQ]
  exact Subgroup.card_dvd_of_le hN

theorem s16e_d3_eq_one_of_commute (hsq : ∀ y : Y, y ^ 2 = 1) (hY : Nat.card Y = 8)
    {x y : MulAut Y} (hxy : Commute x y) (hx : x ^ 3 = 1) (hy : y ^ 7 = 1) (hy1 : y ≠ 1) :
    x = 1 := by
  have h2Y : ∀ v : Y, v * v = 1 := fun v => by rw [← pow_two]; exact hsq v
  obtain ⟨e⟩ := CFSG.OddStandard.ChengHeld.GL32Inv.mulAut_mulEquiv_GL3 hY h2Y
  have hx' : (e x) ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  have hy' : (e y) ^ 7 = 1 := by rw [← map_pow, hy, map_one]
  have hy1' : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
  have hcomm' : Commute (e x) (e y) := hxy.map e.toMonoidHom
  have hx1 : e x = 1 := by
    by_contra hxne
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hox : orderOf (e x) = 3 := orderOf_eq_prime hx' hxne
    have hoy : orderOf (e y) = 7 := orderOf_eq_prime hy' hy1'
    have hco : Nat.Coprime (orderOf (e x)) (orderOf (e y)) := by rw [hox, hoy]; norm_num
    have hz : orderOf (e x * e y) = 21 := by
      rw [hcomm'.orderOf_mul_eq_mul_orderOf_of_coprime hco, hox, hoy]
    rcases s16e_d3_orders_GL32 (e x * e y) with h | h | h
    · have hd : 21 ∣ 4 := by rw [← hz]; exact orderOf_dvd_of_pow_eq_one h
      exact absurd hd (by norm_num)
    · have hd : 21 ∣ 3 := by rw [← hz]; exact orderOf_dvd_of_pow_eq_one h
      exact absurd hd (by norm_num)
    · have hd : 21 ∣ 7 := by rw [← hz]; exact orderOf_dvd_of_pow_eq_one h
      exact absurd hd (by norm_num)
  exact e.injective (by rw [hx1, map_one])

end Abstract

section Blocks

variable {W : Type} [CommGroup W] [Finite W]

private lemma s16e_d3_conj_mem_of_map_conj_eq {L : Subgroup (MulAut W)} {n : MulAut W}
    (h : L.map (MulAut.conj n).toMonoidHom = L) {l : MulAut W} (hl : l ∈ L) :
    n * l * n⁻¹ ∈ L := by
  have hm : (MulAut.conj n).toMonoidHom l ∈ L.map (MulAut.conj n).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hl
  rw [h] at hm
  simpa [MulAut.conj_apply] using hm

theorem s16e_d3_eq_of_commute_on_block (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup W}
    (hY : Nat.card Y = 8) {g l : MulAut W} (hg : g ∈ stabSub Y) (hl : l ∈ stabSub Y)
    (hgl : g * l = l * g) (hg3 : g ^ 3 = 1) (hl7 : l ^ 7 = 1) (hln : ∃ y ∈ Y, l y ≠ y) :
    ∀ y ∈ Y, g y = y := by
  have h2Y : ∀ v : ↥Y, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW (v : W))
  let gb : MulAut ↥Y := resHom Y ⟨g, hg⟩
  let lb : MulAut ↥Y := resHom Y ⟨l, hl⟩
  have hgl' : (⟨g, hg⟩ : stabSub Y) * ⟨l, hl⟩ = ⟨l, hl⟩ * ⟨g, hg⟩ := Subtype.ext hgl
  have hcomm : Commute gb lb := by
    show gb * lb = lb * gb
    rw [show gb = resHom Y ⟨g, hg⟩ from rfl, show lb = resHom Y ⟨l, hl⟩ from rfl,
      ← map_mul, ← map_mul, hgl']
  have hg3' : gb ^ 3 = 1 := by
    have h : (⟨g, hg⟩ : stabSub Y) ^ 3 = 1 := Subtype.ext hg3
    rw [show gb = resHom Y ⟨g, hg⟩ from rfl, ← map_pow, h, map_one]
  have hl7' : lb ^ 7 = 1 := by
    have h : (⟨l, hl⟩ : stabSub Y) ^ 7 = 1 := Subtype.ext hl7
    rw [show lb = resHom Y ⟨l, hl⟩ from rfl, ← map_pow, h, map_one]
  have hlb1 : lb ≠ 1 := by
    intro h1
    have h1' : resHom Y ⟨l, hl⟩ = 1 := h1
    obtain ⟨y, hyY, hly⟩ := hln
    have h2 := congrArg (fun (φ : MulAut ↥Y) => ((φ ⟨y, hyY⟩ : ↥Y) : W)) h1'
    simp only [MulAut.one_apply] at h2
    rw [resHom_apply] at h2
    exact hly (by simpa using h2)
  have hgb1 : gb = 1 :=
    s16e_d3_eq_one_of_commute (Y := ↥Y) h2Y hY hcomm hg3' hl7' hlb1
  intro y hy
  have hgb1' : resHom Y ⟨g, hg⟩ = 1 := hgb1
  have h2 := congrArg (fun (φ : MulAut ↥Y) => ((φ ⟨y, hy⟩ : ↥Y) : W)) hgb1'
  simp only [MulAut.one_apply] at h2
  rw [resHom_apply] at h2
  simpa using h2

theorem s16e_d3_card_autSub_dvd (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup W}
    (hY : Nat.card Y = 8) {N L : Subgroup (MulAut W)} (hN : N ≤ stabSub Y) (hL : L ≤ stabSub Y)
    (hNL : ∀ n ∈ N, L.map (MulAut.conj n).toMonoidHom = L) (hL7 : Nat.card (autSub L Y) = 7) :
    Nat.card (autSub N Y) ∣ 21 := by
  have h2Y : ∀ v : ↥Y, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hW (v : W))
  have hle : autSub N Y ≤ normalizer (autSub L Y : Set (MulAut ↥Y)) := by
    intro φ hφ
    obtain ⟨n, hnN, rfl⟩ := mem_autSub.mp hφ
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      obtain ⟨l, hlL, rfl⟩ := mem_autSub.mp hq
      rw [show resHom Y n * resHom Y l * (resHom Y n)⁻¹ = resHom Y (n * l * n⁻¹) from by
        rw [← map_inv, ← map_mul, ← map_mul]]
      refine mem_autSub.mpr ⟨n * l * n⁻¹, ?_, rfl⟩
      have hmem := s16e_d3_conj_mem_of_map_conj_eq (hNL (n : MulAut W) hnN) hlL
      simpa using hmem
    · intro hq
      obtain ⟨l', hl'L, hl'eq⟩ := mem_autSub.mp hq
      have hq_eq : q = resHom Y (n⁻¹ * l' * n) := by
        have h1 : q = (resHom Y n)⁻¹ * resHom Y l' * resHom Y n := by
          rw [hl'eq]; group
        rw [h1, ← map_inv, ← map_mul, ← map_mul]
      rw [hq_eq]
      refine mem_autSub.mpr ⟨n⁻¹ * l' * n, ?_, rfl⟩
      have hninv : ((n⁻¹ : ↥(stabSub Y)) : MulAut W) ∈ N := by
        simpa using N.inv_mem hnN
      have hmem := s16e_d3_conj_mem_of_map_conj_eq (hNL _ hninv) hl'L
      simpa using hmem
  exact s16e_d3_card_dvd_of_le_normalizer (Y := ↥Y) h2Y hY hL7 hle

end Blocks

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
