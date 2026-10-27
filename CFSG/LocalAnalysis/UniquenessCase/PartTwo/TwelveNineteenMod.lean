module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveNineteenPieces
public import CFSG.Quasithin.Background.E3Defs
import CFSG.Quasithin.Background.FixVLattice
import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

namespace TwelveNineteen

variable {W : Type} [CommGroup W] [Finite W]

private theorem card_mul_ncard_le {p : ℕ} {A S : Subgroup (MulAut W)}
    (hSA : S ≤ normalizer (A : Set (MulAut W)))
    (hSf : ∀ s ∈ S, s ≠ 1 → ∀ x ∈ A, s * x = x * s → x = 1) {x : MulAut W} (hx : x ∈ A)
    (hx1 : x ≠ 1) :
    p * (Nat.card S * (deltaSet p A).ncard) ≤ (deltaSet p A).ncard * Nat.card A +
      p * (Nat.card S * {H | H ∈ deltaSet p A ∧ x ∉ H}.ncard) := by
  classical
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  haveI : Fintype (MulAut W) := Fintype.ofFinite _
  haveI : Fintype (Subgroup (MulAut W)) := Fintype.ofFinite _
  haveI : Fintype S := Fintype.ofFinite S
  set D : Finset (Subgroup (MulAut W)) := Finset.univ.filter (· ∈ deltaSet p A) with hD
  set Cx : Finset (Subgroup (MulAut W)) := D.filter (fun H => x ∉ H) with hCx
  have hDn : (deltaSet p A).ncard = D.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext H
    simp [hD]
  have hCn : {H | H ∈ deltaSet p A ∧ x ∉ H}.ncard = Cx.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext H
    simp [hCx, hD]
  have hinj : Function.Injective (fun s : S => (s : MulAut W) * x * (s : MulAut W)⁻¹) := by
    intro s s' h
    have h' : (s : MulAut W) * x * (s : MulAut W)⁻¹ = s' * x * (s' : MulAut W)⁻¹ := h
    by_contra hne
    have hu : (s' : MulAut W)⁻¹ * s ≠ 1 := fun h1 =>
      hne (Subtype.ext (inv_mul_eq_one.1 h1).symm)
    have hcomm : ((s' : MulAut W)⁻¹ * s) * x = x * ((s' : MulAut W)⁻¹ * s) := by
      calc ((s' : MulAut W)⁻¹ * s) * x
          = (s' : MulAut W)⁻¹ * ((s : MulAut W) * x * (s : MulAut W)⁻¹) * s := by group
        _ = (s' : MulAut W)⁻¹ * (s' * x * (s' : MulAut W)⁻¹) * s := by rw [h']
        _ = x * ((s' : MulAut W)⁻¹ * s) := by group
    exact hx1 (hSf _ (S.mul_mem (S.inv_mem s'.2) s.2) hu x hx hcomm)
  set O : Finset (MulAut W) :=
    (Finset.univ : Finset S).image (fun s : S => (s : MulAut W) * x * (s : MulAut W)⁻¹) with hO
  have hOc : O.card = Nat.card S := by
    rw [hO, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_eq_nat_card]
  have hcol : ∀ H ∈ D, p * (O.filter (· ∈ H)).card ≤ Nat.card A := by
    intro H hH
    obtain ⟨hHA, hHp, -⟩ := (Finset.mem_filter.1 hH).2
    have e := relIndex_mul_card H A
    rw [hHp, inf_eq_left.2 hHA] at e
    rw [← e]
    apply Nat.mul_le_mul_left
    calc (O.filter (· ∈ H)).card ≤ (Finset.univ.filter (· ∈ H)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ O))
      _ = Nat.card H := by rw [← Fintype.card_subtype, Fintype.card_eq_nat_card]
  have hrow : ∀ y ∈ O, D.card ≤ (D.filter (fun H => y ∈ H)).card + Cx.card := by
    intro y hy
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hy
    rw [← Finset.card_filter_add_card_filter_not (s := D)
      (fun H => (s : MulAut W) * x * (s : MulAut W)⁻¹ ∈ H)]
    apply Nat.add_le_add_left
    have hsN : (s : MulAut W)⁻¹ ∈ normalizer (A : Set (MulAut W)) :=
      (normalizer (A : Set (MulAut W))).inv_mem (hSA s.2)
    refine Finset.card_le_card_of_injOn
      (fun H => H.map (MulAut.conj (s : MulAut W)⁻¹).toMonoidHom) ?_ ?_
    · intro H hH
      have hH' := Finset.mem_filter.1 hH
      have hHΔ : H ∈ deltaSet p A := (Finset.mem_filter.1 hH'.1).2
      refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _,
        map_conj_mem_deltaSet hsN hHΔ⟩, ?_⟩
      rintro ⟨h, hh, hhx⟩
      apply hH'.2
      have e : h = (s : MulAut W) * x * (s : MulAut W)⁻¹ := by
        have hhx' : (s : MulAut W)⁻¹ * h * (s : MulAut W)⁻¹⁻¹ = x := hhx
        rw [← hhx']
        group
      exact e ▸ hh
    · intro H _ H' _ hHH'
      exact Subgroup.map_injective (MulAut.conj (s : MulAut W)⁻¹).injective hHH'
  have hdc : ∑ y ∈ O, (D.filter (fun H => y ∈ H)).card =
      ∑ H ∈ D, (O.filter (· ∈ H)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun y H => y ∈ H)
  have hrows : O.card * D.card ≤ ∑ y ∈ O, (D.filter (fun H => y ∈ H)).card + O.card * Cx.card := by
    calc O.card * D.card = ∑ _y ∈ O, D.card := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ y ∈ O, ((D.filter (fun H => y ∈ H)).card + Cx.card) := Finset.sum_le_sum hrow
      _ = ∑ y ∈ O, (D.filter (fun H => y ∈ H)).card + O.card * Cx.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  have hcols : p * ∑ H ∈ D, (O.filter (· ∈ H)).card ≤ D.card * Nat.card A := by
    rw [Finset.mul_sum]
    calc ∑ H ∈ D, p * (O.filter (· ∈ H)).card ≤ ∑ _H ∈ D, Nat.card A := Finset.sum_le_sum hcol
      _ = D.card * Nat.card A := by rw [Finset.sum_const, smul_eq_mul]
  rw [hDn, hCn, ← hOc]
  rw [hdc] at hrows
  have hp' := Nat.mul_le_mul_left p hrows
  rw [mul_add] at hp'
  linarith

theorem three_le_ncard_deltaSet (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A S : Subgroup (MulAut W)} (hA : IsElemAbelian p A) (hAc : p ^ 2 ≤ Nat.card A)
    (hSA : S ≤ normalizer (A : Set (MulAut W)))
    (hSf : ∀ s ∈ S, s ≠ 1 → ∀ x ∈ A, s * x = x * s → x = 1)
    (hSc : Nat.card A ≤ 2 * Nat.card S + 1) :
    3 ≤ (deltaSet p A).ncard := by
  classical
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  have hp2 : p ≠ 2 := by omega
  by_contra hlt
  have hN2 : (deltaSet p A).ncard ≤ 2 := by omega
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAc
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨H₁, hH₁⟩ := deltaSet_nonempty hW hp hp2 hA hA1
  obtain ⟨hH₁A, hH₁p, -⟩ := id hH₁
  have e := relIndex_mul_card H₁ A
  rw [hH₁p, inf_eq_left.2 hH₁A] at e
  have hH₁c : p ≤ Nat.card H₁ := by
    have h1 : p * p ≤ p * Nat.card H₁ := by rw [e, ← sq]; exact hAc
    exact Nat.le_of_mul_le_mul_left h1 hp.pos
  obtain ⟨x, hxH₁, hx1⟩ : ∃ x ∈ H₁, x ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one H₁ with h | h
    · rw [h, Subgroup.card_bot] at hH₁c
      omega
    · exact h
  have hxA : x ∈ A := hH₁A hxH₁
  have hdc := card_mul_ncard_le (p := p) hSA hSf hxA hx1
  have hc : {H | H ∈ deltaSet p A ∧ x ∉ H}.ncard + 1 ≤ (deltaSet p A).ncard := by
    have hsub : {H | H ∈ deltaSet p A ∧ x ∉ H} ⊂ deltaSet p A := by
      refine ⟨fun H hH => hH.1, fun h => ?_⟩
      have h1 := h hH₁
      exact h1.2 hxH₁
    exact Set.ncard_lt_ncard hsub (Set.toFinite _)
  set N := (deltaSet p A).ncard
  set c := {H | H ∈ deltaSet p A ∧ x ∉ H}.ncard
  set s := Nat.card S
  set q := Nat.card A
  have h1 : p * s ≤ N * q := by
    have h2 : p * (s * (c + 1)) ≤ p * (s * N) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc)
    have h3 : p * (s * c) + p * s ≤ N * q + p * (s * c) := by
      calc p * (s * c) + p * s = p * (s * (c + 1)) := by ring
        _ ≤ p * (s * N) := h2
        _ ≤ N * q + p * (s * c) := hdc
    omega
  have h3 : N * q ≤ 2 * q := Nat.mul_le_mul_right _ hN2
  have h4 : p * q ≤ p * (2 * s + 1) := Nat.mul_le_mul_left _ hSc
  have h5 : 5 * q ≤ p * q := Nat.mul_le_mul_right _ hp5
  have h6 : p * p ≤ q := by rw [← sq]; exact hAc
  have h7 : 5 * p ≤ p * p := Nat.mul_le_mul_right _ hp5
  nlinarith

private theorem arith_two {p s N q : ℕ} (hp5 : 5 ≤ p) (hN : 3 ≤ N) (hq : p * p ≤ q)
    (hSc : q ≤ 2 * s + 1) (ha : p * (s * N) ≤ N * q + p * s) : False := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  nlinarith [Nat.mul_le_mul_right (p * (M + 2)) hSc, Nat.mul_le_mul_right (q * M) hp5,
    Nat.mul_le_mul_right q hp5, Nat.mul_le_mul_right M hq, Nat.mul_le_mul_right (p * M) hp5,
    Nat.mul_le_mul_right p hp5, Nat.zero_le (p * M)]

private theorem arith_seven {s N q : ℕ} (hN : 3 ≤ N) (hq : 49 ≤ q) (hSc : q ≤ 2 * s + 1)
    (ha : 7 * (s * N) ≤ N * q + 7 * (s * 2)) : False := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 3 := ⟨N - 3, by omega⟩
  nlinarith [Nat.mul_le_mul_right (M + 1) hSc, Nat.mul_le_mul_right M hq]

theorem two_le_ncard_not_mem (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A S : Subgroup (MulAut W)} (hA : IsElemAbelian p A) (hAc : p ^ 2 ≤ Nat.card A)
    (hSA : S ≤ normalizer (A : Set (MulAut W)))
    (hSf : ∀ s ∈ S, s ≠ 1 → ∀ x ∈ A, s * x = x * s → x = 1)
    (hSc : Nat.card A ≤ 2 * Nat.card S + 1) {x : MulAut W} (hx : x ∈ A) (hx1 : x ≠ 1) :
    2 ≤ {H | H ∈ deltaSet p A ∧ x ∉ H}.ncard ∧
      (p = 7 → 3 ≤ {H | H ∈ deltaSet p A ∧ x ∉ H}.ncard) := by
  have hN := three_le_ncard_deltaSet hW hp hp5 hA hAc hSA hSf hSc
  have hdc := card_mul_ncard_le (p := p) hSA hSf hx hx1
  set N := (deltaSet p A).ncard
  set c := {H | H ∈ deltaSet p A ∧ x ∉ H}.ncard
  set s := Nat.card S
  set q := Nat.card A
  have h6 : p * p ≤ q := by rw [← sq]; exact hAc
  refine ⟨?_, fun h7 => ?_⟩
  · by_contra hlt
    have hc1 : c ≤ 1 := by omega
    have ha : p * (s * N) ≤ N * q + p * s := by
      have : p * (s * c) ≤ p * s := by
        calc p * (s * c) ≤ p * (s * 1) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc1)
          _ = p * s := by ring
      omega
    exact arith_two hp5 hN h6 hSc ha
  · by_contra hlt
    have hc2 : c ≤ 2 := by omega
    rw [h7] at hdc h6
    have ha : 7 * (s * N) ≤ N * q + 7 * (s * 2) := by
      have : 7 * (s * c) ≤ 7 * (s * 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc2)
      omega
    exact arith_seven hN (by omega) hSc ha

theorem two_pow_eight_le_index (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A S : Subgroup (MulAut W)} (hA : IsElemAbelian p A) (hAc : p ^ 2 ≤ Nat.card A)
    (hSA : S ≤ normalizer (A : Set (MulAut W)))
    (hSf : ∀ s ∈ S, s ≠ 1 → ∀ x ∈ A, s * x = x * s → x = 1)
    (hSc : Nat.card A ≤ 2 * Nat.card S + 1) {x : MulAut W} (hx : x ∈ A) (hx1 : x ≠ 1) :
    2 ^ 8 ≤ (fixV (zpowers x)).index := by
  classical
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  haveI : Fintype (Subgroup (MulAut W)) := Fintype.ofFinite _
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hc2, hc7⟩ := two_le_ncard_not_mem hW hp hp5 hA hAc hSA hSf hSc hx hx1
  set F : Finset (Subgroup (MulAut W)) :=
    Finset.univ.filter (fun H => H ∈ deltaSet p A ∧ x ∉ H) with hF
  have hFn : {H | H ∈ deltaSet p A ∧ x ∉ H}.ncard = F.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext H
    simp [hF]
  have hFm : ∀ H ∈ F, H ∈ deltaSet p A ∧ x ∉ H := fun H hH => (Finset.mem_filter.1 hH).2
  have hprod := prod_card_kSub_le_index hW hp hp2 hA hx F fun H hH =>
    ⟨(hFm H hH).1.1, (hFm H hH).1.2.1, (hFm H hH).2⟩
  refine le_trans ?_ hprod
  by_cases h7 : p = 7
  · have hge : ∀ H ∈ F, 8 ≤ Nat.card (kSub A H) := fun H hH =>
      (card_kSub_ge hW hp hp5 hA (hFm H hH).1).1
    have h3 : 3 ≤ F.card := by rw [← hFn]; exact hc7 h7
    calc 2 ^ 8 ≤ 8 ^ 3 := by norm_num
      _ ≤ 8 ^ F.card := Nat.pow_le_pow_right (by norm_num) h3
      _ ≤ ∏ H ∈ F, Nat.card (kSub A H) := Finset.pow_card_le_prod F _ 8 hge
  · have hge : ∀ H ∈ F, 16 ≤ Nat.card (kSub A H) := fun H hH =>
      (card_kSub_ge hW hp hp5 hA (hFm H hH).1).2 h7
    have h2 : 2 ≤ F.card := by rw [← hFn]; exact hc2
    calc 2 ^ 8 = 16 ^ 2 := by norm_num
      _ ≤ 16 ^ F.card := Nat.pow_le_pow_right (by norm_num) h2
      _ ≤ ∏ H ∈ F, Nat.card (kSub A H) := Finset.pow_card_le_prod F _ 16 hge

private theorem index_fixV_mul_le (g h : MulAut W) :
    (fixV (zpowers (g * h))).index ≤ (fixV (zpowers g)).index * (fixV (zpowers h)).index := by
  refine (Subgroup.index_antitone fun v hv => ?_).trans Subgroup.index_inf_le
  rw [Subgroup.mem_inf, CFSG.Quasithin.mem_fixV_zpowers_iff_apply,
    CFSG.Quasithin.mem_fixV_zpowers_iff_apply] at hv
  rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply, MulAut.mul_apply, hv.2, hv.1]

theorem sixteen_le_index (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A S : Subgroup (MulAut W)} (hA : IsElemAbelian p A) (hAc : p ^ 2 ≤ Nat.card A)
    (hSA : S ≤ normalizer (A : Set (MulAut W)))
    (hSf : ∀ s ∈ S, s ≠ 1 → ∀ x ∈ A, s * x = x * s → x = 1)
    (hSc : Nat.card A ≤ 2 * Nat.card S + 1) {t : MulAut W}
    (ht : t ∈ normalizer (A : Set (MulAut W))) (ht2 : t ^ 2 = 1) {b : MulAut W} (hb : b ∈ A)
    (htb : t * b * t⁻¹ ≠ b) :
    16 ≤ (fixV (zpowers t)).index := by
  have hp2 : p ≠ 2 := by omega
  have hcA : t * b * t⁻¹ ∈ A := (mem_normalizer_iff.1 ht b).1 hb
  set a := b⁻¹ * (t * b * t⁻¹) with ha
  have haA : a ∈ A := A.mul_mem (A.inv_mem hb) hcA
  have ha1 : a ≠ 1 := fun h => htb (inv_mul_eq_one.1 h).symm
  have ht1 : t * t = 1 := by rw [← sq]; exact ht2
  have htc : t * (t * b * t⁻¹) * t⁻¹ = b := by
    calc t * (t * b * t⁻¹) * t⁻¹ = (t * t) * b * (t * t)⁻¹ := by group
      _ = b := by rw [ht1, one_mul, inv_one, mul_one]
  have hta : t * a * t⁻¹ = a⁻¹ := by
    calc t * a * t⁻¹ = (t * b * t⁻¹)⁻¹ * (t * (t * b * t⁻¹) * t⁻¹) := by rw [ha]; group
      _ = (t * b * t⁻¹)⁻¹ * b := by rw [htc]
      _ = a⁻¹ := by rw [ha]; group
  have h8 := two_pow_eight_le_index hW hp hp5 hA hAc hSA hSf hSc haA ha1
  have hsq : (fixV (zpowers a)).index ≤ (fixV (zpowers t)).index ^ 2 := by
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    set y : MulAut W := a ^ (m + 1) with hy
    have hty : t * y * t⁻¹ = y⁻¹ := by
      rw [hy, ← conj_pow, hta, inv_pow]
    have h1 : t * y⁻¹ * t⁻¹ = y := by
      rw [show t * y⁻¹ * t⁻¹ = (t * y * t⁻¹)⁻¹ by group, hty, inv_inv]
    have hyy : y * y = a := by
      rw [hy, ← pow_add, show m + 1 + (m + 1) = p + 1 by omega, pow_succ, hA.2 a haA, one_mul]
    have hyt : y * t * y⁻¹ = a * t := by
      calc y * t * y⁻¹ = y * (t * y⁻¹ * t⁻¹) * t := by group
        _ = y * y * t := by rw [h1]
        _ = a * t := by rw [hyy]
    have hst : (a * t) * t = a := by rw [mul_assoc, ht1, mul_one]
    calc (fixV (zpowers a)).index = (fixV (zpowers ((a * t) * t))).index := by rw [hst]
      _ ≤ (fixV (zpowers (a * t))).index * (fixV (zpowers t)).index := index_fixV_mul_le _ _
      _ = (fixV (zpowers t)).index * (fixV (zpowers t)).index := by
          rw [← hyt, CFSG.Quasithin.FixVLat.index_fixV_zpowers_conj]
      _ = (fixV (zpowers t)).index ^ 2 := (sq _).symm
  by_contra hlt
  have hle : (fixV (zpowers t)).index ≤ 15 := by omega
  have h15 : (fixV (zpowers t)).index ^ 2 ≤ 15 ^ 2 := Nat.pow_le_pow_left hle 2
  have : 2 ^ 8 ≤ 15 ^ 2 := le_trans h8 (le_trans hsq h15)
  norm_num at this

theorem three_lt_mParam (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A S X : Subgroup (MulAut W)} (hA : IsElemAbelian p A) (hAc : p ^ 2 ≤ Nat.card A)
    (hSA : S ≤ normalizer (A : Set (MulAut W)))
    (hSf : ∀ s ∈ S, s ≠ 1 → ∀ x ∈ A, s * x = x * s → x = 1)
    (hSc : Nat.card A ≤ 2 * Nat.card S + 1) (hAX : A ≤ X)
    (hXA : X ≤ normalizer (A : Set (MulAut W)))
    (hinv : ∀ t ∈ X, orderOf t = 2 → ∃ b ∈ A, t * b * t⁻¹ ≠ b) :
    3 < E3.mParam X := by
  classical
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2W : IsPGroup 2 W := fun g => ⟨1, by rw [pow_one, sq]; exact hW g⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 h2W
  have hidx : ∀ H : Subgroup W, ∃ k, H.index = 2 ^ k := by
    intro H
    have hdvd : H.index ∣ 2 ^ m := hm ▸ H.index_dvd_card
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k, hk⟩
  unfold E3.mParam
  split_ifs with heven
  · have hne : {n : ℕ | ∃ t ∈ X, orderOf t = 2 ∧ n = rkIdx (fixV (zpowers t))}.Nonempty := by
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (even_iff_two_dvd.1 heven)
      exact ⟨_, t, t.2, by rw [Subgroup.orderOf_coe]; exact ht, rfl⟩
    obtain ⟨t, htX, ht2, hn⟩ := Nat.sInf_mem hne
    rw [hn]
    have ht2' : t ^ 2 = 1 := ht2 ▸ pow_orderOf_eq_one t
    obtain ⟨b, hb, htb⟩ := hinv t htX ht2
    have h16 := sixteen_le_index hW hp hp5 hA hAc hSA hSf hSc (hXA htX) ht2' hb htb
    obtain ⟨k, hk⟩ := hidx (fixV (zpowers t))
    unfold rkIdx
    rw [hk, padicValNat.prime_pow]
    rw [hk] at h16
    by_contra hle
    have hk3 : k ≤ 3 := by omega
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    omega
  · obtain ⟨x, hxA, hx1⟩ : ∃ x ∈ A, x ≠ 1 := by
      rcases Subgroup.bot_or_exists_ne_one A with h | h
      · rw [h, Subgroup.card_bot] at hAc
        have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
        omega
      · exact h
    have h8 := two_pow_eight_le_index hW hp hp5 hA hAc hSA hSf hSc hxA hx1
    have hle : (fixV (zpowers x)).index ≤ 2 ^ m := by
      rw [← hm]
      exact Nat.le_of_dvd Nat.card_pos (fixV (zpowers x)).index_dvd_card
    have h8m : 8 ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 (le_trans h8 hle)
    unfold rk
    rw [hm, padicValNat.prime_pow]
    omega

end TwelveNineteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
