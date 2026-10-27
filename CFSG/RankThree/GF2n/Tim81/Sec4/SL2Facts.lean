module

public import CFSG.CGT.Timmesfeld75.L2Orbit
public import CFSG.LinearAlgebra.SL2CoprimeOrder
public import CFSG.GroupTheory.WeirSylow.FieldTorus

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec4

open scoped MatrixGroups
open CFSG.CGT.Timmesfeld75

section Field

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem odd_index_conjSubgroup_utri (a : SL(2, F)) :
    Odd (conjSubgroup a (utri F)).index := by
  have h : (conjSubgroup a (utri F)).index = (utri F).index :=
    Subgroup.index_map_equiv (H := utri F) (MulAut.conj a)
  rw [h]
  exact CFSG.CGT.Timmesfeld75.odd_index_utri

theorem exists_mul_conjSubgroup_conj_utri_eq_of_ne {a b c : SL(2, F)}
    (ha : conjSubgroup a (conjSubgroup c (utri F)) ≠ conjSubgroup c (utri F))
    (hb : conjSubgroup b (conjSubgroup c (utri F)) ≠ conjSubgroup c (utri F)) :
    ∃ s ∈ conjSubgroup c (utri F),
      conjSubgroup b (conjSubgroup c (utri F)) =
        conjSubgroup (s * a) (conjSubgroup c (utri F)) := by
  have hca : conjSubgroup (c⁻¹ * a * c) (utri F) ≠ utri F := by
    intro h
    apply ha
    calc conjSubgroup a (conjSubgroup c (utri F)) = conjSubgroup (a * c) (utri F) := by
          rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup (c * (c⁻¹ * a * c)) (utri F) := by congr 1; group
      _ = conjSubgroup c (conjSubgroup (c⁻¹ * a * c) (utri F)) := by
          rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup c (utri F) := by rw [h]
  have hcb : conjSubgroup (c⁻¹ * b * c) (utri F) ≠ utri F := by
    intro h
    apply hb
    calc conjSubgroup b (conjSubgroup c (utri F)) = conjSubgroup (b * c) (utri F) := by
          rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup (c * (c⁻¹ * b * c)) (utri F) := by congr 1; group
      _ = conjSubgroup c (conjSubgroup (c⁻¹ * b * c) (utri F)) := by
          rw [conjSubgroup_conjSubgroup]
      _ = conjSubgroup c (utri F) := by rw [h]
  have hna : c⁻¹ * a * c ∉ borel F := fun h =>
    hca (mem_normalizer_iff_conjSubgroup_eq.1 (by rwa [normalizer_utri]))
  have hnb : c⁻¹ * b * c ∉ borel F := fun h =>
    hcb (mem_normalizer_iff_conjSubgroup_eq.1 (by rwa [normalizer_utri]))
  obtain ⟨s₀, hs₀, hconj⟩ := exists_mem_utri_conj_eq hna hnb
  rw [conjSubgroup_conjSubgroup] at hconj
  refine ⟨c * s₀ * c⁻¹, conj_mem_conjSubgroup c hs₀, ?_⟩
  calc conjSubgroup b (conjSubgroup c (utri F)) = conjSubgroup (b * c) (utri F) := by
        rw [conjSubgroup_conjSubgroup]
    _ = conjSubgroup (c * (c⁻¹ * b * c)) (utri F) := by congr 1; group
    _ = conjSubgroup c (conjSubgroup (c⁻¹ * b * c) (utri F)) := by
        rw [conjSubgroup_conjSubgroup]
    _ = conjSubgroup c (conjSubgroup (s₀ * (c⁻¹ * a * c)) (utri F)) := by rw [hconj]
    _ = conjSubgroup (c * (s₀ * (c⁻¹ * a * c))) (utri F) := by
        rw [conjSubgroup_conjSubgroup]
    _ = conjSubgroup ((c * s₀ * c⁻¹ * a) * c) (utri F) := by congr 1; group
    _ = conjSubgroup (c * s₀ * c⁻¹ * a) (conjSubgroup c (utri F)) := by
        rw [conjSubgroup_conjSubgroup]

end Field

section Singer

variable {F : Type} [Field F] [Fintype F]

private theorem exists_singer_trace (p : ℕ) [Fact p.Prime] [CharP F p]
    (h2 : (2 : F) = 0) :
    ∃ τ : F, τ ≠ 0 ∧ ∃ ζ : (FiniteField.Extension F p 2)ˣ,
      orderOf ζ = Nat.card F + 1 ∧
      algebraMap F (FiniteField.Extension F p 2) τ =
        (ζ : FiniteField.Extension F p 2) + (ζ : FiniteField.Extension F p 2)⁻¹ := by
  classical
  let E := FiniteField.Extension F p 2
  haveI : Fintype E := Fintype.ofFinite E
  have hEcard : Nat.card E = Nat.card F ^ 2 := FiniteField.natCard_extension F p 2
  have hdvd : Nat.card F + 1 ∣ Nat.card E - 1 := by
    rw [hEcard]
    rw [show Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) by
      simpa [mul_comm] using (Nat.pow_two_sub_pow_two (Nat.card F) 1)]
    exact dvd_mul_of_dvd_right (dvd_refl _) _
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (L := E) hdvd
  let τ : F := Algebra.trace F E (ζ : E)
  have htrace := FiniteField.algebraMap_trace_eq_sum_pow F E (ζ : E)
  rw [FiniteField.finrank_extension F p 2] at htrace
  have htrace' : algebraMap F E τ = (ζ : E) ^ 1 + (ζ : E) ^ Nat.card F := by
    simpa [τ, Finset.sum_range_succ, pow_one] using htrace
  have hpow : (ζ : E) ^ (Nat.card F + 1) = 1 := by
    simpa [hζ] using congrArg Units.val (pow_orderOf_eq_one ζ)
  have hζq : (ζ : E) ^ Nat.card F = (ζ : E)⁻¹ := by
    have hpow' : (ζ : E) ^ Nat.card F * (ζ : E) = 1 := by
      simpa [pow_succ] using hpow
    exact eq_inv_of_mul_eq_one_left hpow'
  have hζq' : (ζ : E) ^ Fintype.card F = (ζ : E)⁻¹ := by
    simpa [Nat.card_eq_fintype_card] using hζq
  have hτ : algebraMap F E τ = (ζ : E) + (ζ : E)⁻¹ := by
    simpa [hζq'] using htrace'
  have hτ0 : τ ≠ 0 := by
    intro h0
    have hsum : (ζ : E) + (ζ : E)⁻¹ = 0 := by
      rw [← hτ, h0, map_zero]
    have hsq : (ζ : E) ^ 2 = 1 := by
      have h : ((ζ : E) + (ζ : E)⁻¹) * (ζ : E) = 0 := by rw [hsum, zero_mul]
      have h' : (ζ : E) ^ 2 + 1 = 0 := by
        calc (ζ : E) ^ 2 + 1 = ((ζ : E) + (ζ : E)⁻¹) * (ζ : E) := by
              rw [add_mul, inv_mul_cancel₀ (Units.ne_zero ζ), pow_two]
          _ = 0 := h
      have hneg : (-1 : E) = 1 := by
        haveI : CharP F 2 := by
          have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h2
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
          · exact absurd h (Fact.out : p.Prime).ne_one
          · rw [← h]; infer_instance
        haveI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
        exact CharTwo.neg_eq 1
      linear_combination h' + hneg
    have hsqU : ζ ^ 2 = 1 := Units.ext hsq
    have hdvd2 : Nat.card F + 1 ∣ 2 := by
      rw [← hζ]
      exact orderOf_dvd_iff_pow_eq_one.mpr hsqU
    have hle : Nat.card F + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
    omega
  exact ⟨τ, hτ0, ζ, hζ, hτ⟩

private theorem pow_lower_left_aux_rec
    (p : ℕ) [Fact p.Prime] [CharP F p] (h2 : (2 : F) = 0)
    {τ s t : F} (ht : t ≠ 0) (hst : s * t = τ) :
    let Z : Matrix (Fin 2) (Fin 2) F := (utriElt s * ltriElt t : SL(2, F))
    let a : ℕ → F := fun k => (Z ^ k) 1 0 / t
    a 0 = 0 ∧ a 1 = 1 ∧ ∀ k : ℕ, a (k + 2) = τ * a (k + 1) + a k := by
  classical
  let Z : Matrix (Fin 2) (Fin 2) F := (utriElt s * ltriElt t : SL(2, F))
  let a : ℕ → F := fun k => (Z ^ k) 1 0 / t
  change a 0 = 0 ∧ a 1 = 1 ∧ ∀ k : ℕ, a (k + 2) = τ * a (k + 1) + a k
  have hZ00 : Z 0 0 = 1 + τ := by
    dsimp only [Z]
    sl2_simp
    rw [hst]
    ring
  have hZ10 : Z 1 0 = t := by
    dsimp only [Z]
    sl2_simp
    ring
  have hZ11 : Z 1 1 = 1 := by
    dsimp only [Z]
    sl2_simp
    ring
  have htrace : Z.trace = τ := by
    rw [Matrix.trace_fin_two, hZ00, hZ11]
    linear_combination h2
  have hdet : Z.det = 1 := (utriElt s * ltriElt t).2
  have hneg : (-(1 : Matrix (Fin 2) (Fin 2) F)) = 1 := by
    haveI : CharP F 2 := by
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h (Fact.out : p.Prime).ne_one
      · rw [← h]; infer_instance
    exact CharTwo.neg_eq (1 : Matrix (Fin 2) (Fin 2) F)
  have hZZ : Z * Z = τ • Z + 1 := by
    have h := CFSG.LinearAlgebra.mul_self_eq_trace_smul_sub_one Z hdet
    rw [htrace, sub_eq_add_neg, hneg] at h
    exact h
  have hZrec : ∀ k : ℕ, Z ^ (k + 2) = τ • Z ^ (k + 1) + Z ^ k := by
    intro k
    calc Z ^ (k + 2) = Z ^ k * Z ^ 2 := by rw [pow_add]
      _ = Z ^ k * (τ • Z + 1) := by rw [pow_two, hZZ]
      _ = τ • (Z ^ k * Z) + Z ^ k := by rw [mul_add, mul_smul_comm, mul_one]
      _ = τ • Z ^ (k + 1) + Z ^ k := by rw [← pow_succ]
  have hrec : ∀ k : ℕ, a (k + 2) = τ * a (k + 1) + a k := by
    intro k
    have h10 : (Z ^ (k + 2)) 1 0 = τ * (Z ^ (k + 1)) 1 0 + (Z ^ k) 1 0 := by
      rw [hZrec k]
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    dsimp only [a]
    rw [h10]
    field_simp [ht]
  refine ⟨?_, ?_, hrec⟩
  · simp [a]
  · dsimp only [a]
    rw [pow_one, hZ10, div_self ht]

private theorem pow_lower_left_aux_closed
    (p : ℕ) [Fact p.Prime] [CharP F p] (h2 : (2 : F) = 0)
    {τ : F} {ζ : (FiniteField.Extension F p 2)ˣ}
    (hτ : algebraMap F (FiniteField.Extension F p 2) τ =
      (ζ : FiniteField.Extension F p 2) + (ζ : FiniteField.Extension F p 2)⁻¹)
    {a : ℕ → F} (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (hrec : ∀ k : ℕ, a (k + 2) = τ * a (k + 1) + a k) :
    ∀ k : ℕ, algebraMap F (FiniteField.Extension F p 2) (a k) *
      ((ζ : FiniteField.Extension F p 2) - (ζ : FiniteField.Extension F p 2)⁻¹) =
      (ζ : FiniteField.Extension F p 2) ^ k -
        ((ζ : FiniteField.Extension F p 2)⁻¹) ^ k := by
  let E := FiniteField.Extension F p 2
  let u : E := (ζ : E)
  let v : E := (ζ : E)⁻¹
  have huv : u * v = 1 := by
    dsimp only [u, v]
    exact mul_inv_cancel₀ (Units.ne_zero ζ)
  have huvsum : u + v = algebraMap F E τ := by
    dsimp only [u, v]
    exact hτ.symm
  have hnegE : (-1 : E) = 1 := by
    haveI : CharP F 2 := by
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h (Fact.out : p.Prime).ne_one
      · rw [← h]; infer_instance
    haveI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
    exact CharTwo.neg_eq 1
  have hu2 : u ^ 2 = algebraMap F E τ * u + 1 := by
    have h : u ^ 2 + 1 = algebraMap F E τ * u := by
      calc u ^ 2 + 1 = (u + v) * u := by rw [add_mul, mul_comm v u, huv, pow_two]
        _ = algebraMap F E τ * u := by rw [huvsum]
    linear_combination h + hnegE
  have hv2 : v ^ 2 = algebraMap F E τ * v + 1 := by
    have h : v ^ 2 + 1 = algebraMap F E τ * v := by
      calc v ^ 2 + 1 = (v + u) * v := by rw [add_mul, huv, pow_two]
        _ = algebraMap F E τ * v := by rw [add_comm v u, huvsum]
    linear_combination h + hnegE
  have hstep : ∀ k : ℕ, u ^ (k + 2) - v ^ (k + 2) =
      algebraMap F E τ * (u ^ (k + 1) - v ^ (k + 1)) + (u ^ k - v ^ k) := by
    intro k
    calc u ^ (k + 2) - v ^ (k + 2)
        = u ^ k * u ^ 2 - v ^ k * v ^ 2 := by rw [pow_add, pow_add]
      _ = u ^ k * (algebraMap F E τ * u + 1) -
            v ^ k * (algebraMap F E τ * v + 1) := by rw [hu2, hv2]
      _ = algebraMap F E τ * (u ^ (k + 1) - v ^ (k + 1)) + (u ^ k - v ^ k) := by
            rw [pow_succ, pow_succ]
            ring
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · simp [ha0]
    · simp [ha1]
    · have ih1 := ih (k + 1) (by omega)
      have ih2 := ih k (by omega)
      have hrec' := hrec k
      rw [hrec', map_add]
      calc (algebraMap F E (τ * a (k + 1)) + algebraMap F E (a k)) * (u - v)
          = (algebraMap F E τ * algebraMap F E (a (k + 1)) +
              algebraMap F E (a k)) * (u - v) := by rw [map_mul]
        _ = algebraMap F E τ * (algebraMap F E (a (k + 1)) * (u - v)) +
              algebraMap F E (a k) * (u - v) := by ring
        _ = algebraMap F E τ * (u ^ (k + 1) - v ^ (k + 1)) + (u ^ k - v ^ k) := by
            rw [ih1, ih2]
        _ = u ^ (k + 2) - v ^ (k + 2) := by rw [hstep]

private theorem pow_lower_left_aux_ne_zero
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (hcop : Nat.Coprime (Nat.card F + 1) 2)
    {ζ : (FiniteField.Extension F p 2)ˣ}
    (hζ : orderOf ζ = Nat.card F + 1)
    {a : ℕ → F} {m : ℕ} (hm1 : 1 ≤ m) (hmq : m ≤ Nat.card F)
    (hclosed : ∀ k : ℕ, algebraMap F (FiniteField.Extension F p 2) (a k) *
      ((ζ : FiniteField.Extension F p 2) - (ζ : FiniteField.Extension F p 2)⁻¹) =
      (ζ : FiniteField.Extension F p 2) ^ k -
        ((ζ : FiniteField.Extension F p 2)⁻¹) ^ k) :
    a m ≠ 0 := by
  let E := FiniteField.Extension F p 2
  let u : E := (ζ : E)
  let v : E := (ζ : E)⁻¹
  intro hzero
  have hclosedm := hclosed m
  rw [hzero, map_zero, zero_mul] at hclosedm
  have huvm : u ^ m = v ^ m := sub_eq_zero.mp hclosedm.symm
  have hsq : (u ^ m) ^ 2 = 1 := by
    calc (u ^ m) ^ 2 = u ^ m * u ^ m := by rw [pow_two]
      _ = u ^ m * v ^ m := by rw [huvm]
      _ = u ^ m * (u ^ m)⁻¹ := by
            congr 1
            dsimp only [v]
            rw [inv_pow]
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero m (Units.ne_zero ζ))
  have hpow2 : (ζ : E) ^ (2 * m) = 1 := by
    rw [show 2 * m = m * 2 by omega, pow_mul]
    exact hsq
  have hpow2U : ζ ^ (2 * m) = 1 := Units.ext hpow2
  have hdvd2m : Nat.card F + 1 ∣ 2 * m := by
    rw [← hζ]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow2U
  have hdivm : Nat.card F + 1 ∣ m := hcop.dvd_of_dvd_mul_left hdvd2m
  have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  have hle : Nat.card F + 1 ≤ m := Nat.le_of_dvd hmpos hdivm
  exact (not_le_of_gt (Nat.lt_succ_self (Nat.card F))) (hle.trans hmq)

private theorem pow_lower_left_ne_zero (p : ℕ) [Fact p.Prime] [CharP F p]
    (h2 : (2 : F) = 0) (hcop : Nat.Coprime (Nat.card F + 1) 2)
    {τ : F} {ζ : (FiniteField.Extension F p 2)ˣ}
    (hζ : orderOf ζ = Nat.card F + 1)
    (hτ : algebraMap F (FiniteField.Extension F p 2) τ =
      (ζ : FiniteField.Extension F p 2) + (ζ : FiniteField.Extension F p 2)⁻¹)
    {s t : F} (ht : t ≠ 0) (hst : s * t = τ)
    {m : ℕ} (hm1 : 1 ≤ m) (hmq : m ≤ Nat.card F) :
    ((utriElt s * ltriElt t : SL(2, F)) ^ m : SL(2, F)) 1 0 ≠ 0 := by
  classical
  let Z : Matrix (Fin 2) (Fin 2) F := (utriElt s * ltriElt t : SL(2, F))
  let a : ℕ → F := fun k => (Z ^ k) 1 0 / t
  have hrec_data := pow_lower_left_aux_rec (F := F) (p := p) h2 ht hst
  dsimp only at hrec_data
  obtain ⟨ha0, ha1, hrec⟩ := hrec_data
  have hclosed := pow_lower_left_aux_closed (F := F) (p := p) (a := a) h2 hτ ha0 ha1 hrec
  have ham : a m ≠ 0 :=
    pow_lower_left_aux_ne_zero (F := F) (p := p) (a := a) hcop hζ hm1 hmq hclosed
  change (Z ^ m) 1 0 ≠ 0
  have hZpow10 : (Z ^ m) 1 0 = a m * t := by
    dsimp only [a]
    rw [div_mul_cancel₀ _ ht]
  rw [hZpow10]
  exact mul_ne_zero ham ht

end Singer

section F7

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

private theorem card_sylow_sl2 : Nat.card (Sylow 2 SL(2, F)) = Nat.card F + 1 := by
  let P : Sylow 2 SL(2, F) := utriSylow F
  have hP : (P : Subgroup SL(2, F)) = utri F := rfl
  have hidx : (borel F).index = Nat.card F + 1 := by
    have hcard := Subgroup.card_mul_index (borel F)
    rw [card_borel, card_sl2] at hcard
    have hsq : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
      simpa [mul_comm] using (Nat.pow_two_sub_pow_two (Nat.card F) 1)
    rw [hsq, mul_assoc] at hcard
    have hq : 0 < Nat.card F := Nat.card_pos
    have hq1 : 0 < Nat.card F - 1 := by
      have := Finite.one_lt_card (α := F)
      omega
    exact Nat.eq_of_mul_eq_mul_left hq1 (Nat.eq_of_mul_eq_mul_left hq hcard)
  have hPset : (P : Set SL(2, F)) = (utri F : Set SL(2, F)) := by
    exact congrArg (fun H : Subgroup SL(2, F) => (H : Set SL(2, F))) (by
      simpa [P] using coe_utriSylow)
  have hcardP : Nat.card (Sylow 2 SL(2, F)) =
      (Subgroup.normalizer (utri F : Set SL(2, F))).index := by
    have h := P.card_eq_index_normalizer
    rwa [hPset] at h
  calc Nat.card (Sylow 2 SL(2, F)) =
        (Subgroup.normalizer (utri F : Set SL(2, F))).index := hcardP
    _ = (borel F).index := by rw [normalizer_utri]
    _ = Nat.card F + 1 := hidx

theorem exists_utri_mul_ltri_conj_pow (x : SL(2, F)) (hxU : x ∈ utri F) (hx1 : x ≠ 1) :
    ∃ y ∈ ltri F, y ≠ 1 ∧
      ∀ g : SL(2, F), ∃ k : ℕ,
        conjSubgroup g (utri F) = conjSubgroup ((x * y) ^ k) (utri F) := by
  classical
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have hqeven : Fintype.card F % 2 = 0 :=
    FiniteField.even_card_of_char_two (ringChar.eq F 2)
  have hqodd : Odd (Nat.card F + 1) := by
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    omega
  have hcop : Nat.Coprime (Nat.card F + 1) 2 := Nat.coprime_two_right.mpr hqodd
  have hsyl : Nat.card (Sylow 2 SL(2, F)) = Nat.card F + 1 := card_sylow_sl2
  let P : Sylow 2 SL(2, F) := utriSylow F
  have hP : (P : Subgroup SL(2, F)) = utri F := by
    simpa [P] using coe_utriSylow
  haveI : CharP F (ringChar F) := ringChar.charP F
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  obtain ⟨τ, hτ0, ζ, hζ, hτ⟩ := exists_singer_trace (F := F) (ringChar F) h2F
  obtain ⟨s, rfl⟩ := mem_utri_iff.mp hxU
  have hs : s ≠ 0 := fun h0 => hx1 (by rw [h0, utriElt_zero])
  let t : F := τ / s
  have ht : t ≠ 0 := div_ne_zero hτ0 hs
  have hst : s * t = τ := by
    dsimp only [t]
    field_simp [hs]
  let z : SL(2, F) := utriElt s * ltriElt t
  have hz_borel : ∀ m : ℕ, 1 ≤ m → m ≤ Nat.card F → z ^ m ∉ borel F := by
    intro m hm1 hmq hmem
    have h := pow_lower_left_ne_zero (F := F) (ringChar F) h2F hcop hζ hτ ht hst hm1 hmq
    exact h hmem
  let conjSylow (g : SL(2, F)) : Sylow 2 SL(2, F) :=
    Sylow.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective P
  let f : Fin (Nat.card F + 1) → Sylow 2 SL(2, F) := fun k => conjSylow (z ^ (k : ℕ))
  have hf_inj : Function.Injective f := by
    have hlt_contra : ∀ i j : Fin (Nat.card F + 1), (i : ℕ) < (j : ℕ) → f i ≠ f j := by
      intro i j hlt hij
      have hsub : (f i : Subgroup SL(2, F)) = (f j : Subgroup SL(2, F)) :=
        congrArg (fun Q : Sylow 2 SL(2, F) => (Q : Subgroup SL(2, F))) hij
      rw [show (f i : Subgroup SL(2, F)) = conjSubgroup (z ^ (i : ℕ)) (utri F) by
            simp [f, conjSylow, Sylow.coe_mapSurjective, hP, conjSubgroup],
          show (f j : Subgroup SL(2, F)) = conjSubgroup (z ^ (j : ℕ)) (utri F) by
            simp [f, conjSylow, Sylow.coe_mapSurjective, hP, conjSubgroup]] at hsub
      have hmemN : (z ^ (i : ℕ))⁻¹ * z ^ (j : ℕ) ∈
          Subgroup.normalizer (utri F : Set SL(2, F)) :=
        conjSubgroup_eq_conjSubgroup_iff.mp hsub
      have hpow : (z ^ (i : ℕ))⁻¹ * z ^ (j : ℕ) = z ^ ((j : ℕ) - (i : ℕ)) := by
        have hp : z ^ (j : ℕ) = z ^ (i : ℕ) * z ^ ((j : ℕ) - (i : ℕ)) := by
          rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]
        rw [hp]
        group
      have hmemB : z ^ ((j : ℕ) - (i : ℕ)) ∈ borel F := by
        rw [hpow] at hmemN
        rwa [normalizer_utri] at hmemN
      have hm1 : 1 ≤ (j : ℕ) - (i : ℕ) := by omega
      have hmq : (j : ℕ) - (i : ℕ) ≤ Nat.card F := by
        have hj := j.2
        omega
      exact hz_borel _ hm1 hmq hmemB
    intro i j hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
    · exact (hlt_contra i j hlt hij).elim
    · exact Fin.ext heq
    · exact (hlt_contra j i hgt hij.symm).elim
  have hbij : Function.Bijective f :=
    hf_inj.bijective_of_nat_card_le (by rw [Nat.card_fin, hsyl])
  refine ⟨ltriElt t, ltriElt_mem_ltri t, ltriElt_ne_one ht, ?_⟩
  intro g
  obtain ⟨k, hk⟩ := hbij.2 (conjSylow g)
  refine ⟨k, ?_⟩
  have hsub : (f k : Subgroup SL(2, F)) = (conjSylow g : Subgroup SL(2, F)) :=
    congrArg (fun Q : Sylow 2 SL(2, F) => (Q : Subgroup SL(2, F))) hk
  rw [show (f k : Subgroup SL(2, F)) = conjSubgroup (z ^ (k : ℕ)) (utri F) by
        simp [f, conjSylow, Sylow.coe_mapSurjective, hP, conjSubgroup],
      show (conjSylow g : Subgroup SL(2, F)) = conjSubgroup g (utri F) by
        simp [conjSylow, Sylow.coe_mapSurjective, hP, conjSubgroup]] at hsub
  exact hsub.symm

theorem exists_mul_conjSubgroup_conj_utri_pow_of_ne {a b : SL(2, F)}
    (hne : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F))
    {x : SL(2, F)} (hxA : x ∈ conjSubgroup a (utri F)) (hx1 : x ≠ 1) :
    ∃ y ∈ conjSubgroup b (utri F), y ≠ 1 ∧
      ∀ h : SL(2, F), ∃ k : ℕ,
        conjSubgroup h (conjSubgroup a (utri F)) =
          conjSubgroup ((x * y) ^ k) (conjSubgroup a (utri F)) := by
  obtain ⟨g, hA, hB⟩ := exists_conj_utri_ltri_of_ne hne
  let x0 : SL(2, F) := g⁻¹ * x * g
  have hx0U : x0 ∈ utri F := by
    have hxA' : x ∈ conjSubgroup g (utri F) := by rw [← hA]; exact hxA
    exact mem_conjSubgroup.mp hxA'
  have hx01 : x0 ≠ 1 := by
    intro h
    apply hx1
    have := congrArg (fun t : SL(2, F) => g * t * g⁻¹) h
    simpa [x0, mul_assoc] using this
  obtain ⟨y0, hy0L, hy01, hreg⟩ := exists_utri_mul_ltri_conj_pow x0 hx0U hx01
  let z0 : SL(2, F) := x0 * y0
  let y : SL(2, F) := g * y0 * g⁻¹
  have hyB : y ∈ conjSubgroup b (utri F) := by
    rw [hB]
    exact conj_mem_conjSubgroup g hy0L
  have hy1 : y ≠ 1 := by
    intro h
    apply hy01
    have := congrArg (fun t : SL(2, F) => g⁻¹ * t * g) h
    simpa [y, mul_assoc] using this
  refine ⟨y, hyB, hy1, ?_⟩
  intro h
  obtain ⟨k, hk⟩ := hreg (g⁻¹ * h * g)
  refine ⟨k, ?_⟩
  have hz : (x * y) ^ k = g * z0 ^ k * g⁻¹ := by
    rw [show x * y = g * z0 * g⁻¹ by dsimp only [z0, x0, y]; group]
    rw [conj_pow]
  calc conjSubgroup h (conjSubgroup a (utri F)) =
        conjSubgroup h (conjSubgroup g (utri F)) := by rw [hA]
    _ = conjSubgroup (h * g) (utri F) := by rw [conjSubgroup_conjSubgroup]
    _ = conjSubgroup (g * (g⁻¹ * h * g)) (utri F) := by congr 1; group
    _ = conjSubgroup g (conjSubgroup (g⁻¹ * h * g) (utri F)) := by
        rw [conjSubgroup_conjSubgroup]
    _ = conjSubgroup g (conjSubgroup (z0 ^ k) (utri F)) := by rw [hk]
    _ = conjSubgroup (g * z0 ^ k) (utri F) := by rw [conjSubgroup_conjSubgroup]
    _ = conjSubgroup ((x * y) ^ k) (conjSubgroup a (utri F)) := by
        rw [hz, hA, conjSubgroup_conjSubgroup]
        congr 1
        group

end F7

end CFSG.RankThree.GF2n.Tim81.Sec4
