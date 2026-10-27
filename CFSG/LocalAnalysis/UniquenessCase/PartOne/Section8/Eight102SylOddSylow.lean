module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102SylOddAbstract
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102SylOddAut
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102SylOddTorus
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.ComponentClassification.Burgoyne.U
  CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem card_statedProj_statedSU_four (h : UnitaryFieldData 2 f K) :
    Nat.card (StatedProj (StatedSU 4 (2 ^ f) K)) =
      (2 ^ f) ^ 6 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) * ((2 ^ f) ^ 4 - 1) := by
  set Q := 2 ^ f with hQdef
  have hQ1 : 1 ≤ Q := Nat.one_le_pow f 2 (by norm_num)
  have hK : Nat.card K = Q ^ 2 := by
    rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
  have hmain := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (p := 2)
    (f := f) (n := 4) Nat.prime_two h.one_le hK (by norm_num)
  rw [← hQdef] at hmain
  rw [hmain]
  have hgcd : Nat.gcd 4 (Q + 1) = 1 := by
    have hQeven : 2 ∣ Q := by
      rw [hQdef]
      exact dvd_pow_self 2 (n := f) (Nat.one_le_iff_ne_zero.mp h.one_le)
    have h2 : ¬ 2 ∣ Q + 1 := by
      intro hdiv
      have h1 : 2 ∣ 1 := by simpa using Nat.dvd_sub hdiv hQeven
      norm_num at h1
    have hodd : Odd (Q + 1) := Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp h2)
    have hc : Nat.Coprime (2 ^ 2) (Q + 1) := by
      rw [Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
      exact hodd.coprime_two_right.symm
    simpa using hc
  rw [hgcd, Nat.div_one]
  have e2 : (((Q : ℤ) ^ 2 - (-1) ^ 2).toNat) = Q ^ 2 - 1 := by
    rw [show ((-1 : ℤ)) ^ 2 = 1 by norm_num]
    have hQ1' : (1 : ℤ) ≤ Q := by exact_mod_cast hQ1
    have hpos : (0 : ℤ) ≤ (Q : ℤ) ^ 2 - 1 := by
      have h2 : (1 : ℤ) ≤ (Q : ℤ) ^ 2 := by
        simpa using pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1) hQ1' 2
      linarith
    have hcast : (((((Q : ℤ) ^ 2 - 1).toNat : ℕ) : ℤ)) = ((Q ^ 2 - 1 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hpos, Nat.cast_sub (Nat.one_le_pow 2 Q (by omega))]
      push_cast
      ring
    exact Nat.cast_injective hcast
  have e3 : (((Q : ℤ) ^ 3 - (-1) ^ 3).toNat) = Q ^ 3 + 1 := by
    rw [show ((-1 : ℤ)) ^ 3 = -1 by norm_num]
    have hpos : (0 : ℤ) ≤ (Q : ℤ) ^ 3 - (-1) := by
      have : (0 : ℤ) ≤ (Q : ℤ) ^ 3 := by positivity
      linarith
    have hcast : (((((Q : ℤ) ^ 3 - (-1)).toNat : ℕ) : ℤ)) = ((Q ^ 3 + 1 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hpos]
      push_cast
      ring
    exact Nat.cast_injective hcast
  have e4 : (((Q : ℤ) ^ 4 - (-1) ^ 4).toNat) = Q ^ 4 - 1 := by
    rw [show ((-1 : ℤ)) ^ 4 = 1 by norm_num]
    have hQ1' : (1 : ℤ) ≤ Q := by exact_mod_cast hQ1
    have hpos : (0 : ℤ) ≤ (Q : ℤ) ^ 4 - 1 := by
      have h4 : (1 : ℤ) ≤ (Q : ℤ) ^ 4 := by
        simpa using pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1) hQ1' 4
      linarith
    have hcast : (((((Q : ℤ) ^ 4 - 1).toNat : ℕ) : ℤ)) = ((Q ^ 4 - 1 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hpos, Nat.cast_sub (Nat.one_le_pow 4 Q (by omega))]
      push_cast
      ring
    exact Nat.cast_injective hcast
  have hprod : (∏ i ∈ Finset.Icc 2 4, (((Q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) =
      (Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1) := by
    rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 4),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3)]
    rw [Finset.Icc_self, Finset.prod_singleton]
    simp only [Nat.reduceAdd]
    rw [e2, e3, e4]
  rw [hprod]
  rw [show 4 * (4 - 1) / 2 = 6 by norm_num]
  ring

theorem not_dvd_index_u4TorusHom_range (h : UnitaryFieldData 2 f K) {q : ℕ} (hq : q.Prime)
    (hq3 : q ≠ 3) (hqf : q ∣ 2 ^ f + 1) : ¬ q ∣ (u4TorusHom (f := f) (K := K)).range.index := by
  classical
  set Q := 2 ^ f with hQdef
  have hQ1 : 1 ≤ Q := Nat.one_le_pow f 2 (by norm_num)
  have hQ2 : 2 ≤ Q := by
    rw [hQdef]
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) h.one_le
  have hK : Nat.card K = Q ^ 2 := by
    rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
  have hqf' : q ∣ Q + 1 := by rwa [hQdef]
  have h1 : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    simpa [one_pow, mul_comm] using sq_tsub_sq Q 1
  have hcardμ : Nat.card (rootsOfUnity (Q + 1) K) = Q + 1 := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, hK, Nat.gcd_comm]
    exact Nat.gcd_eq_left (by rw [h1]; exact ⟨Q - 1, by rw [mul_comm]⟩)
  have hcardD : Nat.card (Fin 3 → rootsOfUnity (Q + 1) K) = (Q + 1) ^ 3 := by
    rw [Nat.card_fun, hcardμ]
    norm_num
  have hcardT : Nat.card (u4TorusHom (f := f) (K := K)).range = (Q + 1) ^ 3 := by
    rw [MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (u4TorusHom_injective (f := f) (K := K) h.one_le),
      Subgroup.card_top, hcardD]
  have hidx : (u4TorusHom (f := f) (K := K)).range.index * (Q + 1) ^ 3 =
      Nat.card (StatedProj (StatedSU 4 (2 ^ f) K)) := by
    rw [← hcardT]
    exact Subgroup.index_mul_card (G := StatedProj (StatedSU 4 (2 ^ f) K))
      (H := (u4TorusHom (f := f) (K := K)).range)
  have hfac : (u4TorusHom (f := f) (K := K)).range.index * (Q + 1) ^ 3 =
      Q ^ 6 * (Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1) := by
    rw [hidx, card_statedProj_statedSU_four h]
  have h3 : Q ^ 3 + 1 = (Q + 1) * (Q ^ 2 - Q + 1) := by
    have hQ2' : Q ≤ Q ^ 2 := by nlinarith
    apply Nat.cast_injective (R := ℤ)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_sub hQ2']
    ring
  have h4 : Q ^ 4 - 1 = (Q ^ 2 - 1) * (Q ^ 2 + 1) := by
    have hh := sq_tsub_sq (Q ^ 2) 1
    rw [one_pow, mul_comm] at hh
    rwa [show (Q ^ 2) ^ 2 = Q ^ 4 by ring] at hh
  have harith : Q ^ 6 * (Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1) =
      (Q ^ 6 * (Q - 1) ^ 2 * (Q ^ 2 - Q + 1) * (Q ^ 2 + 1)) * (Q + 1) ^ 3 := by
    rw [h1, h3, h4, h1]
    ring
  have hpos : 0 < (Q + 1) ^ 3 := by positivity
  have hidxeq : (u4TorusHom (f := f) (K := K)).range.index =
      Q ^ 6 * (Q - 1) ^ 2 * (Q ^ 2 - Q + 1) * (Q ^ 2 + 1) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hfac, harith]
  rw [hidxeq]
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h2Q : 2 ∣ Q := by
      rw [hQdef]
      exact dvd_pow_self 2 (n := f) (Nat.one_le_iff_ne_zero.mp h.one_le)
    have h1' : 2 ∣ 1 := by simpa using Nat.dvd_sub hqf' h2Q
    norm_num at h1'
  have hqQ : ¬ q ∣ Q := by
    intro hdiv
    have h1' : q ∣ 1 := by simpa using Nat.dvd_sub hqf' hdiv
    exact hq.not_dvd_one h1'
  have hqQ6 : ¬ q ∣ Q ^ 6 := fun hdiv => hqQ (hq.dvd_of_dvd_pow hdiv)
  have hqQm1 : ¬ q ∣ Q - 1 := by
    intro hdiv
    have hd : q ∣ (Q + 1) - (Q - 1) := Nat.dvd_sub hqf' hdiv
    have h2 : (Q + 1) - (Q - 1) = 2 := by omega
    rw [h2] at hd
    have : q = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hq.ne_one
    exact hq2 this
  have hqQm1sq : ¬ q ∣ (Q - 1) ^ 2 := fun hdiv => hqQm1 (hq.dvd_of_dvd_pow hdiv)
  have heq1 : Q ^ 2 - Q + 1 = (Q + 1) * (Q - 2) + 3 := by
    have hQ2' : Q ≤ Q ^ 2 := by nlinarith
    apply Nat.cast_injective (R := ℤ)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_sub hQ2',
      Nat.cast_sub hQ2, Nat.cast_ofNat]
    ring
  have hqQ2mQ1 : ¬ q ∣ Q ^ 2 - Q + 1 := by
    intro hdiv
    have hdiv1 : q ∣ (Q + 1) * (Q - 2) := Dvd.dvd.mul_right hqf' (Q - 2)
    rw [heq1] at hdiv
    have h3' : q ∣ 3 := (Nat.dvd_add_right hdiv1).mp hdiv
    have : q = 3 := ((Nat.dvd_prime Nat.prime_three).mp h3').resolve_left hq.ne_one
    exact hq3 this
  have heq2 : Q ^ 2 + 1 = (Q + 1) * (Q - 1) + 2 := by
    have h1' : (Q + 1) * (Q - 1) = Q ^ 2 - 1 := by
      rw [h1, mul_comm]
    rw [h1']
    omega
  have hqQ2p1 : ¬ q ∣ Q ^ 2 + 1 := by
    intro hdiv
    have hdiv1 : q ∣ (Q + 1) * (Q - 1) := Dvd.dvd.mul_right hqf' (Q - 1)
    rw [heq2] at hdiv
    have h2' : q ∣ 2 := (Nat.dvd_add_right hdiv1).mp hdiv
    have : q = 2 := ((Nat.dvd_prime Nat.prime_two).mp h2').resolve_left hq.ne_one
    exact hq2 this
  intro hdiv
  obtain hdiv | hdiv := hq.dvd_mul.mp hdiv
  · obtain hdiv | hdiv := hq.dvd_mul.mp hdiv
    · obtain hdiv | hdiv := hq.dvd_mul.mp hdiv
      · exact hqQ6 hdiv
      · exact hqQm1sq hdiv
    · exact hqQ2mQ1 hdiv
  · exact hqQ2p1 hdiv

@[expose] noncomputable def u4TorusSylow (q : ℕ) : Subgroup (StatedProj (StatedSU 4 (2 ^ f) K)) :=
  ((powMonoidHom (q ^ (2 ^ f + 1).factorization q) :
    (Fin 3 → rootsOfUnity (2 ^ f + 1) K) →* _).ker).map u4TorusHom

omit [Finite K] in
theorem isPGroup_u4TorusSylow {q : ℕ} (_hq : q.Prime) :
    IsPGroup q (u4TorusSylow (f := f) (K := K) q) := by
  unfold u4TorusSylow
  refine IsPGroup.map ?_ (u4TorusHom (f := f) (K := K))
  intro d
  refine ⟨(2 ^ f + 1).factorization q, ?_⟩
  have hd := d.2
  simp only [MonoidHom.mem_ker, powMonoidHom_apply] at hd
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact hd

theorem not_dvd_index_u4TorusSylow (h : UnitaryFieldData 2 f K) (hf : Even f) {q : ℕ}
    (hq : q.Prime) (hqf : q ∣ 2 ^ f + 1) : ¬ q ∣ (u4TorusSylow (f := f) (K := K) q).index := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  set Q := 2 ^ f with hQdef
  set v := (Q + 1).factorization q with hv
  set w := ordCompl[q] (Q + 1) with hw
  have hQ1 : 1 ≤ Q := Nat.one_le_pow f 2 (by norm_num)
  have hqf' : q ∣ Q + 1 := by rwa [hQdef]
  have hq3 : q ≠ 3 := by
    intro hq3eq
    subst hq3eq
    have h3dvd : 3 ∣ 2 ^ f - 1 := by
      obtain ⟨k, hk⟩ := hf
      have hmod : (2 : ℕ) ^ f ≡ 1 [MOD 3] := by
        rw [hk, show k + k = 2 * k by ring, pow_mul]
        have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by norm_num
        simpa using h4.pow k
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow f 2 (by norm_num))).mp hmod.symm
    have h2 : 3 ∣ 2 := by
      have hd := Nat.dvd_sub hqf' h3dvd
      have h3eq : Q + 1 - (2 ^ f - 1) = 2 := by
        have h1 : 1 ≤ 2 ^ f := Nat.one_le_pow f 2 (by norm_num)
        omega
      rwa [h3eq] at hd
    norm_num at h2
  have hT : ¬ q ∣ (u4TorusHom (f := f) (K := K)).range.index :=
    not_dvd_index_u4TorusHom_range h hq hq3 hqf
  let P : Subgroup (Fin 3 → rootsOfUnity (Q + 1) K) := (powMonoidHom (q ^ v)).ker
  have hS : u4TorusSylow (f := f) (K := K) q =
      P.map (u4TorusHom (f := f) (K := K)) := by
    rw [u4TorusSylow]
  have hidx : (u4TorusSylow (f := f) (K := K) q).index =
      P.index * (u4TorusHom (f := f) (K := K)).range.index := by
    rw [hS]
    exact Subgroup.index_map_of_injective (G := Fin 3 → rootsOfUnity (Q + 1) K)
      (H := P) (f := u4TorusHom (f := f) (K := K)) (u4TorusHom_injective h.one_le)
  have hP : ¬ q ∣ P.index := by
    intro hdiv
    have hcardq : q ∣ Nat.card ((Fin 3 → rootsOfUnity (Q + 1) K) ⧸ P) := by
      rwa [← Subgroup.index_eq_card]
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
      (G := (Fin 3 → rootsOfUnity (Q + 1) K) ⧸ P) q hcardq
    obtain ⟨e, he⟩ := QuotientGroup.mk'_surjective (N := P) x
    have hxq0 : x ^ q = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hx]
    have hxq : (QuotientGroup.mk' P e) ^ q = 1 := by
      rw [he]
      exact hxq0
    have heq : e ^ q ∈ P := by
      have h1 : QuotientGroup.mk' P (e ^ q) = 1 := by
        rw [map_pow]
        exact hxq
      exact (QuotientGroup.eq_one_iff (N := P) (e ^ q)).mp h1
    have heqq : e ^ (q ^ (v + 1)) = 1 := by
      have hmem := heq
      change (powMonoidHom (q ^ v)) (e ^ q) = 1 at hmem
      rw [powMonoidHom_apply] at hmem
      rwa [← pow_mul, ← pow_succ'] at hmem
    have heQ1 : e ^ (Q + 1) = 1 := by
      funext i
      apply Subtype.ext
      have h := (e i).2
      change ((e i : rootsOfUnity (Q + 1) K) : Kˣ) ^ (Q + 1) = 1 at h
      simpa using h
    have hQ1ne : Q + 1 ≠ 0 := by omega
    have hvmul : q ^ v * w = Q + 1 := by
      rw [hv, hw]
      exact Nat.ordProj_mul_ordCompl_eq_self (Q + 1) q
    have hwnot : ¬ q ∣ w := by
      rw [hw]
      exact Nat.not_dvd_ordCompl hq hQ1ne
    have hgcdn : Nat.gcd (q ^ (v + 1)) (Q + 1) = q ^ v := by
      have hcop : Nat.Coprime q w := (hq.coprime_iff_not_dvd).mpr hwnot
      have hdvd1 : q ^ v ∣ Nat.gcd (q ^ (v + 1)) (Q + 1) := by
        apply Nat.dvd_gcd
        · rw [pow_succ]
          exact dvd_mul_right _ _
        · rw [← hvmul]
          exact dvd_mul_right _ _
      obtain ⟨t, ht⟩ := hdvd1
      have hg1 : Nat.gcd (q ^ (v + 1)) (Q + 1) ∣ q ^ v * q := by
        rw [pow_succ]
        exact Nat.gcd_dvd_left _ _
      have hg2 : Nat.gcd (q ^ (v + 1)) (Q + 1) ∣ q ^ v * w := by
        rw [← hvmul]
        exact Nat.gcd_dvd_right _ _
      have htq : t ∣ q :=
        (Nat.mul_dvd_mul_iff_left (pow_pos hq.pos v)).mp (ht ▸ hg1)
      have htw : t ∣ w :=
        (Nat.mul_dvd_mul_iff_left (pow_pos hq.pos v)).mp (ht ▸ hg2)
      have ht1 : t = 1 := Nat.eq_one_of_dvd_coprimes hcop htq htw
      rw [ht, ht1, mul_one]
    have hev : e ^ (q ^ v) = 1 := by
      rw [← hgcdn]
      exact pow_gcd_eq_one.mpr ⟨heqq, heQ1⟩
    have hemem : e ∈ P := by
      change (powMonoidHom (q ^ v)) e = 1
      rw [powMonoidHom_apply]
      exact hev
    have hnot : e ∉ P := by
      intro hmem
      have hx1 : x = 1 := by
        rw [← he]
        exact (QuotientGroup.eq_one_iff (N := P) e).mpr hmem
      rw [hx1, orderOf_one] at hx
      exact hq.ne_one hx.symm
    exact hnot hemem
  rw [hidx]
  exact hq.not_dvd_mul hP hT

@[expose] noncomputable def u4TorusElem (ℓ : ℕ) : Subgroup (StatedProj (StatedSU 4 (2 ^ f) K)) :=
  Subgroup.map u4TorusHom
    { carrier := {d | d 1 = (d 0)⁻¹ ∧ d 0 ^ ℓ = 1 ∧ d 2 ^ ℓ = 1}
      mul_mem' := by
        intro d e hd he
        refine ⟨?_, ?_, ?_⟩
        · rw [Pi.mul_apply, Pi.mul_apply, hd.1, he.1, mul_inv, mul_comm]
        · rw [Pi.mul_apply, mul_pow, hd.2.1, he.2.1, one_mul]
        · rw [Pi.mul_apply, mul_pow, hd.2.2, he.2.2, one_mul]
      one_mem' := by
        refine ⟨?_, ?_, ?_⟩ <;> simp
      inv_mem' := by
        intro d hd
        refine ⟨?_, ?_, ?_⟩ <;> simp [Pi.inv_apply, hd.1, hd.2.1, hd.2.2, inv_pow] }

noncomputable def u4TorusElemEquiv (ℓ : ℕ) (hdiv : ℓ ∣ 2 ^ f + 1) :
    {d : Fin 3 → rootsOfUnity (2 ^ f + 1) K //
        d 1 = (d 0)⁻¹ ∧ d 0 ^ ℓ = 1 ∧ d 2 ^ ℓ = 1} ≃
      rootsOfUnity ℓ K × rootsOfUnity ℓ K where
  toFun d :=
    (⟨(d.1 0 : Kˣ), by
        simpa using congrArg (fun x : rootsOfUnity (2 ^ f + 1) K => (x : Kˣ)) d.2.2.1⟩,
     ⟨(d.1 2 : Kˣ), by
        simpa using congrArg (fun x : rootsOfUnity (2 ^ f + 1) K => (x : Kˣ)) d.2.2.2⟩)
  invFun p :=
    let a : rootsOfUnity (2 ^ f + 1) K :=
      ⟨(p.1 : Kˣ), by
        obtain ⟨t, ht⟩ := hdiv
        rw [ht, mem_rootsOfUnity, pow_mul, p.1.2, one_pow]⟩
    let b : rootsOfUnity (2 ^ f + 1) K :=
      ⟨(p.2 : Kˣ), by
        obtain ⟨t, ht⟩ := hdiv
        rw [ht, mem_rootsOfUnity, pow_mul, p.2.2, one_pow]⟩
    ⟨![a, a⁻¹, b], by
      refine ⟨?_, ?_, ?_⟩
      · simp
      · rw [Matrix.cons_val_zero]
        apply Subtype.ext
        change ((p.1 : Kˣ)) ^ ℓ = 1
        exact p.1.2
      · simp only [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
        apply Subtype.ext
        change ((p.2 : Kˣ)) ^ ℓ = 1
        exact p.2.2⟩
  left_inv d := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [d.2.1]
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext <;> simp

theorem isElemAbelian_u4TorusElem (h : UnitaryFieldData 2 f K) {ℓ : ℕ} (_hℓ : ℓ.Prime)
    (hℓf : ℓ ∣ 2 ^ f + 1) :
    IsElemAbelian ℓ (u4TorusElem (f := f) (K := K) ℓ) ∧
      Nat.card (u4TorusElem (f := f) (K := K) ℓ) = ℓ ^ 2 := by
  classical
  set Q := 2 ^ f with hQdef
  have hK : Nat.card K = Q ^ 2 := by
    rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
  have hℓQ : ℓ ∣ Q + 1 := by rwa [hQdef]
  have h1 : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    simpa [one_pow, mul_comm] using sq_tsub_sq Q 1
  have hμ : Nat.card (rootsOfUnity ℓ K) = ℓ := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, hK, Nat.gcd_comm]
    exact Nat.gcd_eq_left (dvd_trans hℓQ (by rw [h1]; exact ⟨Q - 1, by rw [mul_comm]⟩))
  have hEab : IsElemAbelian ℓ (u4TorusElem (f := f) (K := K) ℓ) := by
    constructor
    · rw [u4TorusElem]
      infer_instance
    · intro x hx
      rw [u4TorusElem] at hx
      obtain ⟨d, hd, hxeq⟩ := Subgroup.mem_map.mp hx
      rw [← hxeq, ← map_pow]
      have hdℓ : d ^ ℓ = 1 := by
        funext i
        fin_cases i <;> simp [Pi.pow_apply, hd.1, hd.2.1, hd.2.2, inv_pow]
      rw [hdℓ, map_one]
  refine ⟨hEab, ?_⟩
  rw [u4TorusElem, Subgroup.card_map_of_injective (u4TorusHom_injective h.one_le)]
  change Nat.card {d : Fin 3 → rootsOfUnity (Q + 1) K //
    d 1 = (d 0)⁻¹ ∧ d 0 ^ ℓ = 1 ∧ d 2 ^ ℓ = 1} = ℓ ^ 2
  rw [Nat.card_congr (u4TorusElemEquiv (f := f) (K := K) ℓ hℓQ)]
  rw [Nat.card_prod, hμ]
  ring

omit [Finite K] in
theorem u4TorusElem_le_u4TorusSylow {q : ℕ} (hq : q.Prime) (hqf : q ∣ 2 ^ f + 1) :
    u4TorusElem (f := f) (K := K) q ≤ u4TorusSylow q := by
  rw [u4TorusElem, u4TorusSylow]
  refine Subgroup.map_mono ?_
  intro d hd
  change (powMonoidHom (q ^ (2 ^ f + 1).factorization q)) d = 1
  rw [powMonoidHom_apply]
  have hdq : d ^ q = 1 := by
    funext i
    fin_cases i <;> simp [Pi.pow_apply, hd.1, hd.2.1, hd.2.2, inv_pow]
  obtain ⟨v', hv'⟩ := Nat.exists_eq_succ_of_ne_zero (show (2 ^ f + 1).factorization q ≠ 0 from
    (Nat.Prime.factorization_pos_of_dvd hq (by positivity) hqf).ne')
  rw [hv', pow_succ', pow_mul, hdq, one_pow]

theorem two_le_pRank_centralizer_u4TorusElem (h : UnitaryFieldData 2 f K) {q p : ℕ}
    (hp : p.Prime) (hpf : p ∣ 2 ^ f + 1) :
    2 ≤ Open.pRank p (centralizer (u4TorusElem (f := f) (K := K) q :
      Set (StatedProj (StatedSU 4 (2 ^ f) K)))) := by
  have hEp := isElemAbelian_u4TorusElem (f := f) (K := K) h hp hpf
  have hle : u4TorusElem (f := f) (K := K) p ≤
      centralizer (u4TorusElem (f := f) (K := K) q :
        Set (StatedProj (StatedSU 4 (2 ^ f) K))) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [u4TorusElem] at hx hy
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, mul_comm]
  exact CFSG.SectionRank.le_pRank (p := p) hp.one_lt hle hEp.1 (k := 2) hEp.2

theorem sylOddConcl_statedSU_four (h : UnitaryFieldData 2 f K) (hf : Even f) {q p : ℕ}
    (hq : q.Prime) (hp : p.Prime) (hqf : q ∣ 2 ^ f + 1) (hpf : p ∣ 2 ^ f + 1) :
    SylOddConcl (StatedProj (StatedSU 4 (2 ^ f) K)) q p := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_eq_sq h
  have hf1 : 1 ≤ f := h.one_le
  obtain ⟨a, m, hm, h2f⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (by omega : 2 * f ≠ 0) q hq.ne_one
  set Φ := uFieldAut h (n := 4) (by norm_num) σ with hΦdef
  have hS₀ : IsPGroup q (u4TorusSylow (f := f) (K := K) q) := isPGroup_u4TorusSylow hq
  have hS₀i : ¬ q ∣ (u4TorusSylow (f := f) (K := K) q).index :=
    not_dvd_index_u4TorusSylow h hf hq hqf
  have hS₀c : ∀ x ∈ u4TorusSylow (f := f) (K := K) q,
      ∀ y ∈ u4TorusSylow (f := f) (K := K) q, x * y = y * x := by
    intro x hx y hy
    rw [u4TorusSylow] at hx hy
    obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, mul_comm]
  have hE₀S₀ : u4TorusElem (f := f) (K := K) q ≤ u4TorusSylow (f := f) (K := K) q :=
    u4TorusElem_le_u4TorusSylow hq hqf
  have hE₀ := (isElemAbelian_u4TorusElem (f := f) (K := K) h hq hqf).1
  have hE₀q := (isElemAbelian_u4TorusElem (f := f) (K := K) h hq hqf).2
  have hE₀p := two_le_pRank_centralizer_u4TorusElem (f := f) (K := K) (q := q) h hp hpf
  have hΦ : ∀ α : MulAut (StatedProj (StatedSU 4 (2 ^ f) K)),
      ∃ y : StatedProj (StatedSU 4 (2 ^ f) K), ∃ j : ℕ,
        α = MulAut.conj y * Φ ^ j := by
    intro α
    obtain ⟨y, j, hα⟩ := exists_conj_mul_uFieldAut_pow h hσ α
    exact ⟨y, j, hα⟩
  have hΦS : ∀ s ∈ u4TorusSylow (f := f) (K := K) q,
      Φ s ∈ u4TorusSylow (f := f) (K := K) q := by
    intro s hs
    rw [u4TorusSylow] at hs ⊢
    obtain ⟨d, hdP, rfl⟩ := Subgroup.mem_map.mp hs
    rw [hΦdef, uFieldAut_u4TorusHom h hσ]
    refine Subgroup.mem_map_of_mem _ ?_
    have hd := hdP
    change (powMonoidHom (q ^ (2 ^ f + 1).factorization q)) d = 1 at hd
    rw [powMonoidHom_apply] at hd
    change (powMonoidHom (q ^ (2 ^ f + 1).factorization q)) (d ^ 2) = 1
    rw [powMonoidHom_apply]
    rw [← pow_mul, mul_comm, pow_mul, hd, one_pow]
  have hΦm : Φ ^ (q ^ a * m) = 1 := by
    rw [hΦdef, ← h2f]
    exact uFieldAut_pow_two_mul_eq_one h hσ
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h2Q : 2 ∣ 2 ^ f := dvd_pow_self 2 (n := f) (Nat.one_le_iff_ne_zero.mp h.one_le)
    have h1 : 2 ∣ 1 := by simpa using Nat.dvd_sub hqf h2Q
    norm_num at h1
  have h2ne0 : (2 : ZMod q) ≠ 0 := by
    intro hzero
    have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hzero
    have hqeq : q = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left hq.ne_one
    exact hq2 hqeq
  have hord_dvd_2f : orderOf (2 : ZMod q) ∣ 2 * f := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have h0 : ((2 : ZMod q) ^ f + 1) = 0 := by
      have h : (((2 : ℕ) ^ f + 1 : ℕ) : ZMod q) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact hqf
      simpa using h
    have hneg : (2 : ZMod q) ^ f = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      exact h0
    rw [show 2 * f = f * 2 by ring, pow_mul, hneg]
    exact neg_one_sq
  have hord_dvd_qm1 : orderOf (2 : ZMod q) ∣ q - 1 :=
    ZMod.orderOf_dvd_card_sub_one h2ne0
  have hcop : Nat.Coprime (orderOf (2 : ZMod q)) (q ^ a) := by
    have hcop_q : Nat.Coprime (q - 1) (q ^ a) := by
      rcases Nat.eq_zero_or_pos a with ha0 | ha
      · rw [ha0, pow_zero]
        exact Nat.coprime_one_right _
      · rw [Nat.coprime_pow_right_iff ha]
        rw [Nat.coprime_self_sub_left hq.one_le]
        simp
    exact Nat.Coprime.of_dvd_left hord_dvd_qm1 hcop_q
  have hord_dvd_m : orderOf (2 : ZMod q) ∣ m := by
    have h := hord_dvd_2f
    rw [h2f] at h
    exact hcop.dvd_of_dvd_mul_left h
  have h2m : (2 : ZMod q) ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp hord_dvd_m
  have hq_dvd : q ∣ 2 ^ m - 1 := by
    have hmod : 2 ^ m ≡ 1 [MOD q] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      exact h2m
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow m 2 (by norm_num))).mp hmod.symm
  obtain ⟨t, ht⟩ := hq_dvd
  have h2m_eq : 2 ^ m = q * t + 1 := by
    have hpos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    rw [← Nat.sub_add_cancel hpos, ht]
  have hΦfix : ∀ s ∈ u4TorusSylow (f := f) (K := K) q, s ^ q = 1 →
      (Φ ^ m) s = s := by
    intro s hs hsq
    rw [u4TorusSylow] at hs
    obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.mp hs
    have hdq : d ^ q = 1 := by
      apply u4TorusHom_injective (f := f) (K := K) h.one_le
      rw [map_pow, map_one]
      exact hsq
    have hd2m : d ^ (2 ^ m) = d := by
      rw [h2m_eq, pow_add, pow_one, pow_mul, hdq, one_pow, one_mul]
    rw [hΦdef, uFieldAut_pow_u4TorusHom h hσ m d, hd2m]
  exact sylOddConcl_of_torus (X := StatedProj (StatedSU 4 (2 ^ f) K)) (q := q) (p := p)
    (S₀ := u4TorusSylow (f := f) (K := K) q) (E₀ := u4TorusElem (f := f) (K := K) q)
    (Φ := Φ) (m := m) (a := a) hS₀ hS₀i hS₀c hE₀S₀ hE₀ hE₀q hE₀p hΦ hΦS hm hΦm hΦfix

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
