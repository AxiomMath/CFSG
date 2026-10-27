module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KSp6C
public import CFSG.RankThree.PartTwo.Sec21.Hering214KSp6G
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
public import CFSG.RankThree.PartTwo.Sec8.Hering611RSp62Inner

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Sec4.Item434Kit
open Sp6R Sp6Data

namespace Sp6Data

theorem dec6_codeOfRows (R : List ℕ) : dec6 (codeOfRows R) = dr R := by
  ext i j
  simp only [dec6, dr, Matrix.of_apply, bit]
  have hlen : 6 * (i : ℕ) + j < (codeOfRows R).length := by
    simp only [codeOfRows, List.length_map, List.length_range]
    omega
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [codeOfRows, List.getElem_map, List.getElem_range]
  have hd : (6 * (i : ℕ) + j) / 6 = i := by omega
  have hm : (6 * (i : ℕ) + j) % 6 = j := by omega
  rw [hd, hm]
  cases (R.getD i 0).testBit j <;> simp

theorem canon_rowsOf (n : ℕ) : Canon (rowsOf n) := by
  refine ⟨by simp [rowsOf], ?_⟩
  intro r hr
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
  have : (n >>> (6 * i)) &&& 63 ≤ 63 := Nat.and_le_right
  omega

theorem canon_zR0 : Canon zR0 := ⟨rfl, by decide⟩
theorem canon_zR1 : Canon zR1 := ⟨rfl, by decide⟩
theorem canon_zR2 : Canon zR2 := ⟨rfl, by decide⟩
theorem canon_tR : Canon tR := ⟨rfl, by decide⟩

theorem canon_eltR (a b c i : ℕ) : Canon (eltR a b c i) := by
  have h1 := canon_powR canon_zR0 a
  have h2 := canon_powR canon_zR1 b
  have h3 := canon_powR canon_zR2 c
  have h4 := canon_powR canon_tR i
  have h5 := canon_mulR h1.1 h2.2
  have h6 := canon_mulR h5.1 h3.2
  exact canon_mulR h6.1 h4.2

theorem canon_cubeR {A : List ℕ} (hA : Canon A) : Canon (cubeR A) :=
  canon_mulR (by rw [length_mulR]; exact hA.1) hA.2

theorem canon_conjR {Z U : List ℕ} (hZ : Canon Z) (hU : Canon U) : Canon (conjR Z U) := by
  have h1 := canon_mulR hZ.1 hU.2
  have h2 := canon_mulR hZ.1 hZ.2
  exact canon_mulR h1.1 h2.2

theorem dec6_zCode0 : dec6 zCode0 = dr zR0 := by decide +kernel
theorem dec6_zCode1 : dec6 zCode1 = dr zR1 := by decide +kernel
theorem dec6_zCode2 : dec6 zCode2 = dr zR2 := by decide +kernel
theorem dec6_tCode : dec6 tCode = dr tR := by decide +kernel

section Cert


theorem mat6_zH0 : mat6 (zH 0) = dr zR0 := (mat6_zH 0).trans dec6_zCode0
theorem mat6_zH1 : mat6 (zH 1) = dr zR1 := (mat6_zH 1).trans dec6_zCode1
theorem mat6_zH2 : mat6 (zH 2) = dr zR2 := (mat6_zH 2).trans dec6_zCode2
theorem mat6_tH' : mat6 CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH = dr tR := mat6_tH.trans dec6_tCode

theorem mat6_elt (v : Fin 3 → ZMod 3) (j : ℕ) :
    mat6 (vecElt zH v * Sec4.Item434SmallTwoIII.tH ^ j) = dr (eltR (v 0).val (v 1).val (v 2).val j) := by
  rw [vecElt, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, mat6_zH0, mat6_zH1,
    mat6_zH2, mat6_tH', eltR, dr_mulR, dr_mulR, dr_mulR, dr_powR, dr_powR, dr_powR, dr_powR]

end Cert

theorem inv_eq_mul_self_of_pow_three {z : H6} (hz : z ^ 3 = 1) : z⁻¹ = z * z :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_three']; exact hz)

theorem mat6_conj {z u : H6} {Z U : List ℕ} (hz : z ^ 3 = 1) (hZ : mat6 z = dr Z)
    (hu : mat6 u = dr U) : mat6 (z * u * z⁻¹) = dr (conjR Z U) := by
  rw [inv_eq_mul_self_of_pow_three hz, map_mul, map_mul, map_mul, hZ, hu, conjR]
  simp only [dr_mulR]

theorem fourDatum_of_fourChk {x y u1 u2 : H6} {X Y U1 U2 : List ℕ} (hX : Canon X) (hY : Canon Y)
    (hU1 : Canon U1) (hU2 : Canon U2) (hx : mat6 x = dr X) (hy : mat6 y = dr Y)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hu1 : mat6 u1 = dr U1) (hu2 : mat6 u2 = dr U2)
    (h : fourChk X Y U1 U2 = true) : FourDatum x y := by
  have f4 : ∀ {z : H6} {Z : List ℕ} {u : H6} {U : List ℕ}, z ^ 3 = 1 → mat6 z = dr Z →
      mat6 u = dr U → four4B U1 U2 (conjR Z U) = true → Four4 u1 u2 (z * u * z⁻¹) := by
    intro z Z u U hz hZ hu hb
    have hm := mat6_conj hz hZ hu
    simp only [four4B, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with ((h | h) | h) | h
    · exact Or.inl (mat6_injective (by rw [hm, h, dr_oneR, map_one]))
    · exact Or.inr (Or.inl (mat6_injective (by rw [hm, h, hu1])))
    · exact Or.inr (Or.inr (Or.inl (mat6_injective (by rw [hm, h, hu2]))))
    · exact Or.inr (Or.inr (Or.inr (mat6_injective (by rw [hm, h, map_mul, hu1, hu2, dr_mulR]))))
  have mv : ∀ {z : H6} {Z : List ℕ}, Canon Z → z ^ 3 = 1 → mat6 z = dr Z →
      conjR Z U1 ≠ U1 → z * u1 * z⁻¹ ≠ u1 := by
    intro z Z hZ hz hZ' hne he
    apply hne
    apply dr_inj (canon_conjR hZ hU1) hU1
    rw [← mat6_conj hz hZ' hu1, he, hu1]
  simp only [fourChk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨u1, u2, ?_, ?_, ?_, ?_, ?_, ?_, f4 hx3 hx hu1 ?_, f4 hx3 hx hu2 ?_, f4 hy3 hy hu1 ?_,
    f4 hy3 hy hu2 ?_, ?_⟩
  · exact mat6_injective (by rw [map_mul, hu1, ← dr_mulR, h1, dr_oneR, map_one])
  · exact mat6_injective (by rw [map_mul, hu2, ← dr_mulR, h2, dr_oneR, map_one])
  · exact mat6_injective (by rw [map_mul, map_mul, hu1, hu2, ← dr_mulR, ← dr_mulR, h3])
  · exact fun e => h4 (dr_inj hU1 canon_oneR (by rw [← hu1, e, map_one, dr_oneR]))
  · exact fun e => h5 (dr_inj hU2 canon_oneR (by rw [← hu2, e, map_one, dr_oneR]))
  · exact fun e => h6 (dr_inj hU1 hU2 (by rw [← hu1, ← hu2, e]))
  · simpa [four4B, beq_iff_eq] using h7
  · simpa [four4B, beq_iff_eq] using h8
  · simpa [four4B, beq_iff_eq] using h9
  · simpa [four4B, beq_iff_eq] using h10
  · rcases h11 with h | h
    · exact Or.inl (mv hX hx3 hx h)
    · exact Or.inr (mv hY hy3 hy h)

theorem mem_wordsXY {X Y a : List ℕ} (h : a ∈ wordsXY X Y) :
    ∃ e < 3, ∃ f < 3, mulR (powR X e) (powR Y f) = a := by
  simp only [wordsXY, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨e, he, f, hf, rfl⟩ := h
  exact ⟨e, he, f, hf, rfl⟩

theorem bad_of_classChk {k : ℕ} (hk16 : k < 16) {x y : H6} {X Y : List ℕ}
    (hx : mat6 x = dr X) (hy : mat6 y = dr Y) (hbad : isGood k = false)
    (h : classChk k X Y = true) :
    ∀ u : H6, u * u = 1 → u ≠ 1 → ¬ (u * x = x * u ∧ u * y = y * u) := by
  rintro u hu2 hu1 ⟨hux, huy⟩
  simp only [classChk, hbad, Bool.false_eq_true, if_false, Bool.and_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨hA, hB⟩ := h
  have hcyc := cycAll_true
  simp only [cycAll, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hcyc
  rcases hcyc k hk16 with hg | hc
  · rw [hbad] at hg
    exact absurd hg (by decide)
  have hMx : mat6 u * dr X = dr X * mat6 u := by
    rw [← hx, ← map_mul, ← map_mul, hux]
  have hMy : mat6 u * dr Y = dr Y * mat6 u := by
    rw [← hy, ← map_mul, ← map_mul, huy]
  have hcm : ∀ {a : List ℕ}, a ∈ wordsXY X Y → mat6 u * dr a = dr a * mat6 u := by
    intro a ha
    obtain ⟨e, -, f, -, rfl⟩ := mem_wordsXY ha
    rw [dr_mulR, dr_powR, dr_powR]
    exact ((Commute.pow_right (show Commute (mat6 u) (dr X) from hMx) e).mul_right
      (Commute.pow_right (show Commute (mat6 u) (dr Y) from hMy) f)).eq
  have hM1 := eq_one_of_cycChk (canon_rowsOf _) (canon_rowsOf _) (canon_rowsOf _) hc
    (hcm hA) (hcm hB) (by rw [← map_mul, hu2, map_one])
  exact hu1 (mat6_injective (by rw [hM1, map_one]))

theorem pairOK_spec {X Y : List ℕ} (h : pairOK X Y = true) (h1 : cubeR Y = oneR)
    (h2 : mulR X Y = mulR Y X) (h3 : Y ≠ oneR) (h4 : Y ≠ X) (h5 : Y ≠ mulR X X) :
    ∃ k < 16, classChk k X Y = true := by
  have hconj : (cubeR Y == oneR && mulR X Y == mulR Y X && Y != oneR && Y != X &&
      Y != mulR X X) = true := by
    simp [h1, h2, h3, h4, h5]
  unfold pairOK at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [hconj] at h
    exact absurd h (by decide)
  · simpa using h

theorem xOK_spec {X : List ℕ} (h1 : cubeR X = oneR) (h2 : X ≠ oneR) : xOK X = true := by
  simp [xOK, h1, h2]

theorem isGood_cases (k : ℕ) : isGood k = true ∨ isGood k = false := by
  cases isGood k <;> simp

theorem pair_dichotomy {x y : H6} (hx : x ∈ wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH)
    (hy : y ∈ wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    FourDatum x y ∨ ∀ u : H6, u * u = 1 → u ≠ 1 → ¬ (u * x = x * u ∧ u * y = y * u) := by
  obtain ⟨v, j, rfl⟩ := mem_wreathW wreathFacts_zH hx
  obtain ⟨v', j', rfl⟩ := mem_wreathW wreathFacts_zH hy
  have hxX := mat6_elt v j
  have hyY := mat6_elt v' j'
  have hXc := canon_eltR (v 0).val (v 1).val (v 2).val j
  have hYc := canon_eltR (v' 0).val (v' 1).val (v' 2).val j'
  have hP := pairsChk_true
  simp only [pairsChk, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hP
  have hP1 := hP _ (ZMod.val_lt (v 0)) _ (ZMod.val_lt (v 1)) _ (ZMod.val_lt (v 2)) j j.2
  have hP2 := fun hx' => (hP1.resolve_left hx') _ (ZMod.val_lt (v' 0)) _ (ZMod.val_lt (v' 1)) _
    (ZMod.val_lt (v' 2)) j' j'.2
  generalize eltR (v 0).val (v 1).val (v 2).val j = X at hxX hXc hP2
  generalize eltR (v' 0).val (v' 1).val (v' 2).val j' = Y at hyY hYc hP2
  have hX3 : cubeR X = oneR := by
    apply dr_inj (canon_cubeR hXc) canon_oneR
    rw [cubeR, dr_mulR, dr_mulR, dr_oneR, ← hxX, ← map_mul, ← map_mul, ← pow_three', hx3,
      map_one]
  have hY3 : cubeR Y = oneR := by
    apply dr_inj (canon_cubeR hYc) canon_oneR
    rw [cubeR, dr_mulR, dr_mulR, dr_oneR, ← hyY, ← map_mul, ← map_mul, ← pow_three', hy3,
      map_one]
  have hXne : X ≠ oneR := fun h => hx1 (mat6_injective (by rw [hxX, h, dr_oneR, map_one]))
  have hcomm : mulR X Y = mulR Y X := by
    apply dr_inj (canon_mulR hXc.1 hYc.2) (canon_mulR hYc.1 hXc.2)
    rw [dr_mulR, dr_mulR, ← hxX, ← hyY, ← map_mul, ← map_mul, hxy]
  have hY1 : Y ≠ oneR := by
    intro h
    apply hyx
    have : (vecElt zH v' * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j' : ℕ)) = 1 :=
      mat6_injective (by rw [hyY, h, dr_oneR, map_one])
    rw [this]
    exact Subgroup.one_mem _
  have hYX : Y ≠ X := by
    intro h
    apply hyx
    have : (vecElt zH v' * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j' : ℕ)) = vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) :=
      mat6_injective (by rw [hyY, hxX, h])
    rw [this]
    exact Subgroup.mem_zpowers _
  have hYXX : Y ≠ mulR X X := by
    intro h
    apply hyx
    have : (vecElt zH v' * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j' : ℕ)) =
        (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) * (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) :=
      mat6_injective (by rw [hyY, map_mul, hxX, h, dr_mulR])
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  obtain ⟨k, hk, hcls⟩ := pairOK_spec (hP2 (by simp [xOK_spec hX3 hXne])) hY3 hcomm hY1 hYX hYXX
  rcases isGood_cases k with hg | hg
  · simp only [classChk, hg, if_true, Bool.and_eq_true] at hcls
    obtain ⟨-, hf⟩ := hcls
    have hu := upairsOK_true
    simp only [upairsOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true'] at hu
    rcases hu k hk with hbad | ⟨hp1, hp2⟩
    · rw [hg] at hbad
      exact absurd hbad (by decide)
    · left
      exact fourDatum_of_fourChk (u1 := ofCode (codeOfRows (rowsOf (clsU1.getD k 0)),
          codeOfRows (rowsOf (clsU1.getD k 0))) hp1)
        (u2 := ofCode (codeOfRows (rowsOf (clsU2.getD k 0)),
          codeOfRows (rowsOf (clsU2.getD k 0))) hp2) hXc hYc (canon_rowsOf _) (canon_rowsOf _)
        hxX hyY hx3 hy3 ((mat6_ofCode _ hp1).trans (dec6_codeOfRows _))
        ((mat6_ofCode _ hp2).trans (dec6_codeOfRows _)) hf
  · right
    exact bad_of_classChk hk hxX hyY hg hcls

end Sp6Data

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem statedModel_H6 : StatedClassicalModel H6 .PSp 3 2 1 := by
  refine ⟨⟨Nat.prime_two, le_refl 1, by norm_num, by decide⟩, ?_⟩
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp [Nat.card_zmod],
    ⟨statedProjSp6Equiv.symm⟩⟩

theorem eInvFourFact_H6 : EInvFourFact H6 := by
  have hmod := statedModel_H6
  have hZ : Subgroup.center H6 = ⊥ := Sec8.Hering611.center_eq_bot_of_sp62 hmod
  have hinn : ∀ α : MulAut H6, ∃ y : H6, α = MulAut.conj y := fun α =>
    Sec8.Hering611.exists_conj_eq_of_sp62 hmod α
  haveI : Finite H6 := Nat.finite_of_card_ne_zero (by rw [card_H6]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P₀ : Sylow 3 H6 := Sylow.ofCard (wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH) (by
    rw [card_wreathW_zH, factorization_card_H6]
    norm_num)
  have hP₀ : (P₀ : Subgroup H6) = wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH := Sylow.coe_ofCard _ _
  refine eInvFourFact_of_sylow_dichotomy hZ hinn P₀ ?_
  intro x y hx hy hx3 hy3 hxy hx1 hyx
  rw [hP₀] at hx hy
  exact Sp6Data.pair_dichotomy hx hy hx3 hy3 hxy hx1 hyx

theorem eInvFourFact_of_statedModel_sp62 {X : Type} [Group X]
    (hX : StatedClassicalModel X .PSp 3 2 1) : EInvFourFact X := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSp_of_statedClassicalModel hX
  exact EInvFourFact.of_mulEquiv (e.trans sp62Equiv) eInvFourFact_H6

end CFSG.RankThree.PartTwo.Sec21.Hering214
