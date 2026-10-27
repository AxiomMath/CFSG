module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3SF4DatumBits
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth80.HeringSec117F4Producer

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Ree CFSG.LieType.Simplicity.TitsBits
  CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
open CFSG.LocalAnalysis.GLTheoremA.F4Sym (bitsProd hasBits_list_prod hasBits_pinnedX_one)

private theorem not_odd_orderOf {G : Type} [Monoid G] {x : G} {m : ℕ} (h2 : x ^ (2 * m) = 1)
    (h1 : x ^ m ≠ 1) : ¬ Odd (orderOf x) := fun hodd =>
  h1 (orderOf_dvd_iff_pow_eq_one.1
    ((Nat.coprime_two_right.2 hodd).dvd_of_dvd_mul_left (orderOf_dvd_of_pow_eq_one h2)))

private abbrev GenFor {G : Type} [Group G] (c : G) : Prop :=
  ∃ d : Fin 5 → G, ∃ e : G,
    (∀ i, IsConj (d i) c) ∧ IsConj e c ∧ IsConj (e * d 4) c ∧ e * d 4 = d 4 * e ∧
      ∃ t ∈ Subgroup.closure (Set.range (Fin.cons e d)),
        ∃ n ∈ Subgroup.closure (Set.range (Fin.cons e d)),
          orderOf t = 13 ∧ n⁻¹ * t * n = t ^ 2

private theorem GenFor.map {G : Type} [Group G] (φ : G ≃* G) {c : G} (h : GenFor c) :
    GenFor (φ c) := by
  obtain ⟨d, e, hd, he, hed, hcomm, t, ht, n, hn, hord, htn⟩ := h
  have hcl : ∀ x ∈ Subgroup.closure (Set.range (Fin.cons e d)),
      φ x ∈ Subgroup.closure (Set.range (Fin.cons (φ e) (φ ∘ d))) := by
    intro x hx
    have h := Subgroup.mem_map_of_mem φ.toMonoidHom hx
    rwa [MonoidHom.map_closure, MulEquiv.coe_toMonoidHom, ← Set.range_comp, Fin.comp_cons] at h
  refine ⟨φ ∘ d, φ e, fun i => φ.toMonoidHom.map_isConj (hd i), φ.toMonoidHom.map_isConj he,
    ?_, ?_, φ t, hcl t ht, φ n, hcl n hn, ?_, ?_⟩
  · simpa only [Function.comp_apply, MulEquiv.coe_toMonoidHom, map_mul] using
      φ.toMonoidHom.map_isConj hed
  · simp only [Function.comp_apply, ← map_mul, hcomm]
  · rw [MulEquiv.orderOf_eq, hord]
  · rw [← map_inv, ← map_mul, ← map_mul, htn, map_pow]

private def conjBits (w : List Letter) (C : ℕ) : ℕ :=
  mul (mul (evalB w) C) (evalB w.reverse)

private noncomputable abbrev word (K : Type) [Field K] (w : List Letter) : adjointGroup .F4 K :=
  evalG K w

section Bits

variable {K : Type} [Field K] [CharP K 2]

private theorem hasBits_f4Rep_singleton {p a : ℕ} (hp : p < 48)
    (ha : a < Tag.F4.rootCertificate.roots.length)
    (h : Tag.F4.rootCertificate.root a = orbitCertRoot .F4 p) :
    HasBits K (f4Rep K [p]) (pack (eltBits a)) := by
  have he : f4Rep K [p] = ⟨pinnedX ReeTag.F4.tag K (orbitCertRoot .F4 p) 1,
      pinnedX_mem_adjointGroup _ 1⟩ :=
    Subtype.ext (coe_f4Rep_singleton p)
  rw [he]
  exact hasBits_pinnedX_one (CFSG.SeitzReduction.isRoot_orbitCertRoot_F4 hp) ha h

private theorem hasBits_conj {c : adjointGroup .F4 K} {C : ℕ} (hc : HasBits K c C)
    (w : List Letter) : HasBits K (word K w * c * (word K w)⁻¹) (conjBits w C) := by
  have hinv : (word K w)⁻¹ = word K w.reverse := evalG_inv w
  rw [hinv]
  exact ((hasBits_evalG w).mul hc).mul (hasBits_evalG w.reverse)

private theorem hasBits_pow {g : adjointGroup .F4 K} {A : ℕ} (h : HasBits K g A) (k : ℕ) :
    HasBits K (g ^ k) (bitsProd (List.replicate k A)) := by
  simpa [List.map_replicate, List.prod_replicate] using
    hasBits_list_prod (fun _ : Unit => g) (fun _ => A) (fun _ => h) (List.replicate k ())

end Bits

private def tuBits : ℕ := mul (pack (eltBits 43)) (pack (eltBits 44))

private def vBits : ℕ := mul (pack (eltBits 36)) (pack (eltBits 35))

private def tuWord : List Letter :=
  [.n 0, .n 1, .n 2, .n 3, .n 2, .n 1, .n 2, .n 0, .n 1, .n 2, .n 3, .n 0, .n 1, .n 2, .n 1, .n 0]

private def vWord : List Letter :=
  [.n 2, .n 1, .n 2, .n 0, .n 1, .n 2, .n 3, .n 2, .n 1, .n 2, .n 0, .n 1]

private theorem tu_bits :
    bitsProd (List.replicate 6 (mul tuBits (conjBits tuWord tuBits))) % 2 ^ 2704 =
        oneBits % 2 ^ 2704 ∧
      bitsProd (List.replicate 3 (mul tuBits (conjBits tuWord tuBits))) % 2 ^ 2704 ≠
        oneBits % 2 ^ 2704 ∧
      bitsProd (List.replicate 4 (mul tuBits (conjBits tuWord tuBits))) % 2 ^ 2704 ≠
        oneBits % 2 ^ 2704 := by
  decide +kernel

private theorem v_bits :
    bitsProd (List.replicate 8 (mul vBits (conjBits vWord vBits))) % 2 ^ 2704 =
        oneBits % 2 ^ 2704 ∧
      bitsProd (List.replicate 4 (mul vBits (conjBits vWord vBits))) % 2 ^ 2704 ≠
        oneBits % 2 ^ 2704 := by
  decide +kernel

theorem f4ExclStatement_holds : F4ExclStatement := by
  intro K _ _ _ c hc
  have h47 : HasBits K (f4Rep K [47]) (pack (eltBits 43)) :=
    hasBits_f4Rep_singleton (by norm_num) (by decide +kernel) (by decide +kernel)
  have h44 : HasBits K (f4Rep K [44]) (pack (eltBits 44)) :=
    hasBits_f4Rep_singleton (by norm_num) (by decide +kernel) (by decide +kernel)
  have h41 : HasBits K (f4Rep K [41]) (pack (eltBits 36)) :=
    hasBits_f4Rep_singleton (by norm_num) (by decide +kernel) (by decide +kernel)
  have h45 : HasBits K (f4Rep K [45]) (pack (eltBits 35)) :=
    hasBits_f4Rep_singleton (by norm_num) (by decide +kernel) (by decide +kernel)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · have hc : HasBits K (f4Rep K [47, 44]) tuBits := by
      rw [f4Rep_pair]
      exact h47.mul h44
    have hst := hc.mul (hasBits_conj hc tuWord)
    refine ⟨_, _, IsConj.refl _,
      (isConj_iff.2 ⟨word K tuWord, rfl⟩).symm, fun h => ?_, ?_⟩
    · exact tu_bits.2.2 (((hasBits_pow hst 4).eq_iff hasBits_one).1 h)
    · refine not_odd_orderOf (m := 3) ?_ fun h => ?_
      · exact ((hasBits_pow hst 6).eq_iff hasBits_one).2 tu_bits.1
      · exact tu_bits.2.1 (((hasBits_pow hst 3).eq_iff hasBits_one).1 h)
  · have hc : HasBits K (f4Rep K [41, 45]) vBits := by
      rw [f4Rep_pair]
      exact h41.mul h45
    have hst := hc.mul (hasBits_conj hc vWord)
    refine ⟨_, _, IsConj.refl _,
      (isConj_iff.2 ⟨word K vWord, rfl⟩).symm, fun h => ?_, ?_⟩
    · exact v_bits.2 (((hasBits_pow hst 4).eq_iff hasBits_one).1 h)
    · refine not_odd_orderOf (m := 4) ?_ fun h => ?_
      · exact ((hasBits_pow hst 8).eq_iff hasBits_one).2 v_bits.1
      · exact v_bits.2 (((hasBits_pow hst 4).eq_iff hasBits_one).1 h)

private def longW0 : List Letter :=
  [.n 0, .x 1, .n 1, .n 2, .x 3, .n 3, .x 2, .n 1, .n 2, .x 0, .n 0, .n 1, .n 2, .n 3, .n 0, .n 1,
    .x 2, .n 2, .n 1, .x 0, .n 0]

private def longW1 : List Letter :=
  [.x 3, .x 1, .n 1, .x 2, .n 2, .n 3, .n 1, .n 2, .n 0, .n 1, .n 2, .n 3, .n 0, .x 1, .n 1, .n 2,
    .x 1, .n 1, .n 0]

private def longW2 : List Letter :=
  [.x 2, .n 0, .x 1, .n 1, .n 2, .n 3, .n 1, .n 2, .x 0, .n 0, .n 1, .x 2, .n 2, .n 3, .x 0, .n 0,
    .n 1, .x 2, .n 2, .n 1, .n 0]

private def longW3 : List Letter :=
  [.n 3, .x 0, .x 1, .x 2, .n 2, .n 0, .n 1, .n 2, .x 3, .n 3, .n 0, .x 1, .n 1, .n 2, .n 1, .x 0,
    .n 0]

private def longWords : Fin 6 → List Letter :=
  ![[.n 0], longW0, longW1, longW2, longW3, []]

private def longGenBits (j : Fin 6) : ℕ :=
  conjBits (longWords j) (pack (eltBits 43))

private def longT : List (Fin 6) := [5, 1, 3, 4]

private def longN : List (Fin 6) :=
  [0, 5, 0, 1, 0, 5, 0, 3, 5, 1, 4, 5, 2, 1, 2, 4, 3, 1, 4, 0, 4, 0, 3, 1, 4, 5, 0, 1, 5, 2, 1, 0,
    2, 3, 4, 0, 1, 4, 3, 0, 2, 4, 5, 0, 2, 5, 1, 2, 4, 0, 1, 0, 5, 0]

private theorem long_bits :
    mul (longGenBits 0) (longGenBits 5) % 2 ^ 2704 =
        mul (longGenBits 5) (longGenBits 0) % 2 ^ 2704 ∧
      mul (longGenBits 0) (longGenBits 5) % 2 ^ 2704 =
        conjBits [.x 0, .n 0] (pack (eltBits 43)) % 2 ^ 2704 ∧
      bitsProd (List.replicate 13 (bitsProd (longT.map longGenBits))) % 2 ^ 2704 =
        oneBits % 2 ^ 2704 ∧
      bitsProd (longT.map longGenBits) % 2 ^ 2704 ≠ oneBits % 2 ^ 2704 ∧
      mul (bitsProd (longT.map longGenBits)) (bitsProd (longN.map longGenBits)) % 2 ^ 2704 =
        mul (bitsProd (longN.map longGenBits))
          (bitsProd (List.replicate 2 (bitsProd (longT.map longGenBits)))) % 2 ^ 2704 := by
  decide +kernel

private noncomputable def longGen (K : Type) [Field K] (j : Fin 6) : adjointGroup .F4 K :=
  word K (longWords j) * f4Rep K [47] * (word K (longWords j))⁻¹

private theorem genFor_long (K : Type) [Field K] [Finite K] [CharP K 2] :
    GenFor (f4Rep K [47]) := by
  have hc : HasBits K (f4Rep K [47]) (pack (eltBits 43)) :=
    hasBits_f4Rep_singleton (by norm_num) (by decide +kernel) (by decide +kernel)
  have hconj : ∀ w, IsConj (word K w * f4Rep K [47] * (word K w)⁻¹) (f4Rep K [47]) := fun w =>
    (isConj_iff.2 ⟨word K w, rfl⟩).symm
  have hgen : ∀ j, HasBits K (longGen K j) (longGenBits j) := fun j => hasBits_conj hc _
  obtain ⟨h1, h2, h3, h4, h5⟩ := long_bits
  have hprod := hasBits_list_prod (longGen K) longGenBits hgen
  have hmem : ∀ L : List (Fin 6),
      (L.map (longGen K)).prod ∈ Subgroup.closure (Set.range (longGen K)) := fun L =>
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      exact Subgroup.subset_closure (Set.mem_range_self j)
  refine ⟨Fin.tail (longGen K), longGen K 0, fun i => hconj _, hconj _, ?_, ?_, ?_⟩
  · have he : longGen K 0 * longGen K 5 =
        word K [.x 0, .n 0] * f4Rep K [47] * (word K [.x 0, .n 0])⁻¹ :=
      ((hgen 0).mul (hgen 5)).eq_iff (hasBits_conj hc [.x 0, .n 0]) |>.2 h2
    show IsConj (longGen K 0 * longGen K 5) _
    rw [he]
    exact hconj _
  · exact ((hgen 0).mul (hgen 5)).eq_iff ((hgen 5).mul (hgen 0)) |>.2 h1
  · rw [Fin.cons_self_tail]
    haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    have ht := hprod longT
    have hn := hprod longN
    refine ⟨_, hmem longT, _, hmem longN, orderOf_eq_prime ?_ ?_, ?_⟩
    · exact ((hasBits_pow ht 13).eq_iff hasBits_one).2 h3
    · exact fun h => h4 ((ht.eq_iff hasBits_one).1 h)
    · have htn : (longT.map (longGen K)).prod * (longN.map (longGen K)).prod =
          (longN.map (longGen K)).prod * (longT.map (longGen K)).prod ^ 2 :=
        ((ht.mul hn).eq_iff (hn.mul (hasBits_pow ht 2))).2 h5
      rw [mul_assoc, htn, inv_mul_cancel_left]

theorem f4GenStatement_holds : F4GenStatement := by
  intro K _ _ _ c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact genFor_long K
  · rw [← (phi_f4Rep_classes (K := K)).1]
    exact GenFor.map (CFSG.SeitzReduction.f4DescPhi K) (genFor_long K)

end CFSG.RankThree.GF2n.Stroth80
