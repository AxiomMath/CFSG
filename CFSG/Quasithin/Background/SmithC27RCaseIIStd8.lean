module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimPerm
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.QuasithinUnique Equiv Equiv.Perm

@[expose] def d8v4Gens : List (Perm (Fin 8)) :=
  [swap 0 1, Claim2526.v8g1, Claim2526.v8g2, Claim2526.v8g3, Claim2526.v8g4]

@[expose] def d8v4 : Subgroup (Perm (Fin 8)) := Subgroup.closure {g | g ∈ d8v4Gens}

@[expose] def s0 : Perm (Fin 8) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

section Codes

open A6Facts

private def d8v4GenC : List (List ℕ) :=
  [[1, 0, 2, 3, 4, 5, 6, 7], [1, 0, 3, 2, 4, 5, 6, 7], [2, 3, 0, 1, 4, 5, 6, 7],
   [0, 1, 2, 3, 5, 4, 7, 6], [0, 1, 2, 3, 6, 7, 4, 5]]

private def d8v4Tree : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4),
   (3, 0), (3, 3), (3, 4), (4, 4), (6, 3), (6, 4), (7, 3), (7, 4), (8, 4), (10, 3), (10, 4),
   (11, 4), (13, 3), (13, 4), (14, 4), (17, 4), (19, 4), (22, 4), (25, 4)]

private def d8v4Tbl : List (List ℕ) :=
  [[1, 2, 3, 4, 5], [0, 6, 7, 8, 9], [6, 0, 10, 11, 12], [13, 10, 0, 14, 15], [8, 11, 14, 0, 16],
   [9, 12, 15, 16, 0], [2, 1, 13, 17, 18], [10, 13, 1, 19, 20], [4, 17, 19, 1, 21],
   [5, 18, 20, 21, 1], [7, 3, 2, 22, 23], [17, 4, 22, 2, 24], [18, 5, 23, 24, 2], [3, 7, 6, 25, 26],
   [25, 22, 4, 3, 27], [26, 23, 5, 27, 3], [21, 24, 27, 5, 4], [11, 8, 25, 6, 28],
   [12, 9, 26, 28, 6], [22, 25, 8, 7, 29], [23, 26, 9, 29, 7], [16, 28, 29, 9, 8],
   [19, 14, 11, 10, 30], [20, 15, 12, 30, 10], [28, 16, 30, 12, 11], [14, 19, 17, 13, 31],
   [15, 20, 18, 31, 13], [31, 30, 16, 15, 14], [24, 21, 31, 18, 17], [30, 31, 21, 20, 19],
   [29, 27, 24, 23, 22], [27, 29, 28, 26, 25]]

private theorem d8v4_tbl : Core.tblCheckC (List.range 8) d8v4GenC
    (Core.buildCodes (List.range 8) d8v4GenC d8v4Tree) d8v4Tbl = true := by decide +kernel

private theorem d8v4_nodup : (Core.buildCodes (List.range 8) d8v4GenC d8v4Tree).Nodup := by
  decide +kernel

private theorem d8v4_length : (Core.buildCodes (List.range 8) d8v4GenC d8v4Tree).length = 32 := by
  decide +kernel

private theorem d8v4Gens_code : d8v4Gens.map (codeN 8) = d8v4GenC := by decide +kernel

private theorem mem_d8v4_iff {x : Perm (Fin 8)} :
    x ∈ d8v4 ↔ codeN 8 x ∈ Core.buildCodes (List.range 8) d8v4GenC d8v4Tree :=
  (mem_closure_iff_of_tblN d8v4Gens_code d8v4_tbl).1 x

theorem card_d8v4 : Nat.card d8v4 = 32 := by
  have := card_closure_eq_of_tblN d8v4Gens_code d8v4_tbl d8v4_nodup
  rw [d8v4_length] at this
  exact this

theorem card_V8 : Nat.card Claim2526.V8 = 16 := by
  have := card_closure_eq_of_tblN Claim2526.v8Gens_code Claim2526.v8_tbl Claim2526.v8_nodup
  have h16 : (Core.buildCodes (List.range 8) Claim2526.v8GenC Claim2526.v8Tree).length = 16 := by
    decide +kernel
  rw [h16] at this
  exact this

theorem V8_le_d8v4 : Claim2526.V8 ≤ d8v4 :=
  Subgroup.closure_mono fun _ hg => List.mem_cons_of_mem _ hg

theorem swap01_mem_d8v4 : swap (0 : Fin 8) 1 ∈ d8v4 :=
  Subgroup.subset_closure (show swap (0 : Fin 8) 1 ∈ d8v4Gens by decide)

theorem V8_le_alt : Claim2526.V8 ≤ alternatingGroup (Fin 8) := by
  have h : Claim2526.v8Gens.all (fun g => decide (sign g = 1)) = true := by decide +kernel
  refine (Subgroup.closure_le _).mpr fun g hg => ?_
  exact Perm.mem_alternatingGroup.mpr (of_decide_eq_true (List.all_eq_true.mp h g hg))

theorem s0_mem_alt : s0 ∈ alternatingGroup (Fin 8) :=
  Perm.mem_alternatingGroup.mpr (by decide)

theorem s0_mem_normalizer_V8 : s0 ∈ Subgroup.normalizer (Claim2526.V8 : Set (Perm (Fin 8))) :=
  Claim2526.mem_B2_of_codes (by decide +kernel)

private theorem d8v4Gens_mem_P8 : ∀ c ∈ d8v4GenC,
    c ∈ Core.buildCodes (List.range 8) Claim2526.p8GenC Claim2526.p8Tree := by
  decide +kernel

theorem d8v4_le_P8 : d8v4 ≤ Claim2526.P8 := by
  refine (Subgroup.closure_le _).mpr fun g hg => ?_
  refine ((mem_closure_iff_of_tblN Claim2526.p8Gens_code Claim2526.p8_tbl).1 g).2 ?_
  refine d8v4Gens_mem_P8 _ ?_
  rw [← d8v4Gens_code]
  exact List.mem_map_of_mem hg

theorem map_s0_d8v4_le_P8 : d8v4.map (MulAut.conj s0).toMonoidHom ≤ Claim2526.P8 := by
  rintro _ ⟨x, hx, rfl⟩
  have hs : s0 ∈ Claim2526.P8 :=
    Subgroup.subset_closure (show s0 ∈ Claim2526.p8Gens by decide)
  exact Claim2526.P8.mul_mem (Claim2526.P8.mul_mem hs (d8v4_le_P8 hx))
    (Claim2526.P8.inv_mem hs)

theorem not_map_s0_d8v4_le : ¬ d8v4.map (MulAut.conj s0).toMonoidHom ≤ d8v4 := by
  intro h
  have e : (MulAut.conj s0).toMonoidHom (swap 0 1) = swap 4 5 := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    decide
  have h1 := h (Subgroup.mem_map_of_mem _ swap01_mem_d8v4)
  rw [e, mem_d8v4_iff] at h1
  exact absurd h1 (by decide +kernel)

private def perm4Codes : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1], [1, 0, 2, 3],
   [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0], [2, 0, 1, 3], [2, 0, 3, 1],
   [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0], [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2],
   [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]]

private def perm4sCodes : List (List ℕ) :=
  [[4, 5, 6, 7], [4, 5, 7, 6], [4, 6, 5, 7], [4, 6, 7, 5], [4, 7, 5, 6], [4, 7, 6, 5], [5, 4, 6, 7],
   [5, 4, 7, 6], [5, 6, 4, 7], [5, 6, 7, 4], [5, 7, 4, 6], [5, 7, 6, 4], [6, 4, 5, 7], [6, 4, 7, 5],
   [6, 5, 4, 7], [6, 5, 7, 4], [6, 7, 4, 5], [6, 7, 5, 4], [7, 4, 5, 6], [7, 4, 6, 5], [7, 5, 4, 6],
   [7, 5, 6, 4], [7, 6, 4, 5], [7, 6, 5, 4]]

private theorem first_mem : ∀ a b c d : Fin 8, (a : ℕ) < 4 → (b : ℕ) < 4 → (c : ℕ) < 4 →
    (d : ℕ) < 4 → [(a : ℕ), b, c, d].Nodup → [(a : ℕ), b, c, d] ∈ perm4Codes := by
  decide +kernel

private theorem second_mem : ∀ a b c d : Fin 8, 4 ≤ (a : ℕ) → 4 ≤ (b : ℕ) → 4 ≤ (c : ℕ) →
    4 ≤ (d : ℕ) → [(a : ℕ), b, c, d].Nodup → [(a : ℕ), b, c, d] ∈ perm4sCodes := by
  decide +kernel

private theorem code_split {g : Perm (Fin 8)} (hg : ∀ x : Fin 8, (x : ℕ) < 4 ↔ (g x : ℕ) < 4) :
    ∃ A ∈ perm4Codes, ∃ B ∈ perm4sCodes, codeN 8 g = A ++ B := by
  have hnd : (codeN 8 g).Nodup := by
    unfold codeN
    rw [List.nodup_ofFn]
    intro a b h
    exact g.injective (Fin.ext h)
  rw [Claim2526.codeN8] at hnd ⊢
  have hnd' := List.nodup_append.mp (show ([(g 0 : ℕ), g 1, g 2, g 3] ++
    [(g 4 : ℕ), g 5, g 6, g 7]).Nodup from hnd)
  have hlo : ∀ x : Fin 8, (x : ℕ) < 4 → (g x : ℕ) < 4 := fun x hx => (hg x).1 hx
  have hhi : ∀ x : Fin 8, 4 ≤ (x : ℕ) → 4 ≤ (g x : ℕ) := fun x hx => by
    by_contra h
    have := (hg x).2 (by omega)
    omega
  exact ⟨_, first_mem _ _ _ _ (hlo 0 (by decide)) (hlo 1 (by decide)) (hlo 2 (by decide))
    (hlo 3 (by decide)) hnd'.1, _, second_mem _ _ _ _ (hhi 4 (by decide)) (hhi 5 (by decide))
    (hhi 6 (by decide)) (hhi 7 (by decide)) hnd'.2.1, rfl⟩

private def c4 (L : List ℕ) : List ℕ := Core.cmul (Core.cmul L L) (Core.cmul L L)

private theorem codeN_pow_four (g : Perm (Fin 8)) : codeN 8 (g ^ 4) = c4 (codeN 8 g) := by
  rw [show g ^ 4 = g * g * (g * g) by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq],
    codeN_mul, codeN_mul]
  rfl

private theorem pow12_check : ∀ A ∈ perm4Codes, ∀ B ∈ perm4sCodes,
    Core.cmul (Core.cmul (c4 (A ++ B)) (c4 (A ++ B))) (c4 (A ++ B)) = List.range 8 := by
  decide +kernel

private def evenRepCodes : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7], [1, 0, 2, 3, 5, 4, 6, 7], [1, 0, 2, 3, 6, 5, 4, 7],
   [1, 0, 2, 3, 7, 5, 6, 4], [2, 1, 0, 3, 5, 4, 6, 7], [2, 1, 0, 3, 6, 5, 4, 7],
   [2, 1, 0, 3, 7, 5, 6, 4], [3, 1, 2, 0, 5, 4, 6, 7], [3, 1, 2, 0, 6, 5, 4, 7],
   [3, 1, 2, 0, 7, 5, 6, 4]]

private def evenReps : List (Perm (Fin 8)) :=
  [1, swap 0 1 * swap 4 5, swap 0 1 * swap 4 6, swap 0 1 * swap 4 7, swap 0 2 * swap 4 5,
   swap 0 2 * swap 4 6, swap 0 2 * swap 4 7, swap 0 3 * swap 4 5, swap 0 3 * swap 4 6,
   swap 0 3 * swap 4 7]

private theorem evenReps_code : evenReps.map (codeN 8) = evenRepCodes := by decide +kernel

private theorem evenReps_alt : ∀ t ∈ evenReps, t ∈ alternatingGroup (Fin 8) := by
  have h : evenReps.all (fun t => decide (sign t = 1)) = true := by decide +kernel
  intro t ht
  exact Perm.mem_alternatingGroup.mpr (of_decide_eq_true (List.all_eq_true.mp h t ht))

private def hCodes : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7], [0, 2, 1, 3, 4, 5, 6, 7], [0, 3, 2, 1, 4, 5, 6, 7],
   [4, 5, 6, 7, 0, 1, 2, 3], [4, 5, 6, 7, 0, 2, 1, 3], [4, 5, 6, 7, 0, 3, 2, 1]]

private def hList : List (Perm (Fin 8)) :=
  [1, swap 1 2, swap 1 3, s0, swap 1 2 * s0, swap 1 3 * s0]

private theorem hList_code : hList.map (codeN 8) = hCodes := by decide +kernel

private theorem hCodes_normalize : ∀ hc ∈ hCodes, ∀ c ∈ Claim2526.v8Codes,
    ∃ c' ∈ Claim2526.v8Codes, Core.cmul hc c = Core.cmul c' hc := by
  decide +kernel

private theorem hList_normalizer {h : Perm (Fin 8)} (hh : h ∈ hList) :
    h ∈ Subgroup.normalizer (Claim2526.V8 : Set (Perm (Fin 8))) := by
  refine Claim2526.mem_B2_of_codes (hCodes_normalize _ ?_)
  rw [← hList_code]
  exact List.mem_map_of_mem hh

private theorem swap01_code : codeN 8 (swap (0 : Fin 8) 1) = [1, 0, 2, 3, 4, 5, 6, 7] := by
  decide +kernel

private theorem half_check : ∀ A ∈ perm4Codes, ∀ B ∈ perm4sCodes, c4 (A ++ B) = List.range 8 →
    ∃ v ∈ Claim2526.v8Codes, Core.cmul v (A ++ B) ∈ evenRepCodes ∨
      ∃ c ∈ hCodes, Core.cmul c (Core.cmul v (A ++ B)) = Core.cmul [1, 0, 2, 3, 4, 5, 6, 7] c := by
  decide +kernel

end Codes

private theorem map_conj_eq_d8v4 {P : Subgroup (Perm (Fin 8))} (hE : Claim2526.V8 ≤ P)
    (h32 : Nat.card P = 32) {h x : Perm (Fin 8)}
    (hN : h ∈ Subgroup.normalizer (Claim2526.V8 : Set (Perm (Fin 8)))) (hx : x ∈ P)
    (hhx : h * x = swap 0 1 * h) : P.map (MulAut.conj h).toMonoidHom = d8v4 := by
  have hconj : ∀ y, (MulAut.conj h).toMonoidHom y = h * y * h⁻¹ := fun y => rfl
  have hle : d8v4 ≤ P.map (MulAut.conj h).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    have hy' : y ∈ d8v4Gens := hy
    rcases List.mem_cons.mp hy' with rfl | hy'
    · refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
      rw [hconj, hhx, mul_inv_cancel_right]
    · have hyV : y ∈ Claim2526.V8 :=
        Subgroup.subset_closure (show y ∈ {g | g ∈ Claim2526.v8Gens} from hy')
      refine Subgroup.mem_map.mpr ⟨h⁻¹ * y * h, hE ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) y).mp hyV
        simpa using this
      · rw [hconj]
        group
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_d8v4, Subgroup.card_map_of_injective (MulAut.conj h).injective, h32]

theorem std44_classify {P : Subgroup (Perm (Fin 8))} (hP : IsPGroup 2 P)
    (hstab : ∀ g ∈ P, ∀ x : Fin 8, (x : ℕ) < 4 ↔ (g x : ℕ) < 4)
    (hE : Claim2526.V8 ≤ P) (hodd : ¬ P ≤ alternatingGroup (Fin 8))
    (h32 : Nat.card P = 32) :
    ∃ h : Perm (Fin 8), P.map (MulAut.conj h).toMonoidHom = d8v4 := by
  obtain ⟨g, hgP, hgA⟩ := IsConcreteLE.not_le_iff_exists.mp hodd
  obtain ⟨A, hA, B, hB, hL⟩ := code_split (hstab g hgP)
  obtain ⟨k, hk⟩ := hP ⟨g, hgP⟩
  have hk' : g ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h12 : g ^ 12 = 1 := by
    apply A6Facts.codeN_injective (n := 8)
    rw [show g ^ 12 = g ^ 4 * g ^ 4 * g ^ 4 by group, A6Facts.codeN_mul, A6Facts.codeN_mul,
      codeN_pow_four, hL, A6Facts.codeN_one]
    exact pow12_check A hA B hB
  have h4 : g ^ 4 = 1 := by
    have hgcd : (2 ^ k).gcd 12 ∣ 4 := by
      rw [show (12 : ℕ) = 4 * 3 from rfl, Nat.Coprime.gcd_mul _ (by norm_num),
        (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, mul_one]
      exact Nat.gcd_dvd_right _ _
    obtain ⟨c, hc⟩ := hgcd
    rw [hc, pow_mul, pow_gcd_eq_one.mpr ⟨hk', h12⟩, one_pow]
  have h4c : c4 (A ++ B) = List.range 8 := by
    rw [← hL, ← codeN_pow_four, h4, A6Facts.codeN_one]
  obtain ⟨v, hv, hcase⟩ := half_check A hA B hB h4c
  obtain ⟨w, hwV, rfl⟩ := Claim2526.exists_V8_of_code hv
  rw [← hL, ← A6Facts.codeN_mul] at hcase
  rcases hcase with heven | ⟨c, hc, hcomm⟩
  ·
    exfalso
    rw [← evenReps_code] at heven
    obtain ⟨t, ht, hte⟩ := List.mem_map.mp heven
    have htg : t = w * g := A6Facts.codeN_injective hte
    apply hgA
    have hg' : g = w⁻¹ * t := by
      rw [htg]
      group
    rw [hg']
    exact (alternatingGroup (Fin 8)).mul_mem
      ((alternatingGroup (Fin 8)).inv_mem (V8_le_alt hwV)) (evenReps_alt t ht)
  ·
    rw [← hList_code] at hc
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hc
    refine ⟨h, map_conj_eq_d8v4 hE h32 (hList_normalizer hh) (P.mul_mem (hE hwV) hgP) ?_⟩
    apply A6Facts.codeN_injective (n := 8)
    rw [A6Facts.codeN_mul, A6Facts.codeN_mul (swap 0 1), swap01_code]
    exact hcomm

end CFSG.Quasithin.SmithC27
