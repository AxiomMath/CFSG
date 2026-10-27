module

public import CFSG.LieType.Steinberg.Adjoint.Pairs
import all CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentE6RootTable

public section

namespace CFSG.StandardType.KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint

private def vecZ (l : List ℤ) : Fin Tag.E6.rank → ℤ := fun i => l.getD i 0

private def vecN (l : List ℕ) : Fin Tag.E6.rank → ℤ := vecZ (l.map ((↑) : ℕ → ℤ))

private def fin6 (i : ℕ) : Fin Tag.E6.rank := ⟨i % 6, Nat.mod_lt _ (by decide)⟩

private def stepL (l : List ℤ) (i : ℕ) : List ℤ := List.ofFn (reflect .E6 (fin6 i) (vecZ l))

private def wordVec : List ℕ → List ℤ
  | [] => []
  | k :: ws => ws.foldl stepL (List.ofFn (Pi.single (fin6 k) 1))

private def words : List (List ℕ) := [[5], [4], [3], [2], [1], [0], [5, 4], [4, 3], [3, 2],
  [3, 1], [2, 0], [5, 4, 3], [4, 3, 2], [4, 3, 1], [3, 2, 1], [3, 2, 0], [5, 4, 3, 2],
  [5, 4, 3, 1], [4, 3, 2, 1], [4, 3, 2, 0], [3, 2, 1, 0], [5, 4, 3, 2, 1], [4, 3, 2, 1, 3],
  [5, 4, 3, 2, 0], [4, 3, 2, 1, 0], [5, 4, 3, 2, 1, 3], [5, 4, 3, 2, 1, 0], [4, 3, 2, 1, 3, 0],
  [5, 4, 3, 2, 1, 3, 4], [5, 4, 3, 2, 1, 3, 0], [4, 3, 2, 1, 3, 0, 2], [5, 4, 3, 2, 1, 3, 4, 0],
  [5, 4, 3, 2, 1, 3, 0, 2], [5, 4, 3, 2, 1, 3, 4, 0, 2], [5, 4, 3, 2, 1, 3, 4, 0, 2, 3],
  [5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1]]

private theorem e6PosRootCoords_facts : ∀ a < 36, (e6PosRootCoords.getD a []).length = 6 ∧
    2 * e6DotNat (e6PosRootCoords.getD a []) (e6PosRootCoords.getD a []) =
      e6EdgeNat (e6PosRootCoords.getD a []) (e6PosRootCoords.getD a []) + 2 ∧ words.getD a [] ≠ [] ∧
    (e6PosRootCoords.getD a []).map ((↑) : ℕ → ℤ) = wordVec (words.getD a []) := by
  decide +kernel

private theorem vecZ_ofFn (f : Fin Tag.E6.rank → ℤ) : vecZ (List.ofFn f) = f := by
  funext i
  simp [vecZ, List.getD_eq_getElem?_getD]

private theorem isRoot_foldl (ws : List ℕ) :
    ∀ l, IsRoot .E6 (vecZ l) → IsRoot .E6 (vecZ (ws.foldl stepL l)) := by
  induction ws with
  | nil => exact fun _ h => h
  | cons i _ ih => exact fun l h => ih _ (by rw [stepL, vecZ_ofFn]; exact h.reflect _)

private theorem isRoot_e6PosRootCoords {a : ℕ} (ha : a < 36) :
    IsRoot .E6 (vecN (e6PosRootCoords.getD a [])) := by
  obtain ⟨-, -, hw, he⟩ := e6PosRootCoords_facts a ha
  obtain ⟨k, ws, h⟩ := List.exists_cons_of_ne_nil hw
  rw [vecN, he, h, wordVec]
  exact isRoot_foldl ws _ (by rw [vecZ_ofFn]; exact .basis _)

private def cartanE6 : Matrix (Fin 6) (Fin 6) ℤ := !![2, 0, -1, 0, 0, 0; 0, 2, 0, -1, 0, 0;
  -1, 0, 2, -1, 0, 0; 0, -1, -1, 2, -1, 0; 0, 0, 0, -1, 2, -1; 0, 0, 0, 0, -1, 2]

private theorem symmetrizedCartan_E6 : Tag.E6.symmetrizedCartan = cartanE6 := by
  have h : ∀ p : Fin 6 × Fin 6, Tag.E6.symmetrizedCartan p.1 p.2 = cartanE6 p.1 p.2 := by
    decide +kernel
  exact Matrix.ext fun i j => h (i, j)

private theorem iform_vecN {x y : List ℕ} (hx : x.length = 6) (hy : y.length = 6) :
    iform (vecN x) (vecN y) = 2 * (e6DotNat x y : ℤ) - e6EdgeNat x y ∧
      iform (vecN x) (vecN y) = 2 * (e6DotNat y x : ℤ) - e6EdgeNat y x := by
  match x, y, hx, hy with
  | [x0, x1, x2, x3, x4, x5], [y0, y1, y2, y3, y4, y5], _, _ =>
    rw [iform]
    change ∑ i : Fin 6, ∑ j : Fin 6, _ = _ ∧ ∑ i : Fin 6, ∑ j : Fin 6, _ = _
    constructor <;> simp [Fin.sum_univ_six, symmetrizedCartan_E6, cartanE6, vecN, vecZ, e6DotNat,
      e6EdgeNat] <;> ring

private def zl (e : Fin Tag.E6.rank → ℤ) : List ℕ :=
  [(e (0 : Fin 6) % 3).toNat, (e (1 : Fin 6) % 3).toNat, (e (2 : Fin 6) % 3).toNat,
    (e (3 : Fin 6) % 3).toNat, (e (4 : Fin 6) % 3).toNat, (e (5 : Fin 6) % 3).toNat]

private theorem exists_cert {e : Fin Tag.E6.rank → ℤ} (he : ∃ i, ¬ (3 : ℤ) ∣ e i) :
    ∃ c, e6KerEntryOK (zl e) c = true := by
  have hz : zl e ∈ e6CharCoords := by
    have h (x : ℤ) : (x % 3).toNat ∈ [0, 1, 2] := by
      rcases (by omega : (x % 3).toNat = 0 ∨ (x % 3).toNat = 1 ∨ (x % 3).toNat = 2) with
        h | h | h <;> simp [h]
    simp only [zl, e6CharCoords, List.mem_flatMap, List.mem_map]
    exact ⟨_, h _, _, h _, _, h _, _, h _, _, h _, _, h _, rfl⟩
  have h0 : zl e ≠ [0, 0, 0, 0, 0, 0] := by
    obtain ⟨i, hi⟩ := he
    intro h
    simp only [zl, List.cons.injEq] at h
    have hall (j : Fin 6) : (3 : ℤ) ∣ e j := by fin_cases j <;> simp <;> omega
    exact hi (hall i)
  generalize zl e = zs at hz h0 ⊢
  have h := e6KerTableCheck_eq_true
  simp only [e6KerTableCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hz
  refine ⟨e6KerRootTable[n]'(by omega), ?_⟩
  exact (h3 (e6CharCoords[n], e6KerRootTable[n]'(by omega))
    (List.mem_iff_getElem.2 ⟨n, by simp; omega, by simp⟩)).resolve_left h0

private def root (c k : ℕ) : List ℕ := e6PosRootCoords.getD ((e6KerTableIdx c).getD k 0) []

private theorem e6KerTableIdx_lt (c k : ℕ) : (e6KerTableIdx c).getD k 0 < 36 := by
  rcases k with _ | _ | _ | _ | _ | k <;> simp [e6KerTableIdx, Nat.mod_lt]

private theorem e6KerEntryOK_spec {zs : List ℕ} {c : ℕ} (h : e6KerEntryOK zs c = true) :
    (∀ k < e6KerTypeSize (c % 5), e6DotNat zs (root c k) % 3 = 0) ∧
      ∀ k l, k < l → l < e6KerTypeSize (c % 5) → 2 * e6DotNat (root c k) (root c l) +
          (if (e6KerTypeEdges (c % 5)).contains (k, l) then 1 else 0) =
        e6EdgeNat (root c k) (root c l) := by
  have hn : e6KerTypeSize (c % 5) ≤ 5 := by unfold e6KerTypeSize; split <;> omega
  simp only [e6KerEntryOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  set rs := ((e6KerTableIdx c).take (e6KerTypeSize (c % 5))).map fun i => e6PosRootCoords.getD i []
  have hrl : rs.length = e6KerTypeSize (c % 5) := by simp [rs, e6KerTableIdx, hn]
  have hg : ∀ k < e6KerTypeSize (c % 5), rs.getD k [] = root c k := fun k hk => by
    have hk5 : k < (e6KerTableIdx c).length := by simp [e6KerTableIdx]; omega
    simp [rs, root, List.getD_eq_getElem?_getD, hk, List.getElem?_eq_getElem hk5]
  refine ⟨fun k hk => ?_, fun k l hkl hl => ?_⟩
  · have hmem : rs.getD k [] ∈ rs := by
      rw [List.getD_eq_getElem _ _ (hrl ▸ hk)]
      exact List.getElem_mem _
    have := h.1 _ hmem
    rw [hg k hk] at this
    simpa using this
  · have := h.2 k (by omega) l hl
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at this
    rw [hg k (by omega), hg l hl] at this
    exact this.resolve_left (by omega)

private def gramT (t k l : ℕ) : ℤ :=
  if k = l then 2 else if (e6KerTypeEdges t).contains (min k l, max k l) then -1 else 0

private theorem iform_root {zs : List ℕ} {c : ℕ} (h : e6KerEntryOK zs c = true) {k l : ℕ}
    (hk : k < e6KerTypeSize (c % 5)) (hl : l < e6KerTypeSize (c % 5)) :
    iform (vecN (root c k)) (vecN (root c l)) = gramT (c % 5) k l := by
  have hlen (m : ℕ) : (root c m).length = 6 := (e6PosRootCoords_facts _ (e6KerTableIdx_lt c m)).1
  obtain ⟨h1, h2⟩ := iform_vecN (hlen k) (hlen l)
  rw [gramT]
  rcases lt_trichotomy k l with hkl | rfl | hkl
  · have := (e6KerEntryOK_spec h).2 k l hkl hl
    rw [h1, if_neg hkl.ne, Nat.min_eq_left hkl.le, Nat.max_eq_right hkl.le]
    split_ifs at this ⊢ <;> omega
  · have : 2 * e6DotNat (root c k) (root c k) = e6EdgeNat (root c k) (root c k) + 2 :=
      (e6PosRootCoords_facts _ (e6KerTableIdx_lt c k)).2.1
    rw [h1, if_pos rfl]
    omega
  · have := (e6KerEntryOK_spec h).2 l k hkl hk
    rw [h2, if_neg hkl.ne', Nat.min_eq_right hkl.le, Nat.max_eq_left hkl.le]
    split_ifs at this ⊢ <;> omega

private theorem iform_add_left' {τ : Tag} (x x' y : Fin τ.rank → ℤ) :
    iform (x + x') y = iform x y + iform x' y := by
  simp only [iform, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem iform_smul_left' {τ : Tag} (c : ℤ) (x y : Fin τ.rank → ℤ) :
    iform (c • x) y = c * iform x y := by
  simp only [iform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem linIndep_of_gram {v : Fin 5 → Fin Tag.E6.rank → ℤ} {t : ℕ} (ht : t < 4)
    (hG : ∀ k l : Fin 5, iform (v k) (v l) = gramT t k l) : LinearIndependent ℤ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hp (m : Fin 5) : ∑ k, g k * gramT t k m = 0 := by
    have h0 : iform (0 : Fin Tag.E6.rank → ℤ) (v m) = 0 := by simp [iform]
    simpa only [Fin.sum_univ_five, iform_add_left', iform_smul_left', hG, h0] using
      congrArg (iform · (v m)) hg
  obtain ⟨h0, h1, h2, h3, h4⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ := ⟨hp 0, hp 1, hp 2, hp 3, hp 4⟩
  have hall : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 ∧ g 3 = 0 ∧ g 4 = 0 := by
    interval_cases t <;> simp +decide [gramT, Fin.sum_univ_five] at h0 h1 h2 h3 h4 <;> omega
  intro k
  fin_cases k
  exacts [hall.1, hall.2.1, hall.2.2.1, hall.2.2.2.1, hall.2.2.2.2]

private theorem dvd_of_e6DotNat {e : Fin Tag.E6.rank → ℤ} {r : List ℕ} (hr : r.length = 6)
    (h : e6DotNat (zl e) r % 3 = 0) : (3 : ℤ) ∣ ∑ i, e i * vecN r i := by
  have hq (x : ℤ) : (((x % 3).toNat : ℕ) : ZMod 3) = (x : ZMod 3) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg x (by decide))]
    exact ZMod.intCast_mod x 3
  have h3 := (ZMod.natCast_eq_zero_iff (e6DotNat (zl e) r) 3).2 (Nat.dvd_of_mod_eq_zero h)
  have key : ((∑ i, e i * vecN r i : ℤ) : ZMod 3) = 0 := by
    match r, hr, h3 with
    | [r0, r1, r2, r3, r4, r5], _, h3 =>
      simp only [e6DotNat, zl, List.zipWith_cons_cons, List.zipWith_nil_left, List.sum_cons,
        List.sum_nil, Nat.cast_add, Nat.cast_mul, Nat.cast_zero, hq] at h3
      change ((∑ i : Fin 6, e i * vecN [r0, r1, r2, r3, r4, r5] i : ℤ) : ZMod 3) = 0
      simp [Fin.sum_univ_six, vecN, vecZ]
      linear_combination h3
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 key

theorem exists_roots_of_not_dvd_three_E6 (e : Fin Tag.E6.rank → ℤ) (he : ∃ i, ¬ (3 : ℤ) ∣ e i) :
    (∃ v : Fin 5 → Fin Tag.E6.rank → ℤ, (∀ k, IsRoot .E6 (v k)) ∧
        (∀ k, (3 : ℤ) ∣ ∑ i, e i * v k i) ∧ LinearIndependent ℤ v) ∨
      ∃ r : Fin 4 → Fin Tag.E6.rank → ℤ, (∀ k, IsRoot .E6 (r k)) ∧
        (∀ k, (3 : ℤ) ∣ ∑ i, e i * r k i) ∧ ∀ k l, k ≠ l → iform (r k) (r l) = 0 := by
  obtain ⟨c, hc⟩ := exists_cert he
  have hdvd (m : ℕ) (hm : m < e6KerTypeSize (c % 5)) : (3 : ℤ) ∣ ∑ i, e i * vecN (root c m) i :=
    dvd_of_e6DotNat (e6PosRootCoords_facts _ (e6KerTableIdx_lt c m)).1
      ((e6KerEntryOK_spec hc).1 m hm)
  by_cases ht : c % 5 = 4
  · have hn (k : Fin 4) : (k : ℕ) < e6KerTypeSize (c % 5) := k.isLt.trans_eq (if_pos ht).symm
    refine .inr ⟨fun k => vecN (root c k), fun k => isRoot_e6PosRootCoords (e6KerTableIdx_lt c k),
      fun k => hdvd k (hn k), fun k l hkl => ?_⟩
    show iform (vecN (root c k)) (vecN (root c l)) = 0
    rw [iform_root hc (hn k) (hn l), gramT, if_neg (Fin.val_ne_of_ne hkl), ht]
    rfl
  · have hn (k : Fin 5) : (k : ℕ) < e6KerTypeSize (c % 5) := k.isLt.trans_eq (if_neg ht).symm
    exact .inl ⟨fun k => vecN (root c k), fun k => isRoot_e6PosRootCoords (e6KerTableIdx_lt c k),
      fun k => hdvd k (hn k), linIndep_of_gram (by omega) fun k l => iform_root hc (hn k) (hn l)⟩

end CFSG.StandardType.KGCentE6

end
