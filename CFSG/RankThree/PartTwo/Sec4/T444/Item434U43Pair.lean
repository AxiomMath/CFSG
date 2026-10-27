module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Class
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43PairCheck
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.PartTwo.Sec5.Hyp

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemU43

open CFSG.LieType.Multipliers.U43 CFSG.Assembly.LowTwoRank CFSG.Quasithin.G2U Matrix
open CFSG.Assembly (IsElemAbelian)

attribute [local irreducible] sAt

@[expose] def InSub (H : Subgroup SUg) (c : List ℕ) : Prop :=
  canon4 c = true ∧ ∃ g ∈ H, dec4 c = toMat g

theorem InSub.one (H : Subgroup SUg) : InSub H one4 :=
  ⟨canon4_one4, 1, H.one_mem, by rw [dec4_one4, map_one]⟩

theorem InSub.mul {H : Subgroup SUg} {x y : List ℕ} (hx : InSub H x) (hy : InSub H y) :
    InSub H (mul4 x y) := by
  obtain ⟨-, g, hg, e⟩ := hx
  obtain ⟨-, g', hg', e'⟩ := hy
  exact ⟨canon4_mul4 _ _, g * g', H.mul_mem hg hg', by rw [dec4_mul4, e, e', map_mul]⟩

theorem InSub.sq {H : Subgroup SUg} {x : List ℕ} (hx : InSub H x) : InSub H (sq4 x) := hx.mul hx

theorem InSub.canon {H : Subgroup SUg} {x : List ℕ} (hx : InSub H x) : canon4 x = true := hx.1

theorem inSub_uAt_iff (hsyl : uSylCheck = true) {H : Subgroup SUg} {t : ℕ} (ht : t < 729) :
    InSub H (uAt t) ↔ sAt t ∈ H := by
  constructor
  · rintro ⟨-, g, hg, e⟩
    have : sAt t = g := toMat_injective ((toMat_sAt hsyl ht).trans e)
    rw [this]
    exact hg
  · intro h
    exact ⟨canon4_uAt hsyl ht, sAt t, h, (toMat_sAt hsyl ht).symm⟩

theorem inSub_zaList {H : Subgroup SUg} {a : List ℕ} (hz : InSub H zc) (ha : InSub H a) :
    ∀ c ∈ zaList a, InSub H c := by
  intro c hc
  simp only [zaList, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hc
  obtain ⟨x, hx, y, hy, rfl⟩ := hc
  have hx' : InSub H x := by
    rcases hx with h | h | h
    · rw [h]; exact InSub.one H
    · rw [h]; exact hz
    · rw [h]; exact hz.sq
  have hy' : InSub H y := by
    rcases hy with h | h | h
    · rw [h]; exact InSub.one H
    · rw [h]; exact ha
    · rw [h]; exact ha.sq
  exact hx'.mul hy'

theorem inSub_pElemsOf {H : Subgroup SUg} {za : List (List ℕ)} {b : List ℕ}
    (hza : ∀ c ∈ za, InSub H c) (hb : InSub H b) : ∀ c ∈ pElemsOf za b, InSub H c := by
  intro c hc
  simp only [pElemsOf, List.mem_toArray, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨u, hu, hc⟩ := hc
  rcases hc with h | h | h
  · rw [h]; exact hza _ hu
  · rw [h]; exact (hza _ hu).mul hb
  · rw [h]; exact (hza _ hu).mul hb.sq

theorem inSub_e9Elems {H : Subgroup SUg} {a b : List ℕ} (ha : InSub H a) (hb : InSub H b) :
    ∀ c ∈ e9Elems a b, InSub H c := by
  intro c hc
  simp only [e9Elems, List.mem_toArray, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map] at hc
  obtain ⟨x, hx, y, hy, rfl⟩ := hc
  have hx' : InSub H x := by
    rcases hx with h | h | h
    · rw [h]; exact InSub.one H
    · rw [h]; exact ha
    · rw [h]; exact ha.sq
  have hy' : InSub H y := by
    rcases hy with h | h | h
    · rw [h]; exact InSub.one H
    · rw [h]; exact hb
    · rw [h]; exact hb.sq
  exact hx'.mul hy'

theorem size_pElemsOf (a b : List ℕ) : (pElemsOf (zaList a) b).size = 27 := by
  simp [pElemsOf, zaList]

theorem getD_mem_array {α : Type*} (arr : Array α) (d : α) {t : ℕ} (ht : t < arr.size) :
    arr.getD t d ∈ arr := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some]
  exact Array.getElem_mem ht

theorem mem_closure_pair_pow {L : Type*} [Group L] {g h : L} (hg3 : g ^ 3 = 1) (hh3 : h ^ 3 = 1)
    (hgh : Commute g h) :
    ∀ x ∈ Subgroup.closure ({g, h} : Set L), ∃ i j : ℕ, x = g ^ i * h ^ j := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨1, 0, by rw [hx]; simp⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨i, j, rfl⟩ := ihx
    obtain ⟨k, l, rfl⟩ := ihy
    refine ⟨i + k, j + l, ?_⟩
    have hc : Commute (h ^ j) (g ^ k) := (hgh.pow_pow k j).symm
    calc g ^ i * h ^ j * (g ^ k * h ^ l) = g ^ i * (h ^ j * g ^ k) * h ^ l := by
          simp only [mul_assoc]
      _ = g ^ i * (g ^ k * h ^ j) * h ^ l := by rw [hc.eq]
      _ = g ^ (i + k) * h ^ (j + l) := by rw [pow_add, pow_add]; simp only [mul_assoc]
  | inv x _ ihx =>
    obtain ⟨i, j, rfl⟩ := ihx
    refine ⟨2 * i, 2 * j, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    have hc : Commute (h ^ j) (g ^ (2 * i)) := (hgh.pow_pow (2 * i) j).symm
    calc g ^ i * h ^ j * (g ^ (2 * i) * h ^ (2 * j))
        = g ^ i * (h ^ j * g ^ (2 * i)) * h ^ (2 * j) := by simp only [mul_assoc]
      _ = g ^ i * (g ^ (2 * i) * h ^ j) * h ^ (2 * j) := by rw [hc.eq]
      _ = g ^ (i + 2 * i) * h ^ (j + 2 * j) := by
          rw [pow_add, pow_add]; simp only [mul_assoc]
      _ = 1 := by
          rw [show i + 2 * i = 3 * i by ring, show j + 2 * j = 3 * j by ring, pow_mul, pow_mul,
            hg3, hh3, one_pow, one_pow, one_mul]

theorem pow4_mem_list (c : List ℕ) {k : ℕ} (hk : k < 3) : pow4 c k ∈ [one4, c, sq4 c] := by
  unfold pow4
  interval_cases k <;> simp

theorem mul4_pow4_mem_e9Elems (a b : List ℕ) {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    mul4 (pow4 a i) (pow4 b j) ∈ e9Elems a b := by
  simp only [e9Elems, List.mem_toArray, List.mem_flatMap, List.mem_map]
  exact ⟨pow4 a i, pow4_mem_list a hi, pow4 b j, pow4_mem_list b hj, rfl⟩

theorem mem_e9Elems {g h : SUg} {a b : List ℕ} (ha : toMat g = dec4 a) (hb : toMat h = dec4 b)
    (hg3 : g ^ 3 = 1) (hh3 : h ^ 3 = 1) (hgh : Commute g h) {x : SUg}
    (hx : x ∈ Subgroup.closure ({g, h} : Set SUg)) : ∃ c ∈ e9Elems a b, dec4 c = toMat x := by
  obtain ⟨i, j, rfl⟩ := mem_closure_pair_pow hg3 hh3 hgh x hx
  have e1 : g ^ i = g ^ (i % 3) := pow_eq_pow_mod i hg3
  have e2 : h ^ j = h ^ (j % 3) := pow_eq_pow_mod j hh3
  have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  refine ⟨mul4 (pow4 a (i % 3)) (pow4 b (j % 3)), mul4_pow4_mem_e9Elems a b hi hj, ?_⟩
  rw [dec4_mul4, ← toMat_pow4 ha hi, ← toMat_pow4 hb hj, e1, e2, map_mul]

theorem exists_pair_aux {L : Type*} [Group L] [Finite L] {P : Subgroup L}
    (hPe : IsElemAbelian 3 P) (hP27 : Nat.card P = 27) {z : L} (hz : z ∈ P) (hz1 : z ≠ 1) :
    ∃ a ∈ P, ∃ b ∈ P, a ∉ Subgroup.zpowers z ∧ b ∉ Subgroup.closure ({z, a} : Set L) := by
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hPe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hz3 : z ^ 3 = 1 := hPe.2 z hz
  obtain ⟨a, haP, haz⟩ : ∃ a ∈ P, a ∉ Subgroup.zpowers z := by
    by_contra hall
    push Not at hall
    have h := Subgroup.card_le_of_le (show P ≤ Subgroup.zpowers z from fun x hx => hall x hx)
    rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1, hP27] at h
    omega
  have ha3 : a ^ 3 = 1 := hPe.2 a haP
  obtain ⟨b, hbP, hb⟩ : ∃ b ∈ P, b ∉ Subgroup.closure ({z, a} : Set L) := by
    by_contra hall
    push Not at hall
    have h := Subgroup.card_le_of_le
      (show P ≤ Subgroup.closure ({z, a} : Set L) from fun x hx => hall x hx)
    rw [Asc83Table.card_closure_pair_eq_nine hz3 ha3 (hPab z hz a haP) hz1 haz, hP27] at h
    omega
  exact ⟨a, haP, b, hbP, haz, hb⟩

theorem independent_swap {L : Type*} [Group L] [Finite L] {z a b : L} (hz3 : z ^ 3 = 1)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hz1 : z ≠ 1) (hza : Commute z a) (hzb : Commute z b)
    (haz : a ∉ Subgroup.zpowers z) (hb : b ∉ Subgroup.closure ({z, a} : Set L)) :
    b ∉ Subgroup.zpowers z ∧ a ∉ Subgroup.closure ({z, b} : Set L) := by
  have hzle : Subgroup.zpowers z ≤ Subgroup.closure ({z, a} : Set L) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hbz : b ∉ Subgroup.zpowers z := fun h => hb (hzle h)
  refine ⟨hbz, fun hab => hb ?_⟩
  have hle : Subgroup.closure ({z, a} : Set L) ≤ Subgroup.closure ({z, b} : Set L) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact hab
  have h1 := Asc83Table.card_closure_pair_eq_nine hz3 ha3 hza hz1 haz
  have h2 := Asc83Table.card_closure_pair_eq_nine hz3 hb3 hzb hz1 hbz
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h1, h2])
  rw [heq]
  exact Subgroup.subset_closure (by simp)

instance finiteSUg : Finite SUg := Finite.of_injective toMat toMat_injective

theorem exists_pair_lt (hsyl : uSylCheck = true) {P : Subgroup SUg} (hP : P ≤ sylS)
    (hPe : IsElemAbelian 3 P) (hP27 : Nat.card P = 27) {z : SUg} (hz : z ∈ P) (hz1 : z ≠ 1) :
    ∃ (ia ib : ℕ) (a b : SUg), ia < ib ∧ ib < 729 ∧ a = sAt ia ∧ b = sAt ib ∧ a ∈ P ∧ b ∈ P ∧
      a ∉ Subgroup.zpowers z ∧ b ∉ Subgroup.closure ({z, a} : Set SUg) := by
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hPe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨a, haP, b, hbP, haz, hb⟩ := exists_pair_aux hPe hP27 hz hz1
  obtain ⟨ia, hia, hae⟩ := exists_sAt_of_mem hsyl (hP haP)
  obtain ⟨ib, hib, hbe⟩ := exists_sAt_of_mem hsyl (hP hbP)
  rcases lt_trichotomy ia ib with h | h | h
  · exact ⟨ia, ib, a, b, h, hib, hae, hbe, haP, hbP, haz, hb⟩
  · exfalso
    have : a = b := by rw [hae, hbe, h]
    exact hb (this ▸ Subgroup.subset_closure (by simp))
  · obtain ⟨hbz, hab⟩ := independent_swap (hPe.2 z hz) (hPe.2 _ haP) (hPe.2 _ hbP) hz1
      (hPab z hz _ haP) (hPab z hz _ hbP) haz hb
    exact ⟨ib, ia, b, a, h, hia, hbe, hae, hbP, haP, hbz, hab⟩

theorem ne_one_of_code_ne (hsyl : uSylCheck = true) {t : ℕ} (ht : t < 729) (h : uAt t ≠ one4) :
    sAt t ≠ 1 := fun e => h (dec4_injective (canon4_uAt hsyl ht) canon4_one4 (by
  rw [dec4_one4, ← toMat_sAt hsyl ht, e, map_one]))

theorem uZ_spec (hsyl : uSylCheck = true) (hz : uZCheck = true) :
    uZ < 729 ∧ sAt uZ ≠ 1 ∧ sAt uZ ^ 3 = 1 ∧ ∀ s ∈ sylS, s * sAt uZ = sAt uZ * s := by
  simp only [uZCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    beq_iff_eq, List.all_eq_true, List.mem_range, ne_eq] at hz
  obtain ⟨⟨⟨hlt, hne⟩, hcu⟩, hcomm⟩ := hz
  refine ⟨hlt, ne_one_of_code_ne hsyl hlt hne, pow_three_of_cube4 hsyl hlt hcu, fun s hs => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := exists_sAt_of_mem hsyl hs
    exact commute_of_commutes4 hsyl ht hlt (hcomm t ht)

theorem isOrd3_of_elem (hsyl : uSylCheck = true) {t : ℕ} (ht : t < 729) (h1 : sAt t ≠ 1)
    (h3 : sAt t ^ 3 = 1) : isOrd3 t = true := by
  have hne : uAt t ≠ one4 := fun e =>
    h1 (toMat_injective (by rw [toMat_sAt hsyl ht, e, dec4_one4, map_one]))
  have hcu : cube4 (uAt t) = one4 := by
    apply dec4_injective (by unfold cube4; exact canon4_mul4 _ _) canon4_one4
    have h : toMat (sAt t ^ 3) = toMat 1 := by rw [h3]
    rw [map_pow, map_one, toMat_sAt hsyl ht] at h
    rw [dec4_cube4, dec4_one4, ← h, pow_three]
  simp only [isOrd3, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq]
  exact ⟨hne, hcu⟩

theorem commutes4_of_comm (hsyl : uSylCheck = true) {s t : ℕ} (hs : s < 729) (ht : t < 729)
    (h : sAt s * sAt t = sAt t * sAt s) : commutes4 (uAt s) (uAt t) = true := by
  unfold commutes4
  rw [beq_iff_eq]
  apply dec4_injective (canon4_mul4 _ _) (canon4_mul4 _ _)
  rw [dec4_mul4, dec4_mul4, ← toMat_sAt hsyl hs, ← toMat_sAt hsyl ht, ← map_mul, ← map_mul, h]

theorem isOrd3Arr_getD {t : ℕ} (ht : t < 729) : isOrd3Arr.getD t false = isOrd3 t := by
  unfold isOrd3Arr
  simp [Array.getD_eq_getD_getElem?, ht]

theorem lookup_mem {α β : Type*} [BEq α] :
    ∀ (l : List (α × β)) (a : α) (w : β), l.lookup a = some w → ∃ q, (q, w) ∈ l
  | [], a, w, h => by simp at h
  | (k, b) :: as, a, w, h => by
    rw [List.lookup_cons] at h
    cases hab : (a == k) with
    | true =>
      rw [hab] at h
      have : b = w := by simpa using h
      exact ⟨k, by simp [this]⟩
    | false =>
      rw [hab] at h
      obtain ⟨q, hq⟩ := lookup_mem as a w h
      exact ⟨q, List.mem_cons_of_mem _ hq⟩

theorem convPairArr_getD (hk : uKindCheck = true) (p : ℕ) :
    ∃ w : List ℕ, (∀ l ∈ w, l < 4) ∧ convPairArr.getD p (wordPair []) = wordPair w := by
  by_cases hp : p < 729
  · refine ⟨convRWord p, ?_, ?_⟩
    · unfold convRWord
      cases hl : uConvR.lookup p with
      | none => simp
      | some w =>
        obtain ⟨q, hq⟩ := lookup_mem _ _ _ hl
        simp only [uKindCheck, Bool.and_eq_true, List.all_eq_true] at hk
        have := hk.2 _ hq
        simpa using lt_four_of_wordOK this
    · unfold convPairArr
      simp [Array.getD_eq_getD_getElem?, hp]
  · refine ⟨[], by simp, ?_⟩
    unfold convPairArr
    simp [Array.getD_eq_getD_getElem?, hp]

theorem pairOKE_of_uPairCheck (hpair : uPairCheck = true) {ia ib : ℕ} (hia : ia < 729)
    (hib : ib < 729) (hlt : ia < ib) (h1 : isOrd3 ia = true) (h2 : isOrd3 ib = true)
    (hc : commutes4 (uAt ia) (uAt ib) = true) : pairOKE (uAt ia) (uAt ib) = true := by
  simp only [uPairCheck, List.all_eq_true, List.mem_range] at hpair
  have h := hpair ia hia
  simp only [pairRow, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h ib hib with h' | h'
  · omega
  · simp only [pairOK, Bool.or_eq_true, Bool.not_eq_true'] at h'
    rw [isOrd3Arr_getD hia, isOrd3Arr_getD hib] at h'
    rcases h' with ((h' | h') | h') | h'
    · rw [h1] at h'; exact absurd h' (by simp)
    · rw [h2] at h'; exact absurd h' (by simp)
    · rw [hc] at h'; exact absurd h' (by simp)
    · exact h'

theorem mul_self_mem_zpowers (z : SUg) : z * z ∈ Subgroup.zpowers z :=
  Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

theorem dependent_false (hsyl : uSylCheck = true) (hz : uZCheck = true) {ia ib : ℕ}
    (hia : ia < 729) (hib : ib < 729) (haz : sAt ia ∉ Subgroup.zpowers (sAt uZ))
    (hb : sAt ib ∉ Subgroup.closure ({sAt uZ, sAt ia} : Set SUg)) :
    dependent (uAt ia) (zaList (uAt ia)) (uAt ib) = false := by
  obtain ⟨hzlt, -, -, -⟩ := uZ_spec hsyl hz
  have hzH : sAt uZ ∈ Subgroup.closure ({sAt uZ, sAt ia} : Set SUg) :=
    Subgroup.subset_closure (by simp)
  have haH : sAt ia ∈ Subgroup.closure ({sAt uZ, sAt ia} : Set SUg) :=
    Subgroup.subset_closure (by simp)
  have hzc : InSub (Subgroup.closure ({sAt uZ, sAt ia} : Set SUg)) zc :=
    (inSub_uAt_iff hsyl hzlt).mpr hzH
  have hac : InSub (Subgroup.closure ({sAt uZ, sAt ia} : Set SUg)) (uAt ia) :=
    (inSub_uAt_iff hsyl hia).mpr haH
  have h1 : (uAt ia == zc) = false := by
    rw [beq_eq_false_iff_ne]
    intro e
    apply haz
    have : sAt ia = sAt uZ := toMat_injective (by
      rw [toMat_sAt hsyl hia, toMat_sAt hsyl hzlt]; exact congrArg dec4 e)
    rw [this]
    exact Subgroup.mem_zpowers _
  have h2 : (uAt ia == zc2) = false := by
    rw [beq_eq_false_iff_ne]
    intro e
    apply haz
    have : sAt ia = sAt uZ * sAt uZ := toMat_injective (by
      rw [toMat_sAt hsyl hia, map_mul, toMat_sAt hsyl hzlt, e, zc2, sq4, dec4_mul4]
      rfl)
    rw [this]
    exact mul_self_mem_zpowers _
  have h3 : (zaList (uAt ia)).contains (uAt ib) = false := by
    by_contra hcon
    have hmem : uAt ib ∈ zaList (uAt ia) := by
      simpa using hcon
    exact hb ((inSub_uAt_iff hsyl hib).mp (inSub_zaList hzc hac _ hmem))
  unfold dependent
  rw [h1, h2, h3]
  rfl

theorem pairGood_spec (hsyl : uSylCheck = true) (hrt : uRtCheck = true)
    (hk : uKindCheck = true) {H : Subgroup SUg} {els : Array (List ℕ)} (hsize : els.size = 27)
    (hall : ∀ c ∈ els, InSub H c) (h : pairGood els = true) :
    ∃ g : SUg, ∃ u ∈ H, ∃ v ∈ H, u ≠ 1 ∧ v ≠ 1 ∧ v ≠ u ∧ v ≠ u * u ∧
      g * u * g⁻¹ ∈ rtS ∧ g * v * g⁻¹ ∈ rtS := by
  unfold pairGood at h
  split at h
  · exact absurd h Bool.false_ne_true
  · rename_i x hx
    unfold pairGoodAt at h
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨u, hu27, ⟨hu1, hurt⟩, v, hv27, ⟨⟨⟨hv1, hvu⟩, hvu2⟩, hvrt⟩⟩ := h
    obtain ⟨w, hw, hgp⟩ := convPairArr_getD hk (posOf (els.getD x []))
    rw [hgp] at hurt hvrt
    have hmu : els.getD u [] ∈ els := getD_mem_array els [] (by omega)
    have hmv : els.getD v [] ∈ els := getD_mem_array els [] (by omega)
    obtain ⟨hcu, ue, hue, hue_dec⟩ := hall _ hmu
    obtain ⟨hcv, ve, hve, hve_dec⟩ := hall _ hmv
    refine ⟨wordElem w, ue, hue, ve, hve, ?_, ?_, ?_, ?_,
      conj_mem_rtS hsyl hrt hw hue_dec.symm hurt, conj_mem_rtS hsyl hrt hw hve_dec.symm hvrt⟩
    · intro e
      exact hu1 (dec4_injective hcu canon4_one4 (by rw [hue_dec, e, map_one, dec4_one4]))
    · intro e
      exact hv1 (dec4_injective hcv canon4_one4 (by rw [hve_dec, e, map_one, dec4_one4]))
    · intro e
      exact hvu (dec4_injective hcv hcu (by rw [hve_dec, hue_dec, e]))
    · intro e
      refine hvu2 (dec4_injective hcv (canon4_mul4 _ _) ?_)
      rw [hve_dec, e, map_mul, sq4, dec4_mul4, hue_dec]

theorem badOK_of_check (hbad : uBadCheck = true) {k : ℕ} (hk : k < 12) : badOK k = true := by
  simp only [uBadCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hbad
  exact hbad.2 k hk

theorem getD_lt_of_all {l : List ℕ} (h : l.all (· < 729) = true) (i : ℕ) : l.getD i 0 < 729 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some c =>
    simp only [Option.getD_some]
    have := List.all_eq_true.mp h c (List.mem_of_getElem? hi)
    simpa using this

theorem badOK_spec {k : ℕ} (h : badOK k = true) :
    (badTriple k).all (· < 729) = true ∧ (badTriple k).getD 0 0 = uZ ∧
      repIdx (badClass k) < 12 ∧ commutes4 (badA k) (badB k) = true ∧ cube4 (badA k) = one4 ∧
      cube4 (badB k) = one4 ∧ badA k ≠ one4 ∧ badB k ∉ [one4, badA k, sq4 (badA k)] ∧
      (∀ c ∈ e9Elems (badA k) (badB k), c = one4 ∨ kindOf c = 3) ∧ (∀ l ∈ badWord k, l < 4) ∧
      conjStep (wordPair (badWord k)) (badA k) = badA (repIdx (badClass k)) ∧
      conjStep (wordPair (badWord k)) (badB k) = badB (repIdx (badClass k)) ∧
      (conjStep (wordPair (badWord k)) zc = zc ∨ conjStep (wordPair (badWord k)) zc = zc2) := by
  simp only [badOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, Bool.or_eq_true, wordOK] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  refine ⟨h2, h3, h4, h5, h6, h7, h8, ?_, ?_, ?_, h12, h13, h14⟩
  · intro hmem
    have h9' : [one4, badA k, sq4 (badA k)].contains (badB k) = true := by simpa using hmem
    rw [h9] at h9'
    exact absurd h9' (by simp)
  · intro c hc
    have := Array.all_eq_true'.mp h10 c hc
    simpa using this
  · intro l hl
    simpa using List.all_eq_true.mp h11 l hl

theorem badTriple_lt (hbad : uBadCheck = true) {k : ℕ} (hk : k < 12) (i : ℕ) :
    (badTriple k).getD i 0 < 729 :=
  getD_lt_of_all (badOK_spec (badOK_of_check hbad hk)).1 i

theorem pairBad_spec (hsyl : uSylCheck = true) (hbad : uBadCheck = true) {H : Subgroup SUg}
    {els : Array (List ℕ)} (hall : ∀ c ∈ els, InSub H c) (h : pairBad els = true) :
    ∃ k < 12, sAt ((badTriple k).getD 1 0) ∈ H ∧ sAt ((badTriple k).getD 2 0) ∈ H := by
  unfold pairBad at h
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨k, hk, h1, h2⟩ := h
  refine ⟨k, hk, ?_, ?_⟩
  · exact (inSub_uAt_iff hsyl (badTriple_lt hbad hk 1)).mp
      (hall _ (by simpa [badA] using h1))
  · exact (inSub_uAt_iff hsyl (badTriple_lt hbad hk 2)).mp
      (hall _ (by simpa [badB] using h2))

theorem mul_comm_of_mem_elemAbelian {G : Type*} [Group G] {K : Subgroup G} {P : Subgroup K}
    {p : ℕ} (hPe : IsElemAbelian p P) {x y : K} (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x :=
  congrArg Subtype.val (hPe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem pair_dichotomy (hsyl : uSylCheck = true) (hcls : uClassCheck = true)
    (hpair : uPairCheck = true) (hbad : uBadCheck = true) {P : Subgroup SUg} (hP : P ≤ sylS)
    (hPe : IsElemAbelian 3 P) (hP27 : Nat.card P = 27) (hz : sAt uZ ∈ P) :
    (∃ g : SUg, ∃ u ∈ P, ∃ v ∈ P, u ≠ 1 ∧ v ≠ 1 ∧ v ≠ u ∧ v ≠ u * u ∧
      g * u * g⁻¹ ∈ rtS ∧ g * v * g⁻¹ ∈ rtS) ∨
    (∃ k < 12, sAt ((badTriple k).getD 1 0) ∈ P ∧ sAt ((badTriple k).getD 2 0) ∈ P) := by
  obtain ⟨hrt, hk, -, -, hzc⟩ := uClassCheck_parts hcls
  obtain ⟨hzlt, hz1, hz3, -⟩ := uZ_spec hsyl hzc
  obtain ⟨ia, ib, a, b, hlt, hib, hae, hbe, haP, hbP, haz, hb⟩ :=
    exists_pair_lt hsyl hP hPe hP27 hz hz1
  have hia : ia < 729 := hlt.trans hib
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_elemAbelian hPe hx hy
  subst hae hbe
  have ha1 : sAt ia ≠ 1 := fun h => haz (h ▸ Subgroup.one_mem _)
  have hb1 : sAt ib ≠ 1 := fun h => hb (h ▸ Subgroup.one_mem _)
  have hord1 : isOrd3 ia = true := isOrd3_of_elem hsyl hia ha1 (hPe.2 _ haP)
  have hord2 : isOrd3 ib = true := isOrd3_of_elem hsyl hib hb1 (hPe.2 _ hbP)
  have hcomm : commutes4 (uAt ia) (uAt ib) = true :=
    commutes4_of_comm hsyl hia hib (hPab _ haP _ hbP)
  have hOKE := pairOKE_of_uPairCheck hpair hia hib hlt hord1 hord2 hcomm
  have hdep := dependent_false hsyl hzc hia hib haz hb
  simp only [pairOKE, hdep, Bool.false_or, Bool.or_eq_true] at hOKE
  have hall : ∀ c ∈ pElemsOf (zaList (uAt ia)) (uAt ib), InSub P c :=
    inSub_pElemsOf (inSub_zaList ((inSub_uAt_iff hsyl hzlt).mpr hz)
      ((inSub_uAt_iff hsyl hia).mpr haP)) ((inSub_uAt_iff hsyl hib).mpr hbP)
  rcases hOKE with hg | hbd
  · exact Or.inl (pairGood_spec hsyl hrt hk (size_pElemsOf _ _) hall hg)
  · exact Or.inr (pairBad_spec hsyl hbad hall hbd)

end CFSG.RankThree.PartTwo.Sec4.Item434RemU43
