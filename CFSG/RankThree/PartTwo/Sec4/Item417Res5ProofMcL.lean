module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofCover
public import CFSG.Sporadic.McL.Setup
public import Certificates.Data.R3E417.McL
public import Certificates.Certificate8175
public import Certificates.Certificate8007
public import Certificates.Certificate8008
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Five

namespace McLE81

open CFSG.Sporadic.McL

local notation "M21" => Matrix (Fin 21) (Fin 21) (ZMod 3)

theorem getD_map_range {α : Type} (f : ℕ → α) (n : ℕ) (d : α) {i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem entR_mulR (a b : List (List ℕ)) {i j : ℕ} (hi : i < 21) (hj : j < 21) :
    entR (mulR a b) i j = ((List.range 21).map fun k => entR a i k * entR b k j).sum % 3 := by
  rw [entR, mulR, getD_map_range _ _ _ hi, getD_map_range _ _ _ hj]

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

theorem decR_mulR (a b : List (List ℕ)) : decR (mulR a b) = decR a * decR b := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [decR, Matrix.of_apply]
  rw [entR_mulR a b i.2 j.2, ZMod.natCast_mod, Nat.cast_list_sum, List.map_map,
    list_sum_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, Nat.cast_mul]

theorem comm_of_le_centralizer {G : Type} [Group G] {E : Subgroup G} {x : G}
    (h : E ≤ Subgroup.centralizer {x}) : ∀ a ∈ E, a * x = x * a :=
  fun _ ha => Subgroup.mem_centralizer_singleton_iff.mp (h ha)

theorem comm_zpowers_of_le_centralizer {G : Type} [Group G] {E : Subgroup G} {x : G}
    (h : E ≤ Subgroup.centralizer {x}) : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
  intro a ha b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_right (comm_of_le_centralizer h a ha) k).eq

theorem isPGroup_zpowers_of_pow_four {G : Type} [Group G] {g : G} (hg : g ^ 4 = 1) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  have hd : orderOf g ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact orderOf_dvd_of_pow_eq_one hg
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])

section Checks


theorem decR_oneR : decR oneR = 1 :=
  Certificates.certificate8175.1

theorem decode_seedA : Blueprint.NativeSporadic.decode 3 21 1 Native.seedA = decR aR :=
  Certificates.certificate8175.2.1

theorem decode_seedB : Blueprint.NativeSporadic.decode 3 21 1 Native.seedB = decR bR :=
  Certificates.certificate8175.2.2.1

theorem codes_targets : (codes ()).getD 77 oneR = xLit ∧ (codes ()).getD 85 oneR = yLit ∧
    (codes ()).getD 103 oneR = zLit ∧ (codes ()).getD 108 oneR = wLit ∧
    (codes ()).getD 87 oneR = iLit ∧ (codes ()).getD 90 oneR = jLit :=
  Certificates.certificate8175.2.2.2.1

theorem cubes : mulR (mulR xLit xLit) xLit = oneR ∧ mulR (mulR yLit yLit) yLit = oneR ∧
    mulR (mulR zLit zLit) zLit = oneR ∧ mulR (mulR wLit wLit) wLit = oneR :=
  Certificates.certificate8175.2.2.2.2.1

theorem comms : mulR yLit xLit = mulR xLit yLit ∧ mulR zLit xLit = mulR xLit zLit ∧
    mulR zLit yLit = mulR yLit zLit ∧ mulR wLit xLit = mulR xLit wLit ∧
    mulR wLit yLit = mulR yLit wLit ∧ mulR wLit zLit = mulR zLit wLit :=
  Certificates.certificate8175.2.2.2.2.2.1

theorem q8_rels : mulR (mulR (mulR iLit iLit) iLit) iLit = oneR ∧
    mulR (mulR (mulR jLit jLit) jLit) jLit = oneR ∧
    mulR jLit iLit = mulR (mulR (mulR iLit iLit) iLit) jLit :=
  Certificates.certificate8175.2.2.2.2.2.2.1

theorem x_rels : mulR xLit iLit = mulR jLit xLit ∧
    mulR xLit jLit = mulR (mulR (mulR (mulR iLit iLit) iLit) jLit) xLit :=
  Certificates.certificate8175.2.2.2.2.2.2.2.1

theorem y_rels : mulR yLit iLit = mulR iLit yLit ∧ mulR yLit jLit = mulR jLit yLit :=
  Certificates.certificate8175.2.2.2.2.2.2.2.2.1

theorem xi_entries : entR (mulR xLit iLit) 0 0 = 2 ∧ entR (mulR iLit xLit) 0 0 = 1 :=
  Certificates.certificate8175.2.2.2.2.2.2.2.2.2.1

theorem x_entry : entR xLit 0 0 = 2 :=
  Certificates.certificate8175.2.2.2.2.2.2.2.2.2.2.1

theorem fixes : mulR xLit (colR v1L) = colR v1L ∧ mulR xLit (colR v2L) = colR v2L ∧
    mulR yLit (colR v2L) = colR v2L ∧ mulR xLit (colR v3L) = colR v3L ∧
    mulR yLit (colR v3L) = colR v3L ∧ mulR zLit (colR v3L) = colR v3L :=
  Certificates.certificate8175.2.2.2.2.2.2.2.2.2.2.2.1

theorem moves :
    (entR (mulR yLit (colR v1L)) 1 0 = 1 ∧ entR (colR v1L) 1 0 = 2) ∧
    (entR (mulR zLit (colR v2L)) 0 0 = 0 ∧ entR (colR v2L) 0 0 = 2) ∧
    (entR (mulR wLit (colR v3L)) 0 0 = 1 ∧ entR (colR v3L) 0 0 = 2) :=
  Certificates.certificate8175.2.2.2.2.2.2.2.2.2.2.2.2

theorem mA_eq : mA = decR aR := by
  rw [show mA = Blueprint.NativeSporadic.decode 3 21 1 Native.seedA by rw [seedA_eq]]
  exact decode_seedA

theorem mB_eq : mB = decR bR := by
  rw [show mB = Blueprint.NativeSporadic.decode 3 21 1 Native.seedB by rw [seedB_eq]]
  exact decode_seedB

end Checks

section Elements


@[expose] noncomputable def elemsOf : List (ℕ × ℕ) → List J → List J
  | [], acc => acc
  | p :: l, acc => elemsOf l (acc ++ [acc.getD p.1 1 * acc.getD p.2 1])

@[expose, irreducible] noncomputable def elems : List J :=
  elemsOf ins [a, b]

@[expose, irreducible] noncomputable def xM : J := elems.getD 77 1

@[expose, irreducible] noncomputable def yM : J := elems.getD 85 1

@[expose, irreducible] noncomputable def zM : J := elems.getD 103 1

@[expose, irreducible] noncomputable def wM : J := elems.getD 108 1

@[expose, irreducible] noncomputable def qi : J := elems.getD 87 1

@[expose, irreducible] noncomputable def qj : J := elems.getD 90 1

theorem mat_mul_rows {g h : J} {c d : List (List ℕ)} (hg : mat g = decR c) (hh : mat h = decR d) :
    mat (g * h) = decR (mulR c d) := by
  rw [mat_mul, hg, hh, decR_mulR]

theorem mat_pow_three_rows {g : J} {c : List (List ℕ)} (hg : mat g = decR c) :
    mat (g ^ 3) = decR (mulR (mulR c c) c) := by
  rw [pow_succ, pow_two, mat_mul_rows (mat_mul_rows hg hg) hg]

theorem mul_eq_mul_of_rows {g h k l : J} {cg ch ck cl : List (List ℕ)}
    (hg : mat g = decR cg) (hh : mat h = decR ch) (hk : mat k = decR ck) (hl : mat l = decR cl)
    (e : mulR cg ch = mulR ck cl) : g * h = k * l :=
  mat_injective (by rw [mat_mul_rows hg hh, mat_mul_rows hk hl, e])

theorem ne_one_of_entry {g : J} {c : List (List ℕ)} (hg : mat g = decR c) (r s : ℕ)
    (hr : r < 21) (hs : s < 21) {α : ℕ} (hα : entR c r s = α)
    (hne : ((α : ℕ) : ZMod 3) ≠ (1 : M21) ⟨r, hr⟩ ⟨s, hs⟩) : g ≠ 1 := by
  intro h1
  apply hne
  have := congrFun (congrFun hg ⟨r, hr⟩) ⟨s, hs⟩
  rw [h1, mat_one] at this
  rw [this]
  simp only [decR, Matrix.of_apply, hα]

@[expose] noncomputable def fixM (V : List (List ℕ)) : Subgroup J where
  carrier := {g | mat g * decR V = decR V}
  one_mem' := by
    show mat 1 * decR V = decR V
    rw [mat_one, one_mul]
  mul_mem' := by
    intro g h hg hh
    have hg' : mat g * decR V = decR V := hg
    have hh' : mat h * decR V = decR V := hh
    show mat (g * h) * decR V = decR V
    rw [mat_mul, mul_assoc, hh', hg']
  inv_mem' := by
    intro g hg
    have hg' : mat g * decR V = decR V := hg
    show mat g⁻¹ * decR V = decR V
    calc mat g⁻¹ * decR V = mat g⁻¹ * (mat g * decR V) := by rw [hg']
      _ = decR V := by rw [← mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, one_mul]

theorem mem_fixM {g : J} {c V : List (List ℕ)} (hg : mat g = decR c) (e : mulR c V = V) :
    g ∈ fixM V := by
  show mat g * decR V = decR V
  rw [hg, ← decR_mulR, e]

theorem not_mem_fixM {g : J} {c V : List (List ℕ)} (hg : mat g = decR c) (r : ℕ) (hr : r < 21)
    {α β : ℕ} (hα : entR (mulR c V) r 0 = α) (hβ : entR V r 0 = β)
    (hne : ((α : ℕ) : ZMod 3) ≠ ((β : ℕ) : ZMod 3)) : g ∉ fixM V := by
  intro hm
  have hm' : mat g * decR V = decR V := hm
  rw [hg, ← decR_mulR] at hm'
  have := congrFun (congrFun hm' ⟨r, hr⟩) 0
  simp only [decR, Matrix.of_apply, Fin.val_zero, hα, hβ] at this
  exact hne this

@[expose] noncomputable def e9 : Subgroup J :=
  Subgroup.zpowers xM ⊔ Subgroup.zpowers yM

@[expose] noncomputable def e27 : Subgroup J :=
  e9 ⊔ Subgroup.zpowers zM

@[expose] noncomputable def e81 : Subgroup J :=
  e27 ⊔ Subgroup.zpowers wM

@[expose] noncomputable def q8 : Subgroup J :=
  Subgroup.zpowers qj ⊔ Subgroup.zpowers qi

theorem e9_le_e81 : e9 ≤ e81 :=
  (le_sup_left : e9 ≤ e27).trans le_sup_left

theorem conj_mem_q8 {g : J} (hj : g * qj * g⁻¹ ∈ q8) (hi : g * qi * g⁻¹ ∈ q8) :
    ∀ n ∈ q8, g * n * g⁻¹ ∈ q8 := by
  intro n hn
  rw [q8, Subgroup.sup_eq_closure] at hn
  induction hn using Subgroup.closure_induction with
  | mem n hn =>
    rcases hn with hn | hn
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ hj k
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ hi k
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  | mul n m _ _ ihn ihm =>
    have h : g * (n * m) * g⁻¹ = g * n * g⁻¹ * (g * m * g⁻¹) := by group
    rw [h]
    exact Subgroup.mul_mem _ ihn ihm
  | inv n _ ihn =>
    have h : g * n⁻¹ * g⁻¹ = (g * n * g⁻¹)⁻¹ := by group
    rw [h]
    exact Subgroup.inv_mem _ ihn

end Elements

section Relations


theorem mat_elemsOf : ∀ (l : List (ℕ × ℕ)) (acc : List J) (accC : List (List (List ℕ))),
    acc.length = accC.length → (∀ k, mat (acc.getD k 1) = decR (accC.getD k oneR)) →
    ∀ k, mat ((elemsOf l acc).getD k 1) = decR ((codesOf l accC).getD k oneR)
  | [], _, _, _, h => h
  | p :: l, acc, accC, hlen, h => by
    refine mat_elemsOf l _ _ (by simp [hlen]) fun k => ?_
    rcases lt_or_ge k acc.length with hk | hk
    · rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ (hlen ▸ hk), h k]
    · rw [List.getD_append_right _ _ _ _ hk, List.getD_append_right _ _ _ _ (hlen ▸ hk), ← hlen]
      rcases Nat.eq_zero_or_pos (k - acc.length) with h0 | h0
      · rw [h0, List.getD_cons_zero, List.getD_cons_zero, mat_mul, h, h, decR_mulR]
      · obtain ⟨m, hm⟩ : ∃ m, k - acc.length = m + 1 := ⟨k - acc.length - 1, by omega⟩
        simp only [hm, List.getD_cons_succ, List.getD_nil, mat_one, decR_oneR]

theorem mat_elems (k : ℕ) : mat (elems.getD k 1) = decR ((codes ()).getD k oneR) := by
  unfold elems codes
  refine mat_elemsOf ins [a, b] [aR, bR] rfl (fun k => ?_) k
  match k with
  | 0 => exact a_val.trans mA_eq
  | 1 => exact b_val.trans mB_eq
  | k + 2 =>
    simp only [List.getD_cons_succ, List.getD_nil, mat_one, decR_oneR]

theorem mat_x : mat xM = decR xLit := by unfold xM; rw [mat_elems, codes_targets.1]

theorem mat_y : mat yM = decR yLit := by unfold yM; rw [mat_elems, codes_targets.2.1]

theorem mat_z : mat zM = decR zLit := by unfold zM; rw [mat_elems, codes_targets.2.2.1]

theorem mat_w : mat wM = decR wLit := by unfold wM; rw [mat_elems, codes_targets.2.2.2.1]

theorem mat_i : mat qi = decR iLit := by unfold qi; rw [mat_elems, codes_targets.2.2.2.2.1]

theorem mat_j : mat qj = decR jLit := by unfold qj; rw [mat_elems, codes_targets.2.2.2.2.2]

theorem pow_three_of_rows {g : J} {c : List (List ℕ)} (hg : mat g = decR c)
    (e : mulR (mulR c c) c = oneR) : g ^ 3 = 1 :=
  mat_injective (by rw [mat_pow_three_rows hg, e, decR_oneR, mat_one])

theorem pow_four_of_rows {g : J} {c : List (List ℕ)} (hg : mat g = decR c)
    (e : mulR (mulR (mulR c c) c) c = oneR) : g ^ 4 = 1 :=
  mat_injective (by rw [pow_succ, mat_mul_rows (mat_pow_three_rows hg) hg, e, decR_oneR, mat_one])

theorem y_not_mem : yM ∉ Subgroup.zpowers xM := fun h =>
  not_mem_fixM mat_y 1 (by norm_num) moves.1.1 moves.1.2 (by decide)
    (Subgroup.zpowers_le.mpr (mem_fixM mat_x fixes.1) h)

theorem z_not_mem : zM ∉ e9 := fun h =>
  not_mem_fixM mat_z 0 (by norm_num) moves.2.1.1 moves.2.1.2 (by decide)
    (sup_le (Subgroup.zpowers_le.mpr (mem_fixM mat_x fixes.2.1))
      (Subgroup.zpowers_le.mpr (mem_fixM mat_y fixes.2.2.1)) h)

theorem w_not_mem : wM ∉ e27 := fun h =>
  not_mem_fixM mat_w 0 (by norm_num) moves.2.2.1 moves.2.2.2 (by decide)
    (sup_le (sup_le (Subgroup.zpowers_le.mpr (mem_fixM mat_x fixes.2.2.2.1))
      (Subgroup.zpowers_le.mpr (mem_fixM mat_y fixes.2.2.2.2.1)))
      (Subgroup.zpowers_le.mpr (mem_fixM mat_z fixes.2.2.2.2.2)) h)

theorem orderOf_x : orderOf xM = 3 :=
  orderOf_eq_prime (pow_three_of_rows mat_x cubes.1)
    (ne_one_of_entry mat_x 0 0 (by norm_num) (by norm_num) x_entry (by decide))

theorem orderOf_y : orderOf yM = 3 :=
  orderOf_eq_prime (pow_three_of_rows mat_y cubes.2.1) fun h =>
    y_not_mem (h ▸ Subgroup.one_mem _)

theorem orderOf_z : orderOf zM = 3 :=
  orderOf_eq_prime (pow_three_of_rows mat_z cubes.2.2.1) fun h =>
    z_not_mem (h ▸ Subgroup.one_mem _)

theorem orderOf_w : orderOf wM = 3 :=
  orderOf_eq_prime (pow_three_of_rows mat_w cubes.2.2.2) fun h =>
    w_not_mem (h ▸ Subgroup.one_mem _)

theorem zpowers_x_le : Subgroup.zpowers xM ≤ Subgroup.centralizer {yM} :=
  Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
    (mul_eq_mul_of_rows mat_x mat_y mat_y mat_x comms.1.symm))

theorem e9_le : e9 ≤ Subgroup.centralizer {zM} :=
  sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_eq_mul_of_rows mat_x mat_z mat_z mat_x comms.2.1.symm)))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_eq_mul_of_rows mat_y mat_z mat_z mat_y comms.2.2.1.symm)))

theorem e27_le : e27 ≤ Subgroup.centralizer {wM} :=
  sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_eq_mul_of_rows mat_x mat_w mat_w mat_x comms.2.2.2.1.symm)))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_eq_mul_of_rows mat_y mat_w mat_w mat_y comms.2.2.2.2.1.symm))))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_eq_mul_of_rows mat_z mat_w mat_w mat_z comms.2.2.2.2.2.symm)))

theorem card_e9 : Nat.card e9 = 9 := by
  rw [e9, card_sup_zpowers_eq_three_mul orderOf_y y_not_mem
      (comm_zpowers_of_le_centralizer zpowers_x_le), Nat.card_zpowers, orderOf_x]

theorem card_e81 : Nat.card e81 = 3 ^ 4 := by
  rw [e81, card_sup_zpowers_eq_three_mul orderOf_w w_not_mem
      (comm_zpowers_of_le_centralizer e27_le), e27,
    card_sup_zpowers_eq_three_mul orderOf_z z_not_mem (comm_zpowers_of_le_centralizer e9_le),
    card_e9]
  norm_num

theorem isElemAbelian_e81 : CFSG.Assembly.IsElemAbelian 3 e81 := by
  have h1 : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers xM) := by
    rw [Subgroup.zpowers_eq_closure]
    refine isElemAbelian_closure_of_commute ?_ ?_
    · intro x hx y hy
      rw [Set.mem_singleton_iff] at hx hy
      rw [hx, hy]
      exact Commute.refl _
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact pow_three_of_rows mat_x cubes.1
  have h2 : CFSG.Assembly.IsElemAbelian 3 e9 :=
    isElemAbelian_sup_zpowers_cube h1 (pow_three_of_rows mat_y cubes.2.1)
      (comm_of_le_centralizer zpowers_x_le)
  have h3 : CFSG.Assembly.IsElemAbelian 3 e27 :=
    isElemAbelian_sup_zpowers_cube h2 (pow_three_of_rows mat_z cubes.2.2.1)
      (comm_of_le_centralizer e9_le)
  exact isElemAbelian_sup_zpowers_cube h3 (pow_three_of_rows mat_w cubes.2.2.2)
    (comm_of_le_centralizer e27_le)

theorem qj_qi : qj * qi = qi ^ 3 * qj :=
  mat_injective (by rw [mat_mul_rows mat_j mat_i, mat_mul_rows (mat_pow_three_rows mat_i) mat_j,
    q8_rels.2.2])

theorem x_qi : xM * qi = qj * xM :=
  mul_eq_mul_of_rows mat_x mat_i mat_j mat_x x_rels.1

theorem x_qj : xM * qj = qi ^ 3 * qj * xM :=
  mul_eq_mul_of_rows mat_x mat_j (mat_mul_rows (mat_pow_three_rows mat_i) mat_j) mat_x x_rels.2

theorem x_qi_ne : xM * qi ≠ qi * xM := by
  intro h
  have h1 := congrArg mat h
  rw [mat_mul_rows mat_x mat_i, mat_mul_rows mat_i mat_x] at h1
  have h2 := congrFun (congrFun h1 0) 0
  simp only [decR, Matrix.of_apply] at h2
  rw [show ((0 : Fin 21) : ℕ) = 0 from rfl, xi_entries.1, xi_entries.2] at h2
  exact absurd h2 (by decide)

theorem isPGroup_q8 : IsPGroup 2 q8 := by
  refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_four
    (pow_four_of_rows mat_j q8_rels.2.1)) (isPGroup_zpowers_of_pow_four
    (pow_four_of_rows mat_i q8_rels.1)) (Subgroup.zpowers_le.mpr ?_)
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have h : qj * qi * qj⁻¹ = qi ^ 3 := by rw [qj_qi, mul_inv_cancel_right]
  rw [← conj_zpow, h]
  exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers qi) 3) k

theorem x_mem_normalizer : xM ∈ Subgroup.normalizer (q8 : Set J) := by
  have hi : qi ∈ q8 := Subgroup.mem_sup_right (Subgroup.mem_zpowers qi)
  have hj : qj ∈ q8 := Subgroup.mem_sup_left (Subgroup.mem_zpowers qj)
  have h1 : xM * qj * xM⁻¹ ∈ q8 := by
    rw [x_qj, mul_inv_cancel_right]
    exact q8.mul_mem (q8.pow_mem hi 3) hj
  have h2 : xM * qi * xM⁻¹ ∈ q8 := by
    rw [x_qi, mul_inv_cancel_right]
    exact hj
  exact Subgroup.mem_normalizer_fintype fun n hn => conj_mem_q8 h1 h2 n hn

theorem y_mem_normalizer : yM ∈ Subgroup.normalizer (q8 : Set J) := by
  have hle : q8 ≤ Subgroup.centralizer {yM} :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_eq_mul_of_rows mat_y mat_j mat_j mat_y y_rels.2).symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        (mul_eq_mul_of_rows mat_y mat_i mat_i mat_y y_rels.1).symm))
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have h : n * yM = yM * n := (Subgroup.mem_centralizer_singleton_iff (G := J)).mp (hle hn)
  rw [← h, mul_inv_cancel_right]
  exact hn

theorem e81_data_J : ∃ P E₀ T₀ : Subgroup J, CFSG.Assembly.IsElemAbelian 3 P ∧
    Nat.card P = 3 ^ 4 ∧ E₀ ≤ P ∧ Nat.card E₀ = 9 ∧ IsPGroup 2 T₀ ∧
    E₀ ≤ Subgroup.normalizer (T₀ : Set J) ∧ ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set J) := by
  refine ⟨e81, e9, q8, isElemAbelian_e81, card_e81, e9_le_e81, card_e9, isPGroup_q8,
    sup_le (Subgroup.zpowers_le.mpr x_mem_normalizer)
      (Subgroup.zpowers_le.mpr y_mem_normalizer), fun h => x_qi_ne ?_⟩
  exact Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers qi)))
    xM (Subgroup.mem_sup_left (Subgroup.mem_zpowers xM))

end Relations

end McLE81

theorem k417E81McL_holds :
    K417E81McL := by
  obtain ⟨P, E₀, T₀, h1, h2, h3, h4, h5, h6, h7⟩ := McLE81.e81_data_J
  exact ⟨_, _, _, e81_data_map (CFSG.Sporadic.McL.mclEquivJ.symm :
    CFSG.Sporadic.McL.J →* Blueprint.NativeSporadic.McL) CFSG.Sporadic.McL.mclEquivJ.symm.injective
    h1 h2 h3 h4 h5 h6 h7⟩

end CFSG.RankThree.PartTwo.Sec4.Res417Five
