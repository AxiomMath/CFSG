module

public import CFSG.RankThree.PartTwo.Sec21.FF84S47
public import CFSG.RankThree.PartTwo.Sec21.FF84S34Dec
public import TauCeti.GroupTheory.Perm.Inversion

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

@[expose] def p128 (a : List (Fin 8)) : List (Fin 8) := sqT^[7] a

theorem tab_pow_two_pow (x : P8) (n : ℕ) : tab (x ^ 2 ^ n) = sqT^[n] (tab x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    rw [h, pow_mul, sq, tab_mul, ih, Function.iterate_succ_apply']
    rfl

theorem tab_pow128 (x : P8) : tab (x ^ 128) = p128 (tab x) := by
  have h := tab_pow_two_pow x 7
  rw [show (2 : ℕ) ^ 7 = 128 by norm_num] at h
  exact h

@[expose] def invTabCount (l : List (Fin 8)) : ℕ :=
  ((List.finRange 8).map fun i => ((List.finRange 8).map fun j =>
    if i < j ∧ l.getD j.val 0 < l.getD i.val 0 then 1 else 0).sum).sum

theorem invTabCount_even_of_sign (σ : P8) (h : sign σ = 1) : invTabCount (tab σ) % 2 = 0 := by
  rw [TauCeti.sign_eq_neg_one_pow_card_inversion] at h
  have hc : (Finset.univ.filter fun p : Fin 8 × Fin 8 => p.1 < p.2 ∧ σ p.2 < σ p.1).card =
      invTabCount (tab σ) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp only [invTabCount, Fin.sum_univ_def, tab_getD]
  rw [hc] at h
  rcases Nat.even_or_odd (invTabCount (tab σ)) with he | ho
  · exact Nat.even_iff.1 he
  · exfalso
    rw [ho.neg_one_pow] at h
    exact absurd h (by decide)

theorem pow128_of_mem {V : Subgroup P8} (hV : IsPGroup 2 V) {x : P8} (hx : x ∈ V) :
    x ^ 128 = 1 := by
  obtain ⟨n, hn⟩ := hV ⟨x, hx⟩
  have h1 : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h2 : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have h3 : orderOf x ∣ 40320 := by
    have h := orderOf_dvd_card (x := x)
    have h8 : Nat.factorial 8 = 40320 := by decide
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, h8] using h
  have hk7 : k ≤ 7 := by
    by_contra hlt
    rw [not_le] at hlt
    have : 2 ^ 8 ∣ 40320 := (pow_dvd_pow 2 hlt).trans (hk' ▸ h3)
    norm_num at this
  have : orderOf x ∣ 2 ^ 7 := hk' ▸ (pow_dvd_pow 2 hk7)
  exact orderOf_dvd_iff_pow_eq_one.1 this

@[expose] def Qchk (UT : List (List (Fin 8))) (cT ciT : List (Fin 8)) (l : List (Fin 8)) : Prop :=
  l ∉ UT → p128 l = tab 1 → invTabCount l % 2 = 0 →
    p128 (comp l (comp ciT (comp l cT))) ≠ tab 1

instance (UT : List (List (Fin 8))) (cT ciT l) : Decidable (Qchk UT cT ciT l) := by
  unfold Qchk; infer_instance

@[expose] def swp2 (a b c d : Fin 8) : List (Fin 8) :=
  List.ofFn fun i : Fin 8 =>
    let j := if i = c then d else if i = d then c else i
    if j = a then b else if j = b then a else j

theorem tab_swp2 (a b c d : Fin 8) : tab (swap a b * swap c d) = swp2 a b c d := by
  unfold tab swp2
  congr 1

theorem conj_swap2 (σ : P8) (a b c d : Fin 8) :
    σ * (swap a b * swap c d) * σ⁻¹ = swap (σ a) (σ b) * swap (σ c) (σ d) := by
  rw [Equiv.swap_apply_apply σ a b, Equiv.swap_apply_apply σ c d]
  group

@[expose] def ChkA (UT : List (List (Fin 8))) (cT ciT : List (Fin 8)) : Prop :=
  ∀ a3 : Fin 8, ∀ a4 : Fin 8, a4 ≠ a3 → ∀ a5 : Fin 8, a5 ≠ a3 → a5 ≠ a4 →
  ∀ a6 : Fin 8, a6 ≠ a3 → a6 ≠ a4 → a6 ≠ a5 →
  swp2 a3 a4 a5 a6 ∈ UT → swp2 a3 a5 a4 a6 ∈ UT →
  ∀ a0 : Fin 8, a0 ≠ a3 → a0 ≠ a4 → a0 ≠ a5 → a0 ≠ a6 →
  ∀ a1 : Fin 8, a1 ≠ a0 → a1 ≠ a3 → a1 ≠ a4 → a1 ≠ a5 → a1 ≠ a6 →
  ∀ a2 : Fin 8, a2 ≠ a0 → a2 ≠ a1 → a2 ≠ a3 → a2 ≠ a4 → a2 ≠ a5 → a2 ≠ a6 →
  ∀ a7 : Fin 8, a7 ≠ a0 → a7 ≠ a1 → a7 ≠ a2 → a7 ≠ a3 → a7 ≠ a4 → a7 ≠ a5 → a7 ≠ a6 →
    Qchk UT cT ciT [a0, a1, a2, a3, a4, a5, a6, a7]

@[expose] def ChkB (UT : List (List (Fin 8))) (cT ciT : List (Fin 8)) : Prop :=
  ∀ a3 : Fin 8, ∀ a4 : Fin 8, a4 ≠ a3 → ∀ a5 : Fin 8, a5 ≠ a3 → a5 ≠ a4 →
  ∀ a7 : Fin 8, a7 ≠ a3 → a7 ≠ a4 → a7 ≠ a5 →
  swp2 a3 a4 a5 a7 ∈ UT → swp2 a3 a5 a4 a7 ∈ UT →
  ∀ a0 : Fin 8, a0 ≠ a3 → a0 ≠ a4 → a0 ≠ a5 → a0 ≠ a7 →
  ∀ a1 : Fin 8, a1 ≠ a0 → a1 ≠ a3 → a1 ≠ a4 → a1 ≠ a5 → a1 ≠ a7 →
  ∀ a2 : Fin 8, a2 ≠ a0 → a2 ≠ a1 → a2 ≠ a3 → a2 ≠ a4 → a2 ≠ a5 → a2 ≠ a7 →
  ∀ a6 : Fin 8, a6 ≠ a0 → a6 ≠ a1 → a6 ≠ a2 → a6 ≠ a3 → a6 ≠ a4 → a6 ≠ a5 → a6 ≠ a7 →
    Qchk UT cT ciT [a0, a1, a2, a3, a4, a5, a6, a7]

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
instance (UT : List (List (Fin 8))) (cT ciT : List (Fin 8)) : Decidable (ChkA UT cT ciT) := by
  unfold ChkA; infer_instance

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
instance (UT : List (List (Fin 8))) (cT ciT : List (Fin 8)) : Decidable (ChkB UT cT ciT) := by
  unfold ChkB; infer_instance

theorem tab_eq_list (σ : P8) : tab σ = [σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, σ 6, σ 7] := by
  simp [tab, List.ofFn_succ]

theorem chkA_qchk {UT : List (List (Fin 8))} {cT ciT : List (Fin 8)} (h : ChkA UT cT ciT)
    (σ : P8) (m1 : swp2 (σ 3) (σ 4) (σ 5) (σ 6) ∈ UT) (m2 : swp2 (σ 3) (σ 5) (σ 4) (σ 6) ∈ UT) :
    Qchk UT cT ciT (tab σ) := by
  have hne : ∀ i j : Fin 8, i ≠ j → σ i ≠ σ j := fun i j hij e => hij (σ.injective e)
  rw [tab_eq_list]
  exact h (σ 3) (σ 4) (hne _ _ (by decide)) (σ 5) (hne _ _ (by decide)) (hne _ _ (by decide))
    (σ 6) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) m1 m2
    (σ 0) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
    (σ 1) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide))
    (σ 2) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)) (hne _ _ (by decide))
    (σ 7) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))

theorem chkB_qchk {UT : List (List (Fin 8))} {cT ciT : List (Fin 8)} (h : ChkB UT cT ciT)
    (σ : P8) (m1 : swp2 (σ 3) (σ 4) (σ 5) (σ 7) ∈ UT) (m2 : swp2 (σ 3) (σ 5) (σ 4) (σ 7) ∈ UT) :
    Qchk UT cT ciT (tab σ) := by
  have hne : ∀ i j : Fin 8, i ≠ j → σ i ≠ σ j := fun i j hij e => hij (σ.injective e)
  rw [tab_eq_list]
  exact h (σ 3) (σ 4) (hne _ _ (by decide)) (σ 5) (hne _ _ (by decide)) (hne _ _ (by decide))
    (σ 7) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) m1 m2
    (σ 0) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
    (σ 1) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide))
    (σ 2) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)) (hne _ _ (by decide))
    (σ 6) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))
      (hne _ _ (by decide)) (hne _ _ (by decide)) (hne _ _ (by decide))

@[expose] def UaT : List (List (Fin 8)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7],
   [2, 7, 0, 3, 4, 5, 6, 1],
   [1, 0, 7, 3, 4, 5, 6, 2],
   [7, 2, 1, 3, 4, 5, 6, 0],
   [0, 1, 2, 5, 6, 3, 4, 7],
   [2, 7, 0, 5, 6, 3, 4, 1],
   [1, 0, 7, 5, 6, 3, 4, 2],
   [7, 2, 1, 5, 6, 3, 4, 0],
   [0, 1, 2, 4, 3, 6, 5, 7],
   [2, 7, 0, 4, 3, 6, 5, 1],
   [1, 0, 7, 4, 3, 6, 5, 2],
   [7, 2, 1, 4, 3, 6, 5, 0],
   [0, 1, 2, 6, 5, 4, 3, 7],
   [2, 7, 0, 6, 5, 4, 3, 1],
   [1, 0, 7, 6, 5, 4, 3, 2],
   [7, 2, 1, 6, 5, 4, 3, 0]]

@[expose] def UbT : List (List (Fin 8)) :=
  [[0, 1, 2, 3, 4, 5, 6, 7],
   [2, 6, 0, 3, 4, 5, 1, 7],
   [1, 0, 6, 3, 4, 5, 2, 7],
   [6, 2, 1, 3, 4, 5, 0, 7],
   [0, 1, 2, 5, 7, 3, 6, 4],
   [2, 6, 0, 5, 7, 3, 1, 4],
   [1, 0, 6, 5, 7, 3, 2, 4],
   [6, 2, 1, 5, 7, 3, 0, 4],
   [0, 1, 2, 4, 3, 7, 6, 5],
   [2, 6, 0, 4, 3, 7, 1, 5],
   [1, 0, 6, 4, 3, 7, 2, 5],
   [6, 2, 1, 4, 3, 7, 0, 5],
   [0, 1, 2, 7, 5, 4, 6, 3],
   [2, 6, 0, 7, 5, 4, 1, 3],
   [1, 0, 6, 7, 5, 4, 2, 3],
   [6, 2, 1, 7, 5, 4, 0, 3]]

@[expose] def ccT : List (Fin 8) := [1, 2, 0, 3, 4, 5, 6, 7]
@[expose] def ccIT : List (Fin 8) := [2, 0, 1, 3, 4, 5, 6, 7]
@[expose] def ddT : List (Fin 8) := [0, 1, 2, 4, 5, 3, 6, 7]
@[expose] def ddIT : List (Fin 8) := [0, 1, 2, 5, 3, 4, 6, 7]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem chk_Ua_cc : ChkA UaT ccT ccIT := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem chk_Ua_dd : ChkA UaT ddT ddIT := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem chk_Ub_cc : ChkB UbT ccT ccIT := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem chk_Ub_dd : ChkB UbT ddT ddIT := by decide +kernel

set_option maxRecDepth 100000 in
theorem tab_cc : tab cc = ccT := by decide +kernel
set_option maxRecDepth 100000 in
theorem tab_cc_inv : tab cc⁻¹ = ccIT := by decide +kernel
set_option maxRecDepth 100000 in
theorem tab_dd : tab dd = ddT := by decide +kernel
set_option maxRecDepth 100000 in
theorem tab_dd_inv : tab dd⁻¹ = ddIT := by decide +kernel

set_option maxRecDepth 100000 in
theorem UaT_of : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tab (tup4 pa pb pc pd t) ∈ UaT := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem UaT_to : ∀ g ∈ UaT, ∃ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tab (tup4 pa pb pc pd t) = g := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem UbT_of : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tab (tup4 qa qb qc qd t) ∈ UbT := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem UbT_to : ∀ g ∈ UbT, ∃ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, tab (tup4 qa qb qc qd t) = g := by
  decide +kernel

@[expose] def Key (U : Subgroup P8) (c : P8) : Prop :=
  ∀ σ : P8, (∀ g ∈ U, σ * g * σ⁻¹ ∈ U) → σ ∉ U → σ ^ 128 = 1 → sign σ = 1 →
    (σ * (c⁻¹ * σ * c)) ^ 128 ≠ 1

theorem qchk_apply {U : Subgroup P8} {c : P8} {UT : List (List (Fin 8))}
    {cT ciT : List (Fin 8)} (hU2 : ∀ g ∈ UT, ∃ x ∈ U, tab x = g)
    (hcT : tab c = cT) (hciT : tab c⁻¹ = ciT) {σ : P8}
    (hnot : σ ∉ U) (h128 : σ ^ 128 = 1) (hsign : sign σ = 1)
    (hq : Qchk UT cT ciT (tab σ)) : (σ * (c⁻¹ * σ * c)) ^ 128 ≠ 1 := by
  have hnotin : tab σ ∉ UT := by
    intro h
    obtain ⟨y, hy, hyt⟩ := hU2 _ h
    exact hnot (tab_inj hyt.symm ▸ hy)
  have hp : p128 (tab σ) = tab 1 := by
    rw [← tab_pow128, h128]
  refine fun hw => hq hnotin hp (invTabCount_even_of_sign σ hsign) ?_
  rw [← hcT, ← hciT, ← tab_mul, ← tab_mul, ← tab_mul]
  have e : σ * (c⁻¹ * (σ * c)) = σ * (c⁻¹ * σ * c) := by group
  rw [e, ← tab_pow128, hw]

theorem swp2_mem_of_norm {U : Subgroup P8} {UT : List (List (Fin 8))}
    (hU1 : ∀ x ∈ U, tab x ∈ UT) {σ : P8} (hN : ∀ g ∈ U, σ * g * σ⁻¹ ∈ U) {w x y z : Fin 8}
    (hg : swap w x * swap y z ∈ U) : swp2 (σ w) (σ x) (σ y) (σ z) ∈ UT := by
  have h := hU1 _ (hN _ hg)
  rwa [conj_swap2, tab_swp2] at h

theorem piStar_of_key {U : Subgroup P8} {c : P8} (hkey : Key U c)
    (hle : U ≤ A8s) (hpg : IsPGroup 2 U) (hnorm : c ∈ Nor U) :
    U ∈ PiStar A8s (Subgroup.zpowers c) 2 := by
  refine ⟨hle, hpg, (Subgroup.zpowers_le).2 hnorm, ?_⟩
  intro V hUV hVA hV2 hVN
  have hcV : c ∈ Nor V := (Subgroup.zpowers_le).1 hVN
  by_contra hne
  have hlt : U < V := lt_of_le_of_ne hUV (Ne.symm hne)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥V := hV2.isNilpotent
  have hH : U.subgroupOf V < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply ne_of_lt hlt
    apply le_antisymm hUV
    intro v hv
    have : (⟨v, hv⟩ : V) ∈ U.subgroupOf V := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨x, hxN, hxH⟩ := SetLike.exists_of_lt (normalizerCondition_of_isNilpotent _ hH)
  set σ : P8 := (x : P8) with hσ
  have hσV : σ ∈ V := x.2
  have hσU : σ ∉ U := hxH
  have hσN : ∀ g ∈ U, σ * g * σ⁻¹ ∈ U := by
    intro g hg
    have hgV : g ∈ V := hUV hg
    have h1 : (⟨g, hgV⟩ : V) ∈ U.subgroupOf V := hg
    exact (Subgroup.mem_normalizer_iff.1 hxN _).1 h1
  have hσ128 : σ ^ 128 = 1 := pow128_of_mem hV2 hσV
  have hσeven : sign σ = 1 := mem_alternatingGroup.1 (hVA hσV)
  have hwV : σ * (c⁻¹ * σ * c) ∈ V := by
    refine mul_mem hσV ?_
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hcV) σ).1 hσV
    simpa using this
  exact hkey σ hσN hσU hσ128 hσeven (pow128_of_mem hV2 hwV)

theorem mem_nor_of {U : Subgroup P8} {c : P8} (h1 : ∀ x ∈ U, c * x * c⁻¹ ∈ U)
    (h2 : ∀ x ∈ U, c⁻¹ * x * c ∈ U) : c ∈ Nor U := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun h => ?_⟩
  have := h2 _ h
  simpa [mul_assoc] using this

set_option maxRecDepth 100000 in
theorem Ua_conj : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    (∃ s, cc * tup4 pa pb pc pd t * cc⁻¹ = tup4 pa pb pc pd s) ∧
    (∃ s, cc⁻¹ * tup4 pa pb pc pd t * cc = tup4 pa pb pc pd s) ∧
    (∃ s, dd * tup4 pa pb pc pd t * dd⁻¹ = tup4 pa pb pc pd s) ∧
    (∃ s, dd⁻¹ * tup4 pa pb pc pd t * dd = tup4 pa pb pc pd s) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem Ub_conj : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    (∃ s, cc * tup4 qa qb qc qd t * cc⁻¹ = tup4 qa qb qc qd s) ∧
    (∃ s, cc⁻¹ * tup4 qa qb qc qd t * cc = tup4 qa qb qc qd s) ∧
    (∃ s, dd * tup4 qa qb qc qd t * dd⁻¹ = tup4 qa qb qc qd s) ∧
    (∃ s, dd⁻¹ * tup4 qa qb qc qd t * dd = tup4 qa qb qc qd s) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem Ua_sign : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, sign (tup4 pa pb pc pd t) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem Ub_sign : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2, sign (tup4 qa qb qc qd t) = 1 := by
  decide +kernel

private theorem Ua_le_A8 : Ua ≤ A8s := fun x hx => by
  obtain ⟨t, rfl⟩ := (mem_Ua_iff x).1 hx
  exact mem_alternatingGroup.2 (Ua_sign t)

private theorem Ub_le_A8 : Ub ≤ A8s := fun x hx => by
  obtain ⟨t, rfl⟩ := (mem_Ub_iff x).1 hx
  exact mem_alternatingGroup.2 (Ub_sign t)

theorem Ua_pgroup : IsPGroup 2 Ua := IsPGroup.of_card (n := 4) (by rw [Ua_card]; norm_num)

theorem Ub_pgroup : IsPGroup 2 Ub := IsPGroup.of_card (n := 4) (by rw [Ub_card]; norm_num)

private theorem Ua_nor (c : P8) (h : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    (∃ s, c * tup4 pa pb pc pd t * c⁻¹ = tup4 pa pb pc pd s) ∧
    (∃ s, c⁻¹ * tup4 pa pb pc pd t * c = tup4 pa pb pc pd s)) : c ∈ Nor Ua := by
  refine mem_nor_of (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨t, rfl⟩ := (mem_Ua_iff x).1 hx
    obtain ⟨s, hs⟩ := (h t).1
    exact hs ▸ (mem_Ua_iff _).2 ⟨s, rfl⟩
  · obtain ⟨t, rfl⟩ := (mem_Ua_iff x).1 hx
    obtain ⟨s, hs⟩ := (h t).2
    exact hs ▸ (mem_Ua_iff _).2 ⟨s, rfl⟩

private theorem Ub_nor (c : P8) (h : ∀ t : Fin 2 × Fin 2 × Fin 2 × Fin 2,
    (∃ s, c * tup4 qa qb qc qd t * c⁻¹ = tup4 qa qb qc qd s) ∧
    (∃ s, c⁻¹ * tup4 qa qb qc qd t * c = tup4 qa qb qc qd s)) : c ∈ Nor Ub := by
  refine mem_nor_of (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨t, rfl⟩ := (mem_Ub_iff x).1 hx
    obtain ⟨s, hs⟩ := (h t).1
    exact hs ▸ (mem_Ub_iff _).2 ⟨s, rfl⟩
  · obtain ⟨t, rfl⟩ := (mem_Ub_iff x).1 hx
    obtain ⟨s, hs⟩ := (h t).2
    exact hs ▸ (mem_Ub_iff _).2 ⟨s, rfl⟩

theorem UaT_mem (x : P8) (hx : x ∈ Ua) : tab x ∈ UaT := by
  obtain ⟨t, rfl⟩ := (mem_Ua_iff x).1 hx
  exact UaT_of t

theorem UaT_pre (g : List (Fin 8)) (hg : g ∈ UaT) : ∃ x ∈ Ua, tab x = g := by
  obtain ⟨t, ht⟩ := UaT_to g hg
  exact ⟨_, (mem_Ua_iff _).2 ⟨t, rfl⟩, ht⟩

theorem UbT_mem (x : P8) (hx : x ∈ Ub) : tab x ∈ UbT := by
  obtain ⟨t, rfl⟩ := (mem_Ub_iff x).1 hx
  exact UbT_of t

theorem UbT_pre (g : List (Fin 8)) (hg : g ∈ UbT) : ∃ x ∈ Ub, tab x = g := by
  obtain ⟨t, ht⟩ := UbT_to g hg
  exact ⟨_, (mem_Ub_iff _).2 ⟨t, rfl⟩, ht⟩

theorem key_Ua {c : P8} {cT ciT : List (Fin 8)} (hcT : tab c = cT) (hciT : tab c⁻¹ = ciT)
    (h : ChkA UaT cT ciT) : Key Ua c := by
  intro σ hN hnot h128 hsign
  have hpa : swap 3 4 * swap 5 6 ∈ Ua := (mem_Ua_iff pa).2 ⟨(1, 0, 0, 0), by simp [tup4]⟩
  have hpb : swap 3 5 * swap 4 6 ∈ Ua := (mem_Ua_iff pb).2 ⟨(0, 1, 0, 0), by simp [tup4]⟩
  exact qchk_apply UaT_pre hcT hciT hnot h128 hsign
    (chkA_qchk h σ
      (swp2_mem_of_norm UaT_mem hN hpa)
      (swp2_mem_of_norm UaT_mem hN hpb))

theorem key_Ub {c : P8} {cT ciT : List (Fin 8)} (hcT : tab c = cT) (hciT : tab c⁻¹ = ciT)
    (h : ChkB UbT cT ciT) : Key Ub c := by
  intro σ hN hnot h128 hsign
  have hqa : swap 3 4 * swap 5 7 ∈ Ub := (mem_Ub_iff qa).2 ⟨(1, 0, 0, 0), by simp [tup4]⟩
  have hqb : swap 3 5 * swap 4 7 ∈ Ub := (mem_Ub_iff qb).2 ⟨(0, 1, 0, 0), by simp [tup4]⟩
  exact qchk_apply UbT_pre hcT hciT hnot h128 hsign
    (chkB_qchk h σ
      (swp2_mem_of_norm UbT_mem hN hqa)
      (swp2_mem_of_norm UbT_mem hN hqb))

theorem A_U_max_holds : A_U_max_stmt := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact piStar_of_key (key_Ua tab_cc tab_cc_inv chk_Ua_cc) Ua_le_A8 Ua_pgroup
      (Ua_nor cc fun t => ⟨(Ua_conj t).1, (Ua_conj t).2.1⟩)
  · exact piStar_of_key (key_Ua tab_dd tab_dd_inv chk_Ua_dd) Ua_le_A8 Ua_pgroup
      (Ua_nor dd fun t => ⟨(Ua_conj t).2.2.1, (Ua_conj t).2.2.2⟩)
  · exact piStar_of_key (key_Ub tab_cc tab_cc_inv chk_Ub_cc) Ub_le_A8 Ub_pgroup
      (Ub_nor cc fun t => ⟨(Ub_conj t).1, (Ub_conj t).2.1⟩)
  · exact piStar_of_key (key_Ub tab_dd tab_dd_inv chk_Ub_dd) Ub_le_A8 Ub_pgroup
      (Ub_nor dd fun t => ⟨(Ub_conj t).2.2.1, (Ub_conj t).2.2.2⟩)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
