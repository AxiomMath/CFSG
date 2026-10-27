module

public import CFSG.Quasithin.Background.GoldschmidtM12SylowCore
public import CFSG.Quasithin.Recognition.M12AmalE8Check
public import CFSG.Quasithin.Recognition.M12AmalInst

public section

namespace CFSG.Quasithin.F6

namespace M12Sylow

open CFSG.Assembly CFSG.Quasithin.M12Amal CFSG.Quasithin.M12AmalE8 CFSG.Sporadic.Bridge Equiv

theorem tel64_eq_of_compL {i j k : ℕ} (hi : i < 64) (hj : j < 64) (hk : k < 64)
    (h : compL (tl i) (tl j) = tl k) : telG i * telG j = telG k :=
  eq_of_reprG (reprG_mul (reprG_tel i hi) (reprG_tel j hj))
    (show ReprG (compL (tl i) (tl j)) (telG k) by rw [h]; exact reprG_tel k hk)

theorem tel64_mul {i j : ℕ} (hi : i < 64) (hj : j < 64) : telG i * telG j = telG (tmul i j) := by
  obtain ⟨hk, he⟩ := tmul_chk i hi j hj
  exact tel64_eq_of_compL hi hj hk he

theorem tel64_inv {i : ℕ} (hi : i < 64) : (telG i)⁻¹ = telG (tinv i) := by
  obtain ⟨hk, he⟩ := tinv_chk i hi
  have : telG i * telG (tinv i) = 1 :=
    eq_of_reprG (reprG_mul (reprG_tel i hi) (reprG_tel _ hk))
      (show ReprG (compL (tl i) (tl (tinv i))) 1 by rw [he]; exact reprG_one)
  exact inv_eq_of_mul_eq_one_right this

theorem tel64_inj {i j : ℕ} (hi : i < 64) (hj : j < 64) (h : telG i = telG j) : i = j :=
  tl_inj_chk i hi j hj (repL_unique (reprG_tel i hi) (h ▸ reprG_tel j hj))

theorem tel64_zero : telG 0 = 1 := tel_zero

theorem tel64_mem_T {i : ℕ} (hi : i < 64) : telG i ∈ m12Data.T :=
  m12Data.Tel_mem_T (⟨i, hi⟩ : Fin 64)

theorem exists_idx_of_mem_T {g : M12G} (hg : g ∈ m12Data.T) : ∃ i : ℕ, i < 64 ∧ g = telG i := by
  obtain ⟨i, hi⟩ := (m12Data.mem_T_iff g).1 hg
  exact ⟨i, i.2, hi.symm⟩

@[expose] def idxSub (L : List ℕ) (h0 : 0 ∈ L) (hlt : ∀ i ∈ L, i < 64)
    (hmul : ∀ i ∈ L, ∀ j ∈ L, tmul i j ∈ L) (hinv : ∀ i ∈ L, tinv i ∈ L) : Subgroup M12G where
  carrier := {g | ∃ i ∈ L, g = telG i}
  one_mem' := ⟨0, h0, tel64_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    exact ⟨tmul i j, hmul i hi j hj, tel64_mul (hlt i hi) (hlt j hj)⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨tinv i, hinv i hi, tel64_inv (hlt i hi)⟩

theorem card64_mem_list (X : List ℕ) (hX : X.Nodup) : Nat.card {i // i ∈ X} = X.length := by
  have e : Fin X.attach.length ≃ {i // i ∈ X} :=
    List.Nodup.getEquivOfForallMemList X.attach (hX.attach) (fun x => List.mem_attach X x)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin, List.length_attach]

theorem card64_of_idx {B : Subgroup M12G} {X : List ℕ} (hX : X.Nodup) (hlt : ∀ i ∈ X, i < 64)
    (hB : ∀ g, g ∈ B ↔ ∃ i ∈ X, g = telG i) : Nat.card B = X.length := by
  have hinj : Function.Injective (fun i : {i // i ∈ X} => telG i.1) := fun i j h =>
    Subtype.ext (tel64_inj (hlt _ i.2) (hlt _ j.2) h)
  have hrange : Set.range (fun i : {i // i ∈ X} => telG i.1) = (B : Set M12G) := by
    ext g
    simp only [Set.mem_range, SetLike.mem_coe, hB]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have h1 : Nat.card B = Nat.card (Set.range (fun i : {i // i ∈ X} => telG i.1)) := by
    rw [hrange]
    rfl
  rw [h1, Nat.card_range_of_injective hinj, card64_mem_list X hX]

@[expose] def powIdx (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => tmul (powIdx i m) i

theorem powIdx_lt {i : ℕ} (hi : i < 64) (m : ℕ) : powIdx i m < 64 := by
  induction m with
  | zero => show 0 < 64; norm_num
  | succ m ih => exact (tmul_chk _ ih i hi).1

theorem tel64_pow {i : ℕ} (hi : i < 64) (m : ℕ) : telG i ^ m = telG (powIdx i m) := by
  induction m with
  | zero => rw [pow_zero]; exact tel64_zero.symm
  | succ m ih => rw [pow_succ, ih, tel64_mul (powIdx_lt hi m) hi]; rfl

theorem pow_exp8 : ∀ i < 64, powIdx i 8 = 0 := by decide +kernel

theorem pow_order8 : ∃ i < 64, powIdx i 4 ≠ 0 := by decide +kernel

@[expose] def invIdx : List ℕ :=
  [3, 4, 6, 8, 9, 10, 11, 14, 16, 19, 21, 23, 29, 30, 31, 33, 36, 37, 39, 45, 48, 50, 53, 54, 56,
   58, 61]

@[expose] def famTab : List (List ℕ) :=
  [[0],
   [0, 3],
   [0, 4],
   [0, 6],
   [0, 8],
   [0, 9],
   [0, 10],
   [0, 11],
   [0, 14],
   [0, 16],
   [0, 19],
   [0, 21],
   [0, 23],
   [0, 29],
   [0, 30],
   [0, 31],
   [0, 33],
   [0, 36],
   [0, 37],
   [0, 39],
   [0, 45],
   [0, 48],
   [0, 50],
   [0, 53],
   [0, 54],
   [0, 56],
   [0, 58],
   [0, 61],
   [0, 3, 4, 14],
   [0, 3, 8, 23],
   [0, 3, 19, 39],
   [0, 3, 29, 50],
   [0, 3, 48, 61],
   [0, 4, 6, 10],
   [0, 4, 8, 29],
   [0, 4, 9, 30],
   [0, 4, 11, 31],
   [0, 4, 16, 21],
   [0, 4, 19, 48],
   [0, 4, 23, 50],
   [0, 4, 33, 36],
   [0, 4, 37, 45],
   [0, 4, 39, 61],
   [0, 4, 53, 58],
   [0, 4, 54, 56],
   [0, 6, 16, 23],
   [0, 6, 19, 53],
   [0, 6, 21, 50],
   [0, 6, 48, 58],
   [0, 8, 9, 11],
   [0, 8, 14, 50],
   [0, 8, 30, 31],
   [0, 8, 33, 37],
   [0, 8, 36, 45],
   [0, 8, 53, 54],
   [0, 8, 56, 58],
   [0, 9, 29, 31],
   [0, 10, 16, 50],
   [0, 10, 19, 58],
   [0, 10, 21, 23],
   [0, 10, 48, 53],
   [0, 11, 29, 30],
   [0, 14, 19, 61],
   [0, 14, 23, 29],
   [0, 14, 39, 48],
   [0, 16, 39, 56],
   [0, 16, 54, 61],
   [0, 21, 39, 54],
   [0, 21, 56, 61],
   [0, 29, 33, 45],
   [0, 29, 36, 37],
   [0, 29, 53, 56],
   [0, 29, 54, 58],
   [0, 3, 4, 8, 14, 23, 29, 50],
   [0, 3, 4, 14, 19, 39, 48, 61],
   [0, 4, 6, 10, 16, 21, 23, 50],
   [0, 4, 6, 10, 19, 48, 53, 58],
   [0, 4, 8, 9, 11, 29, 30, 31],
   [0, 4, 8, 29, 33, 36, 37, 45],
   [0, 4, 8, 29, 53, 54, 56, 58],
   [0, 4, 16, 21, 39, 54, 56, 61]]

theorem invIdx_chk : ∀ u < 64, (u ≠ 0 ∧ tmul u u = 0) ↔ u ∈ invIdx := by decide +kernel

theorem famTab_zero_chk : [0] ∈ famTab := by decide +kernel

theorem famTab_bound_chk : ∀ X ∈ famTab, X.length ≤ 8 ∧ X.Nodup ∧ (∀ i ∈ X, i < 64) ∧ 0 ∈ X := by
  decide +kernel

@[expose] def insSorted (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: insSorted a l

@[expose] def sortList : List ℕ → List ℕ
  | [] => []
  | a :: l => insSorted a (sortList l)

theorem mem_insSorted (a i : ℕ) (l : List ℕ) : i ∈ insSorted a l ↔ i = a ∨ i ∈ l := by
  induction l with
  | nil => simp [insSorted]
  | cons b l ih =>
    unfold insSorted
    split_ifs
    · simp
    · simp only [List.mem_cons, ih]
      tauto

theorem mem_sortList (i : ℕ) (l : List ℕ) : i ∈ sortList l ↔ i ∈ l := by
  induction l with
  | nil => simp [sortList]
  | cons a l ih =>
    unfold sortList
    rw [mem_insSorted, ih]
    simp

@[expose] def extList (X : List ℕ) (u : ℕ) : List ℕ :=
  sortList (X ++ X.map (fun j => tmul j u))

theorem famTab_ext_chk : ∀ X ∈ famTab, ∀ u ∈ invIdx, u ∉ X → (∀ j ∈ X, tmul u j = tmul j u) →
    extList X u ∈ famTab := by
  decide +kernel

theorem sorted_ext_mem (X : List ℕ) (u i : ℕ) :
    i ∈ extList X u ↔ i ∈ X ∨ ∃ j ∈ X, tmul j u = i := by
  unfold extList
  rw [mem_sortList, List.mem_append, List.mem_map]

theorem elemAbelian_mono {G : Type} [Group G] {B B' : Subgroup G} (h : B ≤ B')
    (hel : IsElemAbelian 2 B') : IsElemAbelian 2 B :=
  ⟨⟨⟨fun x y => by
    apply Subtype.ext
    show (x : G) * y = y * x
    exact congrArg Subtype.val (hel.1.is_comm.comm ⟨x, h x.2⟩ ⟨y, h y.2⟩)⟩⟩,
    fun x hx => hel.2 x (h hx)⟩

theorem elemAbelian_mem_fam : ∀ (n : ℕ) (B : Subgroup M12G), B ≤ m12Data.T → IsElemAbelian 2 B →
    Nat.card B = n → ∃ X ∈ famTab, ∀ g, g ∈ B ↔ ∃ i ∈ X, g = telG i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hBT hel hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : n = 1
  ·
    have hB : B = ⊥ := Subgroup.eq_bot_of_card_eq B (hn.trans h1)
    refine ⟨[0], famTab_zero_chk, fun g => ?_⟩
    rw [hB, Subgroup.mem_bot]
    constructor
    · rintro rfl
      exact ⟨0, by simp, tel64_zero.symm⟩
    · rintro ⟨i, hi, rfl⟩
      simp only [List.mem_singleton] at hi
      subst hi
      exact tel64_zero
  ·
    have hp : IsPGroup 2 ↥B := fun x => ⟨1, Subtype.ext (by simpa using hel.2 x x.2)⟩
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0] at hn
      exact Nat.card_pos.ne' hn
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hm
      exact h1 (hn.symm.trans hm)
    obtain ⟨B'', hB''card, -, hB''le⟩ :=
      Sylow.exists_subgroup_card_pow_prime_le_le (p := 2) Nat.prime_two (n := m - 1)
        (H := ⊥) (L := B) (by simp) (by
          rw [hm]
          exact pow_dvd_pow 2 (Nat.sub_le m 1)) bot_le
    have hBcard : Nat.card B = 2 * Nat.card B'' := by
      rw [hm, hB''card, ← pow_succ']
      congr 1
      omega
    have hB''lt : Nat.card B'' < n := by
      have := Nat.card_pos (α := ↥B'')
      omega
    obtain ⟨X', hX'fam, hX'⟩ :=
      ih _ hB''lt B'' (hB''le.trans hBT) (elemAbelian_mono hB''le hel) rfl
    obtain ⟨b, hbB, hbB''⟩ : ∃ b ∈ B, b ∉ B'' := by
      by_contra hcon
      push Not at hcon
      have := Subgroup.card_le_of_le (show B ≤ B'' from hcon)
      have := Nat.card_pos (α := ↥B'')
      omega
    obtain ⟨u, hu64, rfl⟩ := exists_idx_of_mem_T (hBT hbB)
    have hX'lt : ∀ i ∈ X', i < 64 := by
      have := famTab_bound_chk X' hX'fam
      exact this.2.2.1
    have hb1 : u ≠ 0 := fun h => hbB'' (by rw [h, tel64_zero]; exact B''.one_mem)
    have hb2 : tmul u u = 0 := by
      have hsq : telG u * telG u = 1 := by
        rw [← pow_two]
        exact hel.2 _ hbB
      rw [tel64_mul hu64 hu64, ← tel64_zero] at hsq
      exact tel64_inj (tmul_chk u hu64 u hu64).1 (by norm_num) hsq
    have huinv : u ∈ invIdx := (invIdx_chk u hu64).1 ⟨hb1, hb2⟩
    have hunot : u ∉ X' := fun hu => hbB'' ((hX' _).2 ⟨u, hu, rfl⟩)
    have hcomm : ∀ j ∈ X', tmul u j = tmul j u := by
      intro j hj
      have hjB : telG j ∈ B := hB''le ((hX' _).2 ⟨j, hj, rfl⟩)
      have hc := hel.1.is_comm.comm (⟨telG u, hbB⟩ : B) ⟨telG j, hjB⟩
      have hc' : telG u * telG j = telG j * telG u := congrArg Subtype.val hc
      rw [tel64_mul hu64 (hX'lt j hj), tel64_mul (hX'lt j hj) hu64] at hc'
      exact tel64_inj (tmul_chk u hu64 j (hX'lt j hj)).1 (tmul_chk j (hX'lt j hj) u hu64).1 hc'
    refine ⟨extList X' u, famTab_ext_chk X' hX'fam u huinv hunot hcomm, fun g => ?_⟩
    simp only [sorted_ext_mem]
    have hidx : (B''.subgroupOf B).index = 2 := by
      have h := Subgroup.card_mul_index (B''.subgroupOf B)
      have e : Nat.card (B''.subgroupOf B) = Nat.card B'' :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB''le).toEquiv
      rw [e] at h
      have hpos : 0 < Nat.card B'' := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h, hBcard]; ring)
    constructor
    · intro hg
      by_cases hgB'' : g ∈ B''
      · obtain ⟨i, hi, rfl⟩ := (hX' g).1 hgB''
        exact ⟨i, Or.inl hi, rfl⟩
      · have hmem : g * (telG u)⁻¹ ∈ B'' := by
          have ha : (⟨g, hg⟩ : B) ∉ B''.subgroupOf B := hgB''
          have hb : (⟨telG u, hbB⟩ : B)⁻¹ ∉ B''.subgroupOf B := by
            rw [Subgroup.inv_mem_iff]
            exact hbB''
          have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨g, hg⟩ : B))
            (b := (⟨telG u, hbB⟩ : B)⁻¹)).2 ⟨fun h => absurd h ha, fun h => absurd h hb⟩
          exact Subgroup.mem_subgroupOf.1 h
        obtain ⟨j, hj, hjeq⟩ := (hX' _).1 hmem
        refine ⟨tmul j u, Or.inr ⟨j, hj, rfl⟩, ?_⟩
        rw [← tel64_mul (hX'lt j hj) hu64, ← hjeq]
        group
    · rintro ⟨i, hi | ⟨j, hj, rfl⟩, rfl⟩
      · exact hB''le ((hX' _).2 ⟨i, hi, rfl⟩)
      · rw [← tel64_mul (hX'lt j hj) hu64]
        exact B.mul_mem (hB''le ((hX' _).2 ⟨j, hj, rfl⟩)) hbB

theorem card_le_eight (B : Subgroup M12G) (hBT : B ≤ m12Data.T) (hB : IsElemAbelian 2 B) :
    Nat.card B ≤ 8 := by
  obtain ⟨X, hXfam, hX⟩ := elemAbelian_mem_fam _ B hBT hB rfl
  obtain ⟨hlen, hnd, hlt, -⟩ := famTab_bound_chk X hXfam
  rw [card64_of_idx hnd hlt hX]
  exact hlen

@[expose] def X8 : List ℕ := [0, 3, 4, 8, 14, 23, 29, 50]

theorem X8_chk : X8.length = 8 ∧ X8.Nodup ∧ (∀ i ∈ X8, i < 64) ∧ 0 ∈ X8 ∧
    (∀ i ∈ X8, ∀ j ∈ X8, tmul i j ∈ X8 ∧ tmul i j = tmul j i ∧ tmul i i = 0) ∧
    (∀ i ∈ X8, tinv i ∈ X8) := by
  decide +kernel

@[expose] def Esub : Subgroup M12G :=
  idxSub X8 X8_chk.2.2.2.1 X8_chk.2.2.1 (fun i hi j hj => (X8_chk.2.2.2.2.1 i hi j hj).1)
    X8_chk.2.2.2.2.2

theorem Esub_le_T : Esub ≤ m12Data.T := by
  rintro _ ⟨i, hi, rfl⟩
  exact tel64_mem_T (X8_chk.2.2.1 i hi)

theorem card_Esub : Nat.card Esub = 8 := by
  rw [card64_of_idx X8_chk.2.1 X8_chk.2.2.1 (fun g => Iff.rfl)]
  exact X8_chk.1

theorem Esub_elem : IsElemAbelian 2 Esub := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨x, i, hi, rfl⟩ := x
    obtain ⟨y, j, hj, rfl⟩ := y
    apply Subtype.ext
    show telG i * telG j = telG j * telG i
    have hi' := X8_chk.2.2.1 i hi
    have hj' := X8_chk.2.2.1 j hj
    rw [tel64_mul hi' hj', tel64_mul hj' hi', (X8_chk.2.2.2.2.1 i hi j hj).2.1]
  · rintro _ ⟨i, hi, rfl⟩
    have hi' := X8_chk.2.2.1 i hi
    rw [pow_two, tel64_mul hi' hi', (X8_chk.2.2.2.2.1 i hi i hi).2.2]
    exact tel64_zero

theorem tProps64_m12 : TProps64 ↥m12Data.T where
  card := by rw [m12_card_T]; norm_num
  exp := by
    intro x
    obtain ⟨i, hi, hx⟩ := exists_idx_of_mem_T x.2
    apply Subtype.ext
    show (x : M12G) ^ 8 = 1
    rw [hx, tel64_pow hi, pow_exp8 i hi]
    exact tel64_zero
  order8 := by
    obtain ⟨i, hi, hne⟩ := pow_order8
    refine ⟨⟨telG i, tel64_mem_T hi⟩, fun h => hne ?_⟩
    have h1 : telG i ^ 4 = 1 := congrArg Subtype.val h
    rw [tel64_pow hi, ← tel64_zero] at h1
    exact tel64_inj (powIdx_lt hi 4) (by norm_num) h1
  rank := by
    intro B hB
    have hmap : IsElemAbelian 2 (B.map m12Data.T.subtype) := isElemAbelian_map _ hB
    have hle : B.map m12Data.T.subtype ≤ m12Data.T := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hcard : Nat.card (B.map m12Data.T.subtype) = Nat.card B :=
      (Nat.card_congr (B.equivMapOfInjective _ m12Data.T.subtype_injective).toEquiv).symm
    rw [← hcard]
    exact card_le_eight _ hle hmap
  hasE8 := by
    refine ⟨Esub.subgroupOf m12Data.T, ?_, ?_⟩
    · refine ⟨⟨⟨?_⟩⟩, ?_⟩
      · rintro ⟨⟨a, ha⟩, ha'⟩ ⟨⟨b, hb⟩, hb'⟩
        apply Subtype.ext
        apply Subtype.ext
        show a * b = b * a
        exact congrArg Subtype.val (Esub_elem.1.is_comm.comm ⟨a, ha'⟩ ⟨b, hb'⟩)
      · rintro ⟨a, ha⟩ ha'
        apply Subtype.ext
        exact Esub_elem.2 a ha'
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Esub_le_T).toEquiv]
      exact card_Esub

theorem tProps64_sylow (Q : Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M12) :
    TProps64 ↥(Q : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12) :=
  tProps64_m12.of_mulEquiv (Sylow.equiv (m12_syl.1.toSylow m12_syl.2) Q)

end M12Sylow

end CFSG.Quasithin.F6
