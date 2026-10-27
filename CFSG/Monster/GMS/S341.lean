module

import CFSG.Monster.GMS.TwoCentral
public import CFSG.Monster.GMS.BabyCover
public import CFSG.Monster.GMS.Facts.DoubleCover
public import CFSG.Monster.GMS.Facts.LeechPairs

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Defs

variable {G : Type*} [Group G]

@[expose] def tableVISet (a x b : G) : Set G := {c | c ∈ twoANbr a b ∧ c ≠ x ∧ c ≠ x * b}

inductive TableVIClass
  | two_A
  | two_B
  | four_B
  | four_A
  | three_A
  | six_A
  deriving DecidableEq

@[expose] def tableVICond (a z₀ b x : G) : TableVIClass → G → Prop
  | .two_A, c => IsConj a (x * c)
  | .two_B, c => IsConj z₀ (x * c)
  | .four_B, c => (x * c) ^ 2 = b
  | .four_A, c => orderOf (x * c) = 4 ∧ IsConj z₀ ((x * c) ^ 2)
  | .three_A, c => orderOf (x * c) = 3
  | .six_A, c => (x * c) ^ 3 = b

@[expose] def tableVIOrbit (a z₀ x b : G) (K : TableVIClass) : Set G :=
  {c | c ∈ tableVISet a x b ∧ tableVICond a z₀ b x K c}

@[expose] def tableVIStab : TableVIClass → ℕ
  | .two_A => 2 ^ 38 * 3 ^ 6 * 5 * 7 * 11
  | .two_B => 2 ^ 38 * 3 ^ 6 * 5 * 7 * 11
  | .four_B => 2 ^ 25 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17
  | .four_A => 2 ^ 29 * 3 ^ 6 * 5 * 7
  | .three_A => 2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13
  | .six_A => 2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13

@[expose] def tableVISize : TableVIClass → ℕ
  | .two_A => 3968055
  | .two_B => 3968055
  | .four_B => 46227456
  | .four_A => 22348085760
  | .three_A => 2370830336
  | .six_A => 2370830336

@[expose] def TableVIClass.orbitIndex : TableVIClass → Fin 4
  | .two_A => 0
  | .two_B => 0
  | .four_B => 1
  | .four_A => 3
  | .three_A => 2
  | .six_A => 2

theorem tableVIStab_mul_size (K : TableVIClass) : tableVIStab K * tableVISize K = tableVOrderB := by
  cases K <;> norm_num [tableVIStab, tableVISize, tableVOrderB]

@[expose] def tableVIOrder : TableVIClass → ℕ
  | .two_A => 2
  | .two_B => 2
  | .four_B => 4
  | .four_A => 4
  | .three_A => 3
  | .six_A => 6

theorem tableVIStab_pos (K : TableVIClass) : 0 < tableVIStab K := by
  cases K <;> norm_num [tableVIStab]

theorem tableVISize_pos (K : TableVIClass) : 0 < tableVISize K := by
  cases K <;> norm_num [tableVISize]

theorem eq_tableVIStab_of_mul_size {n : ℕ} (K : TableVIClass)
    (h : n * tableVISize K = tableVOrderB) :
    n = tableVIStab K :=
  Nat.eq_of_mul_eq_mul_right (tableVISize_pos K) (h.trans (tableVIStab_mul_size K).symm)

theorem arith_four {n m : ℕ} (h1 : n * (2 * 2) = 2 * m) (hm : m * 23113728 = tableVOrderB) :
    n * 46227456 = tableVOrderB := by
  have h : m = 2 * n := by omega
  rw [← hm, h]
  ring

theorem arith_two {n m : ℕ} (h1 : n * (1 * 2) = 2 * m) (hm : m * 2370830336 = tableVOrderB) :
    n * 2370830336 = tableVOrderB := by
  have h : m = n := by omega
  rw [← hm, h]

theorem TableVIClass.orbitIndex_eq_zero_iff {K : TableVIClass} :
    K.orbitIndex = 0 ↔ K = .two_A ∨ K = .two_B := by
  cases K <;> simp [TableVIClass.orbitIndex]

theorem TableVIClass.orbitIndex_eq_one_iff {K : TableVIClass} : K.orbitIndex = 1 ↔ K = .four_B := by
  cases K <;> simp [TableVIClass.orbitIndex]

theorem TableVIClass.orbitIndex_eq_two_iff {K : TableVIClass} :
    K.orbitIndex = 2 ↔ K = .three_A ∨ K = .six_A := by
  cases K <;> simp [TableVIClass.orbitIndex]

theorem TableVIClass.orbitIndex_eq_three_iff {K : TableVIClass} :
    K.orbitIndex = 3 ↔ K = .four_A := by
  cases K <;> simp [TableVIClass.orbitIndex]

end Defs

section Algebra

variable {G : Type*} [Group G]

theorem dihedral_sq_facts {x c : G} (hx : x * x = 1) (hc : c * c = 1)
    (hw : ((x * c) * (x * c)) * ((x * c) * (x * c)) = 1) :
    x * ((x * c) * (x * c)) = c * x * c ∧ ((x * c) * (x * c)) * x = c * x * c ∧
      c * ((x * c) * (x * c)) = x * c * x ∧ ((x * c) * (x * c)) * c = x * c * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hinv : (c * x) * (c * x) = (x * c) * (x * c) := by
    have h1 : ((x * c) * (x * c))⁻¹ = (x * c) * (x * c) := inv_eq_of_mul_eq_one_right hw
    rw [← h1, mul_inv_rev, mul_inv_rev, hx', hc']
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc x * ((x * c) * (x * c)) = (x * x) * c * x * c := by group
      _ = c * x * c := by rw [hx, one_mul]
  · calc ((x * c) * (x * c)) * x = ((c * x) * (c * x)) * x := by rw [hinv]
      _ = c * x * c * (x * x) := by group
      _ = c * x * c := by rw [hx, mul_one]
  · calc c * ((x * c) * (x * c)) = c * ((c * x) * (c * x)) := by rw [hinv]
      _ = (c * c) * x * c * x := by group
      _ = x * c * x := by rw [hc, one_mul]
  · calc ((x * c) * (x * c)) * c = x * c * x * (c * c) := by group
      _ = x * c * x := by rw [hc, mul_one]

theorem orderOf_eq_four_of_mul_self {s : G} (h1 : s * s ≠ 1) (h2 : (s * s) * (s * s) = 1) :
    orderOf s = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := s)
    (by simpa [pow_two] using h1) (by
      show s ^ 4 = 1
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      exact h2)
  simpa using h

theorem orderOf_eq_six_of_pow_three {s b : G} (hb : b * b = 1) (hb1 : b ≠ 1) (hs1 : s ≠ 1)
    (hsb : s ≠ b) (h3 : s ^ 3 = b) : orderOf s = 6 := by
  have h6 : s ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, h3, hb]
  have hdvd : orderOf s ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hpos : 0 < orderOf s := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : orderOf s ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hn := pow_orderOf_eq_one s
  generalize orderOf s = n at hn hdvd hpos hle ⊢
  interval_cases n
  · exact absurd (pow_one s ▸ hn) hs1
  · exfalso
    apply hsb
    rw [← h3, pow_succ, hn, one_mul]
  · exfalso
    exact hb1 (h3 ▸ hn)
  · omega
  · omega
  · rfl

theorem ncard_split {b : G} {F A B' : Set G} (hF : F = A ∪ B') (hd : Disjoint A B')
    (hfin : F.Finite) (hAB : ∀ y ∈ A, b * y ∈ B') (hBA : ∀ y ∈ B', b * y ∈ A) :
    A.ncard = B'.ncard ∧ 2 * A.ncard = F.ncard := by
  have hAfin : A.Finite := hfin.subset (hF ▸ Set.subset_union_left)
  have hBfin : B'.Finite := hfin.subset (hF ▸ Set.subset_union_right)
  have h1 : A.ncard ≤ B'.ncard :=
    Set.ncard_le_ncard_of_injOn (fun y => b * y) hAB (fun y _ y' _ h => mul_left_cancel h) hBfin
  have h2 : B'.ncard ≤ A.ncard :=
    Set.ncard_le_ncard_of_injOn (fun y => b * y) hBA (fun y _ y' _ h => mul_left_cancel h) hAfin
  have h3 : F.ncard = A.ncard + B'.ncard := by
    rw [hF, Set.ncard_union_eq hd hAfin hBfin]
  omega

end Algebra

section LeechComm

variable {G : Type*} [Group G]

theorem leechQ_commutator_mem_zpowers {w : G} (hw : GMSLeechCentralizer w) {p q : G}
    (hp : p ∈ leechQ w) (hq : q ∈ leechQ w) : p * q * p⁻¹ * q⁻¹ ∈ Subgroup.zpowers w := by
  obtain ⟨hw2, hQ, -, -, hcon⟩ := hw
  obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hp
  obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.mp hq
  rw [← center_pCore_map_eq_zpowers hw2 hQ hcon]
  have hcomm : (⟨p', hp'⟩ : CFSG.pCore 2 (Subgroup.centralizer ({w} : Set G))) * ⟨q', hq'⟩ *
      ⟨p', hp'⟩⁻¹ * ⟨q', hq'⟩⁻¹ ∈
        Subgroup.center (CFSG.pCore 2 (Subgroup.centralizer ({w} : Set G))) := by
    rw [← hQ.2.1]
    have := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (⟨p', hp'⟩ : CFSG.pCore 2 (Subgroup.centralizer ({w} : Set G))))
      (Subgroup.mem_top (⟨q', hq'⟩ : CFSG.pCore 2 (Subgroup.centralizer ({w} : Set G))))
    rwa [← commutator_def, commutatorElement_def] at this
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hcomm)

end LeechComm

section TwoClassesLeech

variable {G : Type} [Group G] {a z₀ b z u : G}

theorem TwoClasses.card_centralizer_inf_of_mem_leechQ_two (h : TwoClasses a z₀ b z u) {w x : G}
    (hw : IsConj z₀ w) (hx : x ∈ leechQ w) (hax : IsConj a x) :
    Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) =
      tableVOrderZ := by
  obtain ⟨g, hg1, hg2⟩ := h.exists_conj_of_mem_leechQ hw hax hx
  rw [← hg1, ← hg2, card_centralizer_inf_conj, inf_comm]
  exact h.tableV.card_z

theorem TwoClasses.isLeechTwo_of_mem (h : TwoClasses a z₀ b z u) {w y : G} (hw : IsConj z₀ w)
    (hy : y ∈ leechQ w) (hyA : IsConj a y) : IsLeechTwo w y := by
  have hy2 : orderOf y = 2 := (orderOf_eq_of_isConj hyA).symm.trans h.orderOf_a
  refine ⟨hy, ne_one_of_orderOf hy2, ?_, mul_self_eq_one_of_orderOf hy2, ?_⟩
  · rintro rfl
    exact h.not_isConj (hyA.trans hw.symm)
  · exact h.card_centralizer_inf_of_mem_leechQ_two hw hy hyA

end TwoClassesLeech

section Ctx

variable {G : Type} [Group G] {a z₀ b₀ z u x b c : G}
  {φ : Subgroup.centralizer ({b} : Set G) →* B}

structure TableVICtx (a z₀ b₀ z u x b : G)
    (φ : Subgroup.centralizer ({b} : Set G) →* B) : Prop where
  two : TwoClasses a z₀ b₀ z u
  t3 : BabyTableIII
  t4 : BabyTableIV
  isConj_x : IsConj a x
  mem_nbr : b ∈ twoANbr a x
  cover : IsBabyCover b φ

namespace TableVICtx

theorem isConj_b (C : TableVICtx a z₀ b₀ z u x b φ) : IsConj a b := C.mem_nbr.1

theorem orderOf_x (C : TableVICtx a z₀ b₀ z u x b φ) : orderOf x = 2 :=
  (orderOf_eq_of_isConj C.isConj_x).symm.trans C.two.orderOf_a

theorem orderOf_b (C : TableVICtx a z₀ b₀ z u x b φ) : orderOf b = 2 :=
  (orderOf_eq_of_isConj C.isConj_b).symm.trans C.two.orderOf_a

theorem xx (C : TableVICtx a z₀ b₀ z u x b φ) : x * x = 1 :=
  mul_self_eq_one_of_orderOf C.orderOf_x

theorem bb (C : TableVICtx a z₀ b₀ z u x b φ) : b * b = 1 :=
  mul_self_eq_one_of_orderOf C.orderOf_b

theorem comm (C : TableVICtx a z₀ b₀ z u x b φ) : x * b = b * x :=
  mul_comm_of_mul_self_eq_one C.xx C.bb (mul_self_eq_one_of_orderOf
    ((orderOf_eq_of_isConj C.mem_nbr.2).symm.trans C.two.orderOf_a))

theorem x_mem_centralizer (C : TableVICtx a z₀ b₀ z u x b φ) :
    x ∈ Subgroup.centralizer ({b} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr C.comm

theorem x_ne_b (C : TableVICtx a z₀ b₀ z u x b φ) : x ≠ b := by
  intro hxb
  have h := orderOf_eq_of_isConj C.mem_nbr.2
  rw [← hxb, C.xx, orderOf_one, C.two.orderOf_a] at h
  omega

theorem x_nbr (C : TableVICtx a z₀ b₀ z u x b φ) : x ∈ twoANbr a b :=
  ⟨C.isConj_x, by rw [← C.comm]; exact C.mem_nbr.2⟩

theorem orderOf_c (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    orderOf c = 2 :=
  (orderOf_eq_of_isConj hc.1.1).symm.trans C.two.orderOf_a

theorem cc (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) : c * c = 1 :=
  mul_self_eq_one_of_orderOf (C.orderOf_c hc)

theorem bc_comm (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    b * c = c * b :=
  mul_comm_of_mul_self_eq_one C.bb (C.cc hc) (mul_self_eq_one_of_orderOf
    ((orderOf_eq_of_isConj hc.1.2).symm.trans C.two.orderOf_a))

theorem c_mem_centralizer (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    c ∈ Subgroup.centralizer ({b} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (C.bc_comm hc).symm

theorem xc_ne_one (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    x * c ≠ 1 := by
  intro h
  apply hc.2.1
  calc c = x * (x * c) := by rw [← mul_assoc, C.xx, one_mul]
    _ = x := by rw [h, mul_one]

theorem xc_ne_b (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    x * c ≠ b := by
  intro h
  apply hc.2.2
  calc c = x * (x * c) := by rw [← mul_assoc, C.xx, one_mul]
    _ = x * b := by rw [h]

theorem xc_mem_centralizer (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    x * c ∈ Subgroup.centralizer ({b} : Set G) :=
  Subgroup.mul_mem _ C.x_mem_centralizer (C.c_mem_centralizer hc)

theorem coverMap_xc (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    coverMap φ (x * c) = coverMap φ x * coverMap φ c :=
  coverMap_mul C.x_mem_centralizer (C.c_mem_centralizer hc)

end TableVICtx

end Ctx

section CtxFin

variable {G : Type} [Group G] [Finite G] {a z₀ b₀ z u x b c : G}
  {φ : Subgroup.centralizer ({b} : Set G) →* B}

namespace TableVICtx

theorem babyInv_x (C : TableVICtx a z₀ b₀ z u x b φ) : BabyInv 0 (coverMap φ x) :=
  ((C.two.mem_twoANbr_iff C.t3 C.isConj_b C.cover).mp C.x_nbr).2

theorem mem_tableVISet_iff (C : TableVICtx a z₀ b₀ z u x b φ) :
    c ∈ tableVISet a x b ↔ c ∈ Subgroup.centralizer ({b} : Set G) ∧
      BabyInv 0 (coverMap φ c) ∧ coverMap φ c ≠ coverMap φ x := by
  constructor
  · rintro ⟨hc, hcx, hcxb⟩
    obtain ⟨hcC, hc0⟩ := (C.two.mem_twoANbr_iff C.t3 C.isConj_b C.cover).mp hc
    refine ⟨hcC, hc0, fun h => ?_⟩
    rcases (C.cover.coverMap_eq_iff C.x_mem_centralizer hcC).mp h.symm with e | e
    · exact hcx e
    · exact hcxb (by rw [e, C.comm])
  · rintro ⟨hcC, hc0, hne⟩
    refine ⟨(C.two.mem_twoANbr_iff C.t3 C.isConj_b C.cover).mpr ⟨hcC, hc0⟩,
      fun e => hne (by rw [e]), fun e => hne ?_⟩
    rw [e, C.comm, C.cover.coverMap_mul_b C.x_mem_centralizer]

theorem exists_orbit (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    ∃ k, BabyOrbit k (coverMap φ x) (coverMap φ c) := by
  obtain ⟨hcC, hc0, hne⟩ := C.mem_tableVISet_iff.mp hc
  obtain ⟨k, hk⟩ := (C.t4 _ C.babyInv_x).1 _ hc0 hne
  exact ⟨k, hk⟩

theorem k0 (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b)
    (hk : BabyOrbit 0 (coverMap φ x) (coverMap φ c)) :
    (x * c) * (x * c) = 1 ∧ ((IsConj z₀ (x * c) ∧ IsConj a (b * (x * c))) ∨
      (IsConj a (x * c) ∧ IsConj z₀ (b * (x * c)))) := by
  refine C.two.babyInv_one_cases C.t3 C.isConj_b C.cover (C.xc_mem_centralizer hc) ?_
  rw [C.coverMap_xc hc]
  exact hk

theorem k1 (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b)
    (hk : BabyOrbit 1 (coverMap φ x) (coverMap φ c)) : (x * c) * (x * c) = b := by
  refine C.two.mul_self_eq_of_babyInv_three C.t3 C.isConj_b C.cover (C.xc_mem_centralizer hc) ?_
  rw [C.coverMap_xc hc]
  exact hk

omit [Finite G] in
theorem k2 (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b)
    (hk : BabyOrbit 2 (coverMap φ x) (coverMap φ c)) : (x * c) ^ 3 = 1 ∨ (x * c) ^ 3 = b := by
  have h3 : coverMap φ ((x * c) ^ 3) = 1 := by
    rw [coverMap_pow (C.xc_mem_centralizer hc), C.coverMap_xc hc]
    have := pow_orderOf_eq_one (coverMap φ x * coverMap φ c)
    rwa [show orderOf (coverMap φ x * coverMap φ c) = 3 from hk] at this
  exact (C.cover.coverMap_eq_one_iff (Subgroup.pow_mem _ (C.xc_mem_centralizer hc) 3)).mp h3

theorem k3_data (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b)
    (hk : BabyOrbit 3 (coverMap φ x) (coverMap φ c)) :
    (x * c) * (x * c) ≠ 1 ∧ IsConj z₀ ((x * c) * (x * c)) ∧
      ((x * c) * (x * c)) * ((x * c) * (x * c)) = 1 ∧
      x ∈ leechQ ((x * c) * (x * c)) ∧ c ∈ leechQ ((x * c) * (x * c)) ∧
      b ∈ leechQ ((x * c) * (x * c)) := by
  obtain ⟨-, hk1⟩ := hk
  have hcC := C.c_mem_centralizer hc
  have htC := C.xc_mem_centralizer hc
  have hwC : (x * c) * (x * c) ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mul_mem _ htC htC
  have h1w : BabyInv 1 (coverMap φ ((x * c) * (x * c))) := by
    rw [coverMap_mul htC htC, C.coverMap_xc hc, ← pow_two]
    exact hk1
  obtain ⟨hww, hcase⟩ := C.two.babyInv_one_cases C.t3 C.isConj_b C.cover hwC h1w
  have hw1 : (x * c) * (x * c) ≠ 1 := by
    intro h
    rw [h, coverMap_one] at h1w
    exact absurd h1w.1 (by simp)
  have hx := C.xx
  have hcc := C.cc hc
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  obtain ⟨hxw, hwx, hcw, hwc⟩ := dihedral_sq_facts hx hcc hww
  have hbx : b * x = x * b := C.comm.symm
  have hbc : b * c = c * b := C.bc_comm hc
  have hbw : b * ((x * c) * (x * c)) = ((x * c) * (x * c)) * b := by
    have h1 : Commute b (x * c) := Commute.mul_right hbx hbc
    exact (h1.mul_right h1)
  generalize hwdef : (x * c) * (x * c) = w at *
  have hxwc : x * c * x * c = w := by rw [← hwdef]; group
  obtain ⟨w₀, hw₀B, hbw₀, hw₀w⟩ : ∃ w₀, IsConj z₀ w₀ ∧ IsConj a (b * w₀) ∧
      (w₀ = w ∨ w₀ = b * w) := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨w, h1, h2, Or.inl rfl⟩
    · refine ⟨b * w, h2, ?_, Or.inr rfl⟩
      rw [← mul_assoc, C.bb, one_mul]
      exact h1
  have hxw₀ : x * w₀ = w₀ * x := by
    rcases hw₀w with rfl | rfl
    · rw [hxw, hwx]
    · calc x * (b * w) = (x * b) * w := (mul_assoc _ _ _).symm
        _ = (b * x) * w := by rw [C.comm]
        _ = b * (x * w) := mul_assoc _ _ _
        _ = b * (w * x) := by rw [hxw, hwx]
        _ = (b * w) * x := (mul_assoc _ _ _).symm
  have hcw₀ : c * w₀ = w₀ * c := by
    rcases hw₀w with rfl | rfl
    · rw [hcw, hwc]
    · calc c * (b * w) = (c * b) * w := (mul_assoc _ _ _).symm
        _ = (b * c) * w := by rw [hbc]
        _ = b * (c * w) := mul_assoc _ _ _
        _ = b * (w * c) := by rw [hcw, hwc]
        _ = (b * w) * c := (mul_assoc _ _ _).symm
  have hbw₀' : b * w₀ = w₀ * b := by
    rcases hw₀w with rfl | rfl
    · exact hbw
    · calc b * (b * w) = b * (w * b) := by rw [hbw]
        _ = (b * w) * b := (mul_assoc _ _ _).symm
  have hxA : IsConj a (x * w₀) := by
    rcases hw₀w with rfl | rfl
    · rw [hxw]
      have : c * x * c = c * x * c⁻¹ := by rw [hc']
      rw [this]
      exact C.isConj_x.trans (isConj_conj_self _ _)
    · have : x * (b * w) = c * (b * x) * c⁻¹ := by
        calc x * (b * w) = b * (x * w) := by rw [← mul_assoc, C.comm, mul_assoc]
          _ = b * (c * x * c) := by rw [hxw]
          _ = (b * c) * x * c := by group
          _ = (c * b) * x * c := by rw [hbc]
          _ = c * (b * x) * c⁻¹ := by rw [hc']; group
      rw [this]
      exact C.x_nbr.2.trans (isConj_conj_self _ _)
  have hcA : IsConj a (c * w₀) := by
    rcases hw₀w with rfl | rfl
    · rw [hcw]
      have : x * c * x = x * c * x⁻¹ := by rw [hx']
      rw [this]
      exact hc.1.1.trans (isConj_conj_self _ _)
    · have : c * (b * w) = x * (b * c) * x⁻¹ := by
        calc c * (b * w) = b * (c * w) := by rw [← mul_assoc, ← hbc, mul_assoc]
          _ = b * (x * c * x) := by rw [hcw]
          _ = (b * x) * c * x := by group
          _ = (x * b) * c * x := by rw [hbx]
          _ = x * (b * c) * x⁻¹ := by rw [hx']; group
      rw [this]
      exact hc.1.2.trans (isConj_conj_self _ _)
  have hxQ : x ∈ leechQ w₀ := C.two.mem_leechQ_of_isConj_mul C.isConj_x hw₀B hxw₀ hxA
  have hcQ : c ∈ leechQ w₀ := C.two.mem_leechQ_of_isConj_mul hc.1.1 hw₀B hcw₀ hcA
  have hbQ : b ∈ leechQ w₀ := C.two.mem_leechQ_of_isConj_mul C.isConj_b hw₀B hbw₀' hbw₀
  have hord : orderOf w₀ = 2 := (orderOf_eq_of_isConj hw₀B).symm.trans C.two.orderOf_z₀
  have hcomm := leechQ_commutator_mem_zpowers (C.two.gms w₀ hw₀B) hxQ hcQ
  rw [hx', hc'] at hcomm
  rw [show x * c * x * c = w from hxwc, mem_zpowers_iff_of_orderOf_eq_two hord] at hcomm
  rcases hcomm with h1 | h1
  · exact absurd h1 hw1
  · rcases hw₀w with h2 | h2
    · subst h2
      exact ⟨hw1, hw₀B, hww, hxQ, hcQ, hbQ⟩
    · exfalso
      rw [h2] at h1
      have : b = 1 := by
        have h3 : b * w = 1 * w := by rw [one_mul]; exact h1.symm
        exact mul_right_cancel h3
      exact ne_one_of_orderOf C.orderOf_b this

omit [Finite G] in
theorem orderOf_of_cond (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b)
    {K : TableVIClass} (h : tableVICond a z₀ b x K c) : orderOf (x * c) = tableVIOrder K := by
  cases K with
  | two_A => exact (orderOf_eq_of_isConj h).symm.trans C.two.orderOf_a
  | two_B => exact (orderOf_eq_of_isConj h).symm.trans C.two.orderOf_z₀
  | four_B =>
    have h2 : (x * c) * (x * c) = b := by rw [← pow_two]; exact h
    apply orderOf_eq_four_of_mul_self
    · rw [h2]
      exact ne_one_of_orderOf C.orderOf_b
    · rw [h2]
      exact C.bb
  | four_A => exact h.1
  | three_A => exact h
  | six_A =>
    exact orderOf_eq_six_of_pow_three C.bb (ne_one_of_orderOf C.orderOf_b) (C.xc_ne_one hc)
      (C.xc_ne_b hc) h

omit [Finite G] in
theorem cond_unique (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b)
    {K K' : TableVIClass} (h : tableVICond a z₀ b x K c) (h' : tableVICond a z₀ b x K' c) :
    K = K' := by
  have o := C.orderOf_of_cond hc h
  have o' := C.orderOf_of_cond hc h'
  have hnc : ¬ IsConj a z₀ := C.two.not_isConj
  cases K <;> cases K' <;> first
    | rfl
    | (exfalso; rw [o] at o'; norm_num [tableVIOrder] at o'; done)
    | (exfalso; exact hnc (h.trans h'.symm))
    | (exfalso; exact hnc (h'.trans h.symm))
    | (exfalso
       have h2 : IsConj z₀ b := by
         have : (x * c) ^ 2 = b := h
         rw [← this]
         exact h'.2
       exact hnc (C.isConj_b.trans h2.symm))
    | (exfalso
       have h2 : IsConj z₀ b := by
         have : (x * c) ^ 2 = b := h'
         rw [← this]
         exact h.2
       exact hnc (C.isConj_b.trans h2.symm))

theorem orbit_to_cond (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b)
    {k : Fin 4} (hk : BabyOrbit k (coverMap φ x) (coverMap φ c)) :
    ∃ K : TableVIClass, K.orbitIndex = k ∧ tableVICond a z₀ b x K c := by
  fin_cases k
  · obtain ⟨-, h | h⟩ := C.k0 hc hk
    · exact ⟨.two_B, rfl, h.1⟩
    · exact ⟨.two_A, rfl, h.1⟩
  · refine ⟨.four_B, rfl, ?_⟩
    show (x * c) ^ 2 = b
    rw [pow_two]
    exact C.k1 hc hk
  · rcases C.k2 hc hk with h | h
    · refine ⟨.three_A, rfl, ?_⟩
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime h (C.xc_ne_one hc)
    · exact ⟨.six_A, rfl, h⟩
  · obtain ⟨hw1, hwB, hww, -⟩ := C.k3_data hc hk
    refine ⟨.four_A, rfl, orderOf_eq_four_of_mul_self hw1 hww, ?_⟩
    rw [pow_two]
    exact hwB

theorem cond_to_orbit (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b)
    {K : TableVIClass} (h : tableVICond a z₀ b x K c) :
    BabyOrbit K.orbitIndex (coverMap φ x) (coverMap φ c) := by
  obtain ⟨k, hk⟩ := C.exists_orbit hc
  obtain ⟨K', hK', h'⟩ := C.orbit_to_cond hc hk
  have := C.cond_unique hc h h'
  subst this
  rw [hK']
  exact hk

theorem exists_cond (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    ∃ K : TableVIClass, tableVICond a z₀ b x K c := by
  obtain ⟨k, hk⟩ := C.exists_orbit hc
  obtain ⟨K, -, h⟩ := C.orbit_to_cond hc hk
  exact ⟨K, h⟩

omit [Finite G] in
theorem card_stab_dvd (C : TableVICtx a z₀ b₀ z u x b φ) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G)) ∣ tableVOrderB := by
  rw [← C.two.card_centralizer_inf_of_mem_twoANbr C.isConj_x C.mem_nbr]
  exact Subgroup.card_dvd_of_le fun g hg => ⟨hg.1.2, hg.1.1⟩

theorem card_stab_k0 (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b)
    (hk : BabyOrbit 0 (coverMap φ x) (coverMap φ c)) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G)) = tableVIStab .two_A := by
  have hxC := C.x_mem_centralizer
  have hcC := C.c_mem_centralizer hc
  obtain ⟨-, hc0, -⟩ := C.mem_tableVISet_iff.mp hc
  have hB := C.t4.card_inf_mul C.babyInv_x hc0 hk
  have hpair := card_inf_inf_mul_orbit C.cover hxC hcC
  set P := coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
    Subgroup.centralizer ({coverMap φ c} : Set B)) with hP
  have hj : {y : G | ∃ g ∈ P ⊓ Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = y}.ncard = 1 := by
    apply ncard_orbit_eq_one
    intro g hg
    obtain ⟨hgP, hgx⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨-, -, hgc⟩ := (mem_coverPre_inf_centralizer_iff C.cover hxC hcC).mp hgP
    rcases hgc with e | e
    · exact e
    · exfalso
      have hgx' : g * x * g⁻¹ = x := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hgx
        rw [hgx, mul_inv_cancel_right]
      have hconj : g * (x * c) * g⁻¹ = b * (x * c) := by
        calc g * (x * c) * g⁻¹ = (g * x * g⁻¹) * (g * c * g⁻¹) := conj_mul_conj g x c
          _ = x * (b * c) := by rw [hgx', e]
          _ = b * (x * c) := by rw [← mul_assoc, C.comm, mul_assoc]
      obtain ⟨-, hcase⟩ := C.k0 hc hk
      have hxc : IsConj (x * c) (b * (x * c)) := isConj_iff.mpr ⟨g, hconj⟩
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact C.two.not_isConj (h2.trans (hxc.symm.trans h1.symm))
      · exact C.two.not_isConj (h1.trans (hxc.trans h2.symm))
  have hsub : ∀ g ∈ P, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = b * x := fun g hg =>
    ((mem_coverPre_inf_centralizer_iff C.cover hxC hcC).mp hg).2.1
  have hdvd := C.card_stab_dvd (c := c)
  have hm : Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
      Subgroup.centralizer ({coverMap φ c} : Set B)) * tableVISize .two_A = tableVOrderB := by
    calc _ = Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
          Subgroup.centralizer ({coverMap φ c} : Set B)) * babyOrbitSize 0 := by
          simp [tableVISize, babyOrbitSize]
      _ = babyCentOrder 0 := hB
      _ = tableVOrderB := by simp [babyCentOrder, tableVOrderB]
  rw [hj] at hpair
  rcases ncard_orbit_eq_one_or_two C.cover.b_ne_one hsub with hi | hi
  · exfalso
    rw [hi] at hpair
    set n := Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G))
    set m := Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
      Subgroup.centralizer ({coverMap φ c} : Set B))
    have hn : n = 2 * m := by omega
    rw [hn, ← hm] at hdvd
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0] at hm
        norm_num [tableVOrderB, tableVISize] at hm
      · exact h0
    have h2 : m * 2 ∣ m * tableVISize .two_A := by
      rw [mul_comm m 2]
      exact hdvd
    have := Nat.dvd_of_mul_dvd_mul_left hmpos h2
    norm_num [tableVISize] at this
  · rw [hi] at hpair
    apply eq_tableVIStab_of_mul_size
    set n := Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G))
    set m := Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
      Subgroup.centralizer ({coverMap φ c} : Set B))
    have hn : n = m := by omega
    rw [hn]
    exact hm

theorem card_stab_k1 (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b)
    (hk : BabyOrbit 1 (coverMap φ x) (coverMap φ c)) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G)) = tableVIStab .four_B := by
  have hxC := C.x_mem_centralizer
  have hcC := C.c_mem_centralizer hc
  obtain ⟨-, hc0, -⟩ := C.mem_tableVISet_iff.mp hc
  have hB := C.t4.card_inf_mul C.babyInv_x hc0 hk
  have hpair := card_inf_inf_mul_orbit C.cover hxC hcC
  set P := coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
    Subgroup.centralizer ({coverMap φ c} : Set B)) with hP
  have hsq := C.k1 hc hk
  have hxx := C.xx
  have hcc := C.cc hc
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hcx : c * x * c⁻¹ = b * x := by
    have h1 : x * (c * x * c) = b := by rw [← hsq]; group
    calc c * x * c⁻¹ = c * x * c := by rw [hc']
      _ = x * (x * (c * x * c)) := by rw [← mul_assoc, hxx, one_mul]
      _ = x * b := by rw [h1]
      _ = b * x := C.comm
  have hxc : x * c * x⁻¹ = b * c := by
    calc x * c * x⁻¹ = x * c * x := by rw [hx']
      _ = ((x * c) * (x * c)) * c := by
          rw [show (x * c) * (x * c) * c = x * c * x * (c * c) by group, hcc, mul_one]
      _ = b * c := by rw [hsq]
  have hsub : ∀ g ∈ P, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = b * x := fun g hg =>
    ((mem_coverPre_inf_centralizer_iff C.cover hxC hcC).mp hg).2.1
  have hcP : c ∈ P := (mem_coverPre_inf_centralizer_iff C.cover hxC hcC).mpr
    ⟨hcC, Or.inr hcx, Or.inl (mul_inv_cancel_right c c)⟩
  have hxP : x ∈ P ⊓ Subgroup.centralizer ({x} : Set G) :=
    ⟨(mem_coverPre_inf_centralizer_iff C.cover hxC hcC).mpr
      ⟨hxC, Or.inl (mul_inv_cancel_right x x), Or.inr hxc⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hsub' : ∀ g ∈ P ⊓ Subgroup.centralizer ({x} : Set G),
      g * c * g⁻¹ = c ∨ g * c * g⁻¹ = b * c := fun g hg =>
    ((mem_coverPre_inf_centralizer_iff C.cover hxC hcC).mp (Subgroup.mem_inf.mp hg).1).2.2
  have hi := ncard_orbit_eq_two C.cover.b_ne_one hcP hcx hsub
  have hj := ncard_orbit_eq_two C.cover.b_ne_one hxP hxc hsub'
  rw [hi, hj] at hpair
  have hm : Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
      Subgroup.centralizer ({coverMap φ c} : Set B)) * 23113728 = tableVOrderB := by
    calc _ = Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
          Subgroup.centralizer ({coverMap φ c} : Set B)) * babyOrbitSize 1 := by
          simp [babyOrbitSize]
      _ = babyCentOrder 0 := hB
      _ = tableVOrderB := by simp [babyCentOrder, tableVOrderB]
  apply eq_tableVIStab_of_mul_size
  exact arith_four hpair hm

theorem card_stab_k2 (C : TableVICtx a z₀ b₀ z u x b φ) (hDC : DoubleCoverThreeSwap b)
    (hc : c ∈ tableVISet a x b) (hk : BabyOrbit 2 (coverMap φ x) (coverMap φ c)) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G)) = tableVIStab .three_A := by
  have hxC := C.x_mem_centralizer
  have hcC := C.c_mem_centralizer hc
  obtain ⟨-, hc0, -⟩ := C.mem_tableVISet_iff.mp hc
  have hB := C.t4.card_inf_mul C.babyInv_x hc0 hk
  have hpair := card_inf_inf_mul_orbit C.cover hxC hcC
  set P := coverPre φ (Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
    Subgroup.centralizer ({coverMap φ c} : Set B)) with hP
  have hsub : ∀ g ∈ P, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = b * x := fun g hg =>
    ((mem_coverPre_inf_centralizer_iff C.cover hxC hcC).mp hg).2.1
  obtain ⟨h, hhC, hhx, hhc⟩ := hDC φ C.cover.surjective C.cover.ker_eq ⟨x, hxC⟩ ⟨c, hcC⟩
    (by rw [← coverMap_apply hxC]; exact C.babyInv_x)
    (by rw [← coverMap_apply hcC]; exact hc0)
    (by rw [← coverMap_apply hxC, ← coverMap_apply hcC]; exact hk)
  have hhx' : h * x * h⁻¹ = b * x := by rw [hhx, C.comm]
  have hhc' : h * c * h⁻¹ = b * c := by rw [hhc, C.bc_comm hc]
  have hhP : h ∈ P := (mem_coverPre_inf_centralizer_iff C.cover hxC hcC).mpr
    ⟨hhC, Or.inr hhx', Or.inr hhc'⟩
  have hi := ncard_orbit_eq_two C.cover.b_ne_one hhP hhx' hsub
  have hj : {y : G | ∃ g ∈ P ⊓ Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = y}.ncard = 1 := by
    apply ncard_orbit_eq_one
    intro g hg
    obtain ⟨hgP, hgx⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨hgb, -, hgc⟩ := (mem_coverPre_inf_centralizer_iff C.cover hxC hcC).mp hgP
    rcases hgc with e | e
    · exact e
    · exfalso
      have hgx' : g * x * g⁻¹ = x := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hgx
        rw [hgx, mul_inv_cancel_right]
      have hconj : g * (x * c) * g⁻¹ = b * (x * c) := by
        calc g * (x * c) * g⁻¹ = (g * x * g⁻¹) * (g * c * g⁻¹) := conj_mul_conj g x c
          _ = x * (b * c) := by rw [hgx', e]
          _ = b * (x * c) := by rw [← mul_assoc, C.comm, mul_assoc]
      have hgbb : g * b * g⁻¹ = b := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hgb
        rw [hgb, mul_inv_cancel_right]
      have hcube : g * (x * c) ^ 3 * g⁻¹ = (x * c) ^ 3 := by
        rcases C.k2 hc hk with h3 | h3
        · rw [h3]
          simp
        · rw [h3]
          exact hgbb
      have hbc3 : (b * (x * c)) ^ 3 = b * (x * c) ^ 3 := by
        have hcomm : Commute b (x * c) := Commute.mul_right C.comm.symm (C.bc_comm hc)
        rw [hcomm.mul_pow, pow_succ, pow_two, C.bb, one_mul]
      have h4 : g * (x * c) ^ 3 * g⁻¹ = b * (x * c) ^ 3 := by rw [← hbc3, ← hconj, conj_pow]
      rw [hcube] at h4
      apply ne_one_of_orderOf C.orderOf_b
      apply mul_right_cancel (b := (x * c) ^ 3)
      rw [one_mul]
      exact h4.symm
  have hdvd := C.card_stab_dvd (c := c)
  rw [hi, hj] at hpair
  have hm : Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
      Subgroup.centralizer ({coverMap φ c} : Set B)) * 2370830336 = tableVOrderB := by
    calc _ = Nat.card ↥(Subgroup.centralizer ({coverMap φ x} : Set B) ⊓
          Subgroup.centralizer ({coverMap φ c} : Set B)) * babyOrbitSize 2 := by
          simp [babyOrbitSize]
      _ = babyCentOrder 0 := hB
      _ = tableVOrderB := by simp [babyCentOrder, tableVOrderB]
  apply eq_tableVIStab_of_mul_size
  exact arith_two hpair hm

theorem card_stab_k3 (C : TableVICtx a z₀ b₀ z u x b φ)
    (hLP : ∀ w : G, IsConj z₀ w → LeechPairData w) (hc : c ∈ tableVISet a x b)
    (hk : BabyOrbit 3 (coverMap φ x) (coverMap φ c)) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G)) = tableVIStab .four_A := by
  obtain ⟨hw1, hwB, hww, hxQ, hcQ, hbQ⟩ := C.k3_data hc hk
  have hLx := C.two.isLeechTwo_of_mem hwB hxQ C.isConj_x
  have hLc := C.two.isLeechTwo_of_mem hwB hcQ hc.1.1
  have hLb := C.two.isLeechTwo_of_mem hwB hbQ C.isConj_b
  have hLxb := C.two.isLeechTwo_of_mem hwB ((leechQ _).mul_mem hxQ hbQ) C.mem_nbr.2
  have hLbc := C.two.isLeechTwo_of_mem hwB ((leechQ _).mul_mem hbQ hcQ) hc.1.2
  have hcard := (hLP _ hwB).2.2 x c b hLx hLc hLb rfl hLxb hLbc
  have hEq : Subgroup.centralizer ({(x * c) * (x * c)} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G) =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G) := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨⟨-, hgx⟩, hgb⟩, hgc⟩
      exact ⟨⟨hgb, hgx⟩, hgc⟩
    · rintro ⟨⟨hgb, hgx⟩, hgc⟩
      have h1 : Commute g (x * c) := Commute.mul_right hgx hgc
      exact ⟨⟨⟨h1.mul_right h1, hgx⟩, hgb⟩, hgc⟩
  rw [hEq] at hcard
  exact hcard

theorem card_stab (C : TableVICtx a z₀ b₀ z u x b φ) (hDC : DoubleCoverThreeSwap b)
    (hLP : ∀ w : G, IsConj z₀ w → LeechPairData w) (hc : c ∈ tableVISet a x b)
    {K : TableVIClass} (h : tableVICond a z₀ b x K c) :
    Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G)) = tableVIStab K := by
  have hk := C.cond_to_orbit hc h
  cases K with
  | two_A => exact C.card_stab_k0 hc hk
  | two_B => exact C.card_stab_k0 hc hk
  | four_B => exact C.card_stab_k1 hc hk
  | four_A => exact C.card_stab_k3 hLP hc hk
  | three_A => exact C.card_stab_k2 hDC hc hk
  | six_A => exact C.card_stab_k2 hDC hc hk

omit [Finite G] in
theorem conj_mem {g : G}
    (hg : g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({b} : Set G))
    (hc : c ∈ tableVISet a x b) : g * c * g⁻¹ ∈ tableVISet a x b := by
  obtain ⟨hgx, hgb⟩ := Subgroup.mem_inf.mp hg
  have hgx' : g * x * g⁻¹ = x := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgx, mul_inv_cancel_right]
  have hgb' : g * b * g⁻¹ = b := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgb, mul_inv_cancel_right]
  refine ⟨⟨hc.1.1.trans (isConj_conj_self g c), ?_⟩, ?_, ?_⟩
  · rw [← conj_mul_of_mem_centralizer hgb c]
    exact hc.1.2.trans (isConj_conj_self g _)
  · intro e
    apply hc.2.1
    rw [← hgx'] at e
    exact mul_left_cancel (mul_right_cancel e)
  · intro e
    apply hc.2.2
    have : g * (x * b) * g⁻¹ = x * b := by
      rw [conj_mul_conj, hgx', hgb']
    rw [← this] at e
    exact mul_left_cancel (mul_right_cancel e)

omit [Finite G] in
theorem cond_conj {g : G}
    (hg : g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({b} : Set G))
    {K : TableVIClass} (h : tableVICond a z₀ b x K c) :
    tableVICond a z₀ b x K (g * c * g⁻¹) := by
  obtain ⟨hgx, hgb⟩ := Subgroup.mem_inf.mp hg
  have hgx' : g * x * g⁻¹ = x := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgx, mul_inv_cancel_right]
  have hgb' : g * b * g⁻¹ = b := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgb, mul_inv_cancel_right]
  have hxc : x * (g * c * g⁻¹) = g * (x * c) * g⁻¹ := by rw [conj_mul_conj, hgx']
  cases K with
  | two_A =>
    show IsConj a (x * (g * c * g⁻¹))
    rw [hxc]
    exact h.trans (isConj_conj_self g _)
  | two_B =>
    show IsConj z₀ (x * (g * c * g⁻¹))
    rw [hxc]
    exact h.trans (isConj_conj_self g _)
  | four_B =>
    show (x * (g * c * g⁻¹)) ^ 2 = b
    have h' : (x * c) ^ 2 = b := h
    rw [hxc, conj_pow, h', hgb']
  | four_A =>
    refine ⟨?_, ?_⟩
    · show orderOf (x * (g * c * g⁻¹)) = 4
      rw [hxc, orderOf_conj_eq]
      exact h.1
    · show IsConj z₀ ((x * (g * c * g⁻¹)) ^ 2)
      rw [hxc, conj_pow]
      exact h.2.trans (isConj_conj_self g _)
  | three_A =>
    show orderOf (x * (g * c * g⁻¹)) = 3
    rw [hxc, orderOf_conj_eq]
    exact h
  | six_A =>
    show (x * (g * c * g⁻¹)) ^ 3 = b
    have h' : (x * c) ^ 3 = b := h
    rw [hxc, conj_pow, h', hgb']

omit [Finite G] in
theorem bmul_mem (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    b * c ∈ tableVISet a x b := by
  refine ⟨⟨hc.1.2, ?_⟩, ?_, ?_⟩
  · rw [← mul_assoc, C.bb, one_mul]
    exact hc.1.1
  · intro e
    apply hc.2.2
    calc c = b * (b * c) := by rw [← mul_assoc, C.bb, one_mul]
      _ = b * x := by rw [e]
      _ = x * b := C.comm.symm
  · intro e
    apply hc.2.1
    rw [C.comm] at e
    exact mul_left_cancel e

theorem mem_preimage_iff (C : TableVICtx a z₀ b₀ z u x b φ) (k : Fin 4) :
    (c ∈ Subgroup.centralizer ({b} : Set G) ∧ coverMap φ c ∈
        {s : B | BabyInv 0 s ∧ BabyOrbit k (coverMap φ x) s}) ↔
      (c ∈ tableVISet a x b ∧ BabyOrbit k (coverMap φ x) (coverMap φ c)) := by
  constructor
  · rintro ⟨hcC, hc0, hk⟩
    refine ⟨C.mem_tableVISet_iff.mpr ⟨hcC, hc0, fun h => ?_⟩, hk⟩
    rw [h] at hk
    exact not_babyOrbit_self C.babyInv_x hk
  · rintro ⟨hc, hk⟩
    obtain ⟨hcC, hc0, -⟩ := C.mem_tableVISet_iff.mp hc
    exact ⟨hcC, hc0, hk⟩

theorem ncard_preimage_orbit (C : TableVICtx a z₀ b₀ z u x b φ) (k : Fin 4) :
    {c : G | c ∈ tableVISet a x b ∧ BabyOrbit k (coverMap φ x) (coverMap φ c)}.ncard =
      2 * babyOrbitSize k := by
  have h1 := ncard_coverMap_preimage C.cover
    {s : B | BabyInv 0 s ∧ BabyOrbit k (coverMap φ x) s}
  rw [(C.t4 _ C.babyInv_x).2.2 k] at h1
  rw [← h1]
  congr 1
  ext c
  exact (C.mem_preimage_iff k).symm

theorem ncard_class_eq_preimage (C : TableVICtx a z₀ b₀ z u x b φ) {K : TableVIClass}
    (hK : ∀ K' : TableVIClass, K'.orbitIndex = K.orbitIndex → K' = K) :
    tableVIOrbit a z₀ x b K =
      {c : G | c ∈ tableVISet a x b ∧ BabyOrbit K.orbitIndex (coverMap φ x) (coverMap φ c)} := by
  ext c
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, C.cond_to_orbit hc h⟩
  · rintro ⟨hc, hk⟩
    obtain ⟨K', hK', h'⟩ := C.orbit_to_cond hc hk
    rw [hK K' hK'] at h'
    exact ⟨hc, h'⟩

theorem ncard_four_B (C : TableVICtx a z₀ b₀ z u x b φ) :
    (tableVIOrbit a z₀ x b .four_B).ncard = 46227456 := by
  rw [C.ncard_class_eq_preimage (K := .four_B)
    (fun K' h => TableVIClass.orbitIndex_eq_one_iff.mp h)]
  exact (C.ncard_preimage_orbit 1).trans (by simp [babyOrbitSize])

theorem ncard_four_A (C : TableVICtx a z₀ b₀ z u x b φ) :
    (tableVIOrbit a z₀ x b .four_A).ncard = 22348085760 := by
  rw [C.ncard_class_eq_preimage (K := .four_A)
    (fun K' h => TableVIClass.orbitIndex_eq_three_iff.mp h)]
  exact (C.ncard_preimage_orbit 3).trans (by simp [babyOrbitSize])

omit [Finite G] in
theorem mul_b_mul (C : TableVICtx a z₀ b₀ z u x b φ) (c : G) : x * (b * c) = b * (x * c) := by
  rw [← mul_assoc, C.comm, mul_assoc]

theorem swap_two (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    (tableVICond a z₀ b x .two_A c → tableVICond a z₀ b x .two_B (b * c)) ∧
      (tableVICond a z₀ b x .two_B c → tableVICond a z₀ b x .two_A (b * c)) := by
  constructor
  · intro h
    obtain ⟨-, hcase⟩ := C.k0 hc (C.cond_to_orbit hc h)
    rcases hcase with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (h.trans h1.symm) C.two.not_isConj
    · show IsConj z₀ (x * (b * c))
      rw [C.mul_b_mul]
      exact h2
  · intro h
    obtain ⟨-, hcase⟩ := C.k0 hc (C.cond_to_orbit hc h)
    rcases hcase with ⟨-, h2⟩ | ⟨h1, -⟩
    · show IsConj a (x * (b * c))
      rw [C.mul_b_mul]
      exact h2
    · exact absurd (h1.trans h.symm) C.two.not_isConj

omit [Finite G] in
theorem swap_three (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    (tableVICond a z₀ b x .three_A c → tableVICond a z₀ b x .six_A (b * c)) ∧
      (tableVICond a z₀ b x .six_A c → tableVICond a z₀ b x .three_A (b * c)) := by
  have hcomm : Commute b (x * c) := Commute.mul_right C.comm.symm (C.bc_comm hc)
  have hb3 : b ^ 3 = b := by rw [pow_succ, pow_two, C.bb, one_mul]
  constructor
  · intro h
    have h3 : (x * c) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (x * c)
      rwa [show orderOf (x * c) = 3 from h] at this
    show (x * (b * c)) ^ 3 = b
    rw [C.mul_b_mul, hcomm.mul_pow, h3, hb3, mul_one]
  · intro h
    have h3 : (x * c) ^ 3 = b := h
    show orderOf (x * (b * c)) = 3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ (C.xc_ne_one (C.bmul_mem hc))
    rw [C.mul_b_mul, hcomm.mul_pow, h3, hb3, C.bb]

theorem ncard_two (C : TableVICtx a z₀ b₀ z u x b φ) :
    (tableVIOrbit a z₀ x b .two_A).ncard = 3968055 ∧
      (tableVIOrbit a z₀ x b .two_B).ncard = 3968055 := by
  have hF := C.ncard_preimage_orbit 0
  have hsplit := ncard_split (b := b) (A := tableVIOrbit a z₀ x b .two_A)
    (B' := tableVIOrbit a z₀ x b .two_B)
    (F := {c : G | c ∈ tableVISet a x b ∧ BabyOrbit 0 (coverMap φ x) (coverMap φ c)})
    (by
      ext c
      constructor
      · rintro ⟨hc, hk⟩
        obtain ⟨K, hK, h⟩ := C.orbit_to_cond hc hk
        rcases TableVIClass.orbitIndex_eq_zero_iff.mp hK with rfl | rfl
        · exact Or.inl ⟨hc, h⟩
        · exact Or.inr ⟨hc, h⟩
      · rintro (⟨hc, h⟩ | ⟨hc, h⟩)
        · exact ⟨hc, C.cond_to_orbit hc h⟩
        · exact ⟨hc, C.cond_to_orbit hc h⟩)
    (Set.disjoint_left.mpr fun c hA hB =>
      absurd (C.cond_unique hA.1 hA.2 hB.2) (by decide))
    (Set.toFinite _)
    (fun c hA => ⟨C.bmul_mem hA.1, (C.swap_two hA.1).1 hA.2⟩)
    (fun c hB => ⟨C.bmul_mem hB.1, (C.swap_two hB.1).2 hB.2⟩)
  have e : babyOrbitSize 0 = 3968055 := by simp [babyOrbitSize]
  rw [hF, e] at hsplit
  constructor <;> omega

theorem ncard_three (C : TableVICtx a z₀ b₀ z u x b φ) :
    (tableVIOrbit a z₀ x b .three_A).ncard = 2370830336 ∧
      (tableVIOrbit a z₀ x b .six_A).ncard = 2370830336 := by
  have hF := C.ncard_preimage_orbit 2
  have hsplit := ncard_split (b := b) (A := tableVIOrbit a z₀ x b .three_A)
    (B' := tableVIOrbit a z₀ x b .six_A)
    (F := {c : G | c ∈ tableVISet a x b ∧ BabyOrbit 2 (coverMap φ x) (coverMap φ c)})
    (by
      ext c
      constructor
      · rintro ⟨hc, hk⟩
        obtain ⟨K, hK, h⟩ := C.orbit_to_cond hc hk
        rcases TableVIClass.orbitIndex_eq_two_iff.mp hK with rfl | rfl
        · exact Or.inl ⟨hc, h⟩
        · exact Or.inr ⟨hc, h⟩
      · rintro (⟨hc, h⟩ | ⟨hc, h⟩)
        · exact ⟨hc, C.cond_to_orbit hc h⟩
        · exact ⟨hc, C.cond_to_orbit hc h⟩)
    (Set.disjoint_left.mpr fun c hA hB =>
      absurd (C.cond_unique hA.1 hA.2 hB.2) (by decide))
    (Set.toFinite _)
    (fun c hA => ⟨C.bmul_mem hA.1, (C.swap_three hA.1).1 hA.2⟩)
    (fun c hB => ⟨C.bmul_mem hB.1, (C.swap_three hB.1).2 hB.2⟩)
  have e : babyOrbitSize 2 = 2370830336 := by simp [babyOrbitSize]
  rw [hF, e] at hsplit
  constructor <;> omega

theorem ncard_orbit (C : TableVICtx a z₀ b₀ z u x b φ) (K : TableVIClass) :
    (tableVIOrbit a z₀ x b K).ncard = tableVISize K := by
  cases K with
  | two_A => exact C.ncard_two.1
  | two_B => exact C.ncard_two.2
  | four_B => exact C.ncard_four_B
  | four_A => exact C.ncard_four_A
  | three_A => exact C.ncard_three.1
  | six_A => exact C.ncard_three.2

theorem transitive (C : TableVICtx a z₀ b₀ z u x b φ) (hDC : DoubleCoverThreeSwap b)
    (hLP : ∀ w : G, IsConj z₀ w → LeechPairData w) {K : TableVIClass} {c c' : G}
    (hc : c ∈ tableVIOrbit a z₀ x b K) (hc' : c' ∈ tableVIOrbit a z₀ x b K) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({b} : Set G),
      g * c * g⁻¹ = c' := by
  have hstab := C.card_stab hDC hLP hc.1 hc.2
  have hH : Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) =
      tableVOrderB := by
    rw [inf_comm]
    exact C.two.card_centralizer_inf_of_mem_twoANbr C.isConj_x C.mem_nbr
  have horb := card_inf_centralizer_mul_orbit
    (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) c
  rw [hstab, hH] at horb
  have hord : {z : G | ∃ g ∈ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = z}.ncard = tableVISize K := by
    apply Nat.eq_of_mul_eq_mul_left (tableVIStab_pos K)
    rw [horb, tableVIStab_mul_size K]
  have hsub : {z : G | ∃ g ∈ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = z} ⊆ tableVIOrbit a z₀ x b K := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :=
      ⟨hg.2, hg.1⟩
    exact ⟨conj_mem hg' hc.1, cond_conj hg' hc.2⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hord, C.ncard_orbit K]) (Set.toFinite _)
  have hc'mem : c' ∈ {z : G | ∃ g ∈ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = z} := by
    rw [heq]
    exact hc'
  obtain ⟨g, hg, hgc⟩ := hc'mem
  exact ⟨g, ⟨hg.2, hg.1⟩, hgc⟩

end TableVICtx

end CtxFin

section Main

variable {G : Type} [Group G] [Finite G] {d₀ : B}

theorem exists_tableVICtx (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {x b : G} (hx : IsConj a x) (hb : b ∈ twoANbr a x) :
    ∃ (b₀ z u : G) (φ : Subgroup.centralizer ({b} : Set G) →* B),
      TableVICtx a z₀ b₀ z u x b φ := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨φ, hφ⟩ := (isTwoBabyCentralizer_of_isConj hSLS hG hb.1).exists_cover
  exact ⟨b₀, z, u, φ, ⟨h, hT3, hT4, hx, hb, hφ⟩⟩

theorem card_centralizer_inf_twoANbr
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x b : G} (hx : IsConj a x)
    (hb : b ∈ twoANbr a x) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)) =
      tableVOrderB := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  exact h.card_centralizer_inf_of_mem_twoANbr hx hb

theorem s341_classify
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x b c : G}
    (hx : IsConj a x) (hb : b ∈ twoANbr a x) (hc : c ∈ tableVISet a x b) :
    ∃! K : TableVIClass, tableVICond a z₀ b x K c := by
  obtain ⟨b₀, z, u, φ, C⟩ := exists_tableVICtx hSLS hTV hL hT3 hT4 hG hx hb
  obtain ⟨K, hK⟩ := C.exists_cond hc
  exact ⟨K, hK, fun K' hK' => C.cond_unique hc hK' hK⟩

theorem s341_transitive
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hT3 : BabyTableIII) (hT4 : BabyTableIV) (hDC : DoubleCoverThreeSwapIn G)
    (hLP : LeechPairStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x b : G} (hx : IsConj a x)
    (hb : b ∈ twoANbr a x) {K : TableVIClass} {c c' : G} (hc : c ∈ tableVIOrbit a z₀ x b K)
    (hc' : c' ∈ tableVIOrbit a z₀ x b K) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({b} : Set G),
      g * c * g⁻¹ = c' := by
  obtain ⟨b₀, z, u, φ, C⟩ := exists_tableVICtx hSLS hTV hL hT3 hT4 hG hx hb
  exact C.transitive (hDC b (isTwoBabyCentralizer_of_isConj hSLS hG hb.1))
    (fun w hw => hLP G w (C.two.gms w hw)) hc hc'

theorem s341_card
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hT3 : BabyTableIII) (hT4 : BabyTableIV) (hDC : DoubleCoverThreeSwapIn G)
    (hLP : LeechPairStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x b : G} (hx : IsConj a x)
    (hb : b ∈ twoANbr a x) {K : TableVIClass} {c : G} (hc : c ∈ tableVIOrbit a z₀ x b K) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G)) = tableVIStab K := by
  obtain ⟨b₀, z, u, φ, C⟩ := exists_tableVICtx hSLS hTV hL hT3 hT4 hG hx hb
  rw [inf_comm (Subgroup.centralizer ({x} : Set G))]
  exact C.card_stab (hDC b (isTwoBabyCentralizer_of_isConj hSLS hG hb.1))
    (fun w hw => hLP G w (C.two.gms w hw)) hc.1 hc.2

theorem s341_ncard
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x b : G}
    (hx : IsConj a x) (hb : b ∈ twoANbr a x) (K : TableVIClass) :
    (tableVIOrbit a z₀ x b K).ncard = tableVISize K := by
  obtain ⟨b₀, z, u, φ, C⟩ := exists_tableVICtx hSLS hTV hL hT3 hT4 hG hx hb
  exact C.ncard_orbit K

end Main

end CFSG.Monster.GMS
