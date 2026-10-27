module

public import CFSG.RankThree.PartTwo.KFacts.KP4Check
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.GH74.GLS.Basic
public import Certificates.Certificate18952

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP4

open Equiv Subgroup CFSG.Blueprint CFSG.ComponentClassification.WittDesign
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Asc83Table (permWord permWord_mem mem_normalizer_closure_of_conj_mem)
open CFSG.RankThree.Asc83Table.M22 (x y X Y E gens gens_mem x_mem y_mem)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)
open CFSG.RankThree.LocalRank (solvable_prime_complement_core_characterization)

abbrev G22 : Type := NativeSporadic.M22

theorem line_mem (i : Fin 4) : line i ∈ NativeSporadic.M22 := by
  fin_cases i
  · exact x_mem
  · exact y_mem
  · exact mul_mem x_mem y_mem
  · exact mul_mem x_mem (pow_mem y_mem 2)

theorem tw_mem (i : Fin 4) : tw i ∈ NativeSporadic.M22 := by
  fin_cases i
  · exact y_mem
  all_goals exact x_mem

theorem vA_eq_word : ∀ i : Fin 4, vA i = permWord gens (vAWord i) :=
  Certificates.certificate18952.1

theorem vA_mem (i : Fin 4) : vA i ∈ NativeSporadic.M22 :=
  (vA_eq_word i) ▸ permWord_mem gens_mem _

theorem vB_eq : ∀ i : Fin 4, vB i = (tw i)⁻¹ * vA i * tw i :=
  Certificates.certificate18952.2.1

theorem vB_mem (i : Fin 4) : vB i ∈ NativeSporadic.M22 := by
  rw [vB_eq]
  exact mul_mem (mul_mem (inv_mem (tw_mem i)) (vA_mem i)) (tw_mem i)

@[expose] def lineE (i : Fin 4) : G22 := ⟨line i, line_mem i⟩

@[expose] def vAE (i : Fin 4) : G22 := ⟨vA i, vA_mem i⟩

@[expose] def vBE (i : Fin 4) : G22 := ⟨vB i, vB_mem i⟩

theorem perm_facts : ∀ i : Fin 4,
    vA i * vA i = 1 ∧ vB i * vB i = 1 ∧ vA i * vB i = vB i * vA i ∧ vA i ≠ 1 ∧ vB i ≠ 1 ∧
      vA i ≠ vB i ∧ vA i * line i = line i * vA i ∧ vB i * line i = line i * vB i ∧
      line i ^ 3 = 1 ∧ line i ≠ 1 :=
  Certificates.certificate18952.2.2.1

theorem conj_facts :
    ∀ i : Fin 4, x * vA i * x⁻¹ = vElem i (conjIdx 0 i) ∧
    x * vB i * x⁻¹ = vElem i (conjIdx 1 i) ∧ y * vA i * y⁻¹ = vElem i (conjIdx 2 i) ∧
    y * vB i * y⁻¹ = vElem i (conjIdx 3 i) :=
  Certificates.certificate18952.2.2.2.1

theorem tw_facts :
    ∀ i : Fin 4, tw i * vA i * (tw i)⁻¹ = vA i * vB i ∧
    tw i * vB i * (tw i)⁻¹ = vA i ∧ (tw i = x ∨ tw i = y) :=
  Certificates.certificate18952.2.2.2.2.1

theorem ofTab_lineTab :
    ∀ i : Fin 4, ∀ p, ofTab (lineTab i) p = line i p :=
  Certificates.certificate18952.2.2.2.2.2.1

theorem coe_lineE (i : Fin 4) : ((lineE i : G22) : Perm (Fin 22)) = line i := rfl

theorem coe_vAE
    (i : Fin 4) : ((vAE i : G22) : Perm (Fin 22)) = vA i := rfl

theorem coe_vBE
    (i : Fin 4) : ((vBE i : G22) : Perm (Fin 22)) = vB i := rfl

theorem vAE_sq
    (i : Fin 4) : vAE i * vAE i = 1 := Subtype.ext (perm_facts i).1

theorem vBE_sq
    (i : Fin 4) : vBE i * vBE i = 1 := Subtype.ext (perm_facts i).2.1

theorem vAE_vBE_comm (i : Fin 4) : vAE i * vBE i = vBE i * vAE i :=
  Subtype.ext (perm_facts i).2.2.1

theorem vAE_ne_one (i : Fin 4) : vAE i ≠ 1 := fun h =>
  (perm_facts i).2.2.2.1 (congrArg Subtype.val h)

theorem vBE_ne_one (i : Fin 4) : vBE i ≠ 1 := fun h =>
  (perm_facts i).2.2.2.2.1 (congrArg Subtype.val h)

theorem vAE_ne_vBE (i : Fin 4) : vAE i ≠ vBE i := fun h =>
  (perm_facts i).2.2.2.2.2.1 (congrArg Subtype.val h)

theorem lineE_cube (i : Fin 4) : lineE i ^ 3 = 1 :=
  Subtype.ext (perm_facts i).2.2.2.2.2.2.2.2.1

theorem lineE_ne_one (i : Fin 4) : lineE i ≠ 1 := fun h =>
  (perm_facts i).2.2.2.2.2.2.2.2.2 (congrArg Subtype.val h)

theorem orderOf_lineE (i : Fin 4) : orderOf (lineE i) = 3 :=
  orderOf_eq_prime (lineE_cube i) (lineE_ne_one i)

noncomputable abbrev P0 : Subgroup G22 := E.sub

theorem card_P0 : Nat.card P0 = 9 := E.card

theorem X_mem_P0 : X ∈ P0 := subset_closure (Set.mem_insert _ _)

theorem Y_mem_P0 : Y ∈ P0 := subset_closure (Set.mem_insert_of_mem _ rfl)

theorem line_eq : ∀ i : Fin 4, line i = x ^ lineA i * y ^ lineB i :=
  Certificates.certificate18952.2.2.2.2.2.2.1

theorem lineE_eq
    (i : Fin 4) : lineE i = X ^ lineA i * Y ^ lineB i :=
  Subtype.ext (line_eq i)

theorem lineE_mem_P0 (i : Fin 4) : lineE i ∈ P0 := by
  rw [lineE_eq]
  exact P0.mul_mem (P0.pow_mem X_mem_P0 _) (P0.pow_mem Y_mem_P0 _)

theorem pow_mul_pow_cases :
    ∀ a b : Fin 3, (a, b) ≠ (0, 0) → ∃ i : Fin 4,
    x ^ (a : ℕ) * y ^ (b : ℕ) = line i ∨ x ^ (a : ℕ) * y ^ (b : ℕ) = line i ^ 2 :=
  Certificates.certificate18952.2.2.2.2.2.2.2

theorem exists_line_of_mem {c : G22} (hc : c ∈ P0) (hc1 : c ≠ 1) :
    ∃ i : Fin 4, c = lineE i ∨ c = lineE i ^ 2 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := E.exists_pow_mul_pow hc
  have hab : ((⟨a, ha⟩ : Fin 3), (⟨b, hb⟩ : Fin 3)) ≠ (0, 0) := by
    intro h
    simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_zero] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hc1 (by simp)
  obtain ⟨i, hi⟩ := pow_mul_pow_cases ⟨a, ha⟩ ⟨b, hb⟩ hab
  refine ⟨i, hi.imp (fun h => Subtype.ext ?_) (fun h => Subtype.ext ?_)⟩
  · exact h
  · exact h

theorem centralizer_sq_eq {G : Type*} [Group G] {u : G} (hu : u ^ 3 = 1) :
    centralizer ({u ^ 2} : Set G) = centralizer ({u} : Set G) := by
  have hu4 : (u ^ 2) ^ 2 = u := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hu, one_mul]
  ext g
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : g * (u ^ 2) ^ 2 = (u ^ 2) ^ 2 * g := by
      rw [sq, ← mul_assoc, h, mul_assoc, h, ← mul_assoc]
    rwa [hu4] at h'
  · intro h
    rw [sq, ← mul_assoc, h, mul_assoc, h, ← mul_assoc]

theorem exists_centralizer_eq
    {c : G22} (hc : c ∈ P0) (hc1 : c ≠ 1) :
    ∃ i : Fin 4, centralizer ({c} : Set G22) = centralizer ({lineE i} : Set G22) := by
  obtain ⟨i, rfl | rfl⟩ := exists_line_of_mem hc hc1
  · exact ⟨i, rfl⟩
  · exact ⟨i, centralizer_sq_eq (lineE_cube i)⟩

theorem zpowers_sq_eq {G : Type*} [Group G] {u : G} (hu : u ^ 3 = 1) :
    zpowers (u ^ 2) = zpowers u := by
  refine le_antisymm (zpowers_le.2 (pow_mem (mem_zpowers u) 2)) (zpowers_le.2 ?_)
  have h4 : (u ^ 2) ^ 2 = u := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hu, one_mul]
  have h : (u ^ 2) ^ 2 ∈ zpowers (u ^ 2) := pow_mem (mem_zpowers (u ^ 2)) 2
  rwa [h4] at h

theorem exists_zpowers_eq
    {C : Subgroup G22} (hC : C ≤ P0) (h3 : Nat.card C = 3) :
    ∃ i : Fin 4, C = zpowers (lineE i) := by
  have : Nontrivial C := Finite.one_lt_card_iff_nontrivial.1 (by rw [h3]; norm_num)
  obtain ⟨⟨c, hcC⟩, hc⟩ := exists_ne (1 : C)
  have hc1 : c ≠ 1 := fun h => hc (Subtype.ext h)
  have hCc : C = zpowers c := by
    have hle : zpowers c ≤ C := zpowers_le.2 hcC
    have hcard : Nat.card (zpowers c) = 3 := by
      rw [Nat.card_zpowers]
      have hcC3 : c ^ 3 = 1 := by
        have := pow_card_eq_one' (G := C) (x := ⟨c, hcC⟩)
        rw [h3] at this
        exact congrArg Subtype.val this
      exact orderOf_eq_prime hcC3 hc1
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h3])).symm
  obtain ⟨i, rfl | rfl⟩ := exists_line_of_mem (hC hcC) hc1
  · exact ⟨i, hCc⟩
  · exact ⟨i, hCc.trans (zpowers_sq_eq (lineE_cube i))⟩

@[expose] def V (i : Fin 4) : Subgroup G22 :=
  FourGroup.kleinFourOf (vAE i) (vBE i) (vAE_sq i) (vBE_sq i) (vAE_vBE_comm i)

theorem mem_V_iff {i : Fin 4} {g : G22} :
    g ∈ V i ↔ g = 1 ∨ g = vAE i ∨ g = vBE i ∨ g = vAE i * vBE i :=
  Iff.rfl

theorem card_V (i : Fin 4) : Nat.card (V i) = 4 :=
  FourGroup.card_kleinFourOf (vAE_ne_one i) (vBE_ne_one i) (vAE_ne_vBE i)

theorem isElementaryAbelian_V
    (i : Fin 4) : IsElementaryAbelian 2 (V i) :=
  FourGroup.isElementaryAbelian_kleinFourOf

theorem V_eq_closure
    (i : Fin 4) : closure ({vAE i, vBE i} : Set G22) = V i := by
  refine le_antisymm ?_ (FourGroup.kleinFourOf_le (subset_closure (Set.mem_insert _ _))
    (subset_closure (Set.mem_insert_of_mem _ rfl)))
  rw [closure_le]
  rintro _ (rfl | rfl)
  · exact FourGroup.left_mem_kleinFourOf
  · exact FourGroup.right_mem_kleinFourOf

theorem sq_eq_one_of_mem_V
    {i : Fin 4} {g : G22} (hg : g ∈ V i) : g * g = 1 := by
  rcases mem_V_iff.1 hg with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact vAE_sq i
  · exact vBE_sq i
  · rw [show vAE i * vBE i * (vAE i * vBE i) = vAE i * (vBE i * vAE i) * vBE i by group,
      ← vAE_vBE_comm, show vAE i * (vAE i * vBE i) * vBE i = (vAE i * vAE i) * (vBE i * vBE i)
      by group, vAE_sq, vBE_sq, one_mul]

theorem V_le_centralizer
    (i : Fin 4) : V i ≤ centralizer ({lineE i} : Set G22) := by
  rw [← V_eq_closure, closure_le]
  rintro _ (rfl | rfl)
  · exact mem_centralizer_singleton_iff.2 (Subtype.ext (perm_facts i).2.2.2.2.2.2.1)
  · exact mem_centralizer_singleton_iff.2 (Subtype.ext (perm_facts i).2.2.2.2.2.2.2.1)

theorem vElem_mem
    (i k : Fin 4) {g : G22} (hg : (g : Perm (Fin 22)) = vElem i k) : g ∈ V i := by
  rw [mem_V_iff]
  fin_cases k
  · exact Or.inl (Subtype.ext hg)
  · exact Or.inr (Or.inl (Subtype.ext hg))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext hg)))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext hg)))

theorem X_mem_normalizer_V
    (i : Fin 4) : X ∈ normalizer (V i : Set G22) := by
  rw [← V_eq_closure]
  refine mem_normalizer_closure_of_conj_mem ?_
  rw [V_eq_closure]
  rintro _ (rfl | rfl)
  · exact vElem_mem i _ (conj_facts i).1
  · exact vElem_mem i _ (conj_facts i).2.1

theorem Y_mem_normalizer_V
    (i : Fin 4) : Y ∈ normalizer (V i : Set G22) := by
  rw [← V_eq_closure]
  refine mem_normalizer_closure_of_conj_mem ?_
  rw [V_eq_closure]
  rintro _ (rfl | rfl)
  · exact vElem_mem i _ (conj_facts i).2.2.1
  · exact vElem_mem i _ (conj_facts i).2.2.2

theorem P0_le_normalizer_V
    (i : Fin 4) : P0 ≤ normalizer (V i : Set G22) := by
  rw [closure_le]
  rintro _ (rfl | rfl)
  · exact X_mem_normalizer_V i
  · exact Y_mem_normalizer_V i

theorem exists_tw
    (i : Fin 4) : ∃ t ∈ P0, t * vAE i * t⁻¹ = vAE i * vBE i ∧
    t * vBE i * t⁻¹ = vAE i := by
  obtain ⟨h1, h2, h3⟩ := tw_facts i
  rcases h3 with h3 | h3
  · refine ⟨X, X_mem_P0, Subtype.ext ?_, Subtype.ext ?_⟩
    · change x * vA i * x⁻¹ = vA i * vB i
      rw [← h3]; exact h1
    · change x * vB i * x⁻¹ = vA i
      rw [← h3]; exact h2
  · refine ⟨Y, Y_mem_P0, Subtype.ext ?_, Subtype.ext ?_⟩
    · change y * vA i * y⁻¹ = vA i * vB i
      rw [← h3]; exact h1
    · change y * vB i * y⁻¹ = vA i
      rw [← h3]; exact h2

theorem V_minimal (i : Fin 4) {W : Subgroup G22} (hW : W ≤ V i)
    (hP : P0 ≤ normalizer (W : Set G22)) : W = ⊥ ∨ W = V i := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  obtain ⟨t, htP, ht1, ht2⟩ := exists_tw i
  have hconj : ∀ w ∈ W, t * w * t⁻¹ ∈ W := fun w hw =>
    (mem_normalizer_iff.1 (hP htP) w).1 hw
  have hA : vAE i ∈ W ∧ vBE i ∈ W := by
    have hg := hW g.2
    rw [mem_V_iff] at hg
    rcases hg with h | h | h | h
    · exact absurd (Subtype.ext h) hg1
    · have hA : vAE i ∈ W := h ▸ g.2
      have hAB := hconj _ hA
      rw [ht1] at hAB
      refine ⟨hA, ?_⟩
      have := W.mul_mem (W.inv_mem hA) hAB
      rwa [inv_mul_cancel_left] at this
    · have hB : vBE i ∈ W := h ▸ g.2
      have hA := hconj _ hB
      rw [ht2] at hA
      exact ⟨hA, hB⟩
    · have hAB : vAE i * vBE i ∈ W := h ▸ g.2
      have h2 : vAE i * vBE i * vAE i ∈ W := by
        have := hconj _ hAB
        rwa [show t * (vAE i * vBE i) * t⁻¹ = (t * vAE i * t⁻¹) * (t * vBE i * t⁻¹) by group,
          ht1, ht2] at this
      have hA : vAE i ∈ W := by
        have := W.mul_mem (W.inv_mem hAB) h2
        rwa [inv_mul_cancel_left] at this
      have hB : vBE i ∈ W := by
        have := W.mul_mem (W.inv_mem hA) hAB
        rwa [inv_mul_cancel_left] at this
      exact ⟨hA, hB⟩
  refine le_antisymm hW ?_
  rw [← V_eq_closure, closure_le]
  rintro _ (rfl | rfl)
  · exact hA.1
  · exact hA.2

theorem mem_centralizer_line_iff (i : Fin 4) (g : G22) :
    g ∈ centralizer ({lineE i} : Set G22) ↔
      ∀ p, (g : Perm (Fin 22)) (ofTab (lineTab i) p) =
        ofTab (lineTab i) ((g : Perm (Fin 22)) p) := by
  rw [mem_centralizer_singleton_iff]
  simp only [ofTab_lineTab]
  constructor
  · intro h p
    exact congrArg (fun σ : G22 => (σ : Perm (Fin 22)) p) h
  · intro h
    exact Subtype.ext (Equiv.ext h)

theorem pow_four_iff (g : G22) :
    g ^ 4 = 1 ↔ ∀ p, (g : Perm (Fin 22)) ((g : Perm (Fin 22)) ((g : Perm (Fin 22))
      ((g : Perm (Fin 22)) p))) = p := by
  rw [Subtype.ext_iff, Equiv.ext_iff]
  simp [pow_succ, Equiv.Perm.mul_apply]

theorem card_centralizer_line
    (i : Fin 4) :
    Nat.card (centralizer ({lineE i} : Set G22)) = 36 := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_centralizer_line_iff i g)).trans
    ((card_m22_subtype _).trans (kp4_counts.1 i))

theorem card_pow_four
    (i : Fin 4) :
    Nat.card {g : G22 // g ∈ centralizer ({lineE i} : Set G22) ∧ g ^ 4 = 1} = 4 := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun g => and_congr
    (mem_centralizer_line_iff i g) (pow_four_iff g))).trans
    ((card_m22_subtype _).trans (kp4_counts.2.1 i))

theorem mem_V_of_pow_four
    {i : Fin 4} {g : G22} (hg : g ∈ centralizer ({lineE i} : Set G22))
    (h4 : g ^ 4 = 1) : g ∈ V i := by
  let f : V i → {g : G22 // g ∈ centralizer ({lineE i} : Set G22) ∧ g ^ 4 = 1} :=
    fun v => ⟨v, V_le_centralizer i v.2, by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq (v : G22), sq_eq_one_of_mem_V v.2, one_pow]⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg (fun z : {g : G22 // _} => (z : G22)) h)
  have hbij := hf.bijective_of_nat_card_le (by rw [card_V, card_pow_four])
  obtain ⟨v, hv⟩ := hbij.2 ⟨g, hg, h4⟩
  have : (v : G22) = g := congrArg (fun z : {g : G22 // _} => (z : G22)) hv
  exact this ▸ v.2

theorem pow_four_of_not_dvd
    {i : Fin 4} {g : G22} (hg : g ∈ centralizer ({lineE i} : Set G22))
    (h3 : ¬ 3 ∣ orderOf g) : g ^ 4 = 1 := by
  have hdvd : orderOf g ∣ 36 := by
    rw [← card_centralizer_line i, ← Subgroup.orderOf_mk g hg]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf g) (3 ^ 2) :=
    Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  have h4 : orderOf g ∣ 4 := hcop.dvd_of_dvd_mul_right (show orderOf g ∣ 4 * 3 ^ 2 from hdvd)
  exact orderOf_dvd_iff_pow_eq_one.1 h4

theorem le_V_of_not_dvd
    {i : Fin 4} {K : Subgroup G22}
    (hK : K ≤ centralizer ({lineE i} : Set G22)) (h3 : ¬ 3 ∣ Nat.card K) : K ≤ V i := by
  intro g hg
  refine mem_V_of_pow_four (hK hg) (pow_four_of_not_dvd (hK hg) fun h => h3 ?_)
  exact h.trans (by rw [← Subgroup.orderOf_mk g hg]; exact orderOf_dvd_natCard _)

theorem not_three_dvd_card_V
    (i : Fin 4) : ¬ 3 ∣ Nat.card (V i) := by
  rw [card_V]
  norm_num

theorem conj_mem_V
    {i : Fin 4} {c g : G22} (hc : c ∈ centralizer ({lineE i} : Set G22))
    (hg : g ∈ V i) : c * g * c⁻¹ ∈ V i := by
  have hgC := V_le_centralizer i hg
  refine mem_V_of_pow_four (mul_mem (mul_mem hc hgC) (inv_mem hc)) ?_
  rw [conj_pow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq g, sq_eq_one_of_mem_V hg, one_pow,
    mul_one, mul_inv_cancel]

theorem normal_V_subgroupOf
    (i : Fin 4) :
    ((V i).subgroupOf (centralizer ({lineE i} : Set G22))).Normal := by
  refine ⟨fun a ha c => ?_⟩
  rw [mem_subgroupOf] at ha ⊢
  exact conj_mem_V c.2 ha

theorem card_V_subgroupOf (i : Fin 4) :
    Nat.card ((V i).subgroupOf (centralizer ({lineE i} : Set G22))) = 4 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (V_le_centralizer i)).toEquiv, card_V]

theorem mem_V_of_mem_subgroup
    {i : Fin 4} {K : Subgroup (centralizer ({lineE i} : Set G22))}
    (h3 : ¬ 3 ∣ Nat.card K) {g : centralizer ({lineE i} : Set G22)} (hg : g ∈ K) :
    (g : G22) ∈ V i := by
  have hle := le_V_of_not_dvd (K := K.map (centralizer ({lineE i} : Set G22)).subtype)
    (map_subtype_le K) (by rwa [Subgroup.card_map_of_injective (subtype_injective _)])
  exact hle (mem_map_of_mem _ hg)

theorem pCore_centralizer_line
    (i : Fin 4) :
    inSubgroup (CFSG.pCore 2) (centralizer ({lineE i} : Set G22)) = V i := by
  set C := centralizer ({lineE i} : Set G22)
  unfold inSubgroup
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    refine mem_V_of_mem_subgroup (K := CFSG.pCore 2 C) ?_ hg
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := C))
    rw [hk]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  · intro g hg
    have hgC : g ∈ C := V_le_centralizer i hg
    have hmem : (V i).subgroupOf C ∈ {K : Subgroup C | K.Normal ∧ IsPGroup 2 K} :=
      ⟨normal_V_subgroupOf i, IsPGroup.of_card (n := 2) (by rw [card_V_subgroupOf]; norm_num)⟩
    exact Subgroup.mem_map.2 ⟨⟨g, hgC⟩,
      le_sSup hmem (show (⟨g, hgC⟩ : C) ∈ (V i).subgroupOf C from hg), rfl⟩

theorem theta_centralizer_line
    (i : Fin 4) :
    inSubgroup (aschbacherSolvableCore 3) (centralizer ({lineE i} : Set G22)) = V i := by
  set C := centralizer ({lineE i} : Set G22)
  obtain ⟨-, -, h3, hmax, -⟩ := solvable_prime_complement_core_characterization (H := C)
    Nat.prime_three
  unfold inSubgroup
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact mem_V_of_mem_subgroup h3 hg
  · intro g hg
    have hgC : g ∈ C := V_le_centralizer i hg
    have hP : IsPGroup 2 ((V i).subgroupOf C) :=
      IsPGroup.of_card (n := 2) (by rw [card_V_subgroupOf]; norm_num)
    have hsolv : Group.IsSolvable ((V i).subgroupOf C) := by
      have := hP.isNilpotent
      infer_instance
    exact ⟨⟨g, hgC⟩, hmax _ (normal_V_subgroupOf i) hsolv
      (by rw [card_V_subgroupOf]; norm_num) (show (⟨g, hgC⟩ : C) ∈ (V i).subgroupOf C from hg),
      rfl⟩

theorem pPrimeCoreOf_centralizer_line
    (i : Fin 4) :
    CFSG.GH74.GLS.pPrimeCoreOf 3 (centralizer ({lineE i} : Set G22)) = V i := by
  set C := centralizer ({lineE i} : Set G22)
  unfold CFSG.GH74.GLS.pPrimeCoreOf
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    refine mem_V_of_mem_subgroup (K := CFSG.pPrimeCore 3 C) ?_ hg
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  · intro g hg
    have hgC : g ∈ C := V_le_centralizer i hg
    have hmem : (V i).subgroupOf C ∈
        {K : Subgroup C | K.Normal ∧ Nat.Coprime 3 (Nat.card K)} :=
      ⟨normal_V_subgroupOf i, by rw [card_V_subgroupOf]; norm_num⟩
    exact Subgroup.mem_map.2 ⟨⟨g, hgC⟩,
      le_sSup hmem (show (⟨g, hgC⟩ : C) ∈ (V i).subgroupOf C from hg), rfl⟩

end CFSG.RankThree.PartTwo.KFacts.KP4
