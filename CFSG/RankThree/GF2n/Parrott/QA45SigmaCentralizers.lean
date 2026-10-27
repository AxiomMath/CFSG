module

public import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses
public import CFSG.RankThree.GF2n.Parrott.QA45ListGroups
public import CFSG.GroupTheory.ConjClassCover
public import CFSG.GroupTheory.ElementaryAbelianBasis
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.Sporadic.Recognition.LyonsAS44Quat

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups
open CFSG.Open
open CFSG.Sporadic.Schreier (tab tab_eq)

local notation "P45" => Equiv.Perm (Fin 45)

private theorem nonempty_mulEquiv_quaternionGroup_two_closure {G : Type*} [Group G] [Finite G]
    {a b : G} (hcard : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = 8) (ha4 : a ^ 4 = 1)
    (ha2 : a ^ 2 ≠ 1) (hba : b * a * b⁻¹ = a⁻¹) (hb2 : b ^ 2 = a ^ 2) :
    Nonempty (↥(Subgroup.closure ({a, b} : Set G)) ≃* QuaternionGroup 2) :=
  CFSG.Sporadic.Recognition.LyonsSims.nonempty_mulEquiv_quaternionGroup_two hcard
    ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩
    ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
    (Subtype.ext (by simpa using ha4)) (fun h => ha2 (by simpa using congrArg Subtype.val h))
    (Subtype.ext (by simpa using hba)) (Subtype.ext (by simpa using hb2))

private theorem nonempty_mulEquiv_dihedralGroup_four_of_elems {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (s r : G) (hs : s * s = 1) (hr2 : r * r ≠ 1) (hr4 : r * r * (r * r) = 1)
    (hsr : s * r * s⁻¹ = r⁻¹) (hsH : s ∈ H) (hrH : r ∈ H)
    (hH : ∀ x ∈ H, x = 1 ∨ x = r ∨ x = r * r ∨ x = r * r * r ∨ x = s ∨ x = s * r ∨
      x = s * (r * r) ∨ x = s * (r * r * r))
    (hs1 : s ≠ 1) (hs3 : s ≠ r) (hs4 : s ≠ r * r) (hs5 : s ≠ r * r * r) :
    Nonempty (↥H ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥H, (ρ : G) = r := ⟨⟨r, hrH⟩, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥H, (σ : G) = s := ⟨⟨s, hsH⟩, rfl⟩
  have hρ2 : ρ ^ 2 ≠ 1 := fun h => hr2 (by
    have := congrArg Subtype.val h
    simpa [sq, hρ] using this)
  have hρ4 : ρ ^ 4 = 1 := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hρ]
    calc r ^ 4 = r * r * (r * r) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hr4
  have hord : orderOf ρ = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ρ) (by simpa using hρ2)
      (by simpa using hρ4)
    simpa using h
  have hρS : ρ ∈ Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers ρ)
  have hσS : σ ∈ Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
  have hgen : (⊤ : Subgroup ↥H) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    refine (eq_top_iff.2 fun x _ => ?_).symm
    rcases hH x.1 x.2 with h | h | h | h | h | h | h | h
    · obtain rfl : x = 1 := Subtype.ext h
      exact one_mem _
    · obtain rfl : x = ρ := Subtype.ext (h.trans hρ.symm)
      exact hρS
    · obtain rfl : x = ρ * ρ := Subtype.ext (by simp [h, hρ])
      exact mul_mem hρS hρS
    · obtain rfl : x = ρ * ρ * ρ := Subtype.ext (by simp [h, hρ])
      exact mul_mem (mul_mem hρS hρS) hρS
    · obtain rfl : x = σ := Subtype.ext (h.trans hσ.symm)
      exact hσS
    · obtain rfl : x = σ * ρ := Subtype.ext (by simp [h, hρ, hσ])
      exact mul_mem hσS hρS
    · obtain rfl : x = σ * (ρ * ρ) := Subtype.ext (by simp [h, hρ, hσ])
      exact mul_mem hσS (mul_mem hρS hρS)
    · obtain rfl : x = σ * (ρ * ρ * ρ) := Subtype.ext (by simp [h, hρ, hσ])
      exact mul_mem hσS (mul_mem (mul_mem hρS hρS) hρS)
  have hσ2 : σ ^ 2 = 1 := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hσ]
    rw [sq]
    exact hs
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ, hρ]
    exact hsr
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro h
    rw [CFSG.GroupTheory.mem_zpowers_four_iff hord] at h
    rcases h with h | h | h | h
    · exact hs1 (by simpa [hσ] using congrArg Subtype.val h)
    · exact hs3 (by simpa [hσ, hρ] using congrArg Subtype.val h)
    · exact hs4 (by simpa [hσ, hρ] using congrArg Subtype.val h)
    · exact hs5 (by simpa [hσ, hρ] using congrArg Subtype.val h)
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  rwa [hord] at h

private theorem conj_eq_inv_mul_of_involutions {G : Type*} [Group G] {s w : G} (hs : s * s = 1)
    (hw : w * w = 1) : s * (s * w) * s⁻¹ = (s * w)⁻¹ := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  rw [mul_inv_rev, hs', hw', ← mul_assoc, hs, one_mul]

private theorem commute_mul_of_swap {G : Type*} [Group G] {u a b : G} (hu : u * u = 1)
    (h1 : u * a * u⁻¹ = b) (hab : a * b = b * a) : u * (a * b) = (a * b) * u := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  rw [hu'] at h1
  have h2 : u * a = b * u :=
    calc u * a = (u * a * u) * u := by rw [mul_assoc (u * a), hu, mul_one]
      _ = b * u := by rw [h1]
  have h3 : u * b = a * u :=
    calc u * b = u * (u * a * u) := by rw [h1]
      _ = (u * u) * a * u := by simp only [mul_assoc]
      _ = a * u := by rw [hu, one_mul]
  calc u * (a * b) = (u * a) * b := (mul_assoc _ _ _).symm
    _ = b * (u * b) := by rw [h2, mul_assoc]
    _ = b * (a * u) := by rw [h3]
    _ = (b * a) * u := (mul_assoc _ _ _).symm
    _ = (a * b) * u := by rw [hab]


private theorem d8CenterCheck_spec (h : d8CenterCheck () = true) :
    ∀ x ∈ D8list (), (∀ g ∈ D8gens, x * g = g * x) → x = 1 ∨ x = u * t := by
  intro x hx hc
  have h1 := List.all_eq_true.1 h x hx
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, tabList_eq, tab_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exfalso
    have hall : D8gens.all (fun g => decide (x * g = g * x)) = true :=
      List.all_eq_true.2 fun g hg => decide_eq_true (hc g hg)
    rw [hall] at h1
    exact Bool.noConfusion h1
  · exact Or.inl h1
  · exact Or.inr h1


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "a2A" => (⟨alpha2, alpha2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "b2A" => (⟨beta2, beta2_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "bA" => (⟨beta, beta_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

private theorem card_centralizer_s1s2 :
    Nat.card (Subgroup.centralizer ({s1A * s2A} : Set A45)) = 216 := by
  have hm : sigma1 * sigma2 ∈ QA45.originalSubgroup :=
    QA45.originalSubgroup.mul_mem sigma1_mem_A sigma2_mem_A
  exact (card_centralizer_QA45_eq_filter (sigma1 * sigma2) hm).trans
    Certificates.certificate946005.centralizer_sigma1sigma2

private theorem card_centralizer_s1s2inv :
    Nat.card (Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45)) = 108 := by
  have hm : sigma1 * sigma2⁻¹ ∈ QA45.originalSubgroup :=
    QA45.originalSubgroup.mul_mem sigma1_mem_A (QA45.originalSubgroup.inv_mem sigma2_mem_A)
  exact (card_centralizer_QA45_eq_filter (sigma1 * sigma2⁻¹) hm).trans
    Certificates.certificate946005.centralizer_sigma1sigma2inv

theorem qa45_orderThree_subgroup_classes :
    ∀ P : Subgroup A45, Nat.card P = 3 →
      QA45SubgroupConj P (Subgroup.zpowers s1A) ∨
      QA45SubgroupConj P (Subgroup.zpowers (s1A * s2A)) ∨
      QA45SubgroupConj P (Subgroup.zpowers (s1A * s2A⁻¹)) := by
  intro P hP
  have hA : Nat.card A45 = 51840 := card_QA45
  obtain ⟨x, hPx, hx3⟩ := CFSG.GroupTheory.exists_zpowers_eq_of_card_eq_prime Nat.prime_three hP
  let s : Set A45 := {y | y * y * y = 1 ∧ y ≠ 1}
  have hs : ∀ y z : A45, IsConj y z → z ∈ s → y ∈ s := by
    intro y z hyz hz
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨?_, fun h1 => hz2 (isConj_one_right.1 (h1 ▸ hyz))⟩
    have h3 : IsConj (y ^ 3) (z ^ 3) := hyz.pow 3
    rw [pow_three' z, hz1] at h3
    rw [← pow_three']
    exact isConj_one_left.1 h3
  have hmem : x ∈ s := by
    refine ⟨?_, ?_⟩
    · have h3 : x ^ 3 = 1 := by
        rw [← hx3]
        exact pow_orderOf_eq_one x
      rwa [pow_three'] at h3
    · intro h1
      rw [h1, orderOf_one] at hx3
      omega
  have hscard : s.ncard = 800 := by
    rw [← Nat.card_coe_set_eq, ← qa45L1Facts.card_order_three, orderThreeCount]
    have h := card_filter QA45 QA45_ok
      (p := fun g : Equiv.Perm (Fin 45) => g * g * g = 1 ∧ g ≠ 1)
    rw [← h]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    simp only [s, Set.mem_setOf_eq, ne_eq, Subtype.ext_iff, Subgroup.coe_mul,
      Subgroup.coe_one]
  have ha3 : s1A ^ 3 = 1 := by
    have := pow_orderOf_eq_one s1A
    rwa [orderOf_sigma1_subtype] at this
  have hb3 : s2A ^ 3 = 1 := by
    have := pow_orderOf_eq_one s2A
    rwa [orderOf_sigma2_subtype] at this
  have hc : s1A * s2A = s2A * s1A := Subtype.ext sigma1_commute_sigma2
  have hc' : s1A * s2A⁻¹ = s2A⁻¹ * s1A := (Commute.inv_right hc).eq
  let r : Fin 3 → A45 := ![s1A, s1A * s2A, s1A * s2A⁻¹]
  have hcard : ∀ i, Nat.card (Subgroup.centralizer ({r i} : Set A45)) = ![648, 216, 108] i := by
    intro i
    fin_cases i
    · exact card_centralizer_sigma1_QA45
    · exact card_centralizer_s1s2
    · exact card_centralizer_s1s2inv
  have hne : ∀ i j, i ≠ j → Nat.card (Subgroup.centralizer ({r i} : Set A45)) ≠
      Nat.card (Subgroup.centralizer ({r j} : Set A45)) := by
    intro i j hij
    rw [hcard, hcard]
    revert i j
    decide
  have hr1 : ∀ i, r i ≠ 1 := by
    intro i
    refine CFSG.GroupTheory.ne_one_of_card_centralizer_ne ?_
    rw [hcard i, hA]
    revert i
    decide
  have hr : ∀ i, r i ∈ s := by
    intro i
    refine ⟨?_, hr1 i⟩
    fin_cases i
    · show s1A * s1A * s1A = 1
      rw [← pow_three']
      exact ha3
    · show (s1A * s2A) * (s1A * s2A) * (s1A * s2A) = 1
      rw [← pow_three', Commute.mul_pow hc 3, ha3, hb3, one_mul]
    · show (s1A * s2A⁻¹) * (s1A * s2A⁻¹) * (s1A * s2A⁻¹) = 1
      rw [← pow_three', Commute.mul_pow (Commute.inv_right hc) 3, ha3, inv_pow, hb3, inv_one,
        one_mul]
  have hsum : ∑ i, Nat.card A45 / Nat.card (Subgroup.centralizer ({r i} : Set A45)) =
      s.ncard := by
    simp only [hcard, hA, hscard, Fin.sum_univ_three]
    norm_num
  obtain ⟨i, hi⟩ := CFSG.GroupTheory.exists_isConj_of_sum_eq r s hs hr hne hsum x hmem
  obtain ⟨c, hc⟩ := isConj_iff.1 hi
  have hconj : QA45SubgroupConj P (Subgroup.zpowers (r i)) :=
    ⟨c, by rw [hPx, CFSG.GroupTheory.map_conj_zpowers, hc]⟩
  fin_cases i
  · exact Or.inl hconj
  · exact Or.inr (Or.inl hconj)
  · exact Or.inr (Or.inr hconj)


section QuaternionPart


private theorem closure_alpha2_beta2_eq :
    Subgroup.closure ({a2A, b2A} : Set A45) = listSubgroup qa45L1Facts.q8_group := by
  have ha : a2A ∈ Subgroup.closure ({a2A, b2A} : Set A45) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : b2A ∈ Subgroup.closure ({a2A, b2A} : Set A45) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  apply le_antisymm
  · refine closure_le_listSubgroup _ fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [Q8gens]
  · intro x hx
    have hxL : (x : P45) ∈ Q8list () := hx
    simp only [Q8list, tabList_eq, tab_eq, List.mem_cons, List.not_mem_nil, or_false] at hxL
    rcases hxL with h | h | h | h | h | h | h | h
    · obtain rfl : x = 1 := Subtype.ext h
      exact one_mem _
    · obtain rfl : x = a2A := Subtype.ext h
      exact ha
    · obtain rfl : x = a2A * a2A := Subtype.ext h
      exact mul_mem ha ha
    · obtain rfl : x = a2A * a2A * a2A := Subtype.ext h
      exact mul_mem (mul_mem ha ha) ha
    · obtain rfl : x = b2A := Subtype.ext h
      exact hb
    · obtain rfl : x = b2A * a2A := Subtype.ext h
      exact mul_mem hb ha
    · obtain rfl : x = b2A * (a2A * a2A) := Subtype.ext h
      exact mul_mem hb (mul_mem ha ha)
    · obtain rfl : x = b2A * (a2A * a2A * a2A) := Subtype.ext h
      exact mul_mem hb (mul_mem (mul_mem ha ha) ha)

private theorem qa45_q8_part :
    Subgroup.closure ({a2A, b2A} : Set A45) ≤ Subgroup.centralizer ({s1A} : Set A45) ∧
    Nat.card (Subgroup.closure ({a2A, b2A} : Set A45)) = 8 ∧
    Nonempty (↥(Subgroup.closure ({a2A, b2A} : Set A45)) ≃* QuaternionGroup 2) := by
  have hcard : Nat.card (Subgroup.closure ({a2A, b2A} : Set A45)) = 8 := by
    rw [closure_alpha2_beta2_eq, card_listSubgroup]
    simp [Q8list, tabList]
  refine ⟨?_, hcard, ?_⟩
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext qa45L1Facts.a2_commutes_sigma1)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext qa45L1Facts.b2_commutes_sigma1)
  · refine nonempty_mulEquiv_quaternionGroup_two_closure hcard ?_ ?_ ?_ ?_
    · exact Subtype.ext (by simpa using alpha2_pow_four)
    · intro h
      exact alpha2_sq_ne_one (by simpa [sq] using congrArg Subtype.val h)
    · exact Subtype.ext (by simpa using qa45L1Facts.q8_conj)
    · refine Subtype.ext ?_
      simp only [Subgroup.coe_pow]
      rw [sq, sq, beta2_sq, alpha2_sq]

end QuaternionPart


section ElementaryAbelianPart


private theorem qa45_e4_part :
    Subgroup.closure ({tA, uA * vA} : Set A45) ≤ Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) ∧
    IsElemAbelian 2 (Subgroup.closure ({tA, uA * vA} : Set A45)) ∧
    Nat.card (Subgroup.closure ({tA, uA * vA} : Set A45)) = 4 := by
  have hA : Nat.card A45 = 51840 := card_QA45
  obtain ⟨hC1, hC2, hC3, hC4⟩ := qa45_involution_centralizers
  have hut : Commute tA uA := Subtype.ext t_commute_u
  have hvt : Commute tA vA := Subtype.ext t_commute_v
  have huv : Commute uA vA := Subtype.ext u_commute_v
  have htuv : Commute tA (uA * vA) := hut.mul_right hvt
  have htt : tA * tA = 1 := Subtype.ext t_sq
  have huu : uA * uA = 1 := Subtype.ext u_sq
  have hvv : vA * vA = 1 := Subtype.ext v_sq
  have huvsq : (uA * vA) * (uA * vA) = 1 := by
    rw [Commute.mul_mul_mul_comm huv.symm uA vA, huu, hvv, one_mul]
  have ht1 : tA ≠ 1 :=
    CFSG.GroupTheory.ne_one_of_card_centralizer_ne (by rw [hC1, hA]; omega)
  have huv1 : uA * vA ≠ 1 :=
    CFSG.GroupTheory.ne_one_of_card_centralizer_ne (by rw [hC4, hA]; omega)
  have hne : uA * vA ≠ tA := fun h => by
    have h' := hC4
    rw [h, hC1] at h'
    omega
  have hcomm : ∀ x ∈ ({tA, uA * vA} : Set A45), ∀ y ∈ ({tA, uA * vA} : Set A45),
      x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact htuv.eq
    · exact htuv.eq.symm
    · rfl
  have hsq : ∀ x ∈ ({tA, uA * vA} : Set A45), x * x = 1 := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact htt
    · exact huvsq
  have hea : IsElemAbelian 2 (Subgroup.closure ({tA, uA * vA} : Set A45)) :=
    IsElemAbelian.closure_of_commute hcomm fun x hx => by
      rw [sq]
      exact hsq x hx
  refine ⟨?_, hea, ?_⟩
  · rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h1 : Commute tA s1A := Subtype.ext t_commute_sigma1
      have h2 : Commute tA s2A := Subtype.ext t_commute_sigma2
      exact (h1.mul_right h2.inv_right).eq
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext qa45L1Facts.uv_commutes_sigma1_sigma2_inv)
  · exact CFSG.GroupTheory.card_closure_pair_of_involutions htt huvsq htuv.eq ht1 huv1 hne

end ElementaryAbelianPart


section DihedralPart


set_option quotPrecheck false in
local notation "rD" => (tA * (vA * bA) : A45)
set_option quotPrecheck false in
local notation "H8" => Subgroup.closure ({tA, uA, vA * bA} : Set A45)

private theorem mem_listSubgroup_d8_iff (x : A45) :
    x ∈ listSubgroup qa45L1Facts.d8_group ↔
      x = 1 ∨ x = rD ∨ x = rD * rD ∨ x = rD * rD * rD ∨ x = tA ∨ x = tA * rD ∨
        x = tA * (rD * rD) ∨ x = tA * (rD * rD * rD) := by
  rw [mem_listSubgroup]
  simp only [D8list, tabList_eq, tab_eq, List.mem_cons, List.not_mem_nil, or_false,
    Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one]

private theorem closure_t_u_vbeta_eq : H8 = listSubgroup qa45L1Facts.d8_group := by
  have htH : tA ∈ H8 := Subgroup.subset_closure (by simp)
  have hwH : vA * bA ∈ H8 := Subgroup.subset_closure (by simp)
  have hrH : rD ∈ H8 := mul_mem htH hwH
  apply le_antisymm
  · refine closure_le_listSubgroup _ fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp [D8gens]
  · intro x hx
    rcases (mem_listSubgroup_d8_iff x).1 hx with h | h | h | h | h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact hrH
    · exact mul_mem hrH hrH
    · exact mul_mem (mul_mem hrH hrH) hrH
    · exact htH
    · exact mul_mem htH hrH
    · exact mul_mem htH (mul_mem hrH hrH)
    · exact mul_mem htH (mul_mem (mul_mem hrH hrH) hrH)

private theorem qa45_d8_part :
    H8 ≤ Subgroup.centralizer ({s1A * s2A} : Set A45) ∧ Nat.card H8 = 8 ∧
    Nonempty (↥H8 ≃* DihedralGroup 4) ∧
    (Subgroup.center ↥H8).map (Subgroup.subtype H8) = Subgroup.zpowers (uA * tA) := by
  have hA : Nat.card A45 = 51840 := card_QA45
  obtain ⟨hC1, hC2, hC3, hC4⟩ := qa45_involution_centralizers
  have hut : Commute tA uA := Subtype.ext t_commute_u
  have htt : tA * tA = 1 := Subtype.ext t_sq
  have huu : uA * uA = 1 := Subtype.ext u_sq
  have hww : (vA * bA) * (vA * bA) = 1 := Subtype.ext qa45L1Facts.vbeta_sq
  have hrr : rD * rD = uA * tA := Subtype.ext qa45L1Facts.tvbeta_sq
  have hutut : (uA * tA) * (uA * tA) = 1 := by
    rw [Commute.mul_mul_mul_comm hut uA tA, huu, htt, one_mul]
  have hut1 : uA * tA ≠ 1 :=
    CFSG.GroupTheory.ne_one_of_card_centralizer_ne (by rw [hC2, hA]; omega)
  have htH : tA ∈ H8 := Subgroup.subset_closure (by simp)
  have huH : uA ∈ H8 := Subgroup.subset_closure (by simp)
  have hwH : vA * bA ∈ H8 := Subgroup.subset_closure (by simp)
  have hrH : rD ∈ H8 := mul_mem htH hwH
  have hHeq := closure_t_u_vbeta_eq
  have hts1 : Commute tA s1A := Subtype.ext t_commute_sigma1
  have hts2 : Commute tA s2A := Subtype.ext t_commute_sigma2
  have hs12 : s1A * s2A = s2A * s1A := Subtype.ext sigma1_commute_sigma2
  have huc : uA * s1A * uA⁻¹ = s2A := Subtype.ext sigma1_conj_u
  have hle : H8 ≤ Subgroup.centralizer ({s1A * s2A} : Set A45) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hts1.mul_right hts2).eq
    · exact Subgroup.mem_centralizer_singleton_iff.2 (commute_mul_of_swap huu huc hs12)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext qa45L1Facts.vbeta_commutes_sigma1_sigma2)
  have hcard : Nat.card H8 = 8 := by
    rw [hHeq, card_listSubgroup]
    simp [D8list, tabList]
  have hH8 : ∀ x ∈ H8, x = 1 ∨ x = rD ∨ x = rD * rD ∨ x = rD * rD * rD ∨ x = tA ∨
      x = tA * rD ∨ x = tA * (rD * rD) ∨ x = tA * (rD * rD * rD) := fun x hx =>
    (mem_listSubgroup_d8_iff x).1 (hHeq ▸ hx)
  have hnd := qa45L1Facts.d8_group.nodup
  simp only [D8list, tabList_eq, tab_eq, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd
  obtain ⟨⟨h01, h02, h03, h04, h05, h06, h07⟩, ⟨h12, h13, h14, h15, h16, h17⟩,
    ⟨h23, h24, h25, h26, h27⟩, ⟨h34, h35, h36, h37⟩, ⟨h45, h46, h47⟩, ⟨h56, h57⟩, h67, -⟩ := hnd
  have hiso : Nonempty (↥H8 ≃* DihedralGroup 4) :=
    nonempty_mulEquiv_dihedralGroup_four_of_elems H8 tA rD htt (by rw [hrr]; exact hut1)
      (by rw [hrr]; exact hutut) (conj_eq_inv_mul_of_involutions htt hww) htH hrH hH8
      (fun h => h04 (congrArg Subtype.val h).symm) (fun h => h14 (congrArg Subtype.val h).symm)
      (fun h => h24 (congrArg Subtype.val h).symm) (fun h => h34 (congrArg Subtype.val h).symm)
  refine ⟨hle, hcard, hiso, ?_⟩
  have hutH : uA * tA ∈ H8 := mul_mem huH htH
  have hgenH : ∀ g ∈ D8gens, ∃ y ∈ ({tA, uA, vA * bA} : Set A45), (y : P45) = g := by
    intro g hg
    simp only [D8gens, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨tA, by simp, rfl⟩
    · exact ⟨uA, by simp, rfl⟩
    · exact ⟨vA * bA, by simp, rfl⟩
  apply le_antisymm
  · rintro z ⟨w, hwc, rfl⟩
    have hwmem : ((w : ↥H8) : A45) ∈ listSubgroup qa45L1Facts.d8_group := by
      rw [← hHeq]
      exact w.2
    have hwL : (((w : ↥H8) : A45) : P45) ∈ D8list () := (mem_listSubgroup _ _).1 hwmem
    have hcomm : ∀ g ∈ D8gens, (((w : ↥H8) : A45) : P45) * g = g * (((w : ↥H8) : A45) : P45) := by
      intro g hg
      obtain ⟨y, hy, rfl⟩ := hgenH g hg
      have hyH : y ∈ H8 := Subgroup.subset_closure hy
      have h1 := congrArg (fun a : ↥H8 => ((a : A45) : P45))
        (Subgroup.mem_center_iff.1 hwc ⟨y, hyH⟩)
      exact h1.symm
    rcases d8CenterCheck_spec qa45L1Facts.d8_center _ hwL hcomm with h | h
    · obtain h' : ((w : ↥H8) : A45) = 1 := Subtype.ext h
      show ((w : ↥H8) : A45) ∈ _
      rw [h']
      exact one_mem _
    · obtain h' : ((w : ↥H8) : A45) = uA * tA := Subtype.ext h
      show ((w : ↥H8) : A45) ∈ _
      rw [h']
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine ⟨⟨uA * tA, hutH⟩, ?_, rfl⟩
    refine CFSG.GroupTheory.mem_center_closure_of_forall (s := ({tA, uA, vA * bA} : Set A45))
      hutH ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact (hut.mul_right (Commute.refl tA)).eq
    · exact ((Commute.refl uA).mul_right hut.symm).eq
    · exact (Subtype.ext qa45L1Facts.vbeta_commutes_ut :
        (uA * tA) * (vA * bA) = (vA * bA) * (uA * tA)).symm

end DihedralPart


theorem qa45_sigma_centralizer_sylow :
    (Subgroup.closure {a2A, b2A} ≤ Subgroup.centralizer ({s1A} : Set A45) ∧
      Nat.card (Subgroup.closure {a2A, b2A}) = 8 ∧
      Nonempty (↥(Subgroup.closure {a2A, b2A}) ≃* QuaternionGroup 2)) ∧
    (Subgroup.closure {tA, uA * vA} ≤ Subgroup.centralizer ({s1A * s2A⁻¹} : Set A45) ∧
      IsElemAbelian 2 (Subgroup.closure {tA, uA * vA}) ∧
      Nat.card (Subgroup.closure {tA, uA * vA}) = 4) ∧
    (Subgroup.closure {tA, uA, vA * bA} ≤ Subgroup.centralizer ({s1A * s2A} : Set A45) ∧
      Nat.card (Subgroup.closure {tA, uA, vA * bA}) = 8 ∧
      Nonempty (↥(Subgroup.closure {tA, uA, vA * bA}) ≃* DihedralGroup 4) ∧
      (Subgroup.center ↥(Subgroup.closure {tA, uA, vA * bA})).map
        (Subgroup.closure {tA, uA, vA * bA}).subtype = Subgroup.zpowers (uA * tA)) :=
  ⟨qa45_q8_part, qa45_e4_part, qa45_d8_part⟩

end CFSG.RankThree.GF2n.Parrott
