module

public import CFSG.GH74.Uniqueness.Section128Bender
public import CFSG.GH74.Uniqueness.Bender.Commuting
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.Timmesfeld.Closure.Line3
public import CFSG.GH74.Uniqueness.Section5Prop53
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.Timmesfeld.Opposite.Moufang
public import CFSG.Timmesfeld.RankOne

public section

namespace CFSG.OddTranspositions.PartThree.EightOne

open CFSG.GH74.Uniqueness.Bender

theorem orderOf_mul_eq_two_of_commuting_involutions
    {L : Type*} [Group L] [Finite L] {n i e : ℕ} (h : BenderType L n i e) {t s s' : L}
    (ht : orderOf t = 2) (hs : orderOf s = 2) (hs' : orderOf s' = 2)
    (hst : s * t = t * s) (hs't : s' * t = t * s') (hne : s ≠ s') :
    orderOf (s * s') = 2 ∧ (s * s') * t = t * (s * s') := by
  have ht2 : t * t = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two ht
  have hs2 : s * s = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two hs
  have hs'2 : s' * s' = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two hs'
  have ht1 : t ≠ 1 := CFSG.GH74.Uniqueness.Sec128B.ne_one_of_orderOf_eq_two ht
  have hss' : s * s' = s' * s :=
    BenderType.commute_of_commute_involutions h hs2 ht2 hs'2 ht1 hst hs't
  have hsq : (s * s') * (s * s') = 1 := by
    calc (s * s') * (s * s') = s * (s' * s) * s' := by group
      _ = s * (s * s') * s' := by rw [hss']
      _ = (s * s) * (s' * s') := by group
      _ = 1 := by rw [hs2, hs'2, one_mul]
  have hne1 : s * s' ≠ 1 := by
    intro h1
    have hs_inv : s = s'⁻¹ := mul_eq_one_iff_eq_inv.mp h1
    rw [inv_eq_of_mul_eq_one_right hs'2] at hs_inv
    exact hne hs_inv
  refine ⟨CFSG.GH74.Uniqueness.Sec128B.orderOf_eq_two_of_mul_self hsq hne1, ?_⟩
  calc (s * s') * t = s * (s' * t) := by rw [mul_assoc]
    _ = s * (t * s') := by rw [hs't]
    _ = (s * t) * s' := by rw [mul_assoc]
    _ = (t * s) * s' := by rw [hst]
    _ = t * (s * s') := by rw [mul_assoc]

theorem exists_involution_commute_ne_of_benderType
    {L : Type*} [Group L] [Finite L] {n i e : ℕ} (h : BenderType L n i e) {a : L}
    (ha : orderOf a = 2) :
    ∃ t : L, orderOf t = 2 ∧ a * t = t * a ∧ t ≠ a := by
  classical
  let S : Set L := {b | orderOf b = 2 ∧ a * b = b * a}
  have hSn : S.ncard = 2 ^ n - 1 := h.ncard_commuting_involutions ha
  have hpow : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le.2
  have hS3 : 3 ≤ S.ncard := by
    rw [hSn]
    omega
  obtain ⟨t, htS, hta⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < S.ncard) a
  exact ⟨t, htS.1, htS.2, hta⟩

theorem exists_isConj_not_commute {L : Type*} [Group L] [Finite L]
    (hL : CFSG.BenderSuzuki.IsBenderGroup L) {a : L} (ha : orderOf a = 2) :
    ∃ b : L, IsConj a b ∧ ¬ Commute a b := by
  classical
  obtain ⟨n, i, e, h⟩ := isBenderGroup_iff_exists_benderType.mp hL
  by_contra hb
  push Not at hb
  have hset : {b : L | orderOf b = 2} = {b : L | orderOf b = 2 ∧ a * b = b * a} := by
    ext b
    constructor
    · intro hb2
      exact ⟨hb2, (hb b
        (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hL ha hb2)).eq⟩
    · rintro ⟨hb2, -⟩
      exact hb2
  have hEq : (2 ^ n - 1) * ((2 ^ n) ^ i + 1) = 2 ^ n - 1 := by
    rw [← h.ncard_involutions, hset, h.ncard_commuting_involutions ha]
  have hqpos : 0 < 2 ^ n - 1 := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le.2
    omega
  have hi : 1 ≤ i := h.two_le.1
  have hfac : 1 < (2 ^ n) ^ i + 1 := by
    have h1 : 1 ≤ (2 ^ n) ^ i := Nat.one_le_pow i (2 ^ n) (by positivity)
    omega
  have hone : (2 ^ n) ^ i + 1 = 1 :=
    Nat.eq_of_mul_eq_mul_left hqpos (by simpa using hEq)
  omega

theorem orderOf_mul_eq_three_of_isConj {L : Type*} [Group L] {a x y : L}
    (ha : orderOf a = 2) (hx : IsConj a x) (hy : IsConj a y)
    (hne : ¬ Commute x y) (hmem : orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ)) :
    orderOf (x * y) = 3 := by
  have hx_ord : orderOf x = 2 :=
    (CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hx).symm.trans ha
  have hy_ord : orderOf y = 2 :=
    (CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hy).symm.trans ha
  have hx2 : x * x = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two hx_ord
  have hy2 : y * y = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two hy_ord
  have hcases : orderOf (x * y) = 1 ∨ orderOf (x * y) = 2 ∨ orderOf (x * y) = 3 := by
    simpa using hmem
  rcases hcases with h1 | h2 | h3
  · exfalso
    have hxy1 : x * y = 1 := (orderOf_eq_one_iff).mp h1
    apply hne
    have hxy : x = y := by
      rw [eq_inv_of_mul_eq_one_left hxy1, inv_eq_of_mul_eq_one_right hy2]
    rw [hxy]
  · exfalso
    apply hne
    have hsq : (x * y) ^ 2 = 1 := by rw [← h2, pow_orderOf_eq_one]
    exact (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one hx2 hy2).mpr hsq
  · exact h3

theorem braid_relations_of_orderOf_mul_eq_three {L : Type*} [Group L] {a t b : L}
    (ha : a * a = 1) (ht : t * t = 1) (hb : b * b = 1)
    (hab : orderOf (a * b) = 3) (htb : orderOf (t * b) = 3) :
    b * a * b = a * b * a ∧ b * t * b = t * b * t := by
  have hba : orderOf (b * a) = 3 := by
    rw [← orderOf_inv (b * a), mul_inv_rev, inv_eq_of_mul_eq_one_right hb,
      inv_eq_of_mul_eq_one_right ha]
    exact hab
  have hbt : orderOf (b * t) = 3 := by
    rw [← orderOf_inv (b * t), mul_inv_rev, inv_eq_of_mul_eq_one_right hb,
      inv_eq_of_mul_eq_one_right ht]
    exact htb
  exact ⟨CFSG.Timmesfeld.Closure.braid_of_orderOf_eq_three hb ha hba,
    CFSG.Timmesfeld.Closure.braid_of_orderOf_eq_three hb ht hbt⟩

theorem mul_eq_and_sq_eq_of_braid {L : Type*} [Group L] {a t b : L}
    (ha : a * a = 1) (hb : b * b = 1) (hat : a * t = t * a)
    (hbraid_ab : b * a * b = a * b * a) (hbraid_tb : b * t * b = t * b * t) :
    (a * t) * (b * a * b) = t * b * a ∧
      ((a * t) * (b * a * b)) ^ 2 = b * (t * a) * b := by
  have hbab : b * a * b * a = a * b := by
    calc b * a * b * a = (b * a * b) * a := by group
      _ = (a * b * a) * a := by rw [hbraid_ab]
      _ = (a * b) * (a * a) := by group
      _ = a * b := by rw [ha, mul_one]
  have hxy : (a * t) * (b * a * b) = t * b * a := by
    calc (a * t) * (b * a * b) = (t * a) * (b * (a * b)) := by rw [hat]; group
      _ = t * (a * (b * (a * b))) := by group
      _ = t * (b * a) := by
        rw [show a * (b * (a * b)) = b * a from by
          calc a * (b * (a * b)) = (a * b * a) * b := by group
            _ = (b * a * b) * b := by rw [← hbraid_ab]
            _ = b * a := by rw [mul_assoc, hb, mul_one]]
      _ = t * b * a := by group
  refine ⟨hxy, ?_⟩
  rw [hxy]
  calc (t * b * a) ^ 2 = t * b * (a * t) * b * a := by rw [pow_two]; group
    _ = t * b * (t * a) * b * a := by rw [hat]
    _ = (t * b * t) * a * b * a := by group
    _ = (b * t * b) * a * b * a := by rw [← hbraid_tb]
    _ = b * (t * (b * a * b * a)) := by group
    _ = b * (t * (a * b)) := by rw [hbab]
    _ = b * (t * a) * b := by group

theorem orderOf_mul_eq_four_of_braid {L : Type*} [Group L] {a t b : L}
    (ha : a * a = 1) (ht : t * t = 1) (hb : b * b = 1)
    (hat : a * t = t * a) (hta : t ≠ a)
    (hbraid_ab : b * a * b = a * b * a) (hbraid_tb : b * t * b = t * b * t) :
    orderOf ((a * t) * (b * a * b)) = 4 := by
  obtain ⟨-, hxysq⟩ := mul_eq_and_sq_eq_of_braid ha hb hat hbraid_ab hbraid_tb
  have hta_ne_one : t * a ≠ 1 := by
    intro h1
    exact hta (by rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right ha])
  have hsquare_ne : ((a * t) * (b * a * b)) ^ (2 ^ 1) ≠ 1 := by
    rw [show (2 : ℕ) ^ 1 = 2 from rfl, hxysq]
    intro h1
    apply hta_ne_one
    have hconj := congrArg (fun z => b * z * b) h1
    have hbta : b * (b * (t * a)) = 1 := by simpa [mul_assoc, hb] using hconj
    calc t * a = (b * b) * (t * a) := by rw [hb, one_mul]
      _ = b * (b * (t * a)) := by group
      _ = 1 := hbta
  have hta_sq : (t * a) * (t * a) = 1 := by
    calc (t * a) * (t * a) = t * (a * t) * a := by group
      _ = t * (t * a) * a := by rw [hat]
      _ = (t * t) * (a * a) := by group
      _ = 1 := by rw [ht, ha, one_mul]
  have hfourth : ((a * t) * (b * a * b)) ^ (2 ^ (1 + 1)) = 1 := by
    have hsq2 : (b * (t * a) * b) * (b * (t * a) * b) = 1 := by
      calc (b * (t * a) * b) * (b * (t * a) * b) =
            b * ((t * a) * (b * b) * (t * a)) * b := by group
        _ = b * ((t * a) * (t * a)) * b := by rw [hb, mul_one]
        _ = 1 := by rw [hta_sq, mul_one, hb]
    rw [show (2 : ℕ) ^ (1 + 1) = 4 from rfl, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hxysq]
    simpa [pow_two] using hsq2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa only [show (2 : ℕ) ^ 1 = 2 from rfl, show (2 : ℕ) ^ (1 + 1) = 4 from rfl] using
    (orderOf_eq_prime_pow (p := 2) (n := 1) hsquare_ne hfourth)

theorem exists_isConj_orderOf_mul_eq_four {L : Type*} [Group L]
    [Finite L] (hL : CFSG.BenderSuzuki.IsBenderGroup L) {a t b : L}
    (ha : orderOf a = 2) (ht : orderOf t = 2) (hb : orderOf b = 2)
    (hat : a * t = t * a) (hta : t ≠ a)
    (hbraid_ab : b * a * b = a * b * a) (hbraid_tb : b * t * b = t * b * t) :
    ∃ x y : L, IsConj a x ∧ IsConj a y ∧ orderOf (x * y) = 4 := by
  have ha2 : a * a = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two ha
  have ht2 : t * t = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two ht
  have hb2 : b * b = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two hb
  have hx_sq : (a * t) * (a * t) = 1 := by
    calc (a * t) * (a * t) = a * (t * a) * t := by group
      _ = a * (a * t) * t := by rw [← hat]
      _ = (a * a) * (t * t) := by group
      _ = 1 := by rw [ha2, ht2, one_mul]
  have hat_ne_one : a * t ≠ 1 := by
    intro h1
    apply hta
    calc t = t⁻¹ := (inv_eq_of_mul_eq_one_right ht2).symm
      _ = a := (eq_inv_of_mul_eq_one_left h1).symm
  have hx_ord : orderOf (a * t) = 2 :=
    CFSG.GH74.Uniqueness.Sec128B.orderOf_eq_two_of_mul_self hx_sq hat_ne_one
  have hxconj : IsConj a (a * t) :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hL ha hx_ord
  have hyconj : IsConj a (b * a * b) := by
    rw [isConj_iff]
    exact ⟨b, by rw [inv_eq_of_mul_eq_one_right hb2]⟩
  exact ⟨a * t, b * a * b, hxconj, hyconj,
    orderOf_mul_eq_four_of_braid ha2 ht2 hb2 hat hta hbraid_ab hbraid_tb⟩

theorem exists_isConj_orderOf_mul_not_mem {L : Type} [Group L]
    [Finite L] (hL : CFSG.BenderSuzuki.IsBenderGroup L) {a : L} (ha : orderOf a = 2) :
    ∃ x y : L, IsConj a x ∧ IsConj a y ∧ orderOf (x * y) ∉ ({1, 2, 3} : Set ℕ) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hbconj, hbnotcomm⟩ := exists_isConj_not_commute hL ha
  obtain ⟨n, i, e, h⟩ := isBenderGroup_iff_exists_benderType.mp hL
  obtain ⟨t, ht_ord, hat, hta⟩ := exists_involution_commute_ne_of_benderType h ha
  have ha2 : a * a = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two ha
  have ht_sq : t * t = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two ht_ord
  have hb_ord : orderOf b = 2 :=
    (CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hbconj).symm.trans ha
  have hb2 : b * b = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two hb_ord
  have hbt : ¬ Commute t b := by
    intro hctb
    have hcomm : b * a = a * b :=
      BenderType.commute_of_commute_involutions h (a := b) (z := t) (y := a)
        hb2 ht_sq ha2 (CFSG.GH74.Uniqueness.Sec128B.ne_one_of_orderOf_eq_two ht_ord)
        hctb.eq.symm hat
    exact hbnotcomm hcomm.symm
  have htconj : IsConj a t :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hL ha ht_ord
  have hab_ord : orderOf (a * b) = 3 :=
    orderOf_mul_eq_three_of_isConj ha (IsConj.refl a) hbconj hbnotcomm
      (hcon a b (IsConj.refl a) hbconj)
  have htb_ord : orderOf (t * b) = 3 :=
    orderOf_mul_eq_three_of_isConj ha htconj hbconj hbt (hcon t b htconj hbconj)
  obtain ⟨hbraid_ab, hbraid_tb⟩ :=
    braid_relations_of_orderOf_mul_eq_three ha2 ht_sq hb2 hab_ord htb_ord
  obtain ⟨x, y, hxconj, hyconj, hxy_ord⟩ :=
    exists_isConj_orderOf_mul_eq_four hL ha ht_ord hb_ord hat hta hbraid_ab hbraid_tb
  have hmem := hcon x y hxconj hyconj
  rw [hxy_ord] at hmem
  norm_num at hmem

theorem exists_two_factors_of_benderType {L : Type*} [Group L]
    [Finite L] {n i e : ℕ} (h : BenderType L n i e) {t : L} (ht : orderOf t = 2) :
    ∃ s₁ s₂ : L, orderOf s₁ = 2 ∧ orderOf s₂ = 2 ∧ Commute s₁ t ∧ Commute s₂ t ∧
        s₁ ≠ t ∧ s₂ ≠ t ∧ s₁ * s₂ = t := by
  classical
  let S : Set L := {b | orderOf b = 2 ∧ t * b = b * t}
  have hSn : S.ncard = 2 ^ n - 1 := h.ncard_commuting_involutions ht
  have hpow : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le.2
  have hS3 : 3 ≤ S.ncard := by
    rw [hSn]
    omega
  have ht_sq : t * t = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two ht
  obtain ⟨s₁, hs₁S, hs₁t⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < S.ncard) t
  have hs₁_sq : s₁ * s₁ = 1 :=
    CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two hs₁S.1
  have hs₂ : orderOf (s₁ * t) = 2 ∧ (s₁ * t) * t = t * (s₁ * t) :=
    orderOf_mul_eq_two_of_commuting_involutions h ht hs₁S.1 ht hs₁S.2.symm rfl hs₁t
  have hs₂t : s₁ * t ≠ t := by
    intro hst
    have hs₁_one : s₁ = 1 := by
      have hconj := congrArg (fun x => x * t) hst
      simpa [mul_assoc, ht_sq] using hconj
    exact CFSG.GH74.Uniqueness.Sec128B.ne_one_of_orderOf_eq_two hs₁S.1 hs₁_one
  have hs₁s₂ : s₁ * (s₁ * t) = t := by
    calc s₁ * (s₁ * t) = (s₁ * s₁) * t := by group
      _ = t := by rw [hs₁_sq, one_mul]
  exact ⟨s₁, s₁ * t, hs₁S.1, hs₂.1, hs₁S.2.symm, hs₂.2, hs₁t, hs₂t, hs₁s₂⟩

theorem exists_commuting_involution_avoiding {L : Type*} [Group L]
    [Finite L] {n i e : ℕ} (h : BenderType L n i e) {t s₁ : L} (ht : orderOf t = 2)
    (hs₁ : orderOf s₁ = 2) (hst : t * s₁ = s₁ * t) (hs₁t : s₁ ≠ t) (hn3 : 3 ≤ n) :
    ∃ s₂ : L, orderOf s₂ = 2 ∧ t * s₂ = s₂ * t ∧ s₂ ≠ t ∧ s₂ ≠ s₁ ∧ s₂ ≠ s₁ * t := by
  classical
  let S : Set L := {b | orderOf b = 2 ∧ t * b = b * t}
  have hSn : S.ncard = 2 ^ n - 1 := h.ncard_commuting_involutions ht
  have hS7 : 7 ≤ S.ncard := by
    rw [hSn]
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  have htS : t ∈ S := ⟨ht, rfl⟩
  have hs₁S : s₁ ∈ S := ⟨hs₁, hst⟩
  have hs₁tS : s₁ * t ∈ S := by
    have hmem := orderOf_mul_eq_two_of_commuting_involutions h ht hs₁ ht hst.symm rfl hs₁t
    exact ⟨hmem.1, hmem.2.symm⟩
  let X : Set L := {t, s₁, s₁ * t}
  have hXsub : X ⊆ S := by
    intro x hx
    simp only [X, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact htS
    · exact hs₁S
    · exact hs₁tS
  have hXcard : X.ncard ≤ 3 := by
    have h1 : X.ncard ≤ ({s₁, s₁ * t} : Set L).ncard + 1 := by
      simpa [X] using Set.ncard_insert_le t ({s₁, s₁ * t} : Set L)
    have h2 : ({s₁, s₁ * t} : Set L).ncard ≤ ({s₁ * t} : Set L).ncard + 1 :=
      Set.ncard_insert_le s₁ ({s₁ * t} : Set L)
    have h3 : ({s₁ * t} : Set L).ncard = 1 := Set.ncard_singleton _
    omega
  have hXleS : X.ncard ≤ S.ncard := Set.ncard_le_ncard hXsub
  have hdiff : (S \ X).ncard = S.ncard - X.ncard := Set.ncard_diff hXsub
  have hbig : 1 < (S \ X).ncard := by omega
  obtain ⟨s₂, hs₂X, -⟩ := Set.exists_ne_of_one_lt_ncard hbig t
  have hs₂S : s₂ ∈ S := hs₂X.1
  have hs₂notX : s₂ ∉ X := hs₂X.2
  have hs₂t : s₂ ≠ t := by
    intro h
    exact hs₂notX (by simp [X, h])
  have hs₂s₁ : s₂ ≠ s₁ := by
    intro h
    exact hs₂notX (by simp [X, h])
  have hs₂prod : s₂ ≠ s₁ * t := by
    intro h
    exact hs₂notX (by simp [X, h])
  exact ⟨s₂, hs₂S.1, hs₂S.2, hs₂t, hs₂s₁, hs₂prod⟩

theorem exists_avoiding_commuting_involution {L : Type*} [Group L]
    [Finite L] {n i e : ℕ} (h : BenderType L n i e) {t s₁ : L} (ht : orderOf t = 2)
    (hs₁ : orderOf s₁ = 2) (hst : t * s₁ = s₁ * t) (hs₁t : s₁ ≠ t) (hn3 : 3 ≤ n) :
    ∃ s₂ : L, orderOf s₂ = 2 ∧ t * s₂ = s₂ * t ∧ s₂ ≠ t ∧ s₂ ≠ s₁ ∧
      s₂ ≠ s₁ * t ∧ s₁ * s₂ ≠ t := by
  have hs₁_sq : s₁ * s₁ = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two hs₁
  obtain ⟨s₂, hs₂ord, hs₂comm, hs₂t, hs₂s₁, hs₂prod⟩ :=
    exists_commuting_involution_avoiding h ht hs₁ hst hs₁t hn3
  have hprod_ne_t : s₁ * s₂ ≠ t := by
    intro hpt
    apply hs₂prod
    calc s₂ = (s₁ * s₁) * s₂ := by rw [hs₁_sq, one_mul]
      _ = s₁ * (s₁ * s₂) := by group
      _ = s₁ * t := by rw [hpt]
  exact ⟨s₂, hs₂ord, hs₂comm, hs₂t, hs₂s₁, hs₂prod, hprod_ne_t⟩

theorem exists_three_factors_of_benderType {L : Type*} [Group L]
    [Finite L] {n i e : ℕ} (h : BenderType L n i e) {t : L} (ht : orderOf t = 2)
    (hn3 : 3 ≤ n) :
    ∃ s₁ s₂ s₃ : L, orderOf s₁ = 2 ∧ orderOf s₂ = 2 ∧ orderOf s₃ = 2 ∧
      Commute s₁ t ∧ Commute s₂ t ∧ Commute s₃ t ∧ s₁ ≠ t ∧ s₂ ≠ t ∧ s₃ ≠ t ∧
      s₁ * s₂ * s₃ = t := by
  classical
  let S : Set L := {b | orderOf b = 2 ∧ t * b = b * t}
  have hSn : S.ncard = 2 ^ n - 1 := h.ncard_commuting_involutions ht
  have hpow : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le.2
  have hS3 : 3 ≤ S.ncard := by
    rw [hSn]
    omega
  have ht_sq : t * t = 1 := CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two ht
  obtain ⟨s₁, hs₁S, hs₁t⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < S.ncard) t
  have hs₁_sq : s₁ * s₁ = 1 :=
    CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two hs₁S.1
  obtain ⟨s₂, hs₂ord, hs₂comm, hs₂t, hs₂s₁, hs₂prod, hprod_ne_t⟩ :=
    exists_avoiding_commuting_involution h ht hs₁S.1 hs₁S.2 hs₁t hn3
  have hprod : orderOf (s₁ * s₂) = 2 ∧ (s₁ * s₂) * t = t * (s₁ * s₂) :=
    orderOf_mul_eq_two_of_commuting_involutions h ht hs₁S.1 hs₂ord hs₁S.2.symm hs₂comm.symm
      hs₂s₁.symm
  let s₃ : L := s₁ * s₂ * t
  have hs₃ : orderOf s₃ = 2 ∧ s₃ * t = t * s₃ :=
    orderOf_mul_eq_two_of_commuting_involutions h ht hprod.1 ht hprod.2 rfl hprod_ne_t
  have hs₃_ne_one : s₃ ≠ 1 := by
    intro h1
    have hpt : s₁ * s₂ = t := by
      have hconj := congrArg (fun x => x * t) h1
      simpa [s₃, mul_assoc, ht_sq] using hconj
    exact hprod_ne_t hpt
  have hs₃t : s₃ ≠ t := by
    intro h1
    have hprod1 : s₁ * s₂ = 1 := by
      have hconj := congrArg (fun x => x * t) h1
      simpa [s₃, mul_assoc, ht_sq] using hconj
    have hs₂s₁' : s₂ = s₁ := by
      calc s₂ = (s₁ * s₁) * s₂ := by rw [hs₁_sq, one_mul]
        _ = s₁ * (s₁ * s₂) := by group
        _ = s₁ := by rw [hprod1, mul_one]
    exact hs₂s₁ hs₂s₁'
  have hprod_sq : (s₁ * s₂) * (s₁ * s₂) = 1 :=
    CFSG.GH74.Uniqueness.Sec128B.mul_self_of_orderOf_eq_two hprod.1
  have hs₃_prod : s₁ * s₂ * s₃ = t := by
    calc s₁ * s₂ * s₃ = (s₁ * s₂) * ((s₁ * s₂) * t) := rfl
      _ = ((s₁ * s₂) * (s₁ * s₂)) * t := by group
      _ = t := by rw [hprod_sq, one_mul]
  exact ⟨s₁, s₂, s₃, hs₁S.1, hs₂ord, hs₃.1, hs₁S.2.symm, hs₂comm.symm, hs₃.2,
    hs₁t, hs₂t, hs₃t, hs₃_prod⟩

theorem exists_mul_eq_of_benderType {L : Type} [Group L] [Finite L]
    {n i e : ℕ} (h : BenderType L n i e) {t : L} (ht : orderOf t = 2) :
    (∃ s₁ s₂ : L, orderOf s₁ = 2 ∧ orderOf s₂ = 2 ∧ Commute s₁ t ∧ Commute s₂ t ∧
        s₁ ≠ t ∧ s₂ ≠ t ∧ s₁ * s₂ = t) ∧
      (3 ≤ n → ∃ s₁ s₂ s₃ : L, orderOf s₁ = 2 ∧ orderOf s₂ = 2 ∧ orderOf s₃ = 2 ∧
        Commute s₁ t ∧ Commute s₂ t ∧ Commute s₃ t ∧ s₁ ≠ t ∧ s₂ ≠ t ∧ s₃ ≠ t ∧
        s₁ * s₂ * s₃ = t) :=
  ⟨exists_two_factors_of_benderType h ht,
    fun hn3 => exists_three_factors_of_benderType h ht hn3⟩

end CFSG.OddTranspositions.PartThree.EightOne
