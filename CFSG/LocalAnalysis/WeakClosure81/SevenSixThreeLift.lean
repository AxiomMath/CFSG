module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped commutatorElement

variable {Q : Type*} [Group Q]

private theorem s763L_index_ne_zero [Finite Q] (H : Subgroup Q) : H.index ≠ 0 := by
  intro h0
  have h := Subgroup.index_mul_card H
  rw [h0, zero_mul] at h
  exact Nat.card_pos.ne' h.symm

private theorem s763L_commutator_le_center (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1) :
    commutator Q ≤ Subgroup.center Q := by
  rw [commutator_def]
  refine (Subgroup.commutator_le (H₁ := ⊤) (H₂ := ⊤) (H₃ := Subgroup.center Q)).mpr ?_
  intro x _ y _
  rw [Subgroup.mem_center_iff]
  intro g
  exact (commutatorElement_eq_one_iff_mul_comm.mp (hcl x y g)).symm

theorem relIndex_sup_zpowers_eq_prime [Finite Q] {p : ℕ} (hp : p.Prime) {M : Subgroup Q}
    [M.Normal] {a : Q} (ha : a ^ p = 1) (haM : a ∉ M) :
    M.relIndex (Subgroup.zpowers a ⊔ M) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha1 : a ≠ 1 := by
    intro h
    apply haM
    rw [h]
    exact M.one_mem
  have hcard : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha ha1
  rw [Subgroup.relIndex_sup_right]
  have hdvd : Nat.card (M ⊓ Subgroup.zpowers a : Subgroup Q) ∣ p := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le
      (inf_le_right : M ⊓ Subgroup.zpowers a ≤ Subgroup.zpowers a)
  have hcardinf : Nat.card (M ⊓ Subgroup.zpowers a : Subgroup Q) = 1 := by
    rcases hp.eq_one_or_self_of_dvd (Nat.card (M ⊓ Subgroup.zpowers a : Subgroup Q)) hdvd
      with h1 | hp'
    · exact h1
    · exfalso
      have heq : M ⊓ Subgroup.zpowers a = Subgroup.zpowers a := by
        refine Subgroup.eq_of_le_of_card_ge
          (inf_le_right : M ⊓ Subgroup.zpowers a ≤ Subgroup.zpowers a) ?_
        exact le_of_eq (hcard.trans hp'.symm)
      have haMem : a ∈ M ⊓ Subgroup.zpowers a := by
        rw [heq]
        exact Subgroup.mem_zpowers a
      exact haM (Subgroup.mem_inf.mp haMem).1
  have hrel := Subgroup.relIndex_mul_card M (Subgroup.zpowers a)
  rw [hcardinf, hcard, mul_one] at hrel
  exact hrel

theorem commutator_eq_bot_of_index_le [Finite Q] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ x : Q, x ^ p = 1) (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1)
    (h : (commutator Q).index ≤ p) : commutator Q = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcent : commutator Q ≤ Subgroup.center Q := s763L_commutator_le_center hcl
  have hdvd : (Subgroup.center Q).index ∣ (commutator Q).index :=
    Subgroup.index_dvd_of_le hcent
  have hne : (commutator Q).index ≠ 0 := s763L_index_ne_zero (commutator Q)
  have hcenter_le : (Subgroup.center Q).index ≤ p :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans h
  have hpgroup : IsPGroup p Q := fun g => ⟨1, by rw [pow_one]; exact hexp g⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := Q)).mp hpgroup
  have hcenter_dvd_pow : (Subgroup.center Q).index ∣ p ^ n := by
    rw [← hn]
    exact Subgroup.index_dvd_card (Subgroup.center Q)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hcenter_dvd_pow
  have hcenter_ne : (Subgroup.center Q).index ≠ 0 :=
    s763L_index_ne_zero (Subgroup.center Q)
  have hcenter_dvd_p : (Subgroup.center Q).index ∣ p := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk, hk0, pow_zero]
      exact one_dvd p
    · have hpdvd : p ∣ (Subgroup.center Q).index := by
        rw [hk]
        exact dvd_pow_self p hkpos.ne'
      have hEq : (Subgroup.center Q).index = p :=
        Nat.le_antisymm hcenter_le
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hcenter_ne) hpdvd)
      rw [hEq]
  haveI : IsCyclic (Q ⧸ Subgroup.center Q) := by
    apply isCyclic_of_card_dvd_prime (p := p)
    rw [← Subgroup.index_eq_card (Subgroup.center Q)]
    exact hcenter_dvd_p
  haveI : IsMulCommutative Q := isMulCommutative_of_isCyclic_quotient_center_self Q
  exact commutator_eq_bot (G := Q)

theorem exists_sup_zpowers_eq_top_of_index_le [Finite Q] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ x : Q, x ^ p = 1) (h : (commutator Q).index ≤ p ^ 2) :
    ∃ a b : Q, Subgroup.zpowers a ⊔ Subgroup.zpowers b ⊔ commutator Q = ⊤ := by
  by_cases hD : commutator Q = ⊤
  · exact ⟨1, 1, by rw [hD]; simp⟩
  · obtain ⟨a, -, haD⟩ := SetLike.exists_of_lt (lt_of_le_of_ne le_top hD)
    let M₁ : Subgroup Q := Subgroup.zpowers a ⊔ commutator Q
    have hM₁D : commutator Q ≤ M₁ := le_sup_right
    haveI : M₁.Normal := Subgroup.Normal.of_commutator_le (G := Q) hM₁D
    have hrel1 : (commutator Q).relIndex M₁ = p :=
      relIndex_sup_zpowers_eq_prime hp (hexp a) haD
    by_cases hM₁ : M₁ = ⊤
    · exact ⟨a, 1, by rw [Subgroup.zpowers_eq_bot.mpr rfl, sup_bot_eq]; exact hM₁⟩
    · obtain ⟨b, -, hbM₁⟩ := SetLike.exists_of_lt (lt_of_le_of_ne le_top hM₁)
      let M₂ : Subgroup Q := Subgroup.zpowers b ⊔ M₁
      have hM₁M₂ : M₁ ≤ M₂ := le_sup_right
      have hDM₂ : commutator Q ≤ M₂ := le_trans hM₁D hM₁M₂
      have hrel2 : M₁.relIndex M₂ = p :=
        relIndex_sup_zpowers_eq_prime hp (hexp b) hbM₁
      have hrelD : (commutator Q).relIndex M₂ = p * p := by
        rw [← Subgroup.relIndex_mul_relIndex (commutator Q) M₁ M₂ hM₁D hM₁M₂,
          hrel1, hrel2]
      have hM₂index : M₂.index = 1 := by
        have hineq : p ^ 2 * M₂.index ≤ p ^ 2 := by
          calc p ^ 2 * M₂.index = (p * p) * M₂.index := by ring
            _ = (commutator Q).relIndex M₂ * M₂.index := by rw [hrelD]
            _ = (commutator Q).index := Subgroup.relIndex_mul_index hDM₂
            _ ≤ p ^ 2 := h
        have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
        have hle1 : M₂.index ≤ 1 := by
          have h' : p ^ 2 * M₂.index ≤ p ^ 2 * 1 := by simpa using hineq
          exact Nat.le_of_mul_le_mul_left h' hpos
        have hposM₂ : 0 < M₂.index := Nat.pos_of_ne_zero (s763L_index_ne_zero M₂)
        omega
      have hM₂top : M₂ = ⊤ := Subgroup.index_eq_one.mp hM₂index
      refine ⟨a, b, ?_⟩
      rw [← hM₂top]
      change Subgroup.zpowers a ⊔ Subgroup.zpowers b ⊔ commutator Q =
        Subgroup.zpowers b ⊔ (Subgroup.zpowers a ⊔ commutator Q)
      ac_rfl

private theorem s763L_commutator_mul_left (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1)
    (x x' y : Q) : ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
  have hcomm : x * ⁅x', y⁆ = ⁅x', y⁆ * x :=
    (commutatorElement_eq_one_iff_mul_comm.mp (hcl x' y x)).symm
  calc ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ :=
        commutatorElement_mul_left_eq_conj_mul x x' y
    _ = ⁅x', y⁆ * x * x⁻¹ * ⁅x, y⁆ := by rw [hcomm]
    _ = ⁅x', y⁆ * ⁅x, y⁆ := by group
    _ = ⁅x, y⁆ * ⁅x', y⁆ := commutatorElement_eq_one_iff_mul_comm.mp (hcl x' y ⁅x, y⁆)

private theorem s763L_commutator_mul_right (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1)
    (x y y' : Q) : ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have hcomm : y * ⁅x, y'⁆ = ⁅x, y'⁆ * y :=
    (commutatorElement_eq_one_iff_mul_comm.mp (hcl x y' y)).symm
  calc ⁅x, y * y'⁆ = ⁅x, y⁆ * y * ⁅x, y'⁆ * y⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj x y y'
    _ = ⁅x, y⁆ * (y * ⁅x, y'⁆) * y⁻¹ := by group
    _ = ⁅x, y⁆ * (⁅x, y'⁆ * y) * y⁻¹ := by rw [hcomm]
    _ = ⁅x, y⁆ * ⁅x, y'⁆ := by group

private theorem s763L_commutator_inv_left (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1)
    (x y : Q) : ⁅x⁻¹, y⁆ = ⁅x, y⁆⁻¹ := by
  have h := s763L_commutator_mul_left hcl x x⁻¹ y
  rw [mul_inv_cancel, commutatorElement_one_left] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem s763L_commutator_inv_right (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1)
    (x y : Q) : ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
  have h := s763L_commutator_mul_right hcl x y y⁻¹
  rw [mul_inv_cancel, commutatorElement_one_right] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private def s763L_fixedRight (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1) (v : Q)
    (E : Subgroup Q) : Subgroup Q where
  carrier := {y | ⁅v, y⁆ ∈ E}
  mul_mem' := fun {y y'} hy hy' => by
    change ⁅v, y * y'⁆ ∈ E
    rw [s763L_commutator_mul_right hcl v y y']
    exact E.mul_mem hy hy'
  one_mem' := by
    change ⁅v, (1 : Q)⁆ ∈ E
    rw [commutatorElement_one_right]
    exact E.one_mem
  inv_mem' := fun {y} hy => by
    change ⁅v, y⁻¹⁆ ∈ E
    rw [s763L_commutator_inv_right hcl v y]
    exact E.inv_mem hy

private def s763L_fixedLeft (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1) (E : Subgroup Q) :
    Subgroup Q where
  carrier := {x | ∀ y, ⁅x, y⁆ ∈ E}
  mul_mem' := fun {x x'} hx hx' => by
    intro y
    change ⁅x * x', y⁆ ∈ E
    rw [s763L_commutator_mul_left hcl x x' y]
    exact E.mul_mem (hx y) (hx' y)
  one_mem' := by
    intro y
    change ⁅(1 : Q), y⁆ ∈ E
    rw [commutatorElement_one_left]
    exact E.one_mem
  inv_mem' := fun {x} hx => by
    intro y
    change ⁅x⁻¹, y⁆ ∈ E
    rw [s763L_commutator_inv_left hcl x y]
    exact E.inv_mem (hx y)

private theorem s763L_commutator_le_fixedRight
    (hcent : commutator Q ≤ Subgroup.center Q)
    (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1) (v : Q) (E : Subgroup Q) :
    commutator Q ≤ s763L_fixedRight hcl v E := by
  intro d hd
  change ⁅v, d⁆ ∈ E
  have h1 : ⁅v, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp (hcent hd) v)
  rw [h1]
  exact E.one_mem

private theorem s763L_commutator_le_fixedLeft
    (hcent : commutator Q ≤ Subgroup.center Q)
    (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1) (E : Subgroup Q) :
    commutator Q ≤ s763L_fixedLeft hcl E := by
  intro d hd
  intro y
  change ⁅d, y⁆ ∈ E
  have h1 : ⁅d, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp (hcent hd) y).symm)
  rw [h1]
  exact E.one_mem

theorem commutator_le_zpowers_of_sup_eq_top (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1) {a b : Q}
    (h : Subgroup.zpowers a ⊔ Subgroup.zpowers b ⊔ commutator Q = ⊤) :
    commutator Q ≤ Subgroup.zpowers ⁅a, b⁆ := by
  let E : Subgroup Q := Subgroup.zpowers ⁅a, b⁆
  have hcent : commutator Q ≤ Subgroup.center Q := s763L_commutator_le_center hcl
  have hSa : (⊤ : Subgroup Q) ≤ s763L_fixedRight hcl a E := by
    rw [← h]
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        change ⁅a, a⁆ ∈ E
        rw [commutatorElement_self]
        exact E.one_mem
      · rw [Subgroup.zpowers_le]
        change ⁅a, b⁆ ∈ E
        exact Subgroup.mem_zpowers ⁅a, b⁆
    · exact s763L_commutator_le_fixedRight hcent hcl a E
  have hSb : (⊤ : Subgroup Q) ≤ s763L_fixedRight hcl b E := by
    rw [← h]
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        change ⁅b, a⁆ ∈ E
        rw [← commutatorElement_inv]
        exact E.inv_mem (Subgroup.mem_zpowers ⁅a, b⁆)
      · rw [Subgroup.zpowers_le]
        change ⁅b, b⁆ ∈ E
        rw [commutatorElement_self]
        exact E.one_mem
    · exact s763L_commutator_le_fixedRight hcent hcl b E
  have haE : ∀ y, ⁅a, y⁆ ∈ E := fun y => hSa (Subgroup.mem_top y)
  have hbE : ∀ y, ⁅b, y⁆ ∈ E := fun y => hSb (Subgroup.mem_top y)
  have hK : (⊤ : Subgroup Q) ≤ s763L_fixedLeft hcl E := by
    rw [← h]
    refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        change ∀ y, ⁅a, y⁆ ∈ E
        exact haE
      · rw [Subgroup.zpowers_le]
        change ∀ y, ⁅b, y⁆ ∈ E
        exact hbE
    · exact s763L_commutator_le_fixedLeft hcent hcl E
  have hcomm : ∀ x y, ⁅x, y⁆ ∈ E := fun x y => hK (Subgroup.mem_top x) y
  rw [commutator_def]
  refine (Subgroup.commutator_le (H₁ := ⊤) (H₂ := ⊤) (H₃ := E)).mpr ?_
  intro x _ y _
  exact hcomm x y

theorem card_le_of_index_commutator_le [Finite Q] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ x : Q, x ^ p = 1) (hcl : ∀ x y z : Q, ⁅⁅x, y⁆, z⁆ = 1)
    (h : (commutator Q).index ≤ p ^ 2) : Nat.card Q ≤ p ^ 3 := by
  obtain ⟨a, b, hab⟩ := exists_sup_zpowers_eq_top_of_index_le hp hexp h
  have hle : commutator Q ≤ Subgroup.zpowers ⁅a, b⁆ :=
    commutator_le_zpowers_of_sup_eq_top hcl hab
  have hcardD : Nat.card (commutator Q) ≤ Nat.card (Subgroup.zpowers ⁅a, b⁆) :=
    Subgroup.card_le_of_le hle
  have horder : orderOf ⁅a, b⁆ ≤ p :=
    Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hexp ⁅a, b⁆))
  have hcardE : Nat.card (Subgroup.zpowers ⁅a, b⁆) ≤ p := by
    rw [Nat.card_zpowers]
    exact horder
  have hcardD' : Nat.card (commutator Q) ≤ p := le_trans hcardD hcardE
  calc Nat.card Q = (commutator Q).index * Nat.card (commutator Q) :=
        (Subgroup.index_mul_card (commutator Q)).symm
    _ ≤ p ^ 2 * p := Nat.mul_le_mul h hcardD'
    _ = p ^ 3 := by ring

end CFSG.LocalAnalysis.WeakClosure81
