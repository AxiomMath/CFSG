module

import CFSG.Monster.GMS.FinalStep
public import CFSG.Monster.GMS.S341

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Dihedral

variable {G : Type*} [Group G]

theorem conj_pow_mul_self {x c : G} (hx : x * x = 1) (hc : c * c = 1) (j : ℕ) :
    (x * c) ^ j * x * ((x * c) ^ j)⁻¹ = (x * c) ^ (2 * j) * x ∧
      (x * c) ^ j * c * ((x * c) ^ j)⁻¹ = (x * c) ^ (2 * j) * c := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hxs : x * (x * c) * x = (x * c)⁻¹ := by
    rw [mul_inv_rev, hx', hc']
    calc x * (x * c) * x = (x * x) * c * x := by group
      _ = c * x := by rw [hx, one_mul]
  have hcs : c * (x * c) * c = (x * c)⁻¹ := by
    rw [mul_inv_rev, hx', hc']
    calc c * (x * c) * c = c * x * (c * c) := by group
      _ = c * x := by rw [hc, mul_one]
  have hpx : ∀ n : ℕ, x * (x * c) ^ n * x = ((x * c) ^ n)⁻¹ := by
    intro n
    have := conj_pow (a := x) (b := x * c) (i := n)
    rw [hx'] at this
    rw [← this, hxs, inv_pow]
  have hpc : ∀ n : ℕ, c * (x * c) ^ n * c = ((x * c) ^ n)⁻¹ := by
    intro n
    have := conj_pow (a := c) (b := x * c) (i := n)
    rw [hc'] at this
    rw [← this, hcs, inv_pow]
  have key : ∀ y : G, (∀ n : ℕ, y * (x * c) ^ n * y = ((x * c) ^ n)⁻¹) → y * y = 1 →
      (x * c) ^ j * y * ((x * c) ^ j)⁻¹ = (x * c) ^ (2 * j) * y := by
    intro y hy hyy
    calc (x * c) ^ j * y * ((x * c) ^ j)⁻¹ = (x * c) ^ j * y * (y * (x * c) ^ j * y) := by
          rw [hy j]
      _ = (x * c) ^ j * (y * y) * (x * c) ^ j * y := by simp only [mul_assoc]
      _ = (x * c) ^ (2 * j) * y := by rw [hyy, mul_one, ← pow_add, two_mul]
  exact ⟨key x hpx hx, key c hpc hc⟩

theorem isConj_pow_mul_cases {x c : G} (hx : x * x = 1) (hc : c * c = 1) (m : ℕ) :
    (IsConj x ((x * c) ^ m * x) ∧ IsConj c ((x * c) ^ m * c)) ∨
      (IsConj c ((x * c) ^ m * x) ∧ IsConj x ((x * c) ^ m * c)) := by
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' m
  · left
    subst hj
    obtain ⟨h1, h2⟩ := conj_pow_mul_self hx hc j
    exact ⟨isConj_iff.mpr ⟨(x * c) ^ j, h1⟩, isConj_iff.mpr ⟨(x * c) ^ j, h2⟩⟩
  · right
    subst hj
    obtain ⟨h1, -⟩ := conj_pow_mul_self hx hc j
    obtain ⟨-, h4⟩ := conj_pow_mul_self hx hc (j + 1)
    have hsc : (x * c) * c = x := by rw [mul_assoc, hc, mul_one]
    have e1 : (x * c) ^ (2 * j + 1) * x = (x * c) ^ (2 * (j + 1)) * c := by
      calc (x * c) ^ (2 * j + 1) * x = (x * c) ^ (2 * j + 1) * ((x * c) * c) := by rw [hsc]
        _ = ((x * c) ^ (2 * j + 1) * (x * c)) * c := (mul_assoc _ _ _).symm
        _ = (x * c) ^ (2 * (j + 1)) * c := by
            rw [← pow_succ, show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    have e2 : (x * c) ^ (2 * j + 1) * c = (x * c) ^ (2 * j) * x := by
      calc (x * c) ^ (2 * j + 1) * c = (x * c) ^ (2 * j) * ((x * c) * c) := by
            rw [pow_succ, mul_assoc]
        _ = (x * c) ^ (2 * j) * x := by rw [hsc]
    refine ⟨?_, ?_⟩
    · rw [e1]
      exact isConj_iff.mpr ⟨(x * c) ^ (j + 1), h4⟩
    · rw [e2]
      exact isConj_iff.mpr ⟨(x * c) ^ j, h1⟩

theorem dihedral_data {x c : G} {m : ℕ} (hx : x * x = 1) (hc : c * c = 1)
    (hm : orderOf (x * c) = 2 * m) (hm0 : 0 < m) :
    (x * c) ^ m * (x * c) ^ m = 1 ∧ (x * c) ^ m ≠ 1 ∧
      (x * c) ^ m * x = x * (x * c) ^ m ∧ (x * c) ^ m * c = c * (x * c) ^ m ∧
      ((IsConj x ((x * c) ^ m * x) ∧ IsConj c ((x * c) ^ m * c)) ∨
        (IsConj c ((x * c) ^ m * x) ∧ IsConj x ((x * c) ^ m * c))) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := dihedral_central_involution hx hc hm hm0
  exact ⟨h1, h2, h3, h4, isConj_pow_mul_cases hx hc m⟩

theorem dihedral_isConj {a x c : G} {m : ℕ} (hxA : IsConj a x) (hcA : IsConj a c)
    (hx : x * x = 1) (hc : c * c = 1) :
    IsConj a ((x * c) ^ m * x) ∧ IsConj a ((x * c) ^ m * c) := by
  rcases isConj_pow_mul_cases hx hc m with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨hxA.trans h1, hcA.trans h2⟩
  · exact ⟨hcA.trans h1, hxA.trans h2⟩

theorem centralizer_inf_le_centralizer_pow (x c : G) (m : ℕ) :
    Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.centralizer ({(x * c) ^ m} : Set G) := by
  intro g hg
  obtain ⟨hgx, hgc⟩ := Subgroup.mem_inf.mp hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgx hgc ⊢
  have h1 : Commute g (x * c) := Commute.mul_right hgx hgc
  exact h1.pow_right m

end Dihedral

section TableVII

variable {G : Type} [Group G]

inductive TableVIIClass
  | two_A
  | two_B
  | four_A
  | four_B
  | six_A
  deriving DecidableEq

@[expose] def tableVIISet (a z₀ x : G) : TableVIIClass → Set G
  | .two_A => twoANbr a x
  | .two_B => twoBNbr a z₀ x
  | .four_A => fourANbr a z₀ x
  | .four_B => fourBNbr a x
  | .six_A => sixANbr a x

@[expose] def tableVIIStab : TableVIIClass → ℕ
  | .two_A => tableVOrderB
  | .two_B => tableVOrderZ
  | .four_A => 2 ^ 30 * 3 ^ 6 * 5 ^ 3 * 7 * 11
  | .four_B => 2 ^ 25 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17
  | .six_A => 2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13

@[expose] def tableVIISize : TableVIIClass → ℕ
  | .two_A => 27143910000
  | .two_B => 11707448673375
  | .four_A => 1102935324621312000
  | .four_B => 1254793905192960000
  | .six_A => 64353605265653760000

theorem tableVIIStab_mul_size (K : TableVIIClass) :
    tableVIIStab K * tableVIISize K = twoBabyOrder := by
  cases K <;> norm_num [tableVIIStab, tableVIISize, tableVOrderB, tableVOrderZ, twoBabyOrder]

theorem tableVIIStab_pos (K : TableVIIClass) : 0 < tableVIIStab K := by
  cases K <;> norm_num [tableVIIStab, tableVOrderB, tableVOrderZ]

@[expose] def tableVIIOrder : TableVIIClass → ℕ
  | .two_A => 2
  | .two_B => 2
  | .four_A => 4
  | .four_B => 4
  | .six_A => 6

variable {a z₀ b z u x c : G}

theorem TwoClasses.orderOf_of_mem_tableVIISet (h : TwoClasses a z₀ b z u) {K : TableVIIClass}
    (hc : c ∈ tableVIISet a z₀ x K) : orderOf (x * c) = tableVIIOrder K := by
  cases K with
  | two_A => exact (orderOf_eq_of_isConj hc.2).symm.trans h.orderOf_a
  | two_B => exact (orderOf_eq_of_isConj hc.2).symm.trans h.orderOf_z₀
  | four_A => exact hc.2.1
  | four_B => exact hc.2.1
  | six_A => exact hc.2.1

theorem TwoClasses.tableVII_unique (h : TwoClasses a z₀ b z u) {K K' : TableVIIClass}
    (hK : c ∈ tableVIISet a z₀ x K) (hK' : c ∈ tableVIISet a z₀ x K') : K = K' := by
  have o := h.orderOf_of_mem_tableVIISet hK
  have o' := h.orderOf_of_mem_tableVIISet hK'
  cases K <;> cases K' <;> first
    | rfl
    | (exfalso; rw [o] at o'; norm_num [tableVIIOrder] at o'; done)
    | (exfalso; exact h.not_isConj (hK.2.trans hK'.2.symm))
    | (exfalso; exact h.not_isConj (hK'.2.trans hK.2.symm))
    | (exfalso; exact h.not_isConj (hK'.2.2.trans hK.2.2.symm))
    | (exfalso; exact h.not_isConj (hK.2.2.trans hK'.2.2.symm))

theorem tableVIISet_conj {g : G} (hg : g ∈ Subgroup.centralizer ({x} : Set G))
    {K : TableVIIClass} (hc : c ∈ tableVIISet a z₀ x K) :
    g * c * g⁻¹ ∈ tableVIISet a z₀ x K := by
  have hxc : x * (g * c * g⁻¹) = g * (x * c) * g⁻¹ := (conj_mul_of_mem_centralizer hg c).symm
  cases K with
  | two_A =>
    refine ⟨hc.1.trans (isConj_conj_self g c), ?_⟩
    rw [hxc]
    exact hc.2.trans (isConj_conj_self g _)
  | two_B =>
    refine ⟨hc.1.trans (isConj_conj_self g c), ?_⟩
    rw [hxc]
    exact hc.2.trans (isConj_conj_self g _)
  | four_A =>
    refine ⟨hc.1.trans (isConj_conj_self g c), ?_, ?_⟩
    · rw [hxc, orderOf_conj_eq]
      exact hc.2.1
    · rw [hxc, conj_pow]
      exact hc.2.2.trans (isConj_conj_self g _)
  | four_B =>
    refine ⟨hc.1.trans (isConj_conj_self g c), ?_, ?_⟩
    · rw [hxc, orderOf_conj_eq]
      exact hc.2.1
    · rw [hxc, conj_pow]
      exact hc.2.2.trans (isConj_conj_self g _)
  | six_A =>
    refine ⟨hc.1.trans (isConj_conj_self g c), ?_, ?_⟩
    · rw [hxc, orderOf_conj_eq]
      exact hc.2.1
    · rw [hxc, conj_pow]
      exact hc.2.2.trans (isConj_conj_self g _)

end TableVII

section Fusion

variable {G : Type} [Group G] {a z₀ b z u x c : G}

theorem TwoClasses.exists_of_isConj_mul (h : TwoClasses a z₀ b z u) (habb : IsConj a (a * b))
    (hx : IsConj a x) :
    ∃ x' z' u' : G, TwoClasses x z₀ x' z' u' ∧ IsConj x (x * x') := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hx
  refine ⟨g * b * g⁻¹, g * z * g⁻¹, g * u * g⁻¹, hg ▸ h.conj g, ?_⟩
  rw [← hg]
  have : g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
  rw [this]
  exact isConj_conj_conj g habb

theorem TwoClasses.exists_conj_of_mem_twoBNbr {x' z' u' : G} (hX : TwoClasses x z₀ x' z' u')
    (hxb : IsConj x (x * x')) (hcx : IsConj x c) (hxc : IsConj z₀ (x * c)) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = x * z' := by
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf hX.orderOf_a
  have hc2 : orderOf c = 2 := (orderOf_eq_of_isConj hcx).symm.trans hX.orderOf_a
  have hcc : c * c = 1 := mul_self_eq_one_of_orderOf hc2
  have hxc2 : orderOf (x * c) = 2 := (orderOf_eq_of_isConj hxc).symm.trans hX.orderOf_z₀
  have hcomm : x * c = c * x :=
    mul_comm_of_mul_self_eq_one hxx hcc (mul_self_eq_one_of_orderOf hxc2)
  have hcC : c ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
  have hcx' : c ≠ x := by
    rintro rfl
    rw [hcc, orderOf_one] at hxc2
    omega
  obtain ⟨g, hg, hcase⟩ := hX.tableV.cover c hcC hc2 hcx'
  have hconj : ∀ y, g * c * g⁻¹ = y → IsConj c y := fun y e => isConj_iff.mpr ⟨g, e⟩
  rcases hcase with e | e | e | e
  · exfalso
    have hgxc : g * (x * c) * g⁻¹ = x * x' := by rw [conj_mul_of_mem_centralizer hg c, e]
    exact hX.not_isConj (hxb.trans (isConj_iff.mpr ⟨g, hgxc⟩).symm |>.trans hxc.symm)
  · exact absurd ((hcx.trans (hconj _ e)).trans hX.isConj_z.symm) hX.not_isConj
  · exact ⟨g, hg, e⟩
  · exact absurd ((hcx.trans (hconj _ e)).trans hX.isConj_u.symm) hX.not_isConj

theorem TwoClasses.mem_tableVISet_dihedral (h : TwoClasses a z₀ b z u) {m : ℕ}
    (hx : IsConj a x) (hc : IsConj a c) (hm : orderOf (x * c) = 2 * m) (hm1 : 1 < m)
    (hwA : IsConj a ((x * c) ^ m)) :
    (x * c) ^ m ∈ twoANbr a x ∧ c ∈ tableVISet a x ((x * c) ^ m) := by
  have hxx : x * x = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hx).symm.trans h.orderOf_a)
  have hcc : c * c = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hc).symm.trans h.orderOf_a)
  obtain ⟨hww, hw1, hwx, hwc, -⟩ := dihedral_data hxx hcc hm (by omega)
  obtain ⟨hwxA, hwcA⟩ := dihedral_isConj (m := m) hx hc hxx hcc
  refine ⟨⟨hwA, by rw [← hwx]; exact hwxA⟩, ⟨hc, hwcA⟩, ?_, ?_⟩
  · rintro rfl
    rw [hxx, orderOf_one] at hm
    omega
  · intro e
    have hxc : x * c = (x * c) ^ m := by
      calc x * c = x * (x * (x * c) ^ m) := by rw [← e]
        _ = (x * c) ^ m := by rw [← mul_assoc, hxx, one_mul]
    have h2 : orderOf ((x * c) ^ m) = 2 := orderOf_eq_two_of_mul_self hww hw1
    rw [← hxc, hm] at h2
    omega

theorem TwoClasses.fourANbr_data (h : TwoClasses a z₀ b z u) (hx : IsConj a x)
    (hc : c ∈ fourANbr a z₀ x) :
    x ∈ leechQ ((x * c) ^ 2) ∧ c ∈ leechQ ((x * c) ^ 2) := by
  have hxx : x * x = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hx).symm.trans h.orderOf_a)
  have hcc : c * c = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hc.1).symm.trans h.orderOf_a)
  obtain ⟨hww, hw1, hwx, hwc, -⟩ := dihedral_data (m := 2) hxx hcc (by rw [hc.2.1]) (by norm_num)
  obtain ⟨hwxA, hwcA⟩ := dihedral_isConj (m := 2) hx hc.1 hxx hcc
  exact ⟨h.mem_leechQ_of_isConj_mul hx hc.2.2 hwx.symm (by rw [← hwx]; exact hwxA),
    h.mem_leechQ_of_isConj_mul hc.1 hc.2.2 hwc.symm (by rw [← hwc]; exact hwcA)⟩

theorem TwoClasses.mem_tableVIOrbit_four_B (h : TwoClasses a z₀ b z u) (hx : IsConj a x)
    (hc : c ∈ fourBNbr a x) :
    (x * c) ^ 2 ∈ twoANbr a x ∧ c ∈ tableVIOrbit a z₀ x ((x * c) ^ 2) .four_B := by
  obtain ⟨hw, hcO⟩ := h.mem_tableVISet_dihedral (m := 2) hx hc.1 (by rw [hc.2.1]) (by norm_num)
    hc.2.2
  exact ⟨hw, hcO, rfl⟩

theorem TwoClasses.mem_tableVIOrbit_six_A (h : TwoClasses a z₀ b z u) (hx : IsConj a x)
    (hc : c ∈ sixANbr a x) :
    (x * c) ^ 3 ∈ twoANbr a x ∧ c ∈ tableVIOrbit a z₀ x ((x * c) ^ 3) .six_A := by
  obtain ⟨hw, hcO⟩ := h.mem_tableVISet_dihedral (m := 3) hx hc.1 (by rw [hc.2.1]) (by norm_num)
    hc.2.2
  exact ⟨hw, hcO, rfl⟩

theorem TwoClasses.mem_tableVISet_of_mem_inter (h : TwoClasses a z₀ b z u) {b₁ : G}
    (hx : IsConj a x) (hc : IsConj a c) (hb₁x : b₁ ∈ twoANbr a x) (hb₁c : b₁ ∈ twoANbr a c)
    (hord : orderOf (x * c) ≠ 1 ∧ orderOf (x * c) ≠ 2) : c ∈ tableVISet a x b₁ := by
  have hb₁2 : orderOf b₁ = 2 := (orderOf_eq_of_isConj hb₁x.1).symm.trans h.orderOf_a
  have hb₁b₁ : b₁ * b₁ = 1 := mul_self_eq_one_of_orderOf hb₁2
  have hc2 : orderOf c = 2 := (orderOf_eq_of_isConj hc).symm.trans h.orderOf_a
  have hcc : c * c = 1 := mul_self_eq_one_of_orderOf hc2
  have hcb₁ : c * b₁ = b₁ * c :=
    mul_comm_of_mul_self_eq_one hcc hb₁b₁ (mul_self_eq_one_of_orderOf
      ((orderOf_eq_of_isConj hb₁c.2).symm.trans h.orderOf_a))
  have hx2 : orderOf x = 2 := (orderOf_eq_of_isConj hx).symm.trans h.orderOf_a
  refine ⟨⟨hc, by rw [← hcb₁]; exact hb₁c.2⟩, ?_, ?_⟩
  · rintro rfl
    exact hord.1 (by rw [mul_self_eq_one_of_orderOf hx2, orderOf_one])
  · intro e
    apply hord.2
    have hxx : x * x = 1 := mul_self_eq_one_of_orderOf hx2
    rw [e, ← mul_assoc, hxx, one_mul]
    exact hb₁2

end Fusion

section Main

variable {G : Type} [Group G] [Finite G] {d₀ : B}

theorem exists_twoClasses_isConj_mul
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) :
    ∃ b z u : G, TwoClasses a z₀ b z u ∧ IsConj a (a * b) := by
  obtain ⟨b, z, u, hTVz, hab, habb, hz₀z, hacz, haQ, hz₀u, hz₀au, hauQ, hcard⟩ :=
    s31_two hSLS hTV hL hG
  exact ⟨b, z, u, ⟨hTVz, hG.1.1, hG.2.1, hG.not_isConj, hab, hz₀z, hacz, haQ, hz₀u, hz₀au, hauQ,
    hcard, fun w hw => hG.2.of_isConj hw, fun w hw => hL G w (hG.2.of_isConj hw)⟩, habb⟩

theorem isConj_of_mem_twoANbr
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x c c' : G} (hx : IsConj a x)
    (hc : c ∈ twoANbr a x) (hc' : c' ∈ twoANbr a x) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = c' := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  exact h.exists_conj_of_mem_twoANbr hx hc hc'

theorem isConj_of_mem_twoBNbr
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x c c' : G} (hx : IsConj a x)
    (hc : c ∈ twoBNbr a z₀ x) (hc' : c' ∈ twoBNbr a z₀ x) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = c' := by
  obtain ⟨b₀, z, u, h, habb⟩ := exists_twoClasses_isConj_mul hSLS hTV hL hG
  obtain ⟨x', z', u', hX, hxb⟩ := h.exists_of_isConj_mul habb hx
  obtain ⟨g, hg, e⟩ := hX.exists_conj_of_mem_twoBNbr hxb (hx.symm.trans hc.1) hc.2
  obtain ⟨g', hg', e'⟩ := hX.exists_conj_of_mem_twoBNbr hxb (hx.symm.trans hc'.1) hc'.2
  refine ⟨g'⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _ hg') hg, ?_⟩
  have : c' = g'⁻¹ * (x * z') * g' := by rw [← e']; group
  rw [this, ← e]
  group

theorem card_centralizer_inf_of_mem_twoBNbr
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x c : G} (hx : IsConj a x)
    (hc : c ∈ twoBNbr a z₀ x) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) =
      tableVOrderZ := by
  obtain ⟨b₀, z, u, h, habb⟩ := exists_twoClasses_isConj_mul hSLS hTV hL hG
  obtain ⟨x', z', u', hX, hxb⟩ := h.exists_of_isConj_mul habb hx
  obtain ⟨g, hg, e⟩ := hX.exists_conj_of_mem_twoBNbr hxb (hx.symm.trans hc.1) hc.2
  rw [← card_inf_centralizer_conj hg c, e, centralizer_inf_mul_eq]
  exact hX.tableV.card_z

theorem isConj_of_mem_fourANbr
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hLP : LeechPairStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀)
    {x c c' : G} (hx : IsConj a x) (hc : c ∈ fourANbr a z₀ x) (hc' : c' ∈ fourANbr a z₀ x) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = c' := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨hxQ, hcQ⟩ := h.fourANbr_data hx hc
  obtain ⟨hxQ', hcQ'⟩ := h.fourANbr_data hx hc'
  obtain ⟨g₁, hg₁a, hg₁z⟩ := h.exists_conj_of_mem_leechQ hc.2.2 hx hxQ
  obtain ⟨g₂, hg₂a, hg₂z⟩ := h.exists_conj_of_mem_leechQ hc'.2.2 hx hxQ'
  obtain ⟨g, hg, hgw⟩ := exists_mem_centralizer_conj hg₁z hg₁a hg₂z hg₂a
  have hc'' : g * c * g⁻¹ ∈ fourANbr a z₀ x := tableVIISet_conj (K := .four_A) hg hc
  have hsq'' : (x * (g * c * g⁻¹)) ^ 2 = (x * c') ^ 2 := by
    rw [← conj_mul_of_mem_centralizer hg c, conj_pow]
    exact hgw
  obtain ⟨hxQ'', hcQ''⟩ := h.fourANbr_data hx hc''
  rw [hsq''] at hxQ'' hcQ''
  have hwB : IsConj z₀ ((x * c') ^ 2) := hc'.2.2
  have hLP' := hLP G _ (h.gms _ hwB)
  have hxsq : (x * (g * c * g⁻¹)) * (x * (g * c * g⁻¹)) = (x * c') ^ 2 := by
    rw [← pow_two]
    exact hsq''
  have hxsq' : (x * c') * (x * c') = (x * c') ^ 2 := (pow_two _).symm
  obtain ⟨k, hk, hkx, hkc⟩ := hLP'.1 x (g * c * g⁻¹) x c' (h.isLeechTwo_of_mem hwB hxQ'' hx)
    (h.isLeechTwo_of_mem hwB hcQ'' hc''.1) (h.isLeechTwo_of_mem hwB hxQ' hx)
    (h.isLeechTwo_of_mem hwB hcQ' hc'.1) hxsq hxsq'
  refine ⟨k * g, Subgroup.mul_mem _ ?_ hg, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * x = k * x * k⁻¹ * k := by group
      _ = x * k := by rw [hkx]
  · calc k * g * c * (k * g)⁻¹ = k * (g * c * g⁻¹) * k⁻¹ := by group
      _ = c' := hkc

theorem card_centralizer_inf_of_mem_fourANbr
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hLP : LeechPairStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀)
    {x c : G} (hx : IsConj a x) (hc : c ∈ fourANbr a z₀ x) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) =
      2 ^ 30 * 3 ^ 6 * 5 ^ 3 * 7 * 11 := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨hxQ, hcQ⟩ := h.fourANbr_data hx hc
  have hwB : IsConj z₀ ((x * c) ^ 2) := hc.2.2
  have hcard := (hLP G _ (h.gms _ hwB)).2.1 x c (h.isLeechTwo_of_mem hwB hxQ hx)
    (h.isLeechTwo_of_mem hwB hcQ hc.1) (pow_two (x * c)).symm
  rw [inf_assoc, inf_eq_right.mpr (centralizer_inf_le_centralizer_pow x c 2)] at hcard
  exact hcard

theorem isConj_of_mem_fourBNbr
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hDC : DoubleCoverThreeSwapIn G) (hLP : LeechPairStatement) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {x c c' : G} (hx : IsConj a x) (hc : c ∈ fourBNbr a x)
    (hc' : c' ∈ fourBNbr a x) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = c' := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨hw, -⟩ := h.mem_tableVIOrbit_four_B hx hc
  obtain ⟨hw', hcO'⟩ := h.mem_tableVIOrbit_four_B hx hc'
  obtain ⟨g, hg, hgw⟩ := h.exists_conj_of_mem_twoANbr hx hw hw'
  have hc'' : g * c * g⁻¹ ∈ fourBNbr a x := tableVIISet_conj (z₀ := z₀) (K := .four_B) hg hc
  obtain ⟨-, hcO''⟩ := h.mem_tableVIOrbit_four_B hx hc''
  have hsq'' : (x * (g * c * g⁻¹)) ^ 2 = (x * c') ^ 2 := by
    rw [← conj_mul_of_mem_centralizer hg c, conj_pow]
    exact hgw
  rw [hsq''] at hcO''
  obtain ⟨k, hk, hkc⟩ := s341_transitive hSLS hTV hL hT3 hT4 hDC hLP hG hx hw' hcO'' hcO'
  refine ⟨k * g, Subgroup.mul_mem _ (Subgroup.mem_inf.mp hk).1 hg, ?_⟩
  calc k * g * c * (k * g)⁻¹ = k * (g * c * g⁻¹) * k⁻¹ := by group
    _ = c' := hkc

theorem isConj_of_mem_sixANbr
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hDC : DoubleCoverThreeSwapIn G) (hLP : LeechPairStatement) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {x c c' : G} (hx : IsConj a x) (hc : c ∈ sixANbr a x)
    (hc' : c' ∈ sixANbr a x) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = c' := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨hw, -⟩ := h.mem_tableVIOrbit_six_A hx hc
  obtain ⟨hw', hcO'⟩ := h.mem_tableVIOrbit_six_A hx hc'
  obtain ⟨g, hg, hgw⟩ := h.exists_conj_of_mem_twoANbr hx hw hw'
  have hc'' : g * c * g⁻¹ ∈ sixANbr a x := tableVIISet_conj (z₀ := z₀) (K := .six_A) hg hc
  obtain ⟨-, hcO''⟩ := h.mem_tableVIOrbit_six_A hx hc''
  have hsq'' : (x * (g * c * g⁻¹)) ^ 3 = (x * c') ^ 3 := by
    rw [← conj_mul_of_mem_centralizer hg c, conj_pow]
    exact hgw
  rw [hsq''] at hcO''
  obtain ⟨k, hk, hkc⟩ := s341_transitive hSLS hTV hL hT3 hT4 hDC hLP hG hx hw' hcO'' hcO'
  refine ⟨k * g, Subgroup.mul_mem _ (Subgroup.mem_inf.mp hk).1 hg, ?_⟩
  calc k * g * c * (k * g)⁻¹ = k * (g * c * g⁻¹) * k⁻¹ := by group
    _ = c' := hkc

theorem card_centralizer_inf_of_mem_fourBNbr
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hDC : DoubleCoverThreeSwapIn G) (hLP : LeechPairStatement) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {x c : G} (hx : IsConj a x) (hc : c ∈ fourBNbr a x) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) =
      2 ^ 25 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17 := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨hw, hcO⟩ := h.mem_tableVIOrbit_four_B hx hc
  have hcard := s341_card hSLS hTV hL hT3 hT4 hDC hLP hG hx hw hcO
  rw [inf_right_comm, inf_eq_left.mpr (centralizer_inf_le_centralizer_pow x c 2)] at hcard
  exact hcard

theorem card_centralizer_inf_of_mem_sixANbr
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hDC : DoubleCoverThreeSwapIn G) (hLP : LeechPairStatement) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {x c : G} (hx : IsConj a x) (hc : c ∈ sixANbr a x) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) =
      2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨hw, hcO⟩ := h.mem_tableVIOrbit_six_A hx hc
  have hcard := s341_card hSLS hTV hL hT3 hT4 hDC hLP hG hx hw hcO
  rw [inf_right_comm, inf_eq_left.mpr (centralizer_inf_le_centralizer_pow x c 3)] at hcard
  exact hcard

theorem exists_mem_tableVIISet
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {x c : G} (hx : IsConj a x) (hc : IsConj a c)
    (hev : Even (orderOf (x * c))) : ∃ K : TableVIIClass, c ∈ tableVIISet a z₀ x K := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  have hxx : x * x = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hx).symm.trans h.orderOf_a)
  have hcc : c * c = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hc).symm.trans h.orderOf_a)
  by_cases hcomm : x * c = c * x
  · have hsq : (x * c) * (x * c) = 1 := by
      calc (x * c) * (x * c) = x * (c * x) * c := by group
        _ = x * (x * c) * c := by rw [hcomm]
        _ = 1 := by rw [← mul_assoc, hxx, one_mul, hcc]
    have hdvd : orderOf (x * c) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have ht2 : orderOf (x * c) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · rw [h1] at hev
        exact absurd hev Nat.not_even_one
      · exact h1
    have htC : x * c ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * c * x = x * (c * x) := mul_assoc _ _ _
        _ = x * (x * c) := by rw [hcomm]
    rcases h.isConj_or_isConj_of_mem_centralizer hx htC ht2 with hA | hB
    · exact ⟨.two_A, hc, hA⟩
    · exact ⟨.two_B, hc, hB⟩
  · obtain ⟨m, hm⟩ := hev
    have hm2 : orderOf (x * c) = 2 * m := by omega
    have hmpos : 0 < m := by
      have := orderOf_pos (x * c)
      omega
    have hm1 : 1 < m := by
      by_contra hle
      have hm1 : m = 1 := by omega
      apply hcomm
      have h1 := pow_orderOf_eq_one (x * c)
      rw [hm2, hm1, pow_two] at h1
      exact mul_comm_of_mul_self_eq_one hxx hcc h1
    obtain ⟨hww, hw1, hwx, hwc, -⟩ := dihedral_data hxx hcc hm2 hmpos
    obtain ⟨hwxA, hwcA⟩ := dihedral_isConj (m := m) hx hc hxx hcc
    have hw2 : orderOf ((x * c) ^ m) = 2 := orderOf_eq_two_of_mul_self hww hw1
    have hwC : (x * c) ^ m ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hwx
    rcases h.isConj_or_isConj_of_mem_centralizer hx hwC hw2 with hwA | hwB
    ·
      obtain ⟨hw', hcO⟩ := h.mem_tableVISet_dihedral hx hc hm2 hm1 hwA
      obtain ⟨b₁, z₁, u₁, φ, C⟩ := exists_tableVICtx hSLS hTV hL hT3 hT4 hG hx hw'
      obtain ⟨K, hK⟩ := C.exists_cond hcO
      have hord := C.orderOf_of_cond hcO hK
      cases K with
      | two_A => simp only [tableVIOrder] at hord; omega
      | two_B => simp only [tableVIOrder] at hord; omega
      | four_B =>
        simp only [tableVIOrder] at hord
        refine ⟨.four_B, hc, hord, ?_⟩
        have hK' : (x * c) ^ 2 = (x * c) ^ m := hK
        rw [hK']
        exact hwA
      | four_A =>
        exfalso
        simp only [tableVIOrder] at hord
        have hm' : m = 2 := by omega
        subst hm'
        exact h.not_isConj (hwA.trans hK.2.symm)
      | three_A => simp only [tableVIOrder] at hord; omega
      | six_A =>
        simp only [tableVIOrder] at hord
        refine ⟨.six_A, hc, hord, ?_⟩
        have hK' : (x * c) ^ 3 = (x * c) ^ m := hK
        rw [hK']
        exact hwA
    ·
      have hxQ : x ∈ leechQ ((x * c) ^ m) :=
        h.mem_leechQ_of_isConj_mul hx hwB hwx.symm (by rw [← hwx]; exact hwxA)
      have hcQ : c ∈ leechQ ((x * c) ^ m) :=
        h.mem_leechQ_of_isConj_mul hc hwB hwc.symm (by rw [← hwc]; exact hwcA)
      have hcomm' := leechQ_commutator_mem_zpowers (h.gms _ hwB) hxQ hcQ
      rw [inv_eq_of_mul_eq_one_right hxx, inv_eq_of_mul_eq_one_right hcc,
        mem_zpowers_iff_of_orderOf_eq_two hw2] at hcomm'
      rcases hcomm' with h1 | h1
      · exfalso
        apply hcomm
        exact mul_comm_of_mul_self_eq_one hxx hcc (by rw [← h1]; group)
      · have hsq : (x * c) * (x * c) = (x * c) ^ m := by rw [← h1]; group
        have hord4 : orderOf (x * c) = 4 :=
          orderOf_eq_four_of_mul_self (by rw [hsq]; exact hw1) (by rw [hsq]; exact hww)
        have hm' : m = 2 := by omega
        subst hm'
        exact ⟨.four_A, hc, hord4, hwB⟩

theorem table7_classify (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {x c : G} (hx : IsConj a x) (hc : IsConj a c)
    (hev : Even (orderOf (x * c))) : ∃! K : TableVIIClass, c ∈ tableVIISet a z₀ x K := by
  obtain ⟨K, hK⟩ := exists_mem_tableVIISet hSLS hTV hL hT3 hT4 hG hx hc hev
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  exact ⟨K, hK, fun K' hK' => h.tableVII_unique hK' hK⟩

theorem table7_cases (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {x c : G} (hx : IsConj a x) (hc : IsConj a c)
    (hev : Even (orderOf (x * c))) :
    c ∈ twoANbr a x ∨ c ∈ twoBNbr a z₀ x ∨ c ∈ fourANbr a z₀ x ∨ c ∈ fourBNbr a x ∨
      c ∈ sixANbr a x := by
  obtain ⟨K, hK⟩ := exists_mem_tableVIISet hSLS hTV hL hT3 hT4 hG hx hc hev
  cases K with
  | two_A => exact Or.inl hK
  | two_B => exact Or.inr (Or.inl hK)
  | four_A => exact Or.inr (Or.inr (Or.inl hK))
  | four_B => exact Or.inr (Or.inr (Or.inr (Or.inl hK)))
  | six_A => exact Or.inr (Or.inr (Or.inr (Or.inr hK)))

theorem table7_transitive (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hDC : DoubleCoverThreeSwapIn G) (hLP : LeechPairStatement) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {x c c' : G} (hx : IsConj a x) {K : TableVIIClass}
    (hc : c ∈ tableVIISet a z₀ x K) (hc' : c' ∈ tableVIISet a z₀ x K) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G), g * c * g⁻¹ = c' := by
  cases K with
  | two_A => exact isConj_of_mem_twoANbr hSLS hTV hL hG hx hc hc'
  | two_B => exact isConj_of_mem_twoBNbr hSLS hTV hL hG hx hc hc'
  | four_A => exact isConj_of_mem_fourANbr hSLS hTV hL hLP hG hx hc hc'
  | four_B => exact isConj_of_mem_fourBNbr hSLS hTV hL hT3 hT4 hDC hLP hG hx hc hc'
  | six_A => exact isConj_of_mem_sixANbr hSLS hTV hL hT3 hT4 hDC hLP hG hx hc hc'

theorem table7_card (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hDC : DoubleCoverThreeSwapIn G) (hLP : LeechPairStatement) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {x c : G} (hx : IsConj a x) {K : TableVIIClass}
    (hc : c ∈ tableVIISet a z₀ x K) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) =
      tableVIIStab K := by
  cases K with
  | two_A => exact card_centralizer_inf_twoANbr hSLS hTV hL hG hx hc
  | two_B => exact card_centralizer_inf_of_mem_twoBNbr hSLS hTV hL hG hx hc
  | four_A => exact card_centralizer_inf_of_mem_fourANbr hSLS hTV hL hLP hG hx hc
  | four_B => exact card_centralizer_inf_of_mem_fourBNbr hSLS hTV hL hT3 hT4 hDC hLP hG hx hc
  | six_A => exact card_centralizer_inf_of_mem_sixANbr hSLS hTV hL hT3 hT4 hDC hLP hG hx hc

theorem table7_nonempty
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x : G}
    (hx : IsConj a x) (K : TableVIIClass) : (tableVIISet a z₀ x K).Nonempty := by
  obtain ⟨b₀, z, u, h, habb⟩ := exists_twoClasses_isConj_mul hSLS hTV hL hG
  obtain ⟨x', z', u', hX, hxb⟩ := h.exists_of_isConj_mul habb hx
  have hx'nbr : x' ∈ twoANbr a x := ⟨hx.trans hX.isConj_b, hx.trans hxb⟩
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf
    ((orderOf_eq_of_isConj hx).symm.trans h.orderOf_a)
  have hpos : ∀ K', 0 < (tableVIOrbit a z₀ x x' K').ncard := fun K' => by
    rw [s341_ncard hSLS hTV hL hT3 hT4 hG hx hx'nbr K']
    exact tableVISize_pos K'
  cases K with
  | two_A => exact ⟨x', hx'nbr⟩
  | two_B =>
    refine ⟨x * z', hx.trans hX.isConj_az, ?_⟩
    rw [← mul_assoc, hxx, one_mul]
    exact hX.isConj_z
  | four_A =>
    obtain ⟨c, hc⟩ := Set.nonempty_of_ncard_ne_zero (hpos .four_A).ne'
    exact ⟨c, hc.1.1.1, hc.2⟩
  | four_B =>
    obtain ⟨c, hc⟩ := Set.nonempty_of_ncard_ne_zero (hpos .four_B).ne'
    obtain ⟨b₁, z₁, u₁, φ, C⟩ := exists_tableVICtx hSLS hTV hL hT3 hT4 hG hx hx'nbr
    have ho := C.orderOf_of_cond hc.1 hc.2
    have hsq : (x * c) ^ 2 = x' := hc.2
    exact ⟨c, hc.1.1.1, ho, by rw [hsq]; exact hx.trans hX.isConj_b⟩
  | six_A =>
    obtain ⟨c, hc⟩ := Set.nonempty_of_ncard_ne_zero (hpos .six_A).ne'
    obtain ⟨b₁, z₁, u₁, φ, C⟩ := exists_tableVICtx hSLS hTV hL hT3 hT4 hG hx hx'nbr
    have ho := C.orderOf_of_cond hc.1 hc.2
    have hcube : (x * c) ^ 3 = x' := hc.2
    exact ⟨c, hc.1.1.1, ho, by rw [hcube]; exact hx.trans hX.isConj_b⟩

theorem table7_ncard
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hT3 : BabyTableIII) (hT4 : BabyTableIV) (hDC : DoubleCoverThreeSwapIn G)
    (hLP : LeechPairStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x : G} (hx : IsConj a x)
    (K : TableVIIClass) : (tableVIISet a z₀ x K).ncard = tableVIISize K := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨c, hc⟩ := table7_nonempty hSLS hTV hL hT3 hT4 hG hx K
  have horb := card_inf_centralizer_mul_ncard (G := G) (H := Subgroup.centralizer ({x} : Set G))
    (Y := tableVIISet a z₀ x K) (fun g hg q hq => tableVIISet_conj hg hq)
    (fun q hq q' hq' => table7_transitive hSLS hTV hL hT3 hT4 hDC hLP hG hx hq hq') hc
  rw [table7_card hSLS hTV hL hT3 hT4 hDC hLP hG hx hc,
    (card_centralizer_eq_of_isConj hx).symm.trans h.tableV.card_centralizer] at horb
  apply Nat.eq_of_mul_eq_mul_left (tableVIIStab_pos K)
  rw [horb, tableVIIStab_mul_size]

theorem s342_one
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x b c : G}
    (hx : IsConj a x) (hb : b ∈ twoANbr a x) (hc : c ∈ tableVISet a x b)
    (hK : tableVICond a z₀ b x .four_B c ∨ tableVICond a z₀ b x .six_A c) :
    twoANbr a x ∩ twoANbr a c = {b} := by
  obtain ⟨b₀, z, u, φ, C⟩ := exists_tableVICtx hSLS hTV hL hT3 hT4 hG hx hb
  apply Set.Subset.antisymm
  · rintro b' ⟨hb'x, hb'c⟩
    have hb'2 : orderOf b' = 2 := (orderOf_eq_of_isConj hb'x.1).symm.trans C.two.orderOf_a
    have hord : orderOf (x * c) ≠ 1 ∧ orderOf (x * c) ≠ 2 := by
      rcases hK with hK | hK
      · have := C.orderOf_of_cond hc hK
        simp only [tableVIOrder] at this
        omega
      · have := C.orderOf_of_cond hc hK
        simp only [tableVIOrder] at this
        omega
    have hcO' : c ∈ tableVISet a x b' :=
      C.two.mem_tableVISet_of_mem_inter hx hc.1.1 hb'x hb'c hord
    obtain ⟨b₁, z₁, u₁, φ', C'⟩ := exists_tableVICtx hSLS hTV hL hT3 hT4 hG hx hb'x
    obtain ⟨K', hK'⟩ := C'.exists_cond hcO'
    have ho' := C'.orderOf_of_cond hcO' hK'
    show b' = b
    rcases hK with hK | hK
    · have ho := C.orderOf_of_cond hc hK
      simp only [tableVIOrder] at ho
      cases K' with
      | two_A => simp only [tableVIOrder] at ho'; omega
      | two_B => simp only [tableVIOrder] at ho'; omega
      | four_B => exact hK'.symm.trans hK
      | four_A =>
        exfalso
        have hK2 : (x * c) ^ 2 = b := hK
        have : IsConj z₀ b := by rw [← hK2]; exact hK'.2
        exact C.two.not_isConj (C.mem_nbr.1.trans this.symm)
      | three_A => simp only [tableVIOrder] at ho'; omega
      | six_A => simp only [tableVIOrder] at ho'; omega
    · have ho := C.orderOf_of_cond hc hK
      simp only [tableVIOrder] at ho
      cases K' with
      | two_A => simp only [tableVIOrder] at ho'; omega
      | two_B => simp only [tableVIOrder] at ho'; omega
      | four_B => simp only [tableVIOrder] at ho'; omega
      | four_A => simp only [tableVIOrder] at ho'; omega
      | three_A => simp only [tableVIOrder] at ho'; omega
      | six_A => exact hK'.symm.trans hK
  · rintro b' rfl
    refine ⟨hb, hb.1, ?_⟩
    rw [← C.bc_comm hc]
    exact hc.1.2

omit [Finite G] in
theorem conj_mem_twoANbr_inter {a x c g b₁ : G}
    (hg : g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G))
    (hb : b₁ ∈ twoANbr a x ∩ twoANbr a c) :
    g * b₁ * g⁻¹ ∈ twoANbr a x ∩ twoANbr a c := by
  obtain ⟨hgx, hgc⟩ := Subgroup.mem_inf.mp hg
  refine ⟨⟨hb.1.1.trans (isConj_conj_self g b₁), ?_⟩, ⟨hb.2.1.trans (isConj_conj_self g b₁), ?_⟩⟩
  · rw [← conj_mul_of_mem_centralizer hgx b₁]
    exact hb.1.2.trans (isConj_conj_self g _)
  · rw [← conj_mul_of_mem_centralizer hgc b₁]
    exact hb.2.2.trans (isConj_conj_self g _)

omit [Finite G] in
theorem tableVICond_conj_of_mem_centralizer {a z₀ x c g : G}
    (hg : g ∈ Subgroup.centralizer ({x} : Set G)) {K : TableVIClass}
    (hK : K = .four_A ∨ K = .three_A) (b' : G) (hc : tableVICond a z₀ b' x K c) :
    tableVICond a z₀ b' x K (g * c * g⁻¹) := by
  have hxc : x * (g * c * g⁻¹) = g * (x * c) * g⁻¹ := (conj_mul_of_mem_centralizer hg c).symm
  rcases hK with rfl | rfl
  · refine ⟨?_, ?_⟩
    · show orderOf (x * (g * c * g⁻¹)) = 4
      rw [hxc, orderOf_conj_eq]
      exact hc.1
    · show IsConj z₀ ((x * (g * c * g⁻¹)) ^ 2)
      rw [hxc, conj_pow]
      exact hc.2.trans (isConj_conj_self g _)
  · show orderOf (x * (g * c * g⁻¹)) = 3
    rw [hxc, orderOf_conj_eq]
    exact hc

theorem s342_aux
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hT3 : BabyTableIII) (hT4 : BabyTableIV) (hDC : DoubleCoverThreeSwapIn G)
    (hLP : LeechPairStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x c : G} (hx : IsConj a x)
    (hc : IsConj a c) {K : TableVIClass} (hK : K = .four_A ∨ K = .three_A)
    (hKc : ∀ b', tableVICond a z₀ b' x K c) :
    (∀ b₁ ∈ twoANbr a x ∩ twoANbr a c, ∀ b₂ ∈ twoANbr a x ∩ twoANbr a c,
      ∃ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G),
        g * b₁ * g⁻¹ = b₂) ∧
    ∀ b₁ ∈ twoANbr a x ∩ twoANbr a c,
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({b₁} : Set G)) = tableVIStab K := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  have hord : orderOf (x * c) ≠ 1 ∧ orderOf (x * c) ≠ 2 := by
    rcases hK with rfl | rfl
    · have : orderOf (x * c) = 4 := (hKc x).1
      omega
    · have : orderOf (x * c) = 3 := hKc x
      omega
  have hmem : ∀ b₁ ∈ twoANbr a x ∩ twoANbr a c, c ∈ tableVIOrbit a z₀ x b₁ K :=
    fun b₁ hb₁ => ⟨h.mem_tableVISet_of_mem_inter hx hc hb₁.1 hb₁.2 hord, hKc b₁⟩
  refine ⟨?_, ?_⟩
  · intro b₁ hb₁ b₂ hb₂
    obtain ⟨g, hg, hgb⟩ := h.exists_conj_of_mem_twoANbr hx hb₁.1 hb₂.1
    have hb₂c' : b₂ ∈ twoANbr a (g * c * g⁻¹) := by
      refine ⟨hb₂.2.1, ?_⟩
      rw [← hgb]
      have : g * c * g⁻¹ * (g * b₁ * g⁻¹) = g * (c * b₁) * g⁻¹ := by group
      rw [this]
      exact hb₁.2.2.trans (isConj_conj_self g _)
    have hc'A : IsConj a (g * c * g⁻¹) := hc.trans (isConj_conj_self g c)
    have hord' : orderOf (x * (g * c * g⁻¹)) ≠ 1 ∧ orderOf (x * (g * c * g⁻¹)) ≠ 2 := by
      rw [← conj_mul_of_mem_centralizer hg c, orderOf_conj_eq]
      exact hord
    have hc'O : g * c * g⁻¹ ∈ tableVIOrbit a z₀ x b₂ K :=
      ⟨h.mem_tableVISet_of_mem_inter hx hc'A hb₂.1 hb₂c' hord',
        tableVICond_conj_of_mem_centralizer hg hK b₂ (hKc b₂)⟩
    obtain ⟨k, hk, hkc⟩ :=
      s341_transitive hSLS hTV hL hT3 hT4 hDC hLP hG hx hb₂.1 hc'O (hmem b₂ hb₂)
    obtain ⟨hkx, hkb⟩ := Subgroup.mem_inf.mp hk
    refine ⟨k * g, Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hkx hg, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc k * g * c = (k * g * c * (k * g)⁻¹) * (k * g) := by group
        _ = c * (k * g) := by
            rw [show k * g * c * (k * g)⁻¹ = k * (g * c * g⁻¹) * k⁻¹ by group, hkc]
    · have hkb' : k * b₂ * k⁻¹ = b₂ := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hkb, mul_inv_cancel_right]
      calc k * g * b₁ * (k * g)⁻¹ = k * (g * b₁ * g⁻¹) * k⁻¹ := by group
        _ = b₂ := by rw [hgb, hkb']
  · intro b₁ hb₁
    have := s341_card hSLS hTV hL hT3 hT4 hDC hLP hG hx hb₁.1 (hmem b₁ hb₁)
    rw [inf_right_comm]
    exact this

theorem s342_two
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hT3 : BabyTableIII) (hT4 : BabyTableIV) (hDC : DoubleCoverThreeSwapIn G)
    (hLP : LeechPairStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x c : G} (hx : IsConj a x)
    (hc : IsConj a c) (hK : orderOf (x * c) = 4 ∧ IsConj z₀ ((x * c) ^ 2)) :
    (∀ b₁ ∈ twoANbr a x ∩ twoANbr a c, ∀ b₂ ∈ twoANbr a x ∩ twoANbr a c,
      ∃ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G),
        g * b₁ * g⁻¹ = b₂) ∧
    ∀ b₁ ∈ twoANbr a x ∩ twoANbr a c,
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({b₁} : Set G)) = 2 ^ 29 * 3 ^ 6 * 5 * 7 :=
  s342_aux hSLS hTV hL hT3 hT4 hDC hLP hG hx hc (K := .four_A) (Or.inl rfl) fun _ => hK

theorem s342_three
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hL : LeechStatement)
    (hT3 : BabyTableIII) (hT4 : BabyTableIV) (hDC : DoubleCoverThreeSwapIn G)
    (hLP : LeechPairStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x c : G} (hx : IsConj a x)
    (hc : IsConj a c) (hK : orderOf (x * c) = 3) :
    (∀ b₁ ∈ twoANbr a x ∩ twoANbr a c, ∀ b₂ ∈ twoANbr a x ∩ twoANbr a c,
      ∃ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G),
        g * b₁ * g⁻¹ = b₂) ∧
    ∀ b₁ ∈ twoANbr a x ∩ twoANbr a c,
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({b₁} : Set G)) = 2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 :=
  s342_aux hSLS hTV hL hT3 hT4 hDC hLP hG hx hc (K := .three_A) (Or.inr rfl) fun _ => hK

end Main

end CFSG.Monster.GMS
