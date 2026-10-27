module

public import CFSG.RankThree.GF2n.Parrott.A1LocalData

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

open CFSG CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

structure Hyp (z s1 s2 : G) : Prop where
  hA1 : Tim79a.ParrottHypA1 z
  s1_mem : s1 ∈ H z
  s2_mem : s2 ∈ H z
  orderOf_s1 : orderOf s1 = 3
  orderOf_s2 : orderOf s2 = 3
  comm12 : s1 * s2 = s2 * s1
  heq : CJ z s1 = CJ z s2
  card_J0 : Nat.card (CJ z s1) = 8
  sup1 : CJ z s1 ⊔ ⁅zpowers s1, J z⁆ = J z
  inf1 : CJ z s1 ⊓ ⁅zpowers s1, J z⁆ = zpowers z
  comm1 : ∀ a ∈ CJ z s1, ∀ b ∈ ⁅zpowers s1, J z⁆, a * b = b * a
  card_Cs : Nat.card (CJ z (s1 * s2⁻¹)) = 32
  card_C12 : Nat.card (CJ z (s1 * s2)) = 128
  supS : CJ z (s1 * s2⁻¹) ⊔ ⁅zpowers (s1 * s2⁻¹), J z⁆ = J z
  infS : CJ z (s1 * s2⁻¹) ⊓ ⁅zpowers (s1 * s2⁻¹), J z⁆ = zpowers z
  commS : ∀ a ∈ CJ z (s1 * s2⁻¹), ∀ b ∈ ⁅zpowers (s1 * s2⁻¹), J z⁆, a * b = b * a

omit [Finite G] in
theorem commute_z_of_mem_H {g : G} (hg : g ∈ H z) : g * z = z * g :=
  (Subgroup.mem_centralizer_iff.mp hg z (Set.mem_singleton z)).symm

omit [Finite G] in
theorem CJ_le_J (σ : G) : CJ z σ ≤ J z := inf_le_right

omit [Finite G] in
theorem le_normalizer_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [h a ha b hb, mul_inv_cancel_right]
    exact hb
  · intro hb
    have hc := h a ha _ hb
    have hb' : b = a * b * a⁻¹ := by
      calc b = a⁻¹ * ((a * b * a⁻¹) * a) := by group
        _ = a⁻¹ * (a * (a * b * a⁻¹)) := by rw [hc]
        _ = a * b * a⁻¹ := by group
    rw [hb']
    exact hb

namespace Hyp

variable {s1 s2 : G} (hy : Hyp z s1 s2)
include hy

theorem z_mem_J : z ∈ J z := z_mem_J_A1 hy.hA1

theorem orderOf_z : orderOf z = 2 := orderOf_z_A1 hy.hA1

theorem z_sq : z * z = 1 := by
  rw [← pow_two, ← hy.orderOf_z, pow_orderOf_eq_one]

theorem centerIn_J_eq : centerIn (J z) = zpowers z := centerIn_J_eq_zpowers_A1 hy.hA1

theorem comm_mem {a b : G} (ha : a ∈ J z) (hb : b ∈ J z) : a * b * a⁻¹ * b⁻¹ ∈ zpowers z := by
  have hmem : ⁅a, b⁆ ∈ ⁅J z, J z⁆ := Subgroup.commutator_mem_commutator ha hb
  rw [hy.hA1.commutator, commutatorElement_def] at hmem
  exact hmem

theorem sq_mem {a : G} (ha : a ∈ J z) : a * a ∈ zpowers z := by
  have hc := CFSG.IsExtraspecial2.mul_self_mem_center_map hy.hA1.extraspecial ha
  rw [← CFSG.centerIn_eq_map_center, hy.centerIn_J_eq] at hc
  exact hc

theorem mem_zpowers_z_iff {g : G} : g ∈ zpowers z ↔ g = 1 ∨ g = z := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      obtain ⟨m, rfl⟩ : (2 : ℤ) ∣ k := Int.dvd_of_emod_eq_zero hk
      rw [zpow_mul, zpow_ofNat, pow_two, hy.z_sq, one_zpow]
    · right
      have hk' : k = 2 * (k / 2) + 1 := by omega
      rw [hk', zpow_add, zpow_mul, zpow_ofNat, pow_two, hy.z_sq, one_zpow, one_mul, zpow_one]
  · rintro (hg | hg)
    · rw [hg]
      exact Subgroup.one_mem _
    · rw [hg]
      exact Subgroup.mem_zpowers z

theorem commute_of_mem_zpowers_of_mem_H {g d : G} (hg : g ∈ H z) (hd : d ∈ zpowers z) :
    g * d = d * g := by
  rcases hy.mem_zpowers_z_iff.mp hd with hd1 | hdz
  · rw [hd1, mul_one, one_mul]
  · rw [hdz]
    exact commute_z_of_mem_H hg

theorem zpowers_le_J : zpowers z ≤ J z := Subgroup.zpowers_le.mpr hy.z_mem_J

theorem mem_zpowers_of_commute_J {a : G} (ha : a ∈ J z) (hc : ∀ b ∈ J z, a * b = b * a) :
    a ∈ zpowers z := by
  rw [← hy.centerIn_J_eq]
  exact ⟨ha, Subgroup.mem_centralizer_iff.mpr fun b hb => (hc b hb).symm⟩

theorem W_le_J : ⁅zpowers s1, J z⁆ ≤ J z := le_sup_right.trans hy.sup1.le

theorem R_le_J : ⁅zpowers (s1 * s2⁻¹), J z⁆ ≤ J z := le_sup_right.trans hy.supS.le

theorem zpowers_le_J0 : zpowers z ≤ CJ z s1 := hy.inf1.symm.le.trans inf_le_left

theorem zpowers_le_W : zpowers z ≤ ⁅zpowers s1, J z⁆ := hy.inf1.symm.le.trans inf_le_right

theorem zpowers_le_CJs : zpowers z ≤ CJ z (s1 * s2⁻¹) := hy.infS.symm.le.trans inf_le_left

theorem zpowers_le_R : zpowers z ≤ ⁅zpowers (s1 * s2⁻¹), J z⁆ :=
  hy.infS.symm.le.trans inf_le_right

theorem J0_le_CJs : CJ z s1 ≤ CJ z (s1 * s2⁻¹) := by
  intro a ha
  have ha2 : a ∈ CJ z s2 := hy.heq ▸ ha
  refine mem_CJ.mpr ⟨?_, (CJ_le_J _) ha⟩
  have h1 : s1 * a = a * s1 := by
    simpa using (Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp ha).1).symm
  have h2 : s2 * a = a * s2 := by
    simpa using (Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp ha2).1).symm
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h2' : s2⁻¹ * a = a * s2⁻¹ := by
    calc s2⁻¹ * a = s2⁻¹ * (a * s2) * s2⁻¹ := by group
      _ = s2⁻¹ * (s2 * a) * s2⁻¹ := by rw [h2]
      _ = a * s2⁻¹ := by group
  calc a * (s1 * s2⁻¹) = (a * s1) * s2⁻¹ := by group
    _ = (s1 * a) * s2⁻¹ := by rw [h1]
    _ = s1 * (a * s2⁻¹) := by group
    _ = s1 * (s2⁻¹ * a) := by rw [h2']
    _ = s1 * s2⁻¹ * a := by group

@[expose] def Q (_hy : Hyp z s1 s2) : Subgroup G := CJ z (s1 * s2⁻¹) ⊓ ⁅zpowers s1, J z⁆

theorem Q_le_W : hy.Q ≤ ⁅zpowers s1, J z⁆ := inf_le_right

theorem Q_le_CJs : hy.Q ≤ CJ z (s1 * s2⁻¹) := inf_le_left

theorem zpowers_le_Q : zpowers z ≤ hy.Q := le_inf hy.zpowers_le_CJs hy.zpowers_le_W

theorem exists_mul_J0_W {j : G} (hj : j ∈ J z) :
    ∃ a ∈ CJ z s1, ∃ w ∈ ⁅zpowers s1, J z⁆, j = a * w := by
  have hn : ⁅zpowers s1, J z⁆ ≤ Subgroup.normalizer (CJ z s1 : Set G) :=
    le_normalizer_of_commute fun w hw a ha => (hy.comm1 a ha w hw).symm
  rw [← hy.sup1, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hj
  obtain ⟨a, ha, w, hw, rfl⟩ := hj
  exact ⟨a, ha, w, hw, rfl⟩

theorem CJs_eq_sup : CJ z (s1 * s2⁻¹) = CJ z s1 ⊔ hy.Q := by
  apply le_antisymm
  · intro c hc
    obtain ⟨a, ha, w, hw, rfl⟩ := hy.exists_mul_J0_W ((CJ_le_J _) hc)
    have hwC : w ∈ CJ z (s1 * s2⁻¹) := by
      have : w = a⁻¹ * (a * w) := by group
      rw [this]
      exact (CJ z (s1 * s2⁻¹)).mul_mem ((CJ z (s1 * s2⁻¹)).inv_mem (hy.J0_le_CJs ha)) hc
    exact Subgroup.mul_mem_sup ha ⟨hwC, hw⟩
  · exact sup_le hy.J0_le_CJs hy.Q_le_CJs

theorem J0_inf_Q : CJ z s1 ⊓ hy.Q = zpowers z := by
  apply le_antisymm
  · rw [← hy.inf1]
    exact inf_le_inf_left _ hy.Q_le_W
  · exact le_inf hy.zpowers_le_J0 hy.zpowers_le_Q

theorem commute_J0_Q : ∀ a ∈ CJ z s1, ∀ b ∈ hy.Q, a * b = b * a :=
  fun a ha b hb => hy.comm1 a ha b (hy.Q_le_W hb)

theorem card_zpowers_z : Nat.card (zpowers z) = 2 := by
  rw [Nat.card_zpowers, hy.orderOf_z]

theorem card_Q : Nat.card hy.Q = 8 := by
  have hn : CJ z s1 ≤ Subgroup.normalizer (hy.Q : Set G) :=
    le_normalizer_of_commute hy.commute_J0_Q
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hn
  rw [← hy.CJs_eq_sup, hy.J0_inf_Q, hy.card_Cs, hy.card_zpowers_z, hy.card_J0] at h
  omega

@[expose] def R (_hy : Hyp z s1 s2) : Subgroup G := ⁅zpowers (s1 * s2⁻¹), J z⁆

theorem commute_CJs_R : ∀ c ∈ CJ z (s1 * s2⁻¹), ∀ r ∈ hy.R, c * r = r * c := hy.commS

theorem exists_mul_of_mem_J {j : G} (hj : j ∈ J z) :
    ∃ c ∈ CJ z (s1 * s2⁻¹), ∃ r ∈ hy.R, j = c * r := by
  have hn : ⁅zpowers (s1 * s2⁻¹), J z⁆ ≤ Subgroup.normalizer (CJ z (s1 * s2⁻¹) : Set G) :=
    le_normalizer_of_commute fun r hr c hc => (hy.commS c hc r hr).symm
  rw [← hy.supS, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hj
  obtain ⟨c, hc, r, hr, rfl⟩ := hj
  exact ⟨c, hc, r, hr, rfl⟩

theorem card_R : Nat.card hy.R = 32 := by
  have hn : CJ z (s1 * s2⁻¹) ≤ Subgroup.normalizer (hy.R : Set G) :=
    le_normalizer_of_commute hy.commute_CJs_R
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hn
  have hsup : CJ z (s1 * s2⁻¹) ⊔ hy.R = J z := hy.supS
  have hinf : CJ z (s1 * s2⁻¹) ⊓ hy.R = zpowers z := hy.infS
  rw [hsup, hinf, hy.hA1.card_J, hy.card_zpowers_z, hy.card_Cs] at h
  omega

theorem mem_zpowers_of_mem_CJs_of_commute {c : G} (hc : c ∈ CJ z (s1 * s2⁻¹))
    (hcomm : ∀ d ∈ CJ z (s1 * s2⁻¹), c * d = d * c) : c ∈ zpowers z := by
  apply hy.mem_zpowers_of_commute_J ((CJ_le_J _) hc)
  intro b hb
  obtain ⟨d, hd, r, hr, rfl⟩ := hy.exists_mul_of_mem_J hb
  calc c * (d * r) = (c * d) * r := by group
    _ = (d * c) * r := by rw [hcomm d hd]
    _ = d * (c * r) := by group
    _ = d * (r * c) := by rw [hy.commute_CJs_R c hc r hr]
    _ = d * r * c := by group

end Hyp

end CFSG.RankThree.GF2n.Parrott.A1Section2Local
