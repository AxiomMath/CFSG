module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36Cc

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

variable {G : Type} [Group G] [Finite G]

theorem S36_comm_of_pow {x g a : G} {k : ℤ} (hg3 : g ^ 3 = 1) (hgne : g ≠ 1)
    (hk : k % 3 = 1 ∨ k % 3 = 2) (ha : a = g ^ k) (hx : Commute x a) : Commute x g := by
  have hkk : (k * k) % 3 = 1 := by
    rcases hk with h | h <;> simp [Int.mul_emod, h]
  have hgak : a ^ k = g := by
    rw [ha, ← zpow_mul, ← zpow_mod3 hg3 hgne (k * k), hkk, zpow_one]
  have h := hx.zpow_right k
  rw [hgak] at h
  exact h

theorem S36_piece {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t)
    (h31 : FF84_3_1) (h33 : FF84_3_3) {a : G}
    (ha : a ∈ Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂) (hne : a ≠ 1) :
    Op 2 (Cen t) ⊓ Cen a ≤ (Op 2 (Cen t) ⊓ Cen b₁) ⊔ (Op 2 (Cen t) ⊓ Cen b₂) := by
  have hb1B : b₁ ∈ B := (Subgroup.mem_inf.1 d.sec.hb₁).1
  have hb2B : b₂ ∈ B := (Subgroup.mem_inf.1 d.sec.hb₂).1
  have hb1L : b₁ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₁).2
  have hb2L : b₂ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₂).2
  have hcom : Commute b₁ b₂ := comm_of_mem_B d.sec hb1B hb2B
  have p1 : b₁ ^ 3 = 1 := pow3_of_mem_B d.sec hb1B
  have p2 : b₂ ^ 3 = 1 := pow3_of_mem_B d.sec hb2B
  have n1 : b₁ ≠ 1 := b₁_ne_one d.sec
  have n2 : b₂ ≠ 1 := b₂_ne_one d.sec
  have htc' : ∀ x ∈ L, t * x = x * t := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 d.htL x hx).symm
  have htCen : t ∈ Cen t := S36_mem_cen_of rfl
  have hzT : Subgroup.zpowers t ≤ Op 2 (Cen t) :=
    S36_zpowers_op2 d.ht htCen (fun g hg => (S36_comm_of_cen hg).symm)
  have hzT1 : Subgroup.zpowers t ≤ Op 2 (Cen t) ⊓ Cen b₁ :=
    le_inf hzT (Subgroup.zpowers_le.2 (S36_mem_cen_of (htc' b₁ hb1L).symm))
  have hzT2 : Subgroup.zpowers t ≤ Op 2 (Cen t) ⊓ Cen b₂ :=
    le_inf hzT (Subgroup.zpowers_le.2 (S36_mem_cen_of (htc' b₂ hb2L).symm))
  have hCT := F6_CT_c d h31 h33
  have hc3 : (b₁ * b₂) ^ 3 = 1 := by rw [hcom.mul_pow, p1, p2, one_mul]
  have hcne : b₁ * b₂ ≠ 1 := b₁b₂_ne_one d.sec
  have hdcom : Commute b₁ (b₂ ^ 2) := hcom.pow_right 2
  have h6 : (b₂ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, p2, one_pow]
  have hd3 : (b₁ * b₂ ^ 2) ^ 3 = 1 := by rw [hdcom.mul_pow, p1, h6, one_mul]
  have hdne : b₁ * b₂ ^ 2 ≠ 1 := by
    rw [S36_sq_eq_inv p2]
    exact b₁b₂inv_ne_one d.sec
  intro x hx
  obtain ⟨hxT, hxa⟩ := Subgroup.mem_inf.1 hx
  have fb1 : Commute x b₁ → x ∈ (Op 2 (Cen t) ⊓ Cen b₁) ⊔ (Op 2 (Cen t) ⊓ Cen b₂) :=
    fun h => Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hxT, S36_mem_cen_of h.eq.symm⟩)
  have fb2 : Commute x b₂ → x ∈ (Op 2 (Cen t) ⊓ Cen b₁) ⊔ (Op 2 (Cen t) ⊓ Cen b₂) :=
    fun h => Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hxT, S36_mem_cen_of h.eq.symm⟩)
  have fc : Commute x (b₁ * b₂) → x ∈ (Op 2 (Cen t) ⊓ Cen b₁) ⊔ (Op 2 (Cen t) ⊓ Cen b₂) :=
    fun h => by
      have hxc : x ∈ Op 2 (Cen t) ⊓ Cen (b₁ * b₂) :=
        Subgroup.mem_inf.2 ⟨hxT, S36_mem_cen_of h.eq.symm⟩
      rw [hCT.1] at hxc
      exact Subgroup.mem_sup_left (hzT1 hxc)
  have fd : Commute x (b₁ * b₂ ^ 2) → x ∈ (Op 2 (Cen t) ⊓ Cen b₁) ⊔ (Op 2 (Cen t) ⊓ Cen b₂) :=
    fun h => by
      have hxc : x ∈ Op 2 (Cen t) ⊓ Cen (b₁ * b₂ ^ 2) :=
        Subgroup.mem_inf.2 ⟨hxT, S36_mem_cen_of h.eq.symm⟩
      rw [hCT.2] at hxc
      exact Subgroup.mem_sup_left (hzT1 hxc)
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hcom ha
  have hxc : Commute x (b₁ ^ i * b₂ ^ j) := (S36_comm_of_cen hxa).symm
  rw [← zpow_mod3 p1 n1 i, ← zpow_mod3 p2 n2 j] at hxc hne
  have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;> rw [hi, hj] at hxc hne
  · simp at hne
  · exact fb2 (S36_comm_of_pow (k := 1) p2 n2 (Or.inl (by norm_num)) (by simp) hxc)
  · exact fb2 (S36_comm_of_pow (k := 2) p2 n2 (Or.inr (by norm_num)) (by simp) hxc)
  · exact fb1 (S36_comm_of_pow (k := 1) p1 n1 (Or.inl (by norm_num)) (by simp) hxc)
  · exact fc (S36_comm_of_pow (k := 1) hc3 hcne (Or.inl (by norm_num)) (by simp) hxc)
  · exact fd (S36_comm_of_pow (k := 1) hd3 hdne (Or.inl (by norm_num))
      (by simp) hxc)
  · exact fb1 (S36_comm_of_pow (k := 2) p1 n1 (Or.inr (by norm_num)) (by simp) hxc)
  · have h4 : (b₂ ^ 2) ^ (2 : ℤ) = b₂ := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← pow_mul,
        show (2 : ℕ) * 2 = 3 + 1 from rfl, pow_succ b₂ 3, p2, one_mul]
    have ha21 : b₁ ^ (2 : ℤ) * b₂ ^ (1 : ℤ) = (b₁ * b₂ ^ 2) ^ (2 : ℤ) := by
      rw [hdcom.mul_zpow 2, h4, zpow_one]
    exact fd (S36_comm_of_pow (k := 2) hd3 hdne (Or.inr (by norm_num)) ha21 hxc)
  · exact fc (S36_comm_of_pow (k := 2) hc3 hcne (Or.inr (by norm_num))
      (hcom.mul_zpow 2).symm hxc)

theorem F6_product {b t b₁ b₂ : G} {L B : Subgroup G} (d : F6Data b L B b₁ b₂ t)
    (h31 : FF84_3_1) (h33 : FF84_3_3) :
    (Op 2 (Cen t) : Set G) = setMul (Op 2 (Cen t) ⊓ Cen b₁) (Op 2 (Cen t) ⊓ Cen b₂) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1L : b₁ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₁).2
  have hb2L : b₂ ∈ L := (Subgroup.mem_inf.1 d.sec.hb₂).2
  have htc' : ∀ x ∈ L, t * x = x * t := fun x hx =>
    (Subgroup.mem_centralizer_iff.1 d.htL x hx).symm
  have htCen : t ∈ Cen t := S36_mem_cen_of rfl
  have hzT : Subgroup.zpowers t ≤ Op 2 (Cen t) :=
    S36_zpowers_op2 d.ht htCen (fun g hg => (S36_comm_of_cen hg).symm)
  have hzT1 : Subgroup.zpowers t ≤ Op 2 (Cen t) ⊓ Cen b₁ :=
    le_inf hzT (Subgroup.zpowers_le.2 (S36_mem_cen_of (htc' b₁ hb1L).symm))
  have hT1 : ∀ k ∈ Op 2 (Cen t), ∀ h ∈ Op 2 (Cen t) ⊓ Cen b₁,
      k * h * k⁻¹ ∈ Op 2 (Cen t) ⊓ Cen b₁ := by
    intro k hk h hh
    have hz := (F6_H d h31 h33).1 k hk h (Subgroup.mem_inf.1 hh).1
    have e : k * h * k⁻¹ = (k * h * k⁻¹ * h⁻¹) * h := by group
    rw [e]
    exact mul_mem (hzT1 hz) hh
  have hT2N : ∀ k ∈ Op 2 (Cen t) ⊓ Cen b₂, k ∈ Nor (Op 2 (Cen t) ⊓ Cen b₁) := by
    intro k hk
    have hkT : k ∈ Op 2 (Cen t) := (Subgroup.mem_inf.1 hk).1
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact fun hn => hT1 k hkT n hn
    · intro hn
      have h := hT1 k⁻¹ (Subgroup.inv_mem _ hkT) _ hn
      have e : k⁻¹ * (k * n * k⁻¹) * k⁻¹⁻¹ = n := by group
      rwa [e] at h
  have hT2le : Op 2 (Cen t) ⊓ Cen b₂ ≤ Nor (Op 2 (Cen t) ⊓ Cen b₁) := fun k hk => hT2N k hk
  have hA : (Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ : Subgroup G) ≤ Nor (Op 2 (Cen t)) := by
    have hb1Ct : b₁ ∈ Cen t := S36_mem_cen_of (htc' b₁ hb1L)
    have hb2Ct : b₂ ∈ Cen t := S36_mem_cen_of (htc' b₂ hb2L)
    exact sup_le (Subgroup.zpowers_le.2 (S36_nor_op2 hb1Ct))
      (Subgroup.zpowers_le.2 (S36_nor_op2 hb2Ct))
  have hcard : 3 ^ 2 ≤ Nat.card (Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ : Subgroup G) := by
    have := nine_le_card_sup d.sec
    norm_num
    exact this
  haveI := elemAb_sup d.sec
  have hgen :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.le_iSup_centralizer_of_coprime
      (p := 3) (A := Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂) (U := Op 2 (Cen t)) hcard
      (S36_not_three_dvd (S36_op2_isPGroup _)) hA
  have hsub : Op 2 (Cen t) ≤ (Op 2 (Cen t) ⊓ Cen b₁) ⊔ (Op 2 (Cen t) ⊓ Cen b₂) := by
    refine hgen.trans ?_
    exact iSup₂_le (fun a ha => iSup_le (fun hne => S36_piece d h31 h33 ha hne))
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : x ∈ ((Op 2 (Cen t) ⊓ Cen b₂ ⊔ Op 2 (Cen t) ⊓ Cen b₁ : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hsub hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hT2le] at hx'
    obtain ⟨k, hk, h, hh, rfl⟩ := Set.mem_mul.1 hx'
    have hkT : k ∈ Op 2 (Cen t) := (Subgroup.mem_inf.1 hk).1
    exact ⟨k * h * k⁻¹, hT1 k hkT h hh, k, hk, by group⟩
  · rintro x ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (Subgroup.mem_inf.1 hh).1 (Subgroup.mem_inf.1 hk).1

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
