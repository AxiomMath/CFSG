module

public import CFSG.RankThree.GF2n.Tim77.Sec414a
public import CFSG.RankThree.GF2n.Tim77.Sec414Basic
public import CFSG.RankThree.GF2n.Tim77.Sec414Red

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Sec414Sys

variable {A A0 : Subgroup G} (S : Sec414Sys A A0)
include S

theorem not_four_dvd {x y : G} (hx : x ∈ Sec414D A A0) (hy : y ∈ Sec414D A A0) :
    ¬ 4 ∣ orderOf (x * y) := by
  intro h4
  obtain ⟨c, -, w, hw, h⟩ := sec414_exists_conj_order_four (S.D_sq hx) (S.D_sq hy) h4
  have hw' : w ∈ Sec414D A A0 := by
    rcases hw with rfl | rfl
    · exact hx
    · exact hy
  have hcw : c * w * c⁻¹ ∈ Sec414D A A0 := S.mem_D_conj c hw'
  obtain ⟨g₁, a, ha, ha0, rfl⟩ := hx
  obtain ⟨g₂, b, hb, hb0, hb'⟩ := hcw
  apply S.four a ha ha0 (g₁⁻¹ * g₂) b hb hb0
  rw [← h, hb']
  have e : g₁ * a * g₁⁻¹ * (g₂ * b * g₂⁻¹) =
      g₁ * (a * ((g₁⁻¹ * g₂) * b * (g₁⁻¹ * g₂)⁻¹)) * g₁⁻¹ := by group
  rw [e, orderOf_conjugate_t77]

theorem comm_of_isPGroup {x y : G} (hx : x ∈ Sec414D A A0) (hy : y ∈ Sec414D A A0)
    (hP : IsPGroup 2 ↥(Subgroup.closure ({x, y} : Set G))) : x * y = y * x := by
  have hxy : x * y ∈ Subgroup.closure ({x, y} : Set G) :=
    mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x * y, hxy⟩
  rw [Subgroup.orderOf_mk] at hi
  have hi' : i ≤ 1 := by
    by_contra hlt
    push Not at hlt
    apply S.not_four_dvd hx hy
    rw [hi]
    exact (pow_dvd_pow 2 hlt : 2 ^ 2 ∣ 2 ^ i)
  have hsq : (x * y) ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hi]
    simpa using (pow_dvd_pow 2 hi' : 2 ^ i ∣ 2 ^ 1)
  exact sec48_comm_of_sq (S.D_sq hx) (S.D_sq hy) (by rw [← pow_two]; exact hsq)

theorem comm_of_isPGroup_conj (g h : G)
    (hP : IsPGroup 2 ↥(conjSubgroup g A ⊔ conjSubgroup h A)) :
    Sec414Comm (conjSubgroup g A) (conjSubgroup h A) := by
  have hgen : ∀ k : G, Subgroup.closure {x | x ∈ conjSubgroup k A ∧ x ∉ conjSubgroup k A0} =
      conjSubgroup k A := fun k => (S.conj k).closure_diff
  have hD : ∀ k : G, ∀ x, x ∈ conjSubgroup k A → x ∉ conjSubgroup k A0 → x ∈ Sec414D A A0 := by
    intro k x hx hx0
    obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 k A x).1 hx
    exact ⟨k, a, ha, fun h0 => hx0 ((mem_conjSubgroup_conj_t77 k a A0).2 h0), rfl⟩
  have hgg : ∀ a, a ∈ conjSubgroup g A → a ∉ conjSubgroup g A0 → ∀ b, b ∈ conjSubgroup h A →
      b ∉ conjSubgroup h A0 → a * b = b * a := by
    intro a ha ha0 b hb hb0
    apply S.comm_of_isPGroup (hD g a ha ha0) (hD h b hb hb0)
    refine hP.to_le ?_
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact Subgroup.mem_sup_left ha
    · exact Subgroup.mem_sup_right hb
  intro a ha b hb
  rw [← hgen g] at ha
  rw [← hgen h] at hb
  induction ha using Subgroup.closure_induction with
  | mem a' ha' =>
    induction hb using Subgroup.closure_induction with
    | mem b' hb' => exact hgg a' ha'.1 ha'.2 b' hb'.1 hb'.2
    | one => simp
    | mul b₁ b₂ _ _ ih₁ ih₂ =>
      calc a' * (b₁ * b₂) = (a' * b₁) * b₂ := by group
        _ = (b₁ * a') * b₂ := by rw [ih₁]
        _ = b₁ * (a' * b₂) := by group
        _ = b₁ * (b₂ * a') := by rw [ih₂]
        _ = b₁ * b₂ * a' := by group
    | inv b₁ _ ih =>
      calc a' * b₁⁻¹ = b₁⁻¹ * (b₁ * a') * b₁⁻¹ := by group
        _ = b₁⁻¹ * (a' * b₁) * b₁⁻¹ := by rw [ih]
        _ = b₁⁻¹ * a' := by group
  | one => simp
  | mul a₁ a₂ _ _ ih₁ ih₂ =>
    calc a₁ * a₂ * b = a₁ * (a₂ * b) := by group
      _ = a₁ * (b * a₂) := by rw [ih₂]
      _ = (a₁ * b) * a₂ := by group
      _ = (b * a₁) * a₂ := by rw [ih₁]
      _ = b * (a₁ * a₂) := by group
  | inv a₁ _ ih =>
    calc a₁⁻¹ * b = a₁⁻¹ * (b * a₁) * a₁⁻¹ := by group
      _ = a₁⁻¹ * (a₁ * b) * a₁⁻¹ := by rw [ih]
      _ = b * a₁⁻¹ := by group

theorem mem_D_of_conj {k x : G} (hx : x ∈ conjSubgroup k A) (hx0 : x ∉ conjSubgroup k A0) :
    x ∈ Sec414D A A0 := by
  obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 k A x).1 hx
  exact ⟨k, a, ha, fun h0 => hx0 ((mem_conjSubgroup_conj_t77 k a A0).2 h0), rfl⟩

theorem mem_normalizer_of_inO2 (g h : G) {t : G} (htC : t ∈ conjSubgroup g A) (ht1 : t ≠ 1)
    (hO : Sec414InO2 (conjSubgroup g A ⊔ conjSubgroup h A) t) :
    t ∈ normalizer (conjSubgroup h A : Set G) := by
  have hCel := isElemAbelian_conj S.elem g
  have hC'el := isElemAbelian_conj S.elem h
  have ht2 : t * t = 1 := by rw [← sq]; exact hCel.2 t htC
  obtain ⟨c, hcC', hcC'0⟩ := (S.conj h).exists_not_mem
  have hc2 : c * c = 1 := by rw [← sq]; exact hC'el.2 c hcC'
  have hc1 : c ≠ 1 := (S.conj h).ne_one_of_not_mem hcC'0
  have hcD : c ∈ Sec414D A A0 := S.mem_D_of_conj hcC' hcC'0
  obtain ⟨P, hPV, hP2, hPn, htP⟩ := hO
  have hcV : c ∈ conjSubgroup g A ⊔ conjSubgroup h A := Subgroup.mem_sup_right hcC'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (Subgroup.zpowers c) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1⟩
  have hPQ : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers c) :=
    sec414_isPGroup_sup hP2 hQ (fun q hq p hp =>
      hPn q ((Subgroup.zpowers_le.mpr hcV) hq) p hp)
  have hrmem : t * c ∈ P ⊔ Subgroup.zpowers c :=
    mul_mem (Subgroup.mem_sup_left htP) (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.mp hPQ) ⟨t * c, hrmem⟩
  rw [Subgroup.orderOf_mk] at hi
  have hcom : ∀ (hr : (t * c) * (t * c) = 1), t ∈ normalizer (conjSubgroup h A : Set G) := by
    intro hr
    have hcomm : t * c = c * t := sec48_comm_of_sq ht2 hc2 hr
    exact mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup S.ti h) hcC' hc1 hcomm
  have hi2 : i ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have hc'D : (t * c)⁻¹ * c * (t * c) ∈ Sec414D A A0 := by
      have := S.mem_D_conj (t * c)⁻¹ hcD
      simpa [mul_assoc] using this
    apply S.not_four_dvd hcD hc'D
    rw [sec414_orderOf_mul_conj hc2 ht2]
    have h1 : orderOf (t * c) ∣ 2 * orderOf ((t * c) ^ 2) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, pow_orderOf_eq_one]
    rw [hi] at h1
    have h2 : 2 ^ (i - 1) ∣ orderOf ((t * c) ^ 2) := by
      have : 2 ^ i = 2 * 2 ^ (i - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this] at h1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    exact (pow_dvd_pow 2 (by omega : 2 ≤ i - 1)).trans h2
  by_cases hr2 : (t * c) ^ 2 = 1
  · exact hcom (by rw [← pow_two]; exact hr2)
  · have hord : orderOf (t * c) = 4 := by
      interval_cases i
      · exfalso
        have h1 : t * c = 1 := orderOf_eq_one_iff.mp (by simpa using hi)
        apply hr2
        rw [h1]; simp
      · exfalso
        have h1 : orderOf (t * c) = 2 := by simpa using hi
        have h3 := pow_orderOf_eq_one (t * c)
        rw [h1] at h3
        exact hr2 h3
      · simpa using hi
    have hct : orderOf (c * t) = 4 := by
      have : c * t = (t * c)⁻¹ := by rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hc2,
        inv_eq_of_mul_eq_one_right ht2]
      rw [this, orderOf_inv]; exact hord
    have hg' : t ∈ conjSubgroup (g * h⁻¹) (conjSubgroup h A) := by
      rw [← conjSubgroup_mul, inv_mul_cancel_right]; exact htC
    exact (S.conj h).four12 c hcC' hcC'0 (g * h⁻¹) t hg' hct

theorem centralizes_of_mul_mem_D {g a x z : G} (hxa : x = g * a * g⁻¹) (ha : a ∈ A)
    (ha0 : a ∉ A0) (hxz : x * z = z * x) (hD : x * z ∈ Sec414D A A0) :
    ∀ c ∈ conjSubgroup g A, c * z = z * c := by
  intro c hc
  obtain ⟨g₃, b, hb, hb0, he⟩ := hD
  have hx : x ∈ conjSubgroup g A := by
    rw [hxa]; exact (mem_conjSubgroup_conj_t77 g a A).2 ha
  have hx0 : x ∉ conjSubgroup g A0 := by
    rw [hxa]; exact fun h0 => ha0 ((mem_conjSubgroup_conj_t77 g a A0).1 h0)
  have hCg : conjSubgroup (g₃ * g⁻¹) (conjSubgroup g A) = conjSubgroup g₃ A := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hCg0 : conjSubgroup (g₃ * g⁻¹) (conjSubgroup g A0) = conjSubgroup g₃ A0 := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hmem : x * z ∈ conjSubgroup (g₃ * g⁻¹) (conjSubgroup g A) := by
    rw [hCg, he]; exact (mem_conjSubgroup_conj_t77 g₃ b A).2 hb
  have hmem0 : x * z ∉ conjSubgroup (g₃ * g⁻¹) (conjSubgroup g A0) := by
    rw [hCg0, he]; exact fun h0 => hb0 ((mem_conjSubgroup_conj_t77 g₃ b A0).1 h0)
  have hcx : x * (x * z) = (x * z) * x := by
    calc x * (x * z) = x * (z * x) := by rw [hxz]
      _ = (x * z) * x := by group
  have hcomm := (S.conj g).comm_of_commute hx hx0 (g₃ * g⁻¹) hmem hmem0 hcx
  rw [hCg] at hcomm
  have hmem' : x * z ∈ conjSubgroup g₃ A := by
    rw [he]; exact (mem_conjSubgroup_conj_t77 g₃ b A).2 hb
  have hce : c * (x * z) = (x * z) * c := hcomm c hc _ hmem'
  have hxx : x * x = 1 := by
    rw [← sq]; exact (isElemAbelian_conj S.elem g).2 x hx
  have hcxc : c * x = x * c :=
    congrArg Subtype.val ((isElemAbelian_conj S.elem g).1.is_comm.comm ⟨c, hc⟩ ⟨x, hx⟩)
  have hzz : x * (x * z) = z := by rw [← mul_assoc, hxx, one_mul]
  calc c * z = c * (x * (x * z)) := by rw [hzz]
    _ = (c * x) * (x * z) := by group
    _ = (x * c) * (x * z) := by rw [hcxc]
    _ = x * (c * (x * z)) := by group
    _ = x * ((x * z) * c) := by rw [hce]
    _ = (x * (x * z)) * c := by group
    _ = z * c := by rw [hzz]

theorem pow_centralizes {g₁ g₂ a b : G} (ha : a ∈ A) (ha0 : a ∉ A0) (hb : b ∈ A) (hb0 : b ∉ A0)
    {n : ℕ} (hn : Odd n)
    (hord : orderOf (g₁ * a * g₁⁻¹ * (g₂ * b * g₂⁻¹)) = 2 * n) :
    (∀ c ∈ conjSubgroup g₁ A,
      c * (g₁ * a * g₁⁻¹ * (g₂ * b * g₂⁻¹)) ^ n = (g₁ * a * g₁⁻¹ * (g₂ * b * g₂⁻¹)) ^ n * c) ∧
    (∀ c ∈ conjSubgroup g₂ A,
      c * (g₁ * a * g₁⁻¹ * (g₂ * b * g₂⁻¹)) ^ n = (g₁ * a * g₁⁻¹ * (g₂ * b * g₂⁻¹)) ^ n * c) := by
  set x := g₁ * a * g₁⁻¹ with hx
  set y := g₂ * b * g₂⁻¹ with hy
  have hxD : x ∈ Sec414D A A0 := ⟨g₁, a, ha, ha0, rfl⟩
  have hyD : y ∈ Sec414D A A0 := ⟨g₂, b, hb, hb0, rfl⟩
  have hx2 := S.D_sq hxD
  have hy2 := S.D_sq hyD
  have hz2 : (x * y) ^ n * (x * y) ^ n = 1 := by
    rw [← pow_add, ← two_mul]; exact hord ▸ pow_orderOf_eq_one _
  have hzx : x * (x * y) ^ n = (x * y) ^ n * x := by
    have h1 := sec414_dihedral_mul_pow (s := x) (r := x * y) hx2
      (sec414_dihedral_left_inv hx2 hy2) n
    rw [h1, inv_eq_of_mul_eq_one_right hz2]
  have hzy : y * (x * y) ^ n = (x * y) ^ n * y := by
    have h1 := sec414_dihedral_mul_pow (s := y) (r := x * y) hy2
      (sec414_dihedral_right_inv hx2 hy2) n
    rw [h1, inv_eq_of_mul_eq_one_right hz2]
  obtain ⟨k, rfl⟩ := hn
  constructor
  · refine S.centralizes_of_mul_mem_D (g := g₁) (a := a) rfl ha ha0 hzx ?_
    rw [sec414_dihedral_pow_odd hx2 hy2 k]
    have := S.mem_D_conj ((x * y) ^ k)⁻¹ hyD
    simpa using this
  · have hyz : y * (x * y) ^ (2 * k + 1) = ((x * y) ^ (k + 1))⁻¹ * x * (x * y) ^ (k + 1) := by
      have hxr : x * (x * y) = y := by rw [← mul_assoc, hx2, one_mul]
      calc y * (x * y) ^ (2 * k + 1) = (x * (x * y)) * (x * y) ^ (2 * k + 1) := by rw [hxr]
        _ = x * (x * y) ^ (2 * k + 1 + 1) := by rw [mul_assoc, ← pow_succ']
        _ = x * (x * y) ^ (2 * (k + 1)) := by rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
        _ = _ := sec414_dihedral_pow_even hx2 hy2 (k + 1)
    refine S.centralizes_of_mul_mem_D (g := g₂) (a := b) rfl hb hb0 hzy ?_
    rw [hyz]
    have := S.mem_D_conj ((x * y) ^ (k + 1))⁻¹ hxD
    simpa using this

end Sec414Sys

end CFSG.RankThree.GF2n.Tim77
