module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre42b
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreD0


public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.LocalRank (thetaT)
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}
variable {θ : ↥(Nor L) →* Perm (Fin 8)}

theorem E_coord (h : FF84Sec4 b L B K b₁ b₂) {x : G}
    (hx : x ∈ Subgroup.closure ({b, b₁} : Set G)) : ∃ i j : ℤ, x = b ^ i * b₁ ^ j := by
  let S : Subgroup G :=
    { carrier := {x | ∃ i j : ℤ, x = b ^ i * b₁ ^ j}
      mul_mem' := by
        rintro x y ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
        refine ⟨i + i', j + j', ?_⟩
        have := mul_coord h i j 0 i' j' 0
        simpa using this
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro x ⟨i, j, rfl⟩
        refine ⟨-i, -j, ?_⟩
        apply inv_eq_of_mul_eq_one_right
        have := mul_coord h i j 0 (-i) (-j) 0
        simpa using this }
  have : Subgroup.closure ({b, b₁} : Set G) ≤ S := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | hz
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff.1 hz]; exact ⟨0, 1, by simp⟩
  exact this hx

theorem E_le_B (h : FF84Sec4 b L B K b₁ b₂) : Subgroup.closure ({b, b₁} : Set G) ≤ B :=
  (Subgroup.closure_le _).2 (by
    intro z hz
    rcases hz with rfl | hz
    · exact mem_b h
    · rw [Set.mem_singleton_iff.1 hz]; exact mem_b₁ h)

theorem relIndex_E (h : FF84Sec4 b L B K b₁ b₂) :
    (Subgroup.closure ({b, b₁} : Set G)).relIndex B = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U := Subgroup.closure ({b, b₁} : Set G) with hU
  have hUB : U ≤ B := E_le_B h
  have hxU : b ∈ U := Subgroup.subset_closure (by simp)
  have hyU : b₁ ∈ U := Subgroup.subset_closure (by simp)
  have hc27 : Nat.card B = 3 ^ 3 := card_B h
  have hd : Nat.card U ∣ 3 ^ 3 := hc27 ▸ Subgroup.card_dvd_of_le hUB
  obtain ⟨k, hk, hkU⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  have hk2 : k = 2 := by
    interval_cases k
    · exfalso
      have : U = ⊥ := Subgroup.card_eq_one.1 (by simpa using hkU)
      rw [this, Subgroup.mem_bot] at hxU
      exact b_ne_one h hxU
    · exfalso
      have hle : Subgroup.zpowers b ≤ U := Subgroup.zpowers_le.2 hxU
      have hcz : Nat.card (Subgroup.zpowers b) = 3 := by
        rw [Nat.card_zpowers, h.hyp.ord]
      have heq : Subgroup.zpowers b = U :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hkU]; norm_num)
      rw [← heq] at hyU
      exact b₁_notin_zpowers_b h hyU
    · rfl
    · exfalso
      have heq : U = B := Subgroup.eq_of_le_of_card_ge hUB (by rw [hkU, hc27])
      have : b₂ ∈ U := by rw [heq]; exact mem_b₂ h
      exact b₂_notin_E h this
  have h1 := Subgroup.card_mul_index (U.subgroupOf B)
  have h2 : Nat.card (U.subgroupOf B) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv
  rw [h2, hkU, hk2, hc27] at h1
  show (U.subgroupOf B).index = 3
  omega

theorem cen_sq {a : G} (ha : a ^ 3 = 1) : Cen (a ^ 2) = Cen a := by
  have ha' : a = (a ^ 2) ^ 2 := by
    calc a = a ^ 4 * (a ^ 3)⁻¹ := by group
      _ = (a ^ 2) ^ 2 := by rw [ha]; group
  ext y
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    have hc : Commute y (a ^ 2) := hy
    have := hc.pow_right 2
    rw [← ha'] at this
    exact this
  · intro hy
    have hc : Commute y a := hy
    exact hc.pow_right 2

theorem cen_conj_iff {a a' g : G} (hg : g * a * g⁻¹ = a') (y : G) :
    y ∈ Cen a ↔ g * y * g⁻¹ ∈ Cen a' := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  subst hg
  constructor
  · intro hy
    calc g * y * g⁻¹ * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [hy]
      _ = g * a * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hy
    have : g * (y * a) * g⁻¹ = g * (a * y) * g⁻¹ := by
      calc g * (y * a) * g⁻¹ = g * y * g⁻¹ * (g * a * g⁻¹) := by group
        _ = g * a * g⁻¹ * (g * y * g⁻¹) := hy
        _ = g * (a * y) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)

set_option maxRecDepth 200000 in
theorem inv_conj_facts : (swap (1 : Fin 8) 2 * swap 6 7) * a8c * (swap 1 2 * swap 6 7)⁻¹ = a8c⁻¹ := by
  unfold a8c
  decide +kernel

theorem exists_inv_b₁ (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂) (hθ : ThM L b₁ b₂ θ) :
    ∃ x ∈ L, x * b₁ * x⁻¹ = b₁⁻¹ := by
  obtain ⟨x, hxL, hx⟩ := hθ.surj (swap (1 : Fin 8) 2 * swap 6 7)
    (mem_alternatingGroup.2 sign_p12_67)
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hxN : x ∈ Nor L := Subgroup.le_normalizer hxL
  have hb₁N : b₁ ∈ Nor L := Subgroup.le_normalizer hb₁L
  set z : G := x * b₁ * x⁻¹ * b₁ with hz
  have hzL : z ∈ L := by
    have h1 : x * b₁ * x⁻¹ ∈ L := mul_mem (mul_mem hxL hb₁L) (inv_mem hxL)
    exact mul_mem h1 hb₁L
  have hzN : z ∈ Nor L := Subgroup.le_normalizer hzL
  have hth : thG L θ z = 1 := by
    rw [hz, thG_mul (mul_mem (mul_mem hxN hb₁N) (inv_mem hxN)) hb₁N,
      thG_conj hxN hb₁N, hθ.c, hx, inv_conj_facts]
    group
  have hzc : z ∈ CenS L := (hθ.ker z hzN).1 hth
  have hz2 := Z_sq hA z hzL hzc
  have hzb : z * b₁ = b₁ * z := (Subgroup.mem_centralizer_iff.1 hzc b₁ hb₁L).symm
  have hb3 : b₁ ^ 3 = 1 := pow3_of_mem h (mem_b₁ h)
  have hz3 : z ^ 3 = 1 := by
    have hconj : (x * b₁ * x⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hb3]; group
    have e : x * b₁ * x⁻¹ = z * b₁⁻¹ := by rw [hz]; group
    have hc : Commute z b₁⁻¹ := (show Commute z b₁ from hzb).inv_right
    have hb3' : (b₁⁻¹) ^ 3 = 1 := by rw [inv_pow, hb3]; simp
    rw [e, hc.mul_pow, hb3', mul_one] at hconj
    exact hconj
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2]; group
  refine ⟨x, hxL, ?_⟩
  calc x * b₁ * x⁻¹ = z * b₁⁻¹ := by rw [hz]; group
    _ = b₁⁻¹ := by rw [hz1, one_mul]

theorem eq_one_of_two_group_odd {S H : Subgroup G} (hS : IsPGroup 2 S) (hH : Odd (Nat.card H))
    {c : G} (hcS : c ∈ S) (hcH : c ∈ H) : c = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨c, hcS⟩
  have h1 : orderOf c ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    exact congrArg Subtype.val hk
  have h2 : orderOf c ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨c, hcH⟩ : ↥H)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf c ∣ 2 ^ k := h1
  have hodd : ¬ 2 ∣ orderOf c := by
    intro hd
    have := hd.trans h2
    exact (Nat.not_even_iff_odd.2 hH) (even_iff_two_dvd.2 this)
  have h4 : Nat.Coprime (orderOf c) (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h4 h3)

theorem M_le_theta_cen_b (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) {m : G} (hm : m ∈ Theta (Cen (b * b₁))) (hmB : m ∈ CenS B) :
    m ∈ Theta (Cen b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmX := theta_cenB_le_X hA h hm hmB
  have hXD : Opp 3 (Cen b) ≤ Cen (b * b₁) := by
    intro x hx
    have h1 : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 (FF79.L14.Opp_le 3 _ hx)
    have h2 : x * b₁ = b₁ * x := Subgroup.mem_centralizer_singleton_iff.1 (S41_cen_X hA h hx)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc x * (b * b₁) = (x * b) * b₁ := by group
      _ = (b * x) * b₁ := by rw [h1]
      _ = b * (x * b₁) := by group
      _ = b * (b₁ * x) := by rw [h2]
      _ = b * b₁ * x := by group
  set N0 : Subgroup G := Opp 3 (Cen b) ⊓ Theta (Cen (b * b₁)) with hN0
  have hsolv : Group.IsSolvable ↥N0 := by
    haveI := theta_solv (Cen (b * b₁))
    exact solvable_of_solvable_injective (f := Subgroup.inclusion (inf_le_right : N0 ≤ _))
      (Subgroup.inclusion_injective _)
  have h3 : ¬ 3 ∣ Nat.card ↥N0 := fun hd =>
    theta_three (Cen (b * b₁)) (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hX : N0 ≤ Theta (Opp 3 (Cen b)) := by
    refine le_theta_of_normal inf_le_left ?_ hsolv h3
    intro x hx n hn
    exact Subgroup.mem_inf.2 ⟨FF79.L14.Opp_conj_mem (FF79.L14.Opp_le 3 _ hx) (Subgroup.mem_inf.1 hn).1,
      theta_norm _ (hXD hx) (Subgroup.mem_inf.1 hn).2⟩
  have hXC : Theta (Opp 3 (Cen b)) ≤ Theta (Cen b) :=
    theta_mono_normal (FF79.L14.Opp_le 3 _) (fun c hc x hx => FF79.L14.Opp_conj_mem hc hx)
  exact hXC (hX (Subgroup.mem_inf.2 ⟨hmX, hm⟩))

theorem M_le_theta_cen_b₁ (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) {m : G} (hm : m ∈ Theta (Cen (b * b₁))) (hmB : m ∈ CenS B) :
    m ∈ Theta (Cen b₁) := by
  obtain ⟨n, hnN, hnb, hnb₁, -⟩ := h.mono.2.2.2.2.1
  have hbb₁ : b * b₁ = b₁ * b := (comm_of_mem h (mem_b h) (mem_b₁ h)).eq
  have hnD : n ∈ Cen (b * b₁) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have : n * (b * b₁) * n⁻¹ = b * b₁ := by
      calc n * (b * b₁) * n⁻¹ = (n * b * n⁻¹) * (n * b₁ * n⁻¹) := by group
        _ = b₁ * b := by rw [hnb, hnb₁]
        _ = b * b₁ := hbb₁.symm
    calc n * (b * b₁) = (n * (b * b₁) * n⁻¹) * n := by group
      _ = (b * b₁) * n := by rw [this]
  have hm' : n * m * n⁻¹ ∈ Theta (Cen (b * b₁)) := theta_norm _ hnD hm
  have hm'B : n * m * n⁻¹ ∈ CenS B := by
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    have hβ' : n⁻¹ * β * n ∈ B := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) β).1 hβ
      simpa using this
    have e := Subgroup.mem_centralizer_iff.1 hmB _ hβ'
    calc β * (n * m * n⁻¹) = n * ((n⁻¹ * β * n) * m) * n⁻¹ := by group
      _ = n * (m * (n⁻¹ * β * n)) * n⁻¹ := by rw [e]
      _ = n * m * n⁻¹ * β := by group
  have hb := M_le_theta_cen_b hA h hm' hm'B
  have := theta_conj_mem (H := Cen b) (H' := Cen b₁) (g := n⁻¹) (fun y => by
    rw [inv_inv]
    exact cen_conj_iff hnb₁ y) hb
  simpa [mul_assoc] using this

theorem M_le_theta_cen_bb₁sq (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) {m : G} (hm : m ∈ Theta (Cen (b * b₁))) (hmB : m ∈ CenS B) :
    m ∈ Theta (Cen (b * b₁ ^ 2)) := by
  obtain ⟨θ, hθ⟩ := exists_thM hA h
  obtain ⟨x, hxL, hx⟩ := exists_inv_b₁ hA h hθ
  have hmX := theta_cenB_le_X hA h hm hmB
  have hmL : m ∈ CenS L := X_le_cenS_L h.hyp hA hmX
  have hxm : x * m * x⁻¹ = m := by
    have := Subgroup.mem_centralizer_iff.1 hmL x hxL
    calc x * m * x⁻¹ = (x * m) * x⁻¹ := rfl
      _ = (m * x) * x⁻¹ := by rw [this]
      _ = m := by group
  have hxb : x * b = b * x := (Subgroup.mem_centralizer_singleton_iff.1 (h.hyp.hLC hxL)).symm.symm
  have hb3 : b₁ ^ 3 = 1 := pow3_of_mem h (mem_b₁ h)
  have e1 : x⁻¹ * b₁ * x = b₁⁻¹ := by
    have : x⁻¹ * (x * b₁ * x⁻¹) * x = x⁻¹ * b₁⁻¹ * x := by rw [hx]
    have h2 : b₁ = x⁻¹ * b₁⁻¹ * x := by rw [← this]; group
    calc x⁻¹ * b₁ * x = (x⁻¹ * b₁⁻¹ * x)⁻¹ := by group
      _ = b₁⁻¹ := by rw [← h2]
  have hconj : x⁻¹ * (b * b₁ ^ 2) * x⁻¹⁻¹ = b * b₁ := by
    have hbx : x⁻¹ * b * x = b := by
      calc x⁻¹ * b * x = x⁻¹ * (b * x) := by group
        _ = x⁻¹ * (x * b) := by rw [hxb]
        _ = b := by group
    calc x⁻¹ * (b * b₁ ^ 2) * x⁻¹⁻¹ = (x⁻¹ * b * x) * (x⁻¹ * b₁ * x) ^ 2 := by
          simp only [pow_two]; group
      _ = b * (b₁⁻¹) ^ 2 := by rw [hbx, e1]
      _ = b * b₁ := by
        have : (b₁⁻¹) ^ 2 = b₁ := by
          calc (b₁⁻¹) ^ 2 = b₁ ^ 3 * (b₁⁻¹) ^ 2 := by rw [hb3, one_mul]
            _ = b₁ := by simp only [pow_succ, pow_zero]; group
        rw [this]
  have := theta_conj_mem (H := Cen (b * b₁)) (H' := Cen (b * b₁ ^ 2)) (g := x) (fun y => by
    have := cen_conj_iff hconj y
    rwa [inv_inv] at this) hm
  rwa [hxm] at this

theorem comm_b_b₁ (h : FF84Sec4 b L B K b₁ b₂) : Commute b b₁ := comm_of_mem h (mem_b h) (mem_b₁ h)

theorem M_le_thetaT (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) {m : G} (hm : m ∈ Theta (Cen (b * b₁))) (hmB : m ∈ CenS B) :
    m ∈ thetaT 3 (Subgroup.closure ({b, b₁} : Set G)) := by
  have hb3 : b ^ 3 = 1 := pow3_of_mem h (mem_b h)
  have hb₁3 : b₁ ^ 3 = 1 := pow3_of_mem h (mem_b₁ h)
  have hcm := comm_b_b₁ h
  have hbb₁3 : (b * b₁) ^ 3 = 1 := by
    rw [hcm.mul_pow, hb3, hb₁3, one_mul]
  have hD := hm
  have hb := M_le_theta_cen_b hA h hm hmB
  have hb₁ := M_le_theta_cen_b₁ hA h hm hmB
  have hD' := M_le_theta_cen_bb₁sq hA h hm hmB
  simp only [thetaT, Subgroup.mem_iInf]
  intro x hx hx1
  obtain ⟨i, j, rfl⟩ := E_coord h hx
  rw [zpow_emod_three hb3 i, zpow_emod_three hb₁3 j] at hx1 ⊢
  have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have hj : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  have hcsq : ((b * b₁) ^ 2) = b ^ 2 * b₁ ^ 2 := hcm.mul_pow 2
  have hcsq' : (b * b₁ ^ 2) ^ 2 = b ^ 2 * b₁ := by
    rw [(hcm.pow_right 2).mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hb₁3,
      one_mul, pow_one]
  have hc2 : ∀ {a : G}, a ^ 3 = 1 → m ∈ Theta (Cen a) → m ∈ Theta (Cen (a ^ 2)) := by
    intro a ha hma
    show m ∈ Theta (Cen (a ^ 2))
    rw [cen_sq ha]
    exact hma
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;> rw [hi, hj] at hx1 ⊢
  · exact absurd (by simp) hx1
  · simpa using hb₁
  · have e : b ^ (0 : ℤ) * b₁ ^ (2 : ℤ) = b₁ ^ 2 := by simp
    rw [e]; exact hc2 hb₁3 hb₁
  · simpa using hb
  · simpa using hD
  · simpa using hD'
  · have e : b ^ (2 : ℤ) * b₁ ^ (0 : ℤ) = b ^ 2 := by simp
    rw [e]; exact hc2 hb3 hb
  · have e : b ^ (2 : ℤ) * b₁ ^ (1 : ℤ) = (b * b₁ ^ 2) ^ 2 := by rw [hcsq']; simp
    rw [e]; exact hc2 (bb₁sq_cube h) hD'
  · have e : b ^ (2 : ℤ) * b₁ ^ (2 : ℤ) = (b * b₁) ^ 2 := by rw [hcsq]; simp
    rw [e]; exact hc2 hbb₁3 hD

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
