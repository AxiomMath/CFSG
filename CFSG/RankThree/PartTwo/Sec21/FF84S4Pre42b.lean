module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre46b
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre42a

import CFSG.CharacterTheory.Wreathed.FullDefectCanonicalStructure

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}
variable {θ : ↥(Nor L) →* Perm (Fin 8)}

theorem Z_sq (hA : A8Model L) : ∀ z ∈ L, z ∈ CenS L → z ^ 2 = 1 := by
  intro z hz hzc
  have hzm : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc g g.2)
  have h1 : orderOf (⟨⟨z, hz⟩, hzm⟩ : Subgroup.center ↥L) ∣ 2 :=
    (orderOf_dvd_natCard _).trans hA.2
  have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
  have h3 := congrArg (fun t : ↥(Subgroup.center ↥L) => (((t : ↥L) : G))) (h2 : _ = (1 : ↥(Subgroup.center ↥L)))
  simpa using h3

theorem lift_cen_b₁ (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂) (hθ : ThM L b₁ b₂ θ)
    {g₀ : Perm (Fin 8)} (hg₀ : g₀ ∈ alternatingGroup (Fin 8)) (hc : g₀ * a8c = a8c * g₀) :
    ∃ y ∈ L ⊓ Cen b₁, thG L θ y = g₀ := by
  obtain ⟨x, hxL, hx⟩ := hθ.surj g₀ hg₀
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hxN : x ∈ Nor L := Subgroup.le_normalizer hxL
  have hb₁N : b₁ ∈ Nor L := Subgroup.le_normalizer hb₁L
  set z : G := x * b₁ * x⁻¹ * b₁⁻¹ with hz
  have hzL : z ∈ L := by
    have h1 : x * b₁ * x⁻¹ ∈ L := mul_mem (mul_mem hxL hb₁L) (inv_mem hxL)
    exact mul_mem h1 (inv_mem hb₁L)
  have hzN : z ∈ Nor L := Subgroup.le_normalizer hzL
  have hth : thG L θ z = 1 := by
    rw [hz, thG_mul (mul_mem (mul_mem hxN hb₁N) (inv_mem hxN)) (inv_mem hb₁N),
      thG_conj hxN hb₁N, thG_inv hb₁N, hθ.c, hx, hc]
    group
  have hzc : z ∈ CenS L := (hθ.ker z hzN).1 hth
  have hz2 := Z_sq hA z hzL hzc
  have hzb : z * b₁ = b₁ * z := Subgroup.mem_centralizer_iff.1 hzc b₁ hb₁L |>.symm
  have hb3 : b₁ ^ 3 = 1 := pow3_of_mem h (mem_b₁ h)
  have hz3 : z ^ 3 = 1 := by
    have hconj : (x * b₁ * x⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hb3]; group
    have e : x * b₁ * x⁻¹ = z * b₁ := by rw [hz]; group
    rw [e, (Commute.mul_pow (show Commute z b₁ from hzb) 3), hb3, mul_one] at hconj
    exact hconj
  have hz1 : z = 1 := by
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [hz3, hz2]; group
  refine ⟨x, Subgroup.mem_inf.2 ⟨hxL, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, hx⟩
  have e : b₁ * x = z⁻¹ * (x * b₁) := by rw [hz]; group
  rw [e, hz1]
  group

theorem B_inf_Q' (h : FF84Sec4 b L B K b₁ b₂) (hZ2 : ∀ z ∈ L, z ∈ CenS L → z ^ 2 = 1) :
    B ⊓ (Cen b ⊓ CenS L) = Subgroup.zpowers b := by
  apply le_antisymm
  · rintro x ⟨hxB, -, hxc⟩
    obtain ⟨a, c, d, rfl⟩ := coord_of_mem_B h hxB
    have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
    have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
    have hbz : b ^ a ∈ CenS L := Subgroup.zpow_mem _ (b_mem_cenS h) a
    have hy : b₁ ^ c * b₂ ^ d ∈ CenS L := by
      have := mul_mem (inv_mem hbz) hxc
      rwa [show (b ^ a)⁻¹ * (b ^ a * b₁ ^ c * b₂ ^ d) = b₁ ^ c * b₂ ^ d by group] at this
    have hyL : b₁ ^ c * b₂ ^ d ∈ L :=
      mul_mem (Subgroup.zpow_mem _ hb₁L c) (Subgroup.zpow_mem _ hb₂L d)
    have hyB : b₁ ^ c * b₂ ^ d ∈ B :=
      mul_mem (Subgroup.zpow_mem _ (mem_b₁ h) c) (Subgroup.zpow_mem _ (mem_b₂ h) d)
    set y := b₁ ^ c * b₂ ^ d with hydef
    have h3 : y ^ 3 = 1 := pow3_of_mem h hyB
    have h2 : y ^ 2 = 1 := hZ2 y hyL hy
    have hy1 : y = 1 := by
      calc y = y ^ 3 * (y ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; group
    rw [mul_assoc, ← hydef, hy1, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) a
  · refine Subgroup.zpowers_le.2 ⟨mem_b h, Subgroup.mem_centralizer_singleton_iff.2 rfl,
      b_mem_cenS h⟩

theorem Q_decomp' (h : FF84Sec4 b L B K b₁ b₂) (hZ2 : ∀ z ∈ L, z ∈ CenS L → z ^ 2 = 1) :
    ∀ c ∈ Cen b ⊓ CenS L, ∃ i : ℤ, ∃ x ∈ Opp 3 (Cen b), c = b ^ i * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C₀ := Cen b ⊓ CenS L with hC₀
  have hBsyl : IsSylowOf 3 (B ⊓ C₀) C₀ :=
    FF79.L14.isSylowOf_inf_normal h.sylB inf_le_left (Q_norm h)
  rw [B_inf_Q' h hZ2] at hBsyl
  have hP0p : IsPGroup 3 ((Subgroup.zpowers b).subgroupOf C₀) := hBsyl.2.1.comap_subtype
  have hidx : ¬ 3 ∣ ((Subgroup.zpowers b).subgroupOf C₀).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hBsyl.2.2
  let P : Sylow 3 ↥C₀ := hP0p.toSylow hidx
  have hPc : (P : Subgroup ↥C₀) ≤ Subgroup.center ↥C₀ := by
    intro p hp
    rw [Subgroup.mem_center_iff]
    intro q
    have hp' : (p : G) ∈ Subgroup.zpowers b := Subgroup.mem_subgroupOf.mp hp
    have hbq : (q : G) * b = b * q := Subgroup.mem_centralizer_singleton_iff.1 q.2.1
    have hpq : (q : G) * (p : G) = (p : G) * q := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hp'
      rw [← hi]
      exact ((Commute.zpow_right (show Commute (q : G) b from hbq) i)).eq
    exact Subtype.ext hpq
  have hcomp := CFSG.FullDefectCanonical.pPrimeCore_isComplement_of_central P hPc
  intro c hc
  obtain ⟨⟨⟨m, hm⟩, ⟨p, hp⟩⟩, hx, -⟩ := hcomp.existsUnique (⟨c, hc⟩ : ↥C₀)
  have hmX : (m : G) ∈ Opp 3 (Cen b) :=
    FF79.L14.Opp_le_Opp_of_normalized inf_le_left (Q_norm h)
      (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)
  have hpZ : (p : G) ∈ Subgroup.zpowers b := Subgroup.mem_subgroupOf.mp hp
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hpZ
  refine ⟨i, m, hmX, ?_⟩
  have hc' : c = m * p := (congrArg Subtype.val hx).symm
  rw [hc', ← hi]
  have hmc : (m : G) ∈ Cen b := FF79.L14.Opp_le 3 _ hmX
  have : (m : G) * b = b * m := Subgroup.mem_centralizer_singleton_iff.1 hmc
  exact (((show Commute (m : G) b from this).zpow_right i)).eq

set_option maxRecDepth 200000 in
theorem cd_pow6 : ∀ i ∈ Finset.range 3, ∀ j ∈ Finset.range 3, ∀ e ∈ Finset.range 2,
    (a8c ^ i * a8d ^ j * swap (6 : Fin 8) 7 ^ e) ^ 6 = 1 := by
  unfold a8c a8d
  decide +kernel

set_option maxRecDepth 200000 in
theorem x0_facts : (swap (7 : Fin 8) 3 * swap 3 4) * a8c = a8c * (swap 7 3 * swap 3 4) ∧
    (swap (7 : Fin 8) 3 * swap 3 4) * swap 6 7 * (swap 7 3 * swap 3 4)⁻¹ = swap 6 3 ∧
    (swap (6 : Fin 8) 7 * swap 6 3) ^ 3 = 1 ∧ swap (6 : Fin 8) 7 * swap 6 3 ≠ 1 := by
  unfold a8c
  decide +kernel

theorem sign_x0 : sign (swap (7 : Fin 8) 3 * swap 3 4) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  decide

theorem cenB_le_X_of_normal (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) {N : Subgroup G}
    (hN : ∀ g ∈ Cen (b * b₁), ∀ x ∈ N, g * x * g⁻¹ ∈ N) (h3 : ¬ 3 ∣ Nat.card ↥N) {m : G}
    (hm : m ∈ N) (hmB : m ∈ CenS B) : m ∈ Opp 3 (Cen b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : ∀ z ∈ N, Nat.Coprime 3 (orderOf z) := fun z hz => by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hd
    apply h3
    have := orderOf_dvd_natCard (⟨z, hz⟩ : ↥N)
    rw [Subgroup.orderOf_mk] at this
    exact hd.trans this
  obtain ⟨θ, hθ⟩ := exists_thM hA h
  have hmb : m ∈ Cen b :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hmB b (mem_b h)).symm
  have hmN : m ∈ Nor L := h.hyp.hLN hmb
  have hb₁N : b₁ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂N : b₂ ∈ Nor L := Subgroup.le_normalizer (Subgroup.mem_inf.1 h.hb₂).2
  have hord := hcop m hm
  have hc1 : thG L θ m * a8c = a8c * thG L θ m := by
    have e : b₁ * m = m * b₁ := Subgroup.mem_centralizer_iff.1 hmB b₁ (mem_b₁ h)
    have := congrArg (thG L θ) e
    rw [thG_mul hb₁N hmN, thG_mul hmN hb₁N, hθ.c] at this
    exact this.symm
  have hc2 : thG L θ m * a8d = a8d * thG L θ m := by
    have e : b₂ * m = m * b₂ := Subgroup.mem_centralizer_iff.1 hmB b₂ (mem_b₂ h)
    have := congrArg (thG L θ) e
    rw [thG_mul hb₂N hmN, thG_mul hmN hb₂N, hθ.d] at this
    exact this.symm
  obtain ⟨⟨i, hi, j, hj, e, he, hg⟩, hinv⟩ := cen_two _ hc1 hc2
  have hpow : (thG L θ m) ^ (orderOf m) = 1 := by
    rw [← thG_pow hmN, pow_orderOf_eq_one, thG_one]
  have h6 : (thG L θ m) ^ 6 = 1 := by rw [hg]; exact cd_pow6 i hi j hj e he
  have hsq : thG L θ m * thG L θ m = 1 := by
    have h1 : orderOf (thG L θ m) ∣ orderOf m := orderOf_dvd_of_pow_eq_one hpow
    have h2 : orderOf (thG L θ m) ∣ 2 * 3 := orderOf_dvd_of_pow_eq_one h6
    have h3 : Nat.Coprime (orderOf (thG L θ m)) 3 :=
      (Nat.Coprime.coprime_dvd_right h1 hord).symm
    have h4 : orderOf (thG L θ m) ∣ 2 := h3.dvd_of_dvd_mul_right h2
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 h4
  rcases hinv hsq with h1 | h1
  ·
    have hmL : m ∈ CenS L := (hθ.ker m hmN).1 h1
    obtain ⟨i, x, hx, hmx⟩ :=
      Q_decomp' h (Z_sq hA) m (Subgroup.mem_inf.2 ⟨hmb, hmL⟩)
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1
      (FF79.L14.Opp_le 3 _ hx)
    have hcu : Commute (b ^ i) x := (Commute.zpow_left (show Commute b x from hxb.symm) i)
    have hcm : Commute m x := by
      rw [hmx]; exact hcu.mul_left (Commute.refl x)
    have hxo : Nat.Coprime 3 (orderOf x) := by
      have hc := FF79.L14.Opp_coprime 3 (Cen b)
      have : orderOf (⟨x, hx⟩ : ↥(Opp 3 (Cen b))) ∣ Nat.card ↥(Opp 3 (Cen b)) :=
        orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at this
      exact Nat.Coprime.coprime_dvd_right this hc
    have hu1 : b ^ i = 1 := by
      have hu : b ^ i = m * x⁻¹ := by rw [hmx]; group
      have hN : (b ^ i) ^ (orderOf m * orderOf x) = 1 := by
        rw [hu, Commute.mul_pow (hcm.inv_right), inv_pow, pow_mul, pow_orderOf_eq_one, one_pow,
          mul_comm (orderOf m), pow_mul, pow_orderOf_eq_one, one_pow]
        simp
      have h3 : (b ^ i) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow3_of_mem h (mem_b h),
          one_zpow]
      have d1 : orderOf (b ^ i) ∣ orderOf m * orderOf x := orderOf_dvd_of_pow_eq_one hN
      have d2 : orderOf (b ^ i) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      have hcp : Nat.Coprime 3 (orderOf m * orderOf x) := Nat.Coprime.mul_right hord hxo
      have h4 : Nat.Coprime (orderOf (b ^ i)) 3 := (Nat.Coprime.coprime_dvd_right d1 hcp).symm
      exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h4 d2)
    rw [hmx, hu1, one_mul]
    exact hx
  ·
    exfalso
    obtain ⟨hcx, hconj, hρ3, hρ1⟩ := x0_facts
    obtain ⟨y, hy, hyθ⟩ := lift_cen_b₁ hA h hθ
      (mem_alternatingGroup.2 sign_x0) hcx
    obtain ⟨hyL, hyb₁⟩ := Subgroup.mem_inf.1 hy
    have hyN : y ∈ Nor L := Subgroup.le_normalizer hyL
    have hyb : y * b = b * y := Subgroup.mem_centralizer_singleton_iff.1 (h.hyp.hLC hyL)
    have hyb₁' : y * b₁ = b₁ * y := Subgroup.mem_centralizer_singleton_iff.1 hyb₁
    have hyD : y ∈ Cen (b * b₁) := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc y * (b * b₁) = (y * b) * b₁ := by group
        _ = (b * y) * b₁ := by rw [hyb]
        _ = b * (y * b₁) := by group
        _ = b * (b₁ * y) := by rw [hyb₁']
        _ = b * b₁ * y := by group
    have hm' : y * m * y⁻¹ ∈ N := hN _ hyD _ hm
    have hmm : m * (y * m * y⁻¹) ∈ N := mul_mem hm hm'
    have himg : thG L θ (m * (y * m * y⁻¹)) = swap 6 7 * swap 6 3 := by
      rw [thG_mul hmN (mul_mem (mul_mem hyN hmN) (inv_mem hyN)), thG_conj hyN hmN, h1, hyθ, hconj]
    have hN' := hcop _ hmm
    have hpow2 : (swap (6 : Fin 8) 7 * swap 6 3) ^ (orderOf (m * (y * m * y⁻¹))) = 1 := by
      rw [← himg, ← thG_pow (mul_mem hmN (mul_mem (mul_mem hyN hmN) (inv_mem hyN))),
        pow_orderOf_eq_one, thG_one]
    have hord3 : orderOf (swap (6 : Fin 8) 7 * swap 6 3) = 3 :=
      orderOf_eq_prime hρ3 hρ1
    have : 3 ∣ orderOf (m * (y * m * y⁻¹)) := by
      rw [← hord3]; exact orderOf_dvd_of_pow_eq_one hpow2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hN' this

theorem theta_cenB_le_X (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) {m : G} (hm : m ∈ Theta (Cen (b * b₁))) (hmB : m ∈ CenS B) :
    m ∈ Opp 3 (Cen b) :=
  cenB_le_X_of_normal hA h (fun g hg x hx => theta_norm _ hg hx) (theta_three _) hm hmB

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
