module

public import CFSG.RankThree.GF2n.Tim77.Sec43Basic
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G] [Finite G] {A Abar S₀ B : Subgroup G}

private theorem sec44i_mem_or_inv_mem {K H : Subgroup G} (hK : H.relIndex K = 2) {a y : G}
    (ha : a ∈ K) (haH : a ∉ H) (hy : y ∈ K) : y ∈ H ∨ a⁻¹ * y ∈ H := by
  by_cases hyH : y ∈ H
  · exact Or.inl hyH
  refine Or.inr ?_
  have haH' : a⁻¹ ∉ H := fun h' => haH (by simpa using H.inv_mem h')
  have h := Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf K) hK
    (a := ⟨a⁻¹, K.inv_mem ha⟩) (b := ⟨y, hy⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mk] at h
  exact h.mpr (by simp [haH', hyH])

private theorem sec44i_relIndex_eq_two {H K : Subgroup G} (hHK : H ≤ K)
    (h : Nat.card K = 2 * Nat.card H) : H.relIndex K = 2 := by
  have e := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [inf_of_le_left hHK, h] at e
  have hpos : 0 < Nat.card H := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos e

private theorem sec44i_zpow_pow {H : Type} [Group H] (z : H) (i : ℤ) (n : ℕ) (hz : z ^ n = 1) :
    (z ^ i) ^ n = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]

private theorem sec44i_even {R s : G} {i : ℤ} (hi : s = R ^ i) (hs4 : orderOf s = 4) {k : ℕ}
    (hk : R ^ 2 ^ k = 1) (hR4 : orderOf R ≠ 4) : Even i := by
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  have hm : orderOf R ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf R) i.natAbs :=
    Nat.Coprime.coprime_dvd_left hm
      (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr hodd)))
  have hgcd : Int.gcd (orderOf R : ℤ) i = 1 := hcop
  have hbez : (orderOf R : ℤ) * Int.gcdA (orderOf R : ℤ) i
      + i * Int.gcdB (orderOf R : ℤ) i = 1 := by
    have e := Int.gcd_eq_gcd_ab (orderOf R : ℤ) i
    rw [hgcd] at e
    exact_mod_cast e.symm
  have hRm : R ^ (orderOf R : ℤ) = 1 := by
    rw [zpow_natCast]
    exact pow_orderOf_eq_one R
  have hRs : R = s ^ Int.gcdB (orderOf R : ℤ) i := by
    calc R = R ^ ((orderOf R : ℤ) * Int.gcdA (orderOf R : ℤ) i
          + i * Int.gcdB (orderOf R : ℤ) i) := by rw [hbez, zpow_one]
      _ = (R ^ (orderOf R : ℤ)) ^ Int.gcdA (orderOf R : ℤ) i
          * (R ^ i) ^ Int.gcdB (orderOf R : ℤ) i := by rw [zpow_add, zpow_mul, zpow_mul]
      _ = s ^ Int.gcdB (orderOf R : ℤ) i := by rw [hRm, one_zpow, one_mul, hi]
  have hs4' : s ^ 4 = 1 := by
    rw [← hs4]
    exact pow_orderOf_eq_one s
  have h4 : orderOf R ∣ 4 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hRs]
    exact sec44i_zpow_pow s _ 4 hs4'
  have hm2 : orderOf R ∣ 2 := by
    have h4' : orderOf R ∣ 2 ^ 2 := by
      norm_num
      exact h4
    obtain ⟨j, hj, hmj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4'
    interval_cases j
    · rw [hmj]
      norm_num
    · rw [hmj]
      norm_num
    · exact (hR4 (by rw [hmj]; norm_num)).elim
  have hR2 : R ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hm2
  have hs2 : s ^ 2 = 1 := by
    rw [hi]
    exact sec44i_zpow_pow R i 2 hR2
  have h2 : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one hs2
  rw [hs4] at h2
  norm_num at h2

theorem sec44_trivial_contra (h : Sec3Ctx A Abar S₀ B) {s : G}
    (hs : Section3.IsSChoice A Abar S₀ B s) (hne : conjSubgroup s Abar ≠ Abar)
    (hg : ∀ w ∈ Section3.Y A Abar s, s * w * s⁻¹ * w⁻¹ ∈ Section3.N A Abar s) : False := by
  have hsN : s ∈ normalizer (Section3.Y A Abar s : Set G) := sa_mem_normalizer_Y h hs
  have hsA0 : s ∈ centralizer (Section3.A0 A Abar : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => (sa_comm_A h hs (h.setup.L_le ha)).symm
  have hsC : s ∈ centralizer (Section3.N A Abar s : Set G) :=
    sa_centralizes_N h hs hsN hsA0 hg
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ Section3.Abar0 A Abar, x ≠ 1 := by
    obtain ⟨b, -, -, hdisj⟩ := hs
    rcases hdisj with ⟨⟨x, hx, hx1, -⟩, -⟩ | ⟨-, x, hx, hx1, -⟩
    · exact ⟨x, hx, hx1⟩
    · exact ⟨x, hx, hx1⟩
  have hxs : x * s = s * x := Subgroup.mem_centralizer_iff.mp hsC x (sa_Abar0_le_N hx)
  have hxAb : x ∈ Abar := h.setup.Lb_le hx
  have hxc : x ∈ conjSubgroup s Abar := by
    rw [mem_conjSubgroup]
    have e : s⁻¹ * x * s = x := by
      calc s⁻¹ * x * s = s⁻¹ * (x * s) := by group
        _ = s⁻¹ * (s * x) := by rw [hxs]
        _ = x := by group
    rw [e]
    exact hxAb
  have hbot : Abar ⊓ conjSubgroup s Abar ≠ ⊥ := by
    intro hb
    apply hx1
    have hmem : x ∈ Abar ⊓ conjSubgroup s Abar := Subgroup.mem_inf.mpr ⟨hxAb, hxc⟩
    rw [hb] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact hne (conjSubgroup_eq_of_isTI h.setup.ti_Ab hbot)

theorem sec44_inner_contra (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    {b s x₀ : G} (hsc : Sec3SChoiceAt A Abar S₀ B b s)
    (hx₀ : x₀ ∈ Section3.Abar0 A Abar) (hx₀1 : x₀ ≠ 1) (hsx : s ∈ Subgroup.closure {x₀, b})
    (hs4 : orderOf s = 4) (hne : conjSubgroup s Abar ≠ Abar)
    {y c : G} (hy : y ∈ Section3.Y A Abar s) (hc : c ∈ conjSubgroup y A)
    (hc0 : c ∉ conjSubgroup y (Section3.A0 A Abar))
    (hCA : conjSubgroup y A ≤ centralizer (A : Set G))
    (hg : ∀ w ∈ Section3.Y A Abar s, (c * s) * w * (c * s)⁻¹ * w⁻¹ ∈ Section3.N A Abar s) :
    False := by
  obtain ⟨hbB, hb1, hdisj⟩ := hsc
  have hs : Section3.IsSChoice A Abar S₀ B s := by
    unfold Section3.IsSChoice
    exact ⟨b, hbB, hb1, hdisj⟩
  have hbb : b * b = 1 := sa_sq_of_mem_B h hbB
  have hx₀Ab : x₀ ∈ Abar := h.setup.Lb_le hx₀
  have hxx : x₀ * x₀ = 1 := h.setup.sq_Ab hx₀Ab
  have hxi : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_right hxx
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hx₀N : x₀ ∈ Section3.N A Abar s := sa_Abar0_le_N hx₀
  have hx₀S : x₀ ∈ S₀ := h.abar0_le_s0 hx₀
  have hbS : b ∈ S₀ := h.b_le_s0 hbB
  have hr4 : orderOf (x₀ * b) ≠ 4 := by
    rcases hdisj with ⟨-, hsb⟩ | ⟨hno, -⟩
    · exfalso
      rw [hsb] at hs4
      have h2 : b ^ 2 = 1 := by rw [sq]; exact hbb
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hs4] at h3
      norm_num at h3
    · exact fun h4 => (hno x₀ hx₀ hx₀1).2 h4
  obtain ⟨R, hR⟩ : ∃ R : G, R = x₀ * b := ⟨_, rfl⟩
  have hRS : R ∈ S₀ := by
    rw [hR]
    exact S₀.mul_mem hx₀S hbS
  have hr4' : orderOf R ≠ 4 := by
    rw [hR]
    exact hr4
  obtain ⟨i, hi⟩ : ∃ i : ℤ, s = R ^ i := by
    rcases sec34_closure_pair hxx hbb hsx with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨i, by rw [hR]; exact hi⟩
    · exfalso
      have hs' : s = (x₀ * b) ^ i * x₀ := by
        rw [← hi, mul_assoc, hxx, mul_one]
      have h1 : s * s = 1 := by
        rw [hs']
        calc (x₀ * b) ^ i * x₀ * ((x₀ * b) ^ i * x₀)
            = (x₀ * b) ^ i * (x₀ * (x₀ * b) ^ i * x₀) := by group
          _ = (x₀ * b) ^ i * (x₀ * b) ^ (-i) := by rw [sec34_conj_zpow hxx hbb i]
          _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero]
      have h2 : s ^ 2 = 1 := by rw [sq]; exact h1
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hs4] at h3
      norm_num at h3
  have hk2 : ∃ k : ℕ, R ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := h.isPGroup_s0 ⟨R, hRS⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨k₂, hk₂⟩ := hk2
  obtain ⟨j, hj⟩ := sec44i_even hi hs4 hk₂ hr4'
  have hsR : R * s = s * R := by
    rw [hi]
    exact ((Commute.refl R).zpow_left i).symm.eq
  have hxs' : x₀ * s * x₀ = s⁻¹ := by
    rw [hi, hR, sec34_conj_zpow hxx hbb i, zpow_neg]
  have hbR : b * R * b⁻¹ = R⁻¹ := by
    rw [hR, mul_inv_rev, hxi, hbi, show b * (x₀ * b) * b = b * x₀ * (b * b) by group, hbb,
      mul_one]
  have hbs : b * s * b⁻¹ = s⁻¹ := by
    rw [hi, ← conj_zpow, hbR, inv_zpow]
  have hA1 : x₀ * R * x₀ = R⁻¹ := by
    rw [hR, mul_inv_rev, hxi, hbi, show x₀ * (x₀ * b) * x₀ = (x₀ * x₀) * (b * x₀) by group, hxx,
      one_mul]
  have hA2 : x₀ * R⁻¹ * x₀ = R := by
    rw [hR, mul_inv_rev, hxi, hbi, show x₀ * (b * x₀) * x₀ = (x₀ * b) * (x₀ * x₀) by group, hxx,
      mul_one]
  obtain ⟨-, hYN, hNab⟩ := tim77Sec32a_holds G A Abar S₀ B s h hs
  have hNc : ∀ x ∈ Section3.N A Abar s, ∀ w ∈ Section3.N A Abar s, x * w = w * x :=
    fun x hx w hw => congrArg Subtype.val (hNab.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)
  have hNe : ∀ n ∈ Section3.N A Abar s, n * n = 1 := fun n hn => by
    rw [← sq]
    exact hNab.2 n hn
  have hsA : ∀ a ∈ A, s * a = a * s := fun a ha => sa_comm_A h hs ha
  have hsN : s ∈ normalizer (Section3.Y A Abar s : Set G) := sa_mem_normalizer_Y h hs
  have hCY : conjSubgroup y A ≤ Section3.Y A Abar s :=
    sec41_conj_le (Subgroup.le_normalizer hy) sa_A_le_Y
  have hCe : IsElemAbelian 2 (conjSubgroup y A) := isElemAbelian_conj h.hyp.elemAbelian y
  have hCTI : IsTI (conjSubgroup y A) := isTI_conjSubgroup h.hyp.ti y
  have hCcomm : ∀ x ∈ conjSubgroup y A, ∀ z ∈ conjSubgroup y A, x * z = z * x :=
    fun x hx z hz => congrArg Subtype.val (hCe.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hcc : c * c = 1 := by
    rw [← sq]
    exact hCe.2 c hc
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hcY : c ∈ Section3.Y A Abar s := hCY hc
  obtain ⟨k, hkAb, hkA, hkA0⟩ := sa_exists_k h
  have hkY : k ∈ Section3.Y A Abar s := (sup_le sa_A_le_Y sa_Abar_le_Y) hkAb
  have hAbTI : IsTI Abar := h.setup.ti_Ab
  obtain ⟨g, hgdef⟩ : ∃ g : G, g = c * s := ⟨_, rfl⟩
  have hsc' : s = c * g := by
    rw [hgdef, ← mul_assoc, hcc, one_mul]
  have hgY : ∀ w ∈ Section3.Y A Abar s, g * w * g⁻¹ * w⁻¹ ∈ Section3.N A Abar s := by
    intro w hw
    rw [hgdef]
    exact hg w hw
  have hgA : ∀ a ∈ A, a * g = g * a := by
    intro a ha
    have hac : a * c = c * a := Subgroup.mem_centralizer_iff.mp (hCA hc) a ha
    calc a * g = (a * c) * s := by rw [hgdef]; group
      _ = (c * a) * s := by rw [hac]
      _ = c * (a * s) := by group
      _ = c * (s * a) := by rw [hsA a ha]
      _ = g * a := by rw [hgdef]; group
  have hgC' : g ∈ centralizer (Section3.A0 A Abar : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => hgA a (h.setup.L_le ha)
  have hgN : g ∈ normalizer (Section3.Y A Abar s : Set G) := by
    rw [hgdef]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hcY) hsN
  have hgC : g ∈ centralizer (Section3.N A Abar s : Set G) :=
    sa_centralizes_N h hs hgN hgC' hgY
  have hgNc : ∀ n ∈ Section3.N A Abar s, n * g = g * n :=
    fun n hn => Subgroup.mem_centralizer_iff.mp hgC n hn
  have hgx : g * x₀ = x₀ * g := (Subgroup.mem_centralizer_iff.mp hgC x₀ hx₀N).symm
  have hnc : ¬ ∀ x ∈ conjSubgroup y A, ∀ w ∈ conjSubgroup k A, x * w = w * x := by
    intro hall
    apply hne
    rw [← hkA] at hall
    have hcx : c * x₀ = x₀ * c := hall c hc x₀ hx₀Ab
    have hcn : c ∈ normalizer (Abar : Set G) :=
      mem_normalizer_of_commute_of_isTI hAbTI hx₀Ab hx₀1 hcx
    have hgn : g ∈ normalizer (Abar : Set G) :=
      mem_normalizer_of_commute_of_isTI hAbTI hx₀Ab hx₀1 hgx
    have hsn : s ∈ normalizer (Abar : Set G) := by
      rw [hsc']
      exact Subgroup.mul_mem _ hcn hgn
    exact conjSubgroup_eq_self_iff.mpr hsn
  have S : Prop24Setup (conjSubgroup y A) Abar (conjSubgroup y (Section3.A0 A Abar))
      (Section3.Abar0 A Abar) (conjSubgroup y (Section3.A0 A Abar) ⊔ Section3.Abar0 A Abar) := by
    have T := sec41_prop24 h hYN hNc hy hkY hnc
    rw [← hkA0, ← hkA] at T
    exact T
  have hC₀C : conjSubgroup y (Section3.A0 A Abar) ≤ conjSubgroup y A := S.L_le
  have hĀ₀Ā : Section3.Abar0 A Abar ≤ Abar := S.Lb_le
  have hC₀N : conjSubgroup y (Section3.A0 A Abar) ≤ Section3.N A Abar s :=
    sec41_conj_le (hYN y hy) sa_A0_le_N
  have hCN : ∀ u ∈ conjSubgroup y A, u ∈ Section3.N A Abar s →
      u ∈ conjSubgroup y (Section3.A0 A Abar) := fun u hu huN =>
    S.mem_L_of_commute hu hx₀Ab hx₀1 (hNc u huN x₀ hx₀N)
  have hx₀n : x₀ ∈ normalizer (conjSubgroup y A : Set G) := (S.mem_Lb.mp hx₀).2
  have hq' : (Section3.Abar0 A Abar).relIndex Abar = 2 := hq
  have hcardC : Nat.card (conjSubgroup y A)
      = 2 * Nat.card (conjSubgroup y (Section3.A0 A Abar)) := by
    have e3 : Nat.card Abar = 2 * Nat.card (Section3.Abar0 A Abar) := by
      have e := Subgroup.relIndex_mul_card (H := Section3.Abar0 A Abar) (K := Abar)
      rw [inf_of_le_left hĀ₀Ā, hq'] at e
      exact e.symm
    have e4 : Nat.card (Section3.Abar0 A Abar) = Nat.card (conjSubgroup y (Section3.A0 A Abar)) :=
      S.card_Lb_eq
    have e2 : Nat.card Abar = Nat.card A := by
      rw [hkA, card_conjSubgroup]
    rw [card_conjSubgroup, ← e2, e3, e4]
  have hK : (conjSubgroup y (Section3.A0 A Abar)).relIndex (conjSubgroup y A) = 2 :=
    sec44i_relIndex_eq_two hC₀C hcardC
  obtain ⟨v, hvdef⟩ : ∃ v : G, v = x₀ * c * x₀ * c := ⟨_, rfl⟩
  have hx₀cC : x₀ * c * x₀ ∈ conjSubgroup y A := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hx₀n c).mp hc
    rwa [hxi] at h1
  have hvN : v ∈ Section3.N A Abar s := by
    have h1 : c * x₀ * c⁻¹ ∈ Section3.N A Abar s :=
      (Subgroup.mem_normalizer_iff.mp (hYN c hcY) x₀).mp hx₀N
    rw [hcinv] at h1
    rw [hvdef, show x₀ * c * x₀ * c = x₀ * (c * x₀ * c) by group]
    exact Subgroup.mul_mem _ hx₀N h1
  have hvC₀ : v ∈ conjSubgroup y (Section3.A0 A Abar) := by
    refine hCN v ?_ hvN
    rw [hvdef]
    exact Subgroup.mul_mem _ hx₀cC hc
  have hvC : v ∈ conjSubgroup y A := hC₀C hvC₀
  have hv1 : v ≠ 1 := by
    intro hv
    have h0 : x₀ * c * x₀ * c = 1 := by rw [← hvdef, hv]
    have h1 : x₀ * c * x₀ = c := by
      rw [mul_eq_one_iff_eq_inv] at h0
      rw [h0, hcinv]
    have h2 : c * x₀ = x₀ * c := by
      calc c * x₀ = (x₀ * c * x₀) * x₀ := by rw [h1]
        _ = x₀ * c * (x₀ * x₀) := by group
        _ = x₀ * c := by rw [hxx, mul_one]
    exact hc0 (S.mem_L_of_commute hc hx₀Ab hx₀1 h2)
  have hxcx : x₀ * c * x₀ = v * c := by
    rw [hvdef, mul_assoc (x₀ * c * x₀) c c, hcc, mul_one]
  have hs4' : s * s * s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs4] at h
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h
  have hsinv : s⁻¹ = s * s * s := inv_eq_of_mul_eq_one_right (by
    rw [← hs4']
    group)
  have hsq_inv : s⁻¹ * s⁻¹ = s * s := by
    rw [hsinv]
    calc s * s * s * (s * s * s) = (s * s * s * s) * (s * s) := by group
      _ = s * s := by rw [hs4', one_mul]
  have hss : s * s = x₀ * (s * x₀ * s⁻¹) := by
    calc s * s = s⁻¹ * s⁻¹ := hsq_inv.symm
      _ = (x₀ * s * x₀) * s⁻¹ := by rw [hxs']
      _ = x₀ * (s * x₀ * s⁻¹) := by group
  have hgx0 : g * x₀ * g⁻¹ = x₀ := by
    rw [hgx]
    group
  have hsx0 : s * x₀ * s⁻¹ = c * x₀ * c := by
    rw [hsc']
    calc c * g * x₀ * (c * g)⁻¹ = c * (g * x₀ * g⁻¹) * c⁻¹ := by group
      _ = c * x₀ * c⁻¹ := by rw [hgx0]
      _ = c * x₀ * c := by rw [hcinv]
  have hss' : s * s = v := by
    rw [hss, hsx0, hvdef]
    group
  have hgC0 : ∀ u ∈ conjSubgroup y (Section3.A0 A Abar), g * u * g⁻¹ = u := by
    intro u hu
    have e := Subgroup.mem_centralizer_iff.mp hgC u (hC₀N hu)
    rw [← e]
    group
  have hgnC : g ∈ normalizer (conjSubgroup y A : Set G) := by
    apply conjSubgroup_eq_self_iff.mp
    apply conjSubgroup_eq_of_isTI hCTI
    intro hbot
    apply hv1
    have hvg : v * g = g * v := Subgroup.mem_centralizer_iff.mp hgC v hvN
    have hmem : v ∈ conjSubgroup y A ⊓ conjSubgroup g (conjSubgroup y A) := by
      refine Subgroup.mem_inf.mpr ⟨hvC, ?_⟩
      rw [mem_conjSubgroup]
      have e : g⁻¹ * v * g = v := by
        calc g⁻¹ * v * g = g⁻¹ * (v * g) := by group
          _ = g⁻¹ * (g * v) := by rw [hvg]
          _ = v := by group
      rw [e]
      exact hvC
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  obtain ⟨n, hndef⟩ : ∃ n : G, n = g * c * g⁻¹ * c⁻¹ := ⟨_, rfl⟩
  have hnN : n ∈ Section3.N A Abar s := by
    rw [hndef]
    exact hgY c hcY
  have hgcC : g * c * g⁻¹ ∈ conjSubgroup y A :=
    (Subgroup.mem_normalizer_iff.mp hgnC c).mp hc
  have hnC : n ∈ conjSubgroup y A := by
    rw [hndef]
    exact Subgroup.mul_mem _ hgcC (Subgroup.inv_mem _ hc)
  have hnC₀ : n ∈ conjSubgroup y (Section3.A0 A Abar) := hCN n hnC hnN
  have hgcn : g * c * g⁻¹ = n * c := by
    rw [hndef]
    group
  have hcnc : c * n * c = n := by
    rw [hCcomm c hc n hnC, mul_assoc, hcc, mul_one]
  have hkey2 : n * (g * g) = v := by
    rw [← hss']
    calc n * (g * g) = c * (n * c) * (g * g) := by rw [← mul_assoc c n c, hcnc]
      _ = c * (g * c * g⁻¹) * (g * g) := by rw [hgcn]
      _ = (c * g) * (c * g) := by group
      _ = s * s := by rw [hsc']
  have hgg : g * g = n⁻¹ * v := by
    rw [← hkey2]
    group
  have hggC₀ : g * g ∈ conjSubgroup y (Section3.A0 A Abar) := by
    rw [hgg]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hnC₀) hvC₀
  have hggY : ∀ w ∈ Section3.Y A Abar s, w * (g * g) * w⁻¹ = g * g := by
    intro w hw
    obtain ⟨m, hmdef⟩ : ∃ m : G, m = g * w * g⁻¹ * w⁻¹ := ⟨_, rfl⟩
    have hmN : m ∈ Section3.N A Abar s := by
      rw [hmdef]
      exact hgY w hw
    have hmi : m⁻¹ ∈ Section3.N A Abar s := Subgroup.inv_mem _ hmN
    have hmg : w * g * w⁻¹ = m⁻¹ * g := by
      rw [hmdef]
      group
    have hcomm' : g * m⁻¹ = m⁻¹ * g := (hgNc m⁻¹ hmi).symm
    calc w * (g * g) * w⁻¹ = (w * g * w⁻¹) * (w * g * w⁻¹) := by group
      _ = (m⁻¹ * g) * (m⁻¹ * g) := by rw [hmg]
      _ = m⁻¹ * (g * m⁻¹) * g := by group
      _ = m⁻¹ * (m⁻¹ * g) * g := by rw [hcomm']
      _ = (m⁻¹ * m⁻¹) * (g * g) := by group
      _ = g * g := by rw [hNe m⁻¹ hmi, one_mul]
  obtain ⟨β, hβAb, hβ0⟩ : ∃ β ∈ Abar, β ∉ Section3.Abar0 A Abar := by
    by_contra hcon
    apply S.Lb_ne
    apply le_antisymm hĀ₀Ā
    intro x hx
    by_contra hx0
    exact hcon ⟨x, hx, hx0⟩
  have hβY : β ∈ Section3.Y A Abar s := sa_Abar_le_Y hβAb
  have hβgg : β * (g * g) = (g * g) * β := by
    calc β * (g * g) = (β * (g * g) * β⁻¹) * β := by group
      _ = (g * g) * β := by rw [hggY β hβY]
  have hgg1 : g * g = 1 := by
    have hmem : g * g ∈ Section3.Abar0 A Abar :=
      S.symm.mem_L_of_commute_M hβAb hβ0 (Subgroup.mem_sup_left hggC₀) hβgg
    have hin : g * g ∈ conjSubgroup y A ⊓ Abar :=
      Subgroup.mem_inf.mpr ⟨hC₀C hggC₀, hĀ₀Ā hmem⟩
    rw [S.inf_eq_bot, Subgroup.mem_bot] at hin
    exact hin
  have hnv : n = v := by
    have h1 : n⁻¹ * v = 1 := by
      rw [← hgg, hgg1]
    exact inv_mul_eq_one.mp h1
  have hgcx : g * c * g⁻¹ = x₀ * c * x₀ := by
    rw [hgcn, hnv, hxcx]
  have hσ : ∀ u ∈ conjSubgroup y A, s * u * s⁻¹ = x₀ * u * x₀ := by
    intro u hu
    have hxuC : x₀ * u * x₀ ∈ conjSubgroup y A := by
      have h1 := (Subgroup.mem_normalizer_iff.mp hx₀n u).mp hu
      rwa [hxi] at h1
    have hgu : g * u * g⁻¹ = x₀ * u * x₀ := by
      rcases sec44i_mem_or_inv_mem hK hc hc0 hu with hu0 | hu0
      · have hxu : x₀ * u = u * x₀ := hNc x₀ hx₀N u (hC₀N hu0)
        rw [hgC0 u hu0, hxu, mul_assoc, hxx, mul_one]
      · obtain ⟨t, htdef⟩ : ∃ t : G, t = c⁻¹ * u := ⟨_, rfl⟩
        have hu_eq : u = c * t := by
          rw [htdef]
          group
        rw [← htdef] at hu0
        have htN : t ∈ Section3.N A Abar s := hC₀N hu0
        have hgt : g * t * g⁻¹ = t := hgC0 t hu0
        have htx : t * x₀ = x₀ * t := hNc t htN x₀ hx₀N
        rw [hu_eq]
        calc g * (c * t) * g⁻¹ = (g * c * g⁻¹) * (g * t * g⁻¹) := by group
          _ = (x₀ * c * x₀) * t := by rw [hgcx, hgt]
          _ = x₀ * (c * t) * x₀ := by
            calc (x₀ * c * x₀) * t = x₀ * c * (x₀ * t) := by group
              _ = x₀ * c * (t * x₀) := by rw [htx]
              _ = x₀ * (c * t) * x₀ := by group
    calc s * u * s⁻¹ = c * (g * u * g⁻¹) * c⁻¹ := by rw [hsc']; group
      _ = c * (x₀ * u * x₀) * c⁻¹ := by rw [hgu]
      _ = x₀ * u * x₀ := by
        rw [hcinv, hCcomm c hc _ hxuC, mul_assoc (x₀ * u * x₀) c c, hcc, mul_one]
  have hbC : b ∈ normalizer (conjSubgroup y A : Set G) := by
    apply conjSubgroup_eq_self_iff.mp
    apply conjSubgroup_eq_of_isTI hCTI
    intro hbot
    apply hv1
    have hvb : b * v * b⁻¹ = v := by
      rw [← hss']
      calc b * (s * s) * b⁻¹ = (b * s * b⁻¹) * (b * s * b⁻¹) := by group
        _ = s⁻¹ * s⁻¹ := by rw [hbs]
        _ = s * s := hsq_inv
    have hmem : v ∈ conjSubgroup y A ⊓ conjSubgroup b (conjSubgroup y A) := by
      refine Subgroup.mem_inf.mpr ⟨hvC, ?_⟩
      rw [mem_conjSubgroup]
      have e : b⁻¹ * v * b = v := by
        rw [hbi]
        calc b * v * b = b * v * b⁻¹ := by rw [hbi]
          _ = v := hvb
      rw [e]
      exact hvC
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hRn : R ∈ normalizer (conjSubgroup y A : Set G) := by
    rw [hR]
    exact Subgroup.mul_mem _ hx₀n hbC
  have hb' : ∀ u ∈ conjSubgroup y A,
      R * (x₀ * u * x₀) * R⁻¹ = x₀ * (R * u * R⁻¹) * x₀ := by
    intro u hu
    have hαu : R * u * R⁻¹ ∈ conjSubgroup y A :=
      (Subgroup.mem_normalizer_iff.mp hRn u).mp hu
    rw [← hσ u hu, ← hσ _ hαu]
    calc R * (s * u * s⁻¹) * R⁻¹ = (R * s) * u * (R * s)⁻¹ := by group
      _ = (s * R) * u * (s * R)⁻¹ := by rw [hsR]
      _ = s * (R * u * R⁻¹) * s⁻¹ := by group
  have hc' : ∀ u ∈ conjSubgroup y A,
      x₀ * (R * (x₀ * u * x₀) * R⁻¹) * x₀ = R⁻¹ * u * R := by
    intro u _
    calc x₀ * (R * (x₀ * u * x₀) * R⁻¹) * x₀ = (x₀ * R * x₀) * u * (x₀ * R⁻¹ * x₀) := by
          group
      _ = R⁻¹ * u * R := by rw [hA1, hA2]
  have hRuR : ∀ u ∈ conjSubgroup y A, R * u * R⁻¹ = R⁻¹ * u * R := by
    intro u hu
    calc R * u * R⁻¹ = x₀ * (x₀ * (R * u * R⁻¹) * x₀) * x₀ := by
          rw [show x₀ * (x₀ * (R * u * R⁻¹) * x₀) * x₀
              = (x₀ * x₀) * (R * u * R⁻¹) * (x₀ * x₀) by group, hxx, one_mul, mul_one]
      _ = x₀ * (R * (x₀ * u * x₀) * R⁻¹) * x₀ := by rw [hb' u hu]
      _ = R⁻¹ * u * R := hc' u hu
  have hR2 : ∀ u ∈ conjSubgroup y A, R * R * u = u * (R * R) := by
    intro u hu
    calc R * R * u = R * (R * u * R⁻¹) * R := by group
      _ = R * (R⁻¹ * u * R) * R := by rw [hRuR u hu]
      _ = u * (R * R) := by group
  have hsu_comm : ∀ u ∈ conjSubgroup y A, s * u = u * s := by
    intro u hu
    have hcomm2 : Commute (R ^ 2) u := by
      rw [sq]
      exact hR2 u hu
    have hpow := hcomm2.zpow_left j
    have hsj : s = (R ^ 2) ^ j := by
      rw [hi, hj, ← zpow_natCast R 2, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [hsj]
    exact hpow.eq
  have hfin : x₀ * c * x₀ = c := by
    have h1 := hσ c hc
    have h2 : s * c * s⁻¹ = c := by
      rw [hsu_comm c hc]
      group
    exact h1.symm.trans h2
  exact hv1 (by rw [hvdef, hfin, hcc])

end CFSG.RankThree.GF2n.Tim77
