module

public import CFSG.Quasithin.Background.E2SeventeenNorm
public import CFSG.Quasithin.Background.E2SolvTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

variable {G : Type*} [Group G] [Finite G]

theorem mem_twoResidual_of_odd' {H : Subgroup G} {x : G} (hx : x ∈ H)
    (ho : Odd (orderOf x)) : x ∈ twoResidual H := by
  obtain ⟨b, hb⟩ := twoResidual_isTwoQuotient H x hx
  exact B6.mem_of_pow_mem_of_coprime hb (Nat.Coprime.pow_right b (Odd.coprime_two_right ho))

structure Setting17 (H T M V U : Subgroup G) (x z : G) : Prop where
  dp : DihedralPair H T V U x z
  mp : MinParabolic H T M
  solv : Group.IsSolvable H
  res : twoResidual M ≤ Subgroup.centralizer (V : Set G)
  V16 : Nat.card V = 2 ^ 4
  q32 : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI dp.elem H)
  z3 : orderOf z = 3
  Z2 : Nat.card (dpZ V z) = 2
  CA : V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z
  UQ : U ≤ pCoreOf 2 H

namespace Setting17

variable {H T M V U : Subgroup G} {x z : G}

@[expose] def IsInv (H : Subgroup G) (x w : G) : Prop :=
  w ∈ H ∧ Odd (orderOf w) ∧ w ≠ 1 ∧ x * w * x⁻¹ = w⁻¹

abbrev Z0 (H V : Subgroup G) : Subgroup G := V ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)

theorem inv (s : Setting17 H T M V U x z) {w : G} (hw : IsInv H x w) :
    orderOf w = 3 ∧ Nat.card (dpZ V w) = 2 ∧
      V ⊓ Subgroup.centralizer (dpA H V U w : Set G) = dpZ V w ∧ dpZ V w = Z0 H V :=
  s.dp.inv_facts s.UQ s.V16 s.q32 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2

theorem dpw (s : Setting17 H T M V U x z) {w : G} (hw : IsInv H x w) :
    DihedralPair H T V U x w :=
  s.dp.ofInv s.UQ hw.1 hw.2.1 hw.2.2.1 hw.2.2.2

theorem isInv_z (s : Setting17 H T M V U x z) : IsInv H x z :=
  ⟨s.dp.zH, s.dp.zodd, s.dp.z1, s.dp.xz⟩

theorem Zeq (s : Setting17 H T M V U x z) : dpZ V z = Z0 H V := (s.inv s.isInv_z).2.2.2

theorem U_eq (s : Setting17 H T M V U x z) : U = V ⊓ pCoreOf 2 H :=
  le_antisymm (le_inf s.dp.UV s.UQ) s.dp.VQU

theorem x2 (s : Setting17 H T M V U x z) : x * x = 1 := s.dp.x2

theorem xinv (s : Setting17 H T M V U x z) : x⁻¹ = x := inv_eq_of_mul_eq_one_right s.x2

theorem eq_one_of_mem_Q (s : Setting17 H T M V U x z) {q : G} (hq : q ∈ pCoreOf 2 H)
    (ho : Odd (orderOf q)) : q = 1 := by
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one s.dp.T2 (s.dp.QT hq)
  exact eq_one_of_odd_orderOf_of_pow_two_pow ho hk

theorem three_pow_mem (s : Setting17 H T M V U x z) :
    ∀ k ∈ twoResidual H, ∃ a : ℕ, k ^ 3 ^ a ∈ pCoreOf 2 H := by
  obtain ⟨p, hp, hp2, hpow⟩ := s.mp.exists_prime_pow_mem_pCoreOf s.solv
  have hzK : z ∈ twoResidual H := mem_twoResidual_of_odd' s.dp.zH s.dp.zodd
  obtain ⟨a, ha⟩ := hpow z hzK
  have hodd : Odd (orderOf (z ^ p ^ a)) := Odd.of_dvd_nat s.dp.zodd (orderOf_pow_dvd _)
  have h1 : z ^ p ^ a = 1 := s.eq_one_of_mem_Q ha hodd
  have h3 : 3 ∣ p ^ a := by
    rw [← s.z3]
    exact orderOf_dvd_of_pow_eq_one h1
  have h3p : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow h3
  have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p).symm
  exact hp3 ▸ hpow

theorem two_mem (s : Setting17 H T M V U x z) {y : G} (hy : y ∈ twoResidual H) {k : ℕ}
    (hk : y ^ 2 ^ k = 1) : y ∈ pCoreOf 2 H := by
  obtain ⟨a, ha⟩ := s.three_pow_mem y hy
  refine B6.mem_of_pow_mem_of_coprime ha ?_
  exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)
    (Nat.Coprime.pow k a (by norm_num))

theorem odd_mem_centralizer (s : Setting17 H T M V U x z) {c : G} (hc : c ∈ M)
    (ho : Odd (orderOf c)) : c ∈ Subgroup.centralizer (V : Set G) :=
  s.res (mem_twoResidual_of_odd' hc ho)

theorem QN (s : Setting17 H T M V U x z) : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  s.dp.HQ

@[expose] def Nx (s : Setting17 H T M V U x z) : Subgroup G where
  carrier := {g | g ∈ H ∧ g * x * g⁻¹ * x⁻¹ ∈ pCoreOf 2 H}
  one_mem' := ⟨H.one_mem, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hgx⟩ ⟨hh, hhx⟩
    refine ⟨H.mul_mem hg hh, ?_⟩
    have h1 : g * (h * x * h⁻¹ * x⁻¹) * g⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (s.QN hg) _).mp hhx
    have e : g * h * x * (g * h)⁻¹ * x⁻¹ =
        (g * (h * x * h⁻¹ * x⁻¹) * g⁻¹) * (g * x * g⁻¹ * x⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem h1 hgx
  inv_mem' := by
    rintro g ⟨hg, hgx⟩
    refine ⟨H.inv_mem hg, ?_⟩
    have h1 : g⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * g⁻¹⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (s.QN (H.inv_mem hg)) _).mp ((pCoreOf 2 H).inv_mem hgx)
    have e : g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ = g⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact h1

theorem TU (s : Setting17 H T M V U x z) : T ≤ Subgroup.normalizer (U : Set G) := by
  rw [s.U_eq]
  exact B2F.le_normalizer_inf s.dp.TV (s.dp.TH.trans s.QN)

theorem T_le_Nx (s : Setting17 H T M V U x z) : T ≤ s.Nx := by
  intro t ht
  refine ⟨s.dp.TH ht, ?_⟩
  have htx : t * x * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (s.dp.TV ht) x).mp s.dp.xV
  rcases s.dp.U2 _ htx with h | h
  · exfalso
    apply s.dp.xU
    have := (Subgroup.mem_normalizer_iff.mp (s.TU (T.inv_mem ht)) _).mp h
    simpa [mul_assoc] using this
  · have e : t * x * t⁻¹ * x⁻¹ = x * (t * x * t⁻¹) := by
      rw [s.xinv, isElemAbelian_comm s.dp.elem htx s.dp.xV]
    rw [e]
    exact s.UQ h

theorem z_not_mem_Nx (s : Setting17 H T M V U x z) : z ∉ s.Nx := by
  rintro ⟨-, hzx⟩
  have hxz' : x * z⁻¹ * x⁻¹ = z := by
    calc x * z⁻¹ * x⁻¹ = (x * z * x⁻¹)⁻¹ := by group
      _ = z := by rw [s.dp.xz, inv_inv]
  have e : z * x * z⁻¹ * x⁻¹ = z ^ 2 := by
    calc z * x * z⁻¹ * x⁻¹ = z * (x * z⁻¹ * x⁻¹) := by group
      _ = z ^ 2 := by rw [hxz', pow_two]
  rw [e] at hzx
  have hodd : Odd (orderOf (z ^ 2)) := Odd.of_dvd_nat s.dp.zodd (orderOf_pow_dvd 2)
  have h1 := s.eq_one_of_mem_Q hzx hodd
  have : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one h1
  rw [s.z3] at this
  omega

theorem Nx_le_M (s : Setting17 H T M V U x z) : s.Nx ≤ M :=
  s.mp.le_of_lt s.T_le_Nx (lt_of_le_of_ne (fun g hg => hg.1) fun h =>
    s.z_not_mem_Nx (by rw [h]; exact s.dp.zH))

theorem normalizes (s : Setting17 H T M V U x z) {c : G} (hcK : c ∈ twoResidual H)
    (hcN : c ∈ s.Nx) : c ∈ Subgroup.normalizer (V : Set G) := by
  obtain ⟨a, b, rfl, ha, hb, ⟨k, hk⟩, hbo⟩ := exists_two_part_odd_part c
  have hzp : Subgroup.zpowers (b * a) ≤ twoResidual H := Subgroup.zpowers_le.2 hcK
  have hzN : Subgroup.zpowers (b * a) ≤ s.Nx := Subgroup.zpowers_le.2 hcN
  have haQ : a ∈ pCoreOf 2 H := s.two_mem (hzp ha) hk
  have hbC : b ∈ Subgroup.centralizer (V : Set G) := s.odd_mem_centralizer (s.Nx_le_M (hzN hb)) hbo
  exact Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hbC) (s.dp.TV (s.dp.QT haQ))

theorem decomp (s : Setting17 H T M V U x z) {k : G} (hk : k ∈ twoResidual H) :
    ∃ i c : G, k = i * c ∧ c ∈ twoResidual H ∧ c ∈ s.Nx ∧ i ∈ twoResidual H ∧
      (i = 1 ∨ IsInv H x i) := by
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hKn : H ≤ Subgroup.normalizer (twoResidual H : Set G) := le_normalizer_twoResidual H
  have hxH : x ∈ H := s.dp.VH s.dp.xV
  set t := k * x * k⁻¹ * x⁻¹ with ht
  have htK : t ∈ twoResidual H := by
    have h1 : x * k⁻¹ * x⁻¹ ∈ twoResidual H :=
      (Subgroup.mem_normalizer_iff.mp (hKn hxH) _).mp ((twoResidual H).inv_mem hk)
    have e : t = k * (x * k⁻¹ * x⁻¹) := by rw [ht]; group
    rw [e]
    exact (twoResidual H).mul_mem hk h1
  have hxt : x * t * x⁻¹ = t⁻¹ := conj_commutator_of_mul_self s.x2
  obtain ⟨a, b, htab, ha, hb, ⟨m, hm⟩, hbo⟩ := exists_two_part_odd_part t
  have hzpK : Subgroup.zpowers t ≤ twoResidual H := Subgroup.zpowers_le.2 htK
  have haQ : a ∈ pCoreOf 2 H := s.two_mem (hzpK ha) hm
  have hxb : x * b * x⁻¹ = b⁻¹ := conj_eq_inv_of_mem_zpowers hxt hb
  obtain ⟨j, hj⟩ := hbo
  set i := b ^ (j + 1) with hi
  have hi2 : i * i = b := by
    rw [hi, ← pow_add, show j + 1 + (j + 1) = orderOf b + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hib : i ∈ Subgroup.zpowers b := Subgroup.npow_mem_zpowers b _
  have hxi : x * i * x⁻¹ = i⁻¹ := conj_eq_inv_of_mem_zpowers hxb hib
  have hiK : i ∈ twoResidual H := hzpK (Subgroup.zpowers_le.2 hb hib)
  have hiodd : Odd (orderOf i) := Odd.of_dvd_nat ⟨j, hj⟩ (orderOf_dvd_of_mem_zpowers hib)
  refine ⟨i, i⁻¹ * k, by group, (twoResidual H).mul_mem ((twoResidual H).inv_mem hiK) hk,
    ⟨H.mul_mem (H.inv_mem (hKH hiK)) (hKH hk), ?_⟩, hiK, ?_⟩
  ·
    have e : i⁻¹ * k * x * (i⁻¹ * k)⁻¹ * x⁻¹ = i⁻¹ * t * (x * i * x⁻¹) := by
      rw [ht]
      group
    rw [e, hxi, htab, ← hi2]
    have e2 : i⁻¹ * (i * i * a) * i⁻¹ = i * a * i⁻¹ := by group
    rw [e2]
    exact (Subgroup.mem_normalizer_iff.mp (s.QN (hKH hiK)) a).mp haQ
  · by_cases hi1 : i = 1
    · exact Or.inl hi1
    · exact Or.inr ⟨hKH hiK, hiodd, hi1, hxi⟩

theorem conj_U (s : Setting17 H T M V U x z) {g : G} (hg : g ∈ H) :
    cjSub g U = cjSub g V ⊓ pCoreOf 2 H := by
  rw [s.U_eq, cjSub_inf, cjSub_eq_of_mem_normalizer (s.QN hg)]

theorem conjV (s : Setting17 H T M V U x z) {k : G} (hk : k ∈ twoResidual H) :
    ∃ i : G, (i = 1 ∨ IsInv H x i) ∧ cjSub k V = cjSub i V := by
  obtain ⟨i, c, rfl, hcK, hcN, -, hi⟩ := s.decomp hk
  exact ⟨i, hi, by rw [cjSub_mul, cjSub_eq_of_mem_normalizer (s.normalizes hcK hcN)]⟩

theorem Z0_card (s : Setting17 H T M V U x z) : Nat.card (Z0 H V) = 2 := by
  rw [← s.Zeq]
  exact s.Z2

theorem inf_inv (s : Setting17 H T M V U x z) {i : G} (hi : IsInv H x i) :
    V ⊓ cjSub i V = Z0 H V := (s.inv hi).2.2.2

theorem conj_ne (s : Setting17 H T M V U x z) {i : G} (hi : IsInv H x i) : cjSub i V ≠ V := by
  intro h
  have h1 := s.inf_inv hi
  rw [h, inf_idem] at h1
  have h2 := s.Z0_card
  rw [← h1, s.V16] at h2
  norm_num at h2

theorem inf_eq (s : Setting17 H T M V U x z) {k : G} (hk : k ∈ twoResidual H) :
    cjSub k V = V ∨ V ⊓ cjSub k V = Z0 H V := by
  obtain ⟨i, hi | hi, hki⟩ := s.conjV hk
  · left
    rw [hki, hi, cjSub_one]
  · right
    rw [hki]
    exact s.inf_inv hi

theorem inv_centralizes (s : Setting17 H T M V U x z) {i : G} (hi : IsInv H x i) {ζ : G}
    (hζ : ζ ∈ Z0 H V) : i * ζ * i⁻¹ = ζ := by
  have d := s.dpw hi
  rw [← s.inf_inv hi] at hζ
  rw [d.ZC ζ hζ i d.zI]
  group

theorem normalizer_centralizer (s : Setting17 H T M V U x z) {g : G} (hg : g ∈ H) :
    g ∈ Subgroup.normalizer
      ((Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_cjSub_eq, cjSub_centralizer, cjSub_eq_of_mem_normalizer (s.QN hg)]

theorem le_center (s : Setting17 H T M V U x z) {g : G} (hg : g ∈ H) {ζ : G}
    (hζ : ζ ∈ Z0 H V) : g * ζ * g⁻¹ = ζ := by
  have hT : T ≤ Subgroup.normalizer (Z0 H V : Set G) :=
    B2F.le_normalizer_inf s.dp.TV fun t ht => s.normalizer_centralizer (s.dp.TH ht)
  have hK : twoResidual H ≤ Subgroup.normalizer (Z0 H V : Set G) := by
    intro k hk
    rw [mem_normalizer_iff_cjSub_eq]
    obtain ⟨i, hi, hki⟩ := s.conjV hk
    have hc : cjSub k (Subgroup.centralizer (pCoreOf 2 H : Set G)) =
        Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      cjSub_eq_of_mem_normalizer (s.normalizer_centralizer (twoResidual_le H hk))
    rw [cjSub_inf, hki, hc]
    rcases hi with rfl | hi
    · rw [cjSub_one]
    · have hiH := hi.1
      have hc' : cjSub i (Subgroup.centralizer (pCoreOf 2 H : Set G)) =
          Subgroup.centralizer (pCoreOf 2 H : Set G) :=
        cjSub_eq_of_mem_normalizer (s.normalizer_centralizer hiH)
      rw [← hc', ← cjSub_inf]
      apply cjSub_eq_of_mem_normalizer
      exact B6.mem_normalizer_of_forall_mem (fun ζ hζ => by rw [s.inv_centralizes hi hζ]; exact hζ)
        (fun ζ hζ => by
          have h1 := s.inv_centralizes hi hζ
          have : i⁻¹ * ζ * i = ζ := by
            calc i⁻¹ * ζ * i = i⁻¹ * (i * ζ * i⁻¹) * i := by rw [h1]
              _ = ζ := by group
          rw [this]
          exact hζ)
  have hH : H ≤ Subgroup.normalizer (Z0 H V : Set G) :=
    (sup_twoResidual_eq s.mp.isSylow).symm.le.trans (sup_le hT hK)
  exact conj_eq_of_card_eq_two s.Z0_card (fun a ha => s.dp.elem.2 a ha.1) (hH hg) hζ

theorem comm_mem (s : Setting17 H T M V U x z) {k l : G} (hk : k ∈ twoResidual H)
    (hl : l ∈ twoResidual H) {a b : G} (ha : a ∈ cjSub k U) (hb : b ∈ cjSub l U) :
    a * b * a⁻¹ * b⁻¹ ∈ Z0 H V := by
  have hKH : twoResidual H ≤ H := twoResidual_le H
  rw [mem_cjSub] at ha hb
  set a' := k⁻¹ * a * k with ha'
  set g := k⁻¹ * l with hg
  have hgK : g ∈ twoResidual H := (twoResidual H).mul_mem ((twoResidual H).inv_mem hk) hl
  have hb' : k⁻¹ * b * k ∈ cjSub g U := by
    rw [mem_cjSub, hg]
    have e : (k⁻¹ * l)⁻¹ * (k⁻¹ * b * k) * (k⁻¹ * l) = l⁻¹ * b * l := by group
    rw [e]
    exact hb
  obtain ⟨i, hi, hgi⟩ := s.conjV hgK
  have hUg : cjSub g U = cjSub i U := by
    rcases hi with rfl | hi
    · rw [s.conj_U (hKH hgK), hgi, cjSub_one, cjSub_one, ← s.U_eq]
    · rw [s.conj_U (hKH hgK), s.conj_U hi.1, hgi]
  rw [hUg] at hb'
  have hc : a' * (k⁻¹ * b * k) * a'⁻¹ * (k⁻¹ * b * k)⁻¹ ∈ Z0 H V := by
    rcases hi with rfl | hi
    · rw [cjSub_one] at hb'
      rw [isElemAbelian_comm (isElemAbelian_mono s.dp.UV s.dp.elem) ha hb']
      have : (k⁻¹ * b * k) * a' * a'⁻¹ * (k⁻¹ * b * k)⁻¹ = 1 := by group
      rw [this]
      exact (Z0 H V).one_mem
    · have d := s.dpw hi
      rw [← d.Aeq] at hb'
      have := Subgroup.commutator_mem_commutator ha hb'
      rw [commutatorElement_def] at this
      have h2 := d.comm2 this
      have h3 : dpZ V i = Z0 H V := s.inf_inv hi
      rwa [h3] at h2
  have e : a * b * a⁻¹ * b⁻¹ = k * (a' * (k⁻¹ * b * k) * a'⁻¹ * (k⁻¹ * b * k)⁻¹) * k⁻¹ := by
    rw [ha']
    group
  rw [e, s.le_center (hKH hk) hc]
  exact hc

end Setting17

end E2

end CFSG.Quasithin
