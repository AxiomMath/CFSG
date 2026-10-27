module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113J1ZK
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5S
public import CFSG.Quasithin.H13.A5OutAlt67
public import CFSG.Quasithin.EmptyFaithfulMultiple.L3213Basic
public import CFSG.CGT.PushingUpLit.CGT6.Diag.S2Transfer

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem factHatA7SylowThree_holds :
    ∀ (X : Type) [Group X] [Finite X], IsHat X (alternatingGroup (Fin 7)) →
      ∀ P : Subgroup X, Nat.card P = 27 → ∃ a ∈ P, ∃ c ∈ P, a * c ≠ c * a := by
  intro X _ _ hX P hP
  by_contra hcomm
  push Not at hcomm
  have : IsMulCommutative ↥P := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  obtain ⟨e⟩ := hX.2.2
  have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hX7 : Nat.card X = 7560 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
      Nat.card_congr e.toEquiv, hA7, hX.2.1]
  have hidx : P.index = 280 := by
    have h1 := P.card_mul_index
    rw [hP, hX7] at h1
    omega
  have hZne : Subgroup.center X ≠ ⊥ := fun h => by
    have h1 := hX.2.1
    rw [h, Subgroup.card_bot] at h1
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzo : orderOf z ∣ 3 := by
    have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center X))
    rwa [hX.2.1, Subgroup.orderOf_mk] at h1
  have hcop : Nat.Coprime (orderOf z) P.index := by
    rw [hidx]
    exact Nat.Coprime.coprime_dvd_left hzo (by norm_num)
  exact hz1' (CFSG.CGT.PushingUpLit.CGT6.Diag.S2.central_eq_one_of_abelian_index
    hX.1.1.commutator_eq_top hz hcop)

section Elem

variable {G : Type*} [Group G]

theorem conj_eq_of_pow_three_of_mem_zpowers {b x : G} (hb : b ^ 3 = 1) (hx : x ^ 3 = 1)
    (hbx : b * x * b⁻¹ ∈ Subgroup.zpowers x) : b * x * b⁻¹ = x := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hbx
  have hj0 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
  have hj3 : j % 3 < 3 := Int.emod_lt_of_pos j (by norm_num)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, j % 3 = (r : ℤ) := ⟨(j % 3).toNat, (Int.toNat_of_nonneg hj0).symm⟩
  have hr3 : r < 3 := by omega
  have hjr : MulAut.conj b x = x ^ r := by
    rw [MulAut.conj_apply, ← hj, zpow_eq_zpow_emod' j hx, Nat.cast_ofNat, hr, zpow_natCast]
  have h3 : x = x ^ (r * (r * r)) := by
    have e : MulAut.conj b (MulAut.conj b (MulAut.conj b x)) = x ^ (r * (r * r)) := by
      rw [hjr, map_pow, hjr, ← pow_mul, map_pow, hjr, ← pow_mul]
    have e' : MulAut.conj b (MulAut.conj b (MulAut.conj b x)) = x := by
      simp only [MulAut.conj_apply]
      calc b * (b * (b * x * b⁻¹) * b⁻¹) * b⁻¹ = b * b * b * x * (b * b * b)⁻¹ := by group
        _ = x := by rw [← pow_three', hb, one_mul, inv_one, mul_one]
    rw [e'] at e
    exact e
  rw [← MulAut.conj_apply, hjr]
  interval_cases r
  · rw [pow_zero]
    simp only [mul_zero, pow_zero] at h3
    exact h3.symm
  · exact pow_one x
  · have h8 : x ^ (2 * (2 * 2)) = x ^ 2 := by
      rw [show 2 * (2 * 2) = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hx, one_pow, one_mul]
    rw [h8] at h3
    have h1 : x = 1 := by
      have h2 : x * x = x * 1 := by rw [mul_one, ← pow_two, ← h3]
      exact mul_left_cancel h2
    rw [h1, one_pow]

end Elem

theorem mem_zpowers_sup_center_of_commute {X : Type} [Group X] [Finite X]
    (hX : IsHat X (alternatingGroup (Fin 7))) {b l : X} (hbl : b * l = l * b)
    (hb3 : b ^ 3 = 1) (hl3 : l ^ 3 ∈ Subgroup.center X) (hbZ : b ∉ Subgroup.center X) :
    l ∈ Subgroup.zpowers b ⊔ Subgroup.center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hl
  have hz3 : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := fun z hz => by
    have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center X))
    rw [hX.2.1, Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hZc : ∀ z ∈ Subgroup.center X, ∀ y : X, z * y = y * z := fun z hz y =>
    (Subgroup.mem_center_iff.mp hz y).symm
  have hcs : ∀ x ∈ ({b, l} ∪ (Subgroup.center X : Set X) : Set X),
      ∀ y ∈ ({b, l} ∪ (Subgroup.center X : Set X) : Set X), x * y = y * x := by
    rintro x ((rfl | rfl) | hx) y ((rfl | rfl) | hy)
    · rfl
    · exact hbl
    · exact (hZc y hy _).symm
    · exact hbl.symm
    · rfl
    · exact (hZc y hy _).symm
    · exact hZc x hx _
    · exact hZc x hx _
    · exact hZc x hx _
  set A := Subgroup.closure ({b, l} ∪ (Subgroup.center X : Set X)) with hA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    have hAc : A ≤ Subgroup.centralizer ({b, l} ∪ (Subgroup.center X : Set X)) := by
      rw [hA, Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcs y hy x hx
    intro x hx y hy
    have hx' : x ∈ Subgroup.centralizer (A : Set X) := by
      rw [hA, Subgroup.centralizer_closure]
      exact hAc hx
    exact (Subgroup.mem_centralizer_iff.mp hx' y hy).symm
  have h9 : ∀ x ∈ A, x ^ 9 = 1 := by
    intro x hx
    rw [hA] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with (rfl | rfl) | hx
      · rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hb3, one_pow]
      · rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hz3 _ hl3]
      · rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hz3 _ hx, one_pow]
    | one => exact one_pow 9
    | mul x y hx hy ihx ihy =>
      rw [Commute.mul_pow (hcomm x hx y hy), ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hP : IsPGroup 3 ↥A := fun g => ⟨2, Subtype.ext (by simpa using h9 g g.2)⟩
  have hbA : b ∈ A := Subgroup.subset_closure (Or.inl (Or.inl rfl))
  have hlA : l ∈ A := Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have hZA : Subgroup.center X ≤ A := fun z hz => Subgroup.subset_closure (Or.inr hz)
  have hA₁A : Subgroup.zpowers b ⊔ Subgroup.center X ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hbA) hZA
  have h1 : 3 * Nat.card (Subgroup.center X) ≤
      Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.center X) :=
    EmptyFaithfulMultiple.L3213.mul_card_le_card_of_lt (hP.to_le hA₁A)
      (lt_of_le_of_ne le_sup_right fun h =>
        hbZ (by rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)))
  have h2 : 3 * Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.center X) ≤ Nat.card A :=
    EmptyFaithfulMultiple.L3213.mul_card_le_card_of_lt hP
      (lt_of_le_of_ne hA₁A fun h => hl (by rw [h]; exact hlA))
  rw [hX.2.1] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
  have hk3 : 3 ≤ k := by
    by_contra hk3
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨P, hP27⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 3)
    (by rw [hk]; exact pow_dvd_pow 3 hk3 : 3 ^ 3 ∣ Nat.card ↥A)
  have hP' : Nat.card ↥(P.map A.subtype) = 27 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hP27]
    norm_num
  obtain ⟨a, ha, c, hc, hac⟩ := factHatA7SylowThree_holds X hX _ hP'
  obtain ⟨a', -, rfl⟩ := ha
  obtain ⟨c', -, rfl⟩ := hc
  exact hac (hcomm _ a'.2 _ c'.2)

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem pow_three_eq_one_of_inv (h : Hyp5_0_1 G T M L n) {D X : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) (hTX : T ≤ X) (hOT : pCoreOf 2 X ≤ T)
    {Q : Subgroup (O2Q X)} [Q.Normal] {x t : G} (hxD : x ∈ D) (hxX : x ∈ X) {a : ℕ}
    (hxa : x ^ 3 ^ a = 1) (ht : t ∈ T)
    (htQ : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨t, hTX ht⟩ ∈ Q)
    (hx3 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hxX⟩ ^ 3 ∈
      Subgroup.centralizer (Q : Set (O2Q X)))
    (hxC : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hxX⟩ ∉
      Subgroup.centralizer (Q : Set (O2Q X)))
    (hinv : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨t, hTX ht⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hxX⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨t, hTX ht⟩)⁻¹ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hxX⟩ ∈ Subgroup.centralizer (Q : Set (O2Q X))) :
    x ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  set C := Subgroup.centralizer (Q : Set (O2Q X)) with hC
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hxN : x ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (hD.1.trans inf_le_right) hxD
  have hEN : t ∈ Subgroup.normalizer (((T ⊓ L) ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_isCyclic (inf_le_borel T L) inf_le_right (h.borelL_eq_sup hD)
      (h.isCyclic_card_of_isHall l2TorusFact hD).1 (Subgroup.zpowers_le.mpr hxD)
      (h.T_le_normalizer_borel ht) (h.T_le_normalizer_inf ht)
  obtain ⟨p, hp, e, he, hpe⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (Subgroup.zpowers_le.mpr hxN)).mp
      ((Subgroup.mem_normalizer_iff.mp hEN x).mp (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  obtain ⟨ε, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  have hpX : p ∈ X := hTX hp.1
  have hpeX : (⟨t, hTX ht⟩ : ↥X) * ⟨x, hxX⟩ * (⟨t, hTX ht⟩ : ↥X)⁻¹ =
      ⟨p, hpX⟩ * (⟨x, hxX⟩ : ↥X) ^ ε := Subtype.ext (by simpa using hpe)
  have hbar : π ⟨t, hTX ht⟩ * π ⟨x, hxX⟩ * (π ⟨t, hTX ht⟩)⁻¹ = π ⟨p, hpX⟩ * π ⟨x, hxX⟩ ^ ε := by
    rw [← map_inv, ← map_mul, ← map_mul, hpeX, map_mul, map_zpow]
  rw [hbar, mul_assoc, ← zpow_add_one] at hinv
  set ψ := QuotientGroup.mk' C with hψ
  have hψ1 : ψ (π ⟨p, hpX⟩) * ψ (π ⟨x, hxX⟩) ^ (ε + 1) = 1 := by
    rw [← map_zpow, ← map_mul, hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hinv
  have hu3 : ψ (π ⟨x, hxX⟩) ^ 3 = 1 := by
    rw [← map_pow, hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx3
  have hu1 : ψ (π ⟨x, hxX⟩) ≠ 1 := fun h1 => hxC (by
    rw [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1)
  have hou : orderOf (ψ (π ⟨x, hxX⟩)) = 3 := orderOf_eq_prime hu3 hu1
  obtain ⟨k, hk⟩ := hT2 ⟨p, hp.1⟩
  have hp2 : ψ (π ⟨p, hpX⟩) ^ 2 ^ k = 1 := by
    have h1 : (⟨p, hpX⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  have hw : ψ (π ⟨x, hxX⟩) ^ (ε + 1) = 1 := by
    have hwv : ψ (π ⟨x, hxX⟩) ^ (ε + 1) = (ψ (π ⟨p, hpX⟩))⁻¹ := eq_inv_of_mul_eq_one_right hψ1
    have hw3 : (ψ (π ⟨x, hxX⟩) ^ (ε + 1)) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]
    have hw2 : (ψ (π ⟨x, hxX⟩) ^ (ε + 1)) ^ 2 ^ k = 1 := by
      rw [hwv, inv_pow, hp2, inv_one]
    have hdvd : orderOf (ψ (π ⟨x, hxX⟩) ^ (ε + 1)) ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw3) (orderOf_dvd_of_pow_eq_one hw2)
    rw [Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2), Nat.dvd_one,
      orderOf_eq_one_iff] at hdvd
    exact hdvd
  have h3ε : (3 : ℤ) ∣ ε + 1 := by
    have h1 := orderOf_dvd_iff_zpow_eq_one.mpr hw
    rwa [hou, Nat.cast_ofNat] at h1
  obtain ⟨p', hp', hpe'⟩ :=
    CFSG.LieType.Chevalley.exists_mul_pow_eq_mul_pow hp (Subgroup.zpow_mem _ hxN ε) 3
  have hcube : t * x ^ 3 * t⁻¹ = p' * x ^ (ε * 3) := by
    rw [← conj_pow, hpe, hpe', ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat]
  have hcomm := Subgroup.mem_centralizer_iff.mp hx3 _ htQ
  have ho : t * x ^ 3 * t⁻¹ * (x ^ 3)⁻¹ ∈ T := by
    have hoX : t * x ^ 3 * t⁻¹ * (x ^ 3)⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem (hTX ht) (X.pow_mem hxX 3)) (X.inv_mem (hTX ht)))
        (X.inv_mem (X.pow_mem hxX 3))
    have h1 : π ⟨t * x ^ 3 * t⁻¹ * (x ^ 3)⁻¹, hoX⟩ = 1 := by
      have e : (⟨t * x ^ 3 * t⁻¹ * (x ^ 3)⁻¹, hoX⟩ : ↥X) =
          ⟨t, hTX ht⟩ * (⟨x, hxX⟩ : ↥X) ^ 3 * (⟨t, hTX ht⟩ : ↥X)⁻¹ *
            ((⟨x, hxX⟩ : ↥X) ^ 3)⁻¹ := Subtype.ext (by simp)
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, hcomm]
      group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    refine hOT ?_
    rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
    exact ⟨_, h1, rfl⟩
  have hT : x ^ (ε * 3 - 3) ∈ T := by
    have e : x ^ (ε * 3 - 3) = p'⁻¹ * (t * x ^ 3 * t⁻¹ * (x ^ 3)⁻¹) := by
      rw [hcube, zpow_sub, ← zpow_natCast x 3, Nat.cast_ofNat]
      group
    rw [e]
    exact T.mul_mem (T.inv_mem hp'.1) ho
  have h1 : x ^ (ε * 3 - 3) = 1 := by
    refine eq_one_of_mem_of_pow_odd (r := 3 ^ a) hT2 hT (Odd.pow (by decide : Odd 3)) ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxa, one_zpow]
  have hy1 : (x ^ 3) ^ (ε - 1) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, Nat.cast_ofNat, show (3 : ℤ) * (ε - 1) = ε * 3 - 3 by ring]
    exact h1
  have hy3 : (x ^ 3) ^ 3 ^ a = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hxa, one_pow]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy3)
  have hjd : ((3 ^ j : ℕ) : ℤ) ∣ ε - 1 := by
    rw [← hj]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hy1
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hj
  · exfalso
    have h3 : (3 : ℤ) ∣ ε - 1 := by
      refine dvd_trans ?_ hjd
      push_cast
      exact dvd_pow_self 3 (Nat.succ_ne_zero j)
    omega

end Hyp5_0_1

theorem stmt5_1_13_type_hat7_of (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h510 : Stmt5_1_10) (hTe : FactType513Three) :
    Stmt5_1_13_type_hat7 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hcl hexp hhat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hHX : H ≤ X := m.inH.1
  have hTX : T ≤ X := hTH.1.trans hHX
  have hTXs : IsSylowTwoOf T X := h.isSylowTwoOf hTX
  have hOT : pCoreOf 2 X ≤ T := F7.isSylowTwoOf_pCoreOf_le hTXs
  have hKX : oTwoUpper H ≤ X := (oTwoUpper_le H).trans hHX
  have hL24 := hc5.1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam m.hyp m.nota
  have heq : K₁ = oTwoUpper H :=
    (m.toEmb512 hk).eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hL24)
  obtain ⟨hst, hnot⟩ := m.star513 h37 h38 h510 heq hcl hL24
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  set Q := modO2Image X Kh₁ with hQ
  set R := modO2Image X (oTwoUpper H) with hR
  set C := Subgroup.centralizer (Q : Set (O2Q X)) with hC
  have hCN : C ≤ Subgroup.normalizer (R : Set (O2Q X)) :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hst.R_le)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hXN : X ≤ Subgroup.normalizer (Kh₁ : Set G) := by
    have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 m.inH.2 hTXs m.hat.1
    rwa [hcl] at this
  have hQN : ∀ g : O2Q X, g ∈ Subgroup.normalizer (Q : Set (O2Q X)) := by
    intro g
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) g
    exact o2Map_mem_normalizer (hXN x'.2)
  have : Q.Normal := ⟨fun q hq g => (Subgroup.mem_normalizer_iff.mp (hQN g) q).mp hq⟩
  obtain ⟨eH⟩ := modO2_mulEquiv m.hat.1
  have hQh : IsHat ↥Q (alternatingGroup (Fin 7)) := IsHat.of_mulEquiv eH hhat
  have hexp' : ∀ d ∈ modO2Image X (D ⊓ X), d ^ 3 ∈ C := hexp
  obtain ⟨-, -, tb, htb, hinv⟩ := hTe (O2Q X) _ _ _ _ _ hst (Or.inr (Or.inl hQh))
    (fun d hd => ⟨1, by rw [pow_one]; exact hexp' d hd⟩) hnot
  obtain ⟨⟨t, htX⟩, ht, rfl⟩ := htb.1
  have htT : t ∈ T := Subgroup.mem_subgroupOf.mp ht
  obtain ⟨-, -, hBorel, hHall, -⟩ := h510 G T M L H B D n m.hyp m.nota
  rw [m.hyp.borel_eq hBorel] at hHall
  have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hB3 : Nat.card B = 3 := by
    have := (isCyclic_card_of_isHall_borelOf le_rfl hc5.1 hTK hHall).2
    norm_num at this
    exact this
  have hBne : B ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hB3
    omega
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  have hb3 : b ^ 3 = 1 := by
    have := orderOf_dvd_natCard (⟨b, hbB⟩ : ↥B)
    rw [hB3, Subgroup.orderOf_mk] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hbK : b ∈ oTwoUpper H := (hHall.1 hbB).1
  have hbX : b ∈ X := hKX hbK
  set bb := π ⟨b, hbX⟩ with hbbdef
  have hbbR : bb ∈ R := ⟨⟨b, hbX⟩, Subgroup.mem_subgroupOf.mpr hbK, rfl⟩
  have hbbQ : bb ∈ Q := hst.R_le hbbR
  have hbbB : bb ∈ modO2Image X B := ⟨⟨b, hbX⟩, Subgroup.mem_subgroupOf.mpr hbB, rfl⟩
  have hb3' : (⟨b, hbX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hbb3 : bb ^ 3 = 1 := by
    rw [hbbdef, ← map_pow, hb3', map_one]
  have hbb1 : bb ≠ 1 := by
    intro h1
    apply hb1'
    rw [hbbdef, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h3 := eq_one_of_mem_of_pow_odd (CFSG.pCore_isPGroup (p := 2) (G := ↥X)) h1
      (by decide : Odd 3) hb3'
    exact congrArg Subtype.val h3
  have hbbC : bb ∉ C := by
    intro hbc
    have : IsSimpleGroup (ModO2 R) := isSimpleGroup_of_lieModel_PSL2 hst.R_type
    have : Group.IsPerfect ↥R := Subgroup.isPerfect_iff.mpr hst.R_perfect
    have : Group.IsPerfect (ModO2 R) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥R))
    have hZR : Subgroup.center (ModO2 R) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ModO2 R)) with h1 | h1
      · exact h1
      · exact absurd (Subgroup.center_eq_top_iff.mp h1)
          (Group.IsPerfect.not_isMulCommutative (ModO2 R))
    have hbR : (⟨bb, hbbR⟩ : ↥R) ∈ Subgroup.center ↥R := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hbc g (hst.R_le g.2))
    have h1 := Subgroup.map_center_le_center (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥R))
      ⟨_, hbR, rfl⟩
    rw [hZR, Subgroup.mem_bot] at h1
    have h1' := (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥R) (⟨bb, hbbR⟩ : ↥R)).mp h1
    have hbR3 : (⟨bb, hbbR⟩ : ↥R) ^ 3 = 1 := Subtype.ext (by simpa using hbb3)
    have h2 := eq_one_of_mem_of_pow_odd (CFSG.pCore_isPGroup (p := 2) (G := ↥R)) h1'
      (by decide : Odd 3) hbR3
    exact hbb1 (congrArg Subtype.val h2)
  have hcen : ∀ z ∈ Subgroup.center ↥Q, (z : O2Q X) ∈ C := fun z hz => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  obtain ⟨y, hy, hyN⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨⟨d, hdX⟩, hd, rfl⟩ := hy
  have hd' : d ∈ D ⊓ X := Subgroup.mem_subgroupOf.mp hd
  have ho : orderOf d ≠ 0 := (isOfFinOrder_of_finite d).orderOf_pos.ne'
  set s := 3 ^ (orderOf d).factorization 3 with hs
  set r := orderOf d / s with hr
  have hsr : Nat.Coprime s r := Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_three ho)
  have h3r : Nat.Coprime 3 r := Nat.coprime_ordCompl Nat.prime_three ho
  have hsr1 : d ^ (s * r) = 1 := by
    rw [hs, hr, Nat.ordProj_mul_ordCompl_eq_self, pow_orderOf_eq_one]
  have hdb : π ⟨d, hdX⟩ ∈ modO2Image X (D ⊓ X) := ⟨⟨d, hdX⟩, hd, rfl⟩
  have hwC : π ⟨d, hdX⟩ ^ s ∈ C := by
    refine E1.mem_of_pow_mem_of_coprime h3r (hexp' _ ((modO2Image X (D ⊓ X)).pow_mem hdb s)) ?_
    have e : (⟨d, hdX⟩ : ↥X) ^ (s * r) = 1 := Subtype.ext (by simpa using hsr1)
    rw [← pow_mul, ← map_pow, e, map_one]
    exact C.one_mem
  have hclaim : π ⟨d, hdX⟩ ^ r ∈ Subgroup.normalizer (R : Set (O2Q X)) := by
    by_contra hxN
    have hxX : d ^ r ∈ X := X.pow_mem hdX r
    have hxD : d ^ r ∈ D := D.pow_mem hd'.1 r
    have hxb : π ⟨d ^ r, hxX⟩ = π ⟨d, hdX⟩ ^ r := by
      rw [← map_pow]
      rfl
    have hxa : (d ^ r) ^ 3 ^ (orderOf d).factorization 3 = 1 := by
      rw [← pow_mul, mul_comm, ← hs]
      exact hsr1
    have hxbD : π ⟨d ^ r, hxX⟩ ∈ modO2Image X (D ⊓ X) :=
      ⟨⟨d ^ r, hxX⟩, Subgroup.mem_subgroupOf.mpr ⟨hxD, hxX⟩, rfl⟩
    have hxC : π ⟨d ^ r, hxX⟩ ∉ C := fun hc => hxN (hxb ▸ hCN hc)
    have hx3 : (d ^ r) ^ 3 = 1 := h.pow_three_eq_one_of_inv m.nota.2.1 hTX hOT hxD hxX hxa htT
      htb.2 (hexp' _ hxbD) hxC (hinv _ hxbD)
    set xb := π ⟨d ^ r, hxX⟩ with hxbdef
    have hxb3 : xb ^ 3 = 1 := by
      have e : (⟨d ^ r, hxX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [hxbdef, ← map_pow, e, map_one]
    have hbx : bb * xb * bb⁻¹ = xb := by
      refine conj_eq_of_pow_three_of_mem_zpowers hbb3 hxb3 ?_
      have hbN : bb ∈ Subgroup.normalizer (Subgroup.zpowers xb : Set (O2Q X)) :=
        mem_normalizer_of_le_isCyclic hst.D_cyclic (Subgroup.zpowers_le.mpr hxbD)
          (hst.B_le_D hbbB)
      exact (Subgroup.mem_normalizer_iff.mp hbN xb).mp (Subgroup.mem_zpowers xb)
    obtain ⟨φ⟩ := hQh.2.2
    have hodd : Odd (orderOf xb) :=
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hxb3)
    obtain ⟨l, hlQ, hl⟩ := A5.exists_conj_of_odd hQh.1.1 (Or.inr rfl) φ (hQN xb) hodd
    set c := l⁻¹ * xb with hcdef
    have hcC : c ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      calc y * (l⁻¹ * xb) = l⁻¹ * (l * y * l⁻¹) * xb := by group
        _ = l⁻¹ * (xb * y * xb⁻¹) * xb := by rw [hl y hy]
        _ = l⁻¹ * xb * y := by group
    have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hcC l hlQ
    have hxc : xb = l * c := by
      rw [hcdef]
      group
    have hcx : Commute xb c⁻¹ := by
      refine Commute.inv_right ?_
      show xb * c = c * xb
      rw [hxc, ← mul_assoc c l c, ← hlc]
    have hl3 : l ^ 3 ∈ C := by
      have e : l = xb * c⁻¹ := by
        rw [hcdef]
        group
      rw [e, hcx.mul_pow, hxb3, one_mul]
      exact C.pow_mem (C.inv_mem hcC) 3
    have hbl : bb * l = l * bb := by
      have h1 := hl bb hbbQ
      have hxbb : xb * bb = bb * xb := by
        calc xb * bb = bb * xb * bb⁻¹ * bb := by rw [hbx]
          _ = bb * xb := by group
      have h2 : xb * bb * xb⁻¹ = bb := by
        rw [hxbb]
        group
      have h3 : l * bb * l⁻¹ = bb := h1.symm.trans h2
      calc bb * l = l * bb * l⁻¹ * l := by rw [h3]
        _ = l * bb := by group
    have hmem := mem_zpowers_sup_center_of_commute hQh (b := ⟨bb, hbbQ⟩) (l := ⟨l, hlQ⟩)
      (Subtype.ext hbl) (Subtype.ext (by simpa using hbb3))
      (by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (by simpa using Subgroup.mem_centralizer_iff.mp hl3 g g.2))
      (fun hz => hbbC (hcen _ hz))
    have hle : Subgroup.zpowers (⟨bb, hbbQ⟩ : ↥Q) ⊔ Subgroup.center ↥Q ≤
        (Subgroup.normalizer (R : Set (O2Q X))).subgroupOf Q := by
      refine sup_le ?_ fun z hz => ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
        exact Subgroup.le_normalizer hbbR
      · rw [Subgroup.mem_subgroupOf]
        exact hCN (hcen z hz)
    have hlN : l ∈ Subgroup.normalizer (R : Set (O2Q X)) := Subgroup.mem_subgroupOf.mp (hle hmem)
    apply hxN
    rw [← hxb, hxc]
    exact Subgroup.mul_mem _ hlN (hCN hcC)
  exact hyN (E1.mem_of_pow_mem_of_coprime hsr.symm hclaim (hCN hwC))

end CFSG.Quasithin.H13
