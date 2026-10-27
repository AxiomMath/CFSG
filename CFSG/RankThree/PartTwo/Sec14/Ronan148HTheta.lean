module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HA6Cent

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped Pointwise

section Gen

variable {G : Type} [Group G] [Finite G]

theorem isElementaryAbelian_of_isE27 {P : Subgroup G} (hP : Late.IsE27 P) :
    CFSG.IsElementaryAbelian 3 P :=
  { toIsMulCommutative := hP.1.1
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using hP.1.2 x x.2) }

theorem le_of_forall_inf_centralizer_hyperplane_three {E V W : Subgroup G}
    (hE : CFSG.IsElementaryAbelian 3 E) (hEn : Nontrivial E) (hpV : ¬ 3 ∣ Nat.card V)
    (hEV : E ≤ Subgroup.normalizer (V : Set G))
    (hle : ∀ B : Subgroup G, B ≤ E → B.relIndex E = 3 →
      V ⊓ Subgroup.centralizer (B : Set G) ≤ W) : V ≤ W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : MulDistribMulAction E V := Subgroup.conjMulDistribMulActionOfLeNormalizer E V hEV
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 3) (A := E) (H := V) hpV
  have hle' : (⨆ (B : Subgroup E) (_ : B.index = 3), CFSG.fixedPointSubgroup B V) ≤
      W.comap V.subtype := by
    refine iSup₂_le fun B hB x hx => ?_
    rw [Subgroup.mem_comap]
    have hcomm : ∀ b : B, ((b : E) : G) * (x : G) * ((b : E) : G)⁻¹ = x := fun b =>
      congrArg Subtype.val (hx b)
    refine hle (B.map E.subtype) (Subgroup.map_subtype_le B) ?_
      (Subgroup.mem_inf.mpr ⟨x.2, ?_⟩)
    · rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
      exact hB
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hyB, rfl⟩
      have h1 := hcomm ⟨y, hyB⟩
      change ((y : E) : G) * (x : G) = (x : G) * ((y : E) : G)
      calc ((y : E) : G) * (x : G) = (((y : E) : G) * x * ((y : E) : G)⁻¹) * ((y : E) : G) := by
            group
        _ = (x : G) * ((y : E) : G) := by rw [h1]
  intro x hx
  have hmem : (⟨x, hx⟩ : V) ∈
      (⨆ (B : Subgroup E) (_ : B.index = 3), CFSG.fixedPointSubgroup B V) := by
    rw [hgen]
    exact Subgroup.mem_top _
  exact hle' hmem

theorem commute_of_mem_zpowers_five {t w : G} (ht : orderOf t = 5) (hw : w ^ 3 = 1)
    (hwt : w * t * w⁻¹ ∈ Subgroup.zpowers t) : w * t = t * w := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwt
  have hconj : ∀ j : ℕ, w ^ j * t * (w ^ j)⁻¹ = t ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc w ^ (j + 1) * t * (w ^ (j + 1))⁻¹ = w * (w ^ j * t * (w ^ j)⁻¹) * w⁻¹ := by group
        _ = w * t ^ (k ^ j) * w⁻¹ := by rw [ih]
        _ = (w * t * w⁻¹) ^ (k ^ j) := by rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
        _ = t ^ (k ^ (j + 1)) := by rw [← hk, ← zpow_mul, pow_succ, mul_comm]
  have h3 := hconj 3
  rw [hw, one_mul, inv_one, mul_one] at h3
  have h5 : (5 : ℤ) ∣ k ^ 3 - 1 := by
    have : t ^ (k ^ 3 - 1) = 1 := by rw [zpow_sub, zpow_one, ← h3, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.mpr this
    rw [ht] at this
    exact_mod_cast this
  have hk1 : (5 : ℤ) ∣ k - 1 := by
    have : ∀ r : ZMod 5, r ^ 3 - 1 = 0 → r - 1 = 0 := by decide
    have h := this (k : ZMod 5) (by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr h5
      push_cast at this
      exact this)
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 5).mp (by push_cast; exact h)
    exact this
  have htk : t ^ k = t := by
    obtain ⟨m, hm⟩ := hk1
    have : k = 1 + 5 * m := by omega
    rw [this, zpow_add, zpow_one, zpow_mul]
    rw [show t ^ (5 : ℤ) = 1 by
      rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast, ← ht, pow_orderOf_eq_one],
      one_zpow, mul_one]
  have : w * t * w⁻¹ = t := by rw [← hk, htk]
  calc w * t = w * t * w⁻¹ * w := by group
    _ = t * w := by rw [this]

end Gen

section Theta

set_option linter.unusedSectionVars false


variable {X : Type} [Group X] [Finite X]

theorem inf_centralizer_eq_bot (hperf : Group.IsPerfect X)
    (hT : IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {P : Subgroup X}
    (hP : Late.IsE27 P) {a : X} (haP : a ∈ P) (haZ : a ∉ Subgroup.center X) {S : Subgroup X}
    (hPS : P ≤ Subgroup.normalizer (S : Set X)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hS : IsPGroup r S) :
    S ⊓ Subgroup.centralizer ({a} : Set X) = ⊥ := by
  obtain ⟨K, hK, hC, hI, -⟩ := exists_centralizer_eq hperf hT hP haP haZ
  have hK1080 : Nat.card K = 1080 := KFacts.KS14.card_eq_of_isExtOf_alternating_six hK
  set R := S ⊓ Subgroup.centralizer ({a} : Set X) with hR
  have ha3 : a ^ 3 = 1 := hP.1.2 a haP
  have hKa : K ≤ Subgroup.centralizer ({a} : Set X) := hC ▸ le_sup_right
  have haN : Subgroup.zpowers a ≤ Subgroup.normalizer (K : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hKa hk)
      have : a * k * a⁻¹ = k := by rw [← h1]; group
      rw [this]; exact hk
    · intro hk
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hKa hk)
      have : k = a * k * a⁻¹ := by
        calc k = a⁻¹ * ((a * k * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * k * a⁻¹)) := by rw [h1]
          _ = a * k * a⁻¹ := by group
      rw [this]; exact hk
  have hRK : R ≤ K := by
    intro x ⟨hxS, hxC⟩
    rw [hC] at hxC
    have hmul : x ∈ ((Subgroup.zpowers a : Set X) * (K : Set X)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ haN]; exact hxC
    obtain ⟨y, hy, k, hk, rfl⟩ := hmul
    obtain ⟨m, hm⟩ := hS ⟨y * k, hxS⟩
    have hm' : (y * k) ^ r ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hyk : Commute y k := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hKa hk)).symm i)
    rw [hyk.mul_pow] at hm'
    have hyr : y ^ r ^ m = 1 := by
      have h1 : y ^ r ^ m = (k ^ r ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hm'
      have h2 : y ^ r ^ m ∈ Subgroup.zpowers a ⊓ K :=
        ⟨Subgroup.pow_mem _ hy _, h1 ▸ K.inv_mem (K.pow_mem hk _)⟩
      rw [hI, Subgroup.mem_bot] at h2
      exact h2
    have hy3 : y ^ 3 = 1 := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
    have hcop : Nat.Coprime (r ^ m) 3 :=
      Nat.Coprime.pow_left _ ((Nat.coprime_primes hr Nat.prime_three).mpr hr3)
    have hy1 : y = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hyr, hy3⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    show y * k ∈ K
    rw [hy1, one_mul]
    exact hk
  obtain ⟨Z', hZ'n, ⟨eZ⟩, ⟨eQ⟩⟩ := hK
  have hZ'3 : Nat.card Z' = 3 := by
    rw [Nat.card_congr eZ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  let ρ : ↥K →* ↥(alternatingGroup (Fin 6)) := eQ.toMonoidHom.comp (QuotientGroup.mk' Z')
  have hρker : ∀ k : ↥K, ρ k = 1 ↔ k ∈ Z' := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
      MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hPK : ∃ w ∈ P, ∃ hwK : w ∈ K, (⟨w, hwK⟩ : ↥K) ∉ Z' := by
    by_contra hne
    push Not at hne
    have hsub : (P : Set X) ⊆ (Subgroup.zpowers a : Set X) * (Z'.map K.subtype : Set X) := by
      intro p hp
      have hpC : p ∈ Subgroup.zpowers a ⊔ K := by
        rw [← hC, Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hP.1.1.is_comm.comm ⟨p, hp⟩ ⟨a, haP⟩)
      have hmul : p ∈ ((Subgroup.zpowers a : Set X) * (K : Set X)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ haN]; exact hpC
      obtain ⟨y, hy, k, hk, rfl⟩ := hmul
      have hkP : k ∈ P := by
        have : k = y⁻¹ * (y * k) := by group
        rw [this]
        refine P.mul_mem (P.inv_mem ?_) hp
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact P.zpow_mem haP i
      exact ⟨y, hy, k, ⟨⟨k, hk⟩, hne k hkP hk, rfl⟩, rfl⟩
    have hcard := (Set.natCard_mul_le (s := (Subgroup.zpowers a : Set X))
      (t := (Z'.map K.subtype : Set X)))
    have h1 : Nat.card P ≤ Nat.card ((Subgroup.zpowers a : Set X) *
        (Z'.map K.subtype : Set X)) := Nat.card_mono (Set.toFinite _) hsub
    have h2 : Nat.card (Subgroup.zpowers a : Set X) ≤ 3 := by
      change Nat.card (Subgroup.zpowers a) ≤ 3
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ha3)
    have h3 : Nat.card (Z'.map K.subtype : Set X) = 3 := by
      change Nat.card (Z'.map K.subtype) = 3
      rw [Subgroup.card_map_of_injective K.subtype_injective, hZ'3]
    rw [hP.2] at h1
    have := h1.trans hcard
    rw [h3] at this
    have := this.trans (Nat.mul_le_mul_right 3 h2)
    norm_num at this
  obtain ⟨w, hwP, hwK, hwZ⟩ := hPK
  have hw3 : w ^ 3 = 1 := hP.1.2 w hwP
  rw [eq_bot_iff]
  intro t htR
  by_contra ht1
  rw [Subgroup.mem_bot] at ht1
  have htK : t ∈ K := hRK htR
  obtain ⟨m, hm⟩ := hS ⟨t, htR.1⟩
  have htm : t ^ r ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hordK : orderOf t ∣ 1080 := by
    have := Subgroup.orderOf_dvd_natCard K htK
    rwa [hK1080] at this
  obtain ⟨j, hj, hjt⟩ := (Nat.dvd_prime_pow hr).mp (orderOf_dvd_of_pow_eq_one htm)
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, pow_zero, orderOf_eq_one_iff] at hjt
    exact ht1 hjt
  have hr5 : r = 5 := by
    have hrd : r ∣ 1080 := (dvd_pow_self r hj0).trans (hjt ▸ hordK)
    have : (1080 : ℕ) = 2 ^ 3 * 3 ^ 3 * 5 := by norm_num
    rw [this] at hrd
    rcases (Nat.Prime.dvd_mul hr).mp hrd with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)) hr2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h))
          hr3
    · exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h
  subst hr5
  have hj1 : j = 1 := by
    have h25 : ¬ (5 ^ 2 ∣ 1080) := by norm_num
    by_contra hj1
    exact h25 ((pow_dvd_pow 5 (by omega)).trans (hjt ▸ hordK))
  subst hj1
  rw [pow_one] at hjt
  have hRcard : Nat.card R ∣ 5 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp (hS.to_le inf_le_left))
    have hRK' : Nat.card R ∣ 1080 := hK1080 ▸ Subgroup.card_dvd_of_le hRK
    rw [hn] at hRK' ⊢
    have : n ≤ 1 := by
      by_contra hn1
      exact (show ¬ (5 ^ 2 ∣ 1080) by norm_num) ((pow_dvd_pow 5 (by omega)).trans hRK')
    exact pow_dvd_pow 5 this |>.trans (by norm_num)
  have hRt : R = Subgroup.zpowers t := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htR)
    rw [Nat.card_zpowers, hjt]
    exact Nat.le_of_dvd (by norm_num) hRcard
  have hwR : w * t * w⁻¹ ∈ R := by
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hPS hwP) t).mp htR.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwa : w * a = a * w := congrArg Subtype.val (hP.1.1.is_comm.comm ⟨w, hwP⟩ ⟨a, haP⟩)
    have hta : t * a = a * t := Subgroup.mem_centralizer_singleton_iff.mp htR.2
    calc w * t * w⁻¹ * a = w * t * (w⁻¹ * a) := by group
      _ = w * t * (a * w⁻¹) := by
          rw [show w⁻¹ * a = a * w⁻¹ by
            calc w⁻¹ * a = w⁻¹ * (a * w) * w⁻¹ := by group
              _ = w⁻¹ * (w * a) * w⁻¹ := by rw [hwa]
              _ = a * w⁻¹ := by group]
      _ = w * (t * a) * w⁻¹ := by group
      _ = w * (a * t) * w⁻¹ := by rw [hta]
      _ = (w * a) * t * w⁻¹ := by group
      _ = (a * w) * t * w⁻¹ := by rw [hwa]
      _ = a * (w * t * w⁻¹) := by group
  have hwt : w * t = t * w := commute_of_mem_zpowers_five hjt hw3 (hRt ▸ hwR)
  set w' : ↥K := ⟨w, hwK⟩ with hw'
  set t' : ↥K := ⟨t, htK⟩ with ht'
  have hwt' : t' * w' = w' * t' := Subtype.ext hwt.symm
  have hτ1 : ((ρ w' : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) ≠ 1 := by
    intro h
    exact hwZ ((hρker w').mp (Subtype.ext h))
  have hτ3 : ((ρ w' : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) ^ 3 = 1 := by
    have : ρ w' ^ 3 = 1 := by
      rw [← map_pow, show w' ^ 3 = 1 from Subtype.ext (by simpa using hw3), map_one]
    exact congrArg Subtype.val this
  have hκ3 := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroup.alt_six_centralizer_cube
    _ hτ3 hτ1 (Equiv.Perm.mem_alternatingGroup.mp (ρ w').2) _
    (Equiv.Perm.mem_alternatingGroup.mp (ρ t').2)
    (by
      have := congrArg (fun u : ↥(alternatingGroup (Fin 6)) => (u : Equiv.Perm (Fin 6)))
        (show ρ t' * ρ w' = ρ w' * ρ t' by rw [← map_mul, ← map_mul, hwt'])
      simpa using this)
  have ht3 : t' ^ 3 ∈ Z' := by
    rw [← hρker, map_pow]
    exact Subtype.ext (by simpa using hκ3)
  have hord3 : orderOf (t' ^ 3) ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard Z' ht3
    rwa [hZ'3] at this
  have hord5 : orderOf (t' ^ 3) ∣ 5 := by
    have h5 : t' ^ 5 = 1 := Subtype.ext (by
      have := pow_orderOf_eq_one t
      rw [hjt] at this
      simpa using this)
    exact orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, h5, one_pow])
  have h1 : orderOf (t' ^ 3) = 1 := by
    have := Nat.dvd_gcd hord3 hord5
    simpa using this
  rw [orderOf_eq_one_iff] at h1
  have h5 : t' ^ 5 = 1 := Subtype.ext (by
    have := pow_orderOf_eq_one t
    rw [hjt] at this
    simpa using this)
  have : t' = 1 := by
    calc t' = (t' ^ 3) ^ 2 * (t' ^ 5)⁻¹ := by group
      _ = 1 := by rw [h1, h5]; group
  exact ht1 (congrArg Subtype.val this)

theorem exists_mem_not_center_of_relIndex (hT : IsTripleCover X CFSG.Blueprint.NativeSporadic.ON)
    {P B : Subgroup X} (hP : Late.IsE27 P) (hBP : B ≤ P) (hB : B.relIndex P = 3) :
    ∃ b ∈ B, b ∉ Subgroup.center X := by
  by_contra hne
  push Not at hne
  have hB9 : Nat.card B = 9 := by
    have h := Subgroup.card_mul_index (B.subgroupOf P)
    rw [← Subgroup.relIndex, hB, hP.2] at h
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv]
    omega
  have hle : Nat.card B ≤ Nat.card (Subgroup.center X) :=
    Subgroup.card_le_of_le (fun b hb => hne b hb)
  rw [hB9, hT.1] at hle
  norm_num at hle

theorem isPGroup_two_of_le_normalizer (hperf : Group.IsPerfect X)
    (hT : IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {P : Subgroup X}
    (hP : Late.IsE27 P) {N : Subgroup X} (hPN : P ≤ Subgroup.normalizer (N : Set X))
    (hN3 : ¬ 3 ∣ Nat.card N) : IsPGroup 2 N := by
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {r} hr hrN => ?_)
  by_contra hr2
  have hr3 : r ≠ 3 := fun h => hN3 (h ▸ hrN)
  haveI : CFSG.IsElementaryAbelian 3 P := isElementaryAbelian_of_isE27 hP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact r.Prime := ⟨hr⟩
  letI : MulDistribMulAction P N := Subgroup.conjMulDistribMulActionOfLeNormalizer P N hPN
  obtain ⟨Q, hQ⟩ := CFSG.SolvableHall.exists_invariant_sylow (p := 3) (A := P) (H := N) hN3 r
  set S := (Q : Subgroup N).map N.subtype with hS
  have hPS : P ≤ Subgroup.normalizer (S : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, hQ ⟨g, hg⟩ y hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hginv := hQ ⟨g, hg⟩⁻¹ y hy
      refine ⟨_, hginv, ?_⟩
      change ((⟨g, hg⟩⁻¹ : P) : X) * (y : X) * ((⟨g, hg⟩⁻¹ : P) : X)⁻¹ = x
      have : (y : X) = g * x * g⁻¹ := hyx
      simp only [InvMemClass.coe_inv, inv_inv, this]
      group
  have hSp : IsPGroup r S := Q.isPGroup'.map N.subtype
  have hS3 : ¬ 3 ∣ Nat.card S := fun h3 =>
    hN3 (h3.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)))
  have hSbot : S ≤ ⊥ := by
    refine le_of_forall_inf_centralizer_hyperplane_three (isElementaryAbelian_of_isE27 hP)
      (Finite.one_lt_card_iff_nontrivial.mp (by rw [hP.2]; norm_num)) hS3 hPS fun B hBP hB => ?_
    obtain ⟨b, hbB, hbZ⟩ := exists_mem_not_center_of_relIndex hT hP hBP hB
    rw [← inf_centralizer_eq_bot hperf hT hP (hBP hbB) hbZ hPS hr hr2 hr3 hSp]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))
  have hQ1 := Q.ne_bot_of_dvd_card hrN
  apply hQ1
  rw [eq_bot_iff]
  intro y hy
  have : (y : X) ∈ S := ⟨y, hy, rfl⟩
  have h1 : (y : X) = 1 := (Subgroup.mem_bot).mp (hSbot this)
  exact (Subgroup.mem_bot).mpr (Subtype.ext h1)

open CFSG.RankThree.Native.ONTriple in
theorem card_le_four_of_le_normalizer (hperf : Group.IsPerfect X)
    (hT : IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {P : Subgroup X}
    (hP : Late.IsE27 P) {N : Subgroup X} (hPN : P ≤ Subgroup.normalizer (N : Set X))
    (hN3 : ¬ 3 ∣ Nat.card N) : Nat.card N ≤ 4 := by
  have h2 := isPGroup_two_of_le_normalizer hperf hT hP hPN hN3
  obtain ⟨φ, j, -, hPφ, hc⟩ := exists_model_AG hperf hT hP
  have hA : Late.IsE27 (AG j) := hPφ ▸ Sec13.ON134.isE27_map hP φ.toMonoidHom φ.injective
  set N' := N.map φ.toMonoidHom with hN'
  have hN'mem : N' ∈ invariantPiSubgroups ⊤ (AG j) (piOf 2) := by
    refine ⟨le_top, fun r hr => ?_, ?_⟩
    · have hr' : (r : ℕ) ∣ Nat.card N := by
        rwa [hN', Subgroup.card_map_of_injective φ.injective] at hr
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
      rw [hn] at hr'
      exact (Nat.prime_dvd_prime_iff_eq r.2 Nat.prime_two).mp (r.2.dvd_of_dvd_pow hr')
    · rw [← hPφ]
      rintro _ ⟨g, hg, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hPN hg) x).mp hx, by simp⟩
      · rintro ⟨x, hx, hxy⟩
        refine ⟨φ.symm y, ?_, by simp⟩
        have hxy' : φ x = φ g * y * (φ g)⁻¹ := hxy
        have : x = φ.symm (φ g * y * (φ g)⁻¹) := by
          rw [← hxy']; simp
        have hx' : g * φ.symm y * g⁻¹ ∈ N := by
          rw [show g * φ.symm y * g⁻¹ = x by rw [this]; simp]
          exact hx
        exact (Subgroup.mem_normalizer_iff.mp (hPN hg) _).mpr hx'
  obtain ⟨S, hS, hNS⟩ := exists_le_mem_maxInvariantPiSubgroups hN'mem
  obtain ⟨q, hqP, hqZ⟩ : ∃ q ∈ P, q ∉ Subgroup.center X := by
    by_contra hne
    push Not at hne
    have hle : Nat.card P ≤ Nat.card (Subgroup.center X) := Subgroup.card_le_of_le hne
    rw [hP.2, hT.1] at hle
    norm_num at hle
  have haA : φ q ∈ AG j := hPφ ▸ ⟨q, hqP, rfl⟩
  have haz : φ q ∉ Subgroup.zpowers zG := fun h => hqZ ((hc q).mpr h)
  obtain ⟨hK4, -⟩ := part_three_M hA haA haz hS
  calc Nat.card N = Nat.card N' := (Subgroup.card_map_of_injective φ.injective).symm
    _ ≤ Nat.card S := Subgroup.card_le_of_le hNS
    _ = 4 := hK4.card_four

end Theta

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
