module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TPtAct
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.H13

open scoped commutatorElement

structure Ob5KN {G : Type} [Group G] (I K U : Subgroup G) (y : G) : Prop where
  hyI : y ∈ I
  hyodd : Odd (orderOf y)
  hKU : ∀ κ ∈ K, ∀ u ∈ U, κ * u * κ⁻¹ ∈ U
  hKI : ∀ κ ∈ K, ∀ i ∈ I, κ * i * κ⁻¹ * i⁻¹ ∈ CFSG.Open.pCoreOf 2 K
  hQI : ∀ q ∈ CFSG.Open.pCoreOf 2 K, ∀ i ∈ I, q * i * q⁻¹ ∈ I
  hUc : ∀ u ∈ U, ∀ i ∈ I, i * u * i⁻¹ = u
  hUP : ∀ u ∈ U, u ∈ CFSG.Open.pCoreOf 2 I
  hPP : ∀ p ∈ CFSG.Open.pCoreOf 2 I, ∀ q ∈ CFSG.Open.pCoreOf 2 I, ⁅p, q⁆ ∈ U
  hfix : ∀ p ∈ CFSG.Open.pCoreOf 2 I, y * p * y⁻¹ * p⁻¹ ∈ U → p ∈ U

namespace Ob5KN

variable {G : Type} [Group G] [Finite G] {I K U : Subgroup G} {y : G}

theorem factor (S : Ob5KN I K U y) (g : G) (hg : g ∈ I ⊔ CFSG.Open.pCoreOf 2 K) :
    ∃ i ∈ I, ∃ q ∈ CFSG.Open.pCoreOf 2 K, g = i * q := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hxI | hxQ
    · exact ⟨x, hxI, 1, (CFSG.Open.pCoreOf 2 K).one_mem, by simp⟩
    · exact ⟨1, I.one_mem, x, hxQ, by simp⟩
  | one => exact ⟨1, I.one_mem, 1, (CFSG.Open.pCoreOf 2 K).one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i₁, hi₁, q₁, hq₁, rfl⟩ := hx
    obtain ⟨i₂, hi₂, q₂, hq₂, rfl⟩ := hy
    refine ⟨i₁ * (q₁ * i₂ * q₁⁻¹), I.mul_mem hi₁ (S.hQI q₁ hq₁ i₂ hi₂),
      q₁ * q₂, (CFSG.Open.pCoreOf 2 K).mul_mem hq₁ hq₂, ?_⟩
    group
  | inv x _ hx =>
    obtain ⟨i, hi, q, hq, rfl⟩ := hx
    refine ⟨q⁻¹ * i⁻¹ * q, ?_, q⁻¹, (CFSG.Open.pCoreOf 2 K).inv_mem hq, ?_⟩
    · have := S.hQI q⁻¹ ((CFSG.Open.pCoreOf 2 K).inv_mem hq) i⁻¹ (I.inv_mem hi)
      rwa [inv_inv] at this
    · group

theorem Q_norm_K (κ : G) (hκ : κ ∈ K) (q : G) (hq : q ∈ CFSG.Open.pCoreOf 2 K) :
    κ * q * κ⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  have hN : κ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hκ
  have h2 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hN
  exact (Subgroup.mem_normalizer_iff.mp h2 q).mp hq

theorem conj_closure (n : G) (T : Set G) (hT : ∀ g ∈ T, n * g * n⁻¹ ∈ T) :
    ∀ x ∈ Subgroup.closure T, n * x * n⁻¹ ∈ Subgroup.closure T := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hT x hx)
  | one => simp [Subgroup.one_mem]
  | mul x y _ _ hx hy =>
    have e : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => 
    have e : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem odd_mem_I (S : Ob5KN I K U y) (g : G) (hg : g ∈ I ⊔ CFSG.Open.pCoreOf 2 K)
    (hodd : Odd (orderOf g)) : g ∈ I := by
  obtain ⟨i, hi, q, hq, rfl⟩ := S.factor _ hg
  have hpow : ∀ m : ℕ, ∃ i' ∈ I, (i * q) ^ m = i' * q ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, I.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨i', hi', hm⟩ := ih
      refine ⟨i' * (q ^ m * i * (q ^ m)⁻¹), I.mul_mem hi'
        (S.hQI _ ((CFSG.Open.pCoreOf 2 K).pow_mem hq m) i hi), ?_⟩
      rw [pow_succ, hm]
      group
  have hq2 : ∃ a : ℕ, q ^ (2 ^ a) = 1 := by
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ⟨q, hq⟩
    exact ⟨a, by
      have := congrArg Subtype.val ha
      simpa using this⟩
  obtain ⟨a, ha⟩ := hq2
  obtain ⟨i', hi', hm⟩ := hpow (2 ^ a)
  rw [ha, mul_one] at hm
  have hgpow : (i * q) ^ (2 ^ a) ∈ I := by rw [hm]; exact hi'
  set n := orderOf (i * q) with hnlt
  have hn : (i * q) ^ n = 1 := pow_orderOf_eq_one _
  have h2n : ¬ 2 ∣ n := by
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcop : Nat.Coprime (2 ^ a) n :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2n)
  have h1 : ((1 : ℕ) : ℤ) = ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) n + (n : ℤ) * Nat.gcdB (2 ^ a) n := by
    have := Nat.gcd_eq_gcd_ab (2 ^ a) n
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    exact this
  have hdecomp : i * q = ((i * q) ^ (2 ^ a)) ^ (Nat.gcdA (2 ^ a) n) *
      ((i * q) ^ n) ^ (Nat.gcdB (2 ^ a) n) := by
    calc i * q = (i * q) ^ ((1 : ℕ) : ℤ) := by simp
      _ = (i * q) ^ (((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) n + (n : ℤ) * Nat.gcdB (2 ^ a) n) := by
          rw [← h1]
      _ = ((i * q) ^ (2 ^ a)) ^ (Nat.gcdA (2 ^ a) n) * ((i * q) ^ n) ^ (Nat.gcdB (2 ^ a) n) := by
          simp only [zpow_add, zpow_mul, zpow_natCast]
  have hfinal : ((i * q) ^ (2 ^ a)) ^ (Nat.gcdA (2 ^ a) n) *
      ((i * q) ^ n) ^ (Nat.gcdB (2 ^ a) n) ∈ I := by
    refine I.mul_mem (I.zpow_mem hgpow _) ?_
    rw [hn, one_zpow]
    exact I.one_mem
  rw [← hdecomp] at hfinal
  exact hfinal

theorem orderOf_conj' (n g : G) : orderOf (n * g * n⁻¹) = orderOf g := by
  have := orderOf_injective (MulAut.conj n).toMonoidHom (MulEquiv.injective _) g
  simpa using this

theorem K_norm (S : Ob5KN I K U y) : ∀ κ ∈ K, ∀ p ∈ CFSG.Open.pCoreOf 2 I,
    κ * p * κ⁻¹ ∈ CFSG.Open.pCoreOf 2 I := by
  classical
  have hJ : ∀ κ ∈ K, ∀ g ∈ I ⊔ CFSG.Open.pCoreOf 2 K,
      κ * g * κ⁻¹ ∈ I ⊔ CFSG.Open.pCoreOf 2 K := by
    intro κ hκ g hg
    obtain ⟨i, hi, q, hq, rfl⟩ := S.factor g hg
    have hc : κ * i * κ⁻¹ * i⁻¹ ∈ I ⊔ CFSG.Open.pCoreOf 2 K :=
      (le_sup_right : CFSG.Open.pCoreOf 2 K ≤ I ⊔ CFSG.Open.pCoreOf 2 K) (S.hKI κ hκ i hi)
    have hi' : i ∈ I ⊔ CFSG.Open.pCoreOf 2 K := (le_sup_left : I ≤ I ⊔ CFSG.Open.pCoreOf 2 K) hi
    have hq' : κ * q * κ⁻¹ ∈ I ⊔ CFSG.Open.pCoreOf 2 K :=
      (le_sup_right : CFSG.Open.pCoreOf 2 K ≤ I ⊔ CFSG.Open.pCoreOf 2 K) (Q_norm_K κ hκ q hq)
    have e : κ * (i * q) * κ⁻¹ = (κ * i * κ⁻¹ * i⁻¹) * i * (κ * q * κ⁻¹) := by group
    rw [e]
    exact (I ⊔ CFSG.Open.pCoreOf 2 K).mul_mem ((I ⊔ CFSG.Open.pCoreOf 2 K).mul_mem hc hi') hq'
  set Oset : Set G := {g | g ∈ I ⊔ CFSG.Open.pCoreOf 2 K ∧ Odd (orderOf g)} with hOdef
  have hS_K : ∀ κ ∈ K, ∀ g ∈ Oset, κ * g * κ⁻¹ ∈ Oset := by
    intro κ hκ g hg
    exact ⟨hJ κ hκ g hg.1, by rw [orderOf_conj']; exact hg.2⟩
  have hS_I : ∀ i ∈ I, ∀ g ∈ Oset, i * g * i⁻¹ ∈ Oset := by
    intro i hi g hg
    have hiJ : i ∈ I ⊔ CFSG.Open.pCoreOf 2 K := (le_sup_left : I ≤ I ⊔ CFSG.Open.pCoreOf 2 K) hi
    refine ⟨(I ⊔ CFSG.Open.pCoreOf 2 K).mul_mem ((I ⊔ CFSG.Open.pCoreOf 2 K).mul_mem hiJ hg.1)
      ((I ⊔ CFSG.Open.pCoreOf 2 K).inv_mem hiJ), ?_⟩
    rw [orderOf_conj']
    exact hg.2
  set X : Subgroup G := Subgroup.closure Oset with hXdef
  have hX_K : ∀ κ ∈ K, ∀ x ∈ X, κ * x * κ⁻¹ ∈ X := fun κ hκ => conj_closure κ Oset (hS_K κ hκ)
  have hX_I : ∀ i ∈ I, ∀ x ∈ X, i * x * i⁻¹ ∈ X := fun i hi => conj_closure i Oset (hS_I i hi)
  have hS_sub : Oset ⊆ I := fun g hg => S.odd_mem_I g hg.1 hg.2
  have hX_le : X ≤ I := Subgroup.closure_le I |>.mpr hS_sub
  have hy_X : y ∈ X := Subgroup.subset_closure ⟨(le_sup_left : I ≤ I ⊔ CFSG.Open.pCoreOf 2 K) S.hyI,
    S.hyodd⟩
  have hIN : I ≤ Subgroup.normalizer (X : Set G) := by
    intro i hi
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hX_I i hi x
    · intro hx
      have h1 := hX_I i⁻¹ (I.inv_mem hi) _ hx
      have e : i⁻¹ * (i * x * i⁻¹) * i⁻¹⁻¹ = x := by group
      rw [e] at h1
      exact h1
  have hKN : K ≤ Subgroup.normalizer (X : Set G) := by
    intro κ hκ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hX_K κ hκ x
    · intro hx
      have h1 := hX_K κ⁻¹ (K.inv_mem hκ) _ hx
      have e : κ⁻¹ * (κ * x * κ⁻¹) * κ⁻¹⁻¹ = x := by group
      rw [e] at h1
      exact h1
  have hPI : ∀ i ∈ I, ∀ p ∈ CFSG.Open.pCoreOf 2 I, i * p * i⁻¹ ∈ CFSG.Open.pCoreOf 2 I :=
    fun i hi p hp =>
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I hi) p).mp hp
  have hZ_le_P : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 I :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hX_le)
      (hIN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hPgrp : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 I) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I
  have hsub2 : ∀ H : Subgroup G, H ≤ CFSG.Open.pCoreOf 2 I → IsPGroup 2 ↥H := by
    intro H hH g
    obtain ⟨k, hk⟩ := hPgrp ⟨g.1, hH g.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hback : ∀ x ∈ I, ∀ z : G, x * z * x⁻¹ ∈ X ⊓ CFSG.Open.pCoreOf 2 I →
      z ∈ X ⊓ CFSG.Open.pCoreOf 2 I := by
    intro x hx z hz
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hz
    have A := hX_I x⁻¹ (I.inv_mem hx) _ h1
    have B := hPI x⁻¹ (I.inv_mem hx) _ h2
    have e : x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z := by group
    rw [e] at A B
    exact Subgroup.mem_inf.mpr ⟨A, B⟩
  have hXP : X ⊓ CFSG.Open.pCoreOf 2 I = CFSG.Open.pCoreOf 2 X := by
    apply le_antisymm
    · apply CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      · intro x hx
        rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · intro hz
          obtain ⟨hzX, hzP⟩ := Subgroup.mem_inf.mp hz
          exact Subgroup.mem_inf.mpr ⟨hX_I x (hX_le hx) z hzX, hPI x (hX_le hx) z hzP⟩
        · exact hback x (hX_le hx) z
      · exact hsub2 _ inf_le_right
    · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hZ_le_P
  have hyP : y ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 I : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I S.hyI
  have hyU : y ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [S.hUc u hu y S.hyI]
      exact hu
    · intro hu
      have h1 := S.hUc _ hu y⁻¹ (I.inv_mem S.hyI)
      have e : y⁻¹ * (y * u * y⁻¹) * y⁻¹⁻¹ = u := by group
      rw [e] at h1
      rw [h1]
      exact hu
  haveI : L828T.PtActCentralAbelian (CFSG.Open.pCoreOf 2 I) U :=
    ⟨fun u hu p hp => S.hUc u hu p ((CFSG.LieType.BorelTits.pCoreOf_le 2 I) hp),
      fun p hp q hq => S.hPP p hp q hq⟩
  set δ : (↥(CFSG.Open.pCoreOf 2 I) ⧸ U.subgroupOf (CFSG.Open.pCoreOf 2 I)) →*
      (↥(CFSG.Open.pCoreOf 2 I) ⧸ U.subgroupOf (CFSG.Open.pCoreOf 2 I)) :=
    L828T.ptActConj (CFSG.Open.pCoreOf 2 I) U y hyP hyU * (MonoidHom.id _)⁻¹ with hδdef
  have hδ : ∀ x, δ x = L828T.ptActConj (CFSG.Open.pCoreOf 2 I) U y hyP hyU x * x⁻¹ :=
    fun x => rfl
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hδ, mul_inv_eq_one] at hx
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    rw [L828T.ptActConj_mk, QuotientGroup.eq] at hx
    rw [QuotientGroup.eq_one_iff]
    have hw : ((L828T.ptActConjP (CFSG.Open.pCoreOf 2 I) y hyP q : ↥(CFSG.Open.pCoreOf 2 I)) : G)⁻¹ *
        (q : G) ∈ U := by
      rw [Subgroup.mem_subgroupOf] at hx
      simpa using hx
    have hqI : (q : G) ∈ I := (CFSG.LieType.BorelTits.pCoreOf_le 2 I) q.2
    rw [Subgroup.mem_subgroupOf]
    have hq' : (q : G) ∈ U := by
      have hfix' : y * (q : G) * y⁻¹ * (q : G)⁻¹ ∈ U := by
        have e : y * (q : G) * y⁻¹ * (q : G)⁻¹ = (q : G) * (((y * (q : G) * y⁻¹)⁻¹ * (q : G))⁻¹) *
            (q : G)⁻¹ := by group
        have hwu : (((y * (q : G) * y⁻¹)⁻¹ * (q : G))⁻¹) ∈ U := U.inv_mem hw
        rw [e, S.hUc _ hwu _ hqI]
        exact hwu
      exact S.hfix q q.2 hfix'
    exact hq'
  have hsurj : Function.Surjective δ := Finite.injective_iff_surjective.mp hinj
  have hPdec : ∀ p ∈ CFSG.Open.pCoreOf 2 I, ∃ z ∈ CFSG.Open.pCoreOf 2 X, ∃ u ∈ U, p = z * u := by
    intro p hp
    obtain ⟨x, hx⟩ := hsurj (QuotientGroup.mk ⟨p, hp⟩)
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have hqI : (q : G) ∈ I := (CFSG.LieType.BorelTits.pCoreOf_le 2 I) q.2
    set zc : ↥(CFSG.Open.pCoreOf 2 I) :=
      L828T.ptActConjP (CFSG.Open.pCoreOf 2 I) y hyP q * q⁻¹ with hzc
    have hzeq : (QuotientGroup.mk zc : ↥(CFSG.Open.pCoreOf 2 I) ⧸ U.subgroupOf (CFSG.Open.pCoreOf 2 I)) =
        QuotientGroup.mk ⟨p, hp⟩ := by
      rw [← hx, hδ, L828T.ptActConj_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    have hz := QuotientGroup.eq.mp hzeq
    rw [Subgroup.mem_subgroupOf] at hz
    have hzU : ((zc : ↥(CFSG.Open.pCoreOf 2 I)) : G)⁻¹ * p ∈ U := by
      simpa using hz
    have hzG : ((zc : ↥(CFSG.Open.pCoreOf 2 I)) : G) = y * (q : G) * y⁻¹ * (q : G)⁻¹ := by
      simp [hzc, L828T.ptActConjP]
    refine ⟨((zc : ↥(CFSG.Open.pCoreOf 2 I)) : G), ?_, ((zc : ↥(CFSG.Open.pCoreOf 2 I)) : G)⁻¹ * p,
      hzU, by group⟩
    rw [← hXP]
    rw [hzG]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e : y * (q : G) * y⁻¹ * (q : G)⁻¹ = y * ((q : G) * y⁻¹ * (q : G)⁻¹) := by group
      rw [e]
      exact X.mul_mem hy_X (hX_I (q : G) hqI y⁻¹ (X.inv_mem hy_X))
    · have e : y * (q : G) * y⁻¹ * (q : G)⁻¹ = (y * (q : G) * y⁻¹) * (q : G)⁻¹ := by group
      rw [e]
      exact (CFSG.Open.pCoreOf 2 I).mul_mem (hPI y S.hyI q q.2) ((CFSG.Open.pCoreOf 2 I).inv_mem q.2)
  intro κ hκ p hp
  obtain ⟨z, hz, u, hu, rfl⟩ := hPdec p hp
  have hzP : z ∈ CFSG.Open.pCoreOf 2 I := hZ_le_P hz
  have e : κ * (z * u) * κ⁻¹ = (κ * z * κ⁻¹) * (κ * u * κ⁻¹) := by group
  rw [e]
  have hκz : κ * z * κ⁻¹ ∈ CFSG.Open.pCoreOf 2 X := by
    have := (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf
      2 X (hKN hκ)) z).mp hz
    exact this
  exact (CFSG.Open.pCoreOf 2 I).mul_mem (hZ_le_P hκz) (S.hUP _ (S.hKU κ hκ u hu))

end Ob5KN

end CFSG.Quasithin.H13
