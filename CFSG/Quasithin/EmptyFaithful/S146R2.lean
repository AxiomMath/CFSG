module

public import CFSG.Quasithin.EmptyFaithful.S146G3
public import CFSG.Quasithin.EmptyFaithful.S146Lem2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem oTwoPIn_le_oTwoFstarIn {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    oTwoPIn p H ≤ oTwoFstarIn H := by
  have : Fact p.Prime := ⟨hp⟩
  unfold oTwoPIn oTwoFstarIn preimageModTwoCore
  refine Subgroup.map_mono (Subgroup.comap_mono ?_)
  have hn : (CFSG.pCore p (↥H ⧸ CFSG.pCore 2 ↥H)).Normal :=
    CFSG.BaerSuzuki.Helpers.pCore_normal p
  have hpg : IsPGroup p ↥(CFSG.pCore p (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    CFSG.BaerSuzuki.Helpers.pCore_isPGroup p
  have hnil : Group.IsNilpotent ↥(CFSG.pCore p (↥H ⧸ CFSG.pCore 2 ↥H)) := hpg.isNilpotent
  exact (le_sSup ⟨hn, hnil⟩ : CFSG.pCore p (↥H ⧸ CFSG.pCore 2 ↥H) ≤
    CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)).trans le_sup_left

theorem exists_odd_orderOf_pow (y : G) : ∃ k : ℕ, Odd (orderOf (y ^ 2 ^ k)) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨k, ?_⟩
  have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
  rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

theorem Setting146.commutator_ne_bot_of_oTwoFstarIn (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    (h5 : oTwoFstarIn H ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G))
    {X : Subgroup G} (hX1 : X ≠ ⊥) (hX2 : oTwoUpper X = X) (hXF : X ≤ oTwoFstarIn H)
    (hQX : pCoreOf 2 H ≤ Subgroup.normalizer (X : Set G)) :
    ⁅⁅conjClosure (VZ T M) H, X⁆, pCoreOf 2 H⁆ ≠ ⊥ := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hUQ : conjClosure (VZ T M) H ≤ pCoreOf 2 H := h91.conjClosure_Vp_le_pCoreOf
  have hFH : oTwoFstarIn H ≤ H := Subgroup.map_subtype_le _
  have hXH : X ≤ H := hXF.trans hFH
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hXU := hXH.trans hHU
  have hQU := hQH.trans hHU
  have hUXU : ⁅conjClosure (VZ T M) H, X⁆ ≤ conjClosure (VZ T M) H :=
    S145.commutator_le_of_le_normalizer hXU
  have hQUX : pCoreOf 2 H ≤ Subgroup.normalizer ((⁅conjClosure (VZ T M) H, X⁆ : Subgroup G) : Set G) :=
    S145.le_normalizer_commutator hQU hQX
  have hUXQ : ⁅⁅conjClosure (VZ T M) H, X⁆, pCoreOf 2 H⁆ ≤ quasithinOmegaOneCenter T := by
    rw [Subgroup.commutator_le]
    intro u hu q hq
    rw [commutatorElement_def]
    exact h91.commutator_conjClosure_le u (hUXU hu) q hq
  have hUXQ' : ⁅⁅conjClosure (VZ T M) H, X⁆, pCoreOf 2 H⁆ ≤ ⁅conjClosure (VZ T M) H, X⁆ :=
    S145.commutator_le_of_le_normalizer hQUX
  intro hbot
  have hQc : ∀ q ∈ pCoreOf 2 H, ∀ y ∈ ⁅conjClosure (VZ T M) H, X⁆, y * q = q * y := by
    intro q hq y hy
    have := Subgroup.commutator_le.mp hbot.le y hy q hq
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hW : ∀ y ∈ ⁅conjClosure (VZ T M) H, X⁆, y ∈ omegaOneCenterOf (pCoreOf 2 H) := by
    intro y hy
    refine Subgroup.subset_closure ⟨⟨hUQ (hUXU hy), Subgroup.mem_centralizer_iff.mpr
      fun q hq => (hQc q hq y hy).symm⟩, isElemAbelian_pow_eq_one hUab (hUXU hy)⟩
  have hXc : ∀ x ∈ X, ∀ y ∈ ⁅conjClosure (VZ T M) H, X⁆, y * x = x * y := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (h5 (hXF hx)) y (hW y hy)
  have hodd : ∀ x ∈ X, Odd (orderOf x) →
      x ∈ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) := by
    intro x hx hox
    have hPX : Subgroup.zpowers x ≤ X := Subgroup.zpowers_le.mpr hx
    have hPU : Subgroup.zpowers x ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
      hPX.trans hXU
    have hidx : Odd ((Subgroup.zpowers x ⊓
        Subgroup.centralizer (conjClosure (VZ T M) H : Set G)).relIndex (Subgroup.zpowers x)) := by
      have hd := Subgroup.index_dvd_card
        ((Subgroup.zpowers x ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G)).subgroupOf
          (Subgroup.zpowers x))
      rw [Nat.card_zpowers] at hd
      exact Odd.of_dvd_nat hox hd
    have hcomm : ⁅conjClosure (VZ T M) H, Subgroup.zpowers x⁆ = ⊥ := by
      refine eq_bot_iff.mpr fun z hz => ?_
      have hzU := S145.commutator_le_of_le_normalizer hPU hz
      have hzX : z ∈ ⁅conjClosure (VZ T M) H, X⁆ := Subgroup.commutator_mono le_rfl hPX hz
      have hfix : ∀ p ∈ Subgroup.zpowers x, p * z * p⁻¹ = z := by
        intro p hp
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        have hzx : Commute z x := hXc x hx z hzX
        have hxk : x ^ k * z = z * x ^ k := (hzx.zpow_right k).eq.symm
        calc x ^ k * z * (x ^ k)⁻¹ = z * x ^ k * (x ^ k)⁻¹ := by rw [hxk]
          _ = z := by group
      exact Subgroup.mem_bot.mpr
        (eq_one_of_mem_commutator_of_fixed hUab hPU hidx hzU hz hfix)
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hle hu) x (Subgroup.mem_zpowers x)).symm
  have hXC : X ≤ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) := by
    have : oTwoUpper X ≤ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) :=
      (Subgroup.closure_le _).mpr fun x hx => hodd x hx.1 hx.2
    rwa [hX2] at this
  have hXQ : X ≤ pCoreOf 2 H := fun x hx => S.inf_centralizer_le_pCoreOf hH ⟨hXH hx, hXC hx⟩
  apply hX1
  have hle : oTwoUpper X ≤ ⊥ := oTwoUpper_le_of_pow_mem fun x hx => by
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨x, hXQ hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  rw [hX2] at hle
  exact le_bot_iff.mp hle


theorem IsDec12.exists_odd_three {H H₀ H₁ H₂ : Subgroup G} {t : G}
    (h : IsDec12 T M H 3 H₀ H₁ H₂ t) :
    ∃ z ∈ H₁, z ∉ pCoreOf 2 H ∧ Odd (orderOf z) ∧ z ^ 3 = 1 := by
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  have hord : orderOf (e.symm (DihedralGroup.r 1)) = 3 := by
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm (DihedralGroup.r 1))
  obtain ⟨k, hk⟩ := exists_odd_orderOf_pow (y : G)
  have hzH₁ : (y : G) ^ 2 ^ k ∈ H₁ := H₁.pow_mem y.2 _
  have hmk : (QuotientGroup.mk (⟨(y : G) ^ 2 ^ k, hzH₁⟩ : ↥H₁) : ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) =
      (e.symm (DihedralGroup.r 1)) ^ 2 ^ k := by
    rw [← hy, ← QuotientGroup.mk_pow]
    rfl
  have hzQ : (y : G) ^ 2 ^ k ∉ pCoreOf 2 H := by
    intro hzQ
    have hone : (QuotientGroup.mk (⟨(y : G) ^ 2 ^ k, hzH₁⟩ : ↥H₁) : ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hzQ)
    rw [hmk] at hone
    have hdvd : 3 ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hone
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  have hz3Q : ((y : G) ^ 2 ^ k) ^ 3 ∈ pCoreOf 2 H := by
    have h1 : (QuotientGroup.mk (⟨((y : G) ^ 2 ^ k) ^ 3, H₁.pow_mem hzH₁ 3⟩ : ↥H₁) : ↥H₁ ⧸ (pCoreOf 2 H).subgroupOf H₁) = 1 := by
      have : (⟨((y : G) ^ 2 ^ k) ^ 3, H₁.pow_mem hzH₁ 3⟩ : ↥H₁) = (⟨(y : G) ^ 2 ^ k, hzH₁⟩ : ↥H₁) ^ 3 :=
        rfl
      have h3 : (e.symm (DihedralGroup.r 1)) ^ 3 = 1 := by
        have := pow_orderOf_eq_one (e.symm (DihedralGroup.r 1))
        rwa [hord] at this
      rw [this, QuotientGroup.mk_pow, hmk, ← pow_mul, pow_mul', h3, one_pow]
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  refine ⟨(y : G) ^ 2 ^ k, hzH₁, hzQ, hk, ?_⟩
  obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 H ⟨_, hz3Q⟩
  have hj' : (((y : G) ^ 2 ^ k) ^ 3) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hd : orderOf (((y : G) ^ 2 ^ k) ^ 3) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hodd3 : Odd (orderOf (((y : G) ^ 2 ^ k) ^ 3)) :=
    hk.of_dvd_nat (orderOf_pow_dvd 3)
  rw [hi] at hodd3
  have hi0 : i = 0 := by
    by_contra hi0
    exact (Nat.not_even_iff_odd.mpr hodd3) (Nat.even_pow.mpr ⟨even_two, hi0⟩)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  exact hi

theorem Setting146.not_le_centralizer_uHi (S : Setting146 G T M) (h5 : Stage1461Five)
    {H PQ : Subgroup G} {p : ℕ} (hred : IsRedCE T M H PQ p) (hp3 : p = 3)
    {H₀ H₁ H₂ : Subgroup G} {t : G} (hdec : IsDec12 T M H p H₀ H₁ H₂ t) :
    ¬ pCoreOf 2 H ≤ Subgroup.centralizer (uHi T M H H₁ : Set G) := by
  subst hp3
  have hH : IsHTM T M H := hred.isHTM
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  obtain ⟨z, hz1, hzQ, hzodd, -⟩ := hdec.exists_odd_three
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hX1 : oTwoUpper H₁ ≠ ⊥ := by
    intro hbot
    have hzX : z ∈ oTwoUpper H₁ := mem_oTwoUpper_of_odd hz1 hzodd
    rw [hbot, Subgroup.mem_bot] at hzX
    exact hzQ (hzX ▸ (pCoreOf 2 H).one_mem)
  have hXF : oTwoUpper H₁ ≤ oTwoFstarIn H :=
    (((oTwoUpper_mono hH₁H).trans (hred.oTwoUpper_le_pq hT2)).trans hred.le_oTwoPIn).trans
      (oTwoPIn_le_oTwoFstarIn hred.prime H)
  have hQX : pCoreOf 2 H ≤ Subgroup.normalizer (oTwoUpper H₁ : Set G) :=
    hdec.Q₁.trans (le_normalizer_oTwoUpper H₁)
  have hne := S.commutator_ne_bot_of_oTwoFstarIn hH (h5 G T M S H hH) hX1
    (S146A.oTwoUpper_idem H₁) hXF hQX
  intro hQc
  apply hne
  have h1 : ⁅conjClosure (VZ T M) H, oTwoUpper H₁⁆ ≤ uHi T M H H₁ :=
    (Subgroup.commutator_mono le_rfl (oTwoUpper_le H₁)).trans le_sup_left
  have h2 : ⁅uHi T M H H₁, pCoreOf 2 H⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hQc
  exact le_bot_iff.mp ((Subgroup.commutator_mono h1 le_rfl).trans h2.le)

end CFSG.Quasithin
