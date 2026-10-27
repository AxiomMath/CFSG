module

public import CFSG.Models.PGL
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowA10

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)
open Equiv Equiv.Perm
open CFSG.Quasithin.SteinbergCB (conjPerm conjPerm_surjective conjPerm_injective)
open scoped commutatorElement

theorem exists_pow_eq_on_support {α : Type*} [Fintype α] [DecidableEq α] {τ x : Perm α}
    (hτ : τ.IsCycle) (hx : Commute x τ) : ∃ i : ℕ, ∀ m ∈ τ.support, x m = (τ ^ i) m := by
  obtain ⟨m₀, hm₀, -⟩ := id hτ
  have hxm₀ : τ (x m₀) ≠ x m₀ := by
    intro h
    apply hm₀
    apply x.injective
    calc x (τ m₀) = (x * τ) m₀ := rfl
      _ = (τ * x) m₀ := by rw [hx.eq]
      _ = x m₀ := h
  obtain ⟨i, hi⟩ := hτ.exists_pow_eq hm₀ hxm₀
  refine ⟨i, fun m hm => ?_⟩
  obtain ⟨j, hj⟩ := hτ.exists_pow_eq hm₀ (mem_support.mp hm)
  calc x m = x ((τ ^ j) m₀) := by rw [hj]
    _ = (x * τ ^ j) m₀ := rfl
    _ = (τ ^ j * x) m₀ := by rw [(hx.pow_right j).eq]
    _ = (τ ^ j * τ ^ i) m₀ := by rw [Perm.mul_apply, ← hi, Perm.mul_apply]
    _ = (τ ^ i * τ ^ j) m₀ := by rw [((Commute.refl τ).pow_pow j i).eq]
    _ = (τ ^ i) m := by rw [Perm.mul_apply, hj]

theorem commutatorElement_apply_of_commute {α : Type*} [Fintype α] [DecidableEq α]
    {τ x y : Perm α} (hτ : τ.IsCycle) (hx : Commute x τ) (hy : Commute y τ) {m : α}
    (hm : m ∈ τ.support) : ⁅x, y⁆ m = m := by
  obtain ⟨i, hi⟩ := exists_pow_eq_on_support hτ hx
  obtain ⟨j, hj⟩ := exists_pow_eq_on_support hτ hy
  have hcx : Commute ((τ ^ i)⁻¹ * x) τ := (((Commute.refl τ).pow_left i).inv_left).mul_left hx
  have hcy : Commute ((τ ^ j)⁻¹ * y) τ := (((Commute.refl τ).pow_left j).inv_left).mul_left hy
  have hfx : ((τ ^ i)⁻¹ * x) m = m := by
    rw [Perm.mul_apply, hi m hm, Perm.inv_eq_iff_eq]
  have hfy : ((τ ^ j)⁻¹ * y) m = m := by
    rw [Perm.mul_apply, hj m hm, Perm.inv_eq_iff_eq]
  have hx' : x = τ ^ i * ((τ ^ i)⁻¹ * x) := by rw [mul_inv_cancel_left]
  have hy' : y = τ ^ j * ((τ ^ j)⁻¹ * y) := by rw [mul_inv_cancel_left]
  rw [hx', hy', commutator_mul_mul_of_commute (hcx.pow_right i).symm (hcy.pow_right i).symm
    (hcx.pow_right j).symm (hcy.pow_right j).symm ((Commute.refl τ).pow_pow i j)]
  have hix : ((τ ^ i)⁻¹ * x)⁻¹ m = m := Perm.inv_eq_iff_eq.mpr hfx.symm
  have hiy : ((τ ^ j)⁻¹ * y)⁻¹ m = m := Perm.inv_eq_iff_eq.mpr hfy.symm
  rw [commutatorElement_def, Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, hiy, hix, hfy, hfx]

theorem le_range_ofSubtype_of_isPerfect {n : ℕ} {τ : Perm (Fin n)} (hτ : τ.IsCycle)
    {K : Subgroup (alternatingGroup (Fin n))} (hK : K ≤ autFix (conjPerm n τ))
    [Group.IsPerfect K] : K ≤ (alternatingGroup.ofSubtype τ.supportᶜ).range := by
  rw [← Subgroup.commutator_eq_self (H := K), Subgroup.commutator_le]
  intro a ha b hb
  rw [alternatingGroup.mem_range_ofSubtype_iff]
  intro m hm
  rw [Finset.mem_compl]
  intro hmτ
  have hcoe : ((⁅a, b⁆ : alternatingGroup (Fin n)) : Perm (Fin n)) =
      ⁅(a : Perm (Fin n)), (b : Perm (Fin n))⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    rfl
  rw [mem_support, hcoe] at hm
  exact hm (commutatorElement_apply_of_commute hτ (mem_autFix_conjPerm_iff.mp (hK ha))
    (mem_autFix_conjPerm_iff.mp (hK hb)) hmτ)

theorem range_ofSubtype_le_autFix {n : ℕ} (τ : Perm (Fin n)) :
    (alternatingGroup.ofSubtype τ.supportᶜ).range ≤ autFix (conjPerm n τ) := by
  intro x hx
  rw [alternatingGroup.mem_range_ofSubtype_iff] at hx
  rw [mem_autFix_conjPerm_iff]
  have hd : Perm.Disjoint (x : Perm (Fin n)) τ := by
    intro m
    by_cases hm : m ∈ τ.support
    · left
      by_contra h
      exact Finset.mem_compl.mp (hx (mem_support.mpr h)) hm
    · right
      exact notMem_support.mp hm
  exact hd.commute.eq

theorem exists_mulEquiv_alternatingGroup_of_isThreeCycle
    {n : ℕ} (hn : 8 ≤ n)
    {τ : Perm (Fin n)} (hτ : τ.IsThreeCycle) {A : Subgroup (MulAut (alternatingGroup (Fin n)))}
    {K : Subgroup (alternatingGroup (Fin n))}
    (hc : CfgS429 (alternatingGroup (Fin n)) A (conjPerm n τ) K) :
    Fintype.card ↥(τ.supportᶜ) = n - 3 ∧
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup ↥(τ.supportᶜ)) := by
  have hcard : Fintype.card ↥(τ.supportᶜ) = n - 3 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hτ.card_support]
  refine ⟨hcard, ?_⟩
  have hRC := range_ofSubtype_le_autFix τ
  haveI := hc.isPerfect
  have hKR : K ≤ (alternatingGroup.ofSubtype τ.supportᶜ).range :=
    le_range_ofSubtype_of_isPerfect hτ.isCycle hc.le_autFix
  let ψ : alternatingGroup ↥(τ.supportᶜ) ≃* (alternatingGroup.ofSubtype τ.supportᶜ).range :=
    MonoidHom.ofInjective alternatingGroup.ofSubtype_injective
  haveI : IsSimpleGroup (alternatingGroup ↥(τ.supportᶜ)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_finsetCard, Finset.card_compl,
      Fintype.card_fin, hτ.card_support]; omega)
  have hRs : IsSimpleGroup (alternatingGroup.ofSubtype τ.supportᶜ).range := ψ.symm.isSimpleGroup
  have hsub : (K.subgroupOf (alternatingGroup.ofSubtype τ.supportᶜ).range).IsSubnormal := by
    have h := Subgroup.IsSubnormal.comap (Subgroup.inclusion hRC) hc.isSubnormal
    have heq : (K.subgroupOf (autFix (conjPerm n τ))).comap (Subgroup.inclusion hRC) =
        K.subgroupOf (alternatingGroup.ofSubtype τ.supportᶜ).range := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h
  have h1 := le_card_of_isType429 hc.isType
  have h2 : Nat.card (K ⧸ CFSG.pCore 2 K) ≤ Nat.card K :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hKeq : K = (alternatingGroup.ofSubtype τ.supportᶜ).range := by
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hRs hsub with h | h
    · exfalso
      have hK : K = ⊥ := (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hKR
      have : Nat.card K = 1 := by rw [hK, Subgroup.card_bot]
      omega
    · exact le_antisymm hKR (Subgroup.subgroupOf_eq_top.mp h)
  let χ : K ≃* alternatingGroup ↥(τ.supportᶜ) := (MulEquiv.subgroupCongr hKeq).trans ψ.symm
  haveI : IsSimpleGroup K := χ.isSimpleGroup
  have hO : CFSG.pCore 2 K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 K) with h | h
    · exact h
    · exfalso
      have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 K)
      have h4 : Nat.card (CFSG.pCore 2 K) = Nat.card K := by rw [h, Subgroup.card_top]
      rw [h4] at h3
      have h5 : 0 < Nat.card K := Nat.card_pos
      have h6 : Nat.card (K ⧸ CFSG.pCore 2 K) = 1 :=
        Nat.eq_of_mul_eq_mul_right h5 (h3.symm.trans (one_mul _).symm)
      omega
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hO).trans (QuotientGroup.quotientBot.trans χ)⟩

theorem nat_card_alternatingGroup_of_card {Ω : Type} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
    (hm : Fintype.card Ω = m) (h2 : 2 ≤ m) :
    Nat.card (alternatingGroup Ω) = m.factorial / 2 := by
  haveI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, hm]

theorem checkSL_a8 : ∀ q < 40, 2 ≤ q →
    20160 * Nat.gcd 3 (q - 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) → q = 4 := by
  decide +kernel

theorem checkSU_a8 : ∀ q < 28, 2 ≤ q → q ^ 3 ∣ 20160 →
    20160 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel

theorem not_isType429_of_alternating_eight
    {T : Type} [Group T] {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 8)
    (φ : T ≃* alternatingGroup Ω) : ¬ IsType429 T := by
  have hT : Nat.card T = 20160 := by
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup_of_card hΩ (by norm_num)]
    decide
  intro h
  rcases h with ⟨p, e, hp, he, h⟩ | h | h | h | h
  · rcases h with ⟨-, ⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩
    · have hp' : p.Prime := Fact.out
      have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
      rw [GaloisField.card p e (by omega), ← Nat.card_congr ψ.toEquiv, hT] at hc
      obtain ⟨q, hq⟩ : ∃ q, q = p ^ e := ⟨_, rfl⟩
      rw [← hq] at hc
      have hq2 : 2 ≤ q := hq ▸ hp'.two_le.trans (Nat.le_self_pow (by omega) p)
      have hq40 : q < 40 := by
        by_contra hge
        have h1 : 64000 ≤ q ^ 3 := by
          calc 64000 = 40 ^ 3 := by norm_num
            _ ≤ q ^ 3 := Nat.pow_le_pow_left (not_lt.mp hge) 3
        have h2 : 1 ≤ q ^ 2 - 1 := by
          have : 4 ≤ q ^ 2 := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ q ^ 2 := Nat.pow_le_pow_left hq2 2
          omega
        have h3 : 1 ≤ q ^ 3 - 1 := by omega
        have h4 : q ^ 3 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos h2 h3)
        have h5 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
        omega
      have h4 : p ^ e = 2 ^ 2 := by rw [← hq, checkSL_a8 q hq40 hq2 hc]; norm_num
      have hp2 : p = 2 := by
        have hd : p ∣ 2 ^ 2 := h4 ▸ dvd_pow_self p (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp (hp'.dvd_of_dvd_pow hd)
      subst hp2
      have he2 : e = 2 := Nat.pow_right_injective le_rfl h4
      subst he2
      have hX := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL
        ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩ ψ
      exact ((CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated T hX).2.2
        Ω (by omega)).false φ
    · exact (KFacts.KS14.isEmpty_mulEquiv_projSU_three_of_card hT
        (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_a8) p e he).false ψ
  · obtain ⟨ψ⟩ := h
    have := Nat.card_congr ψ.toEquiv
    rw [hT, KFacts.KS14.card_alternatingGroup_fin (by norm_num)] at this
    exact absurd this (by decide)
  · obtain ⟨ψ⟩ := h
    have := Nat.card_congr ψ.toEquiv
    rw [hT, CFSG.Sporadic.Mathieu.card_M12] at this
    omega
  · obtain ⟨ψ⟩ := h
    have := Nat.card_congr ψ.toEquiv
    rw [hT, CFSG.Sporadic.Mathieu.card_M22] at this
    omega
  · obtain ⟨ψ⟩ := h
    have := Nat.card_congr ψ.toEquiv
    rw [hT, CFSG.Sporadic.J2.card_J2] at this
    omega

theorem checkSL_a9 : ∀ q < 57, 2 ≤ q → q ^ 3 ∣ 181440 →
    181440 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide +kernel

theorem checkSU_a9 : ∀ q < 57, 2 ≤ q → q ^ 3 ∣ 181440 →
    181440 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel

theorem not_isType429_of_alternating_nine
    {T : Type} [Group T]
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 9)
    (φ : T ≃* alternatingGroup Ω) : ¬ IsType429 T := by
  have hT : Nat.card T = 181440 := by
    rw [Nat.card_congr φ.toEquiv, nat_card_alternatingGroup_of_card hΩ (by norm_num)]
    decide
  intro h
  rcases h with ⟨p, e, hp, he, h⟩ | h | h | h | h
  · exact KFacts.KS14.not_isoLThreePi_of_card hT
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_a9)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_a9) p e h
  · obtain ⟨ψ⟩ := h
    have := Nat.card_congr ψ.toEquiv
    rw [hT, KFacts.KS14.card_alternatingGroup_fin (by norm_num)] at this
    exact absurd this (by decide)
  · obtain ⟨ψ⟩ := h
    have := Nat.card_congr ψ.toEquiv
    rw [hT, CFSG.Sporadic.Mathieu.card_M12] at this
    omega
  · obtain ⟨ψ⟩ := h
    have := Nat.card_congr ψ.toEquiv
    rw [hT, CFSG.Sporadic.Mathieu.card_M22] at this
    omega
  · obtain ⟨ψ⟩ := h
    have := Nat.card_congr ψ.toEquiv
    rw [hT, CFSG.Sporadic.J2.card_J2] at this
    omega

theorem checkSL_dvd_38880 : ∀ q < 34, 2 ≤ q → q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ 38880 →
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) < 2520 := by
  decide +kernel

theorem checkSU_dvd_38880 : ∀ q < 34, 2 ≤ q → q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ 38880 →
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) < 2520 := by
  decide +kernel

theorem lt_34_of_pow_three_dvd {q : ℕ} (h : q ^ 3 ∣ 38880) : q < 34 := by
  by_contra hge
  have h1 : 39304 ≤ q ^ 3 := by
    calc 39304 = 34 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left (not_lt.mp hge) 3
  have h2 := Nat.le_of_dvd (by norm_num) h
  omega

theorem not_isType429_of_card_dvd
    {T : Type} [Group T] [Finite T] [Group.IsPerfect T]
    (h : IsType429 T) (hd : Nat.card T ∣ 12960) : False := by
  have h2520 := le_card_of_isType429 h
  rcases h with ⟨p, e, hp, he, h⟩ | h | h | h | h
  · have hp' : p.Prime := Fact.out
    have hq2 : 2 ≤ p ^ e := hp'.two_le.trans (Nat.le_self_pow (by omega) p)
    rcases h with ⟨-, ⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩
    · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
      rw [GaloisField.card p e (by omega), ← Nat.card_congr ψ.toEquiv] at hc
      have hdvd : (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) ∣ 38880 := by
        rw [← hc]
        exact Nat.mul_dvd_mul hd (Nat.gcd_dvd_left 3 _)
      have hlt := checkSL_dvd_38880 _ (lt_34_of_pow_three_dvd ((dvd_mul_right _ _).trans hdvd))
        hq2 hdvd
      have hg : 0 < Nat.gcd 3 (p ^ e - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
      have hle : Nat.card T ≤ Nat.card T * Nat.gcd 3 (p ^ e - 1) := Nat.le_mul_of_pos_right _ hg
      omega
    · have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
      rw [← Nat.card_congr ψ.toEquiv] at hc
      have hdvd : (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) ∣ 38880 := by
        rw [← hc]
        exact Nat.mul_dvd_mul hd (Nat.gcd_dvd_left 3 _)
      have hlt := checkSU_dvd_38880 _ (lt_34_of_pow_three_dvd ((dvd_mul_right _ _).trans hdvd))
        hq2 hdvd
      have hg : 0 < Nat.gcd 3 (p ^ e + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
      have hle : Nat.card T ≤ Nat.card T * Nat.gcd 3 (p ^ e + 1) := Nat.le_mul_of_pos_right _ hg
      omega
  · obtain ⟨ψ⟩ := h
    rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_fin (by norm_num)] at hd
    exact absurd hd (by decide)
  · obtain ⟨ψ⟩ := h
    rw [Nat.card_congr ψ.toEquiv, CFSG.Sporadic.Mathieu.card_M12] at hd
    exact absurd hd (by norm_num)
  · obtain ⟨ψ⟩ := h
    rw [Nat.card_congr ψ.toEquiv, CFSG.Sporadic.Mathieu.card_M22] at hd
    exact absurd hd (by norm_num)
  · obtain ⟨ψ⟩ := h
    rw [Nat.card_congr ψ.toEquiv, CFSG.Sporadic.J2.card_J2] at hd
    exact absurd hd (by norm_num)

theorem isThreeCycle_or_exists_card_centralizer {n : ℕ} {τ : Perm (Fin n)} (h3 : τ ^ 3 = 1)
    (h1 : τ ≠ 1) :
    τ.IsThreeCycle ∨ ∃ k : ℕ, 2 ≤ k ∧ 3 * k ≤ n ∧
      Nat.card (Subgroup.centralizer ({τ} : Set (Perm (Fin n)))) =
        (n - 3 * k).factorial * 3 ^ k * k.factorial := by
  have hord : orderOf τ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hmem : ∀ m ∈ τ.cycleType, m = 3 := fun m hm => by
    have h2 := two_le_of_mem_cycleType hm
    have hd := (dvd_of_mem_cycleType hm).trans hord
    have : m ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    interval_cases m
    · norm_num at hd
    · rfl
  set k := Multiset.card τ.cycleType with hk
  have hrep : τ.cycleType = Multiset.replicate k 3 := Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hsum : 3 * k ≤ n := by
    have := sum_cycleType_le τ
    rw [hrep, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at this
    omega
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, Multiset.replicate_zero] at hrep
    exact h1 (cycleType_eq_zero.mp hrep)
  by_cases hk1' : k = 1
  · left
    rw [IsThreeCycle, hrep, hk1', Multiset.replicate_one]
  · right
    refine ⟨k, by omega, hsum, ?_⟩
    rw [nat_card_centralizer, hrep, Multiset.sum_replicate, Multiset.prod_replicate,
      Fintype.card_fin, smul_eq_mul, Multiset.toFinset_replicate, if_neg (by omega),
      Finset.prod_singleton, Multiset.count_replicate_self, mul_comm k 3]

theorem card_dvd_card_centralizer {n : ℕ} {τ : Perm (Fin n)}
    {K : Subgroup (alternatingGroup (Fin n))} (hK : K ≤ autFix (conjPerm n τ)) :
    Nat.card K ∣ Nat.card (Subgroup.centralizer ({τ} : Set (Perm (Fin n)))) := by
  have hle : K.map (alternatingGroup (Fin n)).subtype ≤
      Subgroup.centralizer ({τ} : Set (Perm (Fin n))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mem_autFix_conjPerm_iff.mp (hK hx)
  rw [← Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective]
  exact Subgroup.card_dvd_of_le hle

theorem noCfgS429_alternatingGroup_eleven :
    NoCfgS429 (alternatingGroup (Fin 11)) := by
  intro A σ K hc
  obtain ⟨τ, rfl⟩ := conjPerm_surjective (by norm_num : 11 = 5 ∨ 7 ≤ 11) σ
  have hτ3 : τ ^ 3 = 1 := conjPerm_injective (by norm_num)
    (by rw [map_pow, hc.isE27.1.2 _ hc.mem, map_one])
  have hτ1 : τ ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
  rcases isThreeCycle_or_exists_card_centralizer hτ3 hτ1 with h3c | ⟨k, hk2, hk3, hcard⟩
  · obtain ⟨hΩ, ⟨φ⟩⟩ := exists_mulEquiv_alternatingGroup_of_isThreeCycle (by norm_num) h3c hc
    exact not_isType429_of_alternating_eight hΩ φ hc.isType
  · haveI := hc.isPerfect
    have h1 := le_card_of_isType429 hc.isType
    have h2 : Nat.card (K ⧸ CFSG.pCore 2 K) ≤ Nat.card K :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h3 : Nat.card K ≤ Nat.card (autFix (conjPerm 11 τ)) :=
      Subgroup.card_le_of_le hc.le_autFix
    have h4 := card_autFix_conjPerm_le τ
    rw [hcard] at h4
    have h5 : (11 - 3 * k).factorial * 3 ^ k * k.factorial ≤ 2160 := by
      have : k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl <;> decide
    omega

theorem noCfgS429_alternatingGroup_twelve :
    NoCfgS429 (alternatingGroup (Fin 12)) := by
  intro A σ K hc
  obtain ⟨τ, rfl⟩ := conjPerm_surjective (by norm_num : 12 = 5 ∨ 7 ≤ 12) σ
  have hτ3 : τ ^ 3 = 1 := conjPerm_injective (by norm_num)
    (by rw [map_pow, hc.isE27.1.2 _ hc.mem, map_one])
  have hτ1 : τ ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
  rcases isThreeCycle_or_exists_card_centralizer hτ3 hτ1 with h3c | ⟨k, hk2, hk3, hcard⟩
  · obtain ⟨hΩ, ⟨φ⟩⟩ := exists_mulEquiv_alternatingGroup_of_isThreeCycle (by norm_num) h3c hc
    exact not_isType429_of_alternating_nine hΩ φ hc.isType
  · haveI := hc.isPerfect
    have h1 := le_card_of_isType429 hc.isType
    have hdvd : Nat.card (K ⧸ CFSG.pCore 2 K) ∣
        Nat.card (Subgroup.centralizer ({τ} : Set (Perm (Fin 12)))) :=
      (Subgroup.card_quotient_dvd_card _).trans (card_dvd_card_centralizer hc.le_autFix)
    rw [hcard] at hdvd
    have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl
    · exact not_isType429_of_card_dvd hc.isType hdvd
    · have h6 := Nat.le_of_dvd (by decide) hdvd
      have h7 : (12 - 3 * 3).factorial * 3 ^ 3 * Nat.factorial 3 = 972 := by decide
      omega
    · have h6 := Nat.le_of_dvd (by decide) hdvd
      have h7 : (12 - 3 * 4).factorial * 3 ^ 4 * Nat.factorial 4 = 1944 := by decide
      omega

theorem rowSOf429_five_eleven :
    ∀ n : ℕ, 11 ≤ n → n ≤ 12 → RowSOf429 (alternatingGroup (Fin n)) := by
  intro n h11 h12
  have : n = 11 ∨ n = 12 := by omega
  rcases this with rfl | rfl
  · exact rowSOf429_of_noCfgS429 noCfgS429_alternatingGroup_eleven
  · exact rowSOf429_of_noCfgS429 noCfgS429_alternatingGroup_twelve

end CFSG.RankThree.PartTwo.Sec4.RonanK429
