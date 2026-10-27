module

public import CFSG.Quasithin.Background.A1a
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

theorem mem_pResidual_of_not_dvd_orderOf {p : ℕ} (hp : p.Prime) {K : Type*} [Group K] {x : K}
    (hx : ¬ p ∣ orderOf x) : x ∈ pResidual p K := by
  rw [pResidual]
  simp only [Subgroup.mem_iInf]
  intro N hNn hN
  obtain ⟨k, hk⟩ := hN x
  have hcop : Nat.Coprime (p ^ k) (orderOf x) :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hx).pow_left k
  exact Subgroup.zpowers_le.mpr hk (mem_zpowers_pow_iff.mpr hcop)

theorem isNilpotent_of_pResidual_le_centralizer {K : Type*} [Group K] [Finite K]
    [Group.IsSolvable K]
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card (genFittingFitting K) →
      pResidual p K ≤ Subgroup.centralizer (CFSG.Open.pCore p K : Set K)) :
    (∀ q : ℕ, q.Prime → q ∣ Nat.card K → q ∣ Nat.card (genFittingFitting K)) ∧
      genFittingFitting K = ⊤ ∧ Group.IsNilpotent K := by
  classical
  have hFdef : genFittingFitting K = CFSG.fittingSubgroup K := rfl
  rw [hFdef] at h ⊢
  set F : Subgroup K := CFSG.fittingSubgroup K with hF
  have hCent : Subgroup.centralizer (F : Set K) ≤ F :=
    CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance
  have hH : ∀ p : ℕ, p.Prime → p ∣ Nat.card F → ∀ x : K, ¬ p ∣ orderOf x →
      ∀ u ∈ CFSG.pCore p K, u * x = x * u := by
    intro p hp hpF x hx u hu
    have hxres := mem_pResidual_of_not_dvd_orderOf hp hx
    have hxc := Subgroup.mem_centralizer_iff.mp (h p hp hpF hxres)
    exact hxc u (by assumption)
  have hbot : ∀ p : ℕ, p.Prime → ¬ p ∣ Nat.card F → CFSG.pCore p K = ⊥ := by
    intro p hp hpF
    have := Fact.mk hp
    have hle : CFSG.pCore p K ≤ F := CFSG.pCore_le_fitting K p
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp (CFSG.pCore_isPGroup (p := p) (G := K))
    have hdvd : Nat.card (CFSG.pCore p K) ∣ Nat.card F := Subgroup.card_dvd_of_le hle
    have hn0 : n = 0 := by
      by_contra hne
      exact hpF ((dvd_pow_self p hne).trans (hn ▸ hdvd))
    rw [hn0, pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq _ hn
  have hS1 : ∀ q : ℕ, q.Prime → q ∣ Nat.card K → q ∣ Nat.card F := by
    intro q hq hqK
    by_contra hqF
    have := Fact.mk hq
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) q hqK
    have hxC : Subgroup.zpowers x ≤ Subgroup.centralizer (F : Set K) := by
      refine CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores ?_
      intro r
      have hrp : r.1.1.Prime := Nat.prime_of_mem_primeFactors r.1.2
      by_cases hrF : r.1.1 ∣ Nat.card F
      · have hrq : ¬ r.1.1 ∣ orderOf x := by
          rw [hx]
          intro hdvd
          exact hqF (((Nat.prime_dvd_prime_iff_eq hrp hq).mp hdvd) ▸ hrF)
        rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_iff.mpr fun u hu => hH r.1.1 hrp hrF x hrq u hu
      · rw [hbot r.1.1 hrp hrF, Subgroup.zpowers_le]
        refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
        have : u = 1 := Subgroup.mem_bot.mp hu
        rw [this]; simp
    have hxF : x ∈ F := hCent (hxC (Subgroup.mem_zpowers x))
    have := Subgroup.orderOf_dvd_natCard F hxF
    rw [hx] at this
    exact hqF this
  refine ⟨hS1, ?_⟩
  have hall : ∀ q : ℕ, q.Prime → ∀ x : K, ¬ q ∣ orderOf x →
      ∀ u ∈ CFSG.pCore q K, u * x = x * u := by
    intro q hq x hx u hu
    by_cases hqF : q ∣ Nat.card F
    · exact hH q hq hqF x hx u hu
    · have : u = 1 := Subgroup.mem_bot.mp (hbot q hq hqF ▸ hu)
      rw [this]; simp
  have hFprimes : F = ⨆ q : Nat.Primes, CFSG.pCore (q : ℕ) K := by
    apply le_antisymm
    · rw [hF, CFSG.fitting_eq_sup_pCore K]
      exact iSup_le fun r =>
        le_iSup_of_le ⟨r.1.1, Nat.prime_of_mem_primeFactors r.1.2⟩ le_rfl
    · refine iSup_le fun q => ?_
      have := Fact.mk q.2
      exact CFSG.pCore_le_fitting K q
  have hS2 : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → ∀ x : K, (∃ j : ℕ, x ^ p ^ j = 1) → x ∈ F := by
    intro p hp hpK x ⟨j, hxj⟩
    have hpF : p ∣ Nat.card F := hS1 p hp hpK
    have := Fact.mk hp
    obtain ⟨O, hO⟩ : ∃ O : Subgroup K,
        O = ⨆ q : {q : Nat.Primes // (q : ℕ) ≠ p}, CFSG.pCore (q.1 : ℕ) K := ⟨_, rfl⟩
    have hOn : O.Normal := by
      rw [hO]
      exact Subgroup.iSup_normal _
    have hnormO : Subgroup.normalizer (O : Set K) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hOn
    have hFO : F ≤ O ⊔ CFSG.pCore p K := by
      rw [hFprimes]
      refine iSup_le fun q => ?_
      by_cases hq : (q : ℕ) = p
      · rw [hq]; exact le_sup_right
      · refine le_trans ?_ le_sup_left
        rw [hO]
        exact le_iSup (fun q : {q : Nat.Primes // (q : ℕ) ≠ p} => CFSG.pCore (q.1 : ℕ) K) ⟨q, hq⟩
    have hpO : ∀ y : K, (∃ j : ℕ, y ^ p ^ j = 1) → y ∈ Subgroup.centralizer (O : Set K) := by
      rintro y ⟨j, hyj⟩
      have hzp : Subgroup.zpowers y ≤ Subgroup.centralizer (O : Set K) := by
        rw [hO]
        refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ fun q => ?_
        have hqp : (q.1 : ℕ).Prime := q.1.2
        have hq : ¬ (q.1 : ℕ) ∣ orderOf y := by
          intro hdvd
          have h1 : (q.1 : ℕ) ∣ p ^ j := hdvd.trans (orderOf_dvd_of_pow_eq_one hyj)
          exact q.2 (((Nat.prime_dvd_prime_iff_eq hqp hp).mp (hqp.dvd_of_dvd_pow h1)))
        rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_iff.mpr fun u hu => hall _ hqp y hq u hu
      exact hzp (Subgroup.mem_zpowers y)
    have hFpO : ∀ f ∈ F, ¬ p ∣ orderOf f → f ∈ O := by
      intro f hf hfp
      have hmul : f ∈ ((O ⊔ CFSG.pCore p K : Subgroup K) : Set K) := hFO hf
      rw [Subgroup.coe_mul_of_right_le_normalizer_left O (CFSG.pCore p K)
        (by rw [hnormO]; exact le_top)] at hmul
      obtain ⟨b, hb, a, ha, rfl⟩ := hmul
      obtain ⟨e, he⟩ := CFSG.pCore_isPGroup (p := p) (G := K) ⟨a, ha⟩
      have hae : a ^ p ^ e = 1 := by simpa using congrArg Subtype.val he
      have hpow : (b * a) ^ p ^ e ∈ O :=
        A1a.pow_mem_of_pow_eq_one hb (by rw [hnormO]; exact Subgroup.mem_top a) hae
      have hcop : Nat.Coprime (p ^ e) (orderOf (b * a)) :=
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hfp).pow_left e
      exact Subgroup.zpowers_le.mpr hpow (mem_zpowers_pow_iff.mpr hcop)
    have hOnormal := hOn
    obtain ⟨Y, hY⟩ : ∃ Y : Subgroup K, Y = Subgroup.centralizer (O : Set K) := ⟨_, rfl⟩
    have hYn : Y.Normal := hY ▸ A1a.normal_centralizer_of_normal O
    have hYnil : Group.IsNilpotent Y := by
      have hcen : ∀ y : Y, ¬ p ∣ orderOf (y : K) → y ∈ Subgroup.center Y := by
        intro y hy
        have hyO' : ∀ u ∈ O, u * (y : K) = (y : K) * u :=
          Subgroup.mem_centralizer_iff.mp (hY ▸ y.2)
        have hFle : F ≤ Subgroup.centralizer ({(y : K)} : Set K) := by
          refine le_trans hFO (sup_le ?_ ?_)
          · intro u hu
            rw [Subgroup.mem_centralizer_iff]
            intro h' hh'
            rw [Set.mem_singleton_iff] at hh'
            rw [hh']
            exact (hyO' u hu).symm
          · intro u hu
            rw [Subgroup.mem_centralizer_iff]
            intro h' hh'
            rw [Set.mem_singleton_iff] at hh'
            rw [hh']
            exact (hall p hp y hy u hu).symm
        have hyC : (y : K) ∈ Subgroup.centralizer (F : Set K) := by
          rw [Subgroup.mem_centralizer_iff]
          intro f hf
          exact (Subgroup.mem_centralizer_iff.mp (hFle hf) y (Set.mem_singleton _)).symm
        have hyO : (y : K) ∈ O := hFpO _ (hCent hyC) hy
        rw [Subgroup.mem_center_iff]
        intro z
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp (hY ▸ z.2) _ hyO).symm
      let S' : Subgroup Y := Subgroup.closure {y : Y | ¬ p ∣ orderOf (y : K)}
      have hS'c : S' ≤ Subgroup.center Y := (Subgroup.closure_le _).mpr fun y hy => hcen y hy
      have hS'n : S'.Normal := ⟨fun s hs g => by
        have := Subgroup.mem_center_iff.mp (hS'c hs) g
        rw [this, mul_inv_cancel_right]
        exact hs⟩
      have hQp : IsPGroup p (Y ⧸ S') := by
        intro q
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
        obtain ⟨a, m, hm, hord⟩ :=
          Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' p hp.ne_one
        have hdvd : p ^ a ∣ orderOf y := ⟨m, hord⟩
        have hym : orderOf (y ^ p ^ a) = m := by
          rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, hord]
          exact Nat.mul_div_cancel_left m (pow_pos hp.pos a)
        have hmem : y ^ p ^ a ∈ S' := Subgroup.subset_closure (by
          show ¬ p ∣ orderOf ((y ^ p ^ a : Y) : K)
          rw [Subgroup.orderOf_coe, hym]
          exact hm)
        exact ⟨a, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hmem⟩
      have hQnil : Group.IsNilpotent (Y ⧸ S') := hQp.isNilpotent
      exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' S')
        (by rw [QuotientGroup.ker_mk']; exact hS'c)
    have hYF : Y ≤ F := le_sSup ⟨hYn, hYnil⟩
    exact hYF (hY ▸ hpO x ⟨j, hxj⟩)
  have hdvd : Nat.card K ∣ Nat.card F := by
    rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
    intro p hp
    by_cases hpK : p ∣ Nat.card K
    · have := Fact.mk hp
      let P : Sylow p K := default
      have hPF : (P : Subgroup K) ≤ F := fun x hx =>
        hS2 p hp hpK x (by
          obtain ⟨j, hj⟩ := P.isPGroup' ⟨x, hx⟩
          exact ⟨j, by simpa using congrArg Subtype.val hj⟩)
      have h1 : p ^ (Nat.card K).factorization p ∣ Nat.card F := by
        rw [← Sylow.card_eq_multiplicity P]
        exact Subgroup.card_dvd_of_le hPF
      exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h1
    · rw [Nat.factorization_eq_zero_of_not_dvd hpK]
      exact Nat.zero_le _
  have hFtop : F = ⊤ :=
    Subgroup.eq_top_of_card_eq F (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card F) hdvd)
  refine ⟨hFtop, ?_⟩
  have hnil : Group.IsNilpotent (⊤ : Subgroup K) := hFtop ▸ (inferInstance : Group.IsNilpotent F)
  exact Group.nilpotent_of_mulEquiv (Subgroup.topEquiv (G := K))

end CFSG.Quasithin
