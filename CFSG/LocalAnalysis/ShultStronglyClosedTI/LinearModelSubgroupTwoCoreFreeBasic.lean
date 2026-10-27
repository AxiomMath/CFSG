module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearSubgroup
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelSubgroupTorus

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearModel

open CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u

variable {K : Type u} [Field K] [Finite K]

omit [Finite K] in
theorem comap_sylow_normal_of_le_normalizer (A : Subgroup (PSL2MatrixGroup K))
    (P : Sylow 2 (PSL2MatrixGroup K))
    (hAN : A ≤ Subgroup.normalizer (P : Set (PSL2MatrixGroup K))) :
    ((P : Subgroup (PSL2MatrixGroup K)).comap A.subtype).Normal := by
  constructor
  intro s hs a
  change ((a * s * a⁻¹ : A) : PSL2MatrixGroup K) ∈ (P : Subgroup (PSL2MatrixGroup K))
  have h := (Subgroup.mem_normalizer_iff.mp (hAN a.property) (s : PSL2MatrixGroup K)).mp hs
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem two_core_free_sylow_normalizer_stronglyEmbedded {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (A : Subgroup (PSL2MatrixGroup K)) (hAeven : Even (Nat.card A))
    (hcore : CFSG.pCore 2 A = ⊥) (S : Sylow 2 A) (P : Sylow 2 (PSL2MatrixGroup K))
    (hSP : (S : Subgroup A).map A.subtype ≤ P) :
    CFSG.Open.fusionStronglyEmbedded
      ((Subgroup.normalizer (P : Set (PSL2MatrixGroup K))).comap A.subtype) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := (Subgroup.normalizer (P : Set (PSL2MatrixGroup K))).comap A.subtype
  have hSM : (S : Subgroup A) ≤ M := fun s hs =>
    Subgroup.le_normalizer (hSP (Subgroup.mem_map_of_mem A.subtype hs))
  have h2A : 2 ∣ Nat.card A := even_iff_two_dvd.mp hAeven
  refine ⟨?_, ?_, ?_⟩
  ·
    intro htop
    have hAN : A ≤ Subgroup.normalizer (P : Set (PSL2MatrixGroup K)) := by
      intro a ha
      have h : (⟨a, ha⟩ : A) ∈ M := htop ▸ Subgroup.mem_top _
      exact h
    let T := (P : Subgroup (PSL2MatrixGroup K)).comap A.subtype
    have hTnormal : T.Normal := comap_sylow_normal_of_le_normalizer A P hAN
    have hT2 : IsPGroup 2 T := P.isPGroup'.comap_of_injective A.subtype A.subtype_injective
    have hTcore : T ≤ CFSG.pCore 2 A := le_sSup ⟨hTnormal, hT2⟩
    have hST : (S : Subgroup A) ≤ T := fun s hs => hSP (Subgroup.mem_map_of_mem A.subtype hs)
    rw [hcore] at hTcore
    exact S.ne_bot_of_dvd_card h2A (le_bot_iff.mp (hST.trans hTcore))
  · exact even_iff_two_dvd.mpr ((S.dvd_card_of_dvd_card h2A).trans (Subgroup.card_dvd_of_le hSM))
  · intro g hg
    set Q : Sylow 2 (PSL2MatrixGroup K) := ((g : PSL2MatrixGroup K)⁻¹) • P
    have hQ : (Q : Subgroup (PSL2MatrixGroup K)) =
        (P : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj (g : PSL2MatrixGroup K)⁻¹).toMonoidHom :=
      rfl
    have hPQ : P ≠ Q := by
      intro h
      apply hg
      change (g : PSL2MatrixGroup K) ∈ Subgroup.normalizer (P : Set (PSL2MatrixGroup K))
      apply inv_mem_iff.mp
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      exact (congrArg (fun R : Sylow 2 (PSL2MatrixGroup K) =>
        (R : Subgroup (PSL2MatrixGroup K))) h).symm
    have hNQ : Subgroup.normalizer (Q : Set (PSL2MatrixGroup K)) =
        (Subgroup.normalizer (P : Set (PSL2MatrixGroup K))).map
          (MulAut.conj (g : PSL2MatrixGroup K)⁻¹).toMonoidHom := by
      change Subgroup.normalizer ((Q : Subgroup (PSL2MatrixGroup K)) :
        Set (PSL2MatrixGroup K)) = _
      rw [hQ, ← Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj _).bijective]
      rfl
    have hle : (M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom).map A.subtype ≤
        Subgroup.normalizer (P : Set (PSL2MatrixGroup K)) ⊓
          Subgroup.normalizer (Q : Set (PSL2MatrixGroup K)) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxM, hxM'⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hxM'
      refine ⟨hxM, ?_⟩
      rw [hNQ]
      exact ⟨(m : PSL2MatrixGroup K), hm, by simp⟩
    have hodd := odd_card_sylow_normalizer_inf hcard P Q hPQ
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective A.subtype_injective] at hdvd
    exact hodd.of_dvd_nat hdvd

theorem two_core_free_involutions_conjugate {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (A : Subgroup (PSL2MatrixGroup K)) (hAeven : Even (Nat.card A))
    (hcore : CFSG.pCore 2 A = ⊥) {u v : A} (hu : orderOf u = 2) (hv : orderOf v = 2) :
    IsConj u v := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 A := default
  obtain ⟨P, hSP⟩ := (S.isPGroup'.map A.subtype).exists_le_sylow
  have hM := two_core_free_sylow_normalizer_stronglyEmbedded hcard A hAeven hcore S P hSP
  have huI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution u :=
    ⟨(orderOf_eq_prime_iff.mp hu).2, (orderOf_eq_prime_iff.mp hu).1⟩
  have hvI : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution v :=
    ⟨(orderOf_eq_prime_iff.mp hv).2, (orderOf_eq_prime_iff.mp hv).1⟩
  obtain ⟨g, hg⟩ := (native_strong_embedding_of_order_conditions hM).involutions_conjugate huI hvI
  refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
  rw [← hg, inv_inv]
  rfl

theorem eq_bot_of_normal_odd_of_four_le {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (A : Subgroup (PSL2MatrixGroup K)) (S : Sylow 2 A) (hS : 4 ≤ Nat.card S)
    (N : Subgroup A) [hN : N.Normal] (hNodd : Odd (Nat.card N)) : N = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k ≤ 1 := by omega
    have h' : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime (G := (S : Subgroup A)) 2 (n := 2)
    (hk ▸ Nat.pow_dvd_pow 2 hk2)
  let : IsElementaryAbelian 2 S := psl2_even_subgroup_sylow_elementary f hcard A S
  have hSsq : ∀ x : (S : Subgroup A), x ^ 2 = 1 := fun x =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 _) x
  let : IsElementaryAbelian 2 E' :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
        ((IsElementaryAbelian.toIsMulCommutative (p := 2) (G := (S : Subgroup A))).is_comm.comm
          a b)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hSsq x) }
  let ι : E' →* A := (S : Subgroup A).subtype.comp E'.subtype
  let : MulDistribMulAction E' N := MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp ι)
  have hsmul : ∀ (e : E') (n : N), ((e • n : N) : A) = ι e * n * (ι e)⁻¹ := fun e n =>
    MulAut.conjNormal_apply _ _
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := E') (H := N)
    (by rw [hE']) (fun h => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h))
  have hfix : ∀ e : E', e ≠ 1 → CFSG.fixedPointSubgroup (Subgroup.zpowers e) N = ⊥ := by
    intro e he
    rw [eq_bot_iff]
    intro n hn
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hn
    have hn' : ι e * n * (ι e)⁻¹ = n := (hsmul e n).symm.trans (congrArg Subtype.val hn)
    have he1 : ι e ≠ 1 := fun h => he (by
      apply Subtype.ext
      apply Subtype.ext
      exact h)
    have heorder : orderOf ((ι e : A) : PSL2MatrixGroup K) = 2 := by
      rw [Subgroup.orderOf_coe]
      apply orderOf_eq_prime _ he1
      exact congrArg Subtype.val (hSsq (E'.subtype e))
    have hnodd : Odd (orderOf (((n : A) : PSL2MatrixGroup K))) := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hNodd.of_dvd_nat (orderOf_dvd_natCard n)
    have hcomm : ((n : A) : PSL2MatrixGroup K) * ((ι e : A) : PSL2MatrixGroup K) =
        ((ι e : A) : PSL2MatrixGroup K) * ((n : A) : PSL2MatrixGroup K) := by
      have h : (n : A) * ι e = ι e * n := by
        calc (n : A) * ι e = ι e * n * (ι e)⁻¹ * ι e := by rw [hn']
          _ = ι e * n := by group
      exact congrArg Subtype.val h
    have h1 := eq_one_of_odd_of_commute_involution hcard heorder hnodd hcomm
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext h1))
  have htop : (⊤ : Subgroup N) = ⊥ := by
    rw [← hgen]
    exact le_bot_iff.mp (iSup₂_le fun e he => (hfix e he).le)
  rw [eq_bot_iff]
  intro x hx
  have h : (⟨x, hx⟩ : N) ∈ (⊥ : Subgroup N) := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h))

theorem oddCore_eq_bot_of_four_le {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (A : Subgroup (PSL2MatrixGroup K)) (S : Sylow 2 A) (hS : 4 ≤ Nat.card S) :
    CFSG.oddCore A = ⊥ :=
  sSup_eq_bot.mpr fun N hN =>
    let : N.Normal := hN.1
    eq_bot_of_normal_odd_of_four_le hcard A S hS N hN.2

theorem exists_noncommuting_involutions {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (A : Subgroup (PSL2MatrixGroup K)) (hAeven : Even (Nat.card A))
    (hcore : CFSG.pCore 2 A = ⊥) :
    ∃ a b : A, orderOf a = 2 ∧ orderOf b = 2 ∧ a * b ≠ b * a := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  let S : Sylow 2 A := default
  let : IsElementaryAbelian 2 S := psl2_even_subgroup_sylow_elementary f hcard A S
  have hSsq : ∀ x ∈ (S : Subgroup A), x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian
  have hcommS : ∀ g : A,
      (S : Subgroup A) ≤ Subgroup.normalizer ((g • S : Sylow 2 A) : Set A) := by
    intro g s hs
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    change t ∈ (S : Subgroup A).map (MulAut.conj g).toMonoidHom at ht
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp ht
    have ht2 : ((MulAut.conj g).toMonoidHom t') ^ 2 = 1 := by
      rw [← map_pow, hSsq t' ht', map_one]
    by_cases ht1 : (MulAut.conj g).toMonoidHom t' = 1
    · rw [ht1, one_mul, mul_one]
    by_cases hs1 : s = 1
    · rw [hs1, one_mul, mul_one]
    exact hall _ s (orderOf_eq_prime ht2 ht1) (orderOf_eq_prime (hSsq s hs) hs1)
  have hnormal : (S : Subgroup A).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro g _
    have hle := le_sylow_of_le_normalizer (g • S) S.isPGroup' (hcommS g)
    have hcard' : Nat.card ((g • S : Sylow 2 A) : Subgroup A) ≤ Nat.card (S : Subgroup A) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hle hcard').symm
  have hSle : (S : Subgroup A) ≤ CFSG.pCore 2 A := le_sSup ⟨hnormal, S.isPGroup'⟩
  rw [hcore] at hSle
  exact S.ne_bot_of_dvd_card (even_iff_two_dvd.mp hAeven) (le_bot_iff.mp hSle)

end CFSG.ShultStronglyClosedTI.LinearModel
