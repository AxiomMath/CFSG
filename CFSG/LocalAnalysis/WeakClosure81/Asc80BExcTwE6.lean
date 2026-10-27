module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTwisted
import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillsRoot
import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralTwo
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcKilled
public import CFSG.ClassicalInvolution.Balance.Q27D4Parts
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Killed
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.Balance.Q27 (InvolutionCentralizersGenerate)
open CFSG.LieType.SeitzGeneration.ExcWideThree (TwLangData)

theorem twisted_descent_E6_three {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (3 ^ f))
    {x : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hx : x ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hxF : twistHom TwistTag.E6 (AlgebraicClosure K) Fr x = x) :
    ∃ u ∈ twistedE6RootGroup K σ, baseChangeGL (algebraMap K (AlgebraicClosure K)) u = x := by
  obtain ⟨-, hmul, hder, ⟨k, hk⟩, hTcard, -, -⟩ :=
    CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order (ℓ := 3) (f := f)
      Nat.prime_three hf K hK σ.toRingHom hσ (AlgebraicClosure K) Fr hFr
  set R := CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr with hR
  set T := graphFixedTorus TwistTag.E6 (AlgebraicClosure K) Fr with hT
  set C := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K (AlgebraicClosure K))) with hC
  have hle : C ≤ R := by
    intro c hc
    have hmem : c ∈ (R : Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) := by
      rw [hmul]
      simpa using Set.mul_mem_mul (T.one_mem) hc
    exact hmem
  have hNR : C.subgroupOf R = ⁅(⊤ : Subgroup R), ⊤⁆ := by
    have h1 : ⁅CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr,
        CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr⁆ =
        Subgroup.map (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr).subtype
          ⁅(⊤ : Subgroup
            (CFSG.Blueprint.twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr)), ⊤⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← hder, h1]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  have hnorm : (C.subgroupOf R).Normal := by
    rw [hNR]
    exact Subgroup.commutator_normal (⊤ : Subgroup R) (⊤ : Subgroup R)
  have hTR : T ≤ R := graphFixedTorus_le TwistTag.E6 (AlgebraicClosure K) Fr
  have hsup : T.subgroupOf R ⊔ C.subgroupOf R = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hy' : (y : ModGL TwistTag.E6.tag (AlgebraicClosure K)) ∈
        (R : Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) := hy
    rw [hmul, Set.mem_mul] at hy'
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    have e : (⟨a * b, hy⟩ : R) = ⟨a, hTR ha⟩ * ⟨b, hle hb⟩ := rfl
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 ha))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hb))
  have hindex : (C.subgroupOf R).index * Nat.card ↥(T ⊓ C) = Nat.card T := by
    have h1 := Subgroup.relIndex_sup_right (H := T.subgroupOf R) (K := C.subgroupOf R)
    rw [hsup, Subgroup.relIndex_top_right] at h1
    have h2 := Subgroup.relIndex_mul_card (H := C.subgroupOf R) (K := T.subgroupOf R)
    rw [← h1] at h2
    have e : C.subgroupOf R ⊓ T.subgroupOf R = (T ⊓ C).subgroupOf R := by
      ext y
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact and_comm
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hTR)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv] at h2
    exact h2
  have hTcard' : Nat.card T = ((3 ^ f) ^ 2 - 1) ^ 2 * (3 ^ f - 1) ^ 2 := hTcard
  have hnot : ¬ 3 ∣ Nat.card T := by
    intro hdvd
    rw [hTcard'] at hdvd
    have h0 : ((((3 ^ f) ^ 2 - 1) ^ 2 * (3 ^ f - 1) ^ 2 : ℕ) : ZMod 3) = 0 := by
      obtain ⟨m, hm⟩ := hdvd
      have hmul' : ((3 * m : ℕ) : ZMod 3) = ((3 : ℕ) : ZMod 3) * (m : ZMod 3) :=
        Nat.cast_mul 3 m
      rw [hm, hmul', ZMod.natCast_self 3, zero_mul]
    have hz : ((3 ^ f : ℕ) : ZMod 3) = 0 := by
      rw [Nat.cast_pow, show ((3 : ℕ) : ZMod 3) = 0 from ZMod.natCast_self 3]
      exact zero_pow (by omega : f ≠ 0)
    have ha : (1 : ℕ) ≤ (3 ^ f) ^ 2 := by
      have := Nat.one_le_pow f 3 (by norm_num)
      nlinarith
    have hb : (1 : ℕ) ≤ 3 ^ f := Nat.one_le_pow f 3 (by norm_num)
    have e1 : (((3 ^ f) ^ 2 - 1 : ℕ) : ZMod 3) = -1 := by
      rw [Nat.cast_sub ha, Nat.cast_pow, Nat.cast_one, hz]
      norm_num
    have e2 : ((3 ^ f - 1 : ℕ) : ZMod 3) = -1 := by
      rw [Nat.cast_sub hb, hz]
      norm_num
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, e1, e2] at h0
    norm_num at h0
  have hdvd : 3 ^ k ∣ Nat.card T := ⟨Nat.card ↥(T ⊓ C), by rw [← hindex, hk]⟩
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exact absurd ((dvd_pow_self 3 (by omega : k ≠ 0)).trans hdvd) hnot
  have hidx1 : (C.subgroupOf R).index = 1 := by rw [hk, hk0, pow_zero]
  have hCtop : C.subgroupOf R = ⊤ := Subgroup.index_eq_one.1 hidx1
  have hxR : x ∈ R :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).2 ⟨hx, hxF⟩
  have hxR' : (⟨x, hxR⟩ : R) ∈ C.subgroupOf R := by
    rw [hCtop]
    exact Subgroup.mem_top _
  have hxC : x ∈ C := Subgroup.mem_subgroupOf.1 hxR'
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.1 hxC
  exact ⟨u, hu, hux⟩

theorem twE6KillRoot_all
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ) (hσ : ∀ c, σ c = c ^ q)
    (hK : Nat.card K = q ^ 2) (A : Subgroup (ModGL TwistTag.E6.tag K)) (D : TwLangData K σ q A)
    (α : Fin TwistTag.E6.tag.rank → ℤ) (hα : IsRoot TwistTag.E6.tag α)
    (hk : ∀ x ∈ A, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∧ rootChar a α = 1) :
    ∃ u : ModGL TwistTag.E6.tag K, u ∈ twistedE6RootGroup K σ ∧ u ≠ 1 ∧
      (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧ ∀ x ∈ A, Commute u x := by
  by_cases h3 : ringChar K = 3
  · classical
    have hK1 : 1 < Nat.card K := Finite.one_lt_card
    have hq2 : 2 ≤ q := by
      by_contra h
      push Not at h
      interval_cases q <;> norm_num at hK <;> omega
    obtain ⟨hpr, f, hf1, hqf⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.exists_pow_ringChar_of_card_sq K q hK hq2
    set p := ringChar K with hp_def
    have : Fact p.Prime := ⟨hpr⟩
    have : CharP (AlgebraicClosure K) p :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
    have hFrEq : D.Fr = iterateFrobenius (AlgebraicClosure K) p f :=
      RingHom.ext fun c => by rw [D.hFr c, iterateFrobenius_def, hqf]
    set M : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)) :=
      A.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (MulAut.conj D.c).toMonoidHom)
      with hM
    have hMmem : ∀ z ∈ M, ∃ x ∈ A,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) = z := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
      exact ⟨x, hx, rfl⟩
    have hT : ∀ z ∈ M, D.g0⁻¹ * z * D.g0 ∈
        CFSG.RankThree.PartOne.KE.twistedTorusOf
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) D.v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) D.Fr) := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hMmem z hz
      obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.1 (D.hc x hx)
      have hsz' : D.g0 * s * D.g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
          (D.c * x * D.c⁻¹) := hsz
      have hs_eq : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (D.c * x * D.c⁻¹) * D.g0 = s := by
        rw [← hsz']
        group
      rw [hs_eq]
      exact hs
    have hkM : ∀ z ∈ M, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ * z * D.g0 ∧ rootChar a α = 1 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hMmem z hz
      obtain ⟨a, ha, hχ⟩ := hk x hx
      exact ⟨a, ha, hχ⟩
    obtain ⟨uL, huLad, huL1, huLp, huLF, huLc⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.twisted_kill_core (L := AlgebraicClosure K)
        p f hf1 D.Fr hFrEq D.v D.g0 D.hg0C D.hg0 M hT
        α hα hkM
    have hp3 : p = 3 := h3
    have hK3 : Nat.card K = (3 ^ f) ^ 2 := by rw [hK, hqf, hp3]
    have hσ3 : ∀ c, σ c = c ^ (3 ^ f) := fun c => by rw [hσ c, hqf, hp3]
    have hFr3 : ∀ c, D.Fr c = c ^ (3 ^ f) := fun c => by rw [D.hFr c, hqf, hp3]
    obtain ⟨u₀, hu₀C, hu₀⟩ :=
      twisted_descent_E6_three hf1 K hK3 σ hσ3 D.Fr hFr3 huLad huLF
    have hcN : D.c⁻¹ ∈
        Subgroup.normalizer (twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedE6InndiagGL_le_normalizer K σ
        (inv_mem D.hcI)
    set u : ModGL TwistTag.E6.tag K := D.c⁻¹ * u₀ * D.c with hu
    have huC : u ∈ twistedE6RootGroup K σ := by
      have h := (Subgroup.mem_normalizer_iff.1 hcN u₀).1 hu₀C
      rw [inv_inv] at h
      exact h
    refine ⟨u, huC, ?_, ⟨1, ?_⟩, ?_⟩
    · intro h
      have hu0 : u₀ = 1 := by
        rw [hu] at h
        calc u₀ = D.c * (D.c⁻¹ * u₀ * D.c) * D.c⁻¹ := by group
          _ = 1 := by rw [h]; group
      apply huL1
      rw [← hu₀, hu0, map_one]
    · have hu₀p : u₀ ^ p = 1 := (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))) (by
        rw [map_pow, hu₀, huLp, map_one])
      rw [pow_one, hu, show D.c⁻¹ * u₀ * D.c = D.c⁻¹ * u₀ * (D.c⁻¹)⁻¹ by rw [inv_inv], conj_pow,
        hu₀p]
      group
    · intro x hx
      have hz : baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) ∈ M :=
        Subgroup.mem_map_of_mem _ hx
      have hcomm := huLc _ hz
      rw [← hu₀] at hcomm
      have key0 : u₀ * (D.c * x * D.c⁻¹) = (D.c * x * D.c⁻¹) * u₀ := by
        apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
        rw [map_mul (baseChangeGL (algebraMap K (AlgebraicClosure K))) u₀ (D.c * x * D.c⁻¹),
          map_mul (baseChangeGL (algebraMap K (AlgebraicClosure K))) (D.c * x * D.c⁻¹) u₀]
        exact hcomm
      show u * x = x * u
      calc u * x = D.c⁻¹ * (u₀ * (D.c * x * D.c⁻¹)) * D.c := by rw [hu]; group
        _ = D.c⁻¹ * ((D.c * x * D.c⁻¹) * u₀) * D.c := by rw [key0]
        _ = x * u := by rw [hu]; group
  · exact CFSG.LieType.SeitzGeneration.ExcHighThree.twE6KillRoot_proof K σ q h3 hσ hK A D α hα hk

theorem exists_twLangData_four {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (q : ℕ) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (hK2 : ringChar K ≠ 2) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAC : A ≤ twistedE6RootGroup K σ) (hA : ∀ x ∈ A, x ^ 2 = 1) (hcard : Nat.card A = 2 ^ 2) :
    ∃ D : TwLangData K σ q A, D.c = 1 := by
  classical
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have hx2 : x * x = 1 := by rw [← sq]; exact hA x hx
    have hy2 : y * y = 1 := by rw [← sq]; exact hA y hy
    have hyx2 : y * x * (y * x) = 1 := by rw [← sq]; exact hA _ (A.mul_mem hy hx)
    calc x * y = x⁻¹ * y⁻¹ := by
          rw [inv_eq_of_mul_eq_one_right hx2, inv_eq_of_mul_eq_one_right hy2]
      _ = (y * x)⁻¹ := (mul_inv_rev y x).symm
      _ = y * x := inv_eq_of_mul_eq_one_right hyx2
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    interval_cases q <;> norm_num at hK <;> omega
  obtain ⟨hpr, f, hf1, hqf⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_pow_ringChar_of_card_sq K q hK hq2
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp_def
  have : Fact p.Prime := ⟨hpr⟩
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) p f
  have hFr : ∀ c, Fr c = c ^ q := fun c => by rw [iterateFrobenius_def, ← hqf]
  have hle : twistedE6RootGroup K σ ≤ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le (t := TwistTag.E6) (K := K) (σ := σ.toRingHom)).trans inf_le_left
  let A' : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)) :=
    A.map (baseChangeGL (algebraMap K (AlgebraicClosure K)))
  have hA'le : A' ≤ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rintro _ ⟨x, hx, rfl⟩
    exact baseChangeGL_mem_adjointGroup _ (hle (hAC hx))
  have hA'comm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hA'2 : ∀ x ∈ A', x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hA x hx, map_one]
  have hA'card : Nat.card A' = 2 ^ 2 := by
    rw [Subgroup.card_map_of_injective (baseChangeGL_injective _), hcard]
  have hK'2 : ¬ 2 ∣ Nat.card K := by
    intro h
    obtain ⟨m, hr, hcK⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hcK] at h
    exact hK2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  obtain ⟨g, hg, hgA⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.planesToralBar_two (τ := .E6) (by simp)
      K hK'2 A' hA'le hA'comm hA'2 hA'card
  have hFix : ∀ x ∈ A', twistHom TwistTag.E6 (AlgebraicClosure K) Fr x = x := by
    rintro _ ⟨x, hx, rfl⟩
    exact CFSG.LieType.SeitzGeneration.ExcHighThree.twBase_twistHom_fix K σ q Fr hσ hFr x
      (hAC hx)
  obtain ⟨v, g0, hg0C, hg0, hmem⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_lang_torus_of_conj_torus_twisted
      (L := AlgebraicClosure K) (ℓ := p) TwistTag.E6 f hf1 hFix hg hgA
  refine ⟨⟨v, Fr, hFr, g0, hg0C, hg0, 1, one_mem _, ?_⟩, rfl⟩
  intro x hx
  have hmem' := hmem (baseChangeGL (algebraMap K (AlgebraicClosure K)) x)
    (Subgroup.mem_map_of_mem _ hx)
  simpa only [one_mul, inv_one, mul_one] using hmem'

private lemma rootChar_eq_one_of_two_dvd {L : Type} [Field L]
    {a : Fin TwistTag.E6.tag.rank → Lˣ} {k : Fin TwistTag.E6.tag.rank → ℕ}
    (hak : ∀ i, a i = (-1 : Lˣ) ^ k i)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hd : (2 : ℤ) ∣ ∑ i, α i * (k i : ℤ)) :
    rootChar a α = 1 := by
  obtain ⟨m, hm⟩ := hd
  have h1 : rootChar a α = (-1 : Lˣ) ^ (∑ i, α i * (k i : ℤ)) := by
    rw [rootChar, ← CFSG.LieType.SeitzGeneration.ExcHighThree.prod_zpow_eq_zpow_sum_of_group]
    exact Finset.prod_congr rfl fun i _ => by
      rw [hak i, ← zpow_natCast, ← zpow_mul, mul_comm]
  rw [h1, hm, zpow_mul]
  have h2 : (-1 : Lˣ) ^ (2 : ℤ) = 1 := by
    norm_num
  rw [h2, one_zpow]

theorem twLangData_kills_two {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hA : ∀ x ∈ A, x ^ 2 = 1)
    (hcard : Nat.card A = 2 ^ 2) (D : TwLangData K σ q A) :
    ∃ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α ∧
      ∀ x ∈ A, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∧ rootChar a α = 1 := by
  classical
  let ψ : ModGL TwistTag.E6.tag K →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    (MulAut.conj D.g0⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (MulAut.conj D.c).toMonoidHom)
  have hψ : ∀ x, ψ x = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 := fun _ => rfl
  have hψt : ∀ x ∈ A, ψ x ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    intro x hx
    obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.1 (D.hc x hx)
    have hs' : ψ x = s := by
      rw [hψ, ← hsz]
      change D.g0⁻¹ * (D.g0 * s * D.g0⁻¹) * D.g0 = s
      group
    rw [hs']
    exact (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hs).1
  have hdiag : ∀ x ∈ A, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit TwistTag.E6.tag a = ψ x ∧ ∀ i, a i ^ 2 = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ :=
      CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup
        (hψt x hx)
    refine ⟨a, ha, fun i => ?_⟩
    have e1 : rootDiagUnit TwistTag.E6.tag (a ^ 2) = (rootDiagUnit TwistTag.E6.tag a) ^ 2 :=
      map_pow (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K)) a 2
    have e2 : rootDiagUnit TwistTag.E6.tag (1 : Fin TwistTag.E6.tag.rank →
        (AlgebraicClosure K)ˣ) = 1 :=
      map_one (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K))
    have h2 : rootDiagUnit TwistTag.E6.tag (a ^ 2) = rootDiagUnit TwistTag.E6.tag 1 := by
      rw [e1, ha, e2, ← map_pow, hA x hx, map_one]
    have h4 : a ^ 2 = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h2
    simpa using congrFun h4 i
  have hpow : ∀ b : (AlgebraicClosure K)ˣ, b ^ 2 = 1 →
      ∃ k : ℕ, b = (-1 : (AlgebraicClosure K)ˣ) ^ k := by
    intro b hb
    have hb' : (b : AlgebraicClosure K) ^ 2 = 1 := by
      have := congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K)) hb
      simpa using this
    rcases (sq_eq_one_iff (R := AlgebraicClosure K)).1 hb' with h | h
    · exact ⟨0, Units.ext (by simpa using h)⟩
    · exact ⟨1, Units.ext (by simpa using h)⟩
  obtain ⟨x₁, hx₁, x₂, hx₂, -, -, hgen⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_gens_of_plane (p := 2) hA hcard
  obtain ⟨a₁, ha₁, hc₁⟩ := hdiag x₁ hx₁
  obtain ⟨a₂, ha₂, hc₂⟩ := hdiag x₂ hx₂
  choose k₁ hk₁ using fun i => hpow (a₁ i) (hc₁ i)
  choose k₂ hk₂ using fun i => hpow (a₂ i) (hc₂ i)
  obtain ⟨α, hα, hd₁, hd₂⟩ := exists_root_kills_two (Or.inr (Or.inl rfl)) k₁ k₂
  refine ⟨α, hα, ?_⟩
  set Sg : Subgroup (ModGL TwistTag.E6.tag K) :=
    ((CFSG.LieType.SeitzGeneration.ExcHighThree.rootCharHom (L := AlgebraicClosure K) α).ker.map
      (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K))).comap ψ
  have hmemS : ∀ (x : ModGL TwistTag.E6.tag K)
      (a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ),
      rootDiagUnit TwistTag.E6.tag a = ψ x → rootChar a α = 1 → x ∈ Sg := by
    intro x a hax hα1
    exact Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨a, hα1, hax⟩)
  have hx₁S : x₁ ∈ Sg := hmemS x₁ a₁ ha₁ (rootChar_eq_one_of_two_dvd hk₁ hd₁)
  have hx₂S : x₂ ∈ Sg := hmemS x₂ a₂ ha₂ (rootChar_eq_one_of_two_dvd hk₂ hd₂)
  have hAS : A ≤ Sg := hgen.trans ((Subgroup.closure_le Sg).2 (by
    rintro y (rfl | rfl)
    · exact hx₁S
    · exact hx₂S))
  intro x hx
  obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (hAS hx))
  exact ⟨a, hax.trans (hψ x), ha⟩

theorem exists_rElement_commute_four_twistedE6 {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (q : ℕ) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2) (hK2 : ringChar K ≠ 2)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAC : A ≤ twistedE6RootGroup K σ)
    (hA : ∀ x ∈ A, x ^ 2 = 1) (hcard : Nat.card A = 2 ^ 2) :
    ∃ u : ModGL TwistTag.E6.tag K, u ∈ twistedE6RootGroup K σ ∧ u ≠ 1 ∧
      (∃ n : ℕ, u ^ (ringChar K ^ n) = 1) ∧ ∀ x ∈ A, Commute u x := by
  obtain ⟨D, -⟩ := exists_twLangData_four σ q hσ hK hK2 hAC hA hcard
  obtain ⟨α, hα, hk⟩ := twLangData_kills_two hA hcard D
  exact twE6KillRoot_all K σ q hσ hK A D α hα hk

end CFSG.LocalAnalysis.WeakClosure81
