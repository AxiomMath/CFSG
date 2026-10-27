module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem21Post
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7One

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped commutatorElement

theorem lem12221_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) : Lem12221 := by
  intro G _ _ T L V H P U I h n p hyp hNE hC hpre
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, -, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨hHs, hsol, -, -, -, hPH, -, -, -, hhP, -, hI, hUI, -, -, -, hUK, -⟩ := hpre
  have hTH : T ≤ H := hHs.1.1
  have hhH : h ∈ H := hPH hhP
  have hIH : I ≤ H := by
    rw [hI]
    refine sup_le (hVT.trans hTH) fun y hy => ?_
    rw [Lem21Post.mem_conjugate_iff] at hy
    have hy' : h⁻¹ * (h * y * h⁻¹) * h ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hhH) ((hVT.trans hTH) hy)) hhH
    simpa [mul_assoc] using hy'
  have hUH : U ≤ H := (hUI ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 I).trans hIH
  have hU2 : IsPGroup 2 ↥U := hUI ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I
  have hIU : I ≤ Subgroup.normalizer (U : Set G) :=
    hUI ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I
  have hmin := (Lem7.minParabolic h331 hyp hHs).subgroupOf
  obtain ⟨q, hq, hq2, hZ⟩ := hmin.exists_odd_prime_of_solvable hsol
  set N := CFSG.Open.pCore 2 ↥H with hN
  set φ := QuotientGroup.mk' N with hφ
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hker : φ.ker ≤ (H ⊓ Subgroup.normalizer (L : Set G)).subgroupOf H := by
    rw [hφ, QuotientGroup.ker_mk']
    exact hmin.pCore_le_M
  have hmY := hmin.map_of_surjective hsurj hker
  have hOY : CFSG.Open.pCore 2 (↥H ⧸ N) = ⊥ := B6.pCore_quotient_pCore
  have hZY : ∀ r : ℕ, r.Prime → r ∣ Nat.card (↥H ⧸ N) → r = 2 ∨ r = q :=
    fun r hr hrY => hZ r hr (hrY.trans (Subgroup.index_dvd_card _))
  have hKY : IsPGroup q (twoResidual (⊤ : Subgroup (↥H ⧸ N))) :=
    hmY.isPGroup_twoResidual_of_pCore_eq_bot hOY inferInstance hq hZY
  have hKn : (⊤ : Subgroup (↥H ⧸ N)) ≤
      Subgroup.normalizer (twoResidual (⊤ : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N)) :=
    le_normalizer_twoResidual ⊤
  have hcomm : ⁅U, oTwoUpper I⁆ ≤ pCoreOf 2 H := by
    rw [Subgroup.commutator_le]
    intro a ha k hk
    have hkI : k ∈ I := oTwoUpper_le I hk
    have hcU : ⁅a, k⁆ ∈ U := by
      have hka : k * a⁻¹ * k⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hIU hkI) a⁻¹).mp (U.inv_mem ha)
      have e1 : ⁅a, k⁆ = a * (k * a⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
      rw [e1]
      exact U.mul_mem ha hka
    have hkK : (⟨k, hIH hkI⟩ : ↥H) ∈ twoResidual (⊤ : Subgroup ↥H) := by
      rw [B6.twoResidual_top_eq_subgroupOf H, Subgroup.mem_subgroupOf]
      exact oTwoUpper_le_of_pow_mem (twoResidual_isTwoQuotient H) (oTwoUpper_mono hIH hk)
    have hkK' : φ ⟨k, hIH hkI⟩ ∈ twoResidual (⊤ : Subgroup (↥H ⧸ N)) := by
      rw [← B6.twoResidual_map_top hsurj]
      exact Subgroup.mem_map_of_mem φ hkK
    set c : ↥H := ⟨⁅a, k⁆, hUH hcU⟩ with hc
    have hcφ : φ c = φ ⟨a, hUH ha⟩ * φ ⟨k, hIH hkI⟩ * (φ ⟨a, hUH ha⟩)⁻¹ *
        (φ ⟨k, hIH hkI⟩)⁻¹ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      rfl
    have hcK : φ c ∈ twoResidual (⊤ : Subgroup (↥H ⧸ N)) := by
      rw [hcφ]
      refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hkK')
      exact (Subgroup.mem_normalizer_iff.mp (hKn (Subgroup.mem_top _)) _).mp hkK'
    obtain ⟨j, hj⟩ := hU2 ⟨⁅a, k⁆, hcU⟩
    have hj' : (φ c) ^ 2 ^ j = 1 := by
      rw [← map_pow]
      have : c ^ 2 ^ j = 1 := Subtype.ext (by simpa [hc] using congrArg Subtype.val hj)
      rw [this, map_one]
    obtain ⟨i, hi⟩ := hKY ⟨φ c, hcK⟩
    have hi' : (φ c) ^ q ^ i = 1 := by simpa using congrArg Subtype.val hi
    have hcop : Nat.Coprime (2 ^ j) (q ^ i) :=
      Nat.Coprime.pow j i ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
    have hord : orderOf (φ c) = 1 :=
      Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj')
        (orderOf_dvd_of_pow_eq_one hi'))
    have hc1 : φ c = 1 := orderOf_eq_one_iff.mp hord
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc1
    exact ⟨c, hc1, rfl⟩
  exact hUK.le.trans hcomm

theorem lem12221_23_of_steps (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (hpick : Lem12220PickFull) (h22 : Lem12222) (h23 : Lem12223) : Lem12221_23 :=
  lem12221_23_of hpick (lem12221_of h331 h1222) h22 h23 (lem12223Post_of h1222)

end CFSG.Quasithin.H13
