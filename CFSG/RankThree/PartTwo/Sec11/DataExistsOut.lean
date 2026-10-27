module

public import CFSG.RankThree.PartTwo.Sec11.Omega

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace OutCyclic

open CFSG.RankThree.PartTwo.KFacts CFSG.GorensteinWalter
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

theorem exists_forall_map_eq_one_of_isCyclic {Γ C : Type*} [Group Γ] [Group C] [Finite Γ]
    (ψ : Γ →* C) {P : Subgroup Γ} (hP : IsCyclic (P.map ψ)) :
    ∃ σ₀ ∈ P, ∀ σ ∈ P, ∃ i : ℕ, ψ ((σ₀ ^ i)⁻¹ * σ) = 1 := by
  obtain ⟨⟨g, hg⟩, hgen⟩ := IsCyclic.exists_generator (α := P.map ψ)
  obtain ⟨σ₀, hσ₀, rfl⟩ := hg
  refine ⟨σ₀, hσ₀, fun σ hσ => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨ψ σ, ⟨σ, hσ, rfl⟩⟩)
  have hk' : ψ σ₀ ^ k = ψ σ := by simpa using congrArg Subtype.val hk
  have hpos : (0 : ℤ) < (orderOf σ₀ : ℤ) := by exact_mod_cast orderOf_pos σ₀
  refine ⟨(k % (orderOf σ₀ : ℤ)).toNat, ?_⟩
  have e : σ₀ ^ (k % (orderOf σ₀ : ℤ)).toNat = σ₀ ^ k := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne'), zpow_mod_orderOf]
  rw [e, map_mul, map_inv, map_zpow, hk', inv_mul_cancel]

theorem exists_forall_mem_of_mem_range {Γ C : Type*} [Group Γ] [Group C] [Finite Γ] [IsCyclic C]
    {D : Subgroup Γ} [D.Normal] (f : C →* Γ ⧸ D) {P : Subgroup Γ}
    (hP : ∀ σ ∈ P, QuotientGroup.mk' D σ ∈ f.range) :
    ∃ σ₀ ∈ P, ∀ σ ∈ P, ∃ i : ℕ, (σ₀ ^ i)⁻¹ * σ ∈ D := by
  have : IsCyclic f.range := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hle : P.map (QuotientGroup.mk' D) ≤ f.range := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact hP σ hσ
  obtain ⟨σ₀, hσ₀, h⟩ :=
    exists_forall_map_eq_one_of_isCyclic (QuotientGroup.mk' D) (Subgroup.isCyclic_of_le hle)
  exact ⟨σ₀, hσ₀, fun σ hσ => by
    obtain ⟨i, hi⟩ := h σ hσ
    exact ⟨i, (QuotientGroup.eq_one_iff _).mp hi⟩⟩

theorem exists_forall_isInnerAut_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ Q : Subgroup (MulAut Y), IsPGroup 3 Q →
      ∃ σ₀ ∈ Q, ∀ σ ∈ Q, ∃ i : ℕ, IsInnerAut ((σ₀ ^ i)⁻¹ * σ))
    {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P) :
    ∃ σ₀ ∈ P, ∀ σ ∈ P, ∃ i : ℕ, IsInnerAut ((σ₀ ^ i)⁻¹ * σ) := by
  obtain ⟨τ₀, ⟨σ₀, hσ₀, rfl⟩, h⟩ := hY _ (hP.map (MulAut.congr e).toMonoidHom)
  refine ⟨σ₀, hσ₀, fun σ hσ => ?_⟩
  obtain ⟨i, hi⟩ := h _ ⟨σ, hσ, rfl⟩
  refine ⟨i, ?_⟩
  change IsInnerAut ((MulAut.congr e σ₀ ^ i)⁻¹ * MulAut.congr e σ) at hi
  rwa [← map_pow, ← map_inv, ← map_mul, isInnerAut_congr] at hi

theorem exists_forall_isInnerAut_psl2 {K : Type*} [Field K] [Finite K]
    {P : Subgroup (MulAut (PSL2 K))} (hP : IsPGroup 3 P) :
    ∃ σ₀ ∈ P, ∀ σ ∈ P, ∃ i : ℕ, IsInnerAut ((σ₀ ^ i)⁻¹ * σ) := by
  let ψ : MulAut (PSL2 K) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  obtain ⟨σ₀, hσ₀, h⟩ := exists_forall_map_eq_one_of_isCyclic ψ (P := P) inferInstance
  refine ⟨σ₀, hσ₀, fun σ hσ => ?_⟩
  obtain ⟨i, hi⟩ := h σ hσ
  refine ⟨i, ?_⟩
  obtain ⟨g, hg⟩ := mem_range_pglAction_of_rightHom_eq_one hi
  have hmem : (σ₀ ^ i)⁻¹ * σ ∈ P := mul_mem (inv_mem (pow_mem hσ₀ i)) hσ
  obtain ⟨k, hk⟩ := hP ⟨_, hmem⟩
  have hk' : ((σ₀ ^ i)⁻¹ * σ) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hg' : g ^ 3 ^ k = 1 := pglAction_injective (by rw [map_pow, hg, hk', map_one])
  obtain ⟨x, hx⟩ := exists_toPGL_eq_of_pow_odd (Odd.pow (by decide)) hg'
  exact ⟨x, by rw [← hg, ← hx, pglAction_toPGL]⟩

theorem exists_forall_isInnerAut_projectiveSL {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) {P : Subgroup (MulAut (projectiveSL 3 K))} (hP : IsPGroup 3 P) :
    ∃ σ₀ ∈ P, ∀ σ ∈ P, ∃ i : ℕ, IsInnerAut ((σ₀ ^ i)⁻¹ * σ) := by
  obtain ⟨-, -, hDnorm, -⟩ := standard_outer_quotients (n := 3) (K := K)
  obtain ⟨hR, hgen⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  rw [hR] at hDnorm
  have : (linearAutGroup 3 K).Normal := ⟨fun d hd g =>
    hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨g, Subgroup.mem_top g⟩⟩
  have htrans := standard_automorphism_transport (K := K) (n := 3)
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  set π := QuotientGroup.mk' (linearAutGroup 3 K) with hπ
  set δ := dualAut 3 K with hδ
  have hfδ : ∀ τ : K ≃+* K, fieldAut 3 K τ * δ = δ * fieldAut 3 K τ := fun τ =>
    calc fieldAut 3 K τ * δ = δ * fieldAut 3 K τ * δ * δ := by rw [htrans.2.2.2.2.2.1]
      _ = δ * fieldAut 3 K τ := by rw [mul_assoc _ δ δ, htrans.2.2.2.1, mul_one]
  have hδ2 : π δ ^ 2 = 1 := by rw [← map_pow, pow_two, htrans.2.2.2.1, map_one]
  obtain ⟨σ₀, hσ₀, h⟩ := exists_forall_mem_of_mem_range (π.comp (fieldAut 3 K)) (P := P)
    (fun σ hσ => by
      obtain ⟨k, hk⟩ := hP ⟨σ, hσ⟩
      have hk' : σ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨A, τ, ε, -, rfl⟩ := hgen σ
      have hc : π (conjAut 3 K A) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (conjAut_mem_linearAutGroup A)
      have hcomm : Commute (π (fieldAut 3 K τ)) (π δ) := by
        change π _ * π _ = π _ * π _
        rw [← map_mul, ← map_mul, hfδ]
      set y := π (conjAut 3 K A * fieldAut 3 K τ * δ ^ ε) with hy
      have hy' : y = π (fieldAut 3 K τ) * π δ ^ ε := by
        rw [hy, map_mul, map_mul, hc, one_mul, map_pow]
      have hy2 : y ^ 2 = π (fieldAut 3 K τ) ^ 2 := by
        rw [hy', (hcomm.pow_right ε).mul_pow, ← pow_mul, mul_comm ε, pow_mul, hδ2, one_pow,
          mul_one]
      have hy3 : y ^ 3 ^ k = 1 := by rw [hy, ← map_pow, hk', map_one]
      obtain ⟨t, ht⟩ : ∃ t, 3 ^ k + 1 = 2 * t :=
        ⟨(3 ^ k + 1) / 2, by have := Nat.pow_mod 3 k 2; norm_num at this; omega⟩
      refine ⟨τ ^ (2 * t), ?_⟩
      rw [MonoidHom.comp_apply, map_pow, map_pow, pow_mul, ← hy2, ← pow_mul, ← ht, pow_succ,
        hy3, one_mul])
  exact ⟨σ₀, hσ₀, fun σ hσ => by
    obtain ⟨i, hi⟩ := h σ hσ
    exact ⟨i, isInnerAut_of_mem_linearAutGroup hK hi⟩⟩

theorem exists_forall_isInnerAut_unitaryPSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) (hq2 : 2 < p ^ f)
    (P : Subgroup (MulAut (unitaryPSU h 3))) :
    ∃ σ₀ ∈ P, ∀ σ ∈ P, ∃ i : ℕ, IsInnerAut ((σ₀ ^ i)⁻¹ * σ) := by
  have := h.finite
  have : (psuConj h).range.Normal := (stdPinnedPSU3_stable (h := h) hq2).normal
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  set π := QuotientGroup.mk' (psuConj h).range with hπ
  obtain ⟨σ₀, hσ₀, hσ⟩ := exists_forall_mem_of_mem_range (π.comp (psuField h)) (P := P)
    (fun σ _ => by
      obtain ⟨A, τ, rfl⟩ := exists_psuConj_mul_psuField hq2 σ
      have hc : π (psuConj h A) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (MonoidHom.mem_range.mpr ⟨A, rfl⟩)
      refine ⟨τ, ?_⟩
      rw [MonoidHom.comp_apply, map_mul, hc, one_mul])
  exact ⟨σ₀, hσ₀, fun σ hσ' => by
    obtain ⟨i, hi⟩ := hσ σ hσ'
    exact ⟨i, isInnerAut_of_mem_psuConj_range h hq hi⟩⟩

end OutCyclic

open OutCyclic KFacts CFSG.LocalAnalysis.ComponentInitial

theorem exists_forall_isInnerAut_of_isList1016 {X : Type} [Group X] [Finite X]
    (hX : Sec9.IsList1016 X) {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P) :
    ∃ σ₀ ∈ P, ∀ σ ∈ P, ∃ i : ℕ, IsInnerAut ((σ₀ ^ i)⁻¹ * σ) := by
  by_cases hL3 : ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)
  · obtain ⟨n, hn, hL⟩ := hL3
    have hq2 : 2 < 2 ^ (3 * n) :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
    rcases hL with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
    · have h : UnitaryFieldData 2 (3 * n) (GaloisField 2 (2 * (3 * n))) :=
        ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
      obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
      exact exists_forall_isInnerAut_of_mulEquiv (e.trans φ.symm)
        (fun Q _ => exists_forall_isInnerAut_unitaryPSU h hq hq2 Q) hP
    · obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 (3 * n))
      exact exists_forall_isInnerAut_of_mulEquiv (e.trans φ)
        (fun Q hQ => exists_forall_isInnerAut_projectiveSL
          (by rwa [GaloisField.card 2 (3 * n) (by omega)]) hQ) hP
  · obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_mulEquiv_psl2_of_isList1016 hX hL3
    exact exists_forall_isInnerAut_of_mulEquiv e (fun Q hQ => exists_forall_isInnerAut_psl2 hQ) hP

end CFSG.RankThree.PartTwo.Sec11
