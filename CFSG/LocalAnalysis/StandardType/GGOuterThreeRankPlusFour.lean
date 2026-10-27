module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusFour
import CFSG.Mathlib.GroupTheory.CardLeSqOfTower
import CFSG.RankThree.GF2n.Stroth80.FieldAut

public section

namespace CFSG.StandardType.AutOm

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

private theorem normal_sup_zpowers_of_plusFour {K : Type} [Field K] [Finite K] [CharP K 2]
    {θ : MulAut (matrixDerived (coordinateQuadPlus 4 K))} (hθ3 : θ ^ 3 = 1)
    (hρθ : plusRefl (K := K) (by norm_num : 1 ≤ 4) * θ * plusRefl (K := K) (by norm_num) =
      θ⁻¹)
    (hφθ : ∀ σ : K ≃+* K, θ * fieldAutP (K := K) 4 σ = fieldAutP (K := K) 4 σ * θ)
    (hgen : ∀ α : MulAut (matrixDerived (coordinateQuadPlus 4 K)),
      ∃ ι ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
          (matrixDerived (coordinateQuadPlus 4 K)), ∃ k : ℕ,
        ∃ c ∈ plusCompl (K := K) (by norm_num : 1 ≤ 4),
          α = ι * (θ ^ k * c)) :
    (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus 4 K)) ⊔ Subgroup.zpowers θ).Normal := by
  let N : Subgroup (MulAut (matrixDerived (coordinateQuadPlus 4 K))) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (coordinateQuadPlus 4 K))
  let J : Subgroup (MulAut (matrixDerived (coordinateQuadPlus 4 K))) :=
    N ⊔ Subgroup.zpowers θ
  have hN : N.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hJcore : J ≤ J.normalCore := by
    refine sup_le (Subgroup.normal_le_normalCore.mpr le_sup_left) ?_
    rw [Subgroup.zpowers_le]
    intro α
    obtain ⟨ι, hι, k, c, hc, hα⟩ := hgen α
    rw [hα]
    obtain ⟨l', hl'⟩ := compl_mul_pow (n := 4) le_rfl hθ3 hρθ hφθ hc 1
    have hcθ : c * θ * c⁻¹ = θ ^ l' := by
      simpa using congrArg (· * c⁻¹) hl'
    have hq : (θ ^ k * c) * θ * (θ ^ k * c)⁻¹ = θ ^ l' := by
      calc
        (θ ^ k * c) * θ * (θ ^ k * c)⁻¹
            = θ ^ k * (c * θ * c⁻¹) * (θ ^ k)⁻¹ := by group
        _ = θ ^ k * θ ^ l' * (θ ^ k)⁻¹ := by rw [hcθ]
        _ = θ ^ l' := by group
    refine (Subgroup.mem_sup_of_normal_left (s := N) (t := Subgroup.zpowers θ)).mpr ?_
    refine ⟨ι * (θ ^ l' * ι⁻¹ * (θ ^ l')⁻¹), ?_, θ ^ l',
      Subgroup.zpow_mem_zpowers θ l', ?_⟩
    · exact N.mul_mem hι (hN.conj_mem ι⁻¹ (N.inv_mem hι) (θ ^ l'))
    · calc
        ι * (θ ^ l' * ι⁻¹ * (θ ^ l')⁻¹) * θ ^ l' = ι * θ ^ l' * ι⁻¹ := by group
        _ = ι * ((θ ^ k * c) * θ * (θ ^ k * c)⁻¹) * ι⁻¹ := by rw [hq]
        _ = (ι * (θ ^ k * c)) * θ * (ι * (θ ^ k * c))⁻¹ := by group
  have hEq : J = J.normalCore := le_antisymm hJcore J.normalCore_le
  have hJ : J.Normal := by
    rw [hEq]
    exact Subgroup.normalCore_normal J
  exact hJ

private theorem pow_three_eq_one_of_mem_sup {K : Type} [Field K] [Finite K] [CharP K 2]
    {θ : MulAut (matrixDerived (coordinateQuadPlus 4 K))} (hθ3 : θ ^ 3 = 1)
    (huniq : ∀ k : ℕ, ∀ c ∈ plusCompl (K := K) (by norm_num : 1 ≤ 4),
      θ ^ k * c ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus 4 K)) → θ ^ k = 1 ∧ c = 1)
    {J : Subgroup (MulAut (matrixDerived (coordinateQuadPlus 4 K)))} (hJ : J.Normal)
    (hJsup : J = CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (coordinateQuadPlus 4 K)) ⊔ Subgroup.zpowers θ)
    {j c : MulAut (matrixDerived (coordinateQuadPlus 4 K))} (hj : j ∈ J)
    (hc : c ∈ plusCompl (K := K) (by norm_num : 1 ≤ 4))
    (hjc : (j * c) ^ 3 = 1) : c ^ 3 = 1 := by
  let N : Subgroup (MulAut (matrixDerived (coordinateQuadPlus 4 K))) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (coordinateQuadPlus 4 K))
  have hN : N.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  haveI : N.Normal := hN
  haveI : J.Normal := hJ
  have hc3J : c ^ 3 ∈ J := by
    have h1 : (QuotientGroup.mk (j * c) : MulAut (matrixDerived (coordinateQuadPlus 4 K)) ⧸ J) =
        QuotientGroup.mk c := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff j).2 hj, one_mul]
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← h1, ← QuotientGroup.mk_pow,
      hjc]
    rfl
  rw [hJsup] at hc3J
  rw [Subgroup.mem_sup_of_normal_left (s := N) (t := Subgroup.zpowers θ)] at hc3J
  obtain ⟨a, ha, b, hb, hc3ab⟩ := hc3J
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hconjN : θ ^ (-m) * c ^ 3 ∈ N := by
    rw [← hc3ab, ← hm]
    have h := hN.conj_mem a ha (θ ^ (-m))
    simpa [mul_assoc] using h
  let t : ℕ := ((-m) % 3).toNat
  have ht : θ ^ t = θ ^ (-m) := by
    have h3 : θ ^ (3 : ℤ) = 1 := by simpa using hθ3
    rw [zpow_eq_zpow_emod (-m) h3]
    simp only [t]
    rw [← zpow_natCast]
    exact congrArg (θ ^ ·) (Int.toNat_of_nonneg (Int.emod_nonneg (-m) (by norm_num)))
  have hmem : θ ^ t * c ^ 3 ∈ N := by
    rw [ht]
    exact hconjN
  exact (huniq t _ (pow_mem hc 3) hmem).2

private theorem mem_range_of_rho_mul_fieldAutP {K : Type} [Field K] [Finite K] [CharP K 2]
    {θ : MulAut (matrixDerived (coordinateQuadPlus 4 K))} (hθ3 : θ ^ 3 = 1)
    (huniq : ∀ k : ℕ, ∀ c ∈ plusCompl (K := K) (by norm_num : 1 ≤ 4),
      θ ^ k * c ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus 4 K)) → θ ^ k = 1 ∧ c = 1)
    (hJ : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (coordinateQuadPlus 4 K)) ⊔ Subgroup.zpowers θ).Normal)
    {j : MulAut (matrixDerived (coordinateQuadPlus 4 K))}
    (hj : j ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (coordinateQuadPlus 4 K)) ⊔ Subgroup.zpowers θ) {σ : K ≃+* K}
    (hjc : (j * (plusRefl (K := K) (by norm_num : 1 ≤ 4) *
      fieldAutP (K := K) 4 σ)) ^ 3 = 1) :
    plusRefl (K := K) (by norm_num : 1 ≤ 4) * fieldAutP (K := K) 4 σ ∈
      (fieldAutP (K := K) 4).range := by
  let ρ : MulAut (matrixDerived (coordinateQuadPlus 4 K)) := plusRefl (K := K) (by norm_num)
  let F : (K ≃+* K) →* MulAut (matrixDerived (coordinateQuadPlus 4 K)) := fieldAutP (K := K) 4
  have hc : ρ * F σ ∈ plusCompl (K := K) (by norm_num : 1 ≤ 4) := ⟨σ, Or.inr rfl⟩
  have hc3one : (ρ * F σ) ^ 3 = 1 :=
    pow_three_eq_one_of_mem_sup hθ3 huniq hJ rfl hj hc hjc
  have hρρ : ρ * ρ = 1 := plusRefl_mul_self _
  have hρF : Commute ρ (F σ) := plusRefl_mul_fieldAutP _ σ
  have hc3eq : (ρ * F σ) ^ 3 = ρ * F (σ ^ 3) := by
    have hρ3 : ρ ^ 3 = ρ := by rw [pow_succ, pow_two, hρρ, one_mul]
    calc
      (ρ * F σ) ^ 3 = ρ ^ 3 * (F σ) ^ 3 := hρF.mul_pow 3
      _ = ρ * (F σ) ^ 3 := by rw [hρ3]
      _ = ρ * F (σ ^ 3) := by rw [← map_pow F σ 3]
  have hρeq : ρ = (F (σ ^ 3))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← hc3eq]; exact hc3one)
  exact MonoidHom.mem_range.mpr ⟨(σ ^ 3)⁻¹ * σ, by rw [map_mul, map_inv, ← hρeq]⟩

private theorem mem_sup_range_of_pow_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {θ : MulAut (matrixDerived (coordinateQuadPlus 4 K))} (hθ3 : θ ^ 3 = 1)
    (hgen : ∀ α : MulAut (matrixDerived (coordinateQuadPlus 4 K)),
      ∃ ι ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
          (matrixDerived (coordinateQuadPlus 4 K)), ∃ k : ℕ,
        ∃ c ∈ plusCompl (K := K) (by norm_num : 1 ≤ 4),
          α = ι * (θ ^ k * c))
    (huniq : ∀ k : ℕ, ∀ c ∈ plusCompl (K := K) (by norm_num : 1 ≤ 4),
      θ ^ k * c ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus 4 K)) → θ ^ k = 1 ∧ c = 1)
    (hJ : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (matrixDerived (coordinateQuadPlus 4 K)) ⊔ Subgroup.zpowers θ).Normal) :
    ∀ α : MulAut (matrixDerived (coordinateQuadPlus 4 K)), α ^ 3 = 1 →
      α ∈ (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (matrixDerived (coordinateQuadPlus 4 K)) ⊔ Subgroup.zpowers θ) ⊔
        (fieldAutP (K := K) 4).range := by
  intro α hα3
  let N : Subgroup (MulAut (matrixDerived (coordinateQuadPlus 4 K))) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (coordinateQuadPlus 4 K))
  let J : Subgroup (MulAut (matrixDerived (coordinateQuadPlus 4 K))) :=
    N ⊔ Subgroup.zpowers θ
  obtain ⟨ι, hι, k, c, hc, hα⟩ := hgen α
  set j : MulAut (matrixDerived (coordinateQuadPlus 4 K)) := ι * θ ^ k with hj
  have hjJ : j ∈ J := by
    rw [hj]
    exact Subgroup.mul_mem_sup hι (Subgroup.zpow_mem_zpowers θ k)
  have hαj : α = j * c := by
    rw [hα, hj]
    group
  have hc0 : c ∈ plusCompl (K := K) (by norm_num : 1 ≤ 4) := hc
  rw [mem_plusCompl] at hc
  obtain ⟨σ, rfl | rfl⟩ := hc
  · rw [hαj]
    exact Subgroup.mul_mem_sup hjJ (MonoidHom.mem_range.mpr ⟨σ, rfl⟩)
  · have hα3' : (j * (plusRefl (K := K) (by norm_num : 1 ≤ 4) *
        fieldAutP (K := K) 4 σ)) ^ 3 = 1 := by
      rw [← hαj]
      exact hα3
    have hrange := mem_range_of_rho_mul_fieldAutP hθ3 huniq hJ hjJ hα3'
    rw [hαj]
    exact Subgroup.mul_mem_sup hjJ hrange

private theorem exists_zpow_mul_mem_of_mem_sup {K : Type} [Field K] [Finite K] [CharP K 2]
    {J : Subgroup (MulAut (matrixDerived (coordinateQuadPlus 4 K)))}
    (hJ : J.Normal) {σ₀ : K ≃+* K} (hσ₀ : ∀ τ : K ≃+* K, τ ∈ Subgroup.zpowers σ₀)
    {s : MulAut (matrixDerived (coordinateQuadPlus 4 K))}
    (hs : s ∈ J ⊔ (fieldAutP (K := K) 4).range) :
    ∃ m : ℤ, (fieldAutP (K := K) 4 σ₀) ^ m * s ∈ J := by
  haveI : J.Normal := hJ
  rw [Subgroup.mem_sup_of_normal_left (s := J) (t := (fieldAutP (K := K) 4).range)] at hs
  obtain ⟨j, hj, f, hf, rfl⟩ := hs
  obtain ⟨τ, rfl⟩ := MonoidHom.mem_range.mp hf
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hσ₀ τ)
  refine ⟨-m, ?_⟩
  have hφ : fieldAutP (K := K) 4 τ = (fieldAutP (K := K) 4 σ₀) ^ m := by
    rw [← hm, map_zpow]
  rw [hφ]
  have hconj := hJ.conj_mem j hj ((fieldAutP (K := K) 4 σ₀) ^ (-m))
  simpa [mul_assoc, zpow_neg] using hconj

theorem card_le_nine_of_plusFour (hT : PlusFourTrialityInput) {K : Type} [Field K] [Finite K]
    [CharP K 2] {A : Subgroup (MulAut (matrixDerived (coordinateQuadPlus 4 K)))}
    (hexp : ∀ x ∈ A, x ^ 3 = 1)
    (hAI : A ⊓ (MulAut.conj : matrixDerived (coordinateQuadPlus 4 K) →*
      MulAut (matrixDerived (coordinateQuadPlus 4 K))).range = ⊥) :
    Nat.card A ≤ 9 := by
  classical
  obtain ⟨θ, hθ3, hρθ, hφθ, hgen, huniq, -⟩ := hT K
  have hJ := normal_sup_zpowers_of_plusFour hθ3 hρθ hφθ hgen
  have hmemS := mem_sup_range_of_pow_three hθ3 hgen huniq hJ
  haveI : IsCyclic (K ≃+* K) :=
    CFSG.RankThree.GF2n.Stroth80.isCyclic_ringEquiv K
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := K ≃+* K)
  haveI : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (coordinateQuadPlus 4 K)) ⊔ Subgroup.zpowers θ).Normal := hJ
  have hmain := CFSG.card_le_sq_of_two_cyclic_layers (p := 3) (by norm_num)
    (N := CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (coordinateQuadPlus 4 K)))
    (J := CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (coordinateQuadPlus 4 K)) ⊔ Subgroup.zpowers θ)
    (S := (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (matrixDerived (coordinateQuadPlus 4 K)) ⊔ Subgroup.zpowers θ) ⊔
      (fieldAutP (K := K) 4).range)
    (A := A) (φ₀ := θ) (g := fieldAutP (K := K) 4 σ₀)
    inferInstance
    (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨σ₀, rfl⟩))
    (fun s hs => exists_zpow_mul_mem_of_mem_sup hJ hσ₀ hs) le_rfl
    (fun x hx => hmemS x (hexp x hx)) hexp
    (by simpa [CFSG.ComponentClassification.OuterAutomorphisms.inner] using hAI)
  exact hmain

end CFSG.StandardType.AutOm

end
