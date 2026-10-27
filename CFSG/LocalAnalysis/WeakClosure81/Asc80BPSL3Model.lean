module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.Quasithin.Background.A1bBasic
import CFSG.Quasithin.Vol2.Ch12Sec6P31WXL3M
import CFSG.Quasithin.Vol2.Ch11SecOE8Q
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphField
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem normalizer_sylow_data {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (S : Subgroup (projectiveSL 3 K)) (hS : IsSylowIn 2 S ⊤) :
    Group.IsSolvable (normalizer (S : Set (projectiveSL 3 K))) ∧
      Nat.card (normalizer (S : Set (projectiveSL 3 K))) *
          Nat.gcd 3 (Nat.card K - 1) =
        Nat.card K ^ 3 * (Nat.card K - 1) ^ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have hindex : ¬ 2 ∣ S.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hS.not_dvd_relIndex
  have hT : ((hS.isPGroup.toSylow hindex : Sylow 2 (projectiveSL 3 K)) : Subgroup _) = S :=
    IsPGroup.toSylow_coe _ _
  have hmem : normalizer (S : Set (projectiveSL 3 K)) ∈
      sylowNormalizers (projectiveSL 3 K) 2 := by
    refine ⟨hS.isPGroup.toSylow hindex, ?_⟩
    rw [hT]
  rw [sylowNormalizers_eq (K := K) 2 (by norm_num)] at hmem
  obtain ⟨x, hx⟩ := hmem
  have hcard : Nat.card (normalizer (S : Set (projectiveSL 3 K))) =
      Nat.card (projUpperTriangular 3 K) := by
    rw [hx, Subgroup.card_map_of_injective (MulAut.conj x).injective]
  constructor
  · rw [hx]
    haveI : Group.IsSolvable (upperTriangular 3 K) :=
      CFSG.LieType.SteinbergBR.isSolvable_upperTriangular_of_card Nat.prime_two hK 3
    haveI : Group.IsSolvable (projUpperTriangular 3 K) :=
      solvable_of_surjective
        (MonoidHom.subgroupMap_surjective (proj 3 K) (upperTriangular 3 K))
    exact solvable_of_surjective
      (MonoidHom.subgroupMap_surjective (MulAut.conj x).toMonoidHom (projUpperTriangular 3 K))
  · rw [hcard]
    exact CFSG.Quasithin.H13.P31X.l3_card_projUpperTriangular

theorem psl3_graph_involution_model_escape {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (S : Subgroup (projectiveSL 3 K)) (hS : IsSylowIn 2 S ⊤)
    (D : GL (Fin 3) K) (σ : K ≃+* K)
    (hβ : (conjAut 3 K D * fieldAut 3 K σ * dualAut 3 K) ^ 2 = 1) :
    ∃ x : projectiveSL 3 K, (conjAut 3 K D * fieldAut 3 K σ * dualAut 3 K) x = x ∧
      x ∉ normalizer (S : Set (projectiveSL 3 K)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨hNsolv, hNcard⟩ := normalizer_sylow_data (K := K) hf hK S hS
  by_contra hcon
  push Not at hcon
  let β : MulAut (projectiveSL 3 K) :=
    conjAut 3 K D * fieldAut 3 K σ * dualAut 3 K
  change ∀ x, β x = x → x ∈ normalizer (S : Set (projectiveSL 3 K)) at hcon
  have hβ2 : β ^ 2 = 1 := hβ
  by_cases hσ : σ = 1
  ·
    have hβpure : (conjAut 3 K D * dualAut 3 K) ^ 2 = 1 := by
      simpa [β, hσ] using hβ2
    obtain ⟨-, ⟨⟨H, C, -, hconj, hcases⟩, -⟩⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_linear_pure_graph_involution_normal_forms
        (K := K) (n := 3) hf hK (by norm_num) D hβpure
    have hC1 : C = 1 := by
      rcases hcases with ⟨hCmat, -⟩ | ⟨r, hr, -⟩
      · exact Units.ext (by simpa using hCmat)
      · exfalso
        omega
    have hβeq : conjAut 3 K D * dualAut 3 K =
        conjAut 3 K H * dualAut 3 K * (conjAut 3 K H)⁻¹ := by
      have hCaut : conjAut 3 K C = 1 := by rw [hC1, map_one]
      simpa [hCaut] using hconj
    obtain ⟨j, hj_inj, hj_range⟩ :=
      CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3T.exists_SL_two_fixed_dualAut (F := K)
    let F : Subgroup (projectiveSL 3 K) :=
      j.range.map (conjAut 3 K H : projectiveSL 3 K →* projectiveSL 3 K)
    have hFcard : Nat.card F = Nat.card K * (Nat.card K ^ 2 - 1) := by
      have hrange : Nat.card j.range = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
        calc Nat.card j.range = Nat.card (Subgroup.map j ⊤) := by rw [MonoidHom.range_eq_map]
          _ = Nat.card (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) :=
            Subgroup.card_map_of_injective hj_inj
          _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by rw [Subgroup.card_top]
      change Nat.card (j.range.map (conjAut 3 K H : projectiveSL 3 K →* projectiveSL 3 K)) =
        Nat.card K * (Nat.card K ^ 2 - 1)
      rw [Subgroup.card_map_of_injective
        (f := (conjAut 3 K H : projectiveSL 3 K →* projectiveSL 3 K))
        (conjAut 3 K H).injective, hrange,
        CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3T.card_SL_two]
    have hFfix : ∀ x ∈ F, (conjAut 3 K D * dualAut 3 K) x = x := by
      rintro x ⟨y, hy, rfl⟩
      have hyfix : dualAut 3 K y = y := by
        have hy' : y ∈ CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
            (dualAut 3 K) := by
          rwa [← hj_range]
        simpa [CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup] using hy'
      change (conjAut 3 K D * dualAut 3 K) ((conjAut 3 K H) y) = (conjAut 3 K H) y
      rw [hβeq]
      simp [MulAut.mul_apply, hyfix]
    have hFN : F ≤ normalizer (S : Set (projectiveSL 3 K)) :=
      fun x hx => hcon x (by simpa [β, hσ] using hFfix x hx)
    have hFdvd : Nat.card F ∣ Nat.card (normalizer (S : Set (projectiveSL 3 K))) :=
      Subgroup.card_dvd_of_le hFN
    have hFfactor : Nat.card F = Nat.card K * ((Nat.card K + 1) * (Nat.card K - 1)) := by
      rw [hFcard]
      congr 1
      simpa using Nat.sq_sub_sq (Nat.card K) 1
    have hq1dvdF : Nat.card K + 1 ∣ Nat.card F := by
      rw [hFfactor]
      exact dvd_mul_of_dvd_right
        (dvd_mul_right (Nat.card K + 1) (Nat.card K - 1)) (Nat.card K)
    have hq1dvdN : Nat.card K + 1 ∣
        Nat.card (normalizer (S : Set (projectiveSL 3 K))) :=
      dvd_trans hq1dvdF hFdvd
    have hq1dvdB : Nat.card K + 1 ∣ Nat.card K ^ 3 * (Nat.card K - 1) ^ 2 := by
      rw [← hNcard]
      exact dvd_mul_of_dvd_left hq1dvdN _
    have hq2 : 2 ≤ Nat.card K := by
      rw [hK]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hqeven : Even (Nat.card K) := by
      rw [hK]
      exact Nat.even_pow.mpr ⟨by norm_num, by omega⟩
    have hnotEven : ¬ Even (Nat.card K - 1) := by
      have h := Nat.even_add_one (n := Nat.card K - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ Nat.card K)] at h
      exact h.mp hqeven
    have hodd : Odd (Nat.card K - 1) := Nat.not_even_iff_odd.mp hnotEven
    have hcopq : Nat.Coprime (Nat.card K + 1) (Nat.card K) := by
      have h : Nat.Coprime (Nat.card K) (Nat.card K + 1) :=
        Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
      exact h.symm
    have hcopqm1 : Nat.Coprime (Nat.card K + 1) (Nat.card K - 1) := by
      have h : Nat.Coprime (Nat.card K - 1) (Nat.card K + 1) := by
        have hsum : Nat.card K - 1 + 2 = Nat.card K + 1 := by omega
        rw [← hsum]
        exact Nat.coprime_self_add_right.mpr (hodd.coprime_two_right)
      exact h.symm
    have hcop : Nat.Coprime (Nat.card K + 1)
        (Nat.card K ^ 3 * (Nat.card K - 1) ^ 2) :=
      (hcopq.pow_right 3).mul_right (hcopqm1.pow_right 2)
    have hone : Nat.card K + 1 ∣ 1 :=
      hcop.dvd_of_dvd_mul_right (by simpa using hq1dvdB)
    have hq1 : Nat.card K + 1 = 1 := Nat.dvd_one.mp hone
    omega
  ·
    obtain ⟨hfeven, hσpow, H, hβeq⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.linear_graph_field_involution_descent
        (K := K) (n := 3) Nat.prime_two hf hK (by norm_num) D σ hσ hβ2
    let e := f / 2
    have hf2e : f = 2 * e := (Nat.two_mul_div_two_of_even hfeven).symm
    have he1 : 1 ≤ e := by omega
    have hcard : Nat.card K = 2 ^ (2 * e) := by rw [hK, hf2e]
    have hU : UnitaryFieldData 2 e K := ⟨Nat.prime_two, he1, hcard⟩
    have hσbar : ∀ x, σ x = hU.bar x := by
      intro x
      rw [hσpow x, hU.bar_apply]
    by_cases he2 : 2 ≤ e
    ·
      have hnq : (3, 2 ^ e) ≠ (3, 2) := by
        intro hpair
        have hpow : 2 ^ e = 2 := congrArg Prod.snd hpair
        have h4 : 4 ≤ 2 ^ e := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
        omega
      obtain ⟨P, hPperf, hPeven, hPfix⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_fixed_perfect_even_fieldAut_dualAut
          (K := K) (n := 3) hU (by norm_num) hnq σ hσbar
      obtain ⟨F, hFperf, hFeven, hFfix⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_fixed_perfect_even_conj
          (S := projectiveSL 3 K) (α := β) (β := fieldAut 3 K σ * dualAut 3 K)
          (γ := conjAut 3 K H) hβeq ⟨P, hPperf, hPeven, hPfix⟩
      have hFN : F ≤ normalizer (S : Set (projectiveSL 3 K)) :=
        fun x hx => hcon x (hFfix x hx)
      haveI : Group.IsSolvable (normalizer (S : Set (projectiveSL 3 K))) := hNsolv
      have hFsolv : Group.IsSolvable F :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hFN)
      have hsub : Subsingleton F := by
        have htop : ∀ k, derivedSeries F k = ⊤ := by
          intro k
          induction k with
          | zero => rfl
          | succ k ih =>
            rw [derivedSeries_succ, ih, ← _root_.commutator_def, hFperf.commutator_eq_top]
        obtain ⟨n, hn⟩ := hFsolv.solvable
        rw [htop] at hn
        refine ⟨fun a b => ?_⟩
        have ha : a ∈ (⊥ : Subgroup F) := hn ▸ mem_top a
        have hb : b ∈ (⊥ : Subgroup F) := hn ▸ mem_top b
        rw [mem_bot] at ha hb
        rw [ha, hb]
      haveI : Subsingleton F := hsub
      haveI : Unique F := uniqueOfSubsingleton 1
      have hcard1 : Nat.card F = 1 := Nat.card_unique
      rw [hcard1] at hFeven
      exact Nat.not_even_one hFeven
    ·
      have he_eq : e = 1 := by omega
      have hf2 : f = 2 := by omega
      have hk4 : Nat.card K = 4 := by
        rw [hK, hf2]
        norm_num
      have hσ2 : ∀ a, σ a = a ^ 2 := by
        intro a
        have h := hσpow a
        rw [hf2] at h
        simpa using h
      let F₀ : Subgroup (projectiveSL 3 K) :=
        (LinearThreeFourFixedNine.qSub (k := K)).map (proj 3 K)
      have hF₀card : Nat.card F₀ = 9 :=
        LinearThreeFourFixedNine.card_map_proj_qSub hk4
      have hF₀fix : ∀ x ∈ F₀, (fieldAut 3 K σ * dualAut 3 K) x = x :=
        fun x hx => LinearThreeFourFixedNine.beta_fixed hσ2 hk4 hx
      let F : Subgroup (projectiveSL 3 K) :=
        F₀.map (conjAut 3 K H : projectiveSL 3 K →* projectiveSL 3 K)
      have hFcard : Nat.card F = 9 := by
        change Nat.card (F₀.map (conjAut 3 K H : projectiveSL 3 K →* projectiveSL 3 K)) = 9
        rw [Subgroup.card_map_of_injective
          (f := (conjAut 3 K H : projectiveSL 3 K →* projectiveSL 3 K))
          (conjAut 3 K H).injective, hF₀card]
      have hFfix : ∀ x ∈ F, β x = x := by
        rintro x ⟨y, hy, rfl⟩
        have hyfix := hF₀fix y hy
        change (conjAut 3 K D * fieldAut 3 K σ * dualAut 3 K) ((conjAut 3 K H) y) =
          (conjAut 3 K H) y
        rw [hβeq]
        simp [MulAut.mul_apply, hyfix]
      have hFN : F ≤ normalizer (S : Set (projectiveSL 3 K)) :=
        fun x hx => hcon x (hFfix x hx)
      have hFdvd : Nat.card F ∣ Nat.card (normalizer (S : Set (projectiveSL 3 K))) :=
        Subgroup.card_dvd_of_le hFN
      have h9dvdN : 9 ∣ Nat.card (normalizer (S : Set (projectiveSL 3 K))) := by
        rw [← hFcard]
        exact hFdvd
      have hN : Nat.card (normalizer (S : Set (projectiveSL 3 K))) = 192 := by
        have h := hNcard
        rw [hk4] at h
        norm_num at h
        omega
      rw [hN] at h9dvdN
      norm_num at h9dvdN

end CFSG.LocalAnalysis.WeakClosure81

end
