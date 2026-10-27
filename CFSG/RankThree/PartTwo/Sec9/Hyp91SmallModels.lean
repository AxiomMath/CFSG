module

public import CFSG.RankThree.PartTwo.KFacts.K71L28Cent
public import CFSG.RankThree.PartTwo.KFacts.K71Item93b
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.KFacts.K73Lines
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.RankThree.PartTwo.Sec8.Outer
import CFSG.RankThree.Asc83Table.E9

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts


section L28Model

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_l28_model_aux_of_hyp81 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {A : Subgroup G} {c a : G} (hyp : Sec8.Hyp81 G A c L a) (h27 : Nat.card A = 27)
    (e₀ : L ⧸ aschbacherSolvableCore 3 L ≃* PSL(2, K))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL(2, K)) (σ : K ≃+* K) (x : PSL(2, K)) (b : G)
      (hbA : b ∈ A), orderOf σ = 3 ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧ psl2FieldAut _ σ x = x ∧
      inducedAutHom L e ⟨b, hAL hbA⟩ = MulAut.conj x ∧
      ∀ y (hy : y ∈ A), ∃ i j : ℕ,
        inducedAutHom L e ⟨y, hAL hy⟩ = MulAut.conj x ^ i * psl2FieldAut _ σ ^ j := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAel := hyp.mem_partTwoF.1
  have hA3 : ∀ y ∈ A, y ^ 3 = 1 := hAel.2
  have hAcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := hyp.mem_A
  have haA := hyp.a_mem
  have hcN := hAL hcA
  have haN := hAL haA
  have hc3 := hA3 c hcA
  have ha3 := hA3 a haA
  have hβ3 : inducedAutHom L e₀ ⟨a, haN⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one L e₀ haN ha3
  have hout : ¬ IsInnerAut (inducedAutHom L e₀ ⟨a, haN⟩) :=
    (not_isInnerAut_inducedAutHom_iff L e₀ haN).mpr hyp.inducesOuterTheta
  have hD : inducedAutHom L e₀ ⟨a, haN⟩ ∉ (pglAction K).range := fun h =>
    hout (isInnerAut_of_mem_inndiag_of_pow_three h hβ3)
  have hβo : orderOf (inducedAutHom L e₀ ⟨a, haN⟩) = 3 :=
    orderOf_eq_prime hβ3 fun h1 => hout (by rw [h1]; exact ⟨1, map_one _⟩)
  obtain ⟨σ, hσ3, g, hβg⟩ := linear_two_prime_order_field_descent Nat.prime_three _ hβo hD
  set e := e₀.trans (pglAction K g).symm with he
  have hee : e₀.symm.trans e = (pglAction K g)⁻¹ := by
    refine MulEquiv.ext fun m => ?_
    rw [he, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have hγ : ∀ y, inducedAutHom L e y =
      (pglAction K g)⁻¹ * inducedAutHom L e₀ y * pglAction K g := by
    intro y
    rw [inducedAutHom_eq_conj L e₀ e y, hee, inv_inv]
  have hγa : inducedAutHom L e ⟨a, haN⟩ = psl2FieldAut K σ := by
    rw [hγ, hβg]
    group
  have hcτ := thetaQuotMulAut_compAction_eq_one_of_hyp81 hyp hcN
  set S := Subgroup.closure ({c, a} : Set G) with hS
  have hca : c * a = a * c := hAcomm c hcA a haA
  have hcS : c ∈ S := Subgroup.subset_closure (by simp)
  have haS : a ∈ S := Subgroup.subset_closure (by simp)
  have hS9 : Nat.card S ≤ 9 := by
    have hsurj : Function.Surjective (fun ij : Fin 3 × Fin 3 =>
        (⟨c ^ (ij.1 : ℕ) * a ^ (ij.2 : ℕ), mul_mem (pow_mem hcS _) (pow_mem haS _)⟩ : S)) := by
      rintro ⟨z, hz⟩
      obtain ⟨i, j, hi, hj, rfl⟩ := exists_pow_mul_pow_of_mem_closure_pair hca hc3 ha3 hz
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩
    calc Nat.card S ≤ Nat.card (Fin 3 × Fin 3) := Nat.card_le_card_of_surjective _ hsurj
      _ = 9 := by simp
  have hSA : S ≤ A := by
    rw [hS, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcA
    · exact haA
  obtain ⟨b, hbA, hbS⟩ : ∃ b ∈ A, b ∉ S := by
    by_contra hcon
    have h0 : A ≤ S := fun y hy => by
      by_contra hyS
      exact hcon ⟨y, hy, hyS⟩
    have h1 := Subgroup.card_le_of_le h0
    rw [h27] at h1
    omega
  have hbN := hAL hbA
  obtain ⟨h, δ, hhδ⟩ := exists_pglAction_mul_psl2FieldAut (inducedAutHom L e ⟨b, hbN⟩)
  have hδ3 : δ ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (x := δ)
    rwa [card_ringAut_of_card_eight hK] at h1
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  obtain ⟨k, -, rfl⟩ := exists_pow_eq_of_pow_three_eq_one hσ3 hδ3
  obtain ⟨b', hb'⟩ : ∃ b' : G, b' = b * (a ^ k)⁻¹ := ⟨_, rfl⟩
  have hbb' : b = b' * a ^ k := by rw [hb', inv_mul_cancel_right]
  have hb'A : b' ∈ A := by rw [hb']; exact mul_mem hbA (inv_mem (pow_mem haA k))
  have hb'N := hAL hb'A
  have hγb' : inducedAutHom L e ⟨b', hb'N⟩ = pglAction K h := by
    have h1 : (⟨b', hb'N⟩ : Subgroup.normalizer (L : Set G)) = ⟨b, hbN⟩ * (⟨a, haN⟩ ^ k)⁻¹ :=
      Subtype.ext (by simp [hb'])
    rw [h1, map_mul, map_inv, map_pow, hγa, hhδ, map_pow, mul_inv_cancel_right]
  have hγba : inducedAutHom L e ⟨b', hb'N⟩ * psl2FieldAut K σ =
      psl2FieldAut K σ * inducedAutHom L e ⟨b', hb'N⟩ := by
    rw [← hγa, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAcomm b' hb'A a haA)
  rw [hγb'] at hγba
  have hσh : pgl2FieldAut K σ h = h := by
    apply pglAction_injective
    rw [← psl2FieldAut_mul_pglAction_mul_inv, ← hγba, mul_inv_cancel_right]
  have hh3 : h ^ 3 = 1 := by
    apply pglAction_injective
    rw [map_pow, ← hγb', ← map_pow]
    have h1 : (⟨b', hb'N⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hA3 b' hb'A)
    rw [h1, map_one, map_one]
  obtain ⟨x, rfl⟩ := exists_toPGL_eq_of_pow_three hh3
  rw [pglAction_toPGL] at hγb'
  have hx3 : x ^ 3 = 1 := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    (by rw [map_pow, hh3, map_one])
  have hσx : psl2FieldAut K σ x = x := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    (by rw [psl2FieldAut_toPGL, hσh])
  have hb'S : b' ∉ S := fun h1 => hbS (by rw [hbb']; exact mul_mem h1 (pow_mem haS k))
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : thetaQuotMulAut L (compAction L ⟨b', hb'N⟩) = 1 := by
      have h3 : inducedAutHom L e ⟨b', hb'N⟩ = 1 := by rw [hγb', h1, map_one]
      rw [inducedAutHom_apply] at h3
      exact (MulAut.congr e).injective (h3.trans (map_one _).symm)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_thetaQuotMulAut_eq_one hyp hb'N hb'A h2)
    apply hb'S
    rw [← hm]
    exact zpow_mem hcS m
  have hac : a ∉ Subgroup.zpowers c := by
    intro h1
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    apply hout
    have h2 : inducedAutHom L e₀ ⟨a, haN⟩ = 1 := by
      have h3 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) = ⟨c, hcN⟩ ^ m :=
        Subtype.ext (by simp [hm])
      rw [h3, map_zpow, inducedAutHom_apply, hcτ, map_one, one_zpow]
    rw [h2]
    exact ⟨1, map_one _⟩
  have hS9' : Nat.card S = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hc3 ha3 hca hyp.ne_one hac
  set T := S ⊔ Subgroup.zpowers b' with hT
  have hTA : T ≤ A := sup_le hSA (Subgroup.zpowers_le.mpr hb'A)
  have hST : S ≤ T := le_sup_left
  have hb'T : b' ∈ T := (le_sup_right : Subgroup.zpowers b' ≤ T) (Subgroup.mem_zpowers b')
  have hTeq : T = A := by
    have h1 : Nat.card S ∣ Nat.card T := Subgroup.card_dvd_of_le hST
    have h2 : Nat.card T ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
      exact Subgroup.card_dvd_of_le hTA
    have h3 : Nat.card T ≠ 9 := by
      intro h4
      apply hb'S
      have h5 : S = T := Subgroup.eq_of_le_of_card_ge hST (by rw [h4, hS9'])
      rw [h5]
      exact hb'T
    rw [hS9'] at h1
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    have hT27 : Nat.card T = 27 := by
      rw [hj'] at h1 h3 ⊢
      interval_cases j
      · norm_num at h1
      · norm_num at h1
      · exact absurd (by norm_num) h3
      · norm_num
    exact Subgroup.eq_of_le_of_card_ge hTA (by rw [hT27, h27])
  set Q : Subgroup G := ((Subgroup.closure ({MulAut.conj x, psl2FieldAut K σ} :
      Set (MulAut (PSL(2, K))))).comap (inducedAutHom L e)).map
      (Subgroup.normalizer (L : Set G)).subtype with hQ
  have hmemQ : ∀ y (hy : y ∈ Subgroup.normalizer (L : Set G)), inducedAutHom L e ⟨y, hy⟩ ∈
      Subgroup.closure ({MulAut.conj x, psl2FieldAut K σ} : Set (MulAut (PSL(2, K)))) →
      y ∈ Q := fun y hy h1 => ⟨⟨y, hy⟩, h1, rfl⟩
  have hcQ : c ∈ Q := hmemQ c hcN (by rw [inducedAutHom_apply, hcτ, map_one]; exact one_mem _)
  have haQ : a ∈ Q := hmemQ a haN (by rw [hγa]; exact Subgroup.subset_closure (by simp))
  have hb'Q : b' ∈ Q := hmemQ b' hb'N (by rw [hγb']; exact Subgroup.subset_closure (by simp))
  have hAQ : A ≤ Q := by
    rw [← hTeq, hT]
    refine sup_le ?_ (Subgroup.zpowers_le.mpr hb'Q)
    rw [hS, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcQ
    · exact haQ
  have hσ3' : psl2FieldAut K σ ^ 3 = 1 := by
    rw [← map_pow, show σ ^ 3 = 1 by rw [← hσ3]; exact pow_orderOf_eq_one σ, map_one]
  have hx3' : MulAut.conj x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hxσ : MulAut.conj x * psl2FieldAut K σ = psl2FieldAut K σ * MulAut.conj x := by
    rw [← pglAction_toPGL]
    exact hγba
  refine ⟨e, σ, x, b', hb'A, hσ3, hx3, hx1, hσx, hγb', fun y hy => ?_⟩
  obtain ⟨⟨y', hy'N⟩, hy'Q, rfl⟩ := hAQ hy
  have hy'Q' : inducedAutHom L e ⟨y', hy'N⟩ ∈
      Subgroup.closure ({MulAut.conj x, psl2FieldAut K σ} : Set (MulAut (PSL(2, K)))) := hy'Q
  obtain ⟨i, j, -, -, hij⟩ := exists_pow_mul_pow_of_mem_closure_pair hxσ hx3' hσ3' hy'Q'
  exact ⟨i, j, hij⟩

theorem exists_l28_model_of_hyp81 {A : Subgroup G} {c a : G}
    (hyp : Sec8.Hyp81 G A c L a) (h27 : Nat.card A = 27)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL(2, GaloisField 2 3))
      (σ : GaloisField 2 3 ≃+* GaloisField 2 3) (x : PSL(2, GaloisField 2 3)) (b : G)
      (hbA : b ∈ A), orderOf σ = 3 ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧ psl2FieldAut _ σ x = x ∧
      inducedAutHom L e ⟨b, hAL hbA⟩ = MulAut.conj x ∧
      ∀ y (hy : y ∈ A), ∃ i j : ℕ,
        inducedAutHom L e ⟨y, hAL hy⟩ = MulAut.conj x ^ i * psl2FieldAut _ σ ^ j :=
  exists_l28_model_aux_of_hyp81 card_galoisField_two_three hyp h27
    (hL.some.trans (projSLEquivPSL (GaloisField 2 3))) hAL

end L28Model

section L28Cent

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open Matrix
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem eq_bot_of_hyp81_psl28 {A : Subgroup G} {c a : G}
    (hyp : Sec8.Hyp81 G A c L a) (h27 : Nat.card A = 27)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {e : G} (heA : e ∈ A)
    (hec : e ∉ Subgroup.zpowers c) (he : e ∈ Subgroup.normalizer (L : Set G))
    (N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)))
    (hNc : ∀ ν ∈ N, ν * thetaQuotMulAut L (compAction L ⟨e, he⟩) =
      thetaQuotMulAut L (compAction L ⟨e, he⟩) * ν)
    (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ ℓ : L ⧸ aschbacherSolvableCore 3 L,
      thetaQuotMulAut L (compAction L ⟨e, he⟩) ℓ = ℓ →
        ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) :
    N = ⊥ := by
  obtain ⟨e', σ, x, b, hbA, hσ3, hx3, hx1, hσx, -, hA⟩ := exists_l28_model_of_hyp81 hyp h27 hL hAL
  obtain ⟨i, j, hij⟩ := hA e heA
  have hσ3' : σ ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one σ
    rwa [hσ3] at h1
  have hσf3 : psl2FieldAut (GaloisField 2 3) σ ^ 3 = 1 := by rw [← map_pow, hσ3', map_one]
  have hx3' : MulAut.conj x ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hxσ : Commute (MulAut.conj x) (psl2FieldAut (GaloisField 2 3) σ) := by
    have h1 := mul_conj_mul_inv (psl2FieldAut (GaloisField 2 3) σ) x
    rw [hσx] at h1
    change MulAut.conj x * psl2FieldAut _ σ = psl2FieldAut _ σ * MulAut.conj x
    calc MulAut.conj x * psl2FieldAut _ σ =
        psl2FieldAut _ σ * MulAut.conj x * (psl2FieldAut _ σ)⁻¹ * psl2FieldAut _ σ := by rw [h1]
      _ = psl2FieldAut _ σ * MulAut.conj x := by group
  have hε : MulAut.congr e' (thetaQuotMulAut L (compAction L ⟨e, he⟩)) =
      MulAut.conj (x ^ (i % 3)) * psl2FieldAut (GaloisField 2 3) σ ^ (j % 3) := by
    rw [← inducedAutHom_apply, show (⟨e, he⟩ : Subgroup.normalizer (L : Set G)) = ⟨e, hAL heA⟩
      from rfl, hij, mulAut_pow_mod_three hx3' i, mulAut_pow_mod_three hσf3 j, map_pow]
  have hε1 : MulAut.conj (x ^ (i % 3)) * psl2FieldAut (GaloisField 2 3) σ ^ (j % 3) ≠ 1 := by
    intro h1
    apply hec
    refine mem_zpowers_of_thetaQuotMulAut_eq_one hyp he heA ?_
    have h2 := hε.trans h1
    exact (MulAut.congr e').injective (h2.trans (map_one _).symm)
  refine eq_bot_of_congr e' (fun N₀ hc h3 hn => ?_) hNc hN3 hNn
  rw [hε] at hc hn
  have hmodj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  by_cases hj0 : j % 3 = 0
  ·
    rw [hj0, pow_zero, mul_one] at hc hn hε1
    have hu3 : (x ^ (i % 3)) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]
    have hu1 : x ^ (i % 3) ≠ 1 := fun h1 => hε1 (by rw [h1, map_one])
    exact psl28_eq_bot_of_commute_conj hu3 hu1 hc h3
  ·
    set ε' := MulAut.conj (x ^ (i % 3)) * psl2FieldAut (GaloisField 2 3) σ ^ (j % 3) with hε'
    have hε'3 : ε' ^ 3 = 1 := by
      have hc' : Commute (MulAut.conj (x ^ (i % 3)))
          (psl2FieldAut (GaloisField 2 3) σ ^ (j % 3)) := by
        rw [map_pow]
        exact (hxσ.pow_left _).pow_right _
      have e1 : MulAut.conj (x ^ (i % 3)) ^ 3 = 1 := by
        rw [← map_pow, ← pow_mul, mul_comm (i % 3) 3, pow_mul, hx3, one_pow, map_one]
      have e2 : (psl2FieldAut (GaloisField 2 3) σ ^ (j % 3)) ^ 3 = 1 := by
        rw [← pow_mul, mul_comm (j % 3) 3, pow_mul, hσf3, one_pow]
      rw [hε', hc'.mul_pow, e1, e2, one_mul]
    have hε'o : orderOf ε' = 3 := orderOf_eq_prime hε'3 hε1
    have hD : ε' ∉ (pglAction (GaloisField 2 3)).range := by
      rintro ⟨g, hg⟩
      apply hj0
      have h1 : pglAction (GaloisField 2 3)
          ((Matrix.ProjectiveSpecialLinearGroup.toPGL (x ^ (i % 3)))⁻¹ * g) =
          psl2FieldAut (GaloisField 2 3) (σ ^ (j % 3)) := by
        rw [map_mul, map_inv, pglAction_toPGL, hg, hε', map_pow (psl2FieldAut _),
          inv_mul_cancel_left]
      have h2 : semilinearAction (GaloisField 2 3) (SemidirectProduct.inl
          ((Matrix.ProjectiveSpecialLinearGroup.toPGL (x ^ (i % 3)))⁻¹ * g)) =
          semilinearAction (GaloisField 2 3) (SemidirectProduct.inr (σ ^ (j % 3))) := by
        rw [semilinearAction_inl, semilinearAction_inr, h1]
      have h3 := congrArg SemidirectProduct.rightHom
        (semilinearAction_injective (GaloisField 2 3) h2)
      rw [SemidirectProduct.rightHom_inl, SemidirectProduct.rightHom_inr] at h3
      have h4 := orderOf_dvd_of_pow_eq_one h3.symm
      rw [hσ3] at h4
      omega
    obtain ⟨σ', hσ', g, hg⟩ := linear_two_prime_order_field_descent Nat.prime_three ε' hε'o hD
    exact eq_bot_of_conj hg (fun N₁ hc₁ h₁ hn₁ => psl28_eq_bot_of_commute_field hσ' hc₁ h₁ hn₁)
      hc h3 hn

end L28Cent

section SU38Model

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_su38_model_of_hyp81 {A : Subgroup G} {c a : G}
    (hyp : Sec8.Hyp81 G A c L a) (h27 : Nat.card A = 27)
    (hSL : IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) 8)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 3 K)
      (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU 2 3 K 3) (σ : K ≃+* K)
      (B : unitaryIsom3 h) (b : G) (hbA : b ∈ A),
      orderOf σ = 3 ∧ inducedAutHom L e ⟨b, hAL hbA⟩ = suConj h B ∧
      suConj h B * suField h σ = suField h σ * suConj h B ∧ suConj h B ^ 3 = 1 ∧
      suConj h B ≠ 1 ∧ ∀ y (hy : y ∈ A), ∃ i j : ℕ,
        inducedAutHom L e ⟨y, hAL hy⟩ = suConj h B ^ i * suField h σ ^ j := by
  have hAel := hyp.mem_partTwoF.1
  have hA3 : ∀ y ∈ A, y ^ 3 = 1 := hAel.2
  have hAcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hcA := hyp.mem_A
  have haA := hyp.a_mem
  have hcN := hAL hcA
  have haN := hAL haA
  have hc3 := hA3 c hcA
  have ha3 := hA3 a haA
  have hL : Sec8.IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ 3) := by
    obtain ⟨K₀, _, _, h1 | h1⟩ := hSL
    · exact absurd h1.2.1 (by norm_num)
    · exact ⟨K₀, inferInstance, inferInstance, h1.1, h1.2.2⟩
  have hm3 : 3 ∣ 2 ^ 3 + 1 := by norm_num
  have ha : InducesStdKind L a .field := by
    rcases hyp.inducesStdKind with h1 | h1
    · exact h1
    · exact absurd h1 (not_inducesStdKind_graphField_of_isoSUThree le_rfl hm3 hL)
  obtain ⟨K, _, h, hq, e, haN', hfield⟩ := inducesKindSU3_of_inducesStdKind le_rfl hm3 hL ha
  have := h.finite
  have hβ3 : inducedAutHom L e ⟨a, haN'⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one L e haN' ha3
  have hα3 : suDescend h hq (inducedAutHom L e ⟨a, haN'⟩) ^ 3 = 1 := by
    rw [← map_pow, hβ3, map_one]
  have hD : suDescend h hq (inducedAutHom L e ⟨a, haN'⟩) ∉ (psuConj h).range :=
    (stdPinnedPSU3_separated h).not_mem_inndiag_of_isField hfield
  obtain ⟨σ, hσ3, H, hαH⟩ := unitary_order_three_field_descent hq _ hα3 hD
  have hlift : inducedAutHom L e ⟨a, haN'⟩ = suConj h H * suField h σ * (suConj h H)⁻¹ := by
    apply eq_of_suDescend_eq h hq
    rw [hαH, map_mul, map_mul, map_inv, suDescend_suConj, suDescend_suField]
  set e' := e.trans (suConj h H).symm with he'
  have hee' : e.symm.trans e' = (suConj h H)⁻¹ := by
    refine MulEquiv.ext fun m => ?_
    rw [he', MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  have hγ : ∀ y, inducedAutHom L e' y = (suConj h H)⁻¹ * inducedAutHom L e y * suConj h H := by
    intro y
    rw [inducedAutHom_eq_conj L e e' y, hee', inv_inv]
  have hγa : inducedAutHom L e' ⟨a, haN⟩ = suField h σ := by
    rw [hγ, hlift]
    group
  have hcτ := thetaQuotMulAut_compAction_eq_one_of_hyp81 hyp hcN
  set S := Subgroup.closure ({c, a} : Set G) with hS
  have hca : c * a = a * c := hAcomm c hcA a haA
  have hcS : c ∈ S := Subgroup.subset_closure (by simp)
  have haS : a ∈ S := Subgroup.subset_closure (by simp)
  have hS9 : Nat.card S ≤ 9 := by
    have hsurj : Function.Surjective (fun ij : Fin 3 × Fin 3 =>
        (⟨c ^ (ij.1 : ℕ) * a ^ (ij.2 : ℕ), mul_mem (pow_mem hcS _) (pow_mem haS _)⟩ : S)) := by
      rintro ⟨z, hz⟩
      obtain ⟨i, j, hi, hj, rfl⟩ := exists_pow_mul_pow_of_mem_closure_pair hca hc3 ha3 hz
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩
    calc Nat.card S ≤ Nat.card (Fin 3 × Fin 3) := Nat.card_le_card_of_surjective _ hsurj
      _ = 9 := by simp
  have hSA : S ≤ A := by
    rw [hS, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcA
    · exact haA
  obtain ⟨b, hbA, hbS⟩ : ∃ b ∈ A, b ∉ S := by
    by_contra hcon
    have h0 : A ≤ S := fun y hy => by
      by_contra hyS
      exact hcon ⟨y, hy, hyS⟩
    have h1 := Subgroup.card_le_of_le h0
    rw [h27] at h1
    omega
  have hbN := hAL hbA
  have hγb3 : inducedAutHom L e' ⟨b, hbN⟩ ^ 3 = 1 := inducedAutHom_pow_eq_one L e' hbN (hA3 b hbA)
  have hγba : inducedAutHom L e' ⟨b, hbN⟩ * suField h σ =
      suField h σ * inducedAutHom L e' ⟨b, hbN⟩ := by
    rw [← hγa, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAcomm b hbA a haA)
  obtain ⟨B, k, -, hγbB, hBcomm, hB3⟩ := exists_suConj_mul_suField_pow h hq hσ3 hγb3 hγba
  obtain ⟨b', hb'⟩ : ∃ b' : G, b' = b * (a ^ k)⁻¹ := ⟨_, rfl⟩
  have hbb' : b = b' * a ^ k := by rw [hb', inv_mul_cancel_right]
  have hb'A : b' ∈ A := by rw [hb']; exact mul_mem hbA (inv_mem (pow_mem haA k))
  have hb'N := hAL hb'A
  have hγb' : inducedAutHom L e' ⟨b', hb'N⟩ = suConj h B := by
    have h1 : (⟨b', hb'N⟩ : Subgroup.normalizer (L : Set G)) = ⟨b, hbN⟩ * (⟨a, haN⟩ ^ k)⁻¹ :=
      Subtype.ext (by simp [hb'])
    rw [h1, map_mul, map_inv, map_pow, hγa, hγbB, mul_inv_cancel_right]
  have hb'S : b' ∉ S := fun h1 => hbS (by rw [hbb']; exact mul_mem h1 (pow_mem haS k))
  have hB1 : suConj h B ≠ 1 := by
    intro h1
    have h2 : thetaQuotMulAut L (compAction L ⟨b', hb'N⟩) = 1 := by
      have h3 : inducedAutHom L e' ⟨b', hb'N⟩ = 1 := hγb'.trans h1
      rw [inducedAutHom_apply] at h3
      exact (MulAut.congr e').injective (h3.trans (map_one _).symm)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_thetaQuotMulAut_eq_one hyp hb'N hb'A h2)
    apply hb'S
    rw [← hm]
    exact zpow_mem hcS m
  have hac : a ∉ Subgroup.zpowers c := by
    intro h1
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    apply hD
    have h2 : inducedAutHom L e ⟨a, haN'⟩ = 1 := by
      have h3 : (⟨a, haN'⟩ : Subgroup.normalizer (L : Set G)) = ⟨c, hcN⟩ ^ m :=
        Subtype.ext (by simp [hm])
      rw [h3, map_zpow, inducedAutHom_apply, hcτ, map_one, one_zpow]
    rw [h2, map_one]
    exact Subgroup.one_mem _
  have hS9' : Nat.card S = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hc3 ha3 hca hyp.ne_one hac
  set T := S ⊔ Subgroup.zpowers b' with hT
  have hTA : T ≤ A := sup_le hSA (Subgroup.zpowers_le.mpr hb'A)
  have hST : S ≤ T := le_sup_left
  have hb'T : b' ∈ T := (le_sup_right : Subgroup.zpowers b' ≤ T) (Subgroup.mem_zpowers b')
  have hTeq : T = A := by
    have h1 : Nat.card S ∣ Nat.card T := Subgroup.card_dvd_of_le hST
    have h2 : Nat.card T ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
      exact Subgroup.card_dvd_of_le hTA
    have h3 : Nat.card T ≠ 9 := by
      intro h4
      apply hb'S
      have h5 : S = T := Subgroup.eq_of_le_of_card_ge hST (by rw [h4, hS9'])
      rw [h5]
      exact hb'T
    rw [hS9'] at h1
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    have hT27 : Nat.card T = 27 := by
      rw [hj'] at h1 h3 ⊢
      interval_cases j
      · norm_num at h1
      · norm_num at h1
      · exact absurd (by norm_num) h3
      · norm_num
    exact Subgroup.eq_of_le_of_card_ge hTA (by rw [hT27, h27])
  set Q : Subgroup G := ((Subgroup.closure ({suConj h B, suField h σ} :
      Set (MulAut (unitarySU 2 3 K 3)))).comap (inducedAutHom L e')).map
      (Subgroup.normalizer (L : Set G)).subtype with hQ
  have hmemQ : ∀ y (hy : y ∈ Subgroup.normalizer (L : Set G)), inducedAutHom L e' ⟨y, hy⟩ ∈
      Subgroup.closure ({suConj h B, suField h σ} : Set (MulAut (unitarySU 2 3 K 3))) →
      y ∈ Q := fun y hy h1 => ⟨⟨y, hy⟩, h1, rfl⟩
  have hcQ : c ∈ Q := hmemQ c hcN (by rw [inducedAutHom_apply, hcτ, map_one]; exact one_mem _)
  have haQ : a ∈ Q := hmemQ a haN (by rw [hγa]; exact Subgroup.subset_closure (by simp))
  have hb'Q : b' ∈ Q := hmemQ b' hb'N (by rw [hγb']; exact Subgroup.subset_closure (by simp))
  have hAQ : A ≤ Q := by
    rw [← hTeq, hT]
    refine sup_le ?_ (Subgroup.zpowers_le.mpr hb'Q)
    rw [hS, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcQ
    · exact haQ
  have hσ3' : suField h σ ^ 3 = 1 := by
    rw [← map_pow, show σ ^ 3 = 1 by rw [← hσ3]; exact pow_orderOf_eq_one σ, map_one]
  refine ⟨K, inferInstance, h, e', σ, B, b', hb'A, hσ3, hγb', hBcomm, hB3, hB1, fun y hy => ?_⟩
  obtain ⟨⟨y', hy'N⟩, hy'Q, rfl⟩ := hAQ hy
  have hy'Q' : inducedAutHom L e' ⟨y', hy'N⟩ ∈
      Subgroup.closure ({suConj h B, suField h σ} : Set (MulAut (unitarySU 2 3 K 3))) := hy'Q
  obtain ⟨i, j, -, -, hij⟩ := exists_pow_mul_pow_of_mem_closure_pair hBcomm hB3 hσ3' hy'Q'
  exact ⟨i, j, hij⟩

theorem exists_mem_inducedAutHom_eq_conj_of_fixed_of_hyp81 {A : Subgroup G} {c a : G}
    (hyp : Sec8.Hyp81 G A c L a) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] {h : UnitaryFieldData 2 3 K}
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU 2 3 K 3) {σ : K ≃+* K} {B : unitaryIsom3 h}
    (hA : ∀ y (hy : y ∈ A), ∃ i j : ℕ,
      inducedAutHom L e ⟨y, hAL hy⟩ = suConj h B ^ i * suField h σ ^ j)
    {x : unitarySU 2 3 K 3} (hx3 : x ^ 3 = 1) (hσx : suField h σ x = x)
    (hBx : suConj h B x = x) :
    ∃ (d : G) (hdA : d ∈ A), inducedAutHom L e ⟨d, hAL hdA⟩ = MulAut.conj x := by
  obtain ⟨xbar, hxbar⟩ : ∃ xbar, xbar = e.symm x := ⟨_, rfl⟩
  have hxbar3 : xbar ^ 3 = 1 := by rw [hxbar, ← map_pow, hx3, map_one]
  have hfix : ∀ y (hy : y ∈ A), thetaQuotMulAut L (compAction L ⟨y, hAL hy⟩) xbar = xbar := by
    intro y hy
    obtain ⟨i, j, hij⟩ := hA y hy
    have h1 : inducedAutHom L e ⟨y, hAL hy⟩ x = x := by
      rw [hij, MulAut.mul_apply, mulAut_pow_apply_eq hσx, mulAut_pow_apply_eq hBx]
    rw [inducedAutHom_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.trans_apply] at h1
    have h2 := congrArg e.symm h1
    rw [MulEquiv.symm_apply_apply] at h2
    rw [hxbar]
    exact h2
  obtain ⟨d, hdL, hdA, hdx⟩ :=
    exists_mem_of_fixed_of_pow_three hyp.mem_partTwoF.1 hyp.mem_partTwoF.2.1 hAL hxbar3 hfix
  refine ⟨d, hdA, ?_⟩
  rw [inducedAutHom_eq_conj_of_mem e hdL (hAL hdA), hdx, hxbar, MulEquiv.apply_symm_apply]

end SU38Model

section SU38Cent

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open Matrix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_suConj_of_hyp81 {A : Subgroup G} {c a : G}
    (hyp : Sec8.Hyp81 G A c L a) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] {h : UnitaryFieldData 2 3 K}
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU 2 3 K 3) {σ : K ≃+* K} (hσ3 : orderOf σ = 3)
    {B : unitaryIsom3 h} (hBσ : suConj h B * suField h σ = suField h σ * suConj h B)
    (hB3 : suConj h B ^ 3 = 1) (hB1 : suConj h B ≠ 1)
    (hA : ∀ y (hy : y ∈ A), ∃ i j : ℕ,
      inducedAutHom L e ⟨y, hAL hy⟩ = suConj h B ^ i * suField h σ ^ j) :
    ∃ w : unitarySU 2 3 K 3, w ^ 3 = 1 ∧ suConj h B = MulAut.conj w := by
  have hq : 2 < 2 ^ 3 := by norm_num
  by_contra hcon
  rcases su38_dichotomy h hσ3 B hBσ hB3 hB1 with ⟨w, hw3, -, hBw⟩ | ⟨x, hx3, hxs, hσx, hBx⟩
  · exact hcon ⟨w, hw3, hBw⟩
  obtain ⟨d, hdA, hγd⟩ :=
    exists_mem_inducedAutHom_eq_conj_of_fixed_of_hyp81 hyp hAL e hA hx3 hσx hBx
  obtain ⟨i, j, hij⟩ := hA d hdA
  have h1 : MulAut.conj x = suConj h B ^ i * suField h σ ^ j := hγd.symm.trans hij
  have hσj : σ ^ j = 1 := by
    refine eq_one_of_suConj_eq_suConj_mul_suField h hq (X := ⟨x, unitarySU_le_unitaryIsom3 x.2⟩)
      (Y := B ^ i) ?_
    rw [← mulAut_conj_eq_suConj, h1, map_pow, map_pow]
  rw [← map_pow (suField h), hσj, map_one, mul_one] at h1
  rw [mulAut_pow_mod_three hB3 i] at h1
  obtain ⟨r, hr⟩ : ∃ r, r = i % 3 := ⟨_, rfl⟩
  rw [← hr] at h1
  have hr3 : r < 3 := hr ▸ Nat.mod_lt _ (by norm_num)
  interval_cases r
  ·
    rw [pow_zero] at h1
    obtain ⟨c', -, hc'⟩ := exists_scalar_of_conj_eq_one h hq h1
    apply hxs (c' : K)
    rw [hc', GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  · rw [pow_one] at h1
    exact hcon ⟨x, hx3, h1.symm⟩
  · refine hcon ⟨x ^ 2, by rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow], ?_⟩
    rw [map_pow, h1, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hB3, one_mul, pow_one]

theorem eq_bot_of_hyp81_su38 {A : Subgroup G} {c a : G}
    (hyp : Sec8.Hyp81 G A c L a) (h27 : Nat.card A = 27)
    (hSL : IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) 8)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {e : G}
    (heA : e ∈ A) (hec : e ∉ Subgroup.zpowers c) (he : e ∈ Subgroup.normalizer (L : Set G))
    (N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)))
    (hNc : ∀ ν ∈ N, ν * thetaQuotMulAut L (compAction L ⟨e, he⟩) =
      thetaQuotMulAut L (compAction L ⟨e, he⟩) * ν)
    (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ ℓ : L ⧸ aschbacherSolvableCore 3 L,
      thetaQuotMulAut L (compAction L ⟨e, he⟩) ℓ = ℓ →
        ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) :
    N = ⊥ := by
  have hq : 2 < 2 ^ 3 := by norm_num
  obtain ⟨K, _, h, e', σ, B, b, hbA, hσ3, hγb, hBσ, hB3, hB1, hA⟩ :=
    exists_su38_model_of_hyp81 hyp h27 hSL hAL
  have := h.finite
  obtain ⟨w, hw3, hBw⟩ := exists_conj_eq_suConj_of_hyp81 hyp hAL e' hσ3 hBσ hB3 hB1 hA
  obtain ⟨i, j, hij⟩ := hA e heA
  have hσ3' : σ ^ 3 = 1 := by rw [← hσ3]; exact pow_orderOf_eq_one σ
  have hσf3 : suField h σ ^ 3 = 1 := by rw [← map_pow, hσ3', map_one]
  have hw3' : MulAut.conj w ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
  have hwσ : Commute (MulAut.conj w) (suField h σ) := by
    rw [← hBw]
    exact hBσ
  have hε : MulAut.congr e' (thetaQuotMulAut L (compAction L ⟨e, he⟩)) =
      MulAut.conj (w ^ (i % 3)) * suField h σ ^ (j % 3) := by
    rw [← inducedAutHom_apply, show (⟨e, he⟩ : Subgroup.normalizer (L : Set G)) = ⟨e, hAL heA⟩
      from rfl, hij, hBw, mulAut_pow_mod_three hw3' i, mulAut_pow_mod_three hσf3 j, map_pow]
  have hε1 : MulAut.conj (w ^ (i % 3)) * suField h σ ^ (j % 3) ≠ 1 := by
    intro h1
    apply hec
    refine mem_zpowers_of_thetaQuotMulAut_eq_one hyp he heA ?_
    have h2 := hε.trans h1
    exact (MulAut.congr e').injective (h2.trans (map_one _).symm)
  refine eq_bot_of_congr e' (fun N₀ hc h3 hn => ?_) hNc hN3 hNn
  rw [hε] at hc hn
  have hmodj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hmodi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  by_cases hj0 : j % 3 = 0
  ·
    rw [hj0, pow_zero, mul_one] at hc hn hε1
    have hu3 : (w ^ (i % 3)) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw3, one_pow]
    have hus : ∀ c' : K, ((w ^ (i % 3) : unitarySU 2 3 K 3) : GL (Fin 3) K) ≠
        c' • (1 : Matrix (Fin 3) (Fin 3) K) := by
      intro c' hc'
      apply hε1
      refine MulEquiv.ext fun g => ?_
      rw [MulAut.conj_apply, MulAut.one_apply]
      have hcomm : w ^ (i % 3) * g = g * w ^ (i % 3) := by
        apply Subtype.ext
        apply Units.ext
        simp only [Subgroup.coe_mul, Units.val_mul, hc', Matrix.smul_mul, Matrix.one_mul,
          Matrix.mul_smul, Matrix.mul_one]
      rw [hcomm, mul_inv_cancel_right]
    exact eq_bot_of_commute_conj h hu3 hus hc h3 hn
  ·
    set ε' := MulAut.conj (w ^ (i % 3)) * suField h σ ^ (j % 3) with hε'
    have hε'3 : ε' ^ 3 = 1 := by
      have hc' : Commute (MulAut.conj (w ^ (i % 3))) (suField h σ ^ (j % 3)) := by
        rw [map_pow]
        exact (hwσ.pow_left _).pow_right _
      have e1 : MulAut.conj (w ^ (i % 3)) ^ 3 = 1 := by
        rw [← map_pow, ← pow_mul, mul_comm (i % 3) 3, pow_mul, hw3, one_pow, map_one]
      have e2 : (suField h σ ^ (j % 3)) ^ 3 = 1 := by
        rw [← pow_mul, mul_comm (j % 3) 3, pow_mul, hσf3, one_pow]
      rw [hε', hc'.mul_pow, e1, e2, one_mul]
    have hD : suDescend h hq ε' ∉ (psuConj h).range := by
      rintro ⟨X, hX⟩
      apply hj0
      have h1 : suConj h X = suConj h ⟨_, unitarySU_le_unitaryIsom3 (w ^ (i % 3)).2⟩ *
          suField h (σ ^ (j % 3)) := by
        apply eq_of_suDescend_eq h hq
        rw [suDescend_suConj, hX, hε', map_mul, mulAut_conj_eq_suConj h, ← map_pow (suField h),
          map_mul]
      have h2 := eq_one_of_suConj_eq_suConj_mul_suField h hq h1
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hσ3] at h3
      have h4 : j % 3 < 3 := hmodj
      omega
    have hα3 : suDescend h hq ε' ^ 3 = 1 := by rw [← map_pow, hε'3, map_one]
    obtain ⟨σ', hσ'3, H', hαH⟩ := unitary_order_three_field_descent hq _ hα3 hD
    have hlift : ε' = suConj h H' * suField h σ' * (suConj h H')⁻¹ := by
      apply eq_of_suDescend_eq h hq
      rw [hαH, map_mul, map_mul, map_inv, suDescend_suConj, suDescend_suField]
    exact eq_bot_of_conj hlift (fun N₁ hc₁ h₁ hn₁ => eq_bot_of_commute_suField h hσ'3 hc₁ h₁ hn₁)
      hc h3 hn

end SU38Cent

end CFSG.RankThree.PartTwo.KFacts
