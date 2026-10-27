module

public import CFSG.RankThree.PartTwo.KFacts.K71L28TwoFree
public import CFSG.RankThree.PartTwo.KFacts.K71Item93
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.RankThree.PartTwo.KFacts.K73Lines
import CFSG.RankThree.PartTwo.Sec8.Outer
import CFSG.RankThree.Asc83Table.E9

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_galoisField_two_three : Nat.card (GaloisField 2 3) = 8 := by
  rw [GaloisField.card 2 3 (by norm_num)]
  norm_num

theorem card_ringAut_of_card_eight {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    Nat.card (K ≃+* K) = 3 :=
  (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
    (by rw [hK]; norm_num : Nat.card K = 2 ^ 3)).1

theorem card_ringAut_galoisField_two_three :
    Nat.card (GaloisField 2 3 ≃+* GaloisField 2 3) = 3 :=
  card_ringAut_of_card_eight card_galoisField_two_three

theorem exists_l28_model_aux {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    {A : Subgroup G} {c a : G} {R : Subgroup G} (hyp : Sec9.Hyp91 G A c L a R)
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
    (not_isInnerAut_inducedAutHom_iff L e₀ haN).mpr hyp.toHyp81.inducesOuterTheta
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
  have hcτ := thetaQuotMulAut_compAction_eq_one_of_hyp81 hyp.toHyp81 hcN
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
    rw [hyp.card_eq] at h1
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
      (mem_zpowers_of_thetaQuotMulAut_eq_one hyp.toHyp81 hb'N hb'A h2)
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
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hyp.card_eq]
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
    exact Subgroup.eq_of_le_of_card_ge hTA (by rw [hT27, hyp.card_eq])
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

theorem exists_l28_model_of_hyp91 {A : Subgroup G} {c a : G} {R : Subgroup G}
    (hyp : Sec9.Hyp91 G A c L a R)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL(2, GaloisField 2 3))
      (σ : GaloisField 2 3 ≃+* GaloisField 2 3) (x : PSL(2, GaloisField 2 3)) (b : G)
      (hbA : b ∈ A), orderOf σ = 3 ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧ psl2FieldAut _ σ x = x ∧
      inducedAutHom L e ⟨b, hAL hbA⟩ = MulAut.conj x ∧
      ∀ y (hy : y ∈ A), ∃ i j : ℕ,
        inducedAutHom L e ⟨y, hAL hy⟩ = MulAut.conj x ^ i * psl2FieldAut _ σ ^ j :=
  exists_l28_model_aux card_galoisField_two_three hyp
    (hL.some.trans (projSLEquivPSL (GaloisField 2 3))) hAL

theorem not_invTwoBarNontrivial_of_hyp91_psl28 {A : Subgroup G} {c a : G} {R : Subgroup G}
    (hyp : Sec9.Hyp91 G A c L a R)
    (hL : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) : ¬ Sec8.InvTwoBarNontrivial A L := by
  obtain ⟨e, σ, x, b, hbA, -, hx3, hx1, -, hγb, -⟩ := exists_l28_model_of_hyp91 hyp hL hAL
  exact not_invTwoBarNontrivial_of_inducedAutHom_eq_conj_psl28 e hbA (hAL hbA) hx3 hx1 hγb

end CFSG.RankThree.PartTwo.KFacts
