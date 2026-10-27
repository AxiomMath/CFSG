module

public import CFSG.Foundations.Basic
import CFSG.ClassicalInvolution.SL2Facts
import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeRecognition
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open Matrix CFSG
open scoped MatrixGroups

theorem isQuasisimple_of_isPerfect {Q : Type*} [Group Q] [Group.IsPerfect Q]
    (h : IsSimpleGroup (Q ⧸ Subgroup.center Q)) : IsQuasisimple Q := by
  refine ⟨inferInstance, h, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have : IsMulCommutative (Q ⧸ Subgroup.center Q) := ⟨⟨hcomm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q) this

section SL2

variable {p : ℕ} [hp : Fact p.Prime]

theorem isQuasisimple_SL2 (hp5 : 5 ≤ p) : IsQuasisimple SL(2, ZMod p) := by
  have h4 : 4 ≤ Nat.card (ZMod p) := by
    rw [Nat.card_zmod]
    omega
  have := ClassicalInvolution.sl2_isPerfect h4
  exact isQuasisimple_of_isPerfect (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4)

theorem card_center_SL2 (hp2 : p ≠ 2) : Nat.card (Subgroup.center SL(2, ZMod p)) = 2 :=
  ClassicalInvolution.sl2_natCard_center (by
    rw [Nat.card_zmod]
    exact hp.out.odd_of_ne_two hp2)

theorem card_SL2 : Nat.card SL(2, ZMod p) = p * (p ^ 2 - 1) := by
  rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_two]
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have h : (p ^ 2 - p ^ ((0 : Fin 2) : ℕ)) * (p ^ 2 - p ^ ((1 : Fin 2) : ℕ)) =
      p * (p ^ 2 - 1) * (p - 1) := by
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have : p ^ 2 - p = p * (p - 1) := by
      rw [Nat.mul_sub_one, sq]
    rw [this]
    ring
  rw [h, Nat.mul_div_cancel _ (by have := hp.out.two_le; omega)]

theorem two_dvd_card_PSL2 (F : Type*) [Field F] [Finite F] :
    2 ∣ Nat.card (ProjectiveSpecialLinearGroup (Fin 2) F) := by
  set w := CFSG.Semidihedral.OddLinearNormals.quarterTurn F
  set x : ProjectiveSpecialLinearGroup (Fin 2) F := QuotientGroup.mk w
  have hx1 : x ≠ 1 := fun h => CFSG.Semidihedral.OddLinearNormals.quarterTurn_not_mem_center F
    ((QuotientGroup.eq_one_iff w).mp h)
  have hx2 : x ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact CFSG.Semidihedral.OddLinearNormals.quarterTurn_square_mem_center F
  have := orderOf_dvd_natCard x
  rwa [orderOf_eq_prime hx2 hx1] at this

theorem two_dvd_card_PGL2 (F : Type*) [Field F] [Finite F] :
    2 ∣ Nat.card (Matrix.ProjGenLinGroup (Fin 2) F) := by
  have hw : ((Matrix.SpecialLinearGroup.toGL (CFSG.Semidihedral.OddLinearNormals.quarterTurn F) :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := by
    simp [CFSG.Semidihedral.OddLinearNormals.quarterTurn, Matrix.SpecialLinearGroup.toGL]
  have hx1 : (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
      (CFSG.Semidihedral.OddLinearNormals.quarterTurn F)) : Matrix.ProjGenLinGroup (Fin 2) F) ≠
        1 := by
    intro h
    have hc := (QuotientGroup.eq_one_iff _).mp h
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨c, hc⟩ := hc
    have h0 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      simp [Matrix.GeneralLinearGroup.coe_scalar]
    rw [hc, hw] at h0
    exact one_ne_zero h0
  have hx2 : (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
      (CFSG.Semidihedral.OddLinearNormals.quarterTurn F)) : Matrix.ProjGenLinGroup (Fin 2) F) ^ 2 =
        1 := by
    change (QuotientGroup.mk ((Matrix.SpecialLinearGroup.toGL
      (CFSG.Semidihedral.OddLinearNormals.quarterTurn F)) ^ 2) :
        Matrix.ProjGenLinGroup (Fin 2) F) = 1
    rw [QuotientGroup.eq_one_iff, Matrix.GeneralLinearGroup.center_eq_range_scalar, ← map_pow]
    refine ⟨-1, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.coe_pow,
      CFSG.Semidihedral.OddLinearNormals.quarterTurn_square_matrix]
    simp
  have := orderOf_dvd_natCard (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
    (CFSG.Semidihedral.OddLinearNormals.quarterTurn F)) : Matrix.ProjGenLinGroup (Fin 2) F)
  rwa [orderOf_eq_prime hx2 hx1] at this

theorem isCyclic_sylow_SL2 {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (hrp : r ≠ p)
    (Q : Sylow r SL(2, ZMod p)) : IsCyclic Q := by
  classical
  set π := QuotientGroup.mk' (Subgroup.center SL(2, ZMod p))
  set ψ := π.comp (Q : Subgroup SL(2, ZMod p)).subtype
  have hodd : ∀ q : Q, ∃ k : ℕ, q ^ (r ^ k) = 1 := Q.isPGroup'
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hqc : (q : SL(2, ZMod p)) ∈ Subgroup.center _ := (QuotientGroup.eq_one_iff _).mp hq
    obtain ⟨k, hk⟩ := hodd q
    have h1 : orderOf q ∣ r ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf q ∣ 2 := by
      have hc2 : ∀ z ∈ Subgroup.center SL(2, ZMod p), z ^ 2 = 1 := by
        intro z hz
        rcases (ClassicalInvolution.mem_center_sl2_iff z).mp hz with rfl | rfl
        · exact one_pow 2
        · rw [sq, neg_one_mul, neg_neg]
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one (hc2 _ hqc)
    have h3 : orderOf q = 1 := by
      have hcop : Nat.Coprime 2 (r ^ k) :=
        Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hr.out).mpr (Ne.symm hr2))
      exact Nat.eq_one_of_dvd_coprimes hcop h2 h1
    exact orderOf_eq_one_iff.mp h3
  set H := ψ.range
  have hHr : IsPGroup r H := by
    rintro ⟨_, ⟨q, rfl⟩⟩
    obtain ⟨k, hk⟩ := hodd q
    exact ⟨k, Subtype.ext (by rw [SubgroupClass.coe_pow, ← map_pow, hk, map_one]; rfl)⟩
  have hHodd : ¬ 2 ∣ Nat.card H := by
    obtain ⟨k, hk⟩ := hHr.exists_card_eq
    rw [hk]
    intro h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr.out).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)).symm
  have hcyc : IsCyclic H := by
    have hF : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
    rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      hF H with hE | ⟨z, -, -, hc⟩ | ⟨z, -, hz, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, N, C, hN, hNe, hNm, hCc, -, -, hNC⟩ | ⟨m, -, -, ⟨e⟩⟩ | ⟨m, -, -, ⟨e⟩⟩
    ·
      have htriv : ∀ h : H, h = 1 := by
        intro h
        obtain ⟨k, hk⟩ := hHr h
        have h1 : orderOf h ∣ r ^ k := orderOf_dvd_of_pow_eq_one hk
        have h2 : orderOf h ∣ p := orderOf_dvd_of_pow_eq_one
          (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p H) h)
        have hcop : Nat.Coprime p (r ^ k) :=
          Nat.Coprime.pow_right k ((Nat.coprime_primes hp.out hr.out).mpr (Ne.symm hrp))
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
      have : Subsingleton H := ⟨fun a b => by rw [htriv a, htriv b]⟩
      exact isCyclic_of_subsingleton
    · exact hc
    · exact absurd (hz ▸ dvd_mul_right 2 z) hHodd
    · refine absurd ?_ hHodd
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    · refine absurd ?_ hHodd
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    · refine absurd ?_ hHodd
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    ·
      have hNbot : N = ⊥ := by
        rw [eq_bot_iff]
        intro n hn
        obtain ⟨k, hk⟩ := hHr n
        have h1 : orderOf n ∣ r ^ k := orderOf_dvd_of_pow_eq_one hk
        have h2 : orderOf n ∣ p := by
          have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := N) n hn
          exact orderOf_dvd_of_pow_eq_one this
        have hcop : Nat.Coprime p (r ^ k) :=
          Nat.Coprime.pow_right k ((Nat.coprime_primes hp.out hr.out).mpr (Ne.symm hrp))
        exact (Subgroup.mem_bot).mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1))
      rw [hNbot, bot_sup_eq] at hNC
      have : IsCyclic (⊤ : Subgroup H) := hNC ▸ hCc
      exact isCyclic_of_surjective (Subgroup.topEquiv (G := H)).toMonoidHom
        (Subgroup.topEquiv (G := H)).surjective
    · exact absurd (by rw [Nat.card_congr e.toEquiv]; exact two_dvd_card_PSL2 _) hHodd
    · exact absurd (by rw [Nat.card_congr e.toEquiv]; exact two_dvd_card_PGL2 _) hHodd
  have : IsCyclic H := hcyc
  exact isCyclic_of_injective (MonoidHom.ofInjective hinj).toMonoidHom
    (MonoidHom.ofInjective hinj).injective

end SL2

section SL3

theorem isQuasisimple_SL3_three : IsQuasisimple SL(3, ZMod 3) :=
  CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num)

theorem card_SL3_three : Nat.card SL(3, ZMod 3) = 5616 := by
  rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_three]
  norm_num

theorem center_SL3_three : Subgroup.center SL(3, ZMod 3) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hc
  have key : ∀ c : ZMod 3, c ^ 3 = 1 → c = 1 := by decide
  have hc1 : c = 1 := key c hc
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hcA, hc1, Matrix.SpecialLinearGroup.coe_one]
  exact (Matrix.scalar (Fin 3)).map_one

theorem isCyclic_sylow_SL3_three {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (Q : Sylow r SL(3, ZMod 3)) : IsCyclic Q := by
  obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
  have hdvd : r ^ k ∣ 13 := by
    have h1 : r ^ k ∣ 432 * 13 := by
      rw [← hk, show 432 * 13 = 5616 by norm_num, ← card_SL3_three]
      exact Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.Coprime r 2 := (Nat.coprime_primes hr.out Nat.prime_two).mpr hr2
    have h3 : Nat.Coprime r 3 := (Nat.coprime_primes hr.out Nat.prime_three).mpr hr3
    have hcop : Nat.Coprime (r ^ k) 432 := by
      rw [show (432 : ℕ) = 2 ^ 4 * 3 ^ 3 by norm_num]
      exact Nat.Coprime.pow_left k (Nat.Coprime.mul_right (h2.pow_right 4) (h3.pow_right 3))
    exact (Nat.Coprime.dvd_mul_left hcop).mp h1
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp hdvd with h | h
  · have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp (by rw [hk, h])).1
    exact isCyclic_of_subsingleton
  · rw [h] at hk
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    exact isCyclic_of_prime_card hk

end SL3

theorem exists_sylow_two_PSL25 :
    ∃ Q : Sylow 2 (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)),
      CFSG.Open.IsElemAbelian 2 (Q : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))) ∧
        Nat.card (Q : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))) = 4 := by
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.projective_five_alternating
  have hno4 : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → σ ^ 4 = 1 → σ ^ 2 = 1 := by
    decide +kernel
  have hA : ∀ g : alternatingGroup (Fin 5), g ^ 4 = 1 → g ^ 2 = 1 := fun g hg =>
    Subtype.ext (hno4 g (Equiv.Perm.mem_alternatingGroup.mp g.2) (congrArg Subtype.val hg))
  have hcard : Nat.card (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have h4 : ∀ g : ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5), g ^ 4 = 1 → g ^ 2 = 1 := by
    intro g hg
    apply e.injective
    rw [map_pow, map_one]
    exact hA _ (by rw [← map_pow, hg, map_one])
  obtain ⟨Q⟩ : Nonempty (Sylow 2 (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))) := inferInstance
  have hQ : Nat.card (Q : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))) = 4 := by
    rw [Sylow.card_eq_multiplicity, hcard]
    have : (60 : ℕ).factorization 2 = 2 := by
      rw [show (60 : ℕ) = 2 ^ 2 * 15 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 15 by norm_num)]
    rw [this]
    norm_num
  have hsq : ∀ x ∈ (Q : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))), x ^ 2 = 1 := by
    intro x hx
    apply h4
    have := orderOf_dvd_natCard
      (⟨x, hx⟩ : (Q : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))))
    rw [hQ] at this
    have h1 := orderOf_dvd_iff_pow_eq_one.mp this
    exact congrArg Subtype.val h1
  have key : ∀ y : ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5), y ^ 2 = 1 → y⁻¹ = y :=
    fun y hy => inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hy)
  refine ⟨Q, ⟨⟨⟨fun a b => ?_⟩⟩, hsq⟩, hQ⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  have ha := hsq a a.2
  have hb := hsq b b.2
  have hab := hsq _ (mul_mem a.2 b.2)
  calc (a : ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) * b =
        ((a : ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5)) * b)⁻¹ := (key _ hab).symm
    _ = (b : ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))⁻¹ *
        (a : ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5))⁻¹ := mul_inv_rev _ _
    _ = b * a := by rw [key _ hb, key _ ha]

end CFSG.RankThree.PartTwo.Sec4.Census
