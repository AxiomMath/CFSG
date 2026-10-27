module

public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore
public import CFSG.RankThree.Chevalley.G2CyclotomicTori
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
open scoped Pointwise commutatorElement

theorem odd_G2_cyclotomic_three_six_inner_actor_local_core_product_odd {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f)
    (ε : ℤ) (hε : ε = -1 ∨ ε = 1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1)
    (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) (t : B)
    (htE : t ∈ E) (ht1 : t ≠ 1)
    (htinn : (t : MulAut (adjointGroup .G2 K)) ∈
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    ¬E.map B.subtype ≤ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ∧
    thetaT p E = ⊥ ∧
    ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ : Subgroup B) :
        Set B) * (thetaT p E : Set B) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔ thetaT p E :
        Subgroup B) : Set B) ∧
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔
      thetaT p E)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  set R := (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range with hR
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  obtain ⟨hNFpt, Θ, -, -, hΘker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2 (Or.inr ⟨rfl, hℓ3⟩)
  have hNF := conj_normalForm_of_pointwise hNFpt
  obtain ⟨φ, -, -, hφgen, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφgen⟩
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  have hq3 : 3 ≤ Nat.card K := by
    rw [hK]
    have := hℓ.two_le
    calc 3 ≤ ℓ := by omega
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  set d : ℕ := ((Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1).toNat with hd
  have hdZ : (d : ℤ) = (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1 := by
    refine Int.toNat_of_nonneg ?_
    have : (3 : ℤ) ≤ Nat.card K := by exact_mod_cast hq3
    rcases hε with rfl | rfl <;> nlinarith
  have hpd : p ∣ d := by
    rw [← hdZ] at hpq
    exact_mod_cast hpq
  obtain ⟨T, -, -, -, hcyc, hcent⟩ :=
    odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hKodd ε hε d hdZ hp hp3 hpd
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  have hEn : ¬E.map B.subtype ≤ R := by
    intro hle
    set P : Subgroup (adjointGroup .G2 K) := (E.map B.subtype).comap MulAut.conj
    have hPmap : P.map MulAut.conj = E.map B.subtype := Subgroup.map_comap_eq_self hle
    have e : E ≃* P := (Subgroup.equivMapOfInjective E B.subtype B.subtype_injective).trans
      ((MulEquiv.subgroupCongr hPmap.symm).trans (Subgroup.equivMapOfInjective P _ hinj).symm)
    have hPp : IsPGroup p P := (IsElementaryAbelian.isPGroup p E).of_equiv e
    have := hcyc P hPp
    have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact (pow_pos hp.pos 2).ne')
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEcard
      (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  obtain ⟨b, hbE, hbinn⟩ : ∃ b ∈ E, (b : MulAut (adjointGroup .G2 K)) ∉ R := by
    by_contra h
    push Not at h
    exact hEn (by rintro _ ⟨b, hb, rfl⟩; exact h b hb)
  have hb1 : b ≠ 1 := fun h => hbinn (by rw [h]; exact one_mem _)
  have hbp : orderOf b = p := orderOf_eq_prime (hEpow b hbE) hb1
  have hIB : thetaT p E = ⊥ := by
    obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF b
    have hcore := (odd_Chevalley_inner_field_noninner_prime_local_core_trivial .G2 hℓ hℓ2 hf K hK
      hNF hp B hB b hbinn hbp x σ hxσ).2.2.2
    refine eq_bot_iff.2 (iInf_le_of_le b (iInf_le_of_le hbE (iInf_le_of_le hb1 ?_)))
    rw [inSubgroup, hcore, Subgroup.map_bot]
  obtain ⟨x, hx⟩ := htinn
  have htp : orderOf t = p := orderOf_eq_prime (hEpow t htE) ht1
  have hxp : orderOf x = p := by
    rw [← orderOf_injective _ hinj x, hx, Subgroup.orderOf_coe, htp]
  obtain ⟨-, -, -, hxcard, hdodd⟩ := hcent x hxp
  set S := inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)) with hS
  have hSt : S ≤ Subgroup.centralizer ({t} : Set B) := Subgroup.map_subtype_le _
  have hEt : E ≤ Subgroup.centralizer ({t} : Set B) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val
      (hE.is_comm.comm (⟨t, htE⟩ : E) ⟨e, he⟩)).symm
  have hle : ⁅S, E⁆ ≤ ((Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))).map
      MulAut.conj).comap B.subtype := by
    rw [Subgroup.commutator_le]
    intro s hs e he
    have hct : ⁅s, e⁆ ∈ Subgroup.centralizer ({t} : Set B) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hSt hs) (hEt he)) (inv_mem (hSt hs))) (inv_mem (hEt he))
    have hΘ : ((⁅s, e⁆ : B) : MulAut (adjointGroup .G2 K)) ∈ R := by
      rw [hR, ← hΘker, MonoidHom.mem_ker, show ((⁅s, e⁆ : B) : MulAut (adjointGroup .G2 K)) =
        ⁅(s : MulAut (adjointGroup .G2 K)), (e : MulAut (adjointGroup .G2 K))⁆ from
          map_commutatorElement B.subtype s e, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact IsMulCommutative.is_comm.comm _ _
    obtain ⟨y, hy⟩ := hΘ
    refine ⟨y, Subgroup.mem_centralizer_singleton_iff.2 (hinj ?_), hy⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hct)
    simp only [Subgroup.coe_mul] at h1
    rw [map_mul, map_mul, hy, hx]
    exact h1
  have hdvd : Nat.card ↥(⁅S, E⁆ : Subgroup B) ∣ d := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective, ← hxcard,
      ← Subgroup.card_map_of_injective hinj]
    exact Subgroup.card_dvd_of_le (Subgroup.map_le_iff_le_comap.2 hle)
  refine ⟨hEn, hIB, ?_, ?_⟩
  · rw [hIB, sup_bot_eq, Subgroup.coe_bot, Set.mul_singleton]
    simp
  · rw [hIB, sup_bot_eq]
    exact hdodd.of_dvd_nat hdvd

end CFSG.RankThree.Chevalley
