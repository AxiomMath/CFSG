module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveTorus
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
open scoped Pointwise commutatorElement

theorem triality_normal_form_data {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ ∧
    IsCyclic (K ≃+* K) ∧
    ∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
  rcases eq_or_ne ℓ 2 with rfl | hℓ2
  · obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, hcyc, -, -, hZ, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact ⟨hZ, hcyc, Θ, hΘ, hker⟩
  · obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, hcyc, -, -, hZ, -⟩ :=
      odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
    exact ⟨hZ, hcyc, Θ, hΘ, hker⟩

theorem triality_cyclotomic_twelve_local_core_product_odd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1)
    (B : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hB : (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) (t : B)
    (htE : t ∈ E) (ht1 : t ≠ 1) :
    ¬E.map B.subtype ≤ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range ∧
    thetaT p E = ⊥ ∧
    ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ : Subgroup B) :
        Set B) * (thetaT p E : Set B) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔ thetaT p E :
        Subgroup B) : Set B) ∧
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer {t}), E⁆ ⊔
      thetaT p E)) ∧
    ((t : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∉
        (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
          MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range →
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)) = ⊥ ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)), E⁆ ⊔
        thetaT p E = ⊥) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  set R := (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
    MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range with hR
  obtain ⟨hZ, hcycAut, Θ, hΘ, hΘker⟩ := triality_normal_form_data hℓ hf K hK σ hσ
  have hinj : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    mulAut_conj_injective_of_center_eq_bot hZ
  obtain ⟨T, -, -, htor⟩ := triality_cyclotomic_twelve_torus_and_prime_centralizers hℓ hf K hK σ hσ
  obtain ⟨-, hcyc, hcent⟩ := htor p hp hp3 hpd
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    have h' := congrArg Subtype.val h
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h'
  have hEn : ¬E.map B.subtype ≤ R := by
    intro hle
    set P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      (E.map B.subtype).comap MulAut.conj
    have hPmap : P.map MulAut.conj = E.map B.subtype := Subgroup.map_comap_eq_self hle
    have e : E ≃* P := (Subgroup.equivMapOfInjective E B.subtype B.subtype_injective).trans
      ((MulEquiv.subgroupCongr hPmap.symm).trans (Subgroup.equivMapOfInjective P _ hinj).symm)
    have hPp : IsPGroup p P := (IsElementaryAbelian.isPGroup p E).of_equiv e
    have := hcyc P hPp
    have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact (pow_pos hp.pos 2).ne')
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEcard
      (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  have hcore : ∀ b : B, (b : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∉ R →
      orderOf b = p →
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set B)) = ⊥ := by
    intro b hb hbp
    have h := (triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK σ hσ
      Θ hΘ hp hp3 B hB b hb hbp).2.2.2
    rw [inSubgroup, h, Subgroup.map_bot]
  obtain ⟨b, hbE, hbinn⟩ :
      ∃ b ∈ E, (b : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∉ R := by
    by_contra h
    push Not at h
    exact hEn (by rintro _ ⟨b, hb, rfl⟩; exact h b hb)
  have hb1 : b ≠ 1 := fun h => hbinn (by rw [h]; exact one_mem _)
  have hbp : orderOf b = p := orderOf_eq_prime (hEpow b hbE) hb1
  have hIB : thetaT p E = ⊥ :=
    eq_bot_iff.2 (iInf_le_of_le b (iInf_le_of_le hbE (iInf_le_of_le hb1 (hcore b hbinn hbp).le)))
  have htp : orderOf t = p := orderOf_eq_prime (hEpow t htE) ht1
  set S := inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)) with hS
  have hset : ((⁅S, E⁆ : Subgroup B) : Set B) * (thetaT p E : Set B) =
      ((⁅S, E⁆ ⊔ thetaT p E : Subgroup B) : Set B) := by
    rw [hIB, sup_bot_eq, Subgroup.coe_bot, Set.mul_singleton]
    simp only [mul_one, Set.image_id']
  have hnon : (t : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∉ R →
      S = ⊥ ∧ ⁅S, E⁆ ⊔ thetaT p E = ⊥ := fun ht => by
    have hS1 : S = ⊥ := hcore t ht htp
    refine ⟨hS1, ?_⟩
    rw [hS1, Subgroup.commutator_bot_left, bot_sup_eq, hIB]
  by_cases htinn : (t : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈ R
  ·
    obtain ⟨x, hx⟩ := htinn
    have hxp : orderOf x = p := by
      rw [← orderOf_injective _ hinj x, hx, Subgroup.orderOf_coe, htp]
    obtain ⟨g, hgT, hgcent, -, hodd⟩ := hcent x hxp
    have hSt : S ≤ Subgroup.centralizer ({t} : Set B) := Subgroup.map_subtype_le _
    have hEt : E ≤ Subgroup.centralizer ({t} : Set B) := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val
        (hE.is_comm.comm (⟨t, htE⟩ : E) ⟨e, he⟩)).symm
    have : IsMulCommutative (K ≃+* K) := ⟨⟨fun a b => (IsCyclic.commGroup.mul_comm a b)⟩⟩
    have hle : ⁅S, E⁆ ≤ ((Subgroup.centralizer
        ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map MulAut.conj).comap
          B.subtype := by
      rw [Subgroup.commutator_le]
      intro s hs e he
      have hct : ⁅s, e⁆ ∈ Subgroup.centralizer ({t} : Set B) := by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem (hSt hs) (hEt he)) (inv_mem (hSt hs))) (inv_mem (hEt he))
      have hΘ1 : ((⁅s, e⁆ : B) : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∈ R := by
        rw [hR, ← hΘker, MonoidHom.mem_ker,
          show ((⁅s, e⁆ : B) : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
          ⁅(s : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
            (e : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ from
              map_commutatorElement B.subtype s e,
          map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact IsMulCommutative.is_comm.comm _ _
      obtain ⟨y, hy⟩ := hΘ1
      refine ⟨y, Subgroup.mem_centralizer_singleton_iff.2 (hinj ?_), hy⟩
      have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hct)
      simp only [Subgroup.coe_mul] at h1
      rw [map_mul, map_mul, hy, hx]
      exact h1
    have hdvd : Nat.card ↥(⁅S, E⁆ : Subgroup B) ∣
        Nat.card (Subgroup.centralizer
          ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
      rw [← Subgroup.card_map_of_injective B.subtype_injective,
        ← Subgroup.card_map_of_injective hinj]
      exact Subgroup.card_dvd_of_le (Subgroup.map_le_iff_le_comap.2 hle)
    refine ⟨hEn, hIB, hset, ?_, fun h => absurd ⟨x, hx⟩ h⟩
    rw [hIB, sup_bot_eq]
    exact hodd.of_dvd_nat hdvd
  · obtain ⟨hS1, hW⟩ := hnon htinn
    refine ⟨hEn, hIB, hset, ?_, fun _ => ⟨hS1, hW⟩⟩
    rw [hW, Subgroup.card_bot]
    exact odd_one

end CFSG.RankThree.Chevalley
