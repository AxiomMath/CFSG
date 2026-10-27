module

public import CFSG.RankThree.GF2n.Smith81.TiRecognition
public import CFSG.RankThree.GF2n.Stroth80.Sec3Action

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

private theorem odd_two_pow_pow_sub_one' {f n : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) :
    Odd ((2 ^ f) ^ n - 1) := by
  have h : 2 ∣ (2 ^ f) ^ n := dvd_pow (dvd_pow_self 2 (by omega)) (by omega)
  have h1 : 1 ≤ (2 ^ f) ^ n := Nat.one_le_pow _ _ (by positivity)
  rw [Nat.odd_iff]
  omega

theorem factorization_two_pow_sub_pow {f m i : ℕ} (hf : 1 ≤ f) (hi : i < m) :
    ((2 ^ f) ^ m - (2 ^ f) ^ i).factorization 2 = f * i := by
  obtain ⟨d, rfl⟩ : ∃ d, m = i + d + 1 := ⟨m - i - 1, by omega⟩
  have hodd : Odd ((2 ^ f) ^ (d + 1) - 1) := odd_two_pow_pow_sub_one' hf (Nat.succ_pos d)
  refine factorization_two_eq_of_odd (m := (2 ^ f) ^ (d + 1) - 1) ?_ hodd
  have h1 : 1 ≤ (2 ^ f) ^ (d + 1) := Nat.one_le_pow _ _ (by positivity)
  rw [show i + d + 1 = i + (d + 1) by ring, pow_add, ← pow_mul, Nat.mul_sub_one]

theorem factorization_prod_GL {f m : ℕ} (hf : 1 ≤ f) :
    (∏ i : Fin m, ((2 ^ f) ^ m - (2 ^ f) ^ (i : ℕ))).factorization 2 = f * (m * (m - 1) / 2) := by
  rw [Nat.factorization_prod]
  · rw [Finsupp.finset_sum_apply]
    have : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        ((2 ^ f) ^ m - (2 ^ f) ^ (i : ℕ)).factorization 2 = f * (i : ℕ) := fun i _ =>
      factorization_two_pow_sub_pow hf i.2
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => i) m,
      Finset.sum_range_id]
  · intro i _
    have : 0 < (2 ^ f) ^ m - (2 ^ f) ^ (i : ℕ) := by
      have := Nat.pow_lt_pow_right (show 1 < 2 ^ f from Nat.one_lt_two_pow (by omega)) i.2
      omega
    omega

section Semilinear

variable {K : Type} [Field K] [Finite K] {E : Type} [AddCommGroup E] [Module K E]

@[expose] def linearEquivConj {V : Type} [AddCommGroup V] [Module K V] (e : E ≃ₗ[K] V) :
    (E ≃ₗ[K] E) ≃ (V ≃ₗ[K] V) where
  toFun u := (e.symm.trans u).trans e
  invFun v := (e.trans v).trans e.symm
  left_inv u := by ext x; simp
  right_inv v := by ext x; simp

theorem card_linearEquiv [Module.Finite K E] {m : ℕ} (hm : Module.finrank K E = m) :
    Nat.card (E ≃ₗ[K] E) = ∏ i : Fin m, (Nat.card K ^ m - Nat.card K ^ (i : ℕ)) := by
  classical
  haveI := Fintype.ofFinite K
  let b : Module.Basis (Fin m) K E := Module.finBasisOfFinrankEq K E hm
  let e : E ≃ₗ[K] (Fin m → K) := b.equivFun
  have h1 : Nat.card (E ≃ₗ[K] E) = Nat.card ((Fin m → K) ≃ₗ[K] (Fin m → K)) :=
    Nat.card_congr (linearEquivConj e)
  have h2 : Nat.card ((Fin m → K) ≃ₗ[K] (Fin m → K)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin m) K) :=
    Nat.card_congr ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin m → K))).toEquiv.symm)
  rw [h1, h2, Matrix.card_GL_field m, Nat.card_eq_fintype_card (α := K)]

theorem card_ringEquiv_self [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    Nat.card (K ≃+* K) = f := by
  classical
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfr : Module.finrank (ZMod 2) K = f := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [hK, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have e : (K ≃+* K) ≃ (K ≃ₐ[ZMod 2] K) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) (fun x => by
        have := RingHom.ext_zmod ((σ : K →+* K).comp (algebraMap (ZMod 2) K))
          (algebraMap (ZMod 2) K)
        exact congrArg (fun g => g x) this)
      invFun := fun τ => τ.toRingEquiv
      left_inv := fun σ => rfl
      right_inv := fun τ => rfl }
  rw [Nat.card_congr e, IsGalois.card_aut_eq_finrank, hfr]

@[expose] def semilinearPerm (K : Type) [Field K] (E : Type) [AddCommGroup E] [Module K E] :
    Subgroup (Equiv.Perm E) where
  carrier := {T | (∀ x y : E, T (x + y) = T x + T y) ∧
    ∃ σ : K ≃+* K, ∀ (c : K) (e : E), T (c • e) = σ c • T e}
  mul_mem' := by
    rintro T T' ⟨hadd, σ, hσ⟩ ⟨hadd', σ', hσ'⟩
    refine ⟨fun x y => ?_, σ'.trans σ, fun c e => ?_⟩
    · simp only [Equiv.Perm.mul_apply, hadd', hadd]
    · simp only [Equiv.Perm.mul_apply, hσ', hσ]
      rfl
  one_mem' := ⟨fun _ _ => rfl, RingEquiv.refl K, fun _ _ => rfl⟩
  inv_mem' := by
    rintro T ⟨hadd, σ, hσ⟩
    refine ⟨fun x y => ?_, σ.symm, fun c e => ?_⟩
    · apply T.injective
      simp [hadd]
    · apply T.injective
      rw [hσ]
      simp

theorem semilinear_unique [Nontrivial E] {T : Equiv.Perm E} {σ σ' : K ≃+* K}
    (h : ∀ (c : K) (e : E), T (c • e) = σ c • T e)
    (h' : ∀ (c : K) (e : E), T (c • e) = σ' c • T e)
    (hadd : ∀ x y : E, T (x + y) = T x + T y) : σ = σ' := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have hT0 : T 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have hTe : T e ≠ 0 := fun h0 => he (T.injective (h0.trans hT0.symm))
  ext c
  have := (h c e).symm.trans (h' c e)
  exact smul_left_injective K hTe this

section SemilinearOrder

variable {K : Type} [Field K] [Finite K] {E : Type} [AddCommGroup E] [Module K E] [Nontrivial E]

noncomputable def semilinearField (T : semilinearPerm K E) : RingAut K :=
  Classical.choose T.2.2

theorem semilinearField_spec (T : semilinearPerm K E) (c : K) (e : E) :
    T.1 (c • e) = semilinearField T c • T.1 e :=
  Classical.choose_spec T.2.2 c e

noncomputable def semilinearHom : semilinearPerm K E →* RingAut K where
  toFun := semilinearField
  map_one' := semilinear_unique (T := (1 : semilinearPerm K E).1) (semilinearField_spec 1)
    (fun _ _ => rfl) (fun _ _ => rfl)
  map_mul' S T := semilinear_unique (T := (S * T).1) (semilinearField_spec (S * T))
    (fun c e => by
      show S.1 (T.1 (c • e)) = _
      rw [semilinearField_spec T, semilinearField_spec S]
      rfl)
    (S * T).2.1

@[expose] def linearToSemilinear : (E ≃ₗ[K] E) →* semilinearPerm K E where
  toFun u := ⟨u.toEquiv, fun x y => map_add u x y, RingEquiv.refl K, fun c e => map_smul u c e⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem linearToSemilinear_injective :
    Function.Injective (linearToSemilinear (K := K) (E := E)) := fun u v h =>
  LinearEquiv.ext fun x => congrArg (fun T : semilinearPerm K E => T.1 x) h

theorem ker_semilinearHom :
    (semilinearHom (K := K) (E := E)).ker = (linearToSemilinear (K := K) (E := E)).range := by
  ext T
  rw [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro hT
    have hT1 : semilinearField T = 1 := hT
    have hlin : ∀ (c : K) (e : E), T.1 (c • e) = c • T.1 e := fun c e => by
      rw [semilinearField_spec T c e, hT1]
      rfl
    refine ⟨AddEquiv.toLinearEquiv ⟨T.1, T.2.1⟩ hlin, ?_⟩
    exact Subtype.ext (Equiv.ext fun x => rfl)
  · rintro ⟨u, rfl⟩
    exact semilinear_unique (T := (linearToSemilinear u).1) (semilinearField_spec _)
      (fun c e => map_smul u c e) (linearToSemilinear u).2.1

theorem card_semilinearPerm :
    Nat.card (semilinearPerm K E) =
      Nat.card (E ≃ₗ[K] E) * Nat.card (semilinearHom (K := K) (E := E)).range := by
  rw [← Subgroup.card_ker_mul_card_range (semilinearHom (K := K) (E := E)), ker_semilinearHom]
  congr 1
  exact (Nat.card_congr (Equiv.ofInjective _ linearToSemilinear_injective)).symm

theorem card_semilinearPerm_dvd [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    Nat.card (semilinearPerm K E) ∣ Nat.card (E ≃ₗ[K] E) * f := by
  rw [card_semilinearPerm]
  refine mul_dvd_mul_left _ ?_
  have := Subgroup.card_subgroup_dvd_card (semilinearHom (K := K) (E := E)).range
  rwa [show Nat.card (RingAut K) = f from card_ringEquiv_self hK] at this

theorem factorization_card_semilinearPerm_le [CharP K 2] [Module.Finite K E] {f m : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hm : Module.finrank K E = m) :
    (Nat.card (semilinearPerm K E)).factorization 2 ≤
      f * (m * (m - 1) / 2) + f.factorization 2 := by
  haveI : Finite E := Module.finite_of_finite K
  haveI : Finite (E ≃ₗ[K] E) :=
    Finite.of_injective (fun u : E ≃ₗ[K] E => (u : E → E)) DFunLike.coe_injective
  have hdvd := card_semilinearPerm_dvd (K := K) (E := E) hK
  have hP : Nat.card (E ≃ₗ[K] E) ≠ 0 := Nat.card_pos.ne'
  rw [card_linearEquiv hm, hK] at hdvd hP
  have hne : (∏ i : Fin m, ((2 ^ f) ^ m - (2 ^ f) ^ (i : ℕ))) * f ≠ 0 :=
    mul_ne_zero hP (by omega)
  have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hne).mpr hdvd 2
  rw [Nat.factorization_mul hP (by omega), Finsupp.add_apply, factorization_prod_GL hf] at hle
  exact hle

end SemilinearOrder

end Semilinear

section Bound

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem factorization_card_M_eq (H : StrothHyp M Q Z) :
    (Nat.card M).factorization 2 = (Nat.card G).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 M) := inferInstance
  obtain ⟨T, hT⟩ := H.isSylow_of_sylow_M S
  have hcard : Nat.card (T : Subgroup G) = Nat.card (S : Subgroup M) := by
    rw [hT]
    exact Subgroup.card_map_of_injective M.subtype_injective
  have hS := Sylow.card_eq_multiplicity S
  have hT' := Sylow.card_eq_multiplicity T
  have : 2 ^ (Nat.card M).factorization 2 = 2 ^ (Nat.card G).factorization 2 := by
    rw [← hS, ← hT']
    exact hcard.symm
  exact Nat.pow_right_injective (le_refl 2) this

theorem factorization_card_le (H : StrothHyp M Q Z) {n : ℕ} (hn : 1 ≤ n) (hw : Width Q Z n) :
    (Nat.card G).factorization 2 ≤ (2 * n + 1) * (Nat.card Z).factorization 2 +
      n * (2 * n - 1) * (Nat.card Z).factorization 2 +
      ((Nat.card Z).factorization 2).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, γ, M₀, h⟩ := stroth_globalModelData H
  obtain ⟨φ, -, hφker, hφadd, hφσ⟩ := exists_actionHom_M H h
  obtain ⟨f, k₀, hf, -⟩ := H.cp
  have hfac : (Nat.card Z).factorization 2 = f := by
    rw [hf, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  rw [hfac]
  have hf0 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h1
    · have := H.q4
      rw [hf] at this
      simp at this
    · exact h1
  have hKf : Nat.card K = 2 ^ f := h.card.trans hf
  have hK1 : 1 < Nat.card K := by
    rw [hKf]
    exact Nat.one_lt_two_pow (by omega)
  have hdim : Module.finrank K M₀.E = 2 * n := h.finrank_E hw hK1
  haveI : Nontrivial M₀.E := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let ρ : ↥M →* semilinearPerm K M₀.E := φ.codRestrict _ (fun m => ⟨hφadd m, hφσ m⟩)
  have hker : ρ.ker = Q.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hφker]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  have hQM : Q ≤ M := H.Q_normal.1
  have hQcard : Nat.card (ρ.ker) = 2 ^ (f * (2 * n + 1)) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv]
    have : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hw
    rw [this, hf, ← pow_mul]
  have hmul := Subgroup.card_ker_mul_card_range ρ
  have hMne : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hrne : Nat.card ρ.range ≠ 0 := fun h0 => hMne (by rw [← hmul, h0, mul_zero])
  have hv : (Nat.card M).factorization 2 =
      f * (2 * n + 1) + (Nat.card ρ.range).factorization 2 := by
    rw [← hmul, Nat.factorization_mul (by rw [hQcard]; positivity) hrne, Finsupp.add_apply,
      hQcard, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have hRdvd : Nat.card ρ.range ∣ Nat.card (semilinearPerm K M₀.E) :=
    Subgroup.card_subgroup_dvd_card ρ.range
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hRne : Nat.card (semilinearPerm K M₀.E) ≠ 0 := Nat.card_pos.ne'
  have hle := (Nat.factorization_le_iff_dvd hrne hRne).mpr hRdvd 2
  have hbound := factorization_card_semilinearPerm_le (K := K) (E := M₀.E) hf0 hKf hdim
  rw [factorization_card_M_eq H] at hv
  have hm : 2 * n * (2 * n - 1) / 2 = n * (2 * n - 1) := by
    rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [hm] at hbound
  have e1 : f * (2 * n + 1) = (2 * n + 1) * f := Nat.mul_comm _ _
  have e2 : f * (n * (2 * n - 1)) = n * (2 * n - 1) * f := Nat.mul_comm _ _
  omega

end Bound

end CFSG.RankThree.GF2n.Smith81
