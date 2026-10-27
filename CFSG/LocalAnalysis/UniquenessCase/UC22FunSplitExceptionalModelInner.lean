module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitExceptionalTraceInner
public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.Models.Transfer.Basic
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.RankThree.PartOne.S15K.CentralCover
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Pair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Pair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Pair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Rational
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Rational
public import CFSG.ClassicalInvolution.Models.SymplecticPairs

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts
open CFSG.RankThree.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.ClassicalInvolution.Models.Transfer
open scoped MatrixGroups


theorem excresTheta_top_apply {τ : Tag} {K : Type} [Field K]
    (γ : Fin τ.rank → ℤ) (A : SL2 ↥(⊤ : Subfield K)) :
    CFSG.HardMathSupport.Dickson.Sec6.I1431.excresTheta τ (⊤ : Subfield K) γ 1 A =
      rootSL2 τ K γ
        (Matrix.SpecialLinearGroup.map
          (Subfield.topEquiv : ↥(⊤ : Subfield K) ≃+* K).toRingHom A) := by
  change (1 : ModGL τ K) *
      baseChangeGL (⊤ : Subfield K).subtype (rootSL2 τ ↥(⊤ : Subfield K) γ A) *
      (1 : ModGL τ K)⁻¹ = _
  rw [one_mul, inv_one, mul_one]
  rw [baseChangeGL_rootSL2_of_field]
  congr 1

theorem excresTheta_top_conj_apply {τ : Tag} {K : Type} [Field K]
    (γ : Fin τ.rank → ℤ) (c : ModGL τ K) (A : SL2 ↥(⊤ : Subfield K)) :
    CFSG.HardMathSupport.Dickson.Sec6.I1431.excresTheta τ (⊤ : Subfield K) γ c A =
      c * rootSL2 τ K γ
        (Matrix.SpecialLinearGroup.map
          (Subfield.topEquiv : ↥(⊤ : Subfield K) ≃+* K).toRingHom A) * c⁻¹ := by
  rw [CFSG.HardMathSupport.Dickson.Sec6.I1431.excresTheta_apply]
  exact congrArg (fun x => c * x * c⁻¹) (excresTheta_top_apply γ A)

theorem adjoint_conj_stdRankOne_inner
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K]
    (γ : Fin τ.rank → ℤ) (J0 : Subgroup (adjointGroup τ K)) (c : adjointGroup τ K)
    (hstd_mem : ∀ r : adjointGroup τ K,
      r ∈ J0 ↔ ∃ A : SL2 K, (r : ModGL τ K) = rootSL2 τ K γ A)
    {g : adjointGroup τ K}
    (hg : g ∈ Subgroup.normalizer (conjSub c J0 : Set (adjointGroup τ K)))
    (hgo : Odd (orderOf g)) :
    ∃ w ∈ conjSub c J0, ∀ x ∈ conjSub c J0, g * x * g⁻¹ = w * x * w⁻¹ := by
  let J : Subgroup (adjointGroup τ K) := conjSub c J0
  let θ : SL2 ↥(⊤ : Subfield K) →* ModGL τ K :=
    CFSG.HardMathSupport.Dickson.Sec6.I1431.excresTheta τ (⊤ : Subfield K) γ c
  have hθ_apply : ∀ A, θ A = c * rootSL2 τ K γ
      (Matrix.SpecialLinearGroup.map
        (Subfield.topEquiv : ↥(⊤ : Subfield K) ≃+* K).toRingHom A) * c⁻¹ :=
    fun A => excresTheta_top_conj_apply γ c A
  have hθ_adj : ∀ A, θ A ∈ (Subgroup.subtype (adjointGroup τ K)).range := by
    intro A
    refine ⟨⟨θ A, ?_⟩, rfl⟩
    rw [hθ_apply A]
    exact mul_mem (mul_mem c.2
      ((exceptional_Lang_root_rank_one_data τ K γ).2.2.2.2.1 _)) (inv_mem c.2)
  have hJ : ∀ p : adjointGroup τ K, p ∈ J ↔ (p : ModGL τ K) ∈ θ.range := by
    intro p
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨A, hA⟩ := (hstd_mem r).1 hr
      refine ⟨Matrix.SpecialLinearGroup.map
        ((Subfield.topEquiv.symm : K ≃+* ↥(⊤ : Subfield K)) : K →+* ↥(⊤ : Subfield K)) A, ?_⟩
      rw [hθ_apply]
      change c * rootSL2 τ K γ
          (Matrix.SpecialLinearGroup.map
            (Subfield.topEquiv : ↥(⊤ : Subfield K) ≃+* K).toRingHom
              (Matrix.SpecialLinearGroup.map
                ((Subfield.topEquiv.symm : K ≃+* ↥(⊤ : Subfield K)) :
                  K →+* ↥(⊤ : Subfield K)) A)) * c⁻¹ =
        c * (r : ModGL τ K) * c⁻¹
      rw [hA]
      congr 1
    · rintro ⟨A, hA⟩
      let B : SL2 K := Matrix.SpecialLinearGroup.map
        (Subfield.topEquiv : ↥(⊤ : Subfield K) ≃+* K).toRingHom A
      let r : adjointGroup τ K := ⟨rootSL2 τ K γ B,
        (exceptional_Lang_root_rank_one_data τ K γ).2.2.2.2.1 _⟩
      refine ⟨r, (hstd_mem r).2 ⟨B, rfl⟩, ?_⟩
      apply Subtype.ext
      change c * (r : ModGL τ K) * c⁻¹ = (p : ModGL τ K)
      rw [show (p : ModGL τ K) = θ A from hA.symm, hθ_apply A]
  have hstab : ∀ p : adjointGroup τ K, g * p * g⁻¹ ∈ J ↔ p ∈ J := by
    intro p
    rw [Subgroup.mem_normalizer_iff] at hg
    exact (hg p).symm
  have hinner := CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_inner_on_rankOne_of_odd
    (τ := τ) hτ (K' := (⊤ : Subfield K)) (β := γ) (z := c)
    (P := adjointGroup τ K) (ι := Subgroup.subtype (adjointGroup τ K))
    Subtype.val_injective hθ_adj (J := J) hJ (y := g) hgo hstab
  simpa [J] using hinner

theorem central_lift_inner_of_perfect
    {H C : Type*} [Group H] [Group C]
    (φ : H →* C) (hker : φ.ker ≤ Subgroup.center H)
    {Q : Subgroup H} (hQ : ⁅Q, Q⁆ = Q)
    {F : Subgroup C} (hQF : Q.map φ = F)
    {g : H} {x : C} (hx : x ∈ F)
    (h : ∀ y ∈ Q, φ (g * y * g⁻¹) = x * φ y * x⁻¹) :
    ∃ x' ∈ Q, ∀ y ∈ Q, g * y * g⁻¹ = x' * y * x'⁻¹ := by
  have h' := CFSG.RankThree.PartOne.S15K.exists_inner_of_map_eq_conj
    (Φ := φ) hker hQ hQF ((MulAut.conj g).toMonoidHom) hx h
  simpa [MulAut.conj_apply] using h'

theorem E6_universal_fundamental_inner
    {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {R : Subgroup ↥(e6Data_valid.minGroup K)}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E6 (e6Datum K))
    (hRperf : Group.IsPerfect R)
    {g : ↥(e6Data_valid.minGroup K)}
    (hg : g ∈ Subgroup.normalizer (R : Set ↥(e6Data_valid.minGroup K)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  rcases hR with ⟨c, γ, hγ, rfl⟩
  rcases hγ with hγ | ⟨hG2, _⟩ | ⟨hD4, _⟩
  · have hγroot : IsRoot .E6 γ :=
      (e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 K).1 hγ.1
    let φ : ↥(e6Data_valid.minGroup K) →* ↥(adjointGroup .E6 K) := e6Isogeny K
    have hmap_std : (stdRankOne (e6Datum K) γ).map φ = stdRankOne (e6AdjDatum K) γ := by
      change (((e6Datum K).rootGroup γ ⊔ (e6Datum K).rootGroup (-γ)).map φ =
        (e6AdjDatum K).rootGroup γ ⊔ (e6AdjDatum K).rootGroup (-γ))
      rw [Subgroup.map_sup]
      exact congrArg₂ (· ⊔ ·) (map_e6Isogeny_rootGroup _ hγroot)
        (map_e6Isogeny_rootGroup _ (IsRoot.neg hγroot))
    have hF : (conjSub c (stdRankOne (e6Datum K) γ)).map φ =
        conjSub (φ c) (stdRankOne (e6AdjDatum K) γ) := by
      rw [← conjSub_map φ c (stdRankOne (e6Datum K) γ), hmap_std]
    have hgF : φ g ∈ Subgroup.normalizer
        ((conjSub (φ c) (stdRankOne (e6AdjDatum K) γ)) : Set ↥(adjointGroup .E6 K)) := by
      have h := map_mem_normalizer (θ := φ) (J := conjSub c (stdRankOne (e6Datum K) γ)) hg
      rwa [hF] at h
    have hgoF : Odd (orderOf (φ g)) := by
      have hdvd : orderOf (φ g) ∣ orderOf g := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      exact hgo.of_dvd_nat hdvd
    have hres := adjoint_conj_stdRankOne_inner (Or.inl rfl) γ
      (stdRankOne (e6AdjDatum K) γ) (φ c) (Levi.mem_stdRankOne_e6_iff' hγroot) hgF hgoF
    have hres' : ∃ w ∈ (conjSub c (stdRankOne (e6Datum K) γ)).map φ,
        ∀ x ∈ (conjSub c (stdRankOne (e6Datum K) γ)).map φ,
          φ g * x * φ g⁻¹ = w * x * w⁻¹ := by
      simpa [hF] using hres
    obtain ⟨w, hw, hwj⟩ := hres'
    have hker : φ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup K) := by
      simpa [φ] using
        (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (F := K))
    have hQ : ⁅conjSub c (stdRankOne (e6Datum K) γ),
        conjSub c (stdRankOne (e6Datum K) γ)⁆ =
        conjSub c (stdRankOne (e6Datum K) γ) :=
      Subgroup.isPerfect_iff.mp hRperf
    exact central_lift_inner_of_perfect (φ := φ) hker hQ (F :=
      (conjSub c (stdRankOne (e6Datum K) γ)).map φ) rfl hw
      (fun y hy => by
        simpa [map_mul, map_inv] using hwj (φ y) (Subgroup.mem_map_of_mem φ hy))
  · cases hG2
  · cases hD4

theorem E7_universal_fundamental_inner
    {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {R : Subgroup ↥(e7Data_valid.minGroup K)}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E7 (e7Datum K))
    (hRperf : Group.IsPerfect R)
    {g : ↥(e7Data_valid.minGroup K)}
    (hg : g ∈ Subgroup.normalizer (R : Set ↥(e7Data_valid.minGroup K)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  rcases hR with ⟨c, γ, hγ, rfl⟩
  rcases hγ with hγ | ⟨hG2, _⟩ | ⟨hD4, _⟩
  · have hγroot : IsRoot .E7 γ :=
      (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1 hγ.1
    let φ : ↥(e7Data_valid.minGroup K) →* ↥(adjointGroup .E7 K) := e7Isogeny K
    have hmap_std : (stdRankOne (e7Datum K) γ).map φ = stdRankOne (e7AdjDatum K) γ := by
      change (((e7Datum K).rootGroup γ ⊔ (e7Datum K).rootGroup (-γ)).map φ =
        (e7AdjDatum K).rootGroup γ ⊔ (e7AdjDatum K).rootGroup (-γ))
      rw [Subgroup.map_sup]
      exact congrArg₂ (· ⊔ ·) (map_e7Isogeny_rootGroup _ hγroot)
        (map_e7Isogeny_rootGroup _ (IsRoot.neg hγroot))
    have hF : (conjSub c (stdRankOne (e7Datum K) γ)).map φ =
        conjSub (φ c) (stdRankOne (e7AdjDatum K) γ) := by
      rw [← conjSub_map φ c (stdRankOne (e7Datum K) γ), hmap_std]
    have hgF : φ g ∈ Subgroup.normalizer
        ((conjSub (φ c) (stdRankOne (e7AdjDatum K) γ)) : Set ↥(adjointGroup .E7 K)) := by
      have h := map_mem_normalizer (θ := φ) (J := conjSub c (stdRankOne (e7Datum K) γ)) hg
      rwa [hF] at h
    have hgoF : Odd (orderOf (φ g)) := by
      have hdvd : orderOf (φ g) ∣ orderOf g := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      exact hgo.of_dvd_nat hdvd
    have hres := adjoint_conj_stdRankOne_inner (Or.inr (Or.inl rfl)) γ
      (stdRankOne (e7AdjDatum K) γ) (φ c) (Levi.mem_stdRankOne_e7_iff' hγroot) hgF hgoF
    have hres' : ∃ w ∈ (conjSub c (stdRankOne (e7Datum K) γ)).map φ,
        ∀ x ∈ (conjSub c (stdRankOne (e7Datum K) γ)).map φ,
          φ g * x * φ g⁻¹ = w * x * w⁻¹ := by
      simpa [hF] using hres
    obtain ⟨w, hw, hwj⟩ := hres'
    have hker : φ.ker ≤ Subgroup.center ↥(e7Data_valid.minGroup K) := by
      simpa [φ] using
        (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e7Isogeny_ker_le_center (F := K))
    have hQ : ⁅conjSub c (stdRankOne (e7Datum K) γ),
        conjSub c (stdRankOne (e7Datum K) γ)⁆ =
        conjSub c (stdRankOne (e7Datum K) γ) :=
      Subgroup.isPerfect_iff.mp hRperf
    exact central_lift_inner_of_perfect (φ := φ) hker hQ (F :=
      (conjSub c (stdRankOne (e7Datum K) γ)).map φ) rfl hw
      (fun y hy => by
        simpa [map_mul, map_inv] using hwj (φ y) (Subgroup.mem_map_of_mem φ hy))
  · cases hG2
  · cases hD4

theorem E6_model_fundamental_inner
    {p : ℕ} [hp : Fact p.Prime] (_hp2 : p ≠ 2) (n e : ℕ)
    (_hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .E6 n p e)
    {R : Subgroup (CFSG.ClassicalInvolution.Generic.modelUniv .E6 n p e hp.out).K}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E6
      (CFSG.ClassicalInvolution.Generic.modelUniv .E6 n p e hp.out).D)
    (hRperf : Group.IsPerfect R)
    {g : (CFSG.ClassicalInvolution.Generic.modelUniv .E6 n p e hp.out).K}
    (hg : g ∈ Subgroup.normalizer
      (R : Set (CFSG.ClassicalInvolution.Generic.modelUniv .E6 n p e hp.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  let K := GaloisField p e
  let R' : Subgroup ↥(e6Data_valid.minGroup K) := R
  let g' : ↥(e6Data_valid.minGroup K) := g
  have hR' : R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E6 (e6Datum K) := hR
  have hperf' : Group.IsPerfect R' := hRperf
  have hg' : g' ∈ Subgroup.normalizer (R' : Set ↥(e6Data_valid.minGroup K)) := hg
  have hgo' : Odd (orderOf g') := hgo
  exact E6_universal_fundamental_inner (K := K) (R := R') hR' hperf' (g := g') hg' hgo'

theorem E7_model_fundamental_inner
    {p : ℕ} [hp : Fact p.Prime] (_hp2 : p ≠ 2) (n e : ℕ)
    (_hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .E7 n p e)
    {R : Subgroup (CFSG.ClassicalInvolution.Generic.modelUniv .E7 n p e hp.out).K}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E7
      (CFSG.ClassicalInvolution.Generic.modelUniv .E7 n p e hp.out).D)
    (hRperf : Group.IsPerfect R)
    {g : (CFSG.ClassicalInvolution.Generic.modelUniv .E7 n p e hp.out).K}
    (hg : g ∈ Subgroup.normalizer
      (R : Set (CFSG.ClassicalInvolution.Generic.modelUniv .E7 n p e hp.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  let K := GaloisField p e
  let R' : Subgroup ↥(e7Data_valid.minGroup K) := R
  let g' : ↥(e7Data_valid.minGroup K) := g
  have hR' : R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E7 (e7Datum K) := hR
  have hperf' : Group.IsPerfect R' := hRperf
  have hg' : g' ∈ Subgroup.normalizer (R' : Set ↥(e7Data_valid.minGroup K)) := hg
  have hgo' : Odd (orderOf g') := hgo
  exact E7_universal_fundamental_inner (K := K) (R := R') hR' hperf' (g := g') hg' hgo'

theorem E8_adjoint_fundamental_inner
    {K : Type} [Field K] [Finite K]
    {R : Subgroup (adjointGroup .E8 K)}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E8 (e8Datum K))
    {g : adjointGroup .E8 K}
    (hg : g ∈ Subgroup.normalizer (R : Set (adjointGroup .E8 K)))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  rcases hR with ⟨c, γ, hγ, rfl⟩
  rcases hγ with hγ | ⟨hG2, _⟩ | ⟨hD4, _⟩
  · have hγroot : IsRoot .E8 γ := mem_adjDatum_roots.mp hγ.1
    exact adjoint_conj_stdRankOne_inner (Or.inr (Or.inr rfl)) γ
      (stdRankOne (e8Datum K) γ) c (Levi.mem_stdRankOne_e8_iff' hγroot) hg hgo
  · cases hG2
  · cases hD4

theorem E8_model_fundamental_inner
    {p : ℕ} [hp : Fact p.Prime] (_hp2 : p ≠ 2) (n e : ℕ)
    (_hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .E8 n p e)
    {R : Subgroup (CFSG.ClassicalInvolution.Generic.modelUniv .E8 n p e hp.out).K}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E8 (CFSG.ClassicalInvolution.Generic.modelUniv .E8 n p e hp.out).D)
    {g : (CFSG.ClassicalInvolution.Generic.modelUniv .E8 n p e hp.out).K}
    (hg : g ∈ Subgroup.normalizer (R : Set (CFSG.ClassicalInvolution.Generic.modelUniv .E8 n p e hp.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  let K := GaloisField p e
  let R' : Subgroup (adjointGroup .E8 K) := R
  let g' : adjointGroup .E8 K := g
  have hR' : R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups .E8 (e8Datum K) := hR
  have hg' : g' ∈ Subgroup.normalizer (R' : Set (adjointGroup .E8 K)) := hg
  have hgo' : Odd (orderOf g') := hgo
  have hres := E8_adjoint_fundamental_inner (K := K) (R := R') hR' (g := g') hg' hgo'
  exact hres

theorem odd_normalizer_inner_fundamental_exceptional_model
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8)
    {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (n e : ℕ)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e)
    {R : Subgroup (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp.out).K}
    (hR : R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
      (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp.out).D)
    (hRperf : Group.IsPerfect R)
    {g : (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp.out).K}
    (hg : g ∈ Subgroup.normalizer
      (R : Set (CFSG.ClassicalInvolution.Generic.modelUniv t n p e hp.out).K))
    (hgo : Odd (orderOf g)) :
    ∃ r ∈ R, ∀ x ∈ R, g * x * g⁻¹ = r * x * r⁻¹ := by
  rcases ht with rfl | rfl | rfl
  · exact E6_model_fundamental_inner hp2 n e hadm hR hRperf hg hgo
  · exact E7_model_fundamental_inner hp2 n e hadm hR hRperf hg hgo
  · exact E8_model_fundamental_inner hp2 n e hadm hR hg hgo

end CFSG.LocalAnalysis.UniquenessCase.UC22
