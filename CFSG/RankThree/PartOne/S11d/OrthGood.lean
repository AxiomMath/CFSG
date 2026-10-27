module

public import CFSG.RankThree.PartOne.S11d.OrthCaseS
public import CFSG.RankThree.PartOne.S11d.OrthDescent

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.PartOne.KCOrthComm
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)

section Acts

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
  (hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v))

theorem actsBySemilinear_fieldAut :
    ActsBySemilinear Q (coordinateFieldMap d σ)
      (MulAut.congr (matrixProjEquiv Q) (fieldAutT Q σ hQσ)) := by
  intro ω
  obtain ⟨A, rfl⟩ := (matrixDerivedEquiv Q).surjective ω
  refine ⟨matrixDerivedEquiv Q (matrixDerivedConjugation Q (fieldPair Q σ hQσ) A), fun v => ?_, ?_⟩
  · rw [coe_matrixDerivedEquiv, coe_matrixDerivedEquiv, matrixDerivedConjugation_fieldPair_val]
    have := coordinateFieldMap_matrix σ A.1 ((coordinateFieldMap d σ).symm v)
    rw [AddEquiv.apply_symm_apply] at this
    rw [← this]
  · change matrixProjEquiv Q (fieldAutT Q σ hQσ ((matrixProjEquiv Q).symm
      (piOrth Q (matrixDerivedEquiv Q A)))) = _
    have h : (matrixProjEquiv Q).symm (piOrth Q (matrixDerivedEquiv Q A)) =
        QuotientGroup.mk A := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [h]
    change matrixProjEquiv Q (fieldAutT Q σ hQσ (matrixProjectiveProjection Q A)) = _
    rw [fieldAutT_mk]
    rfl

end Acts

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K} {σ : K ≃+* K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {p : ℕ}

theorem orth_good_all (S : SubfieldSetup k Q₀ Q σ p) (hK : 4 ≤ Nat.card K) {f₀ : ℕ}
    (hf₀ : 1 ≤ f₀) (hcard : Nat.card K = 2 ^ (p * f₀))
    (hrank : CFSG.pRank p (ProjOrthDerived Q) ≤ 1) {xT yT : ProjOrthDerived Q}
    (hxp : xT ^ p = 1) (hx1 : xT ≠ 1)
    (hαx : MulAut.congr (matrixProjEquiv Q) (fieldAutT Q σ S.hQσ) xT = xT)
    (hy2 : yT ^ 2 = 1) (hy1 : yT ≠ 1) (hxy : xT * yT = yT * xT) :
    GoodConclusion p (ProjOrthDerived Q)
      (MulAut.congr (matrixProjEquiv Q) (fieldAutT Q σ S.hQσ)) xT := by
  have hp := S.hp
  have hp2 := S.hp2
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpl : p ≠ ringChar K := by rw [ringChar.eq K 2]; exact hp2
  have hQ := S.hnd
  have hT := S.hT
  have : Nontrivial (Fin d → K) := nontrivial_of_threeSingular hT
  have hα := actsBySemilinear_fieldAut Q σ S.hQσ
  have hσ : ∃ c, σ c ≠ c := by
    by_contra h
    push Not at h
    have h1 : σ = 1 := RingEquiv.ext h
    have := S.hσ
    rw [h1, orderOf_one] at this
    exact hp.one_lt.ne this
  obtain ⟨ωx, rfl⟩ := piOrth_surjective xT
  obtain ⟨ωy, rfl⟩ := piOrth_surjective yT
  have : Fact p.Prime := ⟨hp⟩
  have hxp' : ωx ^ p = 1 := piOrth_injective hQ (by rw [map_pow, map_one]; exact hxp)
  have hx1' : ωx ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hord : orderOf ωx = p := orderOf_eq_prime hxp' hx1'
  have hxo : OddOrderIsometry Q p (ωx : (Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    oddOrderIsometry_of_orthDerived hp hpl hQ ωx hord
  have hSx : ∀ v, coordinateFieldMap d σ ((ωx : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) =
      (ωx : (Fin d → K) ≃ₗ[K] (Fin d → K)) (coordinateFieldMap d σ v) := by
    obtain ⟨ω', h1, h2⟩ := hα ωx
    have h3 : ωx = ω' := piOrth_injective hQ (hαx.symm.trans h2)
    intro v
    have h4 := h1 (coordinateFieldMap d σ v)
    rw [AddEquiv.symm_apply_apply, ← h3] at h4
    exact h4.symm
  have hy2' : (ωy : (Fin d → K) ≃ₗ[K] (Fin d → K)) ^ 2 = 1 := by
    have : ωy ^ 2 = 1 := piOrth_injective hQ (by rw [map_pow, map_one]; exact hy2)
    exact congrArg Subtype.val this
  have hy1' : (ωy : (Fin d → K) ≃ₗ[K] (Fin d → K)) ≠ 1 := fun h => by
    have h' : ωy = 1 := Subtype.ext h
    exact hy1 (by rw [h', map_one])
  have hyx : (ωy : (Fin d → K) ≃ₗ[K] (Fin d → K)) * ωx = ωx * ωy :=
    congrArg Subtype.val (commute_of_piOrth_commute hQ (show Commute _ _ from hxy.symm)).eq
  have hmult : ∀ h ∈ primaryFactors (ωx : (Fin d → K) ≃ₗ[K] (Fin d → K)).toLinearMap,
      h ≠ X - 1 → primaryMultiplicity (ωx : (Fin d → K) ≃ₗ[K] (Fin d → K)).toLinearMap h ≤ 1 :=
    fun h hh hne => multiplicity_le_one_of_pRank hQ hT hp hp2 hxo hrank hh hne
  have h4 := hxo.four_le_finrank_fixed hmult hQ ωy.2 hy2' hy1' hyx
  have hWnd := hxo.polarBilin_fixed_nondegenerate
  obtain ⟨m, hm⟩ := hxo.even_finrank_fixed
  have hxΩ : (ωx : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ orthDerived Q := ωx.2
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  · rcases (by omega : m = 2 ∨ m = 3) with rfl | rfl
    · by_cases hsplit : ∃ U : Submodule K (fixedSpace (ωx : (Fin d → K) ≃ₗ[K] (Fin d → K))),
          finrank K U = 2 ∧ ∀ u ∈ U,
            (Q.comp (fixedSpace (ωx : (Fin d → K) ≃ₗ[K] (Fin d → K))).subtype) u = 0
      · exact orth_good_split4 S.hσk S.hext S.hQσ hQ hK hσ hα hp hp2 hxΩ hxo hSx hmult
          (by omega) hsplit hf₀ hcard
      · refine orth_good_nonsplit S.hσk S.hext S.hQσ hQ hK hσ hα hp hp2 hxΩ hxo hSx hmult
          (Or.inl (by omega)) (fun U hU => ?_) hf₀ hcard
        by_contra hall
        push Not at hall
        exact hsplit ⟨U, by omega, hall⟩
    · by_cases hTW : ∃ U : Submodule K (fixedSpace (ωx : (Fin d → K) ≃ₗ[K] (Fin d → K))),
          finrank K U = 3 ∧ ∀ u ∈ U,
            (Q.comp (fixedSpace (ωx : (Fin d → K) ≃ₗ[K] (Fin d → K))).subtype) u = 0
      · exact orth_good_high S.hσk S.hext S.hQσ hQ hK hσ hα hp hp2 hxΩ hxo hSx hmult (by omega)
          hTW hf₀ hcard
      · refine orth_good_nonsplit S.hσk S.hext S.hQσ hQ hK hσ hα hp hp2 hxΩ hxo hSx hmult
          (Or.inr (by omega)) (fun U hU => ?_) hf₀ hcard
        by_contra hall
        push Not at hall
        exact hTW ⟨U, by omega, hall⟩
  · exact orth_good_high S.hσk S.hext S.hQσ hQ hK hσ hα hp hp2 hxΩ hxo hSx hmult (by omega)
      (exists_threeSingular_of_dim _ hWnd hm4 (by omega)) hf₀ hcard

end Main

section Tag

variable {T : Type} [Group T] [Finite T] {p f₀ : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Subfield K} {σ : K ≃+* K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)}

theorem goodConclusion_of_orth_model (hf₀ : 1 ≤ f₀) (hp5 : 5 ≤ p) (hrankT : CFSG.pRank p T = 1)
    (S : SubfieldSetup k Q₀ Q σ p) (ψ : T ≃* matrixProjectiveDerived Q)
    (hcard : Nat.card K = 2 ^ (p * f₀)) (α : MulAut T)
    (hψα : MulAut.congr ψ α = fieldAutT Q σ S.hQσ) {x : T} (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (hαx : α x = x) {y : T} (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) (hxy : x * y = y * x) :
    GoodConclusion p T α x := by
  set φ : T ≃* ProjOrthDerived Q := ψ.trans (matrixProjEquiv Q) with hφ
  have : Finite (ProjOrthDerived Q) := Finite.of_equiv T φ.toEquiv
  have hrank : CFSG.pRank p (ProjOrthDerived Q) ≤ 1 := by
    rw [← pRank_eq_of_mulEquiv_of_one_lt S.hp.one_lt φ]
    exact hrankT.le
  have hK : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hcongr : MulAut.congr φ α = MulAut.congr (matrixProjEquiv Q) (fieldAutT Q σ S.hQσ) := by
    rw [← hψα]
    ext g
    rfl
  refine GoodConclusion.of_mulEquiv φ α x ?_
  rw [hcongr]
  have hαφ : MulAut.congr (matrixProjEquiv Q) (fieldAutT Q σ S.hQσ) (φ x) = φ x := by
    rw [← hcongr]
    simp [MulAut.congr_apply, hαx]
  exact orth_good_all S hK hf₀ hcard hrank (xT := φ x) (yT := φ y)
    (by rw [← map_pow, hxp, map_one]) (fun h => hx1 (φ.injective (by rw [h, map_one]))) hαφ
    (by rw [← map_pow, hy2, map_one]) (fun h => hy1 (φ.injective (by rw [h, map_one])))
    (by rw [← map_mul, ← map_mul, hxy])

end Tag

open CFSG.RankThree.PartOne.FieldFix (exists_orth_model_plus exists_orth_model_minus)

theorem lieGoodComponentFixT_POmegaPlus : LieGoodComponentFixT .POmegaPlus := by
  intro T _ _ p hp hp5 hrank hrankT n f₀ hf₀ hM α hαp hαinn hra hX x hxp hx1 hαx y hy2 hy1 hxy
  obtain ⟨K, _, _, _, k, σ, Q₀, Q, S, ψ, hcard, hn4, hψα⟩ :=
    exists_orth_model_plus hp hp5 hM α hαp hαinn
  exact goodConclusion_of_orth_model hf₀ hp5 hrankT S ψ hcard α hψα hxp hx1 hαx hy2 hy1 hxy

theorem lieGoodComponentFixT_POmegaMinus : LieGoodComponentFixT .POmegaMinus := by
  intro T _ _ p hp hp5 hrank hrankT n f₀ hf₀ hM α hαp hαinn hra hX x hxp hx1 hαx y hy2 hy1 hxy
  obtain ⟨K, _, _, _, k, σ, Q₀, Q, S, ψ, hcard, hn4, hψα⟩ :=
    exists_orth_model_minus hp hp5 hM hf₀ α hαp hαinn
  exact goodConclusion_of_orth_model hf₀ hp5 hrankT S ψ hcard α hψα hxp hx1 hαx hy2 hy1 hxy

end CFSG.RankThree.PartOne
