module

public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient

import CFSG.LieType.SeitzGeneration.Coprime
import CFSG.LieType.SeitzGeneration.RootPairOrthModel
import CFSG.LieType.SeitzGeneration.OrthOppGen
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmega
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPOmegaOpp

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open Subgroup Matrix QuadraticMap CFSG.Open CFSG.LieType.SeitzGeneration
  CFSG.ClassicalGroups.Orthogonal CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical2 (orthDerived)

private theorem polar_similarity {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (g : similarityPairs Q) (x y : Fin d → K) :
    polar Q (coordinateSemilinearMap g.val x) (coordinateSemilinearMap g.val y) =
      (multiplier Q g : K) * g.val.right (polar Q x y) := by
  have h1 := QuadraticMap.map_add Q x y
  have h2 := QuadraticMap.map_add Q (coordinateSemilinearMap g.val x)
    (coordinateSemilinearMap g.val y)
  rw [← map_add] at h2
  rw [multiplier_spec Q g (x + y), h1, multiplier_spec Q g x, multiplier_spec Q g y] at h2
  simp only [map_add] at h2
  linear_combination -h2

private theorem matrixConjugation_vector' {K : Type} [Field K] {d : ℕ}
    (g : coordinateSemilinearGroup d K) (A : GL (Fin d) K) (v : Fin d → K) :
    matrixLinearIso (matrixConjugation g A) v =
      coordinateSemilinearMap g (matrixLinearIso A ((coordinateSemilinearMap g).symm v)) :=
  matrixConjugation_vector g A v

private theorem conj_eichler {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (g : similarityPairs Q) (u w : Fin d → K) :
    matrixLinearIso (matrixConjugation g.val (matrixLinearIso.symm (eichler Q u w))) =
      eichler Q (coordinateSemilinearMap g.val u)
        (((multiplier Q g : K))⁻¹ • coordinateSemilinearMap g.val w) := by
  have hμ0 : ((multiplier Q g : K)) ≠ 0 := (multiplier Q g).ne_zero
  refine LinearEquiv.ext fun x => ?_
  have hlin : matrixLinearIso (matrixLinearIso.symm (eichler Q u w)) = eichler Q u w :=
    MulEquiv.apply_symm_apply _ _
  rw [matrixConjugation_vector', hlin]
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · obtain ⟨hu, huw⟩ := h
    have hσu : Q (coordinateSemilinearMap g.val u) = 0 := by
      rw [multiplier_spec Q g u, hu, map_zero, mul_zero]
    have hpol : polar Q (coordinateSemilinearMap g.val u)
        (((multiplier Q g : K))⁻¹ • coordinateSemilinearMap g.val w) = 0 := by
      rw [polar_smul_right_eq, polar_similarity g u w, huw, map_zero, mul_zero, mul_zero]
    have key : ∀ y : Fin d → K,
        coordinateSemilinearMap g.val (eichler Q u w y) =
          coordinateSemilinearMap g.val y + g.val.right (polar Q y u) •
            coordinateSemilinearMap g.val w -
          (g.val.right (polar Q y w) + g.val.right (Q w) * g.val.right (polar Q y u)) •
            coordinateSemilinearMap g.val u := by
      intro y
      rw [eichler_apply hu huw, map_sub, map_add, coordinateSemilinearMap_smul,
        coordinateSemilinearMap_smul, map_add, map_mul]
    have key2 : ∀ y : Fin d → K,
        eichler Q (coordinateSemilinearMap g.val u)
            (((multiplier Q g : K))⁻¹ • coordinateSemilinearMap g.val w)
            (coordinateSemilinearMap g.val y) =
          coordinateSemilinearMap g.val y + g.val.right (polar Q y u) •
            coordinateSemilinearMap g.val w -
          (g.val.right (polar Q y w) + g.val.right (Q w) * g.val.right (polar Q y u)) •
            coordinateSemilinearMap g.val u := by
      intro y
      rw [eichler_apply hσu hpol, polar_similarity g y u, polar_smul_right_eq,
        polar_similarity g y w, QuadraticMap.map_smul, smul_eq_mul, multiplier_spec Q g w]
      rw [show ((multiplier Q g : K) * g.val.right (polar Q y u)) •
            (((multiplier Q g : K))⁻¹ • coordinateSemilinearMap g.val w) =
          g.val.right (polar Q y u) • coordinateSemilinearMap g.val w from by
        rw [smul_smul]
        congr 1
        field_simp]
      rw [show (multiplier Q g : K)⁻¹ * ((multiplier Q g : K) * g.val.right (polar Q y w)) +
            ((multiplier Q g : K)⁻¹ * (multiplier Q g : K)⁻¹ *
              ((multiplier Q g : K) * g.val.right (Q w))) *
            ((multiplier Q g : K) * g.val.right (polar Q y u)) =
          g.val.right (polar Q y w) + g.val.right (Q w) * g.val.right (polar Q y u) from by
        field_simp]
    conv_rhs => rw [← AddEquiv.apply_symm_apply (coordinateSemilinearMap g.val) x]
    rw [key ((coordinateSemilinearMap g.val).symm x),
      key2 ((coordinateSemilinearMap g.val).symm x), AddEquiv.apply_symm_apply]
  · have h' : ¬(Q (coordinateSemilinearMap g.val u) = 0 ∧
        polar Q (coordinateSemilinearMap g.val u)
          (((multiplier Q g : K))⁻¹ • coordinateSemilinearMap g.val w) = 0) := by
      rintro ⟨h1, h2⟩
      apply h
      constructor
      · rw [multiplier_spec Q g u] at h1
        exact g.val.right.map_eq_zero_iff.mp ((mul_eq_zero.mp h1).resolve_left hμ0)
      · rw [polar_smul_right_eq, polar_similarity g u w] at h2
        have h3 : g.val.right (polar Q u w) = 0 := by
          rcases mul_eq_zero.mp h2 with h4 | h4
          · exact absurd h4 (inv_ne_zero hμ0)
          · rcases mul_eq_zero.mp h4 with h5 | h5
            · exact absurd h5 hμ0
            · exact h5
        rwa [g.val.right.map_eq_zero_iff] at h3
    rw [eichler_of_not h, eichler_of_not h']
    simp

private theorem eichler_mem_eichlerRad_conj {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (g : similarityPairs Q) {X : Submodule K (Fin d → K)}
    (hX : ∀ w ∈ X, coordinateSemilinearMap g.val w ∈ X)
    (hX' : ∀ w ∈ X, (coordinateSemilinearMap g.val).symm w ∈ X)
    {A : GL (Fin d) K} (hA : matrixLinearIso A ∈ eichlerRad Q X) :
    matrixLinearIso (matrixConjugation g.val A) ∈ eichlerRad Q X := by
  let Ψ : ((Fin d → K) ≃ₗ[K] (Fin d → K)) →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    (matrixLinearIso.toMonoidHom.comp (matrixConjugation g.val).toMonoidHom).comp
      matrixLinearIso.symm.toMonoidHom
  have hclosure : eichlerRad Q X ≤ Subgroup.comap Ψ (eichlerRad Q X) := by
    rw [eichlerRad, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    change Ψ (eichler Q x w) ∈ eichlerRad Q X
    show matrixLinearIso (matrixConjugation g.val (matrixLinearIso.symm (eichler Q x w))) ∈
      eichlerRad Q X
    rw [conj_eichler]
    refine eichler_mem_eichlerRad (hX x hx) ?_
    intro y hy
    rw [polar_smul_right_eq]
    have h1 : polar Q (coordinateSemilinearMap g.val ((coordinateSemilinearMap g.val).symm y))
        (coordinateSemilinearMap g.val w) = (multiplier Q g : K) *
          g.val.right (polar Q ((coordinateSemilinearMap g.val).symm y) w) :=
      polar_similarity g _ w
    rw [AddEquiv.apply_symm_apply] at h1
    rw [h1, hw _ (hX' y hy), map_zero, mul_zero, mul_zero]
  have hfin := hclosure hA
  simpa [Ψ] using hfin

private theorem conj_eq_one_of_scalar {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : similarityPairs Q} (hright : g.val.right = 1)
    {a : Kˣ} (hleft : g.val.left = GeneralLinearGroup.scalar (Fin d) a) :
    matrixProjectiveConjugationHom Q g = 1 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q A) =
    (1 : MulAut (matrixProjectiveDerived Q)) ((matrixProjectiveProjection Q) A)
  rw [matrixProjectiveConjugation_mk, MulAut.one_apply]
  have hB : matrixDerivedConjugation Q g A = A := by
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, hright, hleft]
    rw [show CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin d) K
      (1 : K ≃+* K) = 1 from map_one _]
    rw [MulAut.one_apply]
    have hc : GeneralLinearGroup.scalar (Fin d) a ∈ Subgroup.center (GL (Fin d) K) := by
      rw [← matrixScalars_eq_center]
      exact ⟨a, rfl⟩
    rw [← Subgroup.mem_center_iff.mp hc A.val, mul_assoc, mul_inv_cancel, mul_one]
  rw [hB]

theorem planeGen_of_stable_singular {K : Type} [Field K] [Finite K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (h2 : (2 : K) ≠ 0) (hd : 6 ≤ d)
    (hnd : Q.polarBilin.Nondegenerate) (hder : elementaryGroup Q = orthDerived Q)
    (hker : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 →
      g.val.right = 1 ∧ ∃ a : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a)
    {E : Subgroup (MulAut (matrixProjectiveDerived Q))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) (hEim : E ≤ matrixProjectiveImage Q)
    {W : Submodule K (Fin d → K)} (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, Q x = 0)
    (hst : ∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g ∈ E →
      ∀ w ∈ W, coordinateSemilinearMap g.val w ∈ W) :
    PlaneGen E := by
  classical
  have hFact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFintypeK : Fintype K := Fintype.ofFinite K
  have hNonemptyFin : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  set κ := matrixProjectiveConjugationHom Q with hκ
  have hsim : ∀ a : Kˣ,
      (⟨GeneralLinearGroup.scalar (Fin d) a, (1 : K ≃+* K)⟩ : coordinateSemilinearGroup d K) ∈
        similarityPairs Q := by
    intro a
    refine ⟨a * a, fun v => ?_⟩
    rw [coordinateSemilinearMap_apply]
    have h1 : (GeneralLinearGroup.scalar (Fin d) a).val *ᵥ
        (fun i => (1 : K ≃+* K) (v i)) = (a : K) • v := by
      funext i
      simp [GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]
    rw [h1, QuadraticMap.map_smul]
    simp [Units.val_mul, smul_eq_mul]
  have hscalar_ker : ∀ a : Kˣ,
      κ ⟨(⟨GeneralLinearGroup.scalar (Fin d) a, (1 : K ≃+* K)⟩ :
        coordinateSemilinearGroup d K), hsim a⟩ = 1 := by
    intro a
    exact conj_eq_one_of_scalar (Q := Q) rfl rfl
  have hker_iff : ∀ g : similarityPairs Q, κ g = 1 ↔
      g.val.right = 1 ∧ ∃ a : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a := by
    intro g
    refine ⟨hker g, ?_⟩
    rintro ⟨h1, a, h2⟩
    exact conj_eq_one_of_scalar (Q := Q) h1 h2
  have hcardker : Nat.card κ.ker = Nat.card Kˣ := by
    have hφ : Function.Bijective (fun a : Kˣ =>
        (⟨⟨(⟨GeneralLinearGroup.scalar (Fin d) a, (1 : K ≃+* K)⟩ :
            coordinateSemilinearGroup d K), hsim a⟩, hscalar_ker a⟩ : κ.ker)) := by
      constructor
      · intro a b hab
        have h1 : (⟨(⟨GeneralLinearGroup.scalar (Fin d) a, (1 : K ≃+* K)⟩ :
              coordinateSemilinearGroup d K), hsim a⟩ : similarityPairs Q) =
            ⟨(⟨GeneralLinearGroup.scalar (Fin d) b, (1 : K ≃+* K)⟩ :
              coordinateSemilinearGroup d K), hsim b⟩ := congrArg Subtype.val hab
        have h2 : GeneralLinearGroup.scalar (Fin d) a = GeneralLinearGroup.scalar (Fin d) b := by
          simpa using congrArg (fun x : similarityPairs Q => x.val.left) h1
        have h3 : (Matrix.scalar (Fin d) (a : K)) = Matrix.scalar (Fin d) (b : K) := by
          simpa [GeneralLinearGroup.coe_scalar] using
            congrArg (fun x : GL (Fin d) K => (x : Matrix (Fin d) (Fin d) K)) h2
        exact Units.ext (Matrix.scalar_inj.mp h3)
      · intro x
        obtain ⟨h1, a, h2⟩ := hker x.1 x.2
        refine ⟨a, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact SemidirectProduct.ext (by simpa using h2.symm) (by simpa using h1.symm)
    exact Nat.card_congr (Equiv.ofBijective _ hφ).symm
  set S : Subgroup (similarityPairs Q) := E.comap κ with hS
  have hcardS : Nat.card S = Nat.card E * Nat.card κ.ker := by
    have h1 : Nat.card S = Nat.card (S ⧸ (κ.comp S.subtype).ker) *
        Nat.card (κ.comp S.subtype).ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hrange : (κ.comp S.subtype).range = E := by
      ext e
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro he
        obtain ⟨g, hg⟩ := hEim he
        exact ⟨⟨g, by rw [hS, Subgroup.mem_comap]; exact hg ▸ he⟩, hg⟩
    have hkercard : Nat.card (κ.comp S.subtype).ker = Nat.card κ.ker := by
      have hbij : Nat.card (κ.comp S.subtype).ker = Nat.card κ.ker := by
        apply Nat.card_congr
        refine
          { toFun := fun x => (⟨x.1.1, x.2⟩ : κ.ker)
            invFun := fun y => (⟨⟨y.1, ?_⟩, y.2⟩ : (κ.comp S.subtype).ker)
            left_inv := fun x => by
              apply Subtype.ext
              apply Subtype.ext
              rfl
            right_inv := fun y => by
              apply Subtype.ext
              rfl }
        rw [hS, Subgroup.mem_comap]
        exact MonoidHom.mem_ker.mp y.2 ▸ E.one_mem
      exact hbij
    rw [h1, Nat.card_congr (QuotientGroup.quotientKerEquivRange (κ.comp S.subtype)).toEquiv,
      hrange, hkercard]
  set G : Subgroup (coordinateSemilinearGroup d K) := S.map (similarityPairs Q).subtype with hG
  have hGQ : G ≤ similarityPairs Q := by
    rintro g ⟨x, -, rfl⟩
    exact x.2
  have hGstab : ∀ g ∈ G, ∀ w ∈ W, coordinateSemilinearMap g w ∈ W := by
    rintro g ⟨x, hx, rfl⟩ w hw
    exact hst x (by simpa [hS] using (Subgroup.mem_comap.mp hx)) w hw
  have hcardG : Nat.card G = Nat.card S :=
    Subgroup.card_map_of_injective (f := (similarityPairs Q).subtype) (fun x y h => Subtype.ext h)
  have hcardGK : Nat.card G = 4 * (Nat.card K - 1) := by
    rw [hcardG, hcardS, hcardker, h4, Nat.card_units]
  have hq : (Nat.card K : K) = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero K
  have hunit : ((Nat.card K - 1 : ℕ) : K) = -1 := by
    have h1 : Nat.card K = Nat.card Kˣ + 1 := by
      rw [Nat.card_units]
      have hpos : 0 < Nat.card K := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_pos_iff.mpr inferInstance
      omega
    have h2 : ((Nat.card K : ℕ) : K) = ((Nat.card Kˣ : ℕ) : K) + 1 := by
      rw [h1]
      push_cast
      ring
    rw [hq] at h2
    have h3 : ((Nat.card Kˣ : ℕ) : K) = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      exact h2.symm
    rwa [Nat.card_units] at h3
  have hG0 : (Nat.card G : K) ≠ 0 := by
    rw [hcardGK, Nat.cast_mul, hunit]
    have h4K : ((4 : ℕ) : K) = 2 * 2 := by norm_num
    rw [h4K]
    intro hcontra
    have hneg : (2 : K) * 2 * (-1) = -((2 : K) * 2) := by ring
    rw [hneg] at hcontra
    exact (neg_ne_zero.mpr (mul_ne_zero h2 h2)) hcontra
  obtain ⟨Y, hYsing, hYcompl, hYst⟩ :=
    exists_stable_opposite h2 hnd G hGQ hG0 hW hGstab
  let linH : matrixDerived Q →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    matrixLinearIso.toMonoidHom.comp (matrixDerived Q).subtype
  let R : Submodule K (Fin d → K) → Subgroup (matrixProjectiveDerived Q) := fun X =>
    ((eichlerRad Q X).comap linH).map (matrixProjectiveProjection Q)
  have hYS : ∀ g : similarityPairs Q, κ g ∈ E → (g : coordinateSemilinearGroup d K) ∈ G := by
    intro g hg
    exact Subgroup.mem_map.mpr ⟨g, by rw [hS, Subgroup.mem_comap]; exact hg, rfl⟩
  have hinv : ∀ (X : Submodule K (Fin d → K))
      (hX : ∀ g : similarityPairs Q, κ g ∈ E → ∀ x ∈ X, coordinateSemilinearMap g.val x ∈ X),
      (∀ g : similarityPairs Q, κ g ∈ E → ∀ x ∈ X,
        (coordinateSemilinearMap g.val).symm x ∈ X) →
      ∀ e ∈ E, (R X).map e.toMonoidHom = R X := by
    intro X hX hX' e he
    obtain ⟨g, hg⟩ := hEim he
    have hgκ : κ g = (e : MulAut (matrixProjectiveDerived Q)) := hg
    have hle : ∀ (e' : E) (g' : similarityPairs Q),
        κ g' = (e' : MulAut (matrixProjectiveDerived Q)) →
        (R X).map (e' : MulAut (matrixProjectiveDerived Q)).toMonoidHom ≤ R X := by
      intro e' g' hg'
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨A, hA, hAx⟩ := Subgroup.mem_map.mp hx
      have hA' : matrixLinearIso (A : GL (Fin d) K) ∈ eichlerRad Q X :=
        Subgroup.mem_comap.mp hA
      have hg'E : κ g' ∈ E := by rw [hg']; exact e'.2
      refine Subgroup.mem_map.mpr ⟨matrixDerivedConjugation Q g' A, ?_, ?_⟩
      · exact Subgroup.mem_comap.mpr
          (eichler_mem_eichlerRad_conj g' (hX g' hg'E) (hX' g' hg'E) hA')
      · rw [← hAx, ← hg']
        exact (matrixProjectiveConjugation_mk Q g' A).symm
    refine le_antisymm (hle ⟨e, he⟩ g hgκ) ?_
    have hcomp : e.toMonoidHom.comp ((⟨e, he⟩⁻¹ : E) : MulAut
        (matrixProjectiveDerived Q)).toMonoidHom = MonoidHom.id (matrixProjectiveDerived Q) := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
      rw [show ((⟨e, he⟩⁻¹ : E) : MulAut (matrixProjectiveDerived Q)) =
        (e : MulAut (matrixProjectiveDerived Q))⁻¹ from rfl, ← MulAut.mul_apply,
        mul_inv_cancel, MulAut.one_apply]
    have h4 : ((R X).map ((⟨e, he⟩⁻¹ : E) : MulAut
        (matrixProjectiveDerived Q)).toMonoidHom).map e.toMonoidHom = R X := by
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    have h2 := hle (⟨e, he⟩⁻¹) (g⁻¹) (by rw [map_inv, hgκ]; rfl)
    calc R X = ((R X).map ((⟨e, he⟩⁻¹ : E) : MulAut
          (matrixProjectiveDerived Q)).toMonoidHom).map e.toMonoidHom := h4.symm
      _ ≤ (R X).map e.toMonoidHom := Subgroup.map_mono h2
  have hinvW : ∀ g : similarityPairs Q, κ g ∈ E → ∀ w ∈ W,
      (coordinateSemilinearMap g.val).symm w ∈ W := by
    intro g hg w hw
    have hg' : κ g⁻¹ ∈ E := by rw [map_inv]; exact E.inv_mem hg
    have h := hst g⁻¹ hg' w hw
    simpa [coordinateSemilinearMap_inv] using h
  have hinvY : ∀ g : similarityPairs Q, κ g ∈ E → ∀ y ∈ Y,
      (coordinateSemilinearMap g.val).symm y ∈ Y := by
    intro g hg y hy
    have hg' : κ g⁻¹ ∈ E := by rw [map_inv]; exact E.inv_mem hg
    have h := hYst g⁻¹ (hYS g⁻¹ hg') y hy
    simpa [coordinateSemilinearMap_inv] using h
  have hYstab : ∀ g : similarityPairs Q, κ g ∈ E → ∀ y ∈ Y,
      coordinateSemilinearMap g.val y ∈ Y := fun g hg => hYst g (hYS g hg)
  have hRW : ∀ e ∈ E, (R W).map e.toMonoidHom = R W := hinv W hst hinvW
  have hRY : ∀ e ∈ E, (R Y).map e.toMonoidHom = R Y := hinv Y hYstab hinvY
  have hRodd : ∀ (X : Submodule K (Fin d → K)), X ≠ ⊥ → (∀ x ∈ X, Q x = 0) →
      ¬ 2 ∣ Nat.card (R X) := by
    intro X hX0 hXsing hdvd
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    obtain ⟨A, hA, hAt⟩ := Subgroup.mem_map.mp t.2
    have hA' : matrixLinearIso (A : GL (Fin d) K) ∈ eichlerRad Q X := Subgroup.mem_comap.mp hA
    have ht2 : ((t : R X) : matrixProjectiveDerived Q) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one t
      rw [ht] at h
      simpa using congrArg (fun y : R X => (y : matrixProjectiveDerived Q)) h
    have hA2 : matrixProjectiveProjection Q (A ^ 2) = 1 := by
      rw [map_pow, hAt, ht2]
    have hmem : A ^ 2 ∈ matrixDerivedScalars Q := by
      rw [← QuotientGroup.ker_mk' (matrixDerivedScalars Q), MonoidHom.mem_ker]
      exact hA2
    obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q (A ^ 2)).mp hmem
    have hAval2 : A.val ^ 2 = GeneralLinearGroup.scalar (Fin d) c := by
      rw [← Subgroup.coe_pow]
      exact hc.symm
    have hsqv : ∀ v : Fin d → K,
        matrixLinearIso A.val (matrixLinearIso A.val v) = ((c : K)) • v := by
      intro v
      calc matrixLinearIso A.val (matrixLinearIso A.val v)
          = (matrixLinearIso A.val * matrixLinearIso A.val) v := (LinearEquiv.mul_apply ..).symm
        _ = matrixLinearIso (A.val * A.val) v := by rw [map_mul]
        _ = matrixLinearIso (GeneralLinearGroup.scalar (Fin d) c) v := by
              rw [show A.val * A.val = GeneralLinearGroup.scalar (Fin d) c from by
                rw [← pow_two]; exact hAval2]
        _ = ((c : K)) • v := by
              rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixLinearIso_apply,
                GeneralLinearGroup.coe_scalar]
              ext i
              simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hlin_mem : matrixLinearIso A.val ∈ qRad Q X hXsing := eichlerRad_le_qRad hXsing hA'
    obtain ⟨x, hx, hx0⟩ : ∃ x ∈ X, x ≠ 0 := by
      by_contra hcon
      exact hX0 ((Submodule.eq_bot_iff X).mpr fun y hy => by
        by_contra hy0
        exact hcon ⟨y, hy, hy0⟩)
    have hqx : matrixLinearIso A.val x = x := (mem_qRad.mp hlin_mem).2.2 x hx
    have hcx : ((c : K)) • x = x := by
      have h1 := hsqv x
      rw [hqx, hqx] at h1
      exact h1.symm
    have hc1 : c = 1 := by
      apply Units.ext
      have h2 : (c : K) • x = (1 : K) • x := by rw [hcx, one_smul]
      have h3 : ((c : K) - 1) = 0 := by
        have h4 : ((c : K) - 1) • x = 0 := by rw [sub_smul, h2, sub_self]
        exact (smul_eq_zero.mp h4).resolve_right hx0
      exact sub_eq_zero.mp h3
    have hsq1 : matrixLinearIso A.val ^ 2 = 1 := by
      refine LinearEquiv.ext fun v => ?_
      rw [pow_two, LinearEquiv.mul_apply, hsqv, hc1, Units.val_one, one_smul]
      simp
    have hlin1 : matrixLinearIso A.val = 1 := OSeitz.eq_one_of_sq_eq_one_qRad h2 hlin_mem hsq1
    have hA1 : A = 1 := Subtype.ext (by
      have h : matrixLinearIso (A : GL (Fin d) K) = matrixLinearIso (1 : GL (Fin d) K) := by
        rw [hlin1, map_one]
      exact matrixLinearIso.injective h)
    have ht1 : t = 1 := by
      apply Subtype.ext
      rw [← hAt, hA1, map_one, Subgroup.coe_one]
    rw [ht1] at ht
    exact absurd ht (by norm_num)
  have hfinV : Module.finrank K (Fin d → K) = d := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hqPerp_eq : qPerp Q W = LinearMap.BilinForm.orthogonal Q.polarBilin W := by
    ext v
    rw [mem_qPerp, LinearMap.BilinForm.mem_orthogonal_iff]
    simp only [polarBilin_apply_apply]
  have hfinW : Module.finrank K (qPerp Q W) = d - Module.finrank K W := by
    rw [hqPerp_eq, LinearMap.BilinForm.finrank_orthogonal hnd, hfinV]
  have hfinY : Module.finrank K Y = Module.finrank K W := by
    have h1 : Module.finrank K Y + Module.finrank K (qPerp Q W) = d := by
      rw [Submodule.finrank_add_eq_of_isCompl hYcompl, hfinV]
    have hle : Module.finrank K W ≤ d := by
      have h := Submodule.finrank_le (R := K) (M := Fin d → K) W
      omega
    omega
  have hY0 : Y ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfinY
    exact hW0 (Submodule.finrank_eq_zero.mp hfinY.symm)
  have hdim : 2 * Module.finrank K W < Module.finrank K (Fin d → K) ∨
      3 ≤ Module.finrank K W := by
    have hle : 2 * Module.finrank K W ≤ d := by
      have h2' : Module.finrank K W ≤ Module.finrank K (qPerp Q W) :=
        Submodule.finrank_mono (le_qPerp_of_singular hW)
      omega
    rcases lt_or_eq_of_le hle with h | h
    · exact Or.inl (by rw [hfinV]; exact h)
    · exact Or.inr (by omega)
  have hgen : elementaryGroup Q ≤ eichlerRad Q W ⊔ eichlerRad Q Y :=
    elementaryGroup_le_eichlerRad_sup hnd h2 hW hYsing hYcompl hW0 hdim
  have hlinH : linH.range = (matrixDerived Q).map matrixLinearIso.toMonoidHom := by
    ext x
    simp [linH, MonoidHom.mem_range, Subgroup.mem_map]
  have hmapW : ((eichlerRad Q W).comap linH).map linH = eichlerRad Q W := by
    rw [Subgroup.map_comap_eq, hlinH, CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived,
      ← hder, inf_eq_right]
    exact eichlerRad_le_elementaryGroup Q W
  have hmapY : ((eichlerRad Q Y).comap linH).map linH = eichlerRad Q Y := by
    rw [Subgroup.map_comap_eq, hlinH, CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived,
      ← hder, inf_eq_right]
    exact eichlerRad_le_elementaryGroup Q Y
  have hlinHinj : Function.Injective linH := by
    intro a b h
    exact Subtype.ext (matrixLinearIso.injective h)
  have hlift : elementaryGroup Q ≤ RootPairOrth.liftSubgroup Q (R W ⊔ R Y) := by
    intro τ hτ
    have hτ' : τ ∈ eichlerRad Q W ⊔ eichlerRad Q Y := hgen hτ
    have hτder : τ ∈ (matrixDerived Q).map matrixLinearIso.toMonoidHom := by
      rw [CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived]
      exact hder ▸ hτ
    obtain ⟨A, hA, hAτ⟩ := Subgroup.mem_map.mp hτder
    have hlinA : linH ⟨A, hA⟩ = τ := hAτ
    have hsup : linH ⟨A, hA⟩ ∈ ((eichlerRad Q W).comap linH ⊔
        (eichlerRad Q Y).comap linH).map linH := by
      rw [Subgroup.map_sup, hmapW, hmapY, hlinA]
      exact hτ'
    obtain ⟨A', hA', hAA'⟩ := Subgroup.mem_map.mp hsup
    have hAA : A' = ⟨A, hA⟩ := hlinHinj hAA'
    rw [hAA] at hA'
    have hsupmap : R W ⊔ R Y = ((eichlerRad Q W).comap linH ⊔
        (eichlerRad Q Y).comap linH).map (matrixProjectiveProjection Q) := by
      rw [Subgroup.map_sup]
    refine RootPairOrth.mem_liftSubgroup.mpr ⟨⟨A, hA⟩, ?_, hAτ⟩
    rw [hsupmap]
    exact Subgroup.mem_map.mpr ⟨⟨A, hA⟩, hA', rfl⟩
  have htop : R W ⊔ R Y = ⊤ := RootPairOrth.eq_top_of_elementaryGroup_le hder hlift
  have hcardE : 2 ^ 2 ≤ Nat.card E := by rw [h4]; norm_num
  unfold PlaneGen
  rw [eq_top_iff, ← htop]
  exact sup_le (le_planeClosure_of_invariant_coprime (p := 2) hE hcardE hRW (hRodd W hW0 hW))
    (le_planeClosure_of_invariant_coprime (p := 2) hE hcardE hRY (hRodd Y hY0 hYsing))


end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter
