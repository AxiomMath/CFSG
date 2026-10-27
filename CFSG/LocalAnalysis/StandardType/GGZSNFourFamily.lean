module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices
public import Certificates.Certificate709543
public import Certificates.Certificate709544
import CFSG.LocalAnalysis.StandardType.GGZSNFourBound
import CFSG.LocalAnalysis.StandardType.GGZSNFourSound
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import CFSG.LocalAnalysis.StandardType.ZS.NFourRelations
import CFSG.LocalAnalysis.StandardType.ZS.FamilyOfMulEquiv
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import all CFSG.LocalAnalysis.StandardType.GGZSKModelIso
import CFSG.Mathlib.LinearAlgebra.Matrix.ReflectionClass
import CFSG.Timmesfeld.Components

public section

namespace CFSG.StandardType.ZS

local instance factPrimeThirteenFamily : Fact (Nat.Prime 13) := ⟨by norm_num⟩

private lemma zmod_two_ne_zero_of_ne_two {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp)

private lemma linearEquiv_neg_ne_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Nontrivial U] :
    (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : U)
  have h0 : -x = x := by
    simpa using congrArg (fun e : U ≃ₗ[ZMod p] U => e x) h
  have h2 : (2 : ZMod p) • x = 0 := by
    rw [two_smul]
    exact (neg_eq_iff_add_eq_zero).mp h0
  exact zmod_two_ne_zero_of_ne_two hp
    ((smul_eq_zero.mp h2).resolve_right hx)

private lemma coe_prod_map_subtype {m p : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} {s : Fin m → U ≃ₗ[ZMod p] U}
    {s' : Fin m → ↥A} (hcoe : ∀ i, (s' i : U ≃ₗ[ZMod p] U) = s i) (l : List (Fin m)) :
    ((l.map s').prod : U ≃ₗ[ZMod p] U) = (l.map s).prod := by
  change Subgroup.subtype A ((l.map s').prod) = (l.map s).prod
  rw [map_list_prod (Subgroup.subtype A) (l.map s'), List.map_map]
  rw [show l.map (Subgroup.subtype A ∘ s') = l.map s from
    List.map_congr_left (fun i _ => hcoe i)]

lemma aMat_eq_halfOnesMat :
    (aMat : Matrix (Fin 4) (Fin 4) (ZMod 13)) = halfOnesMat 4 := by
  have h2 : (2 : ZMod 13)⁻¹ = 7 :=
    inv_eq_of_mul_eq_one_right (by decide : (2 : ZMod 13) * 7 = 1)
  ext r c
  fin_cases r <;> fin_cases c <;> simp [aMat, halfOnesMat, h2]

lemma n4Rel_of_model {t : Fin 4 → ↥(model .N4)}
    (htm : ∀ i, ((t i).1 : Matrix (Fin (mdeg .N4)) (Fin (mdeg .N4)) (ZMod 13)) =
      ![piMat 0 1 1, piMat 1 2 1, piMat 0 1 5, aMat] i) : N4Rel t := by
  let φ : ↥(model .N4) →* Matrix (Fin 4) (Fin 4) (ZMod 13) :=
    (Units.coeHom (Matrix (Fin 4) (Fin 4) (ZMod 13))).comp (Subgroup.subtype (model .N4))
  have hφ : ∀ i, φ (t i) = n4Mat (5 : ZMod 13) i := by
    intro i
    fin_cases i
    · exact htm 0
    · exact htm 1
    · exact htm 2
    · have h3 : φ (t 3) = aMat := htm 3
      exact h3.trans aMat_eq_halfOnesMat
  refine n4Rel_of_injective φ
    (Units.val_injective.comp (Subgroup.subtype_injective _)) ?_
  change N4Rel (fun i => φ (t i))
  rw [show (fun i => φ (t i)) = n4Mat (5 : ZMod 13) from funext hφ]
  exact n4Rel_n4Mat (by decide) (by decide)

lemma en4Rel_of_model {t : Fin 5 → ↥(model .EN4)}
    (htm : ∀ i, ((t i).1 : Matrix (Fin (mdeg .EN4)) (Fin (mdeg .EN4)) (ZMod 13)) =
      ![piMat 0 1 1, piMat 1 2 1, piMat 0 1 5, aMat,
        Matrix.diagonal fun j => if j = 3 then -1 else 1] i) : EN4Rel t := by
  let φ : ↥(model .EN4) →* Matrix (Fin 4) (Fin 4) (ZMod 13) :=
    (Units.coeHom (Matrix (Fin 4) (Fin 4) (ZMod 13))).comp (Subgroup.subtype (model .EN4))
  have hφ : ∀ i, φ (t i) = en4Mat (5 : ZMod 13) i := by
    intro i
    fin_cases i
    · exact htm 0
    · exact htm 1
    · exact htm 2
    · have h3 : φ (t 3) = aMat := htm 3
      exact h3.trans aMat_eq_halfOnesMat
    · exact htm 4
  refine en4Rel_of_injective φ
    (Units.val_injective.comp (Subgroup.subtype_injective _)) ?_
  change EN4Rel (fun i => φ (t i))
  rw [show (fun i => φ (t i)) = en4Mat (5 : ZMod 13) from funext hφ]
  exact en4Rel_en4Mat (by decide) (by decide)

private lemma n4_isConj_of_rel {G : Type*} [Group G] {t : Fin 4 → G} (h : N4Rel t) :
    ∀ i, IsConj (t 0) (t i) := by
  obtain ⟨hpair, -⟩ := h
  have hsq : ∀ i, t i * t i = 1 := mul_self_of_pair_rel hpair (by decide)
  have h01 : IsConj (t 0) (t 1) :=
    isConj_of_mul_pow_three (hsq 0) (hsq 1) (pow_three_of_pair_rel hpair (by decide))
  have h12 : IsConj (t 1) (t 2) :=
    isConj_of_mul_pow_three (hsq 1) (hsq 2) (pow_three_of_pair_rel hpair (by decide))
  have h23 : IsConj (t 2) (t 3) :=
    isConj_of_mul_pow_three (hsq 2) (hsq 3) (pow_three_of_pair_rel hpair (by decide))
  intro i
  fin_cases i
  · exact IsConj.refl (t 0)
  · exact h01
  · exact h01.trans h12
  · exact (h01.trans h12).trans h23

private lemma en4_isConj_of_rel {G : Type*} [Group G] {t : Fin 5 → G} (h : EN4Rel t) :
    ∀ i, IsConj (t 0) (t i) := by
  obtain ⟨hpair, -, -⟩ := h
  have hsq : ∀ i, t i * t i = 1 := mul_self_of_pair_rel hpair (by decide)
  have h01 : IsConj (t 0) (t 1) :=
    isConj_of_mul_pow_three (hsq 0) (hsq 1) (pow_three_of_pair_rel hpair (by decide))
  have h12 : IsConj (t 1) (t 2) :=
    isConj_of_mul_pow_three (hsq 1) (hsq 2) (pow_three_of_pair_rel hpair (by decide))
  have h23 : IsConj (t 2) (t 3) :=
    isConj_of_mul_pow_three (hsq 2) (hsq 3) (pow_three_of_pair_rel hpair (by decide))
  have h34 : IsConj (t 3) (t 4) :=
    isConj_of_mul_pow_three (hsq 3) (hsq 4) (pow_three_of_pair_rel hpair (by decide))
  intro i
  fin_cases i
  · exact IsConj.refl (t 0)
  · exact h01
  · exact h01.trans h12
  · exact (h01.trans h12).trans h23
  · exact ((h01.trans h12).trans h23).trans h34

private lemma isConj_first_of_isReflMat {m : ℕ} {k : ExcRow} [NeZero m]
    {t : Fin m → ↥(model k)} (hsq0 : t 0 * t 0 = 1)
    (hconj : ∀ i, IsConj (t 0) (t i)) (hrefl0 : IsReflMat (t 0).1)
    (htgen : Subgroup.closure (Set.range t) = ⊤)
    (hG : (Nat.card (model k) : ZMod 13) ≠ 0) :
    ∀ g : ↥(model k), IsReflMat g.1 → IsConj (t 0) g := by
  have hc2 : ((t 0 : ↥(model k)) :
      Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)) *
      ((t 0 : ↥(model k)) :
        Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)) = 1 := by
    simpa using congrArg Subtype.val hsq0
  have hgen := closure_conj_of_forall_isConj (model k) t htgen hconj
  intro g hg
  obtain ⟨h, hh, hgh⟩ := Matrix.GeneralLinearGroup.exists_conj_of_closure_conj_eq
    (n := Fin (mdeg k)) (K := ZMod 13)
    (s := (g : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)))
    hG hc2 hrefl0.2 hgen g.2 hg.1 hg.2
  exact isConj_iff.mpr ⟨⟨h, hh⟩, Subtype.ext (by simpa using hgh.symm)⟩

lemma card_model_n4 :
    Nat.card (model .N4) = 7680 := by
  obtain ⟨r, htm, hrgen, hrcard, -, -, -, -, -, -⟩ := exists_n4_model
  refine le_antisymm ?_ hrcard
  have h := card_closure_le_of_n4Rel (n4Rel_of_model htm)
  rw [hrgen, Subgroup.card_top] at h
  exact h

lemma card_model_en4 :
    Nat.card (model .EN4) = 46080 := by
  obtain ⟨r, htm, hrgen, hrcard, -, -, -, -, -, -⟩ := exists_en4_model
  refine le_antisymm ?_ hrcard
  have h := card_closure_le_of_en4Rel (en4Rel_of_model htm)
  rw [hrgen, Subgroup.card_top] at h
  exact h

private lemma exists_subtype_tuple_of_prod {m p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Nontrivial U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {s : Fin m → (U ≃ₗ[ZMod p] U)} (w : List (Fin m))
    (hgen : Subgroup.closure (Set.range s) = A)
    (hprod : (w.map s).prod = LinearEquiv.neg (ZMod p)) :
    ∃ s' : Fin m → ↥A,
      Subgroup.closure (Set.range s') = ⊤ ∧
      (∀ i, (s' i : U ≃ₗ[ZMod p] U) = s i) ∧
      ((w.map s').prod : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p) ∧
      (w.map s').prod ≠ 1 := by
  obtain ⟨s', htop, hcoe⟩ := exists_subtype_tuple (A := A) hgen
  have hprod' : ((w.map s').prod : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p) := by
    rw [coe_prod_map_subtype hcoe w]
    exact hprod
  refine ⟨s', htop, hcoe, hprod', ?_⟩
  intro h1
  have h2 : ((w.map s').prod : U ≃ₗ[ZMod p] U) = 1 := by
    simpa using congrArg Subtype.val h1
  rw [hprod'] at h2
  exact linearEquiv_neg_ne_one hp h2

private lemma exists_n4_subtype_tuple {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] (f : Module.Basis (Fin 4) (ZMod p) U)
    {t : ZMod p} (ht : t ^ 2 = -1) :
    ∃ s' : Fin 4 → ↥(basisClosure f (weylN4Mats t)),
      Subgroup.closure (Set.range s') = ⊤ ∧ N4Rel s' ∧
      (∀ i, LinearMap.toMatrix f f (s' i : U →ₗ[ZMod p] U) = n4Mat t i) ∧
      ((n4ZW.map s').prod : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p) ∧
      (n4ZW.map s').prod ≠ 1 := by
  have : Nontrivial U := ⟨f 0, 0, Module.Basis.ne_zero f 0⟩
  obtain ⟨s, hsmat, hgen, hrel, hprod⟩ :=
    exists_n4_tuple (zmod_two_ne_zero_of_ne_two hp) ht f
  obtain ⟨s', htop, hcoe, hprod', hne⟩ :=
    exists_subtype_tuple_of_prod (A := basisClosure f (weylN4Mats t)) (w := n4ZW) hp hgen hprod
  have hrel' : N4Rel s' := by
    refine n4Rel_of_injective (Subgroup.subtype (basisClosure f (weylN4Mats t)))
      (Subgroup.subtype_injective _) ?_
    change N4Rel (fun i => (s' i : U ≃ₗ[ZMod p] U))
    rw [funext hcoe]
    exact hrel
  have hmat : ∀ i, LinearMap.toMatrix f f (s' i : U →ₗ[ZMod p] U) = n4Mat t i := by
    intro i
    rw [hcoe i]
    exact hsmat i
  exact ⟨s', htop, hrel', hmat, hprod', hne⟩

private lemma exists_en4_subtype_tuple {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] (f : Module.Basis (Fin 4) (ZMod p) U)
    {t : ZMod p} (ht : t ^ 2 = -1) :
    ∃ s' : Fin 5 → ↥(basisClosure f (weylEN4Mats t)),
      Subgroup.closure (Set.range s') = ⊤ ∧ EN4Rel s' ∧
      (∀ i, LinearMap.toMatrix f f (s' i : U →ₗ[ZMod p] U) = en4Mat t i) ∧
      ((en4ZW.map s').prod : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p) ∧
      (en4ZW.map s').prod ≠ 1 := by
  have : Nontrivial U := ⟨f 0, 0, Module.Basis.ne_zero f 0⟩
  obtain ⟨s, hsmat, hgen, hrel, hprod⟩ :=
    exists_en4_tuple (zmod_two_ne_zero_of_ne_two hp) ht f
  obtain ⟨s', htop, hcoe, hprod', hne⟩ :=
    exists_subtype_tuple_of_prod (A := basisClosure f (weylEN4Mats t)) (w := en4ZW) hp hgen hprod
  have hrel' : EN4Rel s' := by
    refine en4Rel_of_injective (Subgroup.subtype (basisClosure f (weylEN4Mats t)))
      (Subgroup.subtype_injective _) ?_
    change EN4Rel (fun i => (s' i : U ≃ₗ[ZMod p] U))
    rw [funext hcoe]
    exact hrel
  have hmat : ∀ i, LinearMap.toMatrix f f (s' i : U →ₗ[ZMod p] U) = en4Mat t i := by
    intro i
    rw [hcoe i]
    exact hsmat i
  exact ⟨s', htop, hrel', hmat, hprod', hne⟩

theorem family_n4 {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p} (ht : t ^ 2 = -1) :
    Family p (basisClosure f (weylN4Mats t)) := by
  classical
  obtain ⟨r, hrMat, hrGen, hrCard, hrNorm, hrCen, hrPair, hrInv, hrRefl, hrOrd⟩ :=
    exists_n4_model
  have hrel : N4Rel r := n4Rel_of_model hrMat
  have hconj : ∀ i, IsConj (r 0) (r i) := n4_isConj_of_rel hrel
  have hcard : Nat.card (model .N4) = 7680 := card_model_n4
  have hG : (Nat.card (model .N4) : ZMod 13) ≠ 0 := by
    rw [hcard]
    decide
  have hrefl : ∀ g : ↥(model .N4), IsReflMat g.1 → IsConj (r 0) g :=
    isConj_first_of_isReflMat (k := .N4) (mul_self_of_pair_rel hrel.1 (by decide) 0)
      hconj hrRefl hrGen hG
  obtain ⟨s', htop, hsrel, hsmat, hsprod, hsz⟩ := exists_n4_subtype_tuple hp f ht
  obtain ⟨e, he⟩ := exists_mulEquiv_of_n4Rel (r := r) (s := s') hrel hsrel hrGen htop
    hrCard hrNorm hsz
  have hU : Module.finrank (ZMod p) U = ExcRow.N4.deg := by
    rw [Module.finrank_eq_card_basis f, Fintype.card_fin]
    rfl
  have hord : ExcRow.N4.ord = 7680 := by decide
  refine family_exc_of_mulEquiv (k := .N4) hp trivial rfl hU e ?_ hrCen (r 0)
    ((n4ZW.map r).prod) hrRefl ?_ ?_ hrefl hrPair ?_ hrInv
  · exact hcard.trans hord.symm
  · rw [he 0]
    exact isRefl_of_toMatrix_eq_pijMat (t := (s' 0 : U ≃ₗ[ZMod p] U)) f (i := 0) (j := 1)
      (by decide) one_ne_zero (by simpa [n4Mat] using hsmat 0)
  · have hmap : e ((n4ZW.map r).prod) = (n4ZW.map s').prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => he i)
    rw [hmap]
    exact hsprod
  · exact ⟨r 0, r 2, IsConj.refl _, hconj 2, hrOrd⟩

theorem family_en4 {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (f : Module.Basis (Fin 4) (ZMod p) U) {t : ZMod p} (ht : t ^ 2 = -1) :
    Family p (basisClosure f (weylEN4Mats t)) := by
  classical
  obtain ⟨r, hrMat, hrGen, hrCard, hrNorm, hrCen, hrPair, hrInv, hrRefl, hrOrd⟩ :=
    exists_en4_model
  have hrel : EN4Rel r := en4Rel_of_model hrMat
  have hconj : ∀ i, IsConj (r 0) (r i) := en4_isConj_of_rel hrel
  have hcard : Nat.card (model .EN4) = 46080 := card_model_en4
  have hG : (Nat.card (model .EN4) : ZMod 13) ≠ 0 := by
    rw [hcard]
    decide
  have hrefl : ∀ g : ↥(model .EN4), IsReflMat g.1 → IsConj (r 0) g :=
    isConj_first_of_isReflMat (k := .EN4) (mul_self_of_pair_rel hrel.1 (by decide) 0)
      hconj hrRefl hrGen hG
  obtain ⟨s', htop, hsrel, hsmat, hsprod, hsz⟩ := exists_en4_subtype_tuple hp f ht
  obtain ⟨e, he⟩ := exists_mulEquiv_of_en4Rel (r := r) (s := s') hrel hsrel hrGen htop
    hrCard hrNorm hsz
  have hU : Module.finrank (ZMod p) U = ExcRow.EN4.deg := by
    rw [Module.finrank_eq_card_basis f, Fintype.card_fin]
    rfl
  have hord : ExcRow.EN4.ord = 46080 := by decide
  refine family_exc_of_mulEquiv (k := .EN4) hp trivial rfl hU e ?_ hrCen (r 0)
    ((en4ZW.map r).prod) hrRefl ?_ ?_ hrefl hrPair ?_ hrInv
  · exact hcard.trans hord.symm
  · rw [he 0]
    exact isRefl_of_toMatrix_eq_pijMat (t := (s' 0 : U ≃ₗ[ZMod p] U)) f (i := 0) (j := 1)
      (by decide) one_ne_zero (by simpa [en4Mat] using hsmat 0)
  · have hmap : e ((en4ZW.map r).prod) = (en4ZW.map s').prod := by
      rw [map_list_prod, List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => he i)
    rw [hmap]
    exact hsprod
  · exact ⟨r 0, r 2, IsConj.refl _, hconj 2, hrOrd⟩

end CFSG.StandardType.ZS

end
