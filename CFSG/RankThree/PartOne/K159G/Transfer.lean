module

public import CFSG.RankThree.PartOne.U5E.Dict

public section

namespace CFSG.RankThree.PartOne.K159G

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.U5K CFSG.RankThree.PartOne.U5K.Kf
  CFSG.RankThree.PartOne.U5E
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

section Model

variable {G : Type*} [Group G] (I : Subgroup G) {f : ℕ} (hf : 1 ≤ f)
  (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f)

@[expose] noncomputable def modelMap : ↥I →* PI f hf :=
  ((u5Equiv f hf).toMonoidHom.comp e.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center ↥I))

theorem modelMap_apply (y : ↥I) :
    modelMap I hf e y = u5Equiv f hf (e (y : ↥I ⧸ Subgroup.center ↥I)) := rfl

theorem modelMap_eq_one_iff (y : ↥I) : modelMap I hf e y = 1 ↔ y ∈ Subgroup.center ↥I := by
  rw [modelMap_apply, ← map_one (u5Equiv f hf), (u5Equiv f hf).injective.eq_iff, ← map_one e,
    e.injective.eq_iff, QuotientGroup.eq_one_iff]

theorem ker_modelMap_le : (modelMap I hf e).ker ≤ Subgroup.center ↥I := fun y hy =>
  (modelMap_eq_one_iff I hf e y).1 hy

theorem congr_act_fix {x : G} (hx : x ∈ Subgroup.normalizer (I : Set G)) {y : ↥I}
    (hxy : x * (y : G) = (y : G) * x) :
    MulAut.congr (u5Equiv f hf) (U5Act I e ⟨x, hx⟩) (modelMap I hf e y) = modelMap I hf e y := by
  rw [modelMap_apply, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have h1 : (I.normalizerMonoidHom ⟨x, hx⟩ y : ↥I) = y := by
    apply Subtype.ext
    simp [hxy]
  rw [U5Act_apply, h1]

end Model

section Twist

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ} [Fact p.Prime]

theorem conj_dgU_apply (Z : ZetaData h p) (P : primeFormUnitary h (idGram K 5)) (a : Fin 5 → ZMod p)
    (z : primeFormP h (idGram K 5)) :
    primeFormConjHom h (idGram K 5) (Z.dgU a) (primeFormConjHom h (idGram K 5) P⁻¹ z) =
      primeFormConjHom h (idGram K 5) P⁻¹ (Z.par P a z) := by
  have h1 : Z.dgU a = P⁻¹ * Z.Y P a * P := by unfold ZetaData.Y; group
  rw [h1, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
  have h2 : primeFormConjHom h (idGram K 5) P (primeFormConjHom h (idGram K 5) P⁻¹ z) = z := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rw [h2]
  rfl

end Twist

section Fix

variable {G : Type*} [Group G] (I : Subgroup G) {f : ℕ} (hf : 1 ≤ f)
  (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f) {p : ℕ} [Fact p.Prime]

theorem fix_modelTwist (Z : ZetaData (u5FieldData f hf) p)
    (P : primeFormUnitary (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5)) (a : Fin 5 → ZMod p)
    {x : G} (hx : x ∈ Subgroup.normalizer (I : Set G))
    (hpar : Z.par P a = MulAut.congr (u5Equiv f hf) (U5Act I e ⟨x, hx⟩)) {y : ↥I}
    (hxy : x * (y : G) = (y : G) * x) :
    primeFormConjHom (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) (Z.dgU a)
        (primeFormConjHom (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) P⁻¹
          (modelMap I hf e y)) =
      primeFormConjHom (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) P⁻¹
        (modelMap I hf e y) := by
  rw [conj_dgU_apply, hpar, congr_act_fix I hf e hx hxy]

end Fix

section Ebar

variable {G : Type} [Group G] {N : Subgroup G} {f : ℕ} {hf : 1 ≤ f}
  {ρ : ↥N →* MulAut (projSU 5 2 f)} {E B : Subgroup G}

theorem mem_of_mem_EbarOf (hEN : E ≤ N) (hBE : B ≤ E)
    (hinjE : ∀ x ∈ E, ∀ hx : x ∈ N, ρ ⟨x, hx⟩ = 1 → x = 1) {x : G} (hxE : x ∈ E)
    (hmem : MulAut.congr (u5Equiv f hf) (ρ ⟨x, hEN hxE⟩) ∈ EbarOf hf ρ B) : x ∈ B := by
  obtain ⟨_, hb, hbeq⟩ := Subgroup.mem_map.1 hmem
  obtain ⟨b, hbN, hbB, rfl⟩ := mem_rm.1 hb
  have h1 : ρ ⟨b, hbN⟩ = ρ ⟨x, hEN hxE⟩ := (MulAut.congr (u5Equiv f hf)).injective hbeq
  have h2 : ρ ⟨b⁻¹ * x, N.mul_mem (N.inv_mem hbN) (hEN hxE)⟩ = 1 := by
    have : (⟨b⁻¹ * x, N.mul_mem (N.inv_mem hbN) (hEN hxE)⟩ : ↥N) = (⟨b, hbN⟩ : ↥N)⁻¹ * ⟨x, hEN hxE⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_inv, h1, inv_mul_cancel]
  have h3 : b⁻¹ * x = 1 := hinjE _ (E.mul_mem (E.inv_mem (hBE hbB)) hxE) _ h2
  have h4 : x = b := (inv_mul_eq_one.1 h3).symm
  rw [h4]
  exact hbB

end Ebar

section Perfect

variable {G : Type*} [Group G]

theorem commutator_eq_of_subgroupOf {C Q : Subgroup G} (hQC : Q ≤ C)
    (hQ : ⁅Q.subgroupOf C, Q.subgroupOf C⁆ = Q.subgroupOf C) : ⁅Q, Q⁆ = Q := by
  have := congrArg (Subgroup.map C.subtype) hQ
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQC] at this

theorem commutator_subgroupOf_eq {C Q : Subgroup G} (hQC : Q ≤ C) (hQ : ⁅Q, Q⁆ = Q) :
    ⁅Q.subgroupOf C, Q.subgroupOf C⁆ = Q.subgroupOf C := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQC, hQ]

end Perfect

end CFSG.RankThree.PartOne.K159G
