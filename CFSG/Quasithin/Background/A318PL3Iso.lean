module

public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree

public section

namespace CFSG.Quasithin

namespace A318P

open Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

noncomputable def pglEquivLinearAut (K : Type) [Field K] [Finite K] :
    StatedProj (⊤ : Subgroup (GL (Fin 3) K)) ≃* linearAutGroup 3 K := by
  let φ : (⊤ : Subgroup (GL (Fin 3) K)) →* linearAutGroup 3 K :=
    ((conjAut 3 K).codRestrict (linearAutGroup 3 K) conjAut_mem_linearAutGroup).comp
      Subgroup.topEquiv.toMonoidHom
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 x.2
    exact ⟨⟨A, Subgroup.mem_top A⟩, Subtype.ext hA⟩
  have hker : φ.ker = (StatedScalars (Fin 3) K).subgroupOf ⊤ := by
    ext A
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : conjAut 3 K (A : GL (Fin 3) K) = 1 := congrArg Subtype.val h
      obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) (A : GL (Fin 3) K)
        1 (by rw [map_one, mul_one]; exact h1)
      exact ⟨c, hc⟩
    · rintro ⟨c, hc⟩
      apply Subtype.ext
      change conjAut 3 K (A : GL (Fin 3) K) = 1
      rw [← hc, conjAut_scalar]
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)

variable {p f : ℕ} {K : Type} [Field K]

theorem statedGU_eq_unitaryIsom3 (h : UnitaryFieldData p f K) :
    StatedGU 3 (p ^ f) K = unitaryIsom3 h := by
  have hset : {A : GL (Fin 3) K | ((A : Matrix (Fin 3) (Fin 3) K).map (· ^ p ^ f))ᵀ *
      (A : Matrix (Fin 3) (Fin 3) K) = 1} = (unitaryIsom3 h : Set (GL (Fin 3) K)) := by
    ext A
    exact Iff.rfl
  rw [StatedGU, hset, Subgroup.closure_eq]

noncomputable def pguEquivPsuConj (h : UnitaryFieldData p f K) :
    StatedProj (StatedGU 3 (p ^ f) K) ≃* (psuConj h).range := by
  have := h.finite
  let ψ : ↥(StatedGU 3 (p ^ f) K) ≃* ↥(unitaryIsom3 h) :=
    MulEquiv.subgroupCongr (statedGU_eq_unitaryIsom3 h)
  have hker : ∀ A : ↥(unitaryIsom3 h), A ∈ (psuConj h).ker ↔
      (A : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    intro A
    rw [MonoidHom.mem_ker]
    constructor
    · intro hA
      obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one A 1
        (by rw [map_one, mul_one]; exact hA)
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      have hmem : GeneralLinearGroup.scalar (Fin 3) c ∈ unitaryIsom3 h := hc ▸ A.2
      have : A = ⟨_, hmem⟩ := Subtype.ext hc.symm
      rw [this]
      exact psuConj_scalar hmem
  have hmap : (((StatedScalars (Fin 3) K).subgroupOf (StatedGU 3 (p ^ f) K)).map ψ.toMonoidHom) =
      (psuConj h).ker := by
    ext A
    rw [Subgroup.mem_map_equiv]
    change ψ.symm A ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedGU 3 (p ^ f) K) ↔ _
    rw [Subgroup.mem_subgroupOf, hker]
    rfl
  exact (QuotientGroup.congr _ _ ψ hmap).trans (QuotientGroup.quotientKerEquivRange (psuConj h))

noncomputable def comapEquivOfMulEquiv {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G')
    (H' : Subgroup G') : (H'.comap Φ.toMonoidHom) ≃* H' :=
  (Subgroup.equivMapOfInjective _ Φ.toMonoidHom Φ.injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective Φ.surjective H'))

end A318P

end CFSG.Quasithin
