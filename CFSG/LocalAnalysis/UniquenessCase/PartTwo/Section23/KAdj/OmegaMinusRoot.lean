module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaMinusModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusAct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaPlusActOne
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerOrthOne
import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusFamData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.AGLEmbedding.LeviBlock
open CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open scoped MatrixGroups

@[expose] noncomputable def omegaMinusRootEmb (K : Type) [Field K] :
    SL(2, K) →* ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) :=
  (prodHom (Fin 2 → K)).comp (plusRootEmbTwo K)

theorem omegaMinusRootEmb_injective (K : Type) [Field K] :
    Function.Injective (omegaMinusRootEmb K) := by
  intro A B h
  exact plusRootEmbTwo_injective K (CFSG.LocalAnalysis.GLTheoremA.prodHom_apply_injective h)

private theorem plusRootEmbTwo_mem_flagStab_E15 {K : Type} [Field K] [Finite K] [CharP K 2]
    (A : SL(2, K)) : plusRootEmbTwo K A ∈ plusFlagStab K 3 ({1} : Finset ℕ) := by
  show plusResExt K (show 1 + 2 = 3 from rfl) (plusIotaTwo K A) ∈
    plusFlagStab K 3 ({1} : Finset ℕ)
  exact plusResExt_iotaTwo_mem (r := 3) (t := 1) (D := {1}) le_rfl rfl
    (fun d hd => by simp only [Finset.mem_singleton] at hd; omega) A

theorem omegaMinusRootEmb_range_le (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K) :
    (omegaMinusRootEmb K).range ≤ orthElementaryGroup (quadTail 3 (minusTailForm K b c)) := by
  rintro _ ⟨A, rfl⟩
  exact CFSG.LocalAnalysis.GLTheoremA.orthElementaryGroup_map_prodHom_le (r := 3)
    (qA := minusTailForm K b c)
    (Subgroup.mem_map_of_mem (prodHom (Fin 2 → K))
      (mem_plusFlagStab.1 (plusRootEmbTwo_mem_flagStab_E15 A)).1)

@[expose] noncomputable def omegaMinusRootHom (K : Type) [Field K] [Finite K] [CharP K 2]
    (b c : K) :
    SL(2, K) →* OmegaMinusE K b c :=
  (omegaMinusRootEmb K).codRestrict _ (fun A => omegaMinusRootEmb_range_le K b c ⟨A, rfl⟩)

private lemma omegaMinusRootHom_coe_E15 (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (A : SL(2, K)) :
    ((omegaMinusRootHom K b c A : OmegaMinusE K b c) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
      prodHom (Fin 2 → K) (plusRootEmbTwo K A) :=
  rfl

noncomputable abbrev omegaMinusRoot (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K) :
    Subgroup (OmegaMinusE K b c) :=
  (omegaMinusRootHom K b c).range

theorem omegaMinusRootHom_injective (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K) :
    Function.Injective (omegaMinusRootHom K b c) := by
  intro A B h
  exact omegaMinusRootEmb_injective K (congrArg Subtype.val h)

private theorem mem_tailQZero_of_prodHom_E15 {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} {x : OmegaMinusE K b c} {g : PlusLin K}
    (hx : ((x : OmegaMinusE K b c) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        prodHom (Fin 2 → K) g)
    (hg : g ∈ plusFlagStab K 3 ({1} : Finset ℕ)) : x ∈ omegaMinusTailQZero K b c := by
  rw [omegaMinusTailQZero, mem_orthParab, Fin.forall_fin_two]
  constructor
  · rw [show (![0, 1] : Fin 2 → ℕ) 0 = 0 from by simp, tailFlag_zero, Submodule.map_bot]
  · have hstab : (flag 3 K 1).map
        (g : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K)) = flag 3 K 1 := by
      have h := (mem_plusFlagStab.1 hg).2 1 (by simp)
      change Submodule.map (g : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K))
        (flag 3 K 1) = flag 3 K 1 at h
      exact h
    rw [show (![0, 1] : Fin 2 → ℕ) 1 = 1 from by simp, hx, prodHom_apply,
      map_tailFlag_prodCongr_eq_iff, hstab]

theorem omegaMinusRoot_le_tailQZero (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K) :
    omegaMinusRoot K b c ≤ omegaMinusTailQZero K b c := by
  rintro x ⟨A, rfl⟩
  exact mem_tailQZero_of_prodHom_E15 (g := plusRootEmbTwo K A) rfl
    (plusRootEmbTwo_mem_flagStab_E15 A)

private theorem commutator_range_eq_self_E15 {G H : Type} [Group G] [Group H] (f : G →* H)
    (hG : Group.IsPerfect G) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map f, ← Subgroup.map_commutator,
    show ⁅(⊤ : Subgroup G), ⊤⁆ = ⊤ from hG.commutator_eq_top]

private theorem isSLn_range_E15 {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {H : Type} [Group H] (f : SL(2, K) →* H) (hf : Function.Injective f) :
    IsSLn ↥f.range 2 n := by
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  exact ⟨(MonoidHom.ofInjective hf).symm.trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)⟩

theorem omegaMinusRoot_le_hinf {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (b c : K) :
    omegaMinusRoot K b c ≤ Hinf (omegaMinusTailQZero K b c) := by
  refine CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual ?_
    (omegaMinusRoot_le_tailQZero K b c)
  exact commutator_range_eq_self_E15 (omegaMinusRootHom K b c)
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)

theorem isSLn_omegaMinusRoot {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (b c : K) : IsSLn ↥(omegaMinusRoot K b c) 2 n := by
  exact isSLn_range_E15 hK (omegaMinusRootHom K b c) (omegaMinusRootHom_injective K b c)

theorem omegaMinusRootHom_conj {K : Type} [Field K] [Finite K] [CharP K 2] {u b' : Kˣ}
    (hb : b' ^ 2 = u⁻¹) (b c : K)
    {τ : OmegaMinusE K b c}
    (hτ : ((τ : OmegaMinusE K b c) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        prodHom (Fin 2 → K) (torusElt 3 K ![u, u⁻¹, 1])) (A : SL(2, K)) :
    τ * omegaMinusRootHom K b c A * τ⁻¹ =
      omegaMinusRootHom K b c (plusDiagSL2 b' * A * (plusDiagSL2 b')⁻¹) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hτ, omegaMinusRootHom_coe_E15 K b c A,
    omegaMinusRootHom_coe_E15 K b c (plusDiagSL2 b' * A * (plusDiagSL2 b')⁻¹),
    ← map_inv, ← map_mul, ← map_mul]
  rw [torusElt_mul_plusRootEmbTwo_mul_inv (c := u) (b := b') hb A]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
