module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TIFusion
public import CFSG.GroupTheory.FusionFamilyControl
public import CFSG.GroupTheory.IrreducibleAbelianAction
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.RankThreeUC.Focal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Data

open CFSG.GroupTheory
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem U_eq_Z_of_familyControlsFusion (D : Data G)
    (hfus : CFSG.GroupTheory.FamilyControlsFusion (calMOf D.T) D.T)
    (hcyc : ∃ x ∈ D.T, ∀ y ∈ D.T, ∃ m : ℕ, y⁻¹ * x ^ m ∈ centralizer (D.U : Set G))
    (hX : ∀ N ∈ calMOf D.T, N ≠ D.M → ∃ X : Subgroup G, X ≤ N ∧ (X.subgroupOf N).Normal ∧
        ((X : Set G) * ((N ⊓ D.M : Subgroup G) : Set G) = N) ∧
        D.T ⊓ (X ⊔ (N ⊓ centralizer (D.U : Set G))) ≤ centralizer (D.U : Set G)) :
    D.U = D.Z := by
  classical
  obtain ⟨T, hTcoe⟩ : ∃ T : Sylow 2 G, (T : Subgroup G) = D.T := by
    have hs := D.sylowG
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right] at hs
    exact ⟨hs.2.1.toSylow hs.2.2, rfl⟩
  have hfus' : FamilyControlsFusion (calMOf D.T) (T : Subgroup G) := by
    rwa [hTcoe]
  have hMC : D.M ≤ Subgroup.normalizer
      (Subgroup.centralizer (D.U : Set G) : Set G) := by
    rw [← normalizer_U_eq D]
    exact CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (D.U)
  have hTC : (T : Subgroup G) ≤ Subgroup.centralizer (D.U : Set G) := by
    apply sylow_le_of_familyControlsFusion_of_perfect (T := T)
      (S := Subgroup.centralizer (D.U : Set G)) (F := calMOf D.T) hfus'
    · intro H hH
      simpa [hTcoe] using hH.2
    · intro H hH
      by_cases hHM : H = D.M
      ·
        subst hHM
        rw [hTcoe]
        have hMnorms : D.M ≤ Subgroup.normalizer
            ((D.M ⊓ Subgroup.centralizer (D.U : Set G) : Subgroup G) : Set G) := by
          refine (le_inf Subgroup.le_normalizer hMC).trans ?_
          exact Subgroup.inf_normalizer_le_normalizer_inf
        have hKn : ((D.M ⊓ Subgroup.centralizer (D.U : Set G)).subgroupOf D.M).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hMnorms
        refine ⟨D.M ⊓ Subgroup.centralizer (D.U : Set G), hKn, inf_le_left, ?_, ?_⟩
        · exact (inf_le_right :
            D.T ⊓ (D.M ⊓ Subgroup.centralizer (D.U : Set G)) ≤
              D.M ⊓ Subgroup.centralizer (D.U : Set G)).trans inf_le_right
        · exact isCyclic_quotient_of_cyclic_mod D.sylowM.le inf_le_left hKn
            (inf_le_inf D.sylowM.le le_rfl) hcyc
      ·
        rw [hTcoe]
        obtain ⟨X, hXN, hXnormal, hXmul, hXTC⟩ := hX H hH hHM
        set C : Subgroup G := Subgroup.centralizer (D.U : Set G) with hCdef
        set K : Subgroup G := X ⊔ (H ⊓ C) with hKdef
        have hHNX : H ≤ Subgroup.normalizer (X : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mp hXnormal
        have hconjHC_X : ∀ {x c : G}, x ∈ X → c ∈ H ⊓ C → x * c * x⁻¹ ∈ K := by
          intro x c hx hc
          have hcX : c * x⁻¹ * c⁻¹ ∈ X :=
            (Subgroup.mem_normalizer_iff.mp (hHNX hc.1) x⁻¹).mp (X.inv_mem hx)
          have heq : x * c * x⁻¹ = (x * (c * x⁻¹ * c⁻¹)) * c := by group
          rw [hKdef, heq]
          exact Subgroup.mul_mem _
            (Subgroup.mem_sup_left (X.mul_mem hx hcX))
            (Subgroup.mem_sup_right hc)
        have hconjK_X : ∀ {x k : G}, x ∈ X → k ∈ K → x * k * x⁻¹ ∈ K := by
          intro x k hx hk
          rw [hKdef, Subgroup.sup_eq_closure] at hk
          refine Subgroup.closure_induction
            (p := fun k _ => x * k * x⁻¹ ∈ K) ?_ ?_ ?_ ?_ hk
          · intro a ha
            rcases ha with haX | haHC
            · exact Subgroup.mem_sup_left
                ((Subgroup.mem_normalizer_iff.mp (hHNX (hXN hx)) a).mp haX)
            · exact hconjHC_X hx haHC
          · simp
          · intro a b _ _ iha ihb
            have heq : x * (a * b) * x⁻¹ =
                (x * a * x⁻¹) * (x * b * x⁻¹) := by group
            rw [heq]
            exact K.mul_mem iha ihb
          · intro a _ iha
            have heq : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
            rw [heq]
            exact K.inv_mem iha
        have hXnormK : X ≤ Subgroup.normalizer (K : Set G) :=
          Subgroup.le_normalizer_iff.mpr fun x hx k hk => hconjK_X hx hk
        have hconjK_M : ∀ {m k : G}, m ∈ H → m ∈ D.M → k ∈ K → m * k * m⁻¹ ∈ K := by
          intro m k hmH hmM hk
          rw [hKdef, Subgroup.sup_eq_closure] at hk
          refine Subgroup.closure_induction
            (p := fun k _ => m * k * m⁻¹ ∈ K) ?_ ?_ ?_ ?_ hk
          · intro a ha
            rcases ha with haX | haHC
            · exact Subgroup.mem_sup_left
                ((Subgroup.mem_normalizer_iff.mp (hHNX hmH) a).mp haX)
            · exact Subgroup.mem_sup_right
                ⟨H.mul_mem (H.mul_mem hmH haHC.1) (H.inv_mem hmH),
                  (Subgroup.mem_normalizer_iff.mp (hMC hmM) a).mp haHC.2⟩
          · simp
          · intro a b _ _ iha ihb
            have heq : m * (a * b) * m⁻¹ =
                (m * a * m⁻¹) * (m * b * m⁻¹) := by group
            rw [heq]
            exact K.mul_mem iha ihb
          · intro a _ iha
            have heq : m * a⁻¹ * m⁻¹ = (m * a * m⁻¹)⁻¹ := by group
            rw [heq]
            exact K.inv_mem iha
        have hHMnormK : H ⊓ D.M ≤ Subgroup.normalizer (K : Set G) :=
          Subgroup.le_normalizer_iff.mpr fun m hm k hk => hconjK_M hm.1 hm.2 hk
        have hNnormK : H ≤ Subgroup.normalizer (K : Set G) := by
          intro n hn
          have hn' : n ∈ (X : Set G) * ((H ⊓ D.M : Subgroup G) : Set G) := by
            rw [hXmul]
            exact hn
          obtain ⟨x, hx, m, hm, rfl⟩ := hn'
          exact (Subgroup.normalizer (K : Set G)).mul_mem (hXnormK hx) (hHMnormK hm)
        have hKle : K ≤ H := by
          rw [hKdef]
          exact sup_le hXN inf_le_left
        have hKn : (K.subgroupOf H).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mpr hNnormK
        have hTKC : D.T ⊓ K ≤ C := by
          rw [hKdef]
          exact hXTC
        have hPCK : D.T ⊓ C ≤ K := by
          rw [hKdef]
          exact (inf_le_inf hH.2 le_rfl).trans le_sup_right
        refine ⟨K, hKn, hKle, ?_, ?_⟩
        · simpa [hCdef] using hTKC
        · exact isCyclic_quotient_of_cyclic_mod hH.2 hKle hKn hPCK hcyc
    · haveI := D.standing.simple
      exact CFSG.LocalAnalysis.RankThreeUC.commutator_eq_top_of_standing D.standing.nonab
  rw [hTcoe] at hTC
  have hUleM : D.U ≤ D.M :=
    ((CFSG.LocalAnalysis.RankThreeUC.uCore_le_and_isElemAbelian D.standing.charTwo
      D.maxLocal.1 D.sylowM).1.trans inf_le_left).trans (CFSG.openPCoreOf_le 2 D.M)
  have hUT : D.U ≤ D.T := by
    have hsup : IsPGroup 2 (D.T ⊔ D.U : Subgroup G) :=
      (D.sylowM.isPGroup).to_sup_of_normal_right' (U_isPGroup D)
        (D.sylowM.le.trans (CFSG.LocalAnalysis.RankThreeUC.le_normalizer_uCore D.M D.T))
    have hEq : D.T ⊔ D.U = D.T :=
      D.sylowM.eq_of_le le_sup_left (sup_le D.sylowM.le hUleM) hsup
    exact (le_sup_right : D.U ≤ D.T ⊔ D.U).trans hEq.le
  have hUC : D.U ≤ Subgroup.centralizer (D.T : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htC := hTC ht
    rw [Subgroup.mem_centralizer_iff] at htC
    exact (htC u hu).symm
  have hUleZ : D.U ≤ D.Z := by
    change (⨆ m : D.M,
      (CFSG.RankThree.PartOne.omegaOneCenterIn D.T).map
        (MulAut.conj (m : G)).toMonoidHom) ≤
      CFSG.RankThree.PartOne.omegaOneCenterIn D.T
    refine iSup_le fun m => ?_
    rintro _ ⟨z, hz, rfl⟩
    have hzU : z ∈ D.U := Z_le_U D hz
    have hmU : (m : G) * z * (m : G)⁻¹ ∈ D.U :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LocalAnalysis.RankThreeUC.le_normalizer_uCore D.M D.T m.2) z).mp hzU
    have hzT : (m : G) * z * (m : G)⁻¹ ∈ D.T := hUT hmU
    have hzC : (m : G) * z * (m : G)⁻¹ ∈ Subgroup.centralizer (D.T : Set G) := hUC hmU
    have hz2 : z ^ 2 = 1 :=
      (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp hz).2.2
    refine (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff).mpr
      ⟨hzT, Subgroup.mem_centralizer_iff.mp hzC, ?_⟩
    calc ((m : G) * z * (m : G)⁻¹) ^ 2
        = ((m : G) * z * (m : G)⁻¹) * ((m : G) * z * (m : G)⁻¹) := pow_two _
      _ = (m : G) * (z * z) * (m : G)⁻¹ := by group
      _ = (m : G) * z ^ 2 * (m : G)⁻¹ := by rw [pow_two]
      _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
  exact le_antisymm hUleZ (Z_le_U D)

end CFSG.LocalAnalysis.UniquenessCase.UC22.Data

end
