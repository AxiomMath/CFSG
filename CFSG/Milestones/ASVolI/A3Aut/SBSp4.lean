module

public import CFSG.Milestones.ASVolI.A3Aut.SBL3

public section

namespace CFSG.ASVolI

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a

section Symplectic

variable {r : ℕ} {K : Type} [Field K]

theorem burnsideAut_pairRootElt_one_ne_one {a b : Fin r ⊕ Fin r} (hab : a ≠ b) :
    pairRootElt (K := K) hab 1 ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : StatedSp r K => ((g : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) a b) h
  simp only [coe_pairRootElt, pairRootMat_apply_self hab, Subgroup.coe_one, Units.val_one,
    Matrix.one_apply_ne hab] at h1
  exact one_ne_zero h1

theorem burnsideAut_transvection_zero_one_eq_sl2Up (c : K) :
    SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c = sl2Up K c :=
  Subtype.ext (burnsideAut_transvection_zero_one c)

theorem burnsideAut_transvection_one_zero_eq_sl2Low (c : K) :
    SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c = sl2Low K c :=
  Subtype.ext (burnsideAut_transvection_one_zero c)

theorem burnsideAut_sp_rankOne (k : Fin r) :
    ∃ ψ : SpecialLinearGroup (Fin 2) K →* StatedSp r K,
      (∀ c, ψ (sl2Up K c) ∈ rootSubgroup K (simpleRootVec r k)) ∧
      (∀ c, ψ (sl2Low K c) ∈ rootSubgroup K (-simpleRootVec r k)) ∧ ψ (sl2Up K 1) ≠ 1 := by
  by_cases h : (k : ℕ) + 1 < r
  · set k' : Fin r := ⟨k + 1, h⟩ with hk'
    have hkk' : k ≠ k' := fun e => by
      have := congrArg Fin.val e
      simp [k'] at this
    have hsnd : simpleSnd k = Sum.inl k' := by
      unfold simpleSnd
      rw [dif_pos h]
    have hroot : rootVec (Sum.inl k) (Sum.inl k') = simpleRootVec r k := by
      rw [← hsnd]
      exact rootVec_simpleSnd k
    refine ⟨SymplecticTorusWeyl.rho k k' hkk', fun c => ?_, fun c => ?_, ?_⟩
    · rw [← pairRootElt_short hkk' c, ← hroot]
      exact pairRootElt_mem_rootSubgroup _ c
    · rw [← pairRootElt_short' hkk' c, ← hroot, neg_rootVec]
      exact pairRootElt_mem_rootSubgroup _ c
    · rw [← pairRootElt_short hkk' 1]
      exact burnsideAut_pairRootElt_one_ne_one _
  · have hsnd : simpleSnd k = Sum.inr k := by
      unfold simpleSnd
      rw [dif_neg h]
    have hroot : rootVec (Sum.inl k) (Sum.inr k) = simpleRootVec r k := by
      rw [← hsnd]
      exact rootVec_simpleSnd k
    refine ⟨SymplecticTorusWeyl.lam k, fun c => ?_, fun c => ?_, ?_⟩
    · rw [← pairRootElt_long k c, ← hroot]
      exact pairRootElt_mem_rootSubgroup _ c
    · rw [← pairRootElt_long' k c, ← hroot, neg_rootVec]
      exact pairRootElt_mem_rootSubgroup _ c
    · rw [← pairRootElt_long k 1]
      exact burnsideAut_pairRootElt_one_ne_one _

theorem burnsideAut_sp_not_isSolvable_of_weylRep_mem [Finite K] (hK : 4 ≤ Nat.card K)
    {A : Subgroup (StatedSp r K)} (hU : SymplecticFlag.unipotent r K ≤ A) {k : Fin r}
    (hn : weylRep K k ∈ A) : ¬ Group.IsSolvable ↥A := by
  obtain ⟨ψ, hup, hlow, hψ1⟩ := burnsideAut_sp_rankOne (K := K) k
  have hspw : spWeylGroup K k ≤ A :=
    sup_le hU ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hn))
  have hpos : rootSubgroup K (simpleRootVec r k) ≤ A :=
    (CFSG.QuasithinUnique.Setup.X7a.rootSubgroup_le_unipotent
      (simpleRootVec_mem_posRoots k)).trans hU
  have hneg : rootSubgroup K (-simpleRootVec r k) ≤ A :=
    (rootSubgroup_neg_le_spWeylGroup k).trans hspw
  have hrange : ψ.range ≤ A := by
    rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2)
      (K := K), MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨a, b, hab, c, rfl⟩, rfl⟩
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · change ψ (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c) ∈ A
      rw [burnsideAut_transvection_zero_one_eq_sl2Up]
      exact hpos (hup c)
    · change ψ (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c) ∈ A
      rw [burnsideAut_transvection_one_zero_eq_sl2Low]
      exact hneg (hlow c)
    · exact absurd rfl hab
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  exact burnsideAut_not_isSolvable_of_perfect_hom ψ hψ1 hrange

theorem burnsideAut_sp4_solvable_le [Finite K] (hK : 4 ≤ Nat.card K)
    {M : Subgroup (StatedSp 2 K)} (hU : SymplecticFlag.unipotent 2 K ≤ M)
    (hM : Group.IsSolvable ↥M) : M ≤ SymplecticFlag.borelSubgroup 2 K := by
  have hcuts : borelCuts K M = {1, 2} := by
    ext i
    constructor
    · rintro ⟨k, rfl, -⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      have := k.isLt
      omega
    · intro hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      have hk : i - 1 < 2 := by omega
      have hi' : ((⟨i - 1, hk⟩ : Fin 2) : ℕ) + 1 = i := by simp only; omega
      rw [← hi']
      exact (succ_mem_borelCuts_iff M _).2 fun hn =>
        burnsideAut_sp_not_isSolvable_of_weylRep_mem hK hU hn hM
  have hle := ((symplectic_unitriangular_overgroup_subflag_containment (r := 2) (K := K)).1 M hU).1
  rwa [hcuts, ← borelSubgroup_eq_flagStabilizer] at hle

theorem burnsideAut_sp_borel_le_normalizer :
    SymplecticFlag.borelSubgroup r K ≤
      Subgroup.normalizer (SymplecticFlag.unipotent r K : Set (StatedSp r K)) := by
  have hN : ((SymplecticFlag.unipotent r K).subgroupOf (SymplecticFlag.borelSubgroup r K)).Normal := by
    rw [← SymplecticFlag.ker_diagHom]
    infer_instance
  refine Subgroup.le_normalizer_iff.2 fun b hb u hu => ?_
  have h1 := hN.conj_mem ⟨u, SymplecticFlag.unipotent_le_borelSubgroup hu⟩
    (Subgroup.mem_subgroupOf.2 hu) ⟨b, hb⟩
  exact Subgroup.mem_subgroupOf.1 h1

theorem burnsideAut_solvBorel_projSp4 [Finite K] (hK : 4 ≤ Nat.card K) :
    burnsideAut_SolvBorel (StatedProj (StatedSp 2 K)) (SymplecticFlag.projUnipotent 2 K) := by
  refine burnsideAut_solvBorel_of_comap (SymplecticFlag.proj 2 K) proj_surjective ?_
    burnsideAut_sp_borel_le_normalizer (fun Y hUY hY => burnsideAut_sp4_solvable_le hK hUY hY)
  intro a ha b hb
  rw [ker_proj] at ha hb
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 ha
  obtain ⟨d, hd⟩ := Subgroup.mem_subgroupOf.1 hb
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc, ← hd, ← map_mul, ← map_mul, mul_comm]

end Symplectic

theorem burnsideAut_solvBorel_Sp4 :
    ∀ (X : Type) [Group X] [Finite X] (f : ℕ), 2 ≤ f → CFSG.Quasithin.IsPSp4 2 f X →
      ∀ S : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ → burnsideAut_SolvBorel X S := by
  intro X _ _ f hf hX S hS
  obtain ⟨K, _, _, _, φ, hK, hφS, -, -⟩ := even_rank_two_residual_symplectic hX hS
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine burnsideAut_solvBorel_of_mulEquiv φ ?_
  rw [hφS]
  exact burnsideAut_solvBorel_projSp4 hK4

end CFSG.ASVolI
