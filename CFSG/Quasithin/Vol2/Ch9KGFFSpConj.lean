module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3LatSix

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Setup.X7a
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem perfectCore_parabolic_conj {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P)
    {Pa : Subgroup S} (hpar : IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) :
    perfectCore Pa = ⊥ ∨ ∃ (g : S) (j : Fin 2),
      perfectCore Pa = (perfectCore (P j)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨-, S₁, hS₁, hN⟩ := hpar
  obtain ⟨g, hg⟩ := A5.G3.exists_conj_eq_of_isSylowTwoOf hU hS₁
  set c : S ≃* S := (MulAut.conj g).symm with hc
  set Pa' : Subgroup S := Pa.map c.toMonoidHom with hPa'
  have hS₁P : S₁ ≤ Pa := fun x hx => hN ⟨Subgroup.mem_top x, Subgroup.le_normalizer hx⟩
  have hUP : U ≤ Pa' := by
    intro u hu
    have hmem : (MulAut.conj g).toMonoidHom u ∈ S₁ := by
      rw [← hg]
      exact ⟨u, hu, rfl⟩
    refine ⟨(MulAut.conj g).toMonoidHom u, hS₁P hmem, ?_⟩
    simp [hc]
    group
  have hne' : Pa' ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map c.symm.toMonoidHom) htop
    rw [hPa', Subgroup.map_map] at this
    have h' : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id S := by
      ext x
      simp
    rw [h', Subgroup.map_id, Subgroup.map_top_of_surjective _ c.symm.surjective] at this
    exact this
  have hcore : (perfectCore Pa).map c.toMonoidHom = perfectCore Pa' :=
    map_perfectCore c.toMonoidHom Pa
  by_cases hs : Group.IsSolvable ↥Pa'
  · left
    have h1 : perfectCore Pa' = ⊥ := (isSolvable_iff_perfectCore_eq_bot Pa').mp hs
    rw [← hcore] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ c.injective).mp h1
  · right
    obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 Pa' hUP hne' hs
    have hj : perfectCore Pa' = perfectCore (P j) := by
      rw [← dInf_eq_perfectCore, ← dInf_eq_perfectCore, hd]
    refine ⟨g, j, ?_⟩
    rw [← hj, ← hcore, Subgroup.map_map]
    have h' : (MulAut.conj g).toMonoidHom.comp c.toMonoidHom = MonoidHom.id S := by
      ext x
      simp [hc]
    rw [h', Subgroup.map_id]

section Sp4

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def projEquiv : StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
  MulEquiv.ofBijective (proj 2 K) ⟨proj_injective_charTwo, proj_surjective⟩

theorem map_projEquiv_symm_proj (H : Subgroup (StatedSp 2 K)) :
    (H.map (proj 2 K)).map (projEquiv (K := K)).symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have h : (projEquiv (K := K)).symm.toMonoidHom.comp (proj 2 K) = MonoidHom.id _ :=
    MonoidHom.ext fun x => (projEquiv (K := K)).symm_apply_apply x
  rw [h, Subgroup.map_id]

variable [Finite K]

theorem sp4_residualOvergroupsAt (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    ResidualOvergroupsAt (StatedSp 2 K) (unipotent 2 K) (Q2 K) := by
  have hres : ResidualOvergroupsAt (StatedProj (StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) := symplectic_two_residualOvergroupsAt hK
  have h := hres.map (projEquiv (K := K)).symm
  have hU : (projUnipotent 2 K).map (projEquiv (K := K)).symm.toMonoidHom = unipotent 2 K :=
    map_projEquiv_symm_proj _
  have hP : (fun j : Fin 2 => ((Q2 K j).map (proj 2 K)).map
      (projEquiv (K := K)).symm.toMonoidHom) = Q2 K :=
    funext fun j => map_projEquiv_symm_proj _
  rw [hU, hP] at h
  exact h

theorem isSylowTwoOf_unipotent : IsSylowTwoOf (unipotent 2 K) (⊤ : Subgroup (StatedSp 2 K)) := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : IsSylowTwoOf (projUnipotent 2 K) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  have h := A312.isSylowTwoOf_top_map (projEquiv (K := K)).symm.toMonoidHom
    (projEquiv (K := K)).symm.surjective hU
  rwa [projUnipotent, map_projEquiv_symm_proj] at h

theorem sp4_perfectCore_parabolic_conj (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    {Pa : Subgroup (StatedSp 2 K)} (hpar : IsParabolic2 (⊤ : Subgroup (StatedSp 2 K)) Pa)
    (hne : Pa ≠ ⊤) :
    perfectCore Pa = ⊥ ∨ ∃ (g : StatedSp 2 K) (j : Fin 2),
      perfectCore Pa = (perfectCore (Q2 K j)).map (MulAut.conj g).toMonoidHom :=
  perfectCore_parabolic_conj isSylowTwoOf_unipotent (sp4_residualOvergroupsAt hK) hpar hne

end Sp4

end CFSG.Quasithin.H13.Ch9.KGFF
