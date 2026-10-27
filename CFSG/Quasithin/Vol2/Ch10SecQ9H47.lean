module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherIncidenceGraph
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSubspaceIndex
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {K : Type} [Field K]

theorem one_le_finrank_le_two {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (h0 : W ≠ ⊥)
    (hW : IsTotallyIsotropic (pairedSympForm K 2) W) : 1 ≤ finrank K W ∧ finrank K W ≤ 2 :=
  ⟨Nat.pos_of_ne_zero fun h => h0 (Submodule.finrank_eq_zero.mp h),
    finrank_le_of_isTotallyIsotropic pairedSympForm_isAlt
      SymplecticFlag.pairedSympForm_nondegenerate finrank_standard hW⟩

theorem exists_map_projStabilizer [Finite K] (α : MulAut (StatedProj (StatedSp 2 K)))
    {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (h0 : W ≠ ⊥)
    (hW : IsTotallyIsotropic (pairedSympForm K 2) W) :
    ∃ W' : Submodule K (Fin 2 ⊕ Fin 2 → K), W' ≠ ⊥ ∧
      IsTotallyIsotropic (pairedSympForm K 2) W' ∧
        (projStabilizer 2 K W).map α.toMonoidHom = projStabilizer 2 K W' := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨hM, -, -⟩ := maximal_parabolics (K := K) (r := 2) p (by omega)
  have hmem : projStabilizer 2 K W ∈ spMaximalParabolics 2 K p := by
    rw [hM]
    exact ⟨W, h0, hW, rfl⟩
  have h : (projStabilizer 2 K W).map α.toMonoidHom ∈ spMaximalParabolics 2 K p :=
    LinearFlag.map_mem_maximalParabolics α hmem
  rw [hM] at h
  obtain ⟨W', h0', hW', heq⟩ := h
  exact ⟨W', h0', hW', heq⟩

theorem map_map_conj {G : Type*} [Group G] (α : MulAut G) (x : G) (H : Subgroup G) :
    (H.map (MulAut.conj x).toMonoidHom).map α.toMonoidHom =
      (H.map α.toMonoidHom).map (MulAut.conj (α x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext h
  simp [map_mul, map_inv]

theorem exists_map_projStabilizer_of_finrank [Finite K] (α : MulAut (StatedProj (StatedSp 2 K)))
    {W₁ W₂ W₁' : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hW₁ : IsTotallyIsotropic (pairedSympForm K 2) W₁)
    (hW₂ : IsTotallyIsotropic (pairedSympForm K 2) W₂) (hd : finrank K W₁ = finrank K W₂)
    (hW₁' : IsTotallyIsotropic (pairedSympForm K 2) W₁') (h0' : W₁' ≠ ⊥)
    (h : (projStabilizer 2 K W₁).map α.toMonoidHom = projStabilizer 2 K W₁') :
    ∃ W₂' : Submodule K (Fin 2 ⊕ Fin 2 → K), W₂' ≠ ⊥ ∧
      IsTotallyIsotropic (pairedSympForm K 2) W₂' ∧ finrank K W₂' = finrank K W₁' ∧
        (projStabilizer 2 K W₂).map α.toMonoidHom = projStabilizer 2 K W₂' := by
  obtain ⟨g, hg⟩ := exists_statedSp_map_eq hW₁ hW₂ hd
  obtain ⟨h', hh'⟩ := proj_surjective (r := 2) (K := K) (α (proj 2 K g))
  have hfr : finrank K (W₁'.map (spAct h')) = finrank K W₁' := finrank_map_spAct h' W₁'
  refine ⟨W₁'.map (spAct h'), fun hbot => h0' ?_, isTotallyIsotropic_map_spAct h' hW₁', hfr, ?_⟩
  · rw [hbot, finrank_bot] at hfr
    exact Submodule.finrank_eq_zero.mp hfr.symm
  · have hg' : W₂ = W₁.map (spAct g) := hg.symm
    rw [hg', projStabilizer_map_spAct, map_map_conj, h, ← hh', ← projStabilizer_map_spAct]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
