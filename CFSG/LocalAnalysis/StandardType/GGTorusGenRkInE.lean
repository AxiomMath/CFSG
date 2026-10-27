module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private theorem conjN_eq_self_of_diag {d n : ℕ} {K : Type} [Field K]
    (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {t v : Fin d → K}
    (hDt : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (s : ↥(unitarySU 2 n K d))
    (hs : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) :
    conjN D hD s = s := by
  refine Subtype.ext ?_
  rw [coe_conjN]
  have hcomm : D * (s : GL (Fin d) K) = (s : GL (Fin d) K) * D := by
    refine Units.ext ?_
    simp only [Units.val_mul]
    rw [hDt, hs]
    exact Matrix.commute_diagonal t v
  rw [hcomm]
  group

private theorem normalizerMonoidHom_apply_coe {G : Type*} [Group G] (L : Subgroup G)
    (g : Subgroup.normalizer (L : Set G)) (l : L) :
    ((L.normalizerMonoidHom g l : L) : G) = (g : G) * (l : G) * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe L g l

theorem map_diag_pTorsion_mem_E
    {d n p : ℕ} {K : Type} [Field K]
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition p L' E I θ hE)
    {φ : ↥(unitarySU 2 n K d) →* L'}
    (hdiag : ∀ e : E, ∃ t : Fin d → K, ActsDiagU φ (L'.normalizerMonoidHom ⟨e, hE e.2⟩) t)
    (s : ↥(unitarySU 2 n K d))
    (hs : ∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v)
    (hsp : s ^ p = 1) :
    ((φ s : L') : M) ∈ E := by
  obtain ⟨v, hv⟩ := hs
  have hmem : ((φ s : L') : M) ∈ E ⊔ L' := Subgroup.mem_sup_right (φ s).2
  have hcent : ((φ s : L') : M) ∈ Subgroup.centralizer (E : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨t, D, hD, hDt, hact⟩ := hdiag ⟨e, he⟩
    have hconj := hact s
    rw [conjN_eq_self_of_diag D hD hDt s hv] at hconj
    have hcoe := normalizerMonoidHom_apply_coe L' ⟨e, hE he⟩ (φ s)
    have h1 : e * ((φ s : L') : M) * e⁻¹ = ((φ s : L') : M) := by
      rw [← hcoe, hconj]
    calc e * ((φ s : L') : M) = (e * ((φ s : L') : M) * e⁻¹) * e := by group
      _ = ((φ s : L') : M) * e := by rw [h1]
  have hpow : ((φ s : L') : M) ^ p = 1 := by
    have hpowL : (φ s) ^ p = 1 := by rw [← map_pow, hsp, map_one]
    calc ((φ s : L') : M) ^ p = (((φ s) ^ p : L') : M) :=
          (map_pow L'.subtype (φ s) p).symm
      _ = ((1 : L') : M) := by rw [hpowL]
      _ = 1 := map_one L'.subtype
  exact hpos.2.2.2.2.2.1 _ hmem hcent hpow

end CFSG.StandardType
