module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcConj
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

section Tags

theorem ggRootCentralizerCyclicTag_F4 : GGRootCentralizerCyclicTag .F4 := by
  intro G _ _ n f ψ _ _ hker hC r hr Y hY hYd
  have hψ := AutSt.ker_eq_center hker hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hY hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .F4 γ := mem_adjDatum_roots.mp hγ
  have hcz : RootCentExc.CentTwoGen z := RootCentExc.centTwoGen_of_mem_rootGroup
    (K := GaloisField 2 f) _ (RootCentExc.centTwoGen_single_F4 _) hγ' hz hz1
  have hker' : (MonoidHom.id (ggU .F4 n f).K).ker = ψ.ker := by
    rw [MonoidHom.ker_id, hψ]
    exact (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).symm
  refine RootCentExc.exists_zpowers_sup_of_model (π := MonoidHom.id _) Function.surjective_id
    hker' (hcz.conj u) Y fun y hy => ?_
  obtain ⟨g, hg, hyg⟩ :=
    PsiDiag.Adj.exists_mem_centralizer_F4 (K := GaloisField 2 f) ψ hker (hYd y hy)
  exact Subgroup.mem_inf.mpr
    ⟨RootCentExc.mem_range_of_mul_mem_centralizer hC hg hyg, (hY hy).2⟩

theorem ggRootCentralizerCyclicTag_E8 : GGRootCentralizerCyclicTag .E8 := by
  intro G _ _ n f ψ _ _ hker hC r hr Y hY hYd
  have hψ := AutSt.ker_eq_center hker hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hY hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .E8 γ := mem_adjDatum_roots.mp hγ
  have hcz : RootCentExc.CentTwoGen z := RootCentExc.centTwoGen_of_mem_rootGroup
    (K := GaloisField 2 f) _ (RootCentExc.centTwoGen_single_E8 _) hγ' hz hz1
  have hker' : (MonoidHom.id (ggU .E8 n f).K).ker = ψ.ker := by
    rw [MonoidHom.ker_id, hψ]
    exact (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).symm
  refine RootCentExc.exists_zpowers_sup_of_model (π := MonoidHom.id _) Function.surjective_id
    hker' (hcz.conj u) Y fun y hy => ?_
  obtain ⟨g, hg, hyg⟩ :=
    PsiDiag.Adj.exists_mem_centralizer_E8 (K := GaloisField 2 f) ψ hker (hYd y hy)
  exact Subgroup.mem_inf.mpr
    ⟨RootCentExc.mem_range_of_mul_mem_centralizer hC hg hyg, (hY hy).2⟩

theorem RootCentExc.centTwoGen_e7Isogeny (K : Type) [Field K] [Finite K] [CharP K 2]
    {γ : Fin Tag.E7.rank → ℤ} (hγ : γ ∈ (e7Datum K).roots) {z : e7Data_valid.minGroup K}
    (hz : z ∈ (e7Datum K).rootGroup γ) (hz1 : e7Isogeny K z ≠ 1) :
    RootCentExc.CentTwoGen (e7Isogeny K z) := by
  have hγ' : IsRoot .E7 γ := e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 _ |>.mp hγ
  obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hz
  rw [e7Isogeny_xm] at hz1 ⊢
  exact RootCentExc.centTwoGen_of_mem_rootGroup _ (RootCentExc.centTwoGen_single_E7 _) hγ'
    (xPar_mem hγ' _) hz1

theorem ggRootCentralizerCyclicTag_E7 : GGRootCentralizerCyclicTag .E7 := by
  intro G _ _ n f ψ _ _ hker hC r hr Y hY hYd
  have hψ := AutSt.ker_eq_center hker hC
  have hπker : (e7Isogeny (GaloisField 2 f)).ker = ψ.ker :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e7Isogeny_ker_eq_center.trans hψ.symm
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hY hr2 ⊢
  have hz1 : e7Isogeny (GaloisField 2 f) z ≠ 1 := by
    intro h
    have hk : z ∈ ψ.ker := hπker ▸ (MonoidHom.mem_ker.mpr h)
    rw [MonoidHom.mem_ker] at hk
    rw [map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  have hcz := (RootCentExc.centTwoGen_e7Isogeny (GaloisField 2 f) hγ hz hz1).conj
    (e7Isogeny (GaloisField 2 f) u)
  have e : e7Isogeny (GaloisField 2 f) (u * z * u⁻¹) = e7Isogeny (GaloisField 2 f) u *
      e7Isogeny (GaloisField 2 f) z * (e7Isogeny (GaloisField 2 f) u)⁻¹ := by
    erw [map_mul, map_mul, map_inv]
  rw [← e] at hcz
  refine RootCentExc.exists_zpowers_sup_of_model (e7Isogeny_surjective _) hπker hcz Y
    fun y hy => ?_
  obtain ⟨g, hg, hyg⟩ :=
    PsiDiag.Minu.exists_mem_centralizer_E7 (k := GaloisField 2 f) ψ hker (hYd y hy)
  exact Subgroup.mem_inf.mpr
    ⟨RootCentExc.mem_range_of_mul_mem_centralizer hC hg hyg, (hY hy).2⟩

end Tags

end CFSG.StandardType
