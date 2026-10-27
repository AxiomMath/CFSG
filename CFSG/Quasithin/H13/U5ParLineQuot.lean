module

public import CFSG.Quasithin.H13.U5ParLine
public import CFSG.Quasithin.H13.U5ParLineCoord
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316B
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.U5Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Quasithin (perfectCore)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem sup_le_u5LnStab : Ssub h ⊔ N₁sub h ≤ u5LnStab h := by
  rw [u5LnStab_eq_sup h]
  exact le_sup_left

@[expose] noncomputable def lnSL : ↥(Ssub h ⊔ N₁sub h) →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨blkA (mat (g : hypSU h 2 1)), det_blkA_eq_one_of_mem_sup h g.2⟩
  map_one' := by
    apply Subtype.ext
    change blkA (mat (1 : hypSU h 2 1)) = 1
    rw [mat_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkA]
  map_mul' g g' := by
    apply Subtype.ext
    change blkA (mat ((g * g' : ↥(Ssub h ⊔ N₁sub h)) : hypSU h 2 1)) =
      blkA (mat (g : hypSU h 2 1)) * blkA (mat (g' : hypSU h 2 1))
    have hle : Ssub h ⊔ N₁sub h ≤ u5LnStab h := sup_le_u5LnStab h
    have h := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K))
      (map_mul (lnBlk h) ⟨(g : hypSU h 2 1), hle g.2⟩ ⟨(g' : hypSU h 2 1), hle g'.2⟩)
    simpa [lnBlk_coe] using h

theorem lnSL_coe (g : ↥(Ssub h ⊔ N₁sub h)) :
    ((lnSL h g : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blkA (mat (g : hypSU h 2 1)) :=
  rfl

theorem lnSL_surjective : Function.Surjective (lnSL h) := by
  intro A
  have hA : IsUnit (A : Matrix (Fin 2) (Fin 2) K).det := by simp
  have hmem : lev (hK := h) (A : Matrix (Fin 2) (Fin 2) K) hA ∈ Ssub h ⊔ N₁sub h :=
    Subgroup.mem_sup_right ⟨A, (lev_eq_leviSU A hA).symm⟩
  refine ⟨⟨lev (hK := h) (A : Matrix (Fin 2) (Fin 2) K) hA, hmem⟩, ?_⟩
  apply Subtype.ext
  rw [lnSL_coe, mat_lev]
  rfl

theorem lnSL_eq_one_iff (g : ↥(Ssub h ⊔ N₁sub h)) :
    lnSL h g = 1 ↔ (g : hypSU h 2 1) ∈ Ssub h := by
  have hle : Ssub h ⊔ N₁sub h ≤ u5LnStab h := sup_le_u5LnStab h
  constructor
  · intro hg
    apply (lnBlk_eq_one_iff (h := h) ⟨(g : hypSU h 2 1), hle g.2⟩).1
    apply Units.ext
    simpa [lnBlk_coe, lnSL_coe] using congrArg Subtype.val hg
  · intro hg
    apply Subtype.ext
    have hln := (lnBlk_eq_one_iff (h := h) ⟨(g : hypSU h 2 1), hle g.2⟩).2 hg
    have h' := congrArg (fun u : GL (Fin 2) K => (u : Matrix (Fin 2) (Fin 2) K)) hln
    simpa [lnBlk_coe, lnSL_coe] using h'

@[expose] noncomputable def perfHom (hf : 2 ≤ f) :
    ↥(Ssub h ⊔ N₁sub h) →* ↥(perfectCore (u5LnP h)) where
  toFun g := ⟨hypProj h 2 1 (g : hypSU h 2 1), by
    rw [perfectCore_u5LnP h hf]
    exact Subgroup.mem_map_of_mem _ g.2⟩
  map_one' := by
    apply Subtype.ext
    show hypProj h 2 1 ((1 : ↥(Ssub h ⊔ N₁sub h)) : hypSU h 2 1) = 1
    rw [Subgroup.coe_one, map_one]
  map_mul' g g' := by
    apply Subtype.ext
    show hypProj h 2 1 ((g * g' : ↥(Ssub h ⊔ N₁sub h)) : hypSU h 2 1) =
      hypProj h 2 1 (g : hypSU h 2 1) * hypProj h 2 1 (g' : hypSU h 2 1)
    rw [Subgroup.coe_mul, map_mul]

theorem perfHom_injective (hf : 2 ≤ f) : Function.Injective (perfHom h hf) := by
  intro g g' e
  have hπ : hypProj h 2 1 (g : hypSU h 2 1) = hypProj h 2 1 (g' : hypSU h 2 1) :=
    congrArg Subtype.val e
  have hker : (g : hypSU h 2 1)⁻¹ * (g' : hypSU h 2 1) ∈ hypScalars h 2 1 := by
    rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, hπ, inv_mul_cancel]
  have hsup : (g : hypSU h 2 1)⁻¹ * (g' : hypSU h 2 1) ∈ Ssub h ⊔ N₁sub h :=
    Subgroup.mul_mem _ ((Ssub h ⊔ N₁sub h).inv_mem g.2) g'.2
  have hbot : (g : hypSU h 2 1)⁻¹ * (g' : hypSU h 2 1) = 1 := by
    have hmem : (g : hypSU h 2 1)⁻¹ * (g' : hypSU h 2 1) ∈
        (Ssub h ⊔ N₁sub h) ⊓ hypScalars h 2 1 := ⟨hsup, hker⟩
    rwa [Ssub_sup_N₁sub_inf_hypScalars h, Subgroup.mem_bot] at hmem
  exact Subtype.ext (inv_mul_eq_one.1 hbot)

theorem perfHom_surjective (hf : 2 ≤ f) : Function.Surjective (perfHom h hf) := by
  intro x
  have hx : (x : hypPSU h 2 1) ∈ (Ssub h ⊔ N₁sub h).map (hypProj h 2 1) := by
    rw [← perfectCore_u5LnP h hf]
    exact x.2
  obtain ⟨g, hg, hgx⟩ := hx
  exact ⟨⟨g, hg⟩, Subtype.ext hgx⟩

@[expose] noncomputable def perfEquiv (hf : 2 ≤ f) :
    ↥(Ssub h ⊔ N₁sub h) ≃* ↥(perfectCore (u5LnP h)) :=
  MulEquiv.ofBijective (perfHom h hf) ⟨perfHom_injective h hf, perfHom_surjective h hf⟩

theorem perfEquiv_apply (hf : 2 ≤ f) (g : ↥(Ssub h ⊔ N₁sub h)) :
    ((perfEquiv h hf g : ↥(perfectCore (u5LnP h))) : hypPSU h 2 1) =
      hypProj h 2 1 (g : hypSU h 2 1) := by
  simpa [perfEquiv, perfHom] using
    MulEquiv.ofBijective_apply (perfHom h hf)
      ⟨perfHom_injective h hf, perfHom_surjective h hf⟩ g

private noncomputable def alpha (hf : 2 ≤ f) :
    ↥(perfectCore (u5LnP h)) →* Matrix.SpecialLinearGroup (Fin 2) K :=
  (lnSL h).comp (perfEquiv h hf).symm.toMonoidHom

private theorem alpha_surjective (hf : 2 ≤ f) : Function.Surjective (alpha h hf) := by
  intro A
  obtain ⟨g, hg⟩ := lnSL_surjective h A
  refine ⟨perfEquiv h hf g, ?_⟩
  change lnSL h ((perfEquiv h hf).symm (perfEquiv h hf g)) = A
  rw [MulEquiv.symm_apply_apply]
  exact hg

private theorem alpha_ker (hf : 2 ≤ f) :
    (alpha h hf).ker = CFSG.pCore 2 ↥(perfectCore (u5LnP h)) := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hxS : ((perfEquiv h hf).symm x : hypSU h 2 1) ∈ Ssub h :=
      (lnSL_eq_one_iff h _).1 hx
    rw [← mem_openPCoreOf_iff x, pCoreOf_perfectCore_u5LnP h hf]
    have hxeq : (x : hypPSU h 2 1) = hypProj h 2 1 ((perfEquiv h hf).symm x : hypSU h 2 1) := by
      have h := perfEquiv_apply h hf ((perfEquiv h hf).symm x)
      rwa [MulEquiv.apply_symm_apply] at h
    rw [hxeq]
    exact Subgroup.mem_map_of_mem _ hxS
  · intro hx
    have hxpo : (x : hypPSU h 2 1) ∈ CFSG.Open.pCoreOf 2 (perfectCore (u5LnP h)) :=
      (mem_openPCoreOf_iff x).2 hx
    rw [pCoreOf_perfectCore_u5LnP h hf] at hxpo
    obtain ⟨s, hsS, hπs⟩ := hxpo
    have hxR : (x : hypPSU h 2 1) ∈ (Ssub h ⊔ N₁sub h).map (hypProj h 2 1) := by
      rw [← perfectCore_u5LnP h hf]
      exact x.2
    obtain ⟨g, hgP, hπg⟩ := hxR
    have hfg : perfEquiv h hf ⟨g, hgP⟩ = x := Subtype.ext hπg
    have hsym : (perfEquiv h hf).symm x = ⟨g, hgP⟩ := by
      rw [← hfg]
      exact MulEquiv.symm_apply_apply _ _
    have hker : g⁻¹ * s ∈ hypScalars h 2 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, hπg, hπs, inv_mul_cancel]
    have hsup : g⁻¹ * s ∈ Ssub h ⊔ N₁sub h :=
      Subgroup.mul_mem _ ((Ssub h ⊔ N₁sub h).inv_mem hgP) (Subgroup.mem_sup_left hsS)
    have hbot : g⁻¹ * s = 1 := by
      have hmem : g⁻¹ * s ∈ (Ssub h ⊔ N₁sub h) ⊓ hypScalars h 2 1 := ⟨hsup, hker⟩
      rwa [Ssub_sup_N₁sub_inf_hypScalars h, Subgroup.mem_bot] at hmem
    have hgS : g ∈ Ssub h := by
      have hgs : g = s := inv_mul_eq_one.1 hbot
      rwa [hgs]
    change lnSL h ((perfEquiv h hf).symm x) = 1
    rw [hsym]
    exact (lnSL_eq_one_iff h ⟨g, hgP⟩).2 hgS

theorem isPSL_modO2_perfectCore_u5LnP (hf : 2 ≤ f) :
    CFSG.Quasithin.IsPSL 2 2 (2 * f) (CFSG.Quasithin.ModO2 (perfectCore (u5LnP h))) := by
  haveI : Finite K := h.finite
  haveI : CharP K 2 := h.charP
  let e : CFSG.Quasithin.ModO2 (perfectCore (u5LnP h)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq (alpha_ker h hf).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (alpha h hf) (alpha_surjective h hf))
  have hn : 2 ≤ 2 * f := by omega
  exact CFSG.Quasithin.H13.L3316.isPSL2_of_equiv_sl2 hn h.card e

theorem isSimpleGroup_modO2_perfectCore_u5LnP (hf : 2 ≤ f) :
    IsSimpleGroup (CFSG.Quasithin.ModO2 (perfectCore (u5LnP h))) :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 (2 * f)
    (isPSL_modO2_perfectCore_u5LnP h hf)).2

end CFSG.Quasithin.H13.U5Par

end
