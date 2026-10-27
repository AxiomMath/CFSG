module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggLayerClosure_isSubnormal_of_stdSub (hL : GGLBalanceInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G} (hI : GGThmIHyp p B x L)
    (hDJ : LargeEvenStdSub p B x L D J) (hpJ : p ∣ Nat.card J) {d : G}
    (hD : D = Subgroup.closure {x, d}) :
    IsSubnormal (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J)
      (Subgroup.centralizer ({d} : Set G)) := by
  have : IsSimpleGroup G := hI.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  obtain ⟨-, hxd, hd1, -⟩ := facts_of_closure_pair hI hDJ hD
  have hxX : x ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxd
  have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1
  have hJY := isComponentOf_inf_centralizer_of_stdSub hS hDJ.1 hD
  have hJE : J ≤ CFSG.Open.lBalancePLayer p
      (Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    le_sSup (lBalanceIsPComponent_of_isComponentOf hJY (not_le_lBalancePrimeCore_of_dvd hpJ))
  have hYX := lBalancePLayer_inf_centralizer_le_of_input hL hp
    (lBalanceIsKGroup_of_kProper hI.2.2.1
      (centralizer_singleton_ne_top_of_isSimpleGroup hI.2.1 hd1)) hxX hxp
  set P := CFSG.Open.lBalancePLayer p (Subgroup.centralizer ({d} : Set G))
  have hJP : J ≤ P := hJE.trans hYX
  have hKP : ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J ≤ P := by
    refine iSup₂_le fun a ha => Subgroup.map_le_iff_le_comap.mpr fun j hj => ?_
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact P.mul_mem (P.mul_mem (P.inv_mem ha) (hJP hj)) ha
  have hmap : ∀ g ∈ P, (ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J).map
      (MulAut.conj g).toMonoidHom ≤ ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J := by
    intro g hg
    rw [ggLayerClosure, Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    rw [Subgroup.map_map]
    refine le_iSup₂_of_le (f := fun (a : G) (_ : a ∈ P) => J.map (MulAut.conj a⁻¹).toMonoidHom)
      (a * g⁻¹) (P.mul_mem ha (P.inv_mem hg)) (le_of_eq ?_)
    congr 1
    ext z
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, mul_inv_rev, inv_inv]
    group
  have hnorm : ((ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J).subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKP]
    intro h g hh hg
    have hmem := hmap g hg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hh)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  exact IsSubnormal.step hKP hnorm (IsSubnormal.step (lBalancePLayer_le p _)
    (lBalancePLayer_subgroupOf_normal p _) (IsSubnormal.refl _))

end CFSG.StandardType

end
