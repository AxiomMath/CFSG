module

public import CFSG.LocalAnalysis.StandardType.GGPZCutsDefs
public import CFSG.LocalAnalysis.StandardType.GGPZRankTwo
public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGR4Forced

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLayerClosure_normalized {G : Type} [Group G] [Finite G] {p : ℕ} {Y J H : Subgroup G}
    (hHY : H ≤ Y) (hHJ : H ≤ Subgroup.normalizer (J : Set G)) :
    H ≤ Subgroup.normalizer (ggLayerClosure p Y J : Set G) := by
  have hN : ((CFSG.Open.lBalancePLayer p Y).subgroupOf Y).Normal :=
    lBalancePLayer_subgroupOf_normal p Y
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun a ha => ?_
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
  have haY : a ∈ Y := lBalancePLayer_le p Y ha
  have ha' : g * a * g⁻¹ ∈ CFSG.Open.lBalancePLayer p Y := by
    have h := hN.conj_mem ⟨a, haY⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨g, hHY hg⟩
    exact Subgroup.mem_subgroupOf.mp h
  have hJg : J.map (MulAut.conj g).toMonoidHom = J := map_conj_eq_of_mem_normalizer (hHJ hg)
  have hfun : (MulAut.conj g).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom =
      (MulAut.conj (g * a * g⁻¹)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext j
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  calc J.map ((MulAut.conj g).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom)
      = J.map ((MulAut.conj (g * a * g⁻¹)⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) := by
        rw [hfun]
    _ = (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * a * g⁻¹)⁻¹).toMonoidHom :=
        (Subgroup.map_map _ _ _).symm
    _ = J.map (MulAut.conj (g * a * g⁻¹)⁻¹).toMonoidHom := by rw [hJg]
    _ ≤ ggLayerClosure p Y J := le_iSup₂_of_le (g * a * g⁻¹) ha' le_rfl

theorem ggPZVertInput_of_pumpup (hPU : GGPumpupInput) : GGPZVertInput := by
  intro G _ _ p _ B Bs x L D J y K labJ labX X m z h
  have hrank : 2 ≤ labJ.rank := ggPZ_rank_two h
  obtain ⟨hH, -, -, -, -, -, -, -, -, hJcard, -, hzD, hzx, -⟩ := h
  have hI : GGThmIHyp p B x L := hH.1.1
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hInn : GGInnerDiagOn Bs L := hH.2.2.1.1
  have hpJ : p ∣ Nat.card ↥J := by
    have h1 : Nat.card ↥(Bs ⊓ J) ∣ Nat.card ↥J := Subgroup.card_dvd_of_le inf_le_right
    rw [hJcard] at h1
    exact (dvd_pow_self p (by omega)).trans h1
  have hD : D = Subgroup.closure {x, (z : G)} := eq_closure_pair_of_mem hI hDJ hzD hzx
  obtain ⟨hK, hJK, -, -⟩ := pumpup_of_stdSub hPU hI hDJ hpJ hD
  refine ⟨ggLayerClosure p (Subgroup.centralizer ({(z : G)} : Set G)) J, hK, hJK, ?_⟩
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) := ggR4_normalizes_J hH.1 hInn
  have hBsC : Bs ≤ Subgroup.centralizer ({(z : G)} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hH.1.2.1.2.1.1.is_comm.comm (⟨b, hb⟩ : ↥Bs) ⟨z, z.2⟩))
  exact ggLayerClosure_normalized hBsC hBsJ

end CFSG.StandardType

end
