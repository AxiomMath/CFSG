module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourConj
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
public import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.Quasithin.SimsD1.FourBlocks

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {G₂ T M₂ R : Subgroup G}

theorem le_twoResidual_of_isShort2 {H L : Subgroup G} (hL : IsShort2 L) (hLH : L ≤ H) :
    L ≤ twoResidual H := by
  have hN : ((twoResidual H).subgroupOf L).Normal := ⟨fun x hx l => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H (hLH l.2)) x).mp hx⟩
  refine Subgroup.subgroupOf_eq_top.mp (hL.1 ((twoResidual H).subgroupOf L) ?_)
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H x (hLH x.2)
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simpa using hk

theorem le_normalizer_twoResidual_sup {H T R : Subgroup G} (hT : IsSylowTwoOf T H)
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) :
    H ≤ Subgroup.normalizer ((twoResidual H ⊔ R : Subgroup G) : Set G) := by
  refine (sup_twoResidual_eq hT).ge.trans (sup_le (fun t ht => ?_) ?_)
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_twoResidual H (hT.1 ht)),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTR ht)]
  · exact le_sup_left.trans Subgroup.le_normalizer

theorem cgsIn_le_inf {H T M R X : Subgroup G} (hmp : MinParabolic H T M) (hXH : X ≤ H)
    (hTR : T ≤ Subgroup.normalizer (R : Set G))
    (hno : ∀ C : Subgroup G, C ≤ R → C ≠ ⊥ → (C.subgroupOf R).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set G)) :
    cgsIn X R ≤ M ⊓ X := by
  refine iSup_le fun C => iSup_le fun hCR => iSup_le fun hC1 => iSup_le fun hCc => ?_
  have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
    hTR.trans (normalizer_le_normalizer_of_characteristic hCR hCc)
  have hlt : H ⊓ Subgroup.normalizer (C : Set G) < H :=
    lt_of_le_of_ne inf_le_left fun h => hno C hCR hC1 hCc (h.ge.trans inf_le_right)
  exact le_inf ((inf_le_inf_right _ hXH).trans (hmp.le_of_lt (le_inf hmp.isSylow.1 hTC) hlt))
    inf_le_left

theorem le_normalizer_iSup_a3Blocks {H : Subgroup G}
    (hfin : {L : Subgroup G | IsBlock2 H L ∧ IsAltType L 3}.Finite) :
    H ≤ Subgroup.normalizer ((⨆ L ∈ hfin.toFinset, L : Subgroup G) : Set G) := by
  have hmap : ∀ g ∈ H, (⨆ L ∈ hfin.toFinset, L).map (MulAut.conj g).toMonoidHom ≤
      ⨆ L ∈ hfin.toFinset, L := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨hLb, hLa⟩ := hfin.mem_toFinset.mp hL
    exact le_iSup₂ (f := fun L (_ : L ∈ hfin.toFinset) => L) _
      (hfin.mem_toFinset.mpr ⟨CFSG.Quasithin.IsBlock2.conjByElt_of_mem hLb hg,
        L238.IsAltType.map_equiv hLa (MulAut.conj g)⟩)
  exact fun g hg => B6.mem_normalizer_of_forall_mem (fun x hx => hmap g hg ⟨x, hx, rfl⟩)
    (fun x hx => by simpa using hmap g⁻¹ (H.inv_mem hg) ⟨x, hx, rfl⟩)

end CFSG.Quasithin.SimsD1.FourBlocks
