module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Fpf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1Om4Fpf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Ctx
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c11_v1_kappa_ker5 {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (w : Vtil V₀ V hV)
    (hw : s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV (s15_Infra_le_v1Sub D.M V₀ V hV L) w = 1) :
    w ∈ fixV (barSub V₀ V hV L) := by
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV w
  have hx : x.val ∈ v1Sub D.M V₀ V hV L := by
    have h1 : mkTil (v1Sub D.M V₀ V hV L) V hV x = 1 := hw
    exact (QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M V₀ V hV L) V hV) x).1 h1
  have hmem : mkTil V₀ V hV x ∈ imgTil V₀ V hV (v1Sub D.M V₀ V hV L) :=
    (mem_imgTil V₀ V hV _ _).2 ⟨x, hx, rfl⟩
  have hfix := s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
  simpa only [conjSubgroup_one] using hfix hmem

theorem s16c11_v1_eq_bot_of_case5 (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1) (h5 : Case168_5Star D ⊥ V hV L) :
    v1Sub D.M ⊥ V hV L = ⊥ := by
  have hcomm : commV (lBar ⊥ V hV L) = ⊤ := by
    rw [commV_eq_commSub]
    simpa [wTil, lBar] using wTil_eq_top_of_case163_2 hc.conc hs
  let kappa : Vtil ⊥ V hV →* vStar D.M ⊥ V hV L :=
    s15T7Kappa ⊥ (v1Sub D.M ⊥ V hV L) V hV (s15_Infra_le_v1Sub D.M ⊥ V hV L)
  have hW2 : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  obtain ⟨ρ, hρL, hρκ⟩ := s16e_two_kappa_equiv D h1217 hc.setting.hyp151 hV
  have hLX : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := s16e_two_lBar_le D hc.setting.hyp151 hV
  have hLX' : lStar D.M ⊥ V hV L ≤ Mbar D.M (v1Sub D.M ⊥ V hV L) V hV :=
    s16e_two_lStar_le D hc.setting.hyp151 hV
  let e₀ : ↥(lStar D.M ⊥ V hV L) →*
      ↥((lBar ⊥ V hV L).subgroupOf (Mbar D.M ⊥ V hV)) :=
    (ρ.symm.toMonoidHom.comp (Subgroup.inclusion hLX')).codRestrict
      ((lBar ⊥ V hV L).subgroupOf (Mbar D.M ⊥ V hV)) (fun y => by
        have hy : (Subgroup.inclusion hLX' y) ∈
            Subgroup.map ρ.toMonoidHom ((lBar ⊥ V hV L).subgroupOf (Mbar D.M ⊥ V hV)) := by
          rw [hρL]
          exact Subgroup.mem_subgroupOf.mpr y.2
        have hy' : ρ (ρ.symm (Subgroup.inclusion hLX' y)) ∈
            Subgroup.map ρ.toMonoidHom ((lBar ⊥ V hV L).subgroupOf (Mbar D.M ⊥ V hV)) := by
          simpa using hy
        exact (Subgroup.mem_map_iff_mem (MulEquiv.injective ρ)).1 hy')
  let e : ↥(lStar D.M ⊥ V hV L) →* ↥(lBar ⊥ V hV L) :=
    (Subgroup.subgroupOfEquivOfLe hLX).toMonoidHom.comp e₀
  have he₀ : Function.Surjective e₀ := by
    intro a
    have ha : ((a : ↥(Mbar D.M ⊥ V hV)) : MulAut (Vtil ⊥ V hV)) ∈ lBar ⊥ V hV L :=
      Subgroup.mem_subgroupOf.mp a.2
    have hb : ((ρ a : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)) :
        MulAut (vStar D.M ⊥ V hV L)) ∈ lStar D.M ⊥ V hV L := by
      have hmem : (ρ a) ∈
          Subgroup.map ρ.toMonoidHom ((lBar ⊥ V hV L).subgroupOf (Mbar D.M ⊥ V hV)) :=
        Subgroup.mem_map_of_mem ρ.toMonoidHom a.2
      rw [hρL] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    refine ⟨⟨(ρ a : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)), hb⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((ρ.symm (ρ a) : ↥(Mbar D.M ⊥ V hV)) : MulAut (Vtil ⊥ V hV)) =
      ((a : ↥(Mbar D.M ⊥ V hV)) : MulAut (Vtil ⊥ V hV))
    rw [MulEquiv.symm_apply_apply]
  have he : Function.Surjective e :=
    (Subgroup.subgroupOfEquivOfLe hLX).surjective.comp he₀
  have hκequiv : ∀ (b : ↥(lStar D.M ⊥ V hV L)) (w : Vtil ⊥ V hV),
      kappa ((e b : MulAut (Vtil ⊥ V hV)) w) =
        (b : MulAut (vStar D.M ⊥ V hV L)) (kappa w) := by
    intro b w
    have hb : ((e b : ↥(lBar ⊥ V hV L)) : MulAut (Vtil ⊥ V hV)) =
        ((ρ.symm (Subgroup.inclusion hLX' b) : ↥(Mbar D.M ⊥ V hV)) :
          MulAut (Vtil ⊥ V hV)) := rfl
    rw [hb]
    have h := hρκ (ρ.symm (Subgroup.inclusion hLX' b)) w
    have hρg : (ρ (ρ.symm (Subgroup.inclusion hLX' b)) :
        ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)) = Subgroup.inclusion hLX' b :=
      MulEquiv.apply_symm_apply ρ _
    rw [hρg] at h
    simpa [kappa] using h
  obtain ⟨t₁, ht₁, t₂, ht₂, ht₁₂, ht₁3, ht₂3, hfpf₁, hfpf₂, hgen⟩ :=
    s16c11_v1_natOmegaPlus_two_fpf_in (W := vStar D.M ⊥ V hV L)
      (H := lStar D.M ⊥ V hV L) h5.2.2.1
  have hkerbot : kappa.ker = ⊥ :=
    s16c11_v1_kernel_eq_bot_of_fpf (W := Vtil ⊥ V hV) (W' := vStar D.M ⊥ V hV L)
      (κ := kappa) (A := lBar ⊥ V hV L) (B := lStar D.M ⊥ V hV L) hW2 e he hκequiv
      (fun w hw => s16c11_v1_kappa_ker5 hc.setting.hyp151 hV w (by simpa [kappa] using hw))
      hcomm ht₁ ht₂ ht₁₂ (by decide) (by decide) ht₁3 ht₂3 hfpf₁ hfpf₂ hgen
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have hxV : x ∈ V := s15_Infra_v1Sub_le hc.setting.hyp16.hyp125 hV hx
  have hxker : kappa (mkTil ⊥ V hV ⟨x, hxV⟩) = 1 := by
    rw [show kappa (mkTil ⊥ V hV ⟨x, hxV⟩) =
        mkTil (v1Sub D.M ⊥ V hV L) V hV ⟨x, hxV⟩ from rfl]
    exact (QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M ⊥ V hV L) V hV)
      ⟨x, hxV⟩).2 hx
  have hmem : mkTil ⊥ V hV ⟨x, hxV⟩ ∈ kappa.ker := MonoidHom.mem_ker.mpr hxker
  rw [hkerbot, Subgroup.mem_bot] at hmem
  have hx1 : (⟨x, hxV⟩ : IntMod V hV) ∈ modNull ⊥ V hV :=
    (QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) ⟨x, hxV⟩).1 hmem
  have hxG : x ∈ (⊥ : Subgroup G) := (mem_modNull ⊥ V hV ⟨x, hxV⟩).1 hx1
  simpa using hxG

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
