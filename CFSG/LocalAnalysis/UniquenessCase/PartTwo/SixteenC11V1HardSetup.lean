module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Ctx
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c11_v1_kappa_ker_le_fixV (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (w : Vtil V₀ V hV)
    (hw : s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV (s15_Infra_le_v1Sub D.M V₀ V hV L) w = 1) :
    w ∈ fixV (lBar V₀ V hV L) := by
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV w
  have hx : x.val ∈ v1Sub D.M V₀ V hV L := by
    have h1 : mkTil (v1Sub D.M V₀ V hV L) V hV x = 1 := hw
    exact (QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M V₀ V hV L) V hV) x).1 h1
  have hmem : mkTil V₀ V hV x ∈ imgTil V₀ V hV (v1Sub D.M V₀ V hV L) :=
    (mem_imgTil V₀ V hV _ _).2 ⟨x, hx, rfl⟩
  have hfix := s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
  simpa only [conjSubgroup_one, lBar] using hfix hmem

theorem s16c11_v1_setup_data (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M ⊥ V hV L)} (hF : s16e_two_Fam D ⊥ V L hV P) :
    ∃ (κ : Vtil ⊥ V hV →* vStar D.M ⊥ V hV L)
      (e : ↥(lStar D.M ⊥ V hV L) →* ↥(lBar ⊥ V hV L))
      (I₀ I₁ : Subgroup (vStar D.M ⊥ V hV L)),
      Function.Surjective κ ∧ Function.Surjective e ∧
      (∀ (b : ↥(lStar D.M ⊥ V hV L)) (w : Vtil ⊥ V hV),
        κ ((e b : MulAut (Vtil ⊥ V hV)) w) = (b : MulAut (vStar D.M ⊥ V hV L)) (κ w)) ∧
      (∀ w : Vtil ⊥ V hV, κ w = 1 → w ∈ fixV (lBar ⊥ V hV L)) ∧
      commV (lBar ⊥ V hV L) = ⊤ ∧ fixV (lStar D.M ⊥ V hV L) = ⊥ ∧
      (κ.ker = ⊥ → v1Sub D.M ⊥ V hV L = ⊥) ∧
      I₀ ⊓ I₁ = ⊥ ∧ I₀ ⊔ I₁ = ⊤ ∧ P (lStar D.M ⊥ V hV L) I₀ ⊥ ∧
      P (lStar D.M ⊥ V hV L) I₁ ⊥ ∧ IsIrrOn (lStar D.M ⊥ V hV L) I₀ ⊥ ∧
      IsIrrOn (lStar D.M ⊥ V hV L) I₁ ⊥ := by
  have hcomm : commV (lBar ⊥ V hV L) = ⊤ := by
    rw [commV_eq_commSub]
    simpa [wTil, lBar] using wTil_eq_top_of_case163_2 hc.conc hs
  have hwtop : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hc.setting.hyp151 hV hc.ne_bot hs
  obtain ⟨I₀, I₁, hN₀, hN₁, hinf, hsup⟩ := by
    have hsum : SumOfNat P (lStar D.M ⊥ V hV L) ⊤ ⊥ 2 := by
      have h := hF.sum
      rwa [hwtop] at h
    exact s16c167_sumOfNat_two hsum
  let kappa : Vtil ⊥ V hV →* vStar D.M ⊥ V hV L :=
    s15T7Kappa ⊥ (v1Sub D.M ⊥ V hV L) V hV (s15_Infra_le_v1Sub D.M ⊥ V hV L)
  have hκsurj : Function.Surjective kappa :=
    s15_T7_kappa_surjective ⊥ (v1Sub D.M ⊥ V hV L) V hV (s15_Infra_le_v1Sub D.M ⊥ V hV L)
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
  have hkerfix : ∀ w : Vtil ⊥ V hV, kappa w = 1 → w ∈ fixV (lBar ⊥ V hV L) :=
    fun w hw => s16c11_v1_kappa_ker_le_fixV D hc.setting.hyp151 hV w (by simpa [kappa] using hw)
  have hfix : fixV (lStar D.M ⊥ V hV L) = ⊥ :=
    s16c167_fixV_eq_bot_of_two (hF.natFacts.irr I₀ hN₀).2.2.1 (hF.natFacts.irr I₁ hN₁).2.2.1
      (hF.natFacts.fixV_inf I₀ hN₀) (hF.natFacts.fixV_inf I₁ hN₁) hinf hsup
  have hirr₀ : IsIrrOn (lStar D.M ⊥ V hV L) I₀ ⊥ := by
    have h := (hF.natFacts.irr I₀ hN₀).2
    rw [hF.natFacts.fixV_inf I₀ hN₀] at h
    exact h
  have hirr₁ : IsIrrOn (lStar D.M ⊥ V hV L) I₁ ⊥ := by
    have h := (hF.natFacts.irr I₁ hN₁).2
    rw [hF.natFacts.fixV_inf I₁ hN₁] at h
    exact h
  have hv1 : kappa.ker = ⊥ → v1Sub D.M ⊥ V hV L = ⊥ := fun hkerbot => by
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
  exact ⟨kappa, e, I₀, I₁, hκsurj, he, hκequiv, hkerfix, hcomm, hfix, hv1, hinf, hsup,
    hN₀, hN₁, hirr₀, hirr₁⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
