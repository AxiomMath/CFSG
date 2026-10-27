module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CRed2
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec12.Hering129Setup
import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofHJL0
import CFSG.RankThree.PartTwo.Sec11.Item116R1Quot
public import CFSG.RankThree.PartTwo.Sec12.Hering129CDefs
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129C

section Assembly

variable {G : Type} [Group G] [Finite G] {A L K S : Subgroup G} {c b a : G}

theorem sectionFourHyp_quot (h1 : Sec4.Item4_1LargePrime) (hG : TheoremFourHyp G) {x : G}
    (hx1 : x ≠ 1) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 x) :
    SectionFourHyp (Y ⧸ aschbacherSolvableCore 3 Y) := by
  obtain ⟨L', hL', rfl⟩ := hY
  have hS4 : SectionFourHyp (Subgroup.centralizer ({x} : Set G)) :=
    hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG hx1)
  exact Sec4.Census.sectionFourHyp_of_mulEquiv
    (Sec13.thetaQuotEquivSub (Subgroup.centralizer ({x} : Set G)) L')
    (Sec4.Item41Narrow.sectionFourHyp_thetaQuotient h1 hS4 hL')

theorem L_eq_sup (cfg : Cfg129 G A c L b a K S) :
    L = resI L b ⊔ inSubgroup (aschbacherSolvableCore 3) L :=
  Proof128.eq_residual_sup_theta
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt cfg.std.mem_thetaComponentsAt).1 (k := 1)
    (by simpa using b_pow cfg) cfg.hb.2

theorem phiI_surjective_cfg (cfg : Cfg129 G A c L b a K S) : Function.Surjective (phiI L b) :=
  phiI_surjective (L_eq_sup cfg)

theorem ker_le_cfg (cfg : Cfg129 G A c L b a K S) :
    (psiI L K b (hIK_cfg cfg)).ker ≤ (phiI L b).ker :=
  ker_psiI_le_ker_phiI (hIK_cfg cfg)
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt cfg.std.mem_thetaComponentsAt)
    (card_center_eq_three_of_list cfg.list) (phiI_surjective_cfg cfg)

@[expose] noncomputable def fCfg (cfg : Cfg129 G A c L b a K S) :
    ↥(Ibar L K b (hIK_cfg cfg)) →* L ⧸ aschbacherSolvableCore 3 L :=
  fI (hIK_cfg cfg) (ker_le_cfg cfg)

theorem fCfg_surjective (cfg : Cfg129 G A c L b a K S) : Function.Surjective (fCfg cfg) := by
  intro q
  obtain ⟨x, hx⟩ := phiI_surjective_cfg cfg q
  exact ⟨(psiI L K b (hIK_cfg cfg)).rangeRestrict x, by rw [fCfg, fI_apply]; exact hx⟩

theorem ker_fCfg (cfg : Cfg129 G A c L b a K S) :
    Group.IsSolvable (fCfg cfg).ker ∧ ¬ 3 ∣ Nat.card (fCfg cfg).ker := by
  obtain ⟨hθs, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  set φ := phiI L b with hφ
  set r := (psiI L K b (hIK_cfg cfg)).rangeRestrict with hr
  let g : ↥φ.ker →* ↥L := (Subgroup.inclusion (resI_le_L L b)).comp φ.ker.subtype
  have hg : Function.Injective g :=
    (Subgroup.inclusion_injective (resI_le_L L b)).comp φ.ker.subtype_injective
  have hgθ : ∀ x : ↥φ.ker, g x ∈ aschbacherSolvableCore 3 ↥L := fun x =>
    (QuotientGroup.eq_one_iff _).mp x.2
  let j : ↥φ.ker →* ↥(aschbacherSolvableCore 3 ↥L) := g.codRestrict _ hgθ
  have hj : Function.Injective j := fun x y h => hg (congrArg Subtype.val h)
  haveI : Group.IsSolvable ↥(aschbacherSolvableCore 3 ↥L) := hθs
  haveI : Group.IsSolvable ↥φ.ker := Group.isSolvable_of_isSolvable_injective hj
  have hcardφ : Nat.card φ.ker ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    Subgroup.card_dvd_of_injective j hj
  let h : ↥φ.ker →* ↥(fCfg cfg).ker := (r.comp φ.ker.subtype).codRestrict _ (fun x => by
    show fCfg cfg (r x) = 1
    rw [fCfg, fI_apply]
    exact x.2)
  have hh : Function.Surjective h := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (psiI L K b (hIK_cfg cfg)).rangeRestrict_surjective y
    refine ⟨⟨x, ?_⟩, rfl⟩
    have : fCfg cfg (r x) = 1 := hy
    rwa [fCfg, fI_apply] at this
  refine ⟨Group.isSolvable_of_surjective hh, fun h3 => hθ3 ?_⟩
  exact h3.trans ((Subgroup.card_dvd_of_surjective hh).trans hcardφ)

theorem isList46_of_cfg (h46 : Sec4.Item4_6) (cfg : Cfg129 G A c L b a K S) :
    Sec4.IsList46 (K ⧸ aschbacherSolvableCore 3 K) := by
  obtain ⟨-, -, -, hb1, -⟩ := cfg.point_facts
  exact Sec21.Item223PrintProof.isList46_of_mem_thetaComponentsAt h46 cfg.std.toTheoremFourHyp
    (b_pow cfg) hb1 cfg.hK

theorem census129_of_cfg (h1 : Sec4.Item4_1LargePrime) (h125 : Item125BarC9)
    (cfg : Cfg129 G A c L b a K S) :
    Census129 (Lb := L ⧸ aschbacherSolvableCore 3 L) (barK K c (c_mem_K cfg))
      (barK K a (a_mem_K cfg)) (Ibar L K b (hIK_cfg cfg)) (Xbar A K) (fCfg cfg) := by
  obtain ⟨hbA, haA, haL, hb1, ha1, -⟩ := cfg.point_facts
  have hcK := c_mem_K cfg
  have haK := a_mem_K cfg
  have hIK := hIK_cfg cfg
  have hcomm : a * c = c * a := comm_A cfg (a_mem_A cfg) cfg.std.mem_A
  have hĀab : CFSG.Assembly.IsElemAbelian 3
      (Subgroup.zpowers (barK K a haK) ⊔ Subgroup.zpowers (barK K c hcK)) := by
    refine isElemAbelian_zpowers_sup_three ?_ ?_ ?_
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_barK_eq_three haK (a_pow cfg) ha1]
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_barK_eq_three hcK (c_pow cfg) cfg.std.ne_one]
    · show QuotientGroup.mk' _ _ * QuotientGroup.mk' _ _ = QuotientGroup.mk' _ _ *
        QuotientGroup.mk' _ _
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
  have hĀ9 : Nat.card (Subgroup.zpowers (barK K a haK) ⊔ Subgroup.zpowers (barK K c hcK) :
      Subgroup _) = 9 :=
    Proof128.card_zpowers_sup_eq_nine hĀab (x := barK K c hcK) (y := barK K a haK)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      (fun h => by
        have := orderOf_barK_eq_three hcK (c_pow cfg) cfg.std.ne_one
        rw [h, orderOf_one] at this
        omega)
      (fun h => by
        have := orderOf_barK_eq_three haK (a_pow cfg) ha1
        rw [h, orderOf_one] at this
        omega)
      (barK_not_mem_zpowers haK hcK (a_pow cfg) (c_pow cfg) hcomm cfg.ha_not)
  have hĀI : Subgroup.zpowers (barK K a haK) ⊔ Subgroup.zpowers (barK K c hcK) ≤
      Ibar L K b hIK :=
    sup_le (Subgroup.zpowers_le.mpr (mk_mem_Ibar hIK (a_mem_resI cfg)))
      (Subgroup.zpowers_le.mpr (mk_mem_Ibar hIK (c_mem_resI cfg)))
  have hkerf := ker_fCfg cfg
  exact
    { quasisimple := Sec6.isQuasisimple_of_mem_thetaComponentsAt cfg.hK
      theta_eq_bot := Sec11.aschbacherSolvableCore_quotient_eq_bot ↥K
      sectionFourHyp := sectionFourHyp_quot h1 cfg.std.toTheoremFourHyp hb1 cfg.hK
      orderOf_c := orderOf_barK_eq_three hcK (c_pow cfg) cfg.std.ne_one
      c_mem := mk_mem_Ibar hIK (c_mem_resI cfg)
      le_centralizer := Ibar_le_centralizer hIK hcK (resI_le_centralizer_c cfg)
      isPerfect := isPerfect_Ibar hIK
      isSubnormal := Ibar_isSubnormal cfg
      ne_top := Ibar_ne_top hIK cfg.hlt
      surjective := fCfg_surjective cfg
      ker_solvable := hkerf.1
      ker_three := hkerf.2
      quasisimple_Lb := Sec6.isQuasisimple_of_mem_thetaComponentsAt cfg.std.mem_thetaComponentsAt
      type_Lb := cfg.list
      a_mem := mk_mem_Ibar hIK (a_mem_resI cfg)
      orderOf_a := orderOf_barK_eq_three haK (a_pow cfg) ha1
      a_not_mem := barK_not_mem_zpowers haK hcK (a_pow cfg) (c_pow cfg) hcomm cfg.ha_not
      le_X := le_Xbar cfg
      X_le := Xbar_le_sup_center cfg
      beta := fun t ht ht3 => beta_lift cfg ht ht3
      gamma := eps_lift h125 cfg hĀI hĀab hĀ9
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      eps := fun F hFI hFab hF9 hcF => eps_lift h125 cfg hFI hFab hF9 hcF }

end Assembly

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
