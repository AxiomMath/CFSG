module

public import CFSG.Quasithin.Vol2.Ch10SecKRTe
public import CFSG.Quasithin.Vol2.Ch10SecKRTh
public import CFSG.Quasithin.Vol2.Ch10SecKRTk
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native312
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312SL2Native

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

namespace KRT

theorem not_nonquasi_of_quasisimple {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}
    (hq : CFSG.IsQuasisimple ↥L) : ¬ A312Nonquasi B L := by
  have hc : ⁅(CFSG.oddCore ↥L).map L.subtype, L⁆ = ⊥ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (CFSG.oddCore_normal ↥L) with h | h
    · exfalso
      have hs : Group.IsSolvable ↥(CFSG.oddCore ↥L) := A312.oddCore_isSolvable _
      let e : ↥(CFSG.oddCore ↥L) ≃* ↥L := (MulEquiv.subgroupCongr h).trans Subgroup.topEquiv
      have : Group.IsSolvable ↥L := Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
      have : Group.IsPerfect ↥L := hq.1
      have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
      exact Group.IsPerfect.not_isSolvable ↥L inferInstance
    · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (h hx) ⟨l, hl⟩)
  unfold A312Nonquasi
  dsimp only
  rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h hc

variable {G : Type} [Group G] [Finite G] {T L I H K M₁ J : Subgroup G} {n m : ℕ}

theorem T_le_normalizer_of_not_quasisimple (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (cfg : B0KConfig G T L I H K M₁ J n m)
    (hq : ¬ CFSG.IsQuasisimple ↥(modO2Image M₁ J)) : T ≤ Subgroup.normalizer (J : Set G) := by
  rcases Vol2Native.lemma_1_2_1_three (localSQTK cfg) h37 h38 (pCoreOf_ne_bot cfg) cfg.hJ with
    hn | ⟨-, hA⟩
  · exact (T_le cfg).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (J_le cfg)).mp hn)
  · exfalso
    have : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J) := Vol2Native.L122A.isSimpleGroup_of_a38Types hA
    obtain ⟨e⟩ := modO2_mulEquiv cfg.hJ
    have : IsSimpleGroup ↥(modO2Image M₁ J) := e.symm.isSimpleGroup
    have hJb := Jbar_mem_cComp cfg
    have hnc : ∃ a b : ↥(modO2Image M₁ J), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have hb : ⁅modO2Image M₁ J, modO2Image M₁ J⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a ha
        exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
          congrArg Subtype.val (hcon ⟨b, hb⟩ ⟨a, ha⟩)
      rw [perfect_of_mem_cComp hJb] at hb
      exact ne_bot_of_mem_cComp hJb hb
    exact hq (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

end KRT

theorem b0KCases_of (hList : Vol2Native.A312ListFactsCat) (h56 : AsB56)
    (h36 : Vol2Native.A36CoreForSQTKCat) (h36' : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) (h1022 : Stmt10_2_2) :
    B0KCases := by
  intro G _ _ T L I H K M₁ J n m cfg
  have h312 : Vol2Native.A312ForSQTKCat :=
    Vol2Native.a312ForSQTKCat_of_facts hList Vol2Native.a312SL2Fact h36 h37 h39
  by_cases hq : CFSG.IsQuasisimple ↥(modO2Image M₁ J)
  · rcases KRT.list h312 cfg with heq | hA | hN
    · exact Or.inl (KRT.eq_of_modO2Image_eq cfg heq)
    · right
      obtain ⟨M, hM, hc⟩ : ∃ M : ℕ, SecC.C10KH.B56Card M ∧
          (Nat.card ↥(modO2Image M₁ J) = M ∨ Nat.card ↥(modO2Image M₁ J) = 3 * M) := by
        by_cases hTJ : T ≤ Subgroup.normalizer (J : Set G)
        · exact KRT.card_of_normal h56 h36' h1022 cfg hTJ hq
        · exact KRT.card_of_not_normal h56 h37 h38 h1022 cfg hTJ
      rcases KRT.typeB_or_typeC cfg hA hM hc with hb | hc'
      · exact Or.inl hb
      · exact Or.inr (Or.inl hc')
    · exact (KRT.not_nonquasi_of_quasisimple hq hN).elim
  · have hTJ := KRT.T_le_normalizer_of_not_quasisimple h37 h38 cfg hq
    have h36J := (h36' _ (sqtkHyp_of_cat (KRT.sqtkHypCat_bar cfg))) _ (KRT.Jbar_mem_cComp cfg)
    rcases A312.nonquasi_of_lFamily Vol2Native.a312SL2Fact (KRT.sylow_bar cfg)
        (KRT.Jbar_mem_cComp cfg) (KRT.Kbar_le_Jbar cfg) (KRT.Kbar_mem_lFamily cfg) h36J hq with
      h21 | ⟨-, ⟨p, hp, hp5, hp8, hpSL⟩, -⟩
    · exact Or.inr (Or.inr (Or.inr h21))
    · exact (KRT.false_of_22 h56 h1022 cfg hTJ hp hp5 hp8 hpSL).elim

end CFSG.Quasithin.Vol2.Ch10.SecB
