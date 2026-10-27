module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeDatum
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TorsionLabel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLeafComponent
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Absence
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.TablePThreeKG

section Certificates


private theorem datumOn_e6_of_marking {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : GGTablePThreeDatum A δ J)
    (hm : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .E6 ∨ lab.tag = .twE6)) :
    DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J := by
  obtain ⟨_, lab, hlab, hraw⟩ := hm
  have ht : lab.tag = .E6 ∨ lab.tag = .twE6 :=
    e6TwoLeaf_rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun _ _ _ _ h => h.2.2.elim fun _ ht => ht) hraw)
  have hhas : GGHasLabel lab (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun _ _ _ _ h => ⟨h.2.2.choose⟩) hraw
  obtain ⟨hloc, huniq, hcard, hperf, lab₀, hlab₀, hraw₀⟩ := hd
  have hhas₀ : GGHasLabel lab₀ (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun _ _ _ _ h => ⟨h.2.2.choose⟩) hraw₀
  have heq : lab = lab₀ := eq_of_ggLabelIso_of_e6Tag
    (ggLabelRigidInput_holds lab lab₀ _ hlab hlab₀ hhas hhas₀) ht
  refine ⟨hloc, huniq, hcard, hperf, lab₀, hlab₀, ?_⟩
  refine largeEvenRawDatum_mono ?_ hraw₀
  rintro _ _ _ _ ⟨hs, hna, θ, hsplit, hact⟩
  exact ⟨hs, hna, θ, heq ▸ ht, hsplit, hact⟩

private theorem exists_label_not_exc_of_e6_datum {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) ∧
        ¬ (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
  obtain ⟨hperf, lab₀, hlab₀, hraw₀⟩ := hd.2.2.2
  have ht₀ : lab₀.tag = .E6 ∨ lab₀.tag = .twE6 :=
    e6TwoLeaf_rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun _ _ _ _ h => h.2.2.elim fun _ ht => ht.1) hraw₀)
  by_cases hn : 2 ≤ lab₀.n
  · have hq : LargeEvenMarking X (fun lab _ _ _ _ _ => 2 ≤ lab.n) :=
      ⟨hperf, lab₀, hlab₀,
        largeEvenRawDatum_mono (fun _ _ _ _ h => ⟨h.1, h.2.1,
          h.2.2.elim fun θ _ => ⟨θ, hn⟩⟩) hraw₀⟩
    have hδmem : δ ∈ A := hd.1.1.2.1
    have hdat : GGTorsionDatum (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6) 3 δ J :=
      ⟨Nat.prime_three, by norm_num, hd.1.1.1.2 δ hδmem, hd.1.1.2.2.1,
        hd.1.1.2.2.2.1,
        largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.2 δ hδmem⟩) hd.2.2.2⟩
    obtain ⟨_, lab₁, _, hraw₁⟩ := ggTorsion_E6eps_unique_label hdat hq hd.2.1
    have hc : ∃ lab, LargeEvenInLambda2 lab ∧
        GGHasLabel lab (J ⧸ Subgroup.center J) ∧ E6CompLabel (2 ^ lab₁.n) lab :=
      e6TwoLeaf_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun _ _ _ _ h => h.2.2.elim fun _ hc => hc.2) hraw₁)
    obtain ⟨lab, hlab, hhas, hc⟩ := hc
    refine ⟨lab, hlab, hhas, ?_⟩
    intro hexc
    rcases hc with ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨ht, _⟩ | ⟨_, _, ht⟩
    · rcases ht with ht | ht | ht | ht <;> rcases hexc with hexc | hexc | hexc <;>
        simp_all
    · rcases ht with ht | ht <;> rcases hexc with hexc | hexc | hexc <;> simp_all
    · rcases hexc with hexc | hexc | hexc <;> simp_all
    · rcases ht with ⟨_, ht⟩ | ⟨_, ht⟩ <;> rcases hexc with hexc | hexc | hexc <;>
        simp_all
  · have hsmall : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.n < 2) :=
      ⟨hperf, lab₀, hlab₀,
        largeEvenRawDatum_mono (fun _ _ _ _ h => ⟨h.1, h.2.1,
          h.2.2.elim fun θ _ => ⟨θ, Nat.lt_of_not_ge hn⟩⟩) hraw₀⟩
    rcases ht₀ with ht₀ | ht₀
    · have hW : DatumOn (fun t => t = .E6) X A δ J :=
        ⟨hd.1, hd.2.1, hd.2.2.1, hperf, lab₀, hlab₀,
          largeEvenRawDatum_mono (fun _ _ _ _ h => ⟨h.1, h.2.1,
            h.2.2.elim fun θ hθ => ⟨θ, ht₀, hθ.2⟩⟩) hraw₀⟩
      obtain ⟨lab, hlab, hhas, hW, _⟩ := e6TwoLeaf_label_W hW hsmall
      refine ⟨lab, hlab, hhas, ?_⟩
      rcases hW with rfl | rfl | rfl <;> simp
    · have hT : DatumOn (fun t => t = .twE6) X A δ J :=
        ⟨hd.1, hd.2.1, hd.2.2.1, hperf, lab₀, hlab₀,
          largeEvenRawDatum_mono (fun _ _ _ _ h => ⟨h.1, h.2.1,
            h.2.2.elim fun θ hθ => ⟨θ, ht₀, hθ.2⟩⟩) hraw₀⟩
      obtain ⟨lab, hlab, hhas, hT⟩ := e6TwoLeaf_label_T hT hsmall
      refine ⟨lab, hlab, hhas, ?_⟩
      rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ggConfig_not_excLabel_of_e6_marking {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hm : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .E6 ∨ lab.tag = .twE6))
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (htJ : labJ.tag = .E6 ∨ labJ.tag = .twE6 ∨ labJ.tag = .E7)
    (hJ : GGHasLabel labJ (J ⧸ Subgroup.center J)) : False := by
  obtain ⟨hNL, δ, hd⟩ := exists_ggTablePThree_datum hcfg.1 hcfg.2.2
  obtain ⟨lab, hΛ, hhas, hnot⟩ :=
    exists_label_not_exc_of_e6_datum (datumOn_e6_of_marking hd hm)
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hhasJ : GGHasLabel lab (J ⧸ Subgroup.center J) :=
    ggHasLabel_of_mulEquiv (centerQuotCongr (Subgroup.subgroupOfEquivOfLe hJL)) hhas
  have hiso := ggLabelRigidInput_holds labJ lab _ hΛJ hΛ hJ hhasJ
  have heq : lab = labJ := by
    refine ggLabelIso_eq_of_exceptional ?_ ?_ ?_ ?_ ?_ ?_ hiso <;>
      rcases htJ with htJ | htJ | htJ <;> rw [htJ] <;> decide
  exact hnot (heq ▸ htJ)

theorem ggBstarToralJExcInputOn_e6_twE6_holds :
    GGBstarToralJExcInputOn (fun lab => lab.tag = .E6 ∨ lab.tag = .twE6) := by
  intro G _ _ B Bs x L D J hcfg hm _ labJ hΛJ htJ hJ
  exact (ggConfig_not_excLabel_of_e6_marking hcfg
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hm) hΛJ htJ hJ).elim

theorem ggBstarToralJExcInputOn_of_not_e6_twE6 {S : LargeEvenLabel → Prop}
    (hrest : GGBstarToralJExcInputOn
      (fun lab => S lab ∧ ¬ (lab.tag = .E6 ∨ lab.tag = .twE6))) :
    GGBstarToralJExcInputOn S := by
  intro G _ _ B Bs x L D J hcfg hm hJ labJ hΛJ htJ hlabelJ
  obtain ⟨hperf, lab, hlab, hraw⟩ := hm
  by_cases ht : lab.tag = .E6 ∨ lab.tag = .twE6
  · apply ggBstarToralJExcInputOn_e6_twE6_holds G B Bs x L D J hcfg _ hJ
      labJ hΛJ htJ hlabelJ
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro _ _ _ _ ⟨hs, hna, θ, _, hN, hact⟩
    exact ⟨hs, hna, θ, ht, hN, hact⟩
  · apply hrest G B Bs x L D J hcfg _ hJ labJ hΛJ htJ hlabelJ
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro _ _ _ _ ⟨hs, hna, θ, hS, hN, hact⟩
    exact ⟨hs, hna, θ, ⟨hS, ht⟩, hN, hact⟩

end Certificates

end CFSG.StandardType

end
