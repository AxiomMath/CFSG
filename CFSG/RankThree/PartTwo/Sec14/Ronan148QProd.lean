module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QInv
public import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofONConfig
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofMain
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofHJ
public import CFSG.RankThree.PartTwo.Sec14.Item14Res3ProofLBal
public import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec14.Item143DescProofGen
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148Q

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem item143QAt_of_item143NAt {A : Subgroup G} {LB : Subgroup G → Subgroup G} {a : G}
    (h : Item143NAt A LB a) : Item143QAt A LB a := fun Q hQ =>
  (h Q hQ).imp_right (Or.imp_right fun ⟨b, d, Lb, hb, hLb, hJ, hdA, hd1, hdc, hab,
    X, hX, hN, hcase⟩ => ⟨b, d, Lb, hb, hLb, hJ, hdA, hd1, hdc, hab, X, hX, Or.inl hN, hcase⟩)

section DescX

theorem step143HJDescXQ_of (h48 : Sec4.Item4_8) (hcomp : Step143HJCompOne)
    (htwo : Step143HJDescTwoQ) : Step143HJDescXQ := by
  intro G _ _ A c L h a ha ha1 hΩ B b d Lb hB haB hc
  by_cases hne : Subgroup.zpowers a = Subgroup.zpowers d
  · exact htwo G A c L h a ha ha1 hΩ B b d Lb hB haB hc hne
  have hOne : Desc143X.One A c L a b d B Lb := ⟨h, ha, ha1, hΩ, hB, haB, hc, hne⟩
  obtain ⟨X, hXΔ, hLD, hN, hX, hXeq, hne'⟩ :=
    hOne.descX h48 hcomp (Desc143X.lB_le_delta h hB hc haB)
  obtain ⟨-, hd1⟩ := IsLBConfig.ne_one hc hB h.isE27'
  have hdA : d ∈ A := hB.1 (hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  exact ⟨b, d, Lb, hc.2.1, hc.2.2.1 ▸ Set.mem_singleton Lb, Item148HJ.j2_of_isLBConfig hc, hdA,
    hd1, hc.2.2.2.2, hc.1 ▸ haB, X, hXΔ, hLD, Or.inl hN, Or.inl ⟨hX, hXeq, hne'⟩⟩

end DescX

section DescFix

open Res7MemFix Res7DescFix

theorem step143HJDescFixQ_of_memFixL (hbal : Step143Balance) (hX : Step143HJDescXQ)
    (hL : Step143HJMemFixL) : Step143HJDescFixQ := by
  intro G _ _ A c L h a ha ha1 hΩ B b d Lb hB haB hc
  obtain ⟨b', d', Lb', hb'Ω, hLb', hJ2, hd'A, hd'1, hd'3, hab', X, hXΔ, hLD, hN, hcase⟩ :=
    hX G A c L h a ha ha1 hΩ B b d Lb hB haB hc
  have hΔ := delta_eq_sup_sup_of hbal h ha ha1 hΩ hXΔ hLD
  refine ⟨b', d', Lb', hb'Ω, hLb', hJ2, hd'A, hd'1, hd'3, hab', X, hXΔ, hLD, hN, hcase, ?_⟩
  intro D hD haD R hRN hR3 hAR hRR
  by_cases hα : ∃ B' : Subgroup G, IsHyperplane A B' ∧ a ∈ B' ∧ B' ≠ D ∧
      ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))
  · obtain ⟨B', hB', -, hB'D, hcomm⟩ := hα
    exact le_qBound_of_commutator_le h ha hB' hD haD hB'D hcomm hRN hRR
  by_cases hβ : pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X ≤
      lB A D ⊔ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))
  · exact le_qBound_of_le_sup h ha hD haD hβ hD haD hRN hRR
  rcases hN with hN | ⟨-, hXθ, hA6, -⟩
  · rcases hcase with ⟨hXθ, hXeq, -⟩ | ⟨hda, h𝒳, htype⟩
    · exact ((alpha_or_beta_of_caseOne h ha ha1 hΩ hb'Ω hXθ hXeq).elim hα hβ).elim
    rcases htype with hON | hA6 | hA6A6
    · exact hL G A c L h a ha ha1 hΩ B b d Lb hB haB hc b' d' Lb' X hb'Ω hLb' hJ2 hd'A hd'1 hd'3
        hab' hXΔ hLD hΔ hN hda h𝒳 (Or.inl hON) D hD haD
        (fun B' hB' haB' hB'D hcomm => hα ⟨B', hB', haB', hB'D, hcomm⟩) hβ R hRN hR3 hAR hRR
    ·
      have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      obtain ⟨𝒳, h𝒳a, h𝒳ne, hX𝒳⟩ := h𝒳
      obtain ⟨hc3, ⟨e⟩⟩ := hA6
      have hXθ : X ∈ thetaComponentsAt 3 a :=
        h𝒳a (Item148Point.mem_of_eq_sSup148 h𝒳a h𝒳ne hX𝒳 e)
      have hOX := sup_le_sup_lB_of_tripleA6 h hB haB hc hXθ ⟨hc3, ⟨e⟩⟩ (hLD B hB haB)
      exact le_qBound_of_le_sup h ha hB haB hOX hD haD hRN hRR
    · exact hL G A c L h a ha ha1 hΩ B b d Lb hB haB hc b' d' Lb' X hb'Ω hLb' hJ2 hd'A hd'1 hd'3
        hab' hXΔ hLD hΔ hN hda h𝒳 (Or.inr hA6A6) D hD haD
        (fun B' hB' haB' hB'D hcomm => hα ⟨B', hB', haB', hB'D, hcomm⟩) hβ R hRN hR3 hAR hRR
  ·
    have hOX := sup_le_sup_lB_of_tripleA6 h hB haB hc hXθ hA6 (hLD B hB haB)
    exact le_qBound_of_le_sup h ha hB haB hOX hD haD hRN hRR

end DescFix

theorem step143HJQ_of_descFix (hbal : Step143Balance) (hfix : Step143HJDescFixQ) : Step143HJQ := by
  intro G _ _ A c L h a ha ha1 hΩ B b d Lb hB haB hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b', d', Lb', hb'Ω, hLb', hJ2, hd'A, hd'1, hd'3, hab', X, hXΔ, hLD, hN, hcase, hR⟩ :=
    hfix G A c L h a ha ha1 hΩ B b d Lb hB haB hc
  have hΔ := delta_eq_sup_sup_of hbal h ha ha1 hΩ hXΔ hLD
  intro Q hQ
  refine ⟨?_, Or.inr ⟨b', d', Lb', hb'Ω, hLb', hJ2, hd'A, hd'1, hd'3, hab', X, hΔ, hN, hcase⟩⟩
  have hA := h.isE27'
  have hAmax := h.maximal_isElemAbelian
  have hAab : IsMulCommutative A := hA.1.1
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hO
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  have hO'C : O' ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hO'N : O' ≤ Subgroup.normalizer ((O ⊔ X : Subgroup G) : Set G) :=
    hO'C.trans (hN.centralizer_le ha)
  have hΔA : ⁅delta A (lB A) (Subgroup.centralizer ({a} : Set G)), A⁆ ≤ O ⊔ X := by
    rw [hΔ, show O ⊔ O' ⊔ X = (O ⊔ X) ⊔ O' by
      rw [sup_assoc, sup_comm O' X, ← sup_assoc],
      CFSG.RankThreeEvenClassification.Helpers.normalized_sup_commutator_eq_of_fixed (O ⊔ X) O' A
        hO'N hO'C]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hN.le_normalizer hAab ha)
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.prop.2.1
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.prop.2.2
  have hQΔ : Q ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) := hQ.prop.1
  have hQa : Q ≤ Subgroup.centralizer ({a} : Set G) := hQΔ.trans (delta_le _)
  refine ⟨⟨⟨le_top, hQ.prop.2.1, hAQ⟩, fun D hD => ?_⟩, hQa⟩
  have hfac := inf_centralizer_le_commutator_sup hA hAmax hQ3 hAQ hD.1
  by_cases haD : a ∈ D
  ·
    set R := ⁅Q ⊓ Subgroup.centralizer (D : Set G), A⁆ with hRdef
    have hY3 : ¬ 3 ∣ Nat.card (Q ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) := fun h3 =>
      hQ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hAY : A ≤ Subgroup.normalizer
        ((Q ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf_centralizer hAab hAQ hD.1
    have hRY : R ≤ Q ⊓ Subgroup.centralizer (D : Set G) :=
      commutator_inf_centralizer_le hAab hAQ hD.1
    have hR3 : ¬ 3 ∣ Nat.card R := fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le hRY))
    have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
      CFSG.SignalizerFunctor.Helpers.normalized_commutator_normalized A _ hAY
    have hRR : R = ⁅R, A⁆ := (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent
      3 Nat.prime_three A (Q ⊓ Subgroup.centralizer (D : Set G)) hA.isPGroup hY3 hAY).symm
    have hRN : R ≤ (O ⊔ X) ⊓ Subgroup.centralizer (D : Set G) :=
      le_inf ((Subgroup.commutator_mono (inf_le_left.trans hQΔ) le_rfl).trans hΔA)
        (hRY.trans inf_le_right)
    refine hfac.trans (sup_le (hR D hD haD R hRN hR3 hAR hRR) ?_)
    rw [qBound]
    exact le_sup_right.trans le_sup_left
  ·
    have hAle := le_sup_zpowers_of_not_mem hA hD ha haD
    have hCA : Q ⊓ Subgroup.centralizer (D : Set G) ≤ Q ⊓ Subgroup.centralizer (A : Set G) :=
      fun x hx => ⟨hx.1, mem_centralizer_of_le_sup hAle hx.2 (hQa hx.1)⟩
    refine hCA.trans ((inf_centralizer_le_xA hAmax hQ3).trans ?_)
    rw [qBound]
    exact le_sup_right.trans le_sup_left

theorem item143QS14_of (hbal : Step143Balance) (hHJ : Step143HJQ) : Item143QS14 := by
  intro G _ _ A c L h a ha ha1 hΩ
  rcases forall_lB_eq_bot_or_exists_isLBConfig A a with hLB | ⟨B, b, d, Lb, hB, haB, hc⟩
  · exact item143QAt_of_item143NAt (item143NAt_of_lB_eq_bot hbal h ha ha1 hΩ hLB)
  · exact hHJ G A c L h a ha ha1 hΩ B b d Lb hB haB hc

section Items

theorem item143QS14_of_items (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement) (h134 : Item134)
    (hKPSz : KFacts.KPSz) (hON : Ronan148D.ONTripleGenE27) (hT1 : KS143LBalComp2)
    (hT2 : Sec4.Item4_25Fix) (hT3 : Step143HJCompRank)
    (hT4 : Step143HJCompM24) : Item143QS14 := by
  have hbal : Step143Balance := step143Balance_of h45 hKPSz (step143BalanceSz_of_comp2 hT1)
  exact item143QS14_of hbal (step143HJQ_of_descFix hbal (step143HJDescFixQ_of_memFixL hbal
    (step143HJDescXQ_of h48 (step143HJCompOne_of_item4_25Fix hT2 h134 h48 h41 hGW hT3 hT4)
      (step143HJDescTwoQ_of hT2 h134 h48 h41 hGW hON))
    (step143HJMemFixL_of_on hbal (step143HJMemFixON_of h134 h48))))

end Items

end CFSG.RankThree.PartTwo.Sec14.Ronan148Q
