module

public import CFSG.RankThree.PartTwo.Sec9.Hyp91SmallBridge
import CFSG.RankThree.PartTwo.Sec9.Hyp91SmallModels
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
public import CFSG.RankThree.PartTwo.Sec13.Item131a

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section FixedCore

variable {G : Type} [Group G] [Finite G]

theorem thetaAlpha_autThetaQuot_centralizer_eq_bot_of_fixedCore {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L)
    (hK : ∀ e ∈ A, e ∉ Subgroup.zpowers c → ∀ (he : e ∈ Subgroup.normalizer (L : Set G))
      (N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L))),
      (∀ ν ∈ N, ν * Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, he⟩) =
        Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, he⟩) * ν) →
      ¬ 3 ∣ Nat.card N →
      (∀ ℓ : L ⧸ aschbacherSolvableCore 3 L,
        Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, he⟩) ℓ = ℓ →
          ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) →
      N = ⊥) :
    thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
      (Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L)) = ⊥ := by
  set X := Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L with hX
  set B := (Sec4.autThetaQuot A L).subgroupOf X with hB
  have hcore : ∀ b : X, b ∈ B → b ≠ 1 →
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) = ⊥ := by
    intro b hb hb1
    obtain ⟨e, he, heA, hbe⟩ := Sec4.mem_autThetaQuot_iff.mp (Subgroup.mem_subgroupOf.mp hb)
    have hε : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨e, he⟩) = (b : MulAut _) := hbe
    have hec : e ∉ Subgroup.zpowers c := by
      intro hec
      apply hb1
      have h2 : e ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
        rw [hD.sectionCentralizer_eq]
        exact hec
      rw [Late.sectionCentralizer] at h2
      obtain ⟨-, h2'⟩ := h2
      apply Subtype.ext
      rw [← hε]
      exact KFacts.thetaQuotMulAut_compAction_eq_one_of_forall he h2'
    set Q := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) with hQ
    have hQC : Q ≤ Subgroup.centralizer ({b} : Set X) := Subgroup.map_subtype_le _
    have hN : Q.map X.subtype = ⊥ := by
      refine hK e heA hec he (Q.map X.subtype) ?_ ?_ ?_
      ·
        rintro _ ⟨q, hq, rfl⟩
        rw [hε]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hQC hq))
      ·
        intro h3
        apply Sec11.not_three_dvd_card_inSubgroup_theta (Subgroup.centralizer ({b} : Set X))
        rwa [Subgroup.card_map_of_injective X.subtype_injective] at h3
      ·
        intro ℓ hℓ ν hν
        obtain ⟨q, hq, rfl⟩ := hν
        obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) ℓ
        have hlN : (l : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l.2
        have hlX : MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) l) ∈ X := by
          refine Sec4.mem_autThetaQuot_iff.mpr ⟨l, hlN, hD.le_centralizer l.2, ?_⟩
          exact KFacts.thetaQuotMulAut_compAction_of_mem l.2 hlN
        set γ : X := ⟨_, hlX⟩ with hγ
        have hγb : γ ∈ Subgroup.centralizer ({b} : Set X) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply Subtype.ext
          change MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) l) * (b : MulAut _) =
            (b : MulAut _) * MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) l)
          rw [hε] at hℓ
          have h1 := KFacts.mul_conj_mul_inv (b : MulAut _)
            (QuotientGroup.mk' (aschbacherSolvableCore 3 L) l)
          rw [hℓ] at h1
          calc MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) l) * (b : MulAut _) =
              (b : MulAut _) * MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) l) *
                (b : MulAut _)⁻¹ * (b : MulAut _) := by rw [h1]
            _ = (b : MulAut _) * MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) l) :=
              by group
        exact ⟨γ * q * γ⁻¹, conj_mem_inSubgroup_theta hγb hq, rfl⟩
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hN
  have hAX : Sec4.autThetaQuot A L ≤ X := autThetaQuot_mono hD.A_le_centralizer L
  obtain ⟨b₀, hb₀, hb₀1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : Sec4.autThetaQuot A L ≤ ⊥ := by
      intro τ hτ
      have h1 := hcon ⟨τ, hAX hτ⟩ (Subgroup.mem_subgroupOf.mpr hτ)
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
    have h9 := card_autThetaQuot_eq_nine hD
    rw [le_bot_iff.mp hle, Subgroup.card_bot] at h9
    omega
  have hJ : thetaJ 3 B = ⊥ := by
    refine eq_bot_iff.mpr (iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_)
    rw [hcore b hb hb1, Subgroup.commutator_bot_left]
  have hT : thetaT 3 B = ⊥ := by
    refine eq_bot_iff.mpr ((iInf_le_of_le b₀ (iInf_le_of_le hb₀ (iInf_le_of_le hb₀1 le_rfl))).trans
      ?_)
    rw [hcore b₀ hb₀ hb₀1]
  rw [thetaAlpha, hJ, hT, sup_bot_eq]

end FixedCore

section Small

variable {G : Type} [Group G] [Finite G]

theorem hyp81_of_sec13Data {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) {a : G}
    (haA : a ∈ A) (ha1 : a ≠ 1)
    (hk : KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) :
    Sec8.Hyp81 G A c L a := by
  have hFE := (hD.toTheoremFourHyp.partTwoF_eq_partTwoE hD.partTwoS_eq).1
  exact ⟨hD.toPartTwoStanding, hD.mem_partTwoF, hD.mem_A, hD.ne_one, hD.mem_thetaComponentsAt,
    hD.sectionCentralizer_eq, haA, ha1, hk,
    fun hbig => absurd hbig (by rw [hD.card_eq]; omega), fun _ => hFE.symm⟩

theorem not_lTwoEight_of_thetaAlpha_ne_bot {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hα : thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
      (Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L)) ≠ ⊥)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hk : KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) :
    ¬ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)) := by
  intro hL
  have h81 := hyp81_of_sec13Data hD haA ha1 hk
  exact hα (thetaAlpha_autThetaQuot_centralizer_eq_bot_of_fixedCore hD fun e heA hec he N =>
    KFacts.eq_bot_of_hyp81_psl28 h81 hD.card_eq hL hD.le_normalizer heA hec he N)

theorem not_slThreePiEight_of_thetaAlpha_ne_bot {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L)
    (hα : thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
      (Sec4.autThetaQuot (Subgroup.centralizer ({c} : Set G)) L)) ≠ ⊥)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hk : KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) :
    ¬ Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) 8 := by
  intro hSL
  have h81 := hyp81_of_sec13Data hD haA ha1 hk
  exact hα (thetaAlpha_autThetaQuot_centralizer_eq_bot_of_fixedCore hD fun e heA hec he N =>
    KFacts.eq_bot_of_hyp81_su38 h81 hD.card_eq hSL hD.le_normalizer heA hec he N)

end Small

theorem gap131Hyp1134_of_item1134E27N (h1134 : Sec11.Item1134E27N) : Gap131Hyp1134 := by
  intro G _ _ A c L hD hα a haA ha1 hk
  exfalso
  have hst := hD.toPartTwoStanding
  have hFE := (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hD.partTwoS_eq).1
  have hx := h1134 G A c L hst hD.mem_partTwoF hD.not_mem_partTwoT hD.card_eq hD.mem_A hD.ne_one
    (mem_lStarAt_of_sec13Data hD) hD.sectionCentralizer_eq
    (not_lTwoEight_of_thetaAlpha_ne_bot hD hα haA ha1 hk)
    (not_slThreePiEight_of_thetaAlpha_ne_bot hD hα haA ha1 hk) (fun _ => hFE.symm) a haA
  rcases hk with hk | hk
  · exact hx.1 hk
  · exact hx.2 hk

theorem rank3II_13_1a_of_item1134E27N (h423 : Sec4.Item4_23) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (hK : KS131AlphaInvolutionCentral) (h1134 : Sec11.Item1134E27N) :
    Item131a :=
  rank3II_13_1a_of h423 h422 h45 hK (gap131Hyp1134_of_item1134E27N h1134)
    (Sec11.item1134E27_of_item1134E27N h45 h1134)

end CFSG.RankThree.PartTwo.Sec13
