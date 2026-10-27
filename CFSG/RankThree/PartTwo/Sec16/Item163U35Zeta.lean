module

public import CFSG.RankThree.PartTwo.Sec16.Item163U35Conf
public import CFSG.RankThree.PartTwo.KFacts.KS163U35Klein
import CFSG.RankThree.PartTwo.Sec16.Item163U35Two
import CFSG.RankThree.PartTwo.Sec16.Item163U35Y
import CFSG.RankThree.PartTwo.Sec16.Item163U35Push
import CFSG.RankThree.PartTwo.Sec16.Item163ResProofU35Facts
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163U35

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y : Subgroup G}

namespace Conf684

theorem pCoreOf_le_of_isZeta (h : Conf684 A c L Y) {T K : Subgroup G}
    (hTK : IsZeta A L T K) : CFSG.Open.pCoreOf 2 K ≤ T := by
  have hA : IsE27 A := Late.isE27_of_mem_partTwoE h.sec15R.toSec13Data.mem_partTwoE
  have hQ : CFSG.Open.pCoreOf 2 K ∈ scriptQ A (lB A) :=
    Res163U35Facts.pCoreOf_mem_scriptQ h.sec15R hTK.1
      (h.case3_of_mem hTK.1 hTK.2.1) h.item1444 h.item146
  exact pCoreOf_le_of_mem_scriptQPiStar_normalizer hA h.item146 hQ hTK.2.2

private theorem isPGroup_and_le_of_eq_inf (h : Conf684 A c L Y) {T K P : Subgroup G}
    (hTK : IsZeta A L T K)
    (hP : P = CFSG.Open.pCoreOf 2 (K ⊔ T) ⊓ Subgroup.centralizer ({c} : Set G)) :
    IsPGroup 2 P ∧ P ≤ L ∧ A ⊓ L ≤ Subgroup.normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 P := by
    rw [hP]
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ T)).to_le inf_le_left
  have hPc : P ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hP]
    exact inf_le_right
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hTK.1.prop.1.1.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := (mem_scriptQ_iff.mp hTK.2.2.prop.1.1).2.1
  have hAKT : A ≤ Subgroup.normalizer (K ⊔ T : Subgroup G) :=
    (le_inf hAK hAT).trans (Subgroup.inf_normalizer_le_normalizer_sup K T)
  have hAO : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ T) : Set G) :=
    hAKT.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ T))
  have hAN : A ≤ Subgroup.normalizer
      (Subgroup.centralizer ({c} : Set G) : Set G) :=
    h.sec15R.toSec13Data.A_le_centralizer.trans Subgroup.le_normalizer
  have hAP : A ⊓ L ≤ Subgroup.normalizer (P : Set G) := by
    rw [hP]
    exact (le_inf (inf_le_left.trans hAO) (inf_le_left.trans hAN)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨hP2, le_of_le_centralizer h hP2 hPc hAP, hAP⟩

private theorem eq_bot_of_card_eq_four (h : Conf684 A c L Y) {T K P : Subgroup G}
    (hTK : IsZeta A L T K)
    (hP : P = CFSG.Open.pCoreOf 2 (K ⊔ T) ⊓ Subgroup.centralizer ({c} : Set G))
    (hPL : P ≤ L) (hPcard : Nat.card P = 4) : P = ⊥ := by
  set J : Subgroup G := K ⊓ L with hJdef
  obtain ⟨-, hLcard, hJiso, -, -, -, -, -⟩ :=
    Res163U35Facts.facts h.sec15R hTK.1 (h.case3_of_mem hTK.1 hTK.2.1)
  have hcardA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hcardJ : Nat.card J = 2520 := by
    rw [hJdef]
    obtain ⟨e⟩ := hJiso
    rw [Nat.card_congr e.toEquiv, hcardA7]
  have hJL : J ≤ L := by
    rw [hJdef]
    exact inf_le_right
  have hJO : J ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ T) : Set G) := by
    rw [hJdef]
    exact (inf_le_left.trans (le_sup_left : K ≤ K ⊔ T)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T))
  have hJNc : J ≤ Subgroup.normalizer
      (Subgroup.centralizer ({c} : Set G) : Set G) :=
    hJL.trans (h.sec15R.toSec13Data.le_centralizer.trans Subgroup.le_normalizer)
  have hJNP : J ≤ Subgroup.normalizer (P : Set G) := by
    rw [hP]
    exact (le_inf hJO hJNc).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hnorm : ((J ⊓ P).subgroupOf J).Normal := by
    have h1 : (P.subgroupOf J).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hJNP
    have hsub : P.subgroupOf J = (J ⊓ P).subgroupOf J := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
    rwa [hsub] at h1
  haveI : IsSimpleGroup ↥J := by
    rw [hJdef]
    obtain ⟨e⟩ := hJiso
    haveI : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by norm_num)
    exact e.isSimpleGroup
  haveI := hnorm
  have hinfJP : J ⊓ P = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((J ⊓ P).subgroupOf J) with hbot | htop
    · rw [← le_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.1⟩ : ↥J) ∈ (J ⊓ P).subgroupOf J :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hbot] at hx'
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hx')
    · exfalso
      have hJP : J ≤ P := by
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥J) ∈ (J ⊓ P).subgroupOf J := by
          rw [htop]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx')).2
      have hle : Nat.card J ≤ Nat.card P := Subgroup.card_le_of_le hJP
      rw [hcardJ, hPcard] at hle
      norm_num at hle
  have hcardJP : Nat.card (J ⊔ P : Subgroup G) = 10080 := by
    have h := Sec6.card_sup_mul_card_inf (X := J) (N := P) hJNP
    rw [hinfJP, Subgroup.card_bot, mul_one, hcardJ, hPcard] at h
    norm_num at h
    exact h
  have hdvd : Nat.card (J ⊔ P : Subgroup G) ∣ Nat.card L :=
    Subgroup.card_dvd_of_le (sup_le hJL hPL)
  exfalso
  rw [hcardJP, hLcard] at hdvd
  norm_num at hdvd

theorem pCoreOf_sup_inf_centralizer_eq_bot (h : Conf684 A c L Y)
    (hK1 : KFacts.KS163U35InvTwo) {T K : Subgroup G} (hTK : IsZeta A L T K) :
    CFSG.Open.pCoreOf 2 (K ⊔ T) ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ := by
  set P : Subgroup G :=
    CFSG.Open.pCoreOf 2 (K ⊔ T) ⊓ Subgroup.centralizer ({c} : Set G) with hP
  obtain ⟨hP2, hPL, hAP⟩ := isPGroup_and_le_of_eq_inf h hTK hP
  by_contra hPbot
  have hPcard : Nat.card P = 4 :=
    (card_eq_four_of_le h hK1 hPL hP2 hAP hPbot).1
  exact hPbot (eq_bot_of_card_eq_four h hTK hP hPL hPcard)

theorem pCoreOf_sup_eq_of_isZeta (h : Conf684 A c L Y) (hK1 : KFacts.KS163U35InvTwo)
    {T K : Subgroup G} (hTK : IsZeta A L T K) :
    CFSG.Open.pCoreOf 2 (K ⊔ T) = ⁅T, Subgroup.zpowers c⁆ := by
  have hcase := h.case3_of_mem hTK.1 hTK.2.1
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    obtain ⟨e⟩ := hcase.2.1
    have hmap := Subgroup.map_center_eq e
    rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 7))] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  exact pCoreOf_sup_eq_commutator h.sec15R.toSec14Std h.item146 h.concl142
    hTK.1.prop.1.1.2 hTK.2.2 hcase.2.2.1 (pCoreOf_le_of_isZeta h hTK) hZ
    (pCoreOf_sup_inf_centralizer_eq_bot h hK1 hTK)

private theorem commutator_ne_bot_of_isZeta (h : Conf684 A c L Y)
    (hK1 : KFacts.KS163U35InvTwo) {T K : Subgroup G} (hTK : IsZeta A L T K) :
    ⁅T, Subgroup.zpowers c⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := pCoreOf_sup_eq_of_isZeta h hK1 hTK
  have hTK' : T ≤ Subgroup.normalizer (K : Set G) := hTK.2.2.prop.1.2
  have hOleR : CFSG.Open.pCoreOf 2 K ≤ ⁅T, Subgroup.zpowers c⁆ := by
    rw [← hR]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
        (hTK'.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  exact fun hbot => hTK.1.prop.2.2 (le_bot_iff.mp (hbot ▸ hOleR))

private theorem sup_le_normalizer_commutator_of_isZeta (h : Conf684 A c L Y)
    (hK1 : KFacts.KS163U35InvTwo) {T K : Subgroup G} (hTK : IsZeta A L T K) :
    A ⊔ K ≤ Subgroup.normalizer ((⁅T, Subgroup.zpowers c⁆ : Subgroup G) : Set G) := by
  have hR := pCoreOf_sup_eq_of_isZeta h hK1 hTK
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hTK.1.prop.1.1.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := (mem_scriptQ_iff.mp hTK.2.2.prop.1.1).2.1
  have hAKT : A ≤ Subgroup.normalizer (K ⊔ T : Subgroup G) :=
    (le_inf hAK hAT).trans (Subgroup.inf_normalizer_le_normalizer_sup K T)
  have hAN : A ≤ Subgroup.normalizer ((⁅T, Subgroup.zpowers c⁆ : Subgroup G) : Set G) := by
    rw [← hR]
    exact hAKT.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ T))
  have hKN : K ≤ Subgroup.normalizer ((⁅T, Subgroup.zpowers c⁆ : Subgroup G) : Set G) := by
    rw [← hR]
    exact (le_sup_left : K ≤ K ⊔ T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T))
  exact sup_le hAN hKN

theorem eq_of_isZeta (h : Conf684 A c L Y) (hK1 : KFacts.KS163U35InvTwo)
    {T K₁ K₂ : Subgroup G} (h₁ : IsZeta A L T K₁) (h₂ : IsZeta A L T K₂) :
    K₁ = K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup G := ⁅T, Subgroup.zpowers c⁆ with hR
  have hR₁ : CFSG.Open.pCoreOf 2 (K₁ ⊔ T) = R := by
    rw [hR]
    exact pCoreOf_sup_eq_of_isZeta h hK1 h₁
  have hRne : R ≠ ⊥ := by
    rw [hR]
    exact commutator_ne_bot_of_isZeta h hK1 h₁
  have hR2 : IsPGroup 2 R := by
    rw [← hR₁]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K₁ ⊔ T)
  have hNRtop : Subgroup.normalizer (R : Set G) ≠ ⊤ :=
    Sec14.normalizer_ne_top_of_isPGroup h.sec15R.isSimpleGroup h.sec15R.nonabelian hRne hR2
  have hloc : IsPLocal 2 (Subgroup.normalizer (R : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hR2 hRne
  obtain ⟨M, hNRM, hMmax⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hsup₁ : A ⊔ K₁ ≤ Subgroup.normalizer (R : Set G) := by
    rw [hR]
    exact sup_le_normalizer_commutator_of_isZeta h hK1 h₁
  have hsup₂ : A ⊔ K₂ ≤ Subgroup.normalizer (R : Set G) := by
    rw [hR]
    exact sup_le_normalizer_commutator_of_isZeta h hK1 h₂
  have hM₁ : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ K₁ : Subgroup G) : Set G) :=
    ⟨hMmax, fun x hx => hNRM (hsup₁ hx)⟩
  have hM₂ : M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ K₂ : Subgroup G) : Set G) :=
    ⟨hMmax, fun x hx => hNRM (hsup₂ hx)⟩
  have hΔ₁ : delta A (lB A) M ≤ Subgroup.normalizer (K₁ : Set G) :=
    delta_le_normalizer_of_mem h.item155 h₁.1 hM₁
  have hΔ₂ : delta A (lB A) M ≤ Subgroup.normalizer (K₂ : Set G) :=
    delta_le_normalizer_of_mem h.item155 h₂.1 hM₂
  have hK₁M : K₁ ≤ M := (le_sup_right : K₁ ≤ A ⊔ K₁).trans (hsup₁.trans hNRM)
  have hK₂M : K₂ ≤ M := (le_sup_right : K₂ ≤ A ⊔ K₂).trans (hsup₂.trans hNRM)
  have hK₁N₂ : K₁ ≤ Subgroup.normalizer (K₂ : Set G) :=
    (h₁.1.prop.1.2.2.1.le.trans (Sec14.delta_mono hK₁M)).trans hΔ₂
  have hK₂N₁ : K₂ ≤ Subgroup.normalizer (K₁ : Set G) :=
    (h₂.1.prop.1.2.2.1.le.trans (Sec14.delta_mono hK₂M)).trans hΔ₁
  obtain ⟨-, -, hJ₁iso, -, -, -, -, -⟩ :=
    Res163U35Facts.facts h.sec15R h₁.1 (h.case3_of_mem h₁.1 h₁.2.1)
  obtain ⟨-, -, hJ₂iso, -, -, -, -, -⟩ :=
    Res163U35Facts.facts h.sec15R h₂.1 (h.case3_of_mem h₂.1 h₂.2.1)
  have hJ₁N : K₁ ⊓ L ≤ Subgroup.normalizer ((K₂ ⊓ L : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (X := K₂) (Y := L)
      (inf_le_left.trans hK₁N₂) (inf_le_right.trans Subgroup.le_normalizer)
  have hJeq : K₁ ⊓ L = K₂ ⊓ L :=
    eq_of_le_normalizer h inf_le_right inf_le_right hJ₁iso hJ₂iso hJ₁N
  have hcov₂ : K₂ = K₂ ⊓ L ⊔ CFSG.Open.pCoreOf 2 K₂ :=
    (h.case3_of_mem h₂.1 h₂.2.1).2.2.1
  have hcov : K₂ ≤ K₁ ⊔ CFSG.Open.pCoreOf 2 K₂ := by
    calc K₂ = K₂ ⊓ L ⊔ CFSG.Open.pCoreOf 2 K₂ := hcov₂
      _ = K₁ ⊓ L ⊔ CFSG.Open.pCoreOf 2 K₂ := by rw [hJeq]
      _ ≤ K₁ ⊔ CFSG.Open.pCoreOf 2 K₂ := sup_le_sup_right inf_le_left _
  have hsupNR : K₁ ⊔ K₂ ≤ Subgroup.normalizer (R : Set G) :=
    sup_le ((le_sup_right : K₁ ≤ A ⊔ K₁).trans hsup₁)
      ((le_sup_right : K₂ ≤ A ⊔ K₂).trans hsup₂)
  have htop : K₁ ⊔ K₂ ≠ ⊤ := fun htop =>
    hNRtop (top_le_iff.mp (htop ▸ hsupNR))
  exact eq_of_mem_scriptY0Star h₁.1 h₂.1 hK₁N₂ hK₂N₁ hcov htop

end Conf684

end CFSG.RankThree.PartTwo.Sec16.Proof163U35
