module

public import CFSG.RankThree.PartTwo.Sec15.Item153Claims
public import CFSG.RankThree.PartTwo.Sec15.Item156Proof
public import CFSG.RankThree.PartTwo.Sec15.Item1512
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] noncomputable def Claim153NormalNoE9R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ¬ HasFaithfulE9 Y →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
        M ≤ Subgroup.normalizer (Y : Set G)

@[expose] noncomputable def Claim153CharR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Claim153Char A (lB A)

theorem claim153Normal_of_wired {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) (h152 : Item152 A (lB A))
    (hno : ∀ Y ∈ scriptY0Star A (lB A), ¬ HasFaithfulE9 Y →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
        M ≤ Subgroup.normalizer (Y : Set G)) :
    Claim153Normal A (lB A) := by
  intro Y hY M hM
  by_cases hE : HasFaithfulE9 Y
  · exact claim153NormalE9_of h h152 Y hY hE M hM
  · exact hno Y hY hE M hM

@[expose] noncomputable def Step156ONR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156ON A (lB A)

@[expose] noncomputable def Step156DR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156D A (lB A)

@[expose] noncomputable def Step156CQR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step156CQ A (lB A)

@[expose] noncomputable def Item159R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Item159 A c L

variable {G : Type} [Group G] [Finite G]

theorem rank3II_15_12_of_main (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (hM22L3 : ∀ (p e : ℕ) [Fact p.Prime], ¬ Sec4.IsoLThreePi CFSG.Blueprint.NativeSporadic.M22 p e)
    (hM22E : ∀ (p f : ℕ) [Fact p.Prime], ¬ IsLThreeEpsAt CFSG.Blueprint.NativeSporadic.M22 p f)
    (hM22A7 : IsEmpty (CFSG.Blueprint.NativeSporadic.M22 ≃* alternatingGroup (Fin 7)))
    (hM22M12 : IsEmpty (CFSG.Blueprint.NativeSporadic.M22 ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hM22J2 : IsEmpty (CFSG.Blueprint.NativeSporadic.M22 ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hM22s : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M22)
    (hgen : KS15M22Gen) {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h159 : Item159 A c L) (h1411 : Item1411_1 A (lB A)) (h153 : Item153Main A (lB A))
    (hobs : Claim153Obs A (lB A)) : Item1512 A (lB A) L := by
  intro hM22 Y hY hYL
  obtain ⟨-, h9, hirr⟩ :=
    irreducibleOn_of_m22 h131 hspor hSLC hM22L3 hM22M12 hM22J2 h.toSec13Data hM22
  obtain ⟨φ⟩ := hM22
  have hWH : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rcases h159 hirr h9 with hW | ⟨⟨ψ⟩, -⟩ | ⟨⟨ψ⟩, -⟩
    · exact hW
    · exact (hM22A7.false (φ.symm.trans ψ)).elim
    · exact (hM22E 2 2 (Or.inl ⟨φ.symm.trans ψ⟩)).elim
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  have hbot : (⊥ : Subgroup G) ∈ scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2))) hbot
  have hSG : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := ((h153 Y hY).2.1 S hS).1
  have hSY : S ≤ Subgroup.normalizer (Y : Set G) := hobs Y hY S hS
  have hSH := inf_mem_scriptQPiStar_of_transOn (isNaturalFamily_lB A) hWH h1411 hSG
  have hLN : L ≤ Subgroup.normalizer (Y : Set G) := by
    refine (hgen G A c L h ⟨φ⟩ Y hY hYL _ hSH).trans (sup_le ?_ ?_)
    · exact inf_le_left.trans (inf_le_left.trans hSY)
    · exact inf_le_right.trans Subgroup.le_normalizer
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hO2 : CFSG.pCore 2 ↥Y ≠ ⊤ := by
    intro h2
    obtain ⟨-, -, -, hq⟩ := hY4
    obtain ⟨-, hs, -⟩ := hq
    have hnt := hs.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : (↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    apply hx
    rw [(QuotientGroup.eq_one_iff y).mpr (h2 ▸ Subgroup.mem_top y)]
    rfl
  have h3Y : 3 ∣ Nat.card Y := (three_dvd_card_quotient_of_eq_oPrimeResidualOf hY4.2.1
    (CFSG.pCore 2 ↥Y) hO2).trans (Subgroup.card_quotient_dvd_card _)
  have hLYN : L ⊓ Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hdvd : Nat.card Y ∣ Nat.card ↥(L ⊓ Y) * Nat.card ↥(CFSG.Open.pCoreOf 2 Y) := by
    conv_lhs => rw [hYL]
    exact card_sup_dvd_card_mul hLYN
  have hcop : Nat.Coprime 3 (Nat.card ↥(CFSG.Open.pCoreOf 2 Y)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have h3LY : 3 ∣ Nat.card ↥(L ⊓ Y) := hcop.dvd_of_dvd_mul_right (h3Y.trans hdvd)
  have hLY := le_of_le_normalizer_of_theta (Sec6.isPerfect_of_mem_thetaComponentsAt
    h.mem_thetaComponentsAt) φ.isSimpleGroup hLN h3LY
  refine le_antisymm ?_ (sup_le hLY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
  conv_lhs => rw [hYL]
  exact sup_le_sup_right inf_le_left _

end CFSG.RankThree.PartTwo.Sec15
