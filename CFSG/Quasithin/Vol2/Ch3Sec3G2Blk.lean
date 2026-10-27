module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3331E4
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Quasithin.Recognition.CertU33Simple
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Vol2.KGNatVec
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.Vol2.Ch10StatementsB
public import CFSG.Quasithin.Vol2.Ch11SecA11Arith
public import CFSG.Quasithin.Vol2.Ch11SecBFacts
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.Walter.Bender1970.S2.Subnormal
public import CFSG.Walter.Bender1970.S2.TwoSubgroup
public import CFSG.Walter.J1
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

namespace G2Blk

theorem isSimple_of_isPSU
    {Q : Type} [Group Q] (h : IsPSU 3 3 1 Q) :
    IsSimpleGroup Q :=
  (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _ h).2

variable {G : Type} [Group G]

theorem bijective_autOn [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) {T M L D : Subgroup G} (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hG2 : IsG2Block L) :
    ∃ (hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G))
      (hO : CFSG.pCore 2 ↥L ≤ (InternalSec.autOnHom hLV).ker),
      Function.Bijective (QuotientGroup.lift _ (InternalSec.autOnHom hLV) hO) := by
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hO : CFSG.pCore 2 ↥L ≤ (InternalSec.autOnHom hLV).ker := by
    intro x hx
    rw [InternalSec.mem_ker_autOnHom]
    have hx' : x ∈ CFSG.Open.pCore 2 ↥L := by
      exact hx
    exact hQV (hOQ ⟨x, hx', rfl⟩)
  refine ⟨hLV, hO, ?_⟩
  set ψ := QuotientGroup.lift _ (InternalSec.autOnHom hLV) hO with hψ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := InternalSec.autOnHom_surjective hLV y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := isSimple_of_isPSU hG2.2.1
  have hnt : Nontrivial ↥(autOn L (vPlus L T)) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply h.not_L_le_centralizer h38 h39
    intro ℓ hℓ
    have h1 : (⟨ℓ, hℓ⟩ : ↥L) ∈ (InternalSec.autOnHom hLV).ker := Subsingleton.elim _ _
    exact (InternalSec.mem_ker_autOnHom hLV _).mp h1
  refine ⟨(MonoidHom.ker_eq_bot_iff ψ).mp ?_, hψs⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(autOn L (vPlus L T)))
    obtain ⟨g, rfl⟩ := hψs x
    exact hx (MonoidHom.mem_ker.mp (h1 ▸ Subgroup.mem_top g))

theorem card_autOn [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) {T M L D : Subgroup G} (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hG2 : IsG2Block L) :
    Nat.card ↥(autOn L (vPlus L T)) = 6048 := by
  obtain ⟨hLV, hO, hbij⟩ := bijective_autOn h38 h39 h hTL hG2
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  exact card_of_statedClassicalModel_psu_three_three hG2.2.1

theorem mem_pCore_of_mem_centralizer [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) {T M L D : Subgroup G} (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hG2 : IsG2Block L) {ℓ : G} (hℓ : ℓ ∈ L)
    (hℓV : ℓ ∈ Subgroup.centralizer (vPlus L T : Set G)) :
    (⟨ℓ, hℓ⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
  obtain ⟨hLV, hO, hbij⟩ := bijective_autOn h38 h39 h hTL hG2
  have h1 : QuotientGroup.lift _ (InternalSec.autOnHom hLV) hO
      (QuotientGroup.mk (⟨ℓ, hℓ⟩ : ↥L)) = 1 := by
    show InternalSec.autOnHom hLV ⟨ℓ, hℓ⟩ = 1
    exact (InternalSec.mem_ker_autOnHom hLV _).mpr hℓV
  have h2 := hbij.1 (h1.trans (map_one _).symm)
  exact (QuotientGroup.eq_one_iff _).mp h2

theorem sl2_ne (n : ℕ) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 6048 := by
  intro h
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> norm_num at h
  · have h1 : 32 ≤ 2 ^ n := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : 32 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left h1 2) 1
    have h3 := Nat.mul_le_mul h1 h2
    rw [h] at h3
    norm_num at h3

theorem sl3_ne (n : ℕ) : (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ≠ 6048 := by
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h
  · have h1 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : 4 ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h1 3
    have h3 : 4 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left h1 2) 1
    have h4 : 4 ^ 3 - 1 ≤ (2 ^ n) ^ 3 - 1 := Nat.sub_le_sub_right h2 1
    have h5 := Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h4)
    rw [h] at h5
    norm_num at h5

theorem sp4_ne {n : ℕ} (hn : 1 < n) :
    (2 ^ n) ^ (2 ^ 2) * ∏ j ∈ Finset.Icc 1 2, ((2 ^ n) ^ (2 * j) - 1) ≠ 6048 := by
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  intro h
  have h1 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 4 ^ (2 ^ 2) ≤ (2 ^ n) ^ (2 ^ 2) := Nat.pow_le_pow_left h1 _
  have h3 : 4 ^ (2 * 1) - 1 ≤ (2 ^ n) ^ (2 * 1) - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_left h1 _) 1
  have h4 : 4 ^ (2 * 2) - 1 ≤ (2 ^ n) ^ (2 * 2) - 1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_left h1 _) 1
  have h5 := Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h4)
  rw [h] at h5
  norm_num at h5

theorem g2_ne {n : ℕ} (hn : 1 < n) :
    (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ 6048 := by
  intro h
  have h1 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h2 : 4 ^ 6 ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left h1 6
  have h3 : 4 ^ 6 - 1 ≤ (2 ^ n) ^ 6 - 1 := Nat.sub_le_sub_right h2 1
  have h4 : 4 ^ 2 - 1 ≤ (2 ^ n) ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left h1 2) 1
  have h5 := Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h4)
  rw [h] at h5
  norm_num at h5

theorem exists_ne_zero_one {K : Type} [Field K] [Finite K] (hK : 2 < Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun x : K => decide (x = 0)) := by
    intro a b hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · simp [ha, hb] at hab
    · simp [ha, hb] at hab
    · rw [hcon a ha, hcon b hb]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem exists_g2Natural [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) {T M L D : Subgroup G}
    (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hG2 : IsG2Block L) :
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      G2NaturalDerived (V := ↥(vPlus L T)) (autOn L (vPlus L T)) (tildeComm L T L)
        (cvPlus L T) 1 := by
  have h6048 := card_autOn h38 h39 h hTL hG2
  have hMp := Hyp331.mPlus_eq_of_le (L := L) (T := T) hTL
  obtain ⟨hc, hcases⟩ := h.lemma_3_3_8_of_le h38 h39 h51 hTL
  refine ⟨hc, ?_⟩
  have hcard : ∀ {X : Type} [Group X], (↥(autOn (mPlus L T) (vPlus L T)) ≃* X) →
      Nat.card X = 6048 := by
    intro X _ e
    rw [← Nat.card_congr e.toEquiv, hMp]
    exact h6048
  rcases hcases with h1 | ⟨n, -, -, hBN⟩ | (⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩) | h4 | ⟨⟨e⟩, -⟩ |
      ⟨-, hZ3, ⟨e⟩, -⟩ | ⟨n, hn, ⟨e⟩, -⟩
  · obtain ⟨t, ht, htN, -⟩ := h1
    exact absurd (hTL ht) htN
  · obtain ⟨F, _, _, hF, π, hπ⟩ := hBN
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [hMp, h6048, card_statedSL_two1527d, hF] at h1
    exact absurd h1.symm (sl2_ne n)
  · have h1 := hcard e
    rw [card_alternatingGroup1527d 5 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
  · have h1 := hcard e
    rw [card_alternatingGroup1527d 7 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
  · unfold Case3_3_8_four at h4
    rcases h4 with ⟨n, K, _, _, hK, ⟨e⟩, -⟩ | ⟨n, K, _, _, hn, hK, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
        ⟨n, K, _, _, hK, ⟨e⟩, hreal⟩
    · have h1 := hcard e
      rw [card_statedSL_three1527d, hK] at h1
      exact absurd h1 (sl3_ne n)
    · have h1 := hcard e
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK] at h1
      exact absurd h1 (sp4_ne hn)
    · have h1 := hcard e
      rw [card_alternatingGroup1527d 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have hn1 : n = 1 := by
        have h1 := hcard e
        rcases Nat.lt_or_ge n 2 with hn | hn
        · interval_cases n
          · rw [pow_zero] at hK
            exact absurd hK (Finite.one_lt_card (α := K)).ne'
          · rfl
        · exfalso
          have := FFC.charP_two_of_card_pow hK
          have h2 : 2 < Nat.card K := by
            rw [hK]
            calc 2 < 2 ^ 2 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
          obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one h2
          rw [CFSG.Quasithin.Vol2.KGNat.commutator_quasithinG2_eq hc0 hc1,
            ← CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
            card_quasithinG2_1527d hK, hK] at h1
          exact g2_ne (by omega) h1
      subst hn1
      rw [hMp] at hreal
      exact hreal
  · have h1 := hcard e
    rw [card_alternatingGroup1527d 7 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(autOn (mPlus L T) (vPlus L T)))
    rw [Nat.card_congr e.toEquiv, hZ3, card_alternatingGroup1527d 6 (by norm_num), hMp,
      h6048] at h1
    norm_num [Nat.factorial] at h1
  · have h1 := hcard e
    rcases hn with rfl | rfl
    · rw [CFSG.QuasithinUnique.Bridge.card_sl4] at h1
      norm_num at h1
    · rw [CFSG.QuasithinUnique.Bridge.card_sl5] at h1
      norm_num at h1

end G2Blk

end CFSG.Quasithin.H13
