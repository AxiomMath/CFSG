module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofIndex
public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAutQ8Tools
import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofL3Aut
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step2051IndexC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T →
    (∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
        projSL 3 (GaloisField 2 n)) ∧
      Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c))))) →
      ¬ 2 ∣ (M ⊓ Res6.cenK (kTwenty M c) ⊓ N).relIndex (M ⊓ Res6.cenK (kTwenty M c))

namespace Res7

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mem_normalizer_parabolic {K P : Subgroup G} (hOP : CFSG.Open.pCoreOf 2 K ≤ P)
    (hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hpar : Sec18.IsMaxParabolicRankTwo
      ((P.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))))
    {k : G} (hk : k ∈ K) (hkP : k ∈ Subgroup.normalizer (P : Set G)) : k ∈ P := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set Pb := (P.subgroupOf K).map π with hPb
  obtain ⟨hco, T, hT⟩ := hpar
  have hNP : Subgroup.normalizer (Pb : Set (↥K ⧸ CFSG.pCore 2 ↥K)) = Pb := by
    rcases hco.le_iff.mp (Subgroup.le_normalizer (H := Pb)) with h | h
    · exfalso
      have hn : Pb.Normal := Subgroup.normalizer_eq_top_iff.mp h
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Pb with hb | ht
      · have hT1 : ((T : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))) ≤ ⊥ := by
          rw [← hb]
          exact Subgroup.le_normalizer.trans hT
        have hT2 : ((T : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))) = ⊥ := le_bot_iff.mp hT1
        have h3 : Subgroup.normalizer (((T : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K))) :
            Set (↥K ⧸ CFSG.pCore 2 ↥K)) = ⊤ := by
          rw [hT2]
          exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
        rw [h3, hb] at hT
        have : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) := hsimple.toNontrivial
        exact bot_ne_top (le_bot_iff.mp hT).symm
      · exact hco.1 ht
    · exact h
  have hkb : π ⟨k, hk⟩ ∈ Subgroup.normalizer (Pb : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) z
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨k, hk⟩ * y * (⟨k, hk⟩ : K)⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy ⊢
        exact (Subgroup.mem_normalizer_iff.mp hkP _).mp hy
      · rw [map_mul, map_mul, map_inv, hyx]
    · rintro ⟨y, hy, hyx⟩
      refine ⟨(⟨k, hk⟩ : K)⁻¹ * y * ⟨k, hk⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy ⊢
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hkP) _).mp hy
        simpa [mul_assoc] using this
      · rw [map_mul, map_mul, map_inv, hyx]
        group
  rw [hNP] at hkb
  obtain ⟨p, hp, hpk⟩ := hkb
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hp
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hpk
  have h1 : ((p⁻¹ * ⟨k, hk⟩ : K) : G) ∈ P := hOP ((Sec18.mem_pCore_iff_mem_pCoreOf _).mp hpk)
  have h2 : k = (p : G) * ((p⁻¹ * ⟨k, hk⟩ : K) : G) := by simp
  rw [h2]
  exact P.mul_mem hp h1

theorem cenK_le_normalizer {K P : Subgroup G} (hOP : CFSG.Open.pCoreOf 2 K ≤ P) (hPK : P ≤ K) :
    Res6.cenK K ≤ Subgroup.normalizer (P : Set G) := by
  intro z hz
  apply Sec20.mem_normalizer_of_map_conj_le
  rintro _ ⟨p, hp, rfl⟩
  have h1 := hz.2 p (hPK hp)
  have e : (MulAut.conj z).toMonoidHom p = (z * p * z⁻¹ * p⁻¹) * p := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact P.mul_mem (hOP h1) hp

end Res7

theorem step2051IndexN_of (hC : Step2051IndexC) (h187 : Sec18.Item187) : Step2051IndexN := by
  intro G _ _ A M L N c T hT hcase
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hoddC := hC G A M L N c T hT hcase
  obtain ⟨n, hn, ⟨e⟩, hpar⟩ := hcase
  set K := kTwenty M c with hKdef
  set P := (K ⊓ N) ⊔ CFSG.Open.pCoreOf 2 K with hP
  set Y := M ⊓ Subgroup.normalizer (P : Set G) with hY
  set C := M ⊓ Res6.cenK K with hCdef
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hOK : CFSG.Open.pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hPK : P ≤ K := sup_le inf_le_left hOK
  have hOP : CFSG.Open.pCoreOf 2 K ≤ P := le_sup_right
  have hpar' : Sec18.IsMaxParabolicRankTwo
      ((P.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) := by
    rw [hP, Res6.map_sup_pCoreOf_eq inf_le_left]
    exact hpar
  have hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := by
    have : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
        (GaloisField 2 n)) :=
      CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by norm_num)
    exact (e.trans (KFacts.L34.projSLEquivProjectiveSL 3 _)).isSimpleGroup
  obtain ⟨H, hH18, hH187, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  have hMO : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hON : CFSG.Open.pCoreOf 2 K ≤ N := by
    rw [hN, hL]
    refine h187 G A M H c hH18 hH187 _ ?_
    rw [mem_invariantPiSubgroups_piCompl_iff Nat.prime_three]
    refine ⟨le_top, ?_, sup_le ((le_of_hyp201 hT.toHyp201).trans hMO)
      (((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right).trans hMO)⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Res6.coprime_card_of_isPGroup Nat.prime_three (by norm_num)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K))
  have hPN : P ≤ N := sup_le inf_le_right hON
  have hCY : C ≤ Y := fun z hz => ⟨hz.1, Res7.cenK_le_normalizer hOP hPK hz.2⟩
  have hPY : P ≤ Y := fun p hp => ⟨hKM (hPK hp), Subgroup.le_normalizer hp⟩
  have hMC : M ≤ Subgroup.normalizer (C : Set G) := fun m hm =>
    Sec20.mem_normalizer_inf_of_mem (Subgroup.le_normalizer hm)
      (Res6.normalizer_le_normalizer_cenK K (hMK hm))
  have h2el : ∀ g ∈ Y, (∃ a : ℕ, g ^ 2 ^ a = 1) → g ∈ P ⊔ C := by
    intro g hg ha
    obtain ⟨k, hk, hkC⟩ := Res6.exists_mem_cenK_of_kFact kFactL3OddParabolicInner_holds hn e
      hpar' (hMK hg.1) hg.2 ha
    have hkCP : k⁻¹ * g ∈ Subgroup.normalizer (P : Set G) := Res7.cenK_le_normalizer hOP hPK hkC
    have hkN : k ∈ Subgroup.normalizer (P : Set G) := by
      have e1 : g * (k⁻¹ * g)⁻¹ = k := by group
      rw [← e1]
      exact mul_mem hg.2 (inv_mem hkCP)
    have hkP : k ∈ P := Res7.mem_of_mem_normalizer_parabolic hOP hsimple hpar' hk hkN
    have hkgM : k⁻¹ * g ∈ M := M.mul_mem (M.inv_mem (hKM hk)) hg.1
    have e2 : g = k * (k⁻¹ * g) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup hkP ⟨hkgM, hkC⟩
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 Y
  have hSPC : S ≤ P ⊔ C := by
    intro s hs
    refine h2el s (hS.le hs) ?_
    obtain ⟨a, ha⟩ := hS.isPGroup ⟨s, hs⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  have hodd1 : ¬ 2 ∣ (P ⊔ C).relIndex Y := fun h =>
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
      (h.trans (Subgroup.relIndex_dvd_of_le_left Y hSPC))
  have hPnC : P ≤ Subgroup.normalizer (C : Set G) := (hPK.trans hKM).trans hMC
  have hPnCN : P ≤ Subgroup.normalizer ((C ⊓ N : Subgroup G) : Set G) := fun p hp =>
    Sec20.mem_normalizer_inf_of_mem (hPnC hp) (Subgroup.le_normalizer (hPN hp))
  have hc1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hPnC
  have hc2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hPnCN
  have hinf : (C ⊓ N) ⊓ P = C ⊓ P := by
    rw [inf_assoc, inf_of_le_right hPN]
  rw [hinf] at hc2
  set W := (C ⊓ N) ⊔ P with hW
  set U := C ⊔ P with hU
  have hWU : W ≤ U := sup_le_sup_right inf_le_left P
  have hr1 := Subgroup.relIndex_mul_card W U
  rw [inf_of_le_left hWU] at hr1
  have hr2 := Subgroup.relIndex_mul_card (C ⊓ N) C
  rw [inf_of_le_left inf_le_left] at hr2
  have hidx : W.relIndex U = (C ⊓ N).relIndex C := by
    have hpos : 0 < Nat.card W * Nat.card (C ⊓ P : Subgroup G) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc W.relIndex U * (Nat.card W * Nat.card (C ⊓ P : Subgroup G))
        = Nat.card U * Nat.card (C ⊓ P : Subgroup G) := by rw [← hr1]; ring
      _ = Nat.card C * Nat.card P := hc1
      _ = (C ⊓ N).relIndex C * Nat.card (C ⊓ N : Subgroup G) * Nat.card P := by rw [hr2]
      _ = (C ⊓ N).relIndex C * (Nat.card W * Nat.card (C ⊓ P : Subgroup G)) := by
        rw [hc2]; ring
  have hWN : W ≤ U ⊓ N := le_inf hWU (sup_le inf_le_right hPN)
  have hodd2 : ¬ 2 ∣ (U ⊓ N).relIndex U := fun h =>
    hoddC (hidx ▸ h.trans (Subgroup.relIndex_dvd_of_le_left U hWN))
  have hUeq : U = P ⊔ C := sup_comm C P
  have hUY : U ≤ Y := hUeq ▸ sup_le hPY hCY
  have hmul := Subgroup.relIndex_mul_relIndex (U ⊓ N) U Y inf_le_left hUY
  have hUNle : U ⊓ N ≤ M ⊓ N := inf_le_inf_right N (hUY.trans inf_le_left)
  have hdvd : (M ⊓ N).relIndex Y ∣ (U ⊓ N).relIndex Y :=
    Subgroup.relIndex_dvd_of_le_left Y hUNle
  intro h2
  have h3 : 2 ∣ (U ⊓ N).relIndex U * U.relIndex Y := by
    rw [hmul]
    exact h2.trans hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h3 with h | h
  · exact hodd2 h
  · exact hodd1 (hUeq ▸ h)

end CFSG.RankThree.PartTwo.Sec20
