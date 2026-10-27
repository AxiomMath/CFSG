module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1VDefs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1MidGrp
import CFSG.RankThree.PartTwo.Sec15.Sylow155Swap
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.GH74.GLS.C3.Layer1.St1Iv251
public import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec14.Item146General
public import CFSG.RankThree.PartTwo.Sec15.Item153Claims
public import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofCases

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem exists_mul_pow_eq_of_mem_normalizer' {H : Subgroup G} {a b : G} (ha : a ∈ H)
    (hb : b ∈ Subgroup.normalizer (H : Set G)) (n : ℕ) :
    ∃ a' ∈ H, (a * b) ^ n = a' * b ^ n := by
  induction n with
  | zero => exact ⟨1, H.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨a', ha', h⟩ := ih
    have hbn : b ^ n ∈ Subgroup.normalizer (H : Set G) := Subgroup.pow_mem _ hb n
    have h2 : b ^ n * a * (b ^ n)⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hbn a).mp ha
    refine ⟨a' * (b ^ n * a * (b ^ n)⁻¹), H.mul_mem ha' h2, ?_⟩
    rw [pow_succ, h]
    group

omit [Finite G] in
private theorem mem_of_mem_sup_of_odd_orderOf {H K : Subgroup G} (hK : IsPGroup 2 ↥K)
    (hKN : K ≤ Subgroup.normalizer (H : Set G)) {y : G} (hy : y ∈ H ⊔ K)
    (ho : Odd (orderOf y)) : y ∈ H := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left H K hKN] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hy
  obtain ⟨k, hk⟩ := hK ⟨b, hb⟩
  have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨a', ha', h⟩ := exists_mul_pow_eq_of_mem_normalizer' ha (hKN hb) (2 ^ k)
  have hpow : (a * b) ^ 2 ^ k ∈ H := by
    rw [h, hbk, mul_one]
    exact ha'
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr ho))
  rw [← hm]
  exact H.pow_mem hpow m

private theorem odd_orderOf_of_coprime {O : Subgroup G} (hO : Nat.Coprime 2 (Nat.card O))
    {g : G} (hg : g ∈ O) : Odd (orderOf g) :=
  Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hg) hO)

private theorem pPrimeCoreOf_two_eq_bot {M : Subgroup G} (hM : IsCharacteristicP 2 ↥M) :
    pPrimeCoreOf 2 M = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pPrimeCoreOf, CFSG.pPrimeCore_eq_bot_of_isCharacteristicP ↥M 2 hM, Subgroup.map_bot]

theorem pPrimeCoreOf_two_le_centralizer_of_normalizes {M E H₀ : Subgroup G} (hEM : E ≤ M)
    (hME : M ≤ Subgroup.normalizer (E : Set G)) (hM : pPrimeCoreOf 2 M = ⊥) (hH₀M : H₀ ≤ M)
    (hEH₀ : E ≤ Subgroup.normalizer (H₀ : Set G)) :
    pPrimeCoreOf 2 H₀ ≤ Subgroup.centralizer (E : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEO : E ≤ Subgroup.normalizer (pPrimeCoreOf 2 H₀ : Set G) :=
    hEH₀.trans (normalizer_le_normalizer_pPrimeCoreOf 2 H₀)
  have hOE : pPrimeCoreOf 2 E = ⊥ := by
    refine le_bot_iff.mp (le_trans ?_ hM.le)
    exact le_pPrimeCoreOf ((pPrimeCoreOf_le 2 E).trans hEM)
      (hME.trans (normalizer_le_normalizer_pPrimeCoreOf 2 E)) (coprime_card_pPrimeCoreOf 2 E)
  have hDE : pPrimeCoreOf 2 H₀ ⊓ E ≤ pPrimeCoreOf 2 E :=
    le_pPrimeCoreOf inf_le_right (Late.le_normalizer_inf hEO Subgroup.le_normalizer)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 2 H₀))
  intro o ho
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h1 : e * o * e⁻¹ ∈ pPrimeCoreOf 2 H₀ :=
    (Subgroup.mem_normalizer_iff.mp (hEO he) o).mp ho
  have h2 : o * e⁻¹ * o⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hME (hH₀M (pPrimeCoreOf_le 2 H₀ ho))) e⁻¹).mp (inv_mem he)
  have hc : e * o * e⁻¹ * o⁻¹ ∈ pPrimeCoreOf 2 H₀ ⊓ E := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem h1 (inv_mem ho), ?_⟩
    have e1 : e * o * e⁻¹ * o⁻¹ = e * (o * e⁻¹ * o⁻¹) := by group
    rw [e1]
    exact mul_mem he h2
  have h3 := hDE hc
  rw [hOE, Subgroup.mem_bot] at h3
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)

theorem eq_bot_of_le_centralizer_wE {M E O : Subgroup G} (hM : IsCharacteristicP 2 ↥M)
    (hME : M ≤ Subgroup.normalizer (E : Set G)) (hO : Nat.Coprime 2 (Nat.card O)) (hOM : O ≤ M)
    (hOE : O ≤ Subgroup.centralizer (E : Set G))
    (hOW : O ≤ Subgroup.centralizer
      ((CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G)) :
    O = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMC : M ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) :=
    Late.le_normalizer_inf Subgroup.le_normalizer
      fun m hm => CFSG.GH74.GLS.C3.Layer1.Iv251.mem_normalizer_centralizer (hME hm)
  have hCchar : IsCharacteristicP 2 ↥(M ⊓ Subgroup.centralizer (E : Set G)) :=
    Sec15.isCharacteristicP_of_le_normalizer inf_le_left hMC hM
  have hO2C : CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer (E : Set G)) ≤
      CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (E : Set G) :=
    le_inf (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
      (hMC.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right)
  refine eq_bot_iff.mpr fun o ho => ?_
  have hoC : o ∈ M ⊓ Subgroup.centralizer (E : Set G) := ⟨hOM ho, hOE ho⟩
  have hcent : (⟨o, hoC⟩ : ↥(M ⊓ Subgroup.centralizer (E : Set G))) ∈
      Subgroup.centralizer (CFSG.pCore 2 ↥(M ⊓ Subgroup.centralizer (E : Set G)) :
        Set ↥(M ⊓ Subgroup.centralizer (E : Set G))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzO : (z : G) ∈ CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer (E : Set G)) :=
      Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hOW ho) z (hO2C hzO))
  have ho2 : o ∈ CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.centralizer (E : Set G)) :=
    Subgroup.mem_map.mpr ⟨⟨o, hoC⟩, hCchar hcent, rfl⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨o, ho2⟩
  have hok : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (orderOf o) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (odd_orderOf_of_coprime hO ho))
  exact Subgroup.mem_bot.mpr
    (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hok)))

theorem pPrimeCoreOf_two_host_le {A X K Y M T P : Subgroup G} (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) :
    pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      pPrimeCoreOf 3 (u155 A M X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg
  have hg' : g ∈ pPrimeCoreOf 3 (u155 A M X) ⊔ CFSG.Open.pCoreOf 2 Y := by
    rw [sup_comm]
    exact delta_le _ (pPrimeCoreOf_le 2 _ hg)
  exact mem_of_mem_sup_of_odd_orderOf (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    ((Sylow155F.r_le_u155 hE hRP).trans (le_normalizer_pPrimeCoreOf 3 _)) hg'
    (odd_orderOf_of_coprime (coprime_card_pPrimeCoreOf 2 _) hg)

theorem pPrimeCoreOf_two_host_mem_scriptQ {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) {X K Y M T P : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) :
    pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ∈
      scriptQ A (lB A) :=
  mem_scriptQ_of_le (delta_mem_scriptQ h.isE27 h146 (Sylow155S.sup_mem_invariant hC hE hRP))
    (pPrimeCoreOf_le 2 _)
    ((le_normalizer_delta (A := A) (LB := lB A) _).trans
      (normalizer_le_normalizer_pPrimeCoreOf 2 _))

theorem delta_le_normalizer_delta_pPrimeCoreOf_u155 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) {X K Y M T : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) :
    delta A (lB A) M ≤
      Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 (u155 A M X)) : Set G) := by
  have hIU : delta A (lB A) M ≤ Subgroup.normalizer (pPrimeCoreOf 3 (u155 A M X) : Set G) :=
    (Sylow155B1.le_normalizer_u155 Subgroup.le_normalizer hIX).trans
      (normalizer_le_normalizer_pPrimeCoreOf 3 (u155 A M X))
  have hII : delta A (lB A) M ≤ delta A (lB A) (delta A (lB A) M) :=
    sSup_le fun _ hQ => le_delta hQ.1 (le_delta hQ.1 hQ.2)
  exact hII.trans (delta_le_normalizer_delta (fun _ hZ => delta_mem_scriptQ h.isE27 h146 hZ)
    (Sylow155B1.pPrimeCoreOf_u155_mem_invariant hC) hIU)

theorem charTwo_and_le_normalizer_oPrimeResidualOf {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h149 : Item149 A (lB A)) {X K Y M T : Subgroup G}
    (hC : Ctx155 A X K Y M T) :
    IsCharacteristicP 2 ↥M ∧
      M ≤ Subgroup.normalizer ((oPrimeResidualOf 3 (delta A (lB A) M) : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMY : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hC.mem_m.1, fun z hz => hC.mem_m.2 (by rwa [sup_comm] at hz)⟩
  obtain ⟨-, -, hM2, hF⟩ := Sec15.facts_of_mem_maximalTwoLocalsContaining h hMY
  exact ⟨(isCharacteristicP_iff_generalizedFitting_eq_pCore ↥M 2).mpr hF,
    Sec15.normalizer_le_normalizer_oPrimeResidualOf_delta h149 hM2.1⟩

theorem pPrimeCoreOf_two_host_le_centralizer {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) :
    pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer ((oPrimeResidualOf 3 (delta A (lB A) M) : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMchar, hME⟩ := charTwo_and_le_normalizer_oPrimeResidualOf h h149 hC
  have hH₀I : delta A (lB A) (pPrimeCoreOf 3 (u155 A M X)) ≤ delta A (lB A) M :=
    (delta_le _).trans ((pPrimeCoreOf_le 3 _).trans inf_le_left)
  have hO : pPrimeCoreOf 2
      (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
        pPrimeCoreOf 2 (delta A (lB A) (pPrimeCoreOf 3 (u155 A M X))) :=
    le_pPrimeCoreOf (le_delta (pPrimeCoreOf_two_host_mem_scriptQ h h146 hC hE hRP)
        (pPrimeCoreOf_two_host_le hE hRP))
      ((delta_mono le_sup_right).trans (le_normalizer_pPrimeCoreOf 2 _))
      (coprime_card_pPrimeCoreOf 2 _)
  exact hO.trans (pPrimeCoreOf_two_le_centralizer_of_normalizes
    ((Sec14.oPrimeResidualOf_le_self 3 _).trans (delta_le M)) hME (pPrimeCoreOf_two_eq_bot hMchar)
    (hH₀I.trans (delta_le M))
    ((Sec14.oPrimeResidualOf_le_self 3 _).trans
      (delta_le_normalizer_delta_pPrimeCoreOf_u155 h h146 hC hIX)))

theorem pPrimeCoreOf_two_host_eq_bot_of_wE155_mem {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hW : wE155 A M ∈ scriptQ A (lB A)) :
    pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMchar, hME⟩ := charTwo_and_le_normalizer_oPrimeResidualOf h h149 hC
  obtain ⟨-, hRH, -, -⟩ := Sylow155B1.delta_host_facts h h146 hC hE hRP
    (Sylow155S.sup_mem_invariant hC hE hRP) (Sylow155S.sup_le_u155 hE hRP)
    (Sylow155S.p_le_normalizer_sup hE) le_sup_left
  have hHI : delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) ≤
      delta A (lB A) M :=
    (delta_le _).trans ((Sylow155S.sup_le_u155 hE hRP).trans inf_le_left)
  obtain ⟨-, hIZ⟩ := Sylow155B1.delta_pCore_facts h h146 hC
  have hZH := (Sylow155B1.delta_pCore_le_r h h146 hC hE hIX).trans hRH
  have hZ2 : IsPGroup 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 M)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le (delta_le _)
  have hOZ := (pPrimeCoreOf_two_le_layerOddPreimage _).trans
    (layerOddPreimage_le_centralizer hZ2 hZH (hHI.trans hIZ))
  have hWZ : wE155 A M ≤ delta A (lB A) (CFSG.Open.pCoreOf 2 M) := le_delta hW inf_le_left
  refine eq_bot_of_le_centralizer_wE hMchar hME (coprime_card_pPrimeCoreOf 2 _)
    ((pPrimeCoreOf_le 2 _).trans (hHI.trans (delta_le M)))
    (pPrimeCoreOf_two_host_le_centralizer h h146 h149 hC hE hRP hIX) (hOZ.trans ?_)
  exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWZ)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
