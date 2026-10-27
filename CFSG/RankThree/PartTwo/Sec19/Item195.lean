module

public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
import CFSG.RankThree.PartTwo.Sec13.Item136
import CFSG.RankThree.PartTwo.Sec13.Item136E
public import CFSG.RankThree.PartTwo.Late.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18

variable {G : Type} [Group G] [Finite G]

theorem exists_ctx195 (h1730 : Sec17.Item1730) (h131 : Item131) (hspor : SporadicModels131)
    (hG : Sec19Std G) {A : Subgroup G} (hA : A ∈ partTwoE G) (hAT : A ∉ partTwoT G)
    (hS : ¬ HypS A) : ∃ (c : G) (L E M : Subgroup G), Ctx195 G A c L E M := by
  have hst := hG.toPartTwoStanding
  have hFE : partTwoF G = partTwoE G :=
    (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hG.partTwoS_eq).1
  obtain ⟨c, hc, L, hL, hcL⟩ : ∃ c : G, Subgroup.zpowers c ∈ omegaA A ∧ ∃ L ∈ lA A c, c ∈ L := by
    by_contra h
    push Not at h
    exact hS ⟨hA, hAT, h⟩
  have hD : Sec13Data G A c L := ⟨hst, hG.partTwoS_eq, hFE ▸ hA, hAT, hc, hL⟩
  obtain ⟨h7, -, hEcl⟩ := case7_of_mem h131 hspor hD hcL
  obtain ⟨U, hzU, hU9, hU3, hUΛ, hUΛz, hAbU⟩ : ∃ U : Subgroup (lBarA c L A),
      mkC (L := L) hD.mem_A ∈ U ∧ 9 ≤ Nat.card U ∧ (∀ x ∈ U, x ^ 3 = 1) ∧
      (∀ u ∈ U, ∀ l ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A), u * l = l * u) ∧
      (∀ u ∈ U, u ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) →
        u ∈ Subgroup.zpowers (mkC (L := L) hD.mem_A)) ∧
      (∀ a ∈ (aBarHom hD).range, ∀ u ∈ U,
        a * u * a⁻¹ * u⁻¹ ∈ Subgroup.zpowers (mkC (L := L) hD.mem_A)) := by
    rcases h7 with hSL | ⟨hH, hlist⟩
    · exact exists_U_of_isSLThreePiTwo hD hcL hSL
    · have hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
        rcases hlist with h | h | h
        · exact card_center_of_isSLThreePi h
        · exact h.1
        · exact h.1
      exact exists_U_of_isHeisCentral hD hcL hH hZ3
  obtain ⟨E, hEle, hEab, hE27, hEθ, hEL, hAE⟩ :=
    exists_E_of_U hD hcL hzU hU9 hU3 hUΛ hUΛz hAbU
  obtain ⟨hEF, hEcl'⟩ := hEcl E hEle hEab hE27 hEθ hEL
  have hEE : E ∈ partTwoE G := hFE ▸ hEF
  have hET : E ∈ partTwoT G := by
    by_contra hET
    obtain ⟨-, -, e, -, -, hΩ, I, hI, ⟨φI⟩⟩ := hEcl' hET
    have he : Subgroup.zpowers e ∈ omegaA E := by
      rw [hΩ]
      exact ⟨1, A.one_mem, (map_conj_one _).symm⟩
    have hIl : I ∈ lA E e := hI ▸ Set.mem_singleton I
    exact (h1730 G hst hG.partTwoS_eq E hEE hET e he I hIl).2.false φI
  obtain ⟨-, M, hM⟩ := mem_partTwoT_iff.mp hET
  exact ⟨c, L, E, M,
    { hG with
      mem_partTwoE := hA
      not_mem_partTwoT := hAT
      zpowers_mem_omegaA := hc
      mem_lA := hL
      mem_L := hcL
      le_sup := hEle
      isE27 := ⟨hEab, hE27⟩
      centralizer_noncyclic := hEθ
      inf_noncyclic := hEL
      le_normalizer := hAE
      mem_partTwoT := hET
      mem_scriptM := hM }⟩

theorem rank3II_19_5_of (h1730 : Sec17.Item1730) (h131 : Item131) (hspor : SporadicModels131)
    (h181 : Item181_1) (h1812 : Item181_2) (h196 : Step196) (h198 : Step198)
    (h198D : Step198D) (h199 : Step199) (h1910O2 : Step1910O2) (h1910 : Step1910)
    (h1911 : Step1911) (h1911E : Step1911End) : Item195 := by
  intro G _ _ hG A hA hAT
  by_contra hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, L, E, M, hctx⟩ := exists_ctx195 h1730 h131 hspor hG hA hAT hS
  have hE := hctx.isE27
  have hD9 := h198D G A c L E M hctx
  have hDE : E ⊓ A ≤ E := inf_le_left
  have hD3 : IsPGroup 3 (E ⊓ A : Subgroup G) := hE.isPGroup.to_le hDE
  have hDab : CFSG.Assembly.IsElemAbelian 3 (E ⊓ A : Subgroup G) := isElemAbelian_of_le hE.1 hDE
  have hEM : E ≤ M := le_of_mem_scriptM_gamma hE hctx.mem_scriptM
  have h9 := h199 G A c L E M hctx
  rw [gammaOne_le_iff hD3] at h9
  push Not at h9
  obtain ⟨X, hXD, hX1, hXM⟩ := h9
  have hND : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_gamma hDE (two_le_pRank_of_elemAbelian hDab hD9.ge)).trans hctx.mem_scriptM.2
  have hXne : X ≠ E ⊓ A := fun h => hXM (h ▸ hND)
  have hX3 : Nat.card X = 3 := by
    have hdvd : Nat.card X ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hD9]
      exact Subgroup.card_dvd_of_le hXD
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hk, pow_zero])) hX1
    · rw [hk, pow_one]
    · exact absurd (Subgroup.eq_of_le_of_card_ge hXD (by rw [hk, hD9]; norm_num)) hXne
  obtain ⟨d, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hX1
  have hdD : (d : G) ∈ E ⊓ A := hXD d.2
  have hdo : orderOf (d : G) = 3 := by
    have h3 : (d : G) ^ 3 = 1 := hDab.2 _ hdD
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one h3) with h | h
    · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h)) hd1
    · exact h
  have hXd : X = Subgroup.zpowers (d : G) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr d.2) ?_).symm
    rw [Nat.card_zpowers, hdo, hX3]
  have hd1' : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdc : (d : G) ∉ Subgroup.zpowers c := by
    intro hdc
    apply hXM
    have hXc : X = Subgroup.zpowers c := by
      rw [hXd]
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdc) ?_
      rw [hctx.zpowers_mem_omegaA.2.1, Nat.card_zpowers, hdo]
    rw [hXc]
    exact h196 G A c L E M hctx
  have hCd : ¬ Subgroup.centralizer ({(d : G)} : Set G) ≤ M := by
    intro hle
    apply hXM
    intro t ht
    refine mem_of_map_conj_le hG.hyp191 hE hctx.mem_scriptM ?_
    rintro _ ⟨e, he, rfl⟩
    apply hle
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hd' : t⁻¹ * (d : G) * t ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) d).mp d.2
      simpa [mul_assoc] using this
    have hcomm : e * (t⁻¹ * (d : G) * t) = (t⁻¹ * (d : G) * t) * e :=
      congrArg Subtype.val (hE.1.1.is_comm.comm ⟨e, he⟩ ⟨_, hDE (hXD hd')⟩)
    change t * e * t⁻¹ * (d : G) = (d : G) * (t * e * t⁻¹)
    calc t * e * t⁻¹ * (d : G) = t * (e * (t⁻¹ * (d : G) * t)) * t⁻¹ := by group
      _ = t * ((t⁻¹ * (d : G) * t) * e) * t⁻¹ := by rw [hcomm]
      _ = (d : G) * (t * e * t⁻¹) := by group
  have hO2 := h1910O2 G A c L E M hctx d hdD hdc hCd
  have h18 : Sec18Std G E M :=
    ⟨hG.toPartTwoStanding, hG.partTwoS_eq, hctx.mem_partTwoT.1, hctx.mem_scriptM⟩
  have hQ := pCoreOf_centralizer_ne_bot h181 h1812 hG.hyp191 h18 (hDE hdD) hd1' hO2
  set Y := Subgroup.centralizer ({(d : G)} : Set G) with hY
  obtain ⟨H, hH, -⟩ := exists_mem_scriptM_of_isTwoLocal (X := (Y : Set G))
    (H := Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G))
    ⟨CFSG.Open.pCoreOf 2 Y, hQ, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y, rfl⟩
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hHM : H ≠ M := fun h => hCd (fun x hx => h ▸ hH.2 hx)
  obtain ⟨K, hK, hLK, hK8⟩ := h198 G A c L E M hctx
  have hKJ := h1910 G A c L E M hctx K hK hLK hK8 d hdD hdc hCd H hH hHM
  obtain ⟨hKL, hpar⟩ := h1911 G A c L E M hctx K hK hLK hK8 d hdD hdc H hH hHM hKJ
  exact h1911E G A c L E M hctx K hK hLK hKL d hdD hdc H hH hHM hKJ hpar

end CFSG.RankThree.PartTwo.Sec19
