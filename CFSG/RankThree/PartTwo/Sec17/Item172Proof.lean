module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec14.Concl142HJ

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def xb172 (A : Subgroup G) (b : G) : Subgroup G :=
  pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
    oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G)))

@[expose] noncomputable def xB172 (A B : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), xb172 A b

end Defs

@[expose] noncomputable def Item171S17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item171 A (lB A)

@[expose] noncomputable def Step172Perm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Item1514 A (lB A) c L → ∀ B : Subgroup G, IsHyperplane A B →
      Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (xB172 A B : Set G)

namespace Proof172

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCoreOf_centralizer_mem_scriptQ {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A) {b : G} (hb : b ∈ A) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ∈ scriptQ A LB := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) with hO
  have hcop : Nat.Coprime 3 (Nat.card O) := coprime_card_pPrimeCoreOf 3 _
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hON : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hOb : O ≤ Subgroup.centralizer ({b} : Set G) := pPrimeCoreOf_le 3 _
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three O).mpr
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop), hAb.trans hON, fun B hB => ?_⟩
  by_cases hbB : b ∈ B
  ·
    have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)
    have hle : O ⊓ Subgroup.centralizer (B : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) :=
      le_pPrimeCoreOf inf_le_right
        (Late.le_normalizer_inf (hCB.trans hON) Subgroup.le_normalizer)
        (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop)
    exact hle.trans (le_sup_left.trans le_sup_left)
  ·
    have hAle : A ≤ B ⊔ Subgroup.zpowers b := le_sup_zpowers_of_not_mem hA hB hb hbB
    have hCA : O ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (A : Set G) :=
      fun x hx => mem_centralizer_of_le_sup hAle hx.2 (hOb hx.1)
    have hCAb : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb)
    have hle : O ⊓ Subgroup.centralizer (A : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
      le_pPrimeCoreOf inf_le_right
        (Late.le_normalizer_inf (hCAb.trans hON) Subgroup.le_normalizer)
        (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop)
    exact (le_inf inf_le_left hCA |>.trans hle).trans (le_sup_right.trans le_sup_left)

omit [Finite G] in
theorem delta_le_of_forall {A : Subgroup G} {LB : Subgroup G → Subgroup G} {M : Subgroup G}
    (hQ : ∀ Q ∈ scriptQ A LB, Q ≤ M) (Y : Subgroup G) : delta A LB Y ≤ M :=
  sSup_le fun Q hQY => hQ Q hQY.1

theorem xb172_le {A : Subgroup G} (hA : Late.IsE27 A) {M : Subgroup G}
    (hQ : ∀ Q ∈ scriptQ A (lB A), Q ≤ M) {b : G} (hb : b ∈ A) : xb172 A b ≤ M :=
  sup_le (hQ _ (pPrimeCoreOf_centralizer_mem_scriptQ hA hb))
    ((Subgroup.map_subtype_le _).trans (delta_le_of_forall hQ _))

theorem xB172_le {A B : Subgroup G} (hA : Late.IsE27 A) (hBA : B ≤ A) {M : Subgroup G}
    (hQ : ∀ Q ∈ scriptQ A (lB A), Q ≤ M) : xB172 A B ≤ M :=
  iSup_le fun _ => iSup_le fun hb => iSup_le fun _ => xb172_le hA hQ (hBA hb)

theorem le_xB172 {A B Y₀ : Subgroup G} (hA : Late.IsE27 A) (hB : IsHyperplane A B)
    (h171 : Y₀ ≤ ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
      ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)), A⁆ ⊔
        oPrimeResidualOf 3 (delta A (lB A) (Subgroup.centralizer ({b} : Set G)))) :
    Y₀ ≤ xB172 A B := by
  refine h171.trans (iSup_le fun b => iSup_le fun hbB => iSup_le fun hb1 => ?_)
  have hb : b ∈ A := hB.1 hbB
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hcomm : ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)), A⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hAb.trans (le_normalizer_pPrimeCoreOf 3 _))
  refine le_trans ?_ (le_iSup_of_le b (le_iSup_of_le hbB (le_iSup_of_le hb1 le_rfl)))
  exact sup_le_sup_right hcomm _

theorem mem_scriptM_of_std {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) :
    Subgroup.normalizer (Y₀ : Set G) ∈
      CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) := by
  rw [h.scriptM_eq]
  exact Set.mem_singleton _

theorem le_M_of_le_normalizer {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {X K : Subgroup G} (hYX : Y₀ ≤ X)
    (hXM : X ≤ Subgroup.normalizer (Y₀ : Set G)) (hAK : A ≤ K)
    (hK : K ≤ Subgroup.normalizer (X : Set G)) : K ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.Open.pCoreOf 2 X with hP
  have hY2 : CFSG.Open.pCoreOf 2 Y₀ ≠ ⊥ := h.mem_y0Star.prop.2.2
  have hO2 : CFSG.Open.pCoreOf 2 Y₀ ≤ P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀).trans hYX)
      (hXM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀)
  have hP1 : P ≠ ⊥ := fun hbot => hY2 (le_bot_iff.mp (hbot ▸ hO2))
  have hloc : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (P : Set G)) :=
    ⟨P, hP1, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X, rfl⟩
  have hXN : X ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hKN : K ≤ Subgroup.normalizer (P : Set G) :=
    hK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hsub : ((Y₀ ⊔ A : Subgroup G) : Set G) ⊆ Subgroup.normalizer (P : Set G) :=
    SetLike.coe_subset_coe.mpr (sup_le (hYX.trans hXN) (hAK.trans hKN))
  obtain ⟨M', hM', hle⟩ := exists_mem_scriptM_of_isTwoLocal hloc hsub
  change M' ∈ CFSG.maximalTwoLocalsContaining _ at hM'
  rw [h.scriptM_eq] at hM'
  rw [← Set.mem_singleton_iff.mp hM']
  exact hKN.trans hle

theorem eq_or_isHyperplane {A B : Subgroup G} (hA : Late.IsE27 A) (hBA : B ≤ A)
    (hB : 2 ≤ CFSG.Open.pRank 3 B) : B = A ∨ IsHyperplane A B := by
  have hlog := CFSG.RankThreeEvenClassification.Helpers.pRank_le_log_card 3 Nat.prime_three B
  have hdvd : Nat.card B ∣ 27 := hA.2 ▸ Subgroup.card_dvd_of_le hBA
  have hmem : Nat.card B ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 27 = {1, 3, 9, 27} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h3 | h9 | h27
  · rw [h1] at hlog
    simp at hlog
    omega
  · rw [h3] at hlog
    have : Nat.log 3 3 = 1 := by simpa using Nat.log_pow (b := 3) (by norm_num) 1
    omega
  · exact Or.inr ⟨hBA, by rw [hA.2, h9]⟩
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hBA (by rw [h27, hA.2]))

end Proof172

section Item172

variable {G : Type} [Group G] [Finite G]

open Proof172 in
theorem rank3II_17_2_of {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (h171 : Item171 A (lB A))
    (hperm : ∀ B : Subgroup G, IsHyperplane A B →
      Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (xB172 A B : Set G)) :
    Item172 A (lB A) := by
  intro Y hY
  obtain rfl : Y = Y₀ := h.eq_of_mem_y0Star hY
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  by_contra hcon
  push Not at hcon
  have hNB : ∀ B : Subgroup G, IsHyperplane A B →
      Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
    intro B hB
    have hAB : A ≤ Subgroup.normalizer (B : Set G) := fun a ha =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hB.1 hx⟩ ⟨a, ha⟩))
    exact le_M_of_le_normalizer h (le_xB172 hA hB (h171 Y hY B hB))
      (xB172_le hA hB.1 hcon) hAB (hperm B hB)
  have hΓ : gamma 2 A ≤ Subgroup.normalizer (Y : Set G) := by
    refine gamma_le_iff.mpr fun B hBA hB2 => ?_
    rcases eq_or_isHyperplane hA hBA hB2 with rfl | hB
    · exact h.normalizer_le
    · exact hNB B hB
  refine h.not_mem_partTwoT (mem_partTwoT_iff.mpr ⟨h.toSec13Data.mem_partTwoE, ?_⟩)
  exact ⟨Subgroup.normalizer (Y : Set G), (mem_scriptM_of_std h).1,
    SetLike.coe_subset_coe.mpr hΓ⟩

theorem item172S17_of (h171 : Item171S17) (h1514 : Item1514S17) (hperm : Step172Perm) :
    Item172S17 :=
  fun G _ _ A c L Y₀ h => rank3II_17_2_of h (h171 G A c L Y₀ h)
    (hperm G A c L Y₀ h (h1514 G A c L Y₀ h))

end Item172

end CFSG.RankThree.PartTwo.Sec17
