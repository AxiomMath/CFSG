module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec15.Item1424Proof
import CFSG.RankThree.PartTwo.Sec15.Item1424ProofEnd
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofCent
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
public import CFSG.RankThree.PartTwo.Sec15.Item1424ProofFive
public import CFSG.RankThree.PartTwo.Sec15.Item1424ProofNotHJ
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem delta_eq_of_item143Q {A L Y : Subgroup G} {c : G} {n : ℕ}
    (hctx : Ctx1424 G A c L Y n) (h143 : Ronan148Q.Item143Q A (lB A))
    (hHJ : ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {a : G} (haA : a ∈ A) (hac : a ∉ Subgroup.zpowers c) :
    delta A (lB A) (Subgroup.centralizer ({a} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  have h := hctx.std
  have hD := h.toSec13Data
  have ha1 : a ≠ 1 := fun h1 => hac (h1 ▸ Subgroup.one_mem _)
  have haΩ : Subgroup.zpowers a ∉ omegaA A := by
    rw [hctx.omegaA_eq, Set.mem_singleton_iff]
    intro hz
    exact hac (hz ▸ Subgroup.mem_zpowers a)
  obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A (piCompl 3)
  obtain ⟨-, halt⟩ := h143 a haA ha1 haΩ Q hQ
  rcases halt with h1 | ⟨b, d, Lb, hbΩ, hLb, hJ, -⟩
  · exact h1
  · exfalso
    rw [hctx.omegaA_eq, Set.mem_singleton_iff] at hbΩ
    have hCb : Subgroup.centralizer ({b} : Set G) = Subgroup.centralizer ({c} : Set G) :=
      centralizer_singleton_eq_of_zpowers_eq hbΩ
    have hLb' : Lb ∈ thetaComponentsAt 3 c := by
      have := hLb.1
      rw [thetaComponentsAt_eq_thetaComponentsIn, hCb] at this
      exact this
    have h3 : 3 ∣ Nat.card Lb := three_dvd_card_of_thetaQuot_j2 hJ
    have hLbL : Lb = L :=
      (h.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).2 Lb hLb' h3
    exact hHJ (hLbL ▸ hJ)

theorem not_three_dvd_card_delta_ofQ {A L Y : Subgroup G} {c : G} {n : ℕ}
    (hctx : Ctx1424 G A c L Y n) (h143 : Ronan148Q.Item143Q A (lB A))
    (hHJ : ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {a : G} (haA : a ∈ A) (hac : a ∉ Subgroup.zpowers c) :
    ¬ 3 ∣ Nat.card (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) := by
  rw [delta_eq_of_item143Q hctx h143 hHJ haA hac, sup_comm]
  have hCA : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    (pPrimeCoreOf_le 3 _).trans ((Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr haA)).trans (le_normalizer_pPrimeCoreOf 3 _))
  have hnd : ∀ X : Subgroup G, ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 X) := fun X =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X)
  exact Sec6.not_dvd_card_sup Nat.prime_three hCA (hnd _) (hnd _)

theorem commutator_le_delta_of_item143Q {A L Y : Subgroup G} {c : G} {n : ℕ}
    (hctx : Ctx1424 G A c L Y n) (h143 : Ronan148Q.Item143Q A (lB A))
    (hHJ : ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {a : G} (haA : a ∈ A) (hac : a ∉ Subgroup.zpowers c) {E S : Subgroup G}
    (hEQ : E ∈ scriptQ A (lB A)) (hEA : E = ⁅E, A⁆)
    (hEa : E ≤ Subgroup.centralizer ({a} : Set G))
    (hSa : S ≤ Subgroup.centralizer ({a} : Set G)) :
    ⁅S, E⁆ ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) := by
  have hD := hctx.std.toSec13Data
  have hΔ := delta_eq_of_item143Q hctx h143 hHJ haA hac
  set M := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hM
  set C₀ := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hC₀
  have hEΔ : E ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) := le_delta hEQ hEa
  have hCa : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (M : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx haA)
  have hCAa : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA)
  have hEM : E ≤ M := by
    rw [hEA]
    refine (Subgroup.commutator_mono (hΔ ▸ hEΔ) le_rfl).trans ?_
    exact commutator_sup_le148 (hAa.trans hCa) (((pPrimeCoreOf_le 3 _).trans hCAa).trans hCa)
      (pPrimeCoreOf_le 3 _)
  have hSM : ⁅S, E⁆ ≤ M := by
    refine (Subgroup.commutator_mono le_rfl hEM).trans ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hSa.trans hCa)
  rw [hΔ]
  exact hSM.trans le_sup_left

theorem rank3II_14_24Q {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h1423 : Item14_23 A L) (h143 : Ronan148Q.Item143Q A (lB A)) (hE : Step1424E)
    (hcore : Step1424Core) :
    Item14_24 A (lB A) c L := by
  intro Y hY3 hYA n hn hiso hYL hF hLs hΩ
  have hctx : Ctx1424 G A c L Y n := ⟨h, hY3, hYA, hn, hiso, hYL, hF, hLs, hΩ⟩
  have hD := h.toSec13Data
  have hAe := hD.isElemAbelian
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, E, hEprops⟩ := hE G A c L Y n hctx
  obtain ⟨hp, hp3, hEe, hEcard, hEA, hEQ, hEYL, hB⟩ := hEprops
  have : Fact p.Prime := ⟨hp⟩
  set P := CFSG.Open.pCoreOf 2 Y with hP
  set B := A ⊓ Subgroup.centralizer (E : Set G) with hBdef
  have hEY : E ≤ Y := hEYL.trans inf_le_left
  have hEL : E ≤ L := hEYL.trans inf_le_right
  have hE1 : E ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hEcard
    have := Nat.one_lt_pow (by norm_num : (2 : ℕ) ≠ 0) hp.one_lt
    omega
  have hEp : IsPGroup p E := IsPGroup.of_card hEcard
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    hYA.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hEP : E ≤ Subgroup.normalizer (P : Set G) :=
    hEY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hcopP : ∀ {X : Subgroup G}, X ≤ P → p.Coprime (Nat.card X) := by
    intro X hX
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hP2.to_le hX)
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  have hfaith : ¬ P ≤ Subgroup.centralizer (E : Set G) := by
    intro hPE
    have hEC : E ≤ Subgroup.centralizer (P : Set G) := Subgroup.le_centralizer_iff.mp hPE
    have h1 : E ≤ P := fun e he => inf_centralizer_le_pCoreOf_of_fitting hF ⟨hEY he, hEC he⟩
    have h2 : E ⊓ P = ⊥ := (Subgroup.disjoint_of_coprime_natCard (by
      rw [hEcard]
      exact Nat.Coprime.pow_left 2 (hcopP le_rfl))).eq_bot
    apply hE1
    rw [eq_bot_iff, ← h2]
    exact le_inf le_rfl h1
  have hBcard : Nat.card B = 3 ^ 2 := by
    have := hB.2
    rw [hD.card_eq] at this
    norm_num
    omega
  have hBpow : ∀ b : B, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hAe.2 _ b.2.1)
  have hP3 : ¬ 3 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three B P hBpow hBcard hP3 (inf_le_left.trans hAP)
  obtain ⟨b, hb1, hU1⟩ : ∃ b : B, b ≠ 1 ∧
      ⁅P ⊓ Subgroup.centralizer ({(b : G)} : Set G), E⁆ ≠ ⊥ := by
    by_contra hall
    push Not at hall
    apply hfaith
    rw [hgen]
    exact iSup_le fun b => iSup_le fun hb =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hall b hb)
  set a : G := (b : G) with ha
  have haA : a ∈ A := b.2.1
  have haE : a ∈ Subgroup.centralizer (E : Set G) := b.2.2
  have ha1 : a ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  have hEa : E ≤ Subgroup.centralizer ({a} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp haE e he)
  set T := P ⊓ Subgroup.centralizer ({a} : Set G) with hT
  set U := ⁅T, E⁆ with hU
  have hUP : U ≤ P := (Subgroup.commutator_mono inf_le_left le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hEP)
  have hac : a ∉ Subgroup.zpowers c := by
    intro hac
    have ha3 : a ^ 3 = 1 := hAe.2 a haA
    have hz : Subgroup.zpowers a = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hac) ?_
      rw [hD.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
    have hCa := centralizer_singleton_eq_of_zpowers_eq hz
    have hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
      centralizer_le_normalizer_of_three_dvd h (Proof1423.three_dvd_card_of_sec14Std h)
    have hTL : T ≤ Subgroup.normalizer (L : Set G) := inf_le_right.trans (hCa ▸ hCL)
    have hUL : U ≤ L := (Subgroup.commutator_mono le_rfl hEL).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hTL)
    apply hU1
    rw [eq_bot_iff, ← hcore G A c L Y n hctx]
    exact le_inf hUP hUL
  set X := delta A (lB A) (Subgroup.centralizer ({a} : Set G)) with hXdef
  have hHJ := step1424NotHJ G A c L Y n hctx
  have hX3 : ¬ 3 ∣ Nat.card X := not_three_dvd_card_delta_ofQ hctx h143 hHJ haA hac
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_normalizer_sSup fun _ hQ => hQ.1.1.2.2
  have hX : X ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three X).mpr hX3, hAX⟩
  have hEX : E ≤ X := le_delta hEQ hEa
  set N := normalClosureSub X E with hN
  have hNs : Group.IsSolvable N := h1423 p hp hp3 E hE1 hEe hEA hEL X hX hEX
  have hNX : N ≤ X := normalClosureSub_le X E
  have hN3 : ¬ 3 ∣ Nat.card N := fun h3 => hX3 (h3.trans (Subgroup.card_dvd_of_le hNX))
  have hEN : E ≤ N := le_normalClosureSub hEX
  have hET : E ≤ Subgroup.normalizer (T : Set G) :=
    (le_inf hEP (hEa.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hUE : ⁅U, E⁆ = U :=
    SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent p hp E T hEp hET
      (hcopP inf_le_left)
  have hU2 : IsPGroup 2 U := hP2.to_le hUP
  have hEU : E ≤ Subgroup.normalizer (U : Set G) := Sec6.le_normalizer_commutator_right T E
  have hUX' : U ≤ X := commutator_le_delta_of_item143Q hctx h143 hHJ haA hac hEQ hEA hEa
    inf_le_right
  have hUN : U ≤ N := by
    rw [← hUE]
    exact commutator_le_normalClosureSub hEX hUX'
  have hUO : U ≤ CFSG.Open.pCoreOf 2 N := by
    by_cases hp5 : p = 5
    · subst hp5
      have hA3 : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hAe
      have hAE : A ≤ Subgroup.normalizer (E : Set G) := by
        rw [hEA]
        exact Sec6.le_normalizer_commutator_right E A
      have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
        (le_inf hAX hAE).trans (normalizer_inf_le_normalizer_normalClosureSub X E)
      have hAc : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx haA)
      have hAa : A ≤ Subgroup.normalizer
          ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
        hAc.trans Subgroup.le_normalizer
      have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
        le_normalizer_commutator_of_le
          ((le_inf hAP hAa).trans Subgroup.inf_normalizer_le_normalizer_inf) hAE
      exact step1424Five G h.localRank_lt A N U E hNs hN3 hU2 hUN hEN hEe hEcard hEU hUE hA3 hAN
        hAU hAE hEA
    · exact Proof1424.le_pCoreOf_two_of_commutator_action h.localRank_lt hp hp3 hp5 hNs hN3 hU2
        hUN hEN hEe hEU hUE
  have hNO : CFSG.Open.pCoreOf 2 N ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 N).trans hNX)
      ((le_normalizer_normalClosureSub X E).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
  refine ⟨a, haA, hac, fun hbot => hU1 ?_⟩
  rw [eq_bot_iff, ← hbot]
  exact le_inf hUP (hUO.trans hNO)

theorem item14_24R_ofQ (h1423 : Item14_23R) (h143 : Ronan148Q.Item143QS14) (hE : Step1424E)
    (hcore : Step1424Core) : Item14_24R :=
  fun G _ _ A c L h => rank3II_14_24Q h.toSec14Std (h1423 G A c L h) (h143 G A c L h.toSec14Std)
    hE hcore

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
