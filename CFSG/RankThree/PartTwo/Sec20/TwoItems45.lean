module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res10ProofGTwoThree
public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofCyclic
public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeClass
public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeJ1
public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3OddMeet
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL2Odd
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeL3
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeU3
public import CFSG.RankThree.PartTwo.Sec20.SimsYKO3Five
public import CFSG.RankThree.PartTwo.Sec20.TwoAlt20
public import CFSG.RankThree.PartTwo.Sec20.TwoFinal
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Final
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagGriess
import CFSG.RankThree.PartTwo.Sec15.Item1510ProofTools
import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.RankThree.PartTwo.Sec19.Item1923Alt20
import CFSG.RankThree.PartTwo.Sec20.Item20Res9ProofNormalAll
import CFSG.RankThree.PartTwo.Sec20.TwoL2Vacuous
import CFSG.RankThree.PartTwo.Sec20.TwoStep2054

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

private theorem kData_of_item1923 (h194 : Sec19.Item194UsedWide3) (h23 : Item1923)
    {A M N L : Subgroup G} {c : G} (h : Hyp1921 G A M N L)
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)) :
    ∃ n : ℕ, Odd n ∧
      Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 n)) ∧
      (∃ ε : ℕ, (ε = 1 ∨ ε = 2) ∧ (M ⊓ N).relIndex M = ((2 ^ n) ^ 2 + 2 ^ n + 1) * ε) ∧
      M ≤ Subgroup.normalizer (kTwenty M c : Set G) ∧ A ⊓ kTwenty M c = Subgroup.zpowers c ∧
      ∀ P : Subgroup G, IsSylowOf 3 P (M ⊓ N) → A ≤ P →
        IsSylowOf 3 P M ∧ Sec18.omegaOneThree P = A := by
  obtain ⟨K, hK⟩ := (h194 G h.toSec19Std A M N h.isE27 h.mem_scriptM h.mem_scriptM_N h.ne).1
  obtain ⟨-, -, -, ⟨n, hn, hiso, hidx⟩, -, hAK, hKM, hKeq, -, -, -, h6, -⟩ :=
    h23 G A M N L c h hc K hK
  subst hKeq
  refine ⟨n, hn, hiso, hidx, hKM, hAK, fun P hP hAP => ?_⟩
  obtain ⟨hPM, -, hΩ, -⟩ := h6 P hP hAP
  exact ⟨hPM, hΩ⟩

private theorem not_four_dvd_relIndex {M N : Subgroup G} {n ε : ℕ} (hn : Odd n)
    (hε : ε = 1 ∨ ε = 2)
    (h : (M ⊓ N).relIndex M = ((2 ^ n) ^ 2 + 2 ^ n + 1) * ε) : ¬ 4 ∣ (M ⊓ N).relIndex M := by
  have hev : Even (2 ^ n) := (Nat.even_pow' hn.pos.ne').mpr even_two
  have hodd : Odd ((2 ^ n) ^ 2 + 2 ^ n + 1) :=
    (((Nat.even_pow' two_ne_zero).mpr hev).add hev).add_one
  obtain ⟨k, hk⟩ := hodd
  rw [h, hk]
  rcases hε with rfl | rfl <;> omega

private theorem normalizer_le_of_scriptM_eq {A M : Subgroup G} {c : G}
    (h202 : scriptM ((A ⊔ kTwenty M c : Subgroup G) : Set G) = {M}) {R' : Subgroup G}
    (hR'1 : R' ≠ ⊥) (hR'2 : IsPGroup 2 R')
    (hAK : A ⊔ kTwenty M c ≤ Subgroup.normalizer (R' : Set G)) :
    Subgroup.normalizer (R' : Set G) ≤ M := by
  obtain ⟨M', hM', hNM'⟩ := exists_mem_scriptM_of_isTwoLocal
    (X := ((A ⊔ kTwenty M c : Subgroup G) : Set G)) ⟨R', hR'1, hR'2, rfl⟩ hAK
  rw [h202] at hM'
  rw [← hM']
  exact hNM'


section Item205


theorem item205Two_of (h1912 : Item1912) (h194 : Sec19.Item194UsedWide3) (h23 : Item1923)
    (h204 : Item204Two) : Item205Two := by
  intro G _ _ A M L N c T hT hyp
  have hAlt := alt20_of_hyp1921 h1912 h194 h23 hyp hT.centralizer_eq
  obtain ⟨n, hn, hiso, ⟨ε, hε, hidx⟩, -⟩ := kData_of_item1923 h194 h23 hyp hT.centralizer_eq
  have h1 : ¬ IsSylowOf 2 T ⊤ :=
    step2051_core hT hAlt.K_type (fun _ => not_four_dvd_relIndex hn hε hidx)
      (fun R hR hRM => step2051Sylow_core hAlt.card_eq R hR hRM)
  have h2 := rank3II_20_5_2_core hT (h204 G A M L N c T hT hyp) h1
  obtain ⟨h4, T', hT', hT'N⟩ := step2054Two_of hT hAlt.orderOf_c h2 hAlt.K_mem hn hiso
    (hAlt.K_type.isMaxParabolic ⟨n, hn, hiso⟩) (hAlt.centralizer_le ⟨n, hn, hiso⟩)
  exact ⟨h1, h2, ⟨n, hn, hiso⟩, h4, T', hT', hT'N⟩

end Item205

section Item204


theorem item204Two_of
    (h1912 : Item1912) (h194 : Sec19.Item194UsedWide3) (h23 : Item1923)
    (h202 : ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G),
      Hyp201 G A M L N c → Hyp1921 G A M N L →
        scriptM ((A ⊔ kTwenty M c : Subgroup G) : Set G) = {M}) : Item204Two := by
  intro G _ _ A M L N c T hT hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAlt := alt20_of_hyp1921 h1912 h194 h23 hyp hT.centralizer_eq
  obtain ⟨n, hn, hiso, -, hMKn, hAKeq, h6⟩ := kData_of_item1923 h194 h23 hyp hT.centralizer_eq
  have hc3 : orderOf c = 3 := hAlt.orderOf_c
  have hc1 : c ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc3
    omega
  have hB9 : Nat.card (A ⊓ L : Subgroup G) = 9 := hAlt.card_inf
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) := hAlt.sylow_inf.isPGroup
  have hNB : Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ≤ M := by
    obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := item1922Full_of_item1912 h1912 G A M N L hyp
    exact h
  have hQ : ∃ Q : Subgroup (MulAut ↥(A ⊓ L)), Q ≤ Sec4.autIn M (A ⊓ L) ∧
      Nonempty (↥Q ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hAlt.quotient_iso
    obtain ⟨f₀, hf₀⟩ := Sec18.exists_quaternion_autIn e (inf_le_right : A ⊓ L ≤ L) hB3 hB9
    let f : QuaternionGroup 2 →* MulAut ↥(A ⊓ L) := (Sec4.autIn L (A ⊓ L)).subtype.comp f₀
    have hf : Function.Injective f := fun x y h => hf₀ (Subtype.ext h)
    refine ⟨f.range, ?_, ⟨(MonoidHom.ofInjective hf).symm⟩⟩
    rintro _ ⟨q, rfl⟩
    obtain ⟨x, hxN, -, hx⟩ := Sec4.mem_autIn_iff.mp (f₀ q).2
    exact Sec4.mem_autIn_iff.mpr ⟨x, hxN, hNB hxN, hx⟩
  have h202' := h202 G A M L N c hT.toHyp201 hyp
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    eq_zpowers_sup_inf_core hT hAlt.quotient_iso hB9 hc1
  obtain ⟨i, j, hij, hi3, hj3, hi1, hj1, hi, hj⟩ :=
    step204Normal_core hT hB9 hB3 hQ hc1 hAeq hAlt.normal_inf_sup
  have hAKle : ∀ k : Fin 4, K ⊔ A ⊔ T ≤ Subgroup.normalizer (Sec18.fourChar R k : Set G) →
      A ⊔ K ≤ Subgroup.normalizer (Sec18.fourChar R k : Set G) := fun k hk =>
    (sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)).trans hk
  have hNi := normalizer_le_of_scriptM_eq h202' hi1 (hR2.to_le (fourChar_le R i)) (hAKle i hi)
  have hNj := normalizer_le_of_scriptM_eq h202' hj1 (hR2.to_le (fourChar_le R j)) (hAKle j hj)
  have hmax := pCoreOf_mem_maxInvariant hT hNi
  have hNR : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    ((normalizer_le_normalizer_fourChar R i).trans hNi).trans hMK
  have hNAM : Subgroup.normalizer (A : Set G) ≤ M :=
    (normalizer_le_gamma le_rfl (by rw [hyp.isE27.pRank_eq]; norm_num)).trans hyp.mem_scriptM.2
  obtain ⟨P, hP, hAP⟩ :=
    exists_isSylowOf_le hyp.isE27.isPGroup (le_inf hyp.le_M hyp.le_N : A ≤ M ⊓ N)
  obtain ⟨hPM, hΩ⟩ := h6 P hP hAP
  have hPA : P ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer.trans (Sec15.Proof1510.normalizer_le_of_eq_omegaOneThree hΩ.symm)
  have hPN : IsSylowOf 3 P (Subgroup.normalizer (A : Set G)) := hPM.of_le hPA hNAM
  obtain ⟨hPG, hconj, hfrat⟩ := hAlt.sylow_top P hPN
  have hset : Setting204 G A M L N c T i j P :=
    { toCtx20 := hT
      one_of_L2 := fun h =>
        (not_exists_yAlpha_equiv_projSL_two (T := T) hAlt.K_mem hc3 hn hiso h).elim
      ne := hij
      ne_three_left := hi3
      ne_three_right := hj3
      normal_left := hi
      normal_right := hj
      normalizer_left := hNi
      normalizer_right := hNj
      maxInvariant := hmax
      normalizer_le := hNR
      mem_oTwoComponentsIn := hAlt.K_mem
      not_le := hAlt.K_not_le
      kType := Or.inl ⟨n, hn, hiso⟩
      sylow_normalizer := hPN
      sylow_top := hPG
      conjugatesIn_eq := hconj
      normalizer_A := step1923_normalizer_A_le hyp hMKn hAKeq
      omegaOne := Or.inl (by rw [hΩ]; exact hyp.isE27)
      not_mem_frattini := hfrat }
  have h432 : Sec4.Item4_32Comp := Sec4.item4_32Comp_of_three
    Sec4.RonanK432.k432InnerThree_holds Sec4.RonanK432.k432List_holds
  have h41 : Sec4.Item4_1LargePrime := Sec4.diag_item41LargePrime_holds
  have hG2 : Sec17.KS176GTwo := Sec17.ks176GTwo_holds
  have hcyc := step204Cyclic_of h432 h41 hG2
  have hKF3 : KFactKO3Cent := kFactKO3Cent_of_layer kFactKO3CentLayer_holds
  have hKO3 := step204YKO3_of_comm (step204YKO3Comm_of_small hKF3 step204YKO3CommSmall_holds)
  have hcov := step204FinalCover_of_kO3 hKO3
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hT.mem_scriptM.1, ?_⟩, ?_⟩
  · intro x hx
    exact sup_le hKM hT.sylow.le hx
  · intro X hX
    by_contra hXM
    have hm := hcyc G A M L N c T i j P hset X hX hXM
    by_cases hL2 : ∃ m : ℕ, Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))
    · exact not_exists_yAlpha_equiv_projSL_two (T := T) hAlt.K_mem hc3 hn hiso
        ⟨X, hX, hXM, hm, hL2⟩
    · push Not at hL2
      rcases step204Asc1411_of_types step204YAlphaClass_holds step204AscJ1_holds
          step204AscL2Odd_holds (step204AscL3_of_split step204AscL3Even_holds step204AscL3Odd_holds)
          step204AscU3Even_holds G A M L N c T i j P hset X hX hXM hm
        (fun m h => (hL2 m).elim h.some) with hi' | hj'
      · exact hcov G A M L N c T i j P hset X hX hXM hm i (Or.inl rfl) hi'
      · exact hcov G A M L N c T i j P hset X hX hXM hm j (Or.inr rfl) hj'

end Item204

end CFSG.RankThree.PartTwo.Sec20
