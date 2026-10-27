module

public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofKM
public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
public import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofCoprime
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MAssembly3
public import CFSG.RankThree.PartTwo.Sec17.Item1711KMdNoInv
public import CFSG.RankThree.PartTwo.Sec17.Item17Res5ProofFit
public import CFSG.RankThree.PartTwo.Sec14.Concl142Item

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped Pointwise


variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

namespace Proof171Steps

theorem k1711_le_of_le_sup_weak
    {b : G} {X LB M : Subgroup G}
    (hDX : delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X)
    (hInv : Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer
        ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G))
    (hbA : b ∈ A) (hXC : X ≤ Subgroup.centralizer ({b} : Set G)) (hLBX : LB ≤ X)
    (hXY : X ≤ LB ⊔ inSubgroup (aschbacherSolvableCore 3) X) (hLBM : LB ≤ M)
    (hLBK : LB ≤ k1711 A b) :
    k1711 A b ≤ (k1711 A b ⊓ M) ⊔ pPrimeCoreOf 3 (k1711 A b) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set O := pPrimeCoreOf 3 C with hO
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  set K := k1711 A b with hK
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  set R := O ⊔ θX with hR
  have hXeq : X = LB ⊔ θX := le_antisymm hXY (sup_le hLBX (theta_le X))
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hXθN : X ≤ Subgroup.normalizer (θX : Set G) := le_normalizer_theta X
  have hO'CN : O' ≤ Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.normalizer (A : Set G) :=
    le_inf
      ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)))
      ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer (A : Set G)))
  have hO'N : O' ≤ Subgroup.normalizer ((O ⊔ X : Subgroup G) : Set G) :=
    hO'CN.trans hInv
  have hO'3 : Nat.Coprime 3 (Nat.card O') := coprime_card_pPrimeCoreOf 3 _
  have hKOX : K ≤ O ⊔ X := by
    rw [hK, k1711, oPrimeResidualOf_eq_closure, Subgroup.closure_le]
    rintro x ⟨hx, k, hk⟩
    have hx' : x ∈ (O ⊔ X) ⊔ O' := by
      rw [hDX] at hx
      rwa [sup_right_comm] at hx
    exact mem_left_of_pow_prime_pow Nat.prime_three hO'N hO'3 hx' hk
  have hOX : O ⊔ X = LB ⊔ R := by
    rw [hR]
    conv_lhs => rw [hXeq]
    exact sup_left_comm O LB θX
  have hRN : X ≤ Subgroup.normalizer (R : Set G) :=
    le_normalizer_sup' (hXC.trans hCO) hXθN
  have hLBR : LB ≤ Subgroup.normalizer (R : Set G) := hLBX.trans hRN
  have hOXR : O ⊔ X ≤ Subgroup.normalizer (R : Set G) :=
    sup_le ((le_sup_left : O ≤ R).trans Subgroup.le_normalizer) hRN
  have hR3 : Nat.Coprime 3 (Nat.card R) := by
    have hθ3 : ¬ 3 ∣ Nat.card θX := by
      rw [hθX, inSubgroup, Subgroup.card_map_of_injective X.subtype_injective]
      exact (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.2.1
    have hdvd : Nat.card R ∣ Nat.card θX * Nat.card O := by
      rw [hR, sup_comm]
      exact card_sup_dvd_card_mul ((theta_le X).trans (hXC.trans hCO))
    exact Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.mul_right
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3) (coprime_card_pPrimeCoreOf 3 C))
  have hKR : K ⊓ R ≤ pPrimeCoreOf 3 K :=
    le_pPrimeCoreOf inf_le_left
      (Late.le_normalizer_inf Subgroup.le_normalizer (hKOX.trans hOXR))
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hR3)
  intro k hk
  have hk' : k ∈ ((LB : Set G) * (R : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right LB R hLBR, ← hOX]
    exact hKOX hk
  obtain ⟨l, hl, r, hr, rfl⟩ := hk'
  have hrK : r ∈ K := by
    have := mul_mem (inv_mem (hLBK hl)) hk
    rwa [inv_mul_cancel_left] at this
  exact mul_mem (Subgroup.mem_sup_left ⟨hLBK hl, hLBM hl⟩)
    (Subgroup.mem_sup_right (hKR ⟨hrK, hr⟩))


end Proof171Steps

theorem step1711KM_of_Q
    (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (h143 : Ronan148Q.Item143QS14) (hd :   ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ b ∈ A, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A →
    ∀ (b' d : G) (Lb : Subgroup G), Subgroup.zpowers b' ∈ omegaA A → Lb ∈ lA A b' →
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) →
      d ∈ A → d ≠ 1 → IsThreeCentralIn Lb d → Subgroup.zpowers b = Subgroup.zpowers d →
    ∀ X : Subgroup G,
      delta A (lB A) (Subgroup.centralizer ({b} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X →
      (∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 b ∧ 𝒳.Nonempty ∧ X = sSup 𝒳) →
      (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)) →
      CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
      ¬ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) →
        X ≤ (X ⊓ Subgroup.normalizer (Y₀ : Set G)) ⊔ inSubgroup (aschbacherSolvableCore 3) X) : Step1711KM := by
  intro G _ _ A c L Y₀ h b hb hb1 hO2 hDM h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS14 := h.toSec14Std
  have hM := fun e (he : Subgroup.zpowers e ∈ omegaA A) =>
    Proof171Steps.centralizer_le_M_of_mem_omegaA h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h) he
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set D := delta A (lB A) C with hD
  have hbΩ : Subgroup.zpowers b ∉ omegaA A := fun hbΩ => hDM ((delta_le C).trans (hM b hbΩ))
  obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty D A (piCompl 3)
  obtain ⟨-, halt⟩ := h143 G A c L hS14 b hb hb1 hbΩ Qs hQs
  rcases halt with h1 | ⟨b', d, Lb', hb'Ω, hLb', hJ, hdA, hd1, hdc, -, X, hDX, hInv, hcase⟩
  ·
    exfalso
    have hO'O : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 C : Set G) :=
      ((pPrimeCoreOf_le 3 _).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))).trans
          (le_normalizer_pPrimeCoreOf 3 C)
    have hdvd : Nat.card D ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) *
        Nat.card (pPrimeCoreOf 3 C) := by
      rw [hD, h1, sup_comm]
      exact card_sup_dvd_card_mul hO'O
    have hcop := Nat.Coprime.mul_right (coprime_card_pPrimeCoreOf 3
      (Subgroup.centralizer (A : Set G))) (coprime_card_pPrimeCoreOf 3 C)
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.coprime_dvd_right hdvd hcop)) h3
  have hXD : X ≤ D := le_sup_right.trans hDX.ge
  rcases hcase with ⟨hXθ, hXeq, -⟩ | ⟨hbd, h𝒳, htypes⟩
  ·
    obtain ⟨hb'A, hb'3, -⟩ := zpowers_mem_omegaA_iff.mp hb'Ω
    have hb'1 : b' ≠ 1 := by
      rintro rfl
      rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hb'3
      norm_num at hb'3
    have hne : Subgroup.zpowers b ≠ Subgroup.zpowers b' := fun heq => hbΩ (heq ▸ hb'Ω)
    have hB := Proof171Steps.isHyperplane_closure_pair hS14.isE27' hb hb'A hb1 hb'1 hne
    have hLBX : lB A (Subgroup.closure {b, b'}) ≤ X := hXeq ▸ le_sup_left
    have hInv' : Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer
          ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G) := by
      rcases hInv with hstrong | ⟨-, -, -, hweak⟩
      · exact inf_le_left.trans hstrong
      · exact hweak
    exact Proof171Steps.k1711_le_of_le_sup_weak hDX hInv' hb
      (le_centralizer_of_mem_thetaComponentsAt hXθ) hLBX hXeq.le
      (Proof171Steps.lB_le_of_centralizer_le hM)
      (Proof171Steps.lB_le_oPrimeResidualOf hS14 hB (hLBX.trans hXD))
  ·
    obtain ⟨𝒳, h𝒳b, h𝒳ne, hX𝒳⟩ := h𝒳
    have hXp : Group.IsPerfect ↥X := by
      rw [hX𝒳]
      exact Proof171Steps.isPerfect_sSup fun M hM =>
        Sec6.isPerfect_of_mem_thetaComponentsAt (h𝒳b hM)
    have hX3 := Proof171Steps.eq_oPrimeResidualOf_of_quot hXp
      (Proof171Steps.oPrimeResidual_eq_top_of_types143 htypes)
    have hXK : X ≤ k1711 A b := by
      rw [hX3]
      exact Proof171Steps.oPrimeResidualOf_mono_three hXD
    have hXC : X ≤ C := by
      rw [hX𝒳]
      exact sSup_le fun M hM => le_centralizer_of_mem_thetaComponentsAt (h𝒳b hM)
    have hInv' : Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer
          ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G) := by
      rcases hInv with hstrong | ⟨-, -, -, hweak⟩
      · exact inf_le_left.trans hstrong
      · exact hweak
    exact Proof171Steps.k1711_le_of_le_sup_weak hDX hInv' hb hXC inf_le_left
      (hd G A c L Y₀ h b hb hb1 hbΩ b' d Lb' hb'Ω hLb' hJ hdA hd1 hdc hbd X hDX
        ⟨𝒳, h𝒳b, h𝒳ne, hX𝒳⟩ htypes hO2 hDM)
      inf_le_right (inf_le_left.trans hXK)


theorem step1711Fit_of_concl143
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h142 : Item142R) (h143c : Concl143S14) (hP : Step1711FitP) : Step1711Fit := by
  intro G _ _ A c L Y₀ h a ha ha1 b hb hb1 U hU hUa hUQ hO2 hDM hcomm
  obtain ⟨p, Z₀, hp, hp2, hp3, hZ₀p, hZ₀D, hAZ₀, hUZ₀, hZ₀U⟩ :=
    hP G A c L Y₀ h a ha ha1 b hb hb1 U hU hUa hUQ hO2 hDM hcomm
  have : Fact p.Prime := ⟨hp⟩
  have hS14 := h.toSec14Std
  have hc142 : Concl142 A (lB A) :=
    concl142_of_item142 h422 h45 hS14 fun e Le hS => h142 G A e Le ⟨hS, h.hypR⟩
  have hc143 : Concl143 A (lB A) := h143c G A c L hS14
  obtain ⟨hAU, hUe, hU4⟩ := mem_fourGroups_iff.mp hU
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  set Z := ⁅Z₀, U⁆ with hZdef
  have hZZ₀ : Z ≤ Z₀ := Subgroup.le_normalizer_iff_commutator_le_left.mp hUZ₀
  have hZp : IsPGroup p Z := hZ₀p.to_le hZZ₀
  have hZodd : Odd (Nat.card Z) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZp
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hZ₀2 : ¬ 2 ∣ Nat.card Z₀ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ₀p
    rw [hn]
    intro h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hUZ : U ≤ Subgroup.normalizer (Z : Set G) := Subgroup.normalizer_commutator_ge_right Z₀ U
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) :=
    Proof171Steps.le_normalizer_commutator hAZ₀ hAU
  have hZU : Z = ⁅Z, U⁆ :=
    (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 2 Nat.prime_two U Z₀
      hU2 hZ₀2 hUZ₀).symm
  have ha3 : a ^ 3 = 1 := h.toSec13Data.isElemAbelian.2 a ha
  refine ⟨Z, hZodd, hUZ, ?_, ?_, ?_⟩
  · rw [← hZU]
    exact hZ₀U
  · exact Proof171Steps.le_iSup_inf_centralizer_conj hp hp2 hp3 hZp hUe hU4 ha3 hUZ (hAZ ha)
      (hAU ha) hUa hZU
  ·
    have hZ3 : ¬ 3 ∣ Nat.card Z := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZp
      rw [hn]
      intro h3
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    have hZQ := Proof171Steps.mem_scriptQ_of_le_delta hc142 hc143 hb hb1 (hZZ₀.trans hZ₀D) hZ3 hAZ
    have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute hx ha)
    have hAZa : A ≤ Subgroup.normalizer
        ((Z ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
      Late.le_normalizer_inf hAZ (hAa.trans Subgroup.le_normalizer)
    exact le_delta (mem_scriptQ_of_le hZQ inf_le_left hAZa) inf_le_right



theorem step1711KM_of_balance_meets_Q
    (hbal : Step143Balance) (h48 : Sec4.Item4_8)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h134 : Item134) : Step1711KM :=
  step1711KM_of_Q h1514 hMeets (Ronan148M.item143QS14_holds)
    (step1711KMdNoInv_holds hbal h48 h1514 hMeets h134)

theorem step1711Fit_of_item166_concl143
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h142 : Item142R) (h143c : Concl143S14) (h166 : Sec16.Item166S17) : Step1711Fit :=
  step1711Fit_of_concl143 h422 h45 h142 h143c (step1711FitP_of h166)

theorem item1711S17_of_item166_concl143
    (h179 : Item179S17) (hKM : Step1711KM)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h142 : Item142R) (h143c : Concl143S14)
    (h166 : Sec16.Item166S17) : Item1711S17 :=
  item1711S17_of h179 hKM (step1711Fit_of_item166_concl143 h422 h45 h142 h143c h166)

end CFSG.RankThree.PartTwo.Sec17
