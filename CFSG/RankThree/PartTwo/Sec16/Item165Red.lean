module

public import CFSG.RankThree.PartTwo.Sec16.CTrick
public import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofThree
public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofU

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

namespace Red165

open CTrick

variable {G : Type} [Group G] [Finite G]
variable {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem deltaZero_le_residual_sup_pPrimeCore (h : Sec17Std G A c L Y₀)
    (hRead : Y4CoreReadR) {X : Subgroup G} (hX : X ∈ scriptY3 A (lB A)) :
    deltaZero A (lB A) X ≤ oPrimeResidualOf 3 X ⊔ pPrimeCoreOf 3 X := by
  have hread := hRead G A c L h.toSec15R X hX.1.1 hX.2
  refine hread.2.trans ?_
  refine sup_le ?_ le_sup_right
  refine (sSup_le fun K hK => ?_).trans le_sup_left
  have hKX : K ≤ X := (mem_thetaComponentsIn_iff.mp hK.1).1
  calc K = oPrimeResidualOf 3 K := hK.2
    _ ≤ oPrimeResidualOf 3 X := oPrimeResidualOf_mono 3 hKX

theorem isEmpty_alt7_of_isL3TwoPow (hL3 : IsL3TwoPow L) :
    IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨n, hn, hIso⟩ := hL3
  rcases hIso with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact Steps165.isEmpty_alt7_of_projSL hn hq φ
  · exact Steps165.isEmpty_alt7_of_projSU hn hq φ

private theorem pCoreOf_two_oPrimeResidualOf_le_pPrimeCore (X : Subgroup G) :
    CFSG.Open.pCoreOf 2 (oPrimeResidualOf 3 X) ≤ pPrimeCoreOf 3 X := by
  have hXV : X ≤ Subgroup.normalizer
      (CFSG.Open.pCoreOf 2 (oPrimeResidualOf 3 X) : Set G) :=
    (le_normalizer_oPrimeResidualOf (p := 3) (K := X) Subgroup.le_normalizer).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.Open.pCoreOf 2 (oPrimeResidualOf 3 X))) := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup
      (r := 2) (oPrimeResidualOf 3 X)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  exact le_pPrimeCoreOf ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
    (oPrimeResidualOf_le_self 3 X)) hXV hcop

private theorem commutatorElement_mul_mem_pCoreOf {P L : Subgroup G} {c l p : G}
    (hLP : L ≤ Subgroup.normalizer (P : Set G))
    (hcP : c ∈ Subgroup.normalizer (P : Set G))
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hl : l ∈ L) (hp : p ∈ P) :
    ⁅l * p, c⁆ ∈ P := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hpcP : ⁅p, c⁆ ∈ P := by
    have hcp : c * p⁻¹ * c⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hcP p⁻¹).mp (P.inv_mem hp)
    rw [commutatorElement_def,
      show p * c * p⁻¹ * c⁻¹ = p * (c * p⁻¹ * c⁻¹) by group]
    exact P.mul_mem hp hcp
  have hconj : l * ⁅p, c⁆ * l⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hLP hl) _).mp hpcP
  have hlc : ⁅l, c⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
  rw [hlc, mul_one]
  exact hconj

theorem commutatorElement_mem_pPrimeCore (h : Sec17Std G A c L Y₀)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (hL3 : IsL3TwoPow L)
    {X : Subgroup G} (hX : X ∈ scriptY3Star A (lB A))
    (hJY : oPrimeResidualOf 3 X ≤ Y₀) :
    ∀ j ∈ oPrimeResidualOf 3 X, ⁅j, c⁆ ∈ pPrimeCoreOf 3 X := by
  obtain ⟨hY0, -⟩ := Steps165.cover_prod_of_std h h1514 hMeets
    (isEmpty_alt7_of_isL3TwoPow hL3)
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hAY : A ≤ Subgroup.normalizer (Y₀ : Set G) := h.mem_y0Star.prop.1.1.2
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1
  set P := CFSG.Open.pCoreOf 2 Y₀ with hP
  have hPle : P ≤ Y₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀
  have hPN : Y₀ ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := h.le_y0.trans hPN
  have hcP : c ∈ Subgroup.normalizer (P : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀) (hAY hcA)
  have hset : (Y₀ : Set G) = (L : Set G) * (P : Set G) := by
    rw [hY0, Subgroup.coe_mul_of_left_le_normalizer_right L P hLP]
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀
  have hcJ : c ∈ Subgroup.normalizer (oPrimeResidualOf 3 X : Set G) :=
    le_normalizer_oPrimeResidualOf (p := 3) hX.prop.1.1.2 hcA
  have hPnorm : (P.subgroupOf Y₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mpr hPN
  have hJP : ((oPrimeResidualOf 3 X ⊓ P).subgroupOf
      (oPrimeResidualOf 3 X)).Normal := by
    haveI : (P.subgroupOf Y₀).Normal := hPnorm
    have h := Subgroup.inf_subgroupOf_inf_normal_of_left (A' := P) (A := Y₀)
      (B := oPrimeResidualOf 3 X)
    rwa [inf_comm P (oPrimeResidualOf 3 X), inf_eq_right.mpr hJY] at h
  have hJP2 : IsPGroup 2 ↥(oPrimeResidualOf 3 X ⊓ P) := by
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    have hdvd : Nat.card ↥(oPrimeResidualOf 3 X ⊓ P) ∣ 2 ^ n :=
      hn ▸ Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := m) hm
  intro j hj
  have hjY : j ∈ Y₀ := hJY hj
  have hjprod : j ∈ (L : Set G) * (P : Set G) := hset ▸ hjY
  obtain ⟨l, hlL, p, hpP, rfl⟩ := hjprod
  have hcommP : ⁅l * p, c⁆ ∈ P :=
    commutatorElement_mul_mem_pCoreOf hLP hcP hLc hlL hpP
  have hcommJ : ⁅l * p, c⁆ ∈ oPrimeResidualOf 3 X := by
    have hconj : c * (l * p)⁻¹ * c⁻¹ ∈ oPrimeResidualOf 3 X :=
      (Subgroup.mem_normalizer_iff.mp hcJ (l * p)⁻¹).mp
        ((oPrimeResidualOf 3 X).inv_mem hj)
    rw [commutatorElement_def,
      show l * p * c * (l * p)⁻¹ * c⁻¹ =
        (l * p) * (c * (l * p)⁻¹ * c⁻¹) by group]
    exact (oPrimeResidualOf 3 X).mul_mem hj hconj
  exact pCoreOf_two_oPrimeResidualOf_le_pPrimeCore X
    (CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left hJP hJP2 ⟨hcommJ, hcommP⟩)

theorem not_delta_pPrimeCore_le (h : Sec17Std G A c L Y₀) (hbot : Item145BotS17)
    (h146 : Item146S14) (hRead : Y4CoreReadR) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (hL3 : IsL3TwoPow L)
    {X : Subgroup G} (hX : X ∈ scriptY3Star A (lB A))
    (hXM : ¬ X ≤ Subgroup.normalizer (Y₀ : Set G))
    (hJY : oPrimeResidualOf 3 X ≤ Y₀) :
    ¬ delta A (lB A) (pPrimeCoreOf 3 X) ≤ Subgroup.normalizer (Y₀ : Set G) := by
  intro hΔM
  have h146' : Item146 A (lB A) := h146 G A c L h.toSec14Std
  have hbot' : ∃ B, IsHyperplane A B ∧ lB A B = ⊥ := hbot G A c L Y₀ h
  have hJD : oPrimeResidualOf 3 X ≤ deltaZero A (lB A) X :=
    oPrimeResidualOf_le_deltaZero h hbot' hX
  have hDJ : deltaZero A (lB A) X ≤
      oPrimeResidualOf 3 X ⊔ pPrimeCoreOf 3 X :=
    deltaZero_le_residual_sup_pPrimeCore h hRead hX.prop
  have hDT : deltaZero A (lB A) X ≤
      Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 X) : Set G) :=
    (deltaZero_le X).trans (le_normalizer_delta_pPrimeCore h h146' hX)
  have hJc : ∀ j ∈ oPrimeResidualOf 3 X, ⁅j, c⁆ ∈ pPrimeCoreOf 3 X :=
    commutatorElement_mem_pPrimeCore h h1514 hMeets hL3 hX hJY
  have hJM : oPrimeResidualOf 3 X ≤ Subgroup.normalizer (Y₀ : Set G) :=
    hJY.trans Subgroup.le_normalizer
  exact deltaZero_not_le_normalizer h hbot' hX hXM
    (deltaZero_le_normalizer_of_delta_le h hX.prop.1.1.2 hJD hDT hDJ hJc hJM hΔM)

theorem pCoreOf_two_deltaZero_ne_bot (h : Sec17Std G A c L Y₀)
    (hbot : Item145BotS17) (h149 : Item149S14)
    {X : Subgroup G} (hX : X ∈ scriptY3Star A (lB A))
    (hXM : ¬ X ≤ Subgroup.normalizer (Y₀ : Set G)) :
    CFSG.Open.pCoreOf 2 (deltaZero A (lB A) X) ≠ ⊥ := by
  have h149' : Item149 A (lB A) := h149 G A c L h.toSec14Std
  have hbot' : ∃ B, IsHyperplane A B ∧ lB A B = ⊥ := hbot G A c L Y₀ h
  set D := deltaZero A (lB A) X with hD
  have hFD : generalizedFitting ↥D = CFSG.pCore 2 ↥D :=
    generalizedFitting_deltaZero_eq h h149' hX
  have hDne : D ≠ ⊥ := fun h0 =>
    deltaZero_not_le_normalizer h hbot' hX hXM (by rw [← hD, h0]; exact bot_le)
  haveI : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hDne
  have hPdone : CFSG.pCore 2 ↥D ≠ ⊥ :=
    Sec15.Push153.pCore_ne_bot_of_nontrivial (X := ↥D) hFD
  intro h0
  apply hPdone
  rw [CFSG.Open.pCoreOf] at h0
  exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp h0

private theorem centralizer_pCoreOf_two_deltaZero_le_delta
    (h : Sec17Std G A c L Y₀) (h142 : Concl142S14) {X : Subgroup G}
    (hVR : CFSG.Open.pCoreOf 2 (deltaZero A (lB A) X) ≤ pPrimeCoreOf 3 X) :
    CFSG.Open.pCoreOf 2 (deltaZero A (lB A) X) ⊓
        Subgroup.centralizer ({c} : Set G) ≤
      delta A (lB A) (pPrimeCoreOf 3 X) := by
  let D := deltaZero A (lB A) X
  let R := pPrimeCoreOf 3 X
  let V := CFSG.Open.pCoreOf 2 D
  have hRpi : IsPiSubgroup (piCompl 3) R :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 X))
  have hAb : IsMulCommutative A := h.isE27.1.1
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_sSup (S := collectionIn (scriptQZero A (lB A)) X)
      fun _ hQ => hQ.1.1.1.2.2
  have hQinv : V ⊓ Subgroup.centralizer ({c} : Set G) ∈
      invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hxC : x ∈ Subgroup.centralizer ({c} : Set G) :=
        (inf_le_right : V ⊓ Subgroup.centralizer ({c} : Set G) ≤
          Subgroup.centralizer ({c} : Set G)) hx
      rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure] at hxC
      exact (Subgroup.centralizer_le_normalizer _) hxC
    · exact isPiSubgroup_piCompl_of_le hRpi (inf_le_left.trans hVR)
    · exact (le_inf
        (hAD.trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D))
        (((Subgroup.le_centralizer_iff_isMulCommutative.mpr hAb).trans
          (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA))).trans
          Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  exact le_delta (mem_scriptQ_of_concl142 (h142 G A c L h.toSec14Std)
    h.zpowers_mem_omegaA hQinv) (inf_le_left.trans hVR)

theorem pCoreOf_two_deltaZero_le_delta (h : Sec17Std G A c L Y₀)
    (hbot : Item145BotS17) (h146 : Item146S14) (hRead : Y4CoreReadR)
    (h142 : Concl142S14) (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (hL3 : IsL3TwoPow L) {X : Subgroup G} (hX : X ∈ scriptY3Star A (lB A))
    (hJY : oPrimeResidualOf 3 X ≤ Y₀) :
    CFSG.Open.pCoreOf 2 (deltaZero A (lB A) X) ≤
      delta A (lB A) (pPrimeCoreOf 3 X) := by
  let D := deltaZero A (lB A) X
  let R := pPrimeCoreOf 3 X
  let ΔR := delta A (lB A) R
  let V := CFSG.Open.pCoreOf 2 D
  let N : Subgroup G := ⁅V, Subgroup.zpowers c⁆
  have h146' : Item146 A (lB A) := h146 G A c L h.toSec14Std
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.prop.1.1.2
  have hJX : oPrimeResidualOf 3 X ≤ X := oPrimeResidualOf_le_self 3 X
  have hDT : D ≤ Subgroup.normalizer (ΔR : Set G) :=
    (deltaZero_le X).trans (le_normalizer_delta_pPrimeCore h h146' hX)
  have hDJ : D ≤ oPrimeResidualOf 3 X ⊔ R :=
    deltaZero_le_residual_sup_pPrimeCore h hRead hX.prop
  have hJc : ∀ j ∈ oPrimeResidualOf 3 X, ⁅j, c⁆ ∈ R :=
    commutatorElement_mem_pPrimeCore h h1514 hMeets hL3 hX hJY
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) D
  have hVD : V ≤ D := CFSG.LieType.BorelTits.pCoreOf_le 2 D
  have hVX : V ≤ X := hVD.trans (deltaZero_le X)
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := by
    obtain ⟨h145, -, h145norm⟩ :=
      rank3II_14_5_lB h.isE27 (hbot G A c L Y₀ h) hX.prop.1.1.2
    calc X = delta A (lB A) X := hX.prop.2
      _ ≤ Subgroup.normalizer (deltaZero A (lB A) X : Set G) := h145norm
  have hXV : X ≤ Subgroup.normalizer (V : Set G) :=
    hXD.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D)
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_sSup (S := collectionIn (scriptQZero A (lB A)) X)
      fun _ hQ => hQ.1.1.1.2.2
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    hAD.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D)
  have hRV : Subgroup.zpowers c ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.zpowers_le.mpr (hAV hcA)
  have hNV : N ≤ V := (Subgroup.le_normalizer_iff_commutator_le_left).mp hRV
  have hVcop : Nat.Coprime 3 (Nat.card V) := by
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hVR : V ≤ R :=
    le_pPrimeCoreOf hVX hXV hVcop
  have hRN : Subgroup.zpowers c ≤ Subgroup.normalizer (N : Set G) := by
    intro a ha
    exact CFSG.GH74.GLS.Balance.SolvComp.mem_normalizer_commutator
      (hRV ha) (Subgroup.le_normalizer ha)
  have hR3 : IsPGroup 3 (Subgroup.zpowers c) := by
    have hcard : Nat.card (Subgroup.zpowers c) = 3 :=
      (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).2.1
    exact IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hN3 : ¬ 3 ∣ Nat.card N := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hVcop
      (h3.trans (Subgroup.card_dvd_of_le hNV))
  have hdec := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le (p := 3)
    (X := V) (N := N) (R := Subgroup.zpowers c) hNV hRV hRN hR3 hN3 le_rfl
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hdec
  have hNΔR : N ≤ ΔR := by
    rw [Subgroup.commutator_le]
    intro v hv t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact commutatorElement_zpow_mem_delta h hAX hJX hDT hDJ hJc v (hVD hv) k
  have hCVΔR : V ⊓ Subgroup.centralizer ({c} : Set G) ≤ ΔR :=
    centralizer_pCoreOf_two_deltaZero_le_delta h h142 hVR
  calc V ≤ V ⊓ Subgroup.centralizer ({c} : Set G) ⊔ N := hdec.ge
    _ ≤ ΔR := sup_le hCVΔR hNΔR

theorem exists_three_prime_witness (h : Sec17Std G A c L Y₀) (hL3 : IsL3TwoPow L)
    (X : Subgroup G) (hX : X ∈ scriptY3Star A (lB A))
    (hXM : ¬ X ≤ Subgroup.normalizer (Y₀ : Set G))
    (hJY : oPrimeResidualOf 3 X ≤ Y₀) (hbot : Item145BotS17) (h146 : Item146S14)
    (h149 : Item149S14) (h142 : Concl142S14) (hRead : Y4CoreReadR)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets) (T : Subgroup G)
    (hT : T ∈ scriptQPiStar A (lB A) X (piOf 2)) :
    ∃ X' ∈ scriptY3 A (lB A), ¬ X' ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      ¬ 3 ∣ Nat.card X' ∧ T ≤ X' := by
  let R := pPrimeCoreOf 3 X
  let ΔR := delta A (lB A) R
  let X' := ΔR ⊔ T
  have h146' : Item146 A (lB A) := h146 G A c L h.toSec14Std
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.prop.1.1.2
  have hRpi : IsPiSubgroup (piCompl 3) R :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X))
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hRinv : R ∈ invariantPiSubgroups ⊤ A (piCompl 3) := ⟨le_top, hRpi, hAR⟩
  have hΔRQ : ΔR ∈ scriptQ A (lB A) := delta_mem_scriptQ h.isE27 h146' hRinv
  have hTQ : T ∈ scriptQ A (lB A) := hT.prop.1.1
  have hXR : X ≤ Subgroup.normalizer (ΔR : Set G) :=
    le_normalizer_delta_pPrimeCore h h146' hX
  have hTΔR : T ≤ Subgroup.normalizer (ΔR : Set G) := hT.prop.1.2.trans hXR
  have hX'Q : X' ∈ scriptQ A (lB A) := by
    simpa [X', sup_comm] using
      sup_mem_scriptQ_of_item146 h.isE27 h146' hTQ hΔRQ hTΔR
  have hX'Δ : X' = delta A (lB A) X' := by
    refine le_antisymm ?_ (delta_le (A := A) (LB := lB A) X')
    exact le_delta (A := A) (LB := lB A) (Q := X') (Y := X') hX'Q le_rfl
  have hX'3 : ¬ 3 ∣ Nat.card X' :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hX'Q.1.2.1
  have hΔRleX : ΔR ≤ X := (delta_le R).trans (pPrimeCoreOf_le 3 X)
  have hX'leX : X' ≤ X := sup_le hΔRleX hT.prop.1.2
  have hX'ne : X' ≠ ⊤ := fun htop => hX.prop.1.1.1 (top_le_iff.mp (htop ▸ hX'leX))
  have hVleΔR : CFSG.Open.pCoreOf 2 (deltaZero A (lB A) X) ≤ ΔR :=
    pCoreOf_two_deltaZero_le_delta h hbot h146 hRead h142 h1514 hMeets hL3 hX hJY
  have hVne : CFSG.Open.pCoreOf 2 (deltaZero A (lB A) X) ≠ ⊥ :=
    pCoreOf_two_deltaZero_ne_bot h hbot h149 hX hXM
  have hVX' : CFSG.Open.pCoreOf 2 (deltaZero A (lB A) X) ≤ X' :=
    hVleΔR.trans le_sup_left
  have hXD : X ≤ Subgroup.normalizer (deltaZero A (lB A) X : Set G) := by
    obtain ⟨-, -, h145norm⟩ :=
      rank3II_14_5_lB h.isE27 (hbot G A c L Y₀ h) hX.prop.1.1.2
    calc X = delta A (lB A) X := hX.prop.2
      _ ≤ Subgroup.normalizer (deltaZero A (lB A) X : Set G) := h145norm
  have hXV : X ≤ Subgroup.normalizer
      (CFSG.Open.pCoreOf 2 (deltaZero A (lB A) X) : Set G) :=
    hXD.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hX'V : X' ≤ Subgroup.normalizer
      (CFSG.Open.pCoreOf 2 (deltaZero A (lB A) X) : Set G) := hX'leX.trans hXV
  have hX'pCoreNe : CFSG.Open.pCoreOf 2 X' ≠ ⊥ := by
    intro h0
    have hle : CFSG.Open.pCoreOf 2 (deltaZero A (lB A) X) ≤ CFSG.Open.pCoreOf 2 X' :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVX' hX'V
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _)
    rw [h0] at hle
    exact hVne (le_bot_iff.mp hle)
  have hX'Y : X' ∈ scriptY A := ⟨hX'ne, hX'Q.1.2.2⟩
  have hX'2 : X' ∈ scriptY2 A := ⟨hX'Y, hX'pCoreNe⟩
  have hX'3' : X' ∈ scriptY3 A (lB A) := ⟨hX'2, hX'Δ⟩
  have hnotM : ¬ X' ≤ Subgroup.normalizer (Y₀ : Set G) := fun hle =>
    not_delta_pPrimeCore_le h hbot h146 hRead h1514 hMeets hL3 hX hXM hJY
      (le_sup_left.trans hle)
  exact ⟨X', hX'3', hnotM, hX'3, le_sup_right⟩

end Red165

theorem red165R_of (hbot : Sec14.Item145BotS17) (h146 : Sec14.Item146S14) (h149 : Item149S14)
    (h142 : Sec14.Concl142S14) (hRead : Sec15.Y4CoreReadR) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) : Red165R := by
  intro G _ _ A c L Y₀ h hL3 X hX hXM _hXnsolv hJY T hT
  exact Red165.exists_three_prime_witness h hL3 X hX hXM hJY hbot h146 h149 h142 hRead
    h1514 hMeets T hT

end CFSG.RankThree.PartTwo.Sec16
