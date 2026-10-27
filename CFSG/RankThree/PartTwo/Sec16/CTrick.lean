module

public import CFSG.RankThree.PartTwo.Sec17.Item17Setup
public import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec14.Item14Statements
public import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.GroupTheory.CommutatorCentralizerIn
public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GH74.GLS.Balance.SolvCompBasic
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements

public section

namespace CFSG.RankThree.PartTwo.Sec16.CTrick

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private theorem commutatorElement_zpow_mem {N : Subgroup G} {c q : G}
    (hcN : c ∈ Subgroup.normalizer (N : Set G)) (hqc : ⁅q, c⁆ ∈ N) :
    ∀ k : ℤ, ⁅q, c ^ k⁆ ∈ N := by
  let H : Subgroup G :=
    { carrier := {t : G | t ∈ Subgroup.zpowers c ∧ ⁅q, t⁆ ∈ N}
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haA, hab⟩ ⟨hbA, hbc⟩
        refine ⟨Subgroup.mul_mem _ haA hbA, ?_⟩
        rw [commutatorElement_mul_right_eq_mul_conj]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haA
        have haN : a ∈ Subgroup.normalizer (N : Set G) := by
          rw [← hk]
          exact Subgroup.zpow_mem (Subgroup.normalizer (N : Set G)) hcN k
        have hconj : a * ⁅q, b⁆ * a⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.mp haN _).mp hbc
        rw [show ⁅q, a⁆ * a * ⁅q, b⁆ * a⁻¹ =
          ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) by group]
        exact N.mul_mem hab hconj
      inv_mem' := by
        rintro a ⟨haA, haN⟩
        refine ⟨Subgroup.inv_mem _ haA, ?_⟩
        rw [commutatorElement_inv_right]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haA
        have haN' : a⁻¹ ∈ Subgroup.normalizer (N : Set G) := by
          rw [← hk, ← zpow_neg]
          exact Subgroup.zpow_mem (Subgroup.normalizer (N : Set G)) hcN (-k)
        have hconj : a⁻¹ * ⁅q, a⁆⁻¹ * (a⁻¹)⁻¹ ∈ N :=
          (Subgroup.mem_normalizer_iff.mp haN' _).mp
            (N.inv_mem haN)
        simpa [commutatorElement_inv] using hconj }
  have hcH : c ∈ H := ⟨Subgroup.mem_zpowers c, hqc⟩
  have hle : Subgroup.zpowers c ≤ H := Subgroup.zpowers_le.mpr hcH
  intro k
  exact (hle (Subgroup.zpow_mem_zpowers c k)).2

theorem centralizer_le_normalizer_y0 (h : Sec17Std G A c L Y₀) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact (Subgroup.centralizer_le_normalizer _).trans h.normalizer_c_le

theorem X_eq_deltaZero_sup (h : Sec17Std G A c L Y₀)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {X : Subgroup G} (hX : X ∈ scriptY3Star A (lB A)) :
    X = deltaZero A (lB A) X ⊔
      (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ X) := by
  obtain ⟨h145, -, -⟩ :=
    rank3II_14_5_lB h.toSec14Std.isE27 hbot hX.prop.1.1.2
  exact hX.prop.2.trans h145

theorem oPrimeResidualOf_le_deltaZero (h : Sec17Std G A c L Y₀)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {X : Subgroup G} (hX : X ∈ scriptY3Star A (lB A)) :
    oPrimeResidualOf 3 X ≤ deltaZero A (lB A) X := by
  obtain ⟨h145, -, h145norm⟩ :=
    rank3II_14_5_lB h.toSec14Std.isE27 hbot hX.prop.1.1.2
  set D := deltaZero A (lB A) X with hD
  set C₀ := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ X with hC₀
  have hXeq : X = D ⊔ C₀ := hX.prop.2.trans h145
  have hXN : X ≤ Subgroup.normalizer (D : Set G) :=
    calc X = delta A (lB A) X := hX.prop.2
      _ ≤ Subgroup.normalizer (D : Set G) := h145norm
  have hC₀D : C₀ ≤ Subgroup.normalizer (D : Set G) := inf_le_right.trans hXN
  have hC₀cop : Nat.Coprime 3 (Nat.card C₀) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro x ⟨hxX, k, hxk⟩
  exact mem_left_of_pow_prime_pow Nat.prime_three hC₀D hC₀cop (hXeq ▸ hxX) hxk

theorem deltaZero_not_le_normalizer (h : Sec17Std G A c L Y₀)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {X : Subgroup G} (hX : X ∈ scriptY3Star A (lB A))
    (hXM : ¬ X ≤ Subgroup.normalizer (Y₀ : Set G)) :
    ¬ deltaZero A (lB A) X ≤ Subgroup.normalizer (Y₀ : Set G) := by
  intro hDM
  have hXeq := X_eq_deltaZero_sup h hbot hX
  have hC₀M : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ X ≤
      Subgroup.normalizer (Y₀ : Set G) :=
    (inf_le_left.trans (pPrimeCoreOf_le 3 _)).trans
      ((Subgroup.centralizer_le_normalizer (A : Set G)).trans h.normalizer_le)
  exact hXM (hXeq.trans_le (sup_le hDM hC₀M))

theorem le_normalizer_delta_pPrimeCore (h : Sec17Std G A c L Y₀) (h146 : Item146 A (lB A))
    {X : Subgroup G} (hX : X ∈ scriptY3Star A (lB A)) :
    X ≤ Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 X) : Set G) := by
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.prop.1.1.2
  have hAR : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 X : Set G) :=
    hAX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hRpi : IsPiSubgroup (piCompl 3) (pPrimeCoreOf 3 X) :=
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (coprime_card_pPrimeCoreOf 3 X))
  have hRinv : pPrimeCoreOf 3 X ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, hRpi, hAR⟩
  have hle := delta_le_normalizer_delta
    (fun Z hZ => delta_mem_scriptQ h.isE27 h146 hZ) hRinv
    (le_normalizer_pPrimeCoreOf 3 X)
  calc X = delta A (lB A) X := hX.prop.2
    _ ≤ _ := hle

theorem delta_normalizer_pCoreOf_mem_scriptY3 (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} {X : Subgroup G} (hX : X ∈ scriptY3 A LB) :
    delta A LB (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X)) ∈ scriptY3 A LB := by
  have hP1 : CFSG.Open.pCoreOf 2 X ≠ ⊥ := hX.1.2
  have hP2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 X) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X
  set P := CFSG.Open.pCoreOf 2 X with hP
  set K := Subgroup.normalizer (P : Set G) with hK
  have hKtop : K ≠ ⊤ := normalizer_ne_top_of_isPGroup hsimp hnab hP1 hP2
  have hXK : X ≤ K := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hXD : X ≤ delta A LB K := by
    calc X = delta A LB X := hX.2
      _ ≤ delta A LB K := delta_mono hXK
  have hPΔ : P ≤ delta A LB K :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXD
  have hO2 : P ≤ CFSG.Open.pCoreOf 2 (delta A LB K) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPΔ (delta_le K) hP2
  have hAΔK : A ≤ Subgroup.normalizer (delta A LB K : Set G) :=
    le_normalizer_sSup fun _ hQ => hQ.1.1.2.2
  refine ⟨⟨⟨?_, hAΔK⟩, ?_⟩, (delta_delta K).symm⟩
  · intro htop
    exact hKtop (top_le_iff.mp (htop ▸ delta_le K))
  · intro h0
    rw [h0] at hO2
    exact hP1 (le_bot_iff.mp hO2)

theorem generalizedFitting_deltaZero_eq (h : Sec17Std G A c L Y₀) (h149 : Item149 A (lB A))
    {X : Subgroup G} (hX : X ∈ scriptY3Star A (lB A)) :
    generalizedFitting ↥(deltaZero A (lB A) X) = CFSG.pCore 2 ↥(deltaZero A (lB A) X) := by
  set P := CFSG.Open.pCoreOf 2 X with hP
  set K := Subgroup.normalizer (P : Set G) with hK
  have hP1 : P ≠ ⊥ := hX.prop.1.2
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X
  have hKmem : K ∈ scriptY A := by
    refine ⟨?_, ?_⟩
    · intro htop
      exact normalizer_ne_top_of_isPGroup h.isSimpleGroup h.nonabelian hP1 hP2 htop
    · rw [hK, hP]
      exact (hX.prop.1.1.2.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)).trans
        (Subgroup.le_normalizer
          (H := Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)))
  have hKloc : IsPLocal 2 K :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hP2 hP1
  have hFK : generalizedFitting ↥K = CFSG.pCore 2 ↥K :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥K 2).mp
      (CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal
        h.toTheoremFourHyp.charTwoType hKloc)
  have hXK : X ≤ K := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hΔK3 : delta A (lB A) K ∈ scriptY3 A (lB A) :=
    delta_normalizer_pCoreOf_mem_scriptY3 h.isSimpleGroup h.nonabelian hX.prop
  have hXleΔK : X ≤ delta A (lB A) K := by
    calc X = delta A (lB A) X := hX.prop.2
      _ ≤ delta A (lB A) K := delta_mono hXK
  have hΔKX : delta A (lB A) K ≤ X := hX.2 hΔK3 hXleΔK
  set D := deltaZero A (lB A) X with hD
  have hD0K : deltaZero A (lB A) K = D := by
    refine le_antisymm ?_ ?_
    · exact sSup_le fun Q hQ =>
        le_deltaZero hQ.1 ((le_delta hQ.1.1 hQ.2).trans hΔKX)
    · exact sSup_le fun Q hQ => le_deltaZero hQ.1 (hQ.2.trans hXK)
  obtain ⟨-, -, -, h9⟩ := h149 K hKmem
  have hFD : generalizedFitting ↥D = CFSG.pCore 2 ↥D := by
    have h := (h9 hFK).2
    rwa [hD0K] at h
  exact hFD

theorem commutator_zpowers_le_delta (h : Sec17Std G A c L Y₀) {X J Q : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hJX : J ≤ X)
    (hDJ : deltaZero A (lB A) X ≤ J ⊔ pPrimeCoreOf 3 X)
    (hJc : ∀ j ∈ J, ⁅j, c⁆ ∈ pPrimeCoreOf 3 X)
    (hQ : Q ∈ scriptQZero A (lB A)) (hQX : Q ≤ X) :
    ⁅Q, Subgroup.zpowers c⁆ ≤ delta A (lB A) (pPrimeCoreOf 3 X) := by
  let R := pPrimeCoreOf 3 X
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAX.trans (normalizer_le_normalizer_pPrimeCoreOf 3 X)
  have hAc : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    ((Subgroup.le_centralizer_iff_isMulCommutative.mpr h.toSec14Std.isE27.1.1).trans
      (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hcA))).trans
      (Subgroup.centralizer_le_normalizer (Subgroup.zpowers c : Set G))
  have hcR : c ∈ Subgroup.normalizer (R : Set G) := hAR hcA
  have hJR : J ≤ Subgroup.normalizer (R : Set G) :=
    hJX.trans (le_normalizer_pPrimeCoreOf 3 X)
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := hQ.1.1.2.2
  have hcQ : c ∈ Subgroup.normalizer (Q : Set G) := hAQ hcA
  have hcommQR : ⁅Q, Subgroup.zpowers c⁆ ≤ Q ⊓ R := by
    rw [Subgroup.commutator_le]
    intro q' hq' t ht
    constructor
    · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ht
      have htQ : t ∈ Subgroup.normalizer (Q : Set G) := by
        rw [← hn]
        exact Subgroup.zpow_mem (Subgroup.normalizer (Q : Set G)) hcQ n
      have hconj : t * q'⁻¹ * t⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp htQ q'⁻¹).mp (Q.inv_mem hq')
      rw [commutatorElement_def,
        show q' * t * q'⁻¹ * t⁻¹ = q' * (t * q'⁻¹ * t⁻¹) by group]
      exact Q.mul_mem hq' hconj
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
      have hq'prod : q' ∈ (J : Set G) * (R : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right J R hJR]
        exact hDJ (le_deltaZero hQ hQX hq')
      obtain ⟨j', hj', r', hr', rfl⟩ := hq'prod
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hjcR : ⁅j', c ^ k⁆ ∈ R :=
        commutatorElement_zpow_mem hcR (hJc j' hj') k
      have hconj : j' * ⁅r', c ^ k⁆ * j'⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hJR hj') _).mp
          (by
            have htR : c ^ k ∈ Subgroup.normalizer (R : Set G) :=
              Subgroup.zpow_mem (Subgroup.normalizer (R : Set G)) hcR k
            have hconj2 : c ^ k * r'⁻¹ * (c ^ k)⁻¹ ∈ R :=
              (Subgroup.mem_normalizer_iff.mp htR r'⁻¹).mp (R.inv_mem hr')
            rw [commutatorElement_def,
              show r' * c ^ k * r'⁻¹ * (c ^ k)⁻¹ =
                r' * (c ^ k * r'⁻¹ * (c ^ k)⁻¹) by group]
            exact R.mul_mem hr' hconj2)
      exact R.mul_mem hconj hjcR
  have hcommQ : ⁅Q, Subgroup.zpowers c⁆ ∈ scriptQ A (lB A) := by
    refine mem_scriptQ_of_le hQ.1 (hcommQR.trans inf_le_left) ?_
    intro a ha
    exact CFSG.GH74.GLS.Balance.SolvComp.mem_normalizer_commutator (hAQ ha) (hAc ha)
  exact le_delta hcommQ (hcommQR.trans inf_le_right)

theorem commutatorElement_zpow_mem_delta (h : Sec17Std G A c L Y₀) {X J : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hJX : J ≤ X)
    (hDT : deltaZero A (lB A) X ≤
      Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 X) : Set G))
    (hDJ : deltaZero A (lB A) X ≤ J ⊔ pPrimeCoreOf 3 X)
    (hJc : ∀ j ∈ J, ⁅j, c⁆ ∈ pPrimeCoreOf 3 X) :
    ∀ x ∈ deltaZero A (lB A) X, ∀ k : ℤ, ⁅x, c ^ k⁆ ∈ delta A (lB A) (pPrimeCoreOf 3 X) := by
  let D := deltaZero A (lB A) X
  let R := pPrimeCoreOf 3 X
  let ΔR := delta A (lB A) R
  let C := CFSG.GroupTheory.commutatorCentralizerIn D ΔR (Subgroup.zpowers c) hDT
  have hCmem : ∀ x : G, x ∈ C ↔ x ∈ D ∧
      ∀ t ∈ Subgroup.zpowers c, ⁅x, t⁆ ∈ ΔR := by
    intro x
    exact CFSG.GroupTheory.mem_commutatorCentralizerIn hDT
  have key : ∀ Q ∈ collectionIn (scriptQZero A (lB A)) X, Q ≤ C := by
    rintro Q ⟨hQ, hQX⟩ q hq
    refine (hCmem q).mpr ⟨le_deltaZero hQ hQX hq, ?_⟩
    intro t ht
    exact (commutator_zpowers_le_delta h hAX hJX hDJ hJc hQ hQX)
      (Subgroup.commutator_mem_commutator hq ht)
  have hDC : D ≤ C := sSup_le key
  intro d hd k
  have hdC : d ∈ D ∧ ∀ t ∈ Subgroup.zpowers c, ⁅d, t⁆ ∈ ΔR :=
    (hCmem d).mp (hDC hd)
  exact hdC.2 (c ^ k) (Subgroup.zpow_mem_zpowers c k)

theorem deltaZero_le_normalizer_of_delta_le (h : Sec17Std G A c L Y₀) {X J : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hJD : J ≤ deltaZero A (lB A) X)
    (hDT : deltaZero A (lB A) X ≤
      Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 X) : Set G))
    (hDJ : deltaZero A (lB A) X ≤ J ⊔ pPrimeCoreOf 3 X)
    (hJc : ∀ j ∈ J, ⁅j, c⁆ ∈ pPrimeCoreOf 3 X)
    (hJM : J ≤ Subgroup.normalizer (Y₀ : Set G))
    (hTM : delta A (lB A) (pPrimeCoreOf 3 X) ≤ Subgroup.normalizer (Y₀ : Set G)) :
    deltaZero A (lB A) X ≤ Subgroup.normalizer (Y₀ : Set G) := by
  let D := deltaZero A (lB A) X
  let R := pPrimeCoreOf 3 X
  let ΔR := delta A (lB A) R
  let D0 := D ⊓ R
  let N : Subgroup G := ⁅D0, Subgroup.zpowers c⁆
  have hJX : J ≤ X := hJD.trans (deltaZero_le X)
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hAD : A ≤ Subgroup.normalizer (deltaZero A (lB A) X : Set G) :=
    le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2
  have hcD : c ∈ Subgroup.normalizer (D : Set G) := hAD hcA
  have hcR : c ∈ Subgroup.normalizer (R : Set G) :=
    (normalizer_le_normalizer_pPrimeCoreOf 3 X) (hAX hcA)
  have hRD0 : Subgroup.zpowers c ≤ Subgroup.normalizer (D0 : Set G) :=
    (le_inf (Subgroup.zpowers_le.mpr hcD) (Subgroup.zpowers_le.mpr hcR)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hNle : N ≤ D0 :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hRD0
  have hD0R : D0 ≤ R := inf_le_right
  have hD0cop : Nat.Coprime 3 (Nat.card D0) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hD0R) (coprime_card_pPrimeCoreOf 3 X)
  have hN3 : ¬ 3 ∣ Nat.card N := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hD0cop
      (h3.trans (Subgroup.card_dvd_of_le hNle))
  have hRN : Subgroup.zpowers c ≤ Subgroup.normalizer (N : Set G) := by
    intro a ha
    exact CFSG.GH74.GLS.Balance.SolvComp.mem_normalizer_commutator
      (hRD0 ha) (Subgroup.le_normalizer ha)
  have hR3 : IsPGroup 3 (Subgroup.zpowers c) := by
    have hcard : Nat.card (Subgroup.zpowers c) = 3 :=
      (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).2.1
    exact IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hdec := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le (p := 3)
    (X := D0) (N := N) (R := Subgroup.zpowers c) hNle hRD0 hRN hR3 hN3 le_rfl
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hdec
  have hNΔR : N ≤ ΔR := by
    rw [Subgroup.commutator_le]
    intro d hd t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact commutatorElement_zpow_mem_delta h hAX hJX hDT hDJ hJc d
      ((inf_le_left : D0 ≤ D) hd) k
  have hD0M : D0 ≤ Subgroup.normalizer (Y₀ : Set G) :=
    hdec.ge.trans (sup_le
      (((inf_le_right : D0 ⊓ Subgroup.centralizer ({c} : Set G) ≤
        Subgroup.centralizer ({c} : Set G)).trans (centralizer_le_normalizer_y0 h)))
      (hNΔR.trans hTM))
  have hJR : J ≤ Subgroup.normalizer (R : Set G) :=
    hJX.trans (le_normalizer_pPrimeCoreOf 3 X)
  have hD_eq : D = J ⊔ D0 := by
    refine le_antisymm ?_ (sup_le hJD inf_le_left)
    intro d hd
    have hdprod : d ∈ (J : Set G) * (R : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right J R hJR]
      exact hDJ hd
    obtain ⟨j, hj, r, hr, rfl⟩ := hdprod
    have hrD : r ∈ D := by
      have hmem : j⁻¹ * (j * r) ∈ D := D.mul_mem (D.inv_mem (hJD hj)) hd
      simpa using hmem
    exact (J ⊔ D0).mul_mem (Subgroup.mem_sup_left hj)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hrD, hr⟩))
  change D ≤ Subgroup.normalizer (Y₀ : Set G)
  rw [hD_eq]
  exact sup_le hJM hD0M

end CFSG.RankThree.PartTwo.Sec16.CTrick
