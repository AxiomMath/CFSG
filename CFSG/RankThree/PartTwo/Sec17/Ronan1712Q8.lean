module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofDelta
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec17.Item17Res13ProofQ8
import CFSG.RankThree.PartTwo.Sec14.Ronan148QA6
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec17.Item17Res12ProofQ8

public section

namespace CFSG.RankThree.PartTwo.Sec17.Ronan1712Q8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec17
  CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem coprime_card_of_isPGroup {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hpq : p ≠ q)
    {H : Subgroup G} (hH : IsPGroup p H) : Nat.Coprime q (Nat.card H) := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes hq hp).mpr (Ne.symm hpq))

theorem commutator_pCoreOf_eq_bot_of_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {D N K Z : Subgroup G} (hKN : K ≤ N) (hND : N ≤ D)
    (hDN : D ≤ Subgroup.normalizer (N : Set G)) (hNK : N ≤ Subgroup.normalizer (K : Set G))
    (hpN : CFSG.Open.pCoreOf p N ≤ K) (hZN : Z ≤ N) (hZ2 : IsPGroup 2 Z)
    (hK : ⁅CFSG.Open.pCoreOf p K, Z⁆ = ⊥) : ⁅CFSG.Open.pCoreOf p D, Z⁆ = ⊥ := by
  set P := CFSG.Open.pCoreOf p D with hPdef
  have hP : IsPGroup p P := CFSG.LieType.BorelTits.pCoreOf_isPGroup p D
  have hPD : P ≤ D := CFSG.LieType.BorelTits.pCoreOf_le p D
  have hDP : D ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf p D
  have hNP : N ≤ Subgroup.normalizer (P : Set G) := hND.trans hDP
  have hKP : K ≤ Subgroup.normalizer (P : Set G) := hKN.trans hNP
  have hZP : Z ≤ Subgroup.normalizer (P : Set G) := hZN.trans hNP
  have h1 : ⁅P, Z⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hZP
  have h2 : ⁅P, Z⁆ ≤ N := by
    have hPN : ⁅N, P⁆ ≤ N := Subgroup.le_normalizer_iff_commutator_le_left.mp (hPD.trans hDN)
    rw [Subgroup.commutator_comm] at hPN
    exact (Subgroup.commutator_mono le_rfl hZN).trans hPN
  have h3 : P ⊓ N ≤ CFSG.Open.pCoreOf p N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p inf_le_right
      (Late.le_normalizer_inf hNP Subgroup.le_normalizer) (hP.to_le inf_le_left)
  have h4 : P ⊓ K ≤ CFSG.Open.pCoreOf p K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p inf_le_right
      (Late.le_normalizer_inf hKP Subgroup.le_normalizer) (hP.to_le inf_le_left)
  have h5 : ⁅P, Z⁆ ≤ CFSG.Open.pCoreOf p K :=
    (le_inf h1 (((le_inf h1 h2).trans h3).trans hpN)).trans h4
  have hP2 : ¬ 2 ∣ Nat.card P :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (coprime_card_of_isPGroup Nat.prime_two hp2 hP)
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 2
    Nat.prime_two Z P hZ2 hP2 hZP
  rw [← hidem, eq_bot_iff, ← hK]
  exact Subgroup.commutator_mono h5 le_rfl

theorem pPrimeCoreOf_sup_le {a : G} {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 a)
    (hXC : X ≤ Subgroup.centralizer ({a} : Set G)) :
    pPrimeCoreOf 3 (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have h := Ronan148Q.pPrimeCoreOf_inf_sup_le (Y := Subgroup.centralizer ({a} : Set G)) hX
  rwa [inf_idem, inf_eq_right.mpr (sup_le (pPrimeCoreOf_le 3 _) hXC)] at h

theorem commutator_pCoreOf_delta_eq_bot {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h143 : Ronan148Q.Item143QS14)
    (hΩ : omegaA A = {Subgroup.zpowers c}) {a : G} (ha : a ∈ A) (hac : a ∉ Subgroup.zpowers c)
    {Z : Subgroup G} (hZ4 : Z ∈ fourGroups A) (hZA : ⁅Z, A⁆ ≠ ⊥) (hZQ : Z ∈ scriptQ A (lB A))
    (hZa : Z ≤ Subgroup.centralizer ({a} : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3)
    (hK : ⁅CFSG.Open.pCoreOf p (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))), Z⁆ = ⊥) :
    ⁅CFSG.Open.pCoreOf p (delta A (lB A) (Subgroup.centralizer ({a} : Set G))), Z⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := HeadProof.isE27_of_std h
  have hAab : IsMulCommutative A := hA.1.1
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hac (Subgroup.one_mem _)
  have haΩ : Subgroup.zpowers a ∉ omegaA A := by
    rw [hΩ, Set.mem_singleton_iff]
    intro heq
    exact hac (heq ▸ Subgroup.mem_zpowers a)
  obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty
    (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A (piCompl 3)
  obtain ⟨-, halt⟩ := h143 G A c L h.toSec14Std a ha ha1 haΩ Qs hQs
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set D := delta A (lB A) C with hD
  set K := pPrimeCoreOf 3 C with hKdef
  set O := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO
  have hZeq : Z = ⁅Z, A⁆ := by
    rcases Sec6.mem_fourGroupsPlus_or_mem_fourGroupsMinus (Sec5.isPGroup_of_isElemAbelian hA.1)
      hZ4 with hP | ⟨hM, -⟩
    · exact absurd hP.2 hZA
    · exact hM.2
  have hZ2 : IsPGroup 2 Z := IsPGroup.of_card (n := 2) (by rw [hZ4.2.2]; norm_num)
  have hZD : Z ≤ D := le_delta hZQ hZa
  have hDC : D ≤ C := delta_le C
  have hCK : C ≤ Subgroup.normalizer (K : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hOA : O ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hOC : O ≤ C := hOA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hAC : A ≤ C := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute hx ha)
  have hcop : ∀ H : Subgroup G, IsPGroup p H → Nat.Coprime 3 (Nat.card H) := fun H hH =>
    coprime_card_of_isPGroup Nat.prime_three hp3 hH
  rcases halt with h1 | ⟨_, _, _, -, -, -, -, -, -, -, X, hDX, hinv, -⟩
  ·
    replace h1 : D = K ⊔ O := h1
    have hZK : Z ≤ K := by
      rw [hZeq]
      exact (Subgroup.commutator_mono (hZD.trans h1.le) le_rfl).trans
        (commutator_sup_le148 (hAC.trans hCK) (hOC.trans hCK) hOA)
    have hKD : K ≤ D := by
      rw [h1]
      exact le_sup_left
    have hDK : D ≤ Subgroup.normalizer (K : Set G) := by
      rw [h1]
      exact sup_le Subgroup.le_normalizer (hOC.trans hCK)
    exact commutator_pCoreOf_eq_bot_of_le hp2 le_rfl hKD hDK Subgroup.le_normalizer
      (CFSG.LieType.BorelTits.pCoreOf_le p K) hZK hZ2 hK
  ·
    replace hDX : D = K ⊔ O ⊔ X := hDX
    have hDeq : D = K ⊔ X ⊔ O := by rw [hDX, sup_right_comm]
    have hND : K ⊔ X ≤ D := by
      rw [hDeq]
      exact le_sup_left
    have hON : O ≤ Subgroup.normalizer ((K ⊔ X : Subgroup G) : Set G) :=
      hOA.trans (hinv.centralizer_le ha)
    have hDN : D ≤ Subgroup.normalizer ((K ⊔ X : Subgroup G) : Set G) := by
      rw [hDeq]
      exact sup_le Subgroup.le_normalizer hON
    have hNC : K ⊔ X ≤ C := hND.trans hDC
    have hpN : CFSG.Open.pCoreOf p (K ⊔ X) ≤ K := by
      have hP := CFSG.LieType.BorelTits.pCoreOf_isPGroup p (K ⊔ X)
      rcases hinv with hfull | ⟨-, hXθ, -, -⟩
      · exact le_pPrimeCoreOf ((CFSG.LieType.BorelTits.pCoreOf_le p _).trans hNC)
          (hfull.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p _))
          (hcop _ hP)
      · exact (le_pPrimeCoreOf (CFSG.LieType.BorelTits.pCoreOf_le p _)
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p _) (hcop _ hP)).trans
          (pPrimeCoreOf_sup_le hXθ (le_sup_right.trans hNC))
    have hZN : Z ≤ K ⊔ X := by
      rw [hZeq]
      exact (Subgroup.commutator_mono (hZD.trans hDeq.le) le_rfl).trans
        (commutator_sup_le148 (hinv.le_normalizer hAab ha) hON hOA)
    exact commutator_pCoreOf_eq_bot_of_le hp2 le_sup_left hND hDN (hNC.trans hCK) hpN hZN hZ2 hK

open Proof17Res12 in
theorem commutator_pCoreOf_eq_bot_of_cfg {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {a : G} {Z R : Subgroup G} (hZ4 : Z ∈ fourGroups A)
    (hZa : Z ≤ Subgroup.centralizer ({a} : Set G))
    (hRa : R ≤ Subgroup.centralizer ({a} : Set G)) (eR : ↥R ≃* QuaternionGroup 2)
    (hRZ : ⁅R, Z⁆ = ⊥) {a' : G} (ha' : a' ∈ A) (ha'a : a' ∈ Subgroup.centralizer ({a} : Set G))
    (hRa' : R ≤ Subgroup.centralizer ({a'} : Set G)) (hZa' : ⁅Z, Subgroup.zpowers a'⁆ ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3' : 3 < p) :
    ⁅CFSG.Open.pCoreOf p (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))), Z⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set K := pPrimeCoreOf 3 C with hKdef
  set P := CFSG.Open.pCoreOf p K with hPdef
  have hP : IsPGroup p P := CFSG.LieType.BorelTits.pCoreOf_isPGroup p K
  have hCP : C ≤ Subgroup.normalizer (P : Set G) := (le_normalizer_pPrimeCoreOf 3 C).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p K)
  obtain ⟨hAZ, hZab, hZcard⟩ := mem_fourGroups_iff.mp hZ4
  have hZ2 : ∀ u ∈ Z, u ^ 2 = 1 := hZab.2
  have hZc : ∀ u ∈ Z, ∀ v ∈ Z, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hZab.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  obtain ⟨d, hd, hwd⟩ : ∃ d ∈ Z, a' * d * a'⁻¹ ≠ d := by
    by_contra hcon
    push Not at hcon
    apply hZa'
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hcon u hu
    calc u * a' = a' * u * a'⁻¹ * a' := by rw [h1]
      _ = a' * u := by group
  obtain ⟨b₁, hb₁, b₂, hb₂, z, hz, hb, hz2, hz1, -⟩ := exists_quaternion_elems eR
  have hRC : R ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hRZ
  have hcomm : ∀ r ∈ R, ∀ u ∈ Z, r * u = u * r := fun r hr u hu =>
    (Subgroup.mem_centralizer_iff.mp (hRC hr) u hu).symm
  have hwz : a' * z = z * a' := (Subgroup.mem_centralizer_singleton_iff.mp (hRa' hz)).symm
  have hZP := Proof17Res13.le_centralizer_of_elems hp hp3'
    (h.toTheoremFourHyp.localRank_lt p hp hp3') hP hZcard hZ2 hZc (hZa.trans hCP) (hCP ha'a)
    (hCP (hRa hz)) (hCP (hRa hb₁)) (hCP (hRa hb₂)) (hAZ ha') (HeadProof.pow_three_of_std h ha')
    hd hwd hz2 hz1 (hcomm z hz) hwz (hcomm b₁ hb₁) (hcomm b₂ hb₂) hb
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  exact hZP

open Proof17Res13 Proof17Res11 in
theorem exists_cfg (hFaith : Step1712Faith) {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {V : Subgroup G}
    (hV : Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      CFSG.Assembly.IsElemAbelian 2 V) V)
    (hVc : ⁅V, Subgroup.zpowers c⁆ = ⊥)
    (hR4 : ∀ R ∈ fourGroups A, R ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) →
      R ≠ ⁅R, Subgroup.zpowers c⁆) :
    ∃ a ∈ A, a ∉ Subgroup.zpowers c ∧ ∃ Z ∈ fourGroups A, Z ∈ scriptQ A (lB A) ∧
      Z ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ⊓
        Subgroup.centralizer ({a} : Set G) ∧ ⁅Z, A⁆ ≠ ⊥ ∧
      ∃ R : Subgroup G, R ≤ Subgroup.centralizer ({a} : Set G) ∧
        Nonempty (↥R ≃* QuaternionGroup 2) ∧ ⁅R, Z⁆ = ⊥ ∧
        ∃ a' ∈ A, R ≤ Subgroup.centralizer ({a'} : Set G) ∧ ⁅Z, Subgroup.zpowers a'⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  obtain ⟨hVM, hMV, hVab⟩ := hV.prop
  have hA : IsE27 A := HeadProof.isE27_of_std h
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
  have hVQ : V ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVM hMV hV2
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hVC : V ≤ Subgroup.centralizer ({c} : Set G) := commutator_zpowers_eq_bot_iff.mp hVc
  have hAM : A ≤ M := Subgroup.le_normalizer.trans h.normalizer_le
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  obtain ⟨a, haA, hac, Z, hZfour, hZVa, hZA, hX⟩ := exists_choice_of hFaith h hV hVc hQ2
    (hAM.trans hMQ) (hVM.trans hMQ) (not_pCoreOf_le_centralizer h)
  have hAZ : A ≤ Subgroup.normalizer (Z : Set G) := (mem_fourGroups_iff.mp hZfour).1
  have hZV : Z ≤ V := hZVa.trans inf_le_left
  have hZa : Z ≤ Subgroup.centralizer ({a} : Set G) := hZVa.trans inf_le_right
  have hZQ : Z ∈ scriptQ A (lB A) := mem_scriptQ_of_le_of_commutator_eq_bot h hMV hV2 hVc hZV hAZ
  have hcZ : Subgroup.zpowers c ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hZV.trans hVC
  obtain ⟨y, hyA, hyZ⟩ : ∃ y ∈ A, y ∉ Subgroup.centralizer (Z : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hZA
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hcon x hx) u hu).symm
  set Q₀ := Q ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer (Z : Set G) with hQ₀def
  have hAa : A ≤ Subgroup.normalizer (Subgroup.centralizer ({a} : Set G) : Set G) :=
    fun x hx => Subgroup.le_normalizer
      (Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute hx haA))
  have hAZC : A ≤ Subgroup.normalizer (Subgroup.centralizer (Z : Set G) : Set G) := fun x hx =>
    Source.mem_normalizer_centralizer (hAZ hx)
  have hAQ₀ : A ≤ Subgroup.normalizer (Q₀ : Set G) :=
    Late.le_normalizer_inf (Late.le_normalizer_inf (hAM.trans hMQ) hAa) hAZC
  have hQ₀2 : IsPGroup 2 Q₀ := hQ2.to_le (inf_le_left.trans inf_le_left)
  have hQ₀c' : ¬ Q₀ ≤ Subgroup.centralizer ({c} : Set G) := fun hle =>
    hX (commutator_zpowers_eq_bot_iff.mpr hle)
  obtain ⟨R, hRp, hcR⟩ := exists_commutatorPiece_not_mem hA.1 hQ₀2 hAQ₀ hcA hQ₀c'
  have hRQ₀ : R ≤ Q₀ := hRp.1
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hRp.2.1.le
  have hRc : ⁅R, Subgroup.zpowers c⁆ = R := commutator_zpowers_eq_of_piece hA.1 hQ₀2 hRp hcA hcR
  have hRQ : R ≤ Q := hRQ₀.trans (inf_le_left.trans inf_le_left)
  obtain ⟨eR⟩ : Nonempty (↥R ≃* QuaternionGroup 2) := by
    rcases Source.IsCommutatorPiece.kleinFour_or_quaternion hA.1 hQ₀2 hRp with hKl | hq
    · exfalso
      obtain ⟨hRab, hR4'⟩ := isElemAbelian_card_of_isKleinFour hKl
      exact hR4 R (mem_fourGroups_iff.mpr ⟨hAR, hRab, hR4'⟩) hRQ hRc.symm
    · exact hq
  have hRcard : Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) * 3 = Nat.card A :=
    hRp.2.2.2.2
  obtain ⟨a', ha'A, ha'R, ha'Z⟩ : ∃ a' ∈ A, a' ∈ Subgroup.centralizer (R : Set G) ∧
      a' ∉ Subgroup.centralizer (Z : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : A ⊓ Subgroup.centralizer (R : Set G) ≤ A ⊓ Subgroup.centralizer (Z : Set G) :=
      fun x hx => ⟨hx.1, hcon x hx.1 hx.2⟩
    have hne : A ⊓ Subgroup.centralizer (Z : Set G) ≠ A := by
      intro heq
      apply hyZ
      have hy : y ∈ A ⊓ Subgroup.centralizer (Z : Set G) := by
        rw [heq]
        exact hyA
      exact hy.2
    have heq := Source.eq_of_le_of_le_of_card_mul_three hle inf_le_left hne hRcard
    apply hcR
    have hcZ' : c ∈ A ⊓ Subgroup.centralizer (Z : Set G) := ⟨hcA, hcZ (Subgroup.mem_zpowers c)⟩
    rw [← heq] at hcZ'
    exact hcZ'.2
  refine ⟨a, haA, hac, Z, hZfour, hZQ, le_inf (hZV.trans hVQ) hZa, hZA, R,
    hRQ₀.trans (inf_le_left.trans inf_le_right), ⟨eR⟩,
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hRQ₀.trans inf_le_right), a', ha'A, ?_, ?_⟩
  · intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp ha'R r hr
  · intro hbot
    apply ha'Z
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mp (commutator_zpowers_eq_bot_iff.mp hbot hu)

theorem step1712DeltaQ8_of_faith (hFaith : Step1712Faith) (h143 : Ronan148Q.Item143QS14) :
    Step1712DeltaQ8 := by
  intro G _ _ A c L Y₀ h V hV hVc hΩ hR4
  obtain ⟨a, ha, hac, Z, hZ4, hZQ, hZM, hZA, R, hRa, ⟨eR⟩, hRZ, a', ha', hRa', hZa'⟩ :=
    exists_cfg hFaith h hV hVc hR4
  refine Or.inr ⟨a, ha, hac, Or.inr ⟨Z, hZ4, hZQ, hZM, fun p hp hp2 hp3 => ?_⟩⟩
  have hp3' : 3 < p := by
    have := hp.two_le
    omega
  have ha'a : a' ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute ha' ha)
  exact commutator_pCoreOf_delta_eq_bot h h143 hΩ ha hac hZ4 hZA hZQ (hZM.trans inf_le_right) hp
    hp2 hp3 (commutator_pCoreOf_eq_bot_of_cfg h hZ4 (hZM.trans inf_le_right) hRa eR hRZ ha' ha'a
      hRa' hZa' hp hp3')

end CFSG.RankThree.PartTwo.Sec17.Ronan1712Q8
