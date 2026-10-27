module

public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PGroups.SolvableTrivialComplementCore

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Steps

variable (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G) (L : Subgroup G)

@[expose] noncomputable def Step167VB : Prop :=
  ∀ Y ∈ scriptY1Star A LB, Hyp1673 A LB c L Y →
    generalizedFitting ↥Y ≠ CFSG.pCore 2 ↥Y → ∀ Y₀ ∈ scriptY0Star A LB,
      ∀ B : Subgroup G, IsHyperplane A B → (∀ F ∈ omegaA A, ¬ F ≤ B) →
        CFSG.Open.pCoreOf 2 Y₀ ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 Y : Set G) ⊓
            Subgroup.centralizer (B : Set G) ≤
          pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔
            pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))

@[expose] noncomputable def Step167O2Loc : Prop :=
  ∀ Y ∈ scriptY1Star A LB, Hyp1673 A LB c L Y →
    generalizedFitting ↥Y ≠ CFSG.pCore 2 ↥Y → ∀ Y₀ ∈ scriptY0Star A LB,
      pPrimeCoreOf 2 Y ≠ ⊥ → A ≤ Subgroup.centralizer (pPrimeCoreOf 2 Y : Set G) →
        Y₀ ≤ Subgroup.centralizer (pPrimeCoreOf 2 Y : Set G) →
          ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧
            A ⊔ Y₀ ⊔ Y ≤ Subgroup.normalizer (T : Set G)

@[expose] noncomputable def Step167EmptyFaith : Prop :=
  ∀ Y ∈ scriptY1Star A LB, Hyp1673 A LB c L Y → scriptY0 A LB = ∅ →
    generalizedFitting ↥Y ≠ CFSG.pCore 2 ↥Y → pPrimeCoreOf 2 Y ≠ ⊥ →
      A ≤ Subgroup.centralizer (pPrimeCoreOf 2 Y : Set G) →
        pPrimeCoreOf 2 Y ⊓ Subgroup.centralizer (L : Set G) = ⊥

end Steps

section Tools

omit [Finite G] in
theorem le_normalizer_centralizer_of_le_normalizer {A P : Subgroup G}
    (h : A ≤ Subgroup.normalizer (P : Set G)) :
    A ≤ Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) := fun a ha =>
  mem_normalizer_of_map_conj_eq (by
    rw [map_conj_centralizer, Late.map_conj_eq_of_mem_normalizer (h ha)])

theorem facts1673 {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h149 : Item149 A (lB A)) (h146 : Item146 A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY1Star A (lB A)) (hsol : Group.IsSolvable ↥Y)
    (hF : generalizedFitting ↥Y ≠ CFSG.pCore 2 ↥Y) :
    pPrimeCoreOf 2 Y ≠ ⊥ ∧ ⁅Y, A⁆ ≤ deltaZero A (lB A) Y ∧
      pPrimeCoreOf 2 Y ⊓ deltaZero A (lB A) Y = ⊥ ∧
      A ≤ Subgroup.centralizer (pPrimeCoreOf 2 Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsE27 A := h.toSec14Std.isE27
  have hA3 : IsPGroup 3 A := hA.isPGroup
  obtain ⟨⟨hY2, hYΔ⟩, hYo⟩ := hY.prop
  have hY3' : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY2.1.2
  have hYinv : Y ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three Y).mpr hY3', hAY⟩
  have hYQ : Y ∈ scriptQ A (lB A) := by
    have := delta_mem_scriptQ hA h146 hYinv
    rwa [← hYΔ] at this
  set X := deltaZero A (lB A) Y with hXdef
  have hYAX : ⁅Y, A⁆ ≤ X := by
    have hcomm : ⁅Y, A⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hAY
    have hAcomm : A ≤ Subgroup.normalizer ((⁅Y, A⁆ : Subgroup G) : Set G) := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.normalizer_commutator_ge_left A Y
    exact le_deltaZero ⟨mem_scriptQ_of_le hYQ hcomm hAcomm,
      (CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
        A Y hA3 hY3' hAY).symm⟩ hcomm
  set Z := pPrimeCoreOf 2 Y with hZdef
  have hZ1 : Z ≠ ⊥ := pPrimeCoreOf_two_ne_bot hsol hF
  have hZY : Z ≤ Y := pPrimeCoreOf_le 2 Y
  have hFX : generalizedFitting ↥X = CFSG.pCore 2 ↥X :=
    rank3II_16_7_1 h.isSimpleGroup h.nonabelian h.charTwoType h149 hY
  have hZX : Z ⊓ X = ⊥ := pPrimeCoreOf_inf_deltaZero_eq_bot hFX
  refine ⟨hZ1, hYAX, hZX, ?_⟩
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have haZ : a ∈ Subgroup.normalizer (Z : Set G) :=
    (hAY.trans (normalizer_le_normalizer_pPrimeCoreOf 2 Y)) ha
  have hk1 : z * a * z⁻¹ * a⁻¹ ∈ Z := by
    have : a * z⁻¹ * a⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp haZ _).mp (inv_mem hz)
    have h2 := mul_mem hz this
    rwa [show z * (a * z⁻¹ * a⁻¹) = z * a * z⁻¹ * a⁻¹ by group] at h2
  have hk2 : z * a * z⁻¹ * a⁻¹ ∈ X := by
    apply hYAX
    have := Subgroup.commutator_mem_commutator (hZY hz) ha
    rwa [commutatorElement_def] at this
  have hk : z * a * z⁻¹ * a⁻¹ = 1 := by
    have : z * a * z⁻¹ * a⁻¹ ∈ Z ⊓ X := ⟨hk1, hk2⟩
    rwa [hZX, Subgroup.mem_bot] at this
  calc z * a = (z * a * z⁻¹ * a⁻¹) * (a * z) := by group
    _ = a * z := by rw [hk, one_mul]

theorem false_of_le_normalizer {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY1Star A (lB A)) (hY3s : Y ∈ scriptY3Star A (lB A))
    {Y₀ : Subgroup G} (hY₀ : Y₀ ∈ scriptY0Star A (lB A))
    (hYM : Y ≤ Subgroup.normalizer (Y₀ : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hY2, hYΔ⟩, hYo⟩ := hY.prop
  have hY3' : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY2.1.2
  obtain ⟨⟨hY₀Y, hY₀o, hY₀Δ, -⟩, hY₀2⟩ := hY₀.prop
  set M := Subgroup.normalizer (Y₀ : Set G) with hMdef
  set Q := CFSG.Open.pCoreOf 2 Y₀ with hQdef
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have hY₀1 : Y₀ ≠ ⊥ := fun h0 => hY₀2.2 (by
    rw [eq_bot_iff, ← h0]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀)
  have hMtop : M ≠ ⊤ := by
    have : IsSimpleGroup G := h.isSimpleGroup
    intro htop
    rcases (Subgroup.normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with h0 | h1
    · exact hY₀1 h0
    · exact hY₀Y.1 h1
  have hmem3 : Y ⊔ Y₀ ∈ scriptY3 A (lB A) := by
    refine ⟨⟨⟨fun htop => hMtop (top_le_iff.mp (htop ▸ sup_le hYM Subgroup.le_normalizer)),
      le_normalizer_sup hAY hY₀Y.2⟩, fun h0 => hY₀2.2 ?_⟩, ?_⟩
    · have hle : Q ≤ CFSG.Open.pCoreOf 2 (Y ⊔ Y₀) :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀).trans le_sup_right)
          (sup_le (hYM.trans hMQ) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)) hQ2
      rw [h0] at hle
      exact le_bot_iff.mp hle
    · refine le_antisymm (sup_le ?_ ?_) (delta_le _)
      · exact hYΔ.le.trans (delta_mono le_sup_left)
      · exact hY₀Δ.le.trans (delta_mono le_sup_right)
  have hle := hY3s.2 hmem3 le_sup_left
  have hY₀le : Y₀ ≤ Y := le_sup_right.trans hle
  apply hY3'
  have hY₀3 : 3 ∣ Nat.card Y₀ := by
    by_contra h3
    exact hY₀1 (hY₀o.trans (oPrimeResidualOf_three_eq_bot_of_not_dvd h3))
  exact hY₀3.trans (Subgroup.card_dvd_of_le hY₀le)

end Tools

section V

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem step167V_of (h : Sec15R G A c L) (h142 : Concl142 A (lB A))
    (hVB : Step167VB A (lB A) c L) : Step167V A (lB A) c L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Y hY hH hF Y₀ hY₀
  have hVB' := hVB Y hY hH hF Y₀ hY₀
  obtain ⟨hY3s, -, -, -⟩ := hH
  obtain ⟨⟨hY2, hYΔ⟩, -⟩ := hY.prop
  have hAab : IsMulCommutative A := h.isElemAbelian.1
  set P := CFSG.Open.pCoreOf 2 Y with hP
  set Q₀ := CFSG.Open.pCoreOf 2 Y₀ with hQ₀
  set V := Q₀ ⊓ Subgroup.centralizer (P : Set G) with hV
  have hQ₀2 : IsPGroup 2 Q₀ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hV2 : IsPGroup 2 V := hQ₀2.to_le inf_le_left
  have h3of2 : ∀ {R : Subgroup G}, IsPGroup 2 R → IsPiSubgroup (piCompl 3) R := fun {R} hR =>
    (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr fun h3 => by
      obtain ⟨k, hk⟩ := hR.exists_card_eq
      rw [hk] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
  have hAY₀ : A ≤ Subgroup.normalizer (Y₀ : Set G) := hY₀.prop.1.1.2
  have hAQ₀ : A ≤ Subgroup.normalizer (Q₀ : Set G) :=
    hAY₀.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    hY2.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    Late.le_normalizer_inf hAQ₀ (le_normalizer_centralizer_of_le_normalizer hAP)
  have hVQ : V ∈ scriptQ A (lB A) := by
    refine mem_scriptQ_iff.mpr ⟨h3of2 hV2, hAV, fun B hB => ?_⟩
    by_cases hΩ : ∃ F ∈ omegaA A, F ≤ B
    · obtain ⟨F, hFΩ, hFB⟩ := hΩ
      obtain ⟨-, -, b, hFb, -⟩ := id hFΩ
      subst hFb
      have hbB : b ∈ B := hFB (Subgroup.mem_zpowers b)
      set R := V ⊓ Subgroup.centralizer (B : Set G) with hR
      have hAB : A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun x hx =>
          congrArg Subtype.val (hAab.is_comm.comm ⟨x, hB.1 hx⟩ ⟨a, ha⟩)
      have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
        Late.le_normalizer_inf hAV (hAB.trans (Subgroup.le_normalizer))
      have hRN : R ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
        inf_le_right.trans ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)).trans
          (centralizer_singleton_le_normalizer_zpowers b))
      have hRinv : R ∈ invariantPiSubgroups
          (Subgroup.normalizer (Subgroup.zpowers b : Set G)) A (piCompl 3) :=
        ⟨hRN, h3of2 (hV2.to_le inf_le_left), hAR⟩
      have hRQ := mem_scriptQ_of_concl142 h142 hFΩ hRinv
      exact (le_inf le_rfl inf_le_right).trans (hRQ.2 B hB)
    · simp only [not_exists, not_and] at hΩ
      exact (hVB' B hB hΩ).trans (le_sup_left.trans le_rfl)
  have hN2 := normalizer_pCoreOf_mem_scriptY2 h.isSimpleGroup h.nonabelian hY2
  set K := Y ⊔ V with hK
  have hKN : K ≤ Subgroup.normalizer (P : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  set Z := delta A (lB A) K with hZ
  have hZK : Z ≤ K := delta_le K
  have hYZ : Y ≤ Z := hYΔ.le.trans (delta_mono le_sup_left)
  have hVZ : V ≤ Z := le_delta hVQ le_sup_right
  have hZ3 : Z ∈ scriptY3 A (lB A) := by
    refine ⟨⟨⟨fun htop => hN2.1.1 (top_le_iff.mp (htop ▸ hZK.trans hKN)),
      le_normalizer_delta K⟩, fun h0 => ?_⟩, (delta_delta K).symm⟩
    have hPZ : P ≤ CFSG.Open.pCoreOf 2 Z :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYZ) (hZK.trans hKN)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    rw [h0] at hPZ
    exact hY2.2 (le_bot_iff.mp hPZ)
  exact hVZ.trans (hY3s.2 hZ3 hYZ)

end V

section O2

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem step167O2_of (h : Sec15R G A c L) (h163 : Item163 A (lB A) c L)
    (hM : Claim17M A (lB A)) (hT : Step167O2Loc A (lB A) c L) : Step167O2 A (lB A) c L := by
  intro Y hY hH hF Y₀ hY₀ hZ1 hZA hY₀Z
  exfalso
  obtain ⟨T, hT1, hT2, hKT⟩ := hT Y hY hH hF Y₀ hY₀ hZ1 hZA hY₀Z
  obtain ⟨-, -, hstar, -, -⟩ := h163 Y₀ hY₀
  have hloc : IsPLocal 2 (Subgroup.normalizer (T : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hT2 hT1
  obtain ⟨M', hTM', hM'⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hmem : M' ∈ CFSG.maximalTwoLocalsContaining ((Y₀ ⊔ A : Subgroup G) : Set G) :=
    ⟨hM', fun x hx => hTM' (hKT ((sup_le le_sup_right le_sup_left : Y₀ ⊔ A ≤ A ⊔ Y₀).trans
      le_sup_left hx))⟩
  rw [hM Y₀ hY₀ hstar, Set.mem_singleton_iff] at hmem
  have hYM : Y ≤ Subgroup.normalizer (Y₀ : Set G) :=
    (le_sup_right.trans hKT).trans (hTM'.trans hmem.le)
  exact false_of_le_normalizer h hY hH.1 hY₀ hYM

end O2

section Empty

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem generalizedFitting_eq_pCore_sup_center {Y : Type*} [Group Y] [Finite Y]
    [Group.IsSolvable Y] (hZ : CFSG.pPrimeCore 2 Y ≤ Subgroup.center Y) :
    generalizedFitting Y = CFSG.pCore 2 Y ⊔ Subgroup.center Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.RankThree.PGroups.generalizedFitting_eq_fittingSubgroup_of_isSolvable]
  refine le_antisymm ?_ (sup_le (pCore_le_fitting Y 2) ?_)
  · rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun p => ?_
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have : Fact (p : ℕ).Prime := ⟨hp⟩
    by_cases hp2 : (p : ℕ) = 2
    · rw [hp2]
      exact le_sup_left
    · refine (le_sSup ⟨CFSG.pCore_normal, ?_⟩ : CFSG.pCore (p : ℕ) Y ≤ CFSG.pPrimeCore 2 Y).trans
        (hZ.trans le_sup_right)
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := (p : ℕ)) (G := Y)).exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  · have hnil : Group.IsNilpotent (Subgroup.center Y) := by
      have : Subgroup.center (Subgroup.center Y) = ⊤ := by
        rw [eq_top_iff]
        intro b _
        rw [Subgroup.mem_center_iff]
        intro c'
        exact Subtype.ext (Subgroup.mem_center_iff.mp b.2 c')
      exact Subgroup.isNilpotent_of_ker_le_center (1 : Subgroup.center Y →* Unit)
        (by rw [this]; exact le_top)
    exact le_sSup ⟨inferInstance, hnil⟩

end Empty

@[expose] noncomputable def Step167VBR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step167VB A (lB A) c L

@[expose] noncomputable def Step167O2LocR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step167O2Loc A (lB A) c L

@[expose] noncomputable def Step167EmptyFaithR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step167EmptyFaith A (lB A) c L

theorem step167VR_of (h142 : Concl142R) (hVB : Step167VBR) : Step167VR :=
  fun G _ _ A c L h => step167V_of h (h142 G A c L h) (hVB G A c L h)

theorem step167O2R_of (h163 : Item163R) (hM : Claim17MR) (hT : Step167O2LocR) : Step167O2R :=
  fun G _ _ A c L h => step167O2_of h (h163 G A c L h) (hM G A c L h) (hT G A c L h)

end CFSG.RankThree.PartTwo.Sec16
