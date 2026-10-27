module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofOmega

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_delta_centralizer {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y : Subgroup G}
    {d : G} (hY : Y ∈ scriptY4 A LB) (hYd : Y ≤ Subgroup.centralizer ({d} : Set G)) :
    Y ≤ delta A LB (Subgroup.centralizer ({d} : Set G)) :=
  calc Y = delta A LB Y := hY.2.2.1
    _ ≤ _ := delta_mono hYd

omit [Finite G] in
theorem mem_normalizer_sSup {𝒳 : Set (Subgroup G)} {g : G}
    (h : ∀ L ∈ 𝒳, g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer ((sSup 𝒳 : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, (Subgroup.gc_map_comap _).l_sSup, sSup_eq_iSup]
  exact iSup_congr fun L => iSup_congr fun hL => Subgroup.mem_normalizer_iff_map_conj_eq.mp (h L hL)

theorem mem_normalizer_sSup_of_item45 (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G) {d : G}
    (hd : orderOf d = 3) {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d) {y : G}
    (hyC : y ∈ Subgroup.centralizer ({d} : Set G)) {k : ℕ} (hy : y ^ (3 ^ k) = 1) :
    y ∈ Subgroup.normalizer ((sSup 𝒳 : Subgroup G) : Set G) := by
  have hP : IsPGroup 3 (Subgroup.zpowers y) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hyN : y ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute y d := Subgroup.mem_centralizer_singleton_iff.mp hyC
    exact (hc.zpow_right n).symm.eq
  refine mem_normalizer_sSup fun L hL => ?_
  exact Sec12.le_normalizer_of_mem_thetaComponentsAt h45 hG hd (h𝒳 hL) hP
    (Subgroup.zpowers_le.mpr hyN) (Subgroup.mem_zpowers y)

theorem le_of_le_sup_of_le_normalizer {N X Y : Subgroup G}
    (hN : Nat.Coprime 3 (Nat.card N)) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hY : Y = oPrimeResidualOf 3 Y) (hYNX : Y ≤ N ⊔ X)
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) : Y ≤ X := by
  set S := N ⊓ Subgroup.normalizer (X : Set G) with hS
  have hS3 : Nat.Coprime 3 (Nat.card S) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hN
  have hYS : Y ≤ X ⊔ S := by
    intro y hy
    have hy' : y ∈ ((X ⊔ N : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hYNX hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X N hXN] at hy'
    obtain ⟨x, hx, n, hn, rfl⟩ := hy'
    have hnX : n ∈ Subgroup.normalizer (X : Set G) := by
      have e : n = x⁻¹ * (x * n) := by group
      rw [e]
      exact mul_mem (inv_mem (Subgroup.le_normalizer hx)) (hYX hy)
    exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right ⟨hn, hnX⟩)
  calc Y = oPrimeResidualOf 3 Y := hY
    _ ≤ X := Proof15Res7.oPrimeResidualOf_le_of_le_sup_coprime hS3 inf_le_right hYS

section Certified


theorem exists_le_sSup_of_item143Q (h134 : Item134) (h48 : Sec4.Item4_8) (h45 : Sec4.Item4_5)
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h143 : Ronan148Q.Item143Q A (lB A)) {Y : Subgroup G} (hY4 : Y ∈ scriptY4 A (lB A))
    (h3Y : 3 ∣ Nat.card Y) {c₀ : G} {L₀ : Subgroup G} {d : G} {X₁ : Subgroup G}
    (D : Data156 A (lB A) Y c₀ L₀ d X₁) (hΩ : omegaA A ≠ {Subgroup.zpowers c₀})
    (hYd : Y ≤ Subgroup.centralizer ({d} : Set G)) :
    ∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 d ∧ 𝒳.Nonempty ∧ Y ≤ sSup 𝒳 ∧
      (Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          CFSG.Blueprint.NativeSporadic.ON ∨
        Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
          (alternatingGroup (Fin 6)) ∨
        IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have h₀ : Sec14Std G A c₀ L₀ := { h with zpowers_mem_omegaA := D.omega, mem_lA := D.mem_lA }
  have hA : Late.IsE27 A := h₀.isE27
  have hc₀A : c₀ ∈ A := h₀.toSec13Data.mem_A
  obtain ⟨-, hdΩ, hpts⟩ :=
    (Proof153Twin2.omegaA_eq_or_facts_of_data156 h134 h48 h₀ D).resolve_left hΩ
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set O := pPrimeCoreOf 3 C with hO
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hO'C : O' ≤ C :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr D.mem_d))
  have hO'NA : O' ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  have hO'3 : Nat.Coprime 3 (Nat.card O') := coprime_card_pPrimeCoreOf 3 _
  have hO3 : Nat.Coprime 3 (Nat.card O) := coprime_card_pPrimeCoreOf 3 C
  have hYΔ : Y ≤ delta A (lB A) C := le_delta_centralizer hY4 hYd
  obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty (delta A (lB A) C) A (piCompl 3)
  obtain ⟨-, halt⟩ := h143 d D.mem_d D.ne_d hdΩ Q hQ
  rcases halt with h1 | ⟨b, d', Lb, hbΩ, hLb, hJb, hd'A, hd'1, hd'c, hdbd', X, hΔ, hinv, hcase⟩
  ·
    exfalso
    have hdvd : Nat.card (O' ⊔ O : Subgroup G) ∣ Nat.card O' * Nat.card O :=
      card_sup_dvd_card_mul (hO'C.trans hCO)
    have hYle : Y ≤ O' ⊔ O := by
      rw [sup_comm]
      exact h1 ▸ hYΔ
    have h3 : 3 ∣ Nat.card O' * Nat.card O :=
      (h3Y.trans (Subgroup.card_dvd_of_le hYle)).trans hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (Nat.Coprime.mul_right hO'3 hO3) h3
  rcases hcase with ⟨-, -, hne⟩ | ⟨-, ⟨𝒳, h𝒳, hne𝒳, hX𝒳⟩, htypes⟩
  ·
    exfalso
    have hDb : Sec13Data G A b Lb :=
      { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
    have hd'Z : IsZCentral Lb d' := by
      obtain ⟨hd'L, S, hS1, hS2⟩ := hd'c
      obtain ⟨-, -, hθ3, -⟩ :=
        solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
      obtain ⟨hSy, hZ⟩ := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJb hd'L hd'1 S hS1 hS2
      exact ⟨_, hSy, hZ⟩
    have hdc : d ∉ Subgroup.zpowers c₀ := not_mem_zpowers_of_data156 h₀ D
    have hΩb : omegaA A ≠ {Subgroup.zpowers b} := by
      intro heq
      have h1 : Subgroup.zpowers c₀ ∈ ({Subgroup.zpowers b} : Set (Subgroup G)) :=
        heq ▸ D.omega
      have h2 : Subgroup.zpowers (c₀ * d) ∈ ({Subgroup.zpowers b} : Set (Subgroup G)) :=
        heq ▸ hpts d (Subgroup.mem_zpowers d)
      rw [Set.mem_singleton_iff] at h1 h2
      have hcd' : c₀ * d ∈ Subgroup.zpowers c₀ := by
        rw [h1, ← h2]
        exact Subgroup.mem_zpowers _
      apply hdc
      have e : d = c₀⁻¹ * (c₀ * d) := by group
      rw [e]
      exact (Subgroup.zpowers c₀).mul_mem
        ((Subgroup.zpowers c₀).inv_mem (Subgroup.mem_zpowers c₀)) hcd'
    obtain ⟨-, hbk⟩ := Proof15Res11.omega_facts h134 h48 hDb hJb hΩb hd'A hd'1 hd'Z
    have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
    have hd3 : Nat.card (Subgroup.zpowers d) = 3 :=
      Sec13.card_zpowers_of_pow_three (hA.1.2 d D.mem_d) D.ne_d
    have hd'3 : Nat.card (Subgroup.zpowers d') = 3 :=
      Sec13.card_zpowers_of_pow_three (hA.1.2 d' hd'A) hd'1
    have hdd' : d ∉ Subgroup.zpowers d' := fun hm =>
      hne (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hm) (by rw [hd3, hd'3]))
    have hBA : Subgroup.closure {b, d'} ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers d' := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hbd' : b ∉ Subgroup.zpowers d' := by
      intro hm
      apply hdd'
      have hle : Subgroup.closure {b, d'} ≤ Subgroup.zpowers d' := by
        rw [Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact hm
        · exact Subgroup.mem_zpowers _
      exact hle hdbd'
    obtain ⟨k, hk, hkeq⟩ := Proof152ResW.exists_eq_zpowers_mul hA hbA hd'A hd'1 hbd'
      (Subgroup.zpowers_le.mpr (hBA hdbd')) hd3 hne
    exact hdΩ (hkeq ▸ hbk k hk)
  subst hX𝒳
  refine ⟨𝒳, h𝒳, hne𝒳, ?_, htypes⟩
  have hXΔ : sSup 𝒳 ≤ delta A (lB A) C := hΔ ▸ le_sup_right
  have hXC : sSup 𝒳 ≤ C := hXΔ.trans (delta_le C)
  have hO'N : O' ≤ Subgroup.normalizer ((O ⊔ sSup 𝒳 : Subgroup G) : Set G) := by
    rcases hinv with hinv | ⟨-, -, -, hinv⟩
    · exact hO'C.trans hinv
    · exact (le_inf hO'C hO'NA).trans hinv
  have hΔle : delta A (lB A) C ≤ (O ⊔ sSup 𝒳) ⊔ O' := by
    rw [hΔ]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (le_sup_right.trans le_sup_left)
  have hYOX : Y ≤ O ⊔ sSup 𝒳 :=
    calc Y = oPrimeResidualOf 3 Y := hY4.2.1
      _ ≤ O ⊔ sSup 𝒳 :=
        Proof15Res7.oPrimeResidualOf_le_of_le_sup_coprime hO'3 hO'N (hYΔ.trans hΔle)
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d D.mem_d) D.ne_d
  have hYN : Y ≤ Subgroup.normalizer ((sSup 𝒳 : Subgroup G) : Set G) := by
    calc Y = oPrimeResidualOf 3 Y := hY4.2.1
      _ ≤ _ := by
        rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
        rintro y ⟨hy, k, hk⟩
        exact mem_normalizer_sSup_of_item45 h45 h.toTheoremFourHyp hd3 h𝒳 (hYd hy) hk
  exact le_of_le_sup_of_le_normalizer hO3 (hXC.trans hCO) hY4.2.1 hYOX hYN

end Certified

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
