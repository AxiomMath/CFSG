module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck156O2
import CFSG.RankThree.PartTwo.Sec15.Item15Res7ProofEnd
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck156

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem exists_le_of_item143Q (h45 : Sec4.Item4_5) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h143 : Ronan148Q.Item143Q A (lB A)) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) (haΩ : Subgroup.zpowers a ∉ omegaA A) {Y : Subgroup G}
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G))
    (hYΔ : Y ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)))
    (hY3 : Y = oPrimeResidualOf 3 Y) (h3Y : 3 ∣ Nat.card Y) :
    ∃ (b d : G) (Lb : Subgroup G) (𝒳 : Set (Subgroup G)),
      Subgroup.zpowers b ∈ omegaA A ∧ Lb ∈ lA A b ∧
      Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn Lb d ∧ a ∈ Subgroup.closure {b, d} ∧
      𝒳 ⊆ thetaComponentsAt 3 a ∧ 𝒳.Nonempty ∧ Y ≤ sSup 𝒳 ∧
      delta A (lB A) (Subgroup.centralizer ({a} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ sSup 𝒳 ∧
      Ronan148Q.Inv143Q A a d (sSup 𝒳) ∧
      ((∃ X : Subgroup G, 𝒳 = {X} ∧
          X = lB A (Subgroup.closure {a, b}) ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
          Subgroup.zpowers a ≠ Subgroup.zpowers d) ∨
        (Subgroup.zpowers a = Subgroup.zpowers d ∧
          (Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
              CFSG.Blueprint.NativeSporadic.ON ∨
            Sec4.IsTripleCover (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))
              (alternatingGroup (Fin 6)) ∨
            IsCentralProductA6Covers (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳))))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Late.IsE27 A := h.isE27
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set O := pPrimeCoreOf 3 C with hO
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hO'C : O' ≤ C :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  have hO'NA : O' ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  have hO'3 : Nat.Coprime 3 (Nat.card O') := coprime_card_pPrimeCoreOf 3 _
  have hO3 : Nat.Coprime 3 (Nat.card O) := coprime_card_pPrimeCoreOf 3 C
  obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty (delta A (lB A) C) A (piCompl 3)
  obtain ⟨-, halt⟩ := h143 a haA ha1 haΩ Q hQ
  rcases halt with h1 | ⟨b, d, Lb, hbΩ, hLb, hJb, hdA, hd1, hdc, hab, X, hΔ, hinv, hcase⟩
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
  have hXΔ : X ≤ delta A (lB A) C := hΔ ▸ le_sup_right
  have hXC : X ≤ C := hXΔ.trans (delta_le C)
  have hO'N : O' ≤ Subgroup.normalizer ((O ⊔ X : Subgroup G) : Set G) := by
    rcases hinv with hinv | ⟨-, -, -, hinv⟩
    · exact hO'C.trans hinv
    · exact (le_inf hO'C hO'NA).trans hinv
  have hΔle : delta A (lB A) C ≤ (O ⊔ X) ⊔ O' := by
    rw [hΔ]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (le_sup_right.trans le_sup_left)
  have hYOX : Y ≤ O ⊔ X :=
    calc Y = oPrimeResidualOf 3 Y := hY3
      _ ≤ O ⊔ X := Proof15Res7.oPrimeResidualOf_le_of_le_sup_coprime hO'3 hO'N (hYΔ.trans hΔle)
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hA.1.2 a haA) ha1
  obtain ⟨𝒳, h𝒳, hne𝒳, hX𝒳, hrest⟩ : ∃ 𝒳 : Set (Subgroup G), 𝒳 ⊆ thetaComponentsAt 3 a ∧
      𝒳.Nonempty ∧ X = sSup 𝒳 ∧
      ((∃ X' : Subgroup G, 𝒳 = {X'} ∧
          X' = lB A (Subgroup.closure {a, b}) ⊔ inSubgroup (aschbacherSolvableCore 3) X' ∧
          Subgroup.zpowers a ≠ Subgroup.zpowers d) ∨
        (Subgroup.zpowers a = Subgroup.zpowers d ∧
          (Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
              CFSG.Blueprint.NativeSporadic.ON ∨
            Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
              (alternatingGroup (Fin 6)) ∨
            IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X)))) := by
    rcases hcase with ⟨hXmem, hXeq, hne⟩ | ⟨hdd, ⟨𝒳, h𝒳, hne𝒳, hX𝒳⟩, htypes⟩
    · refine ⟨{X}, Set.singleton_subset_iff.mpr hXmem, Set.singleton_nonempty X,
        (sSup_singleton).symm, Or.inl ⟨X, rfl, hXeq, hne⟩⟩
    · exact ⟨𝒳, h𝒳, hne𝒳, hX𝒳, Or.inr ⟨hdd, htypes⟩⟩
  subst hX𝒳
  have hYN : Y ≤ Subgroup.normalizer ((sSup 𝒳 : Subgroup G) : Set G) := by
    calc Y = oPrimeResidualOf 3 Y := hY3
      _ ≤ _ := by
        rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
        rintro y ⟨hy, k, hk⟩
        exact mem_normalizer_sSup_of_item45 h45 h.toTheoremFourHyp ha3 h𝒳 (hYa hy) hk
  have hYX : Y ≤ sSup 𝒳 := le_of_le_sup_of_le_normalizer hO3 (hXC.trans hCO) hY3 hYOX hYN
  exact ⟨b, d, Lb, 𝒳, hbΩ, hLb, hJb, hdA, hd1, hdc, hab, h𝒳, hne𝒳, hYX, hΔ, hinv, hrest⟩

end CFSG.RankThree.PartTwo.Sec15.Liebeck156
