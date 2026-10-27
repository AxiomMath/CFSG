module

public import CFSG.RankThree.PartTwo.Sec18.Statements
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.RankThree.CentralCover.FourGroupWitness
import CFSG.RankThree.PartTwo.Sec18.Transport

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Item183One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    ∀ c ∈ A, c ≠ 1 → ∀ K ∈ thetaComponentsAt 3 c,
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) →
      (∀ a ∈ A, InducesInnerMod a K (CFSG.Open.pCoreOf 2 K)) →
      ∃ E : Subgroup G, IsE27 E ∧ E ≤ (A ⊔ K) ⊓ Subgroup.normalizer (A : Set G) ∧
        (¬ ∃ x : G, ((E ⊓ K : Subgroup G) : Set G) ⊆ (Subgroup.zpowers x : Set G)) ∧
        (¬ ∃ x : G, sectionCentralizer E K (CFSG.Open.pCoreOf 2 K) ⊆
          (Subgroup.zpowers x : Set G)) ∧
        gamma 2 E ≤ M

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_subgroup_eq_sectionCentralizer {E K : Subgroup G}
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) :
    ∃ C : Subgroup G, (C : Set G) = sectionCentralizer E K (CFSG.Open.pCoreOf 2 K) := by
  set R := CFSG.Open.pCoreOf 2 K with hR
  have hER : E ≤ Subgroup.normalizer (R : Set G) :=
    hEK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hmul : ∀ {z₁ z₂ : G}, z₁ ∈ sectionCentralizer E K R → z₂ ∈ sectionCentralizer E K R →
      z₁ * z₂ ∈ sectionCentralizer E K R := by
    rintro z₁ z₂ ⟨h₁E, h₁⟩ ⟨h₂E, h₂⟩
    refine ⟨E.mul_mem h₁E h₂E, fun y hy => ?_⟩
    have e : z₁ * z₂ * y * (z₁ * z₂)⁻¹ * y⁻¹ =
        z₁ * (z₂ * y * z₂⁻¹ * y⁻¹) * z₁⁻¹ * (z₁ * y * z₁⁻¹ * y⁻¹) := by group
    rw [e]
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hER h₁E) _).mp (h₂ y hy)) (h₁ y hy)
  have hinv : ∀ {z : G}, z ∈ sectionCentralizer E K R → z⁻¹ ∈ sectionCentralizer E K R := by
    rintro z ⟨hzE, hz⟩
    refine ⟨E.inv_mem hzE, fun y hy => ?_⟩
    have hy' : z⁻¹ * y * z⁻¹⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hEK (E.inv_mem hzE)) y).mp hy
    have h1 := R.inv_mem (hz _ hy')
    have e : (z * (z⁻¹ * y * z⁻¹⁻¹) * z⁻¹ * (z⁻¹ * y * z⁻¹⁻¹)⁻¹)⁻¹ =
        z⁻¹ * y * z⁻¹⁻¹ * y⁻¹ := by
      group
    rwa [e] at h1
  have hone : (1 : G) ∈ sectionCentralizer E K R :=
    ⟨E.one_mem, fun y _ => by simp⟩
  exact ⟨⟨⟨⟨sectionCentralizer E K R, hmul⟩, hone⟩, hinv⟩, rfl⟩

theorem nine_le_card_of_not_subset_zpowers {C : Subgroup G}
    (hexp : ∀ x ∈ C, x ^ 3 = 1) (hC : ¬ ∃ x : G, (C : Set G) ⊆ (Subgroup.zpowers x : Set G)) :
    9 ≤ Nat.card C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 C := fun g => ⟨1, Subtype.ext (by simpa using hexp g g.2)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  by_contra hlt
  have hn1 : n ≤ 1 := by
    by_contra h2
    have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  apply hC
  have hcyc : IsCyclic C := by
    interval_cases n
    · have : Subsingleton C := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (p := 3) (by simpa using hn)
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  refine ⟨(g : G), fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem le_of_commutator_le_of_gamma_le {E M B R K : Subgroup G} (hE : IsE27 E)
    (hΓ : gamma 2 E ≤ M) (hBE : B ≤ E) (hB : 2 ≤ CFSG.Open.pRank 3 B) (hR2 : IsPGroup 2 R)
    (hER : E ≤ Subgroup.normalizer (R : Set G)) (hKR : K ≤ Subgroup.normalizer (R : Set G))
    (hcomm : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ * b⁻¹ ∈ R) : K ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNB : Subgroup.normalizer (B : Set G) ≤ M := (normalizer_le_gamma hBE hB).trans hΓ
  have hBM : B ≤ M := Subgroup.le_normalizer.trans hNB
  have hRM : R ≤ M := by
    refine (Source.le_aschCore_of_le_normalizer hE.1 hE.2 hR2 hER).trans ?_
    rw [aschCore_eq_gamma_of_isMulCommutative 2 hE.1.1 hE.pRank_eq.ge]
    exact hΓ
  have hconj : ∀ k ∈ K, ∀ x ∈ B ⊔ R, k * x * k⁻¹ ∈ B ⊔ R := by
    intro k hk
    have hle : B ⊔ R ≤ (B ⊔ R).comap (MulAut.conj k).toMonoidHom := by
      refine sup_le (fun b hb => ?_) (fun r hr => ?_)
      · rw [Subgroup.mem_comap]
        change k * b * k⁻¹ ∈ B ⊔ R
        have h1 : k * b * k⁻¹ = (k * b * k⁻¹ * b⁻¹) * b := by group
        rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hcomm k hk b hb))
          (Subgroup.mem_sup_left hb)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hKR hk) r).mp hr)
    intro x hx
    exact hle hx
  have hKN : K ≤ Subgroup.normalizer ((B ⊔ R : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj k hk x, fun hx => ?_⟩
    have := hconj k⁻¹ (K.inv_mem hk) _ hx
    simpa [mul_assoc] using this
  have hB3 : IsPGroup 3 B :=
    (IsPGroup.of_card (n := 3) (by rw [hE.2]; norm_num) : IsPGroup 3 E).to_le hBE
  have hBR : B ⊓ R = ⊥ := Source.inf_eq_bot_of_isPGroup (by norm_num) hB3 hR2
  have hcard : Nat.card (B ⊔ R : Subgroup G) = Nat.card B * Nat.card R := by
    rw [sup_comm, CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer (hBE.trans hER)
      (by rw [inf_comm]; exact hBR), mul_comm]
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 B (B ⊔ R) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_left, hB3, ?_⟩
    have hrel : B.relIndex (B ⊔ R) = Nat.card R := by
      have h1 := Subgroup.relIndex_mul_card B (B ⊔ R)
      rw [inf_eq_left.mpr le_sup_left, hcard] at h1
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h1, mul_comm])
    rw [hrel]
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  exact (le_sup_normalizer_of_isSylowOf hsyl hKN).trans (sup_le (sup_le hBM hRM) hNB)

theorem le_of_item183One (h183 : Item183One) {A M : Subgroup G} (h : Sec18Std G A M) {c : G}
    (hcA : c ∈ A) (hc1 : c ≠ 1) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c)
    (hKiso : Nonempty (K ⧸ CFSG.pCore 2 K ≃*
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (hinner : ∀ a ∈ A, InducesInnerMod a K (CFSG.Open.pCoreOf 2 K)) : K ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE, hEAK, -, hCE, hΓ⟩ := h183 G A M h c hcA hc1 K hK hKiso hinner
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := fun a ha => (hinner a ha).1
  have hEK : E ≤ Subgroup.normalizer (K : Set G) :=
    hEAK.trans (inf_le_left.trans (sup_le hAK Subgroup.le_normalizer))
  set R := CFSG.Open.pCoreOf 2 K with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hER : E ≤ Subgroup.normalizer (R : Set G) :=
    hEK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hKR : K ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  obtain ⟨B, hB⟩ := exists_subgroup_eq_sectionCentralizer hEK
  have hmem : ∀ x ∈ B, x ∈ E ∧ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ R := fun x hx => by
    have hx' : x ∈ (B : Set G) := hx
    rwa [hB] at hx'
  have hBE : B ≤ E := fun x hx => (hmem x hx).1
  have hB9 : 9 ≤ Nat.card B :=
    nine_le_card_of_not_subset_zpowers (fun x hx => hE.1.2 x (hBE hx)) (by rwa [hB])
  have hB2 : 2 ≤ CFSG.Open.pRank 3 B :=
    two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 hBE) hB9
  have hcomm : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ * b⁻¹ ∈ R := by
    intro k hk b hb
    have h1 := R.inv_mem ((hmem b hb).2 k hk)
    have e : (b * k * b⁻¹ * k⁻¹)⁻¹ = k * b * k⁻¹ * b⁻¹ := by group
    rwa [e] at h1
  exact le_of_commutator_le_of_gamma_le hE hΓ hBE hB2 hR2 hER hKR hcomm

end CFSG.RankThree.PartTwo.Sec18
