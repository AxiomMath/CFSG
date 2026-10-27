module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.HyperplaneGeneration

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering233i

open CFSG CFSG.Open

theorem le_iSup_inf_centralizer_of_cover {G : Type*} [Group G] [Finite G] {D A B : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (D : Set G)) (hAe : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hBA : B ≤ A) (hB3 : Nat.card B = 3)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, b * d = d * b) (hD : ¬ 3 ∣ Nat.card D) {ι : Type*} (r : ι → G)
    (hr : ∀ h ∈ A, h ∉ B → ∃ i, r i ∈ B ⊔ Subgroup.zpowers h) :
    D ≤ ⨆ i, D ⊓ Subgroup.centralizer ({r i} : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsMulCommutative A := hAe.1
  letI : CommGroup A := IsMulCommutative.instCommGroup
  letI act : MulDistribMulAction A D :=
    MulDistribMulAction.compHom D (D.normalizerMonoidHom.comp (Subgroup.inclusion hAN))
  have hsmul : ∀ (a : A) (d : D), ((a • d : D) : G) = (a : G) * d * (a : G)⁻¹ := fun a d => rfl
  have hpow : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have htop := CFSG.PreuniquenessRankFour.Helpers.coprime_group_generated_by_prime_fixedSubgroups
    (acting := A) (source := D) 3 hD hpow
  have key : ∀ F : Subgroup D, (∃ K : Subgroup A, (K.index = 1 ∨ K.index = 3) ∧
      ∀ k ∈ K, ∀ e ∈ F, k • e = e) →
      F ≤ (⨆ i, D ⊓ Subgroup.centralizer ({r i} : Set G)).comap D.subtype := by
    rintro F ⟨K, hK, hF⟩ e he
    have hcard : Nat.card K * K.index = 27 := by
      rw [Subgroup.card_mul_index, hA27]
    have hK9 : 9 ≤ Nat.card K := by
      rcases hK with h | h <;> rw [h] at hcard <;> omega
    obtain ⟨k, hkK, hkB⟩ : ∃ k ∈ K, (k : G) ∉ B := by
      by_contra hcon
      push Not at hcon
      have hle : Nat.card K ≤ Nat.card B := by
        have hinj : Function.Injective (fun k : K => (⟨(k : G), hcon k k.2⟩ : B)) := by
          intro x y hxy
          have h1 := congrArg (fun z : B => (z : G)) hxy
          exact Subtype.ext (Subtype.ext h1)
        exact Nat.card_le_card_of_injective _ hinj
      omega
    have hke : (k : G) * e = e * (k : G) := by
      have h1 := congrArg Subtype.val (hF k hkK e he)
      rw [hsmul] at h1
      calc (k : G) * e = (k : G) * e * (k : G)⁻¹ * (k : G) := by group
        _ = e * (k : G) := by rw [h1]
    obtain ⟨i, hi⟩ := hr k k.2 hkB
    have hC : B ⊔ Subgroup.zpowers (k : G) ≤ Subgroup.centralizer ({(e : G)} : Set G) := by
      refine sup_le ?_ ?_
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hBD b hb e e.2
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hke
    have hri := Subgroup.mem_centralizer_singleton_iff.mp (hC hi)
    change (e : G) ∈ ⨆ i, D ⊓ Subgroup.centralizer ({r i} : Set G)
    exact Subgroup.mem_iSup_of_mem i ⟨e.2, Subgroup.mem_centralizer_singleton_iff.mpr hri.symm⟩
  intro d hd
  have hd' : (⟨d, hd⟩ : D) ∈ sSup {fixedGroup : Subgroup D |
      ∃ kernel : Subgroup A, (kernel.index = 1 ∨ kernel.index = 3) ∧
        ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element} := by
    rw [htop]
    exact Subgroup.mem_top _
  have hle : sSup {fixedGroup : Subgroup D |
      ∃ kernel : Subgroup A, (kernel.index = 1 ∨ kernel.index = 3) ∧
        ∀ scalar ∈ kernel, ∀ element ∈ fixedGroup, scalar • element = element} ≤
      (⨆ i, D ⊓ Subgroup.centralizer ({r i} : Set G)).comap D.subtype :=
    sSup_le fun F hF => key F hF
  exact hle hd'

end CFSG.RankThree.PartTwo.Sec21.Hering233i
