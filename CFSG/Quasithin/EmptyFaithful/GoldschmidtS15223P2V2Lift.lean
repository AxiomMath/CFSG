module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P1Z2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem quasithinV2_ne_bot_of_normal {X X₀ : Subgroup G} (hX : X = oPrimeResidualOf 3 X)
    (hXX₀ : X ≤ X₀) (hN : X₀ ≤ Subgroup.normalizer (X : Set G)) (hV : quasithinV2 X ≠ ⊥) :
    quasithinV2 X₀ ≠ ⊥ := by
  intro h0
  have hQ2 : IsPGroup 2 (pCoreOf 2 X₀) := pCoreOf_isPGroup 2 X₀
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 X₀ : Set G) :=
    hXX₀.trans (le_normalizer_pCoreOf 2 X₀)
  have hQX : pCoreOf 2 X₀ ≤ Subgroup.normalizer (X : Set G) := (pCoreOf_le 2 X₀).trans hN
  have hAB : ⁅X, pCoreOf 2 X₀⁆ ≤ Subgroup.centralizer (z2Of X : Set G) := by
    have h1 : ⁅X, pCoreOf 2 X₀⁆ ≤ X ⊓ pCoreOf 2 X₀ := by
      refine Subgroup.commutator_le.mpr fun a ha q hq => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have : q * a⁻¹ * q⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp (hQX hq) a⁻¹).mp (X.inv_mem ha)
        rw [commutatorElement_def]
        simpa [mul_assoc] using X.mul_mem ha this
      · have : a * q * a⁻¹ ∈ pCoreOf 2 X₀ :=
          (Subgroup.mem_normalizer_iff.mp (hXQ ha) q).mp hq
        rw [commutatorElement_def]
        exact (pCoreOf 2 X₀).mul_mem this ((pCoreOf 2 X₀).inv_mem hq)
    have h2 : X ⊓ pCoreOf 2 X₀ ≤ pCoreOf 2 X :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hg, hXQ hg⟩) hQ2.to_inf_right
    exact (h1.trans h2).trans (pCoreOf_le_centralizer_z2Of X)
  have hnotc : ¬ X ≤ Subgroup.centralizer (z2Of X : Set G) := by
    intro hc
    apply hV
    rw [quasithinV2_eq_commutator, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hc
  have hnfix : ¬ X ≤ Subgroup.centralizer
      ((z2Of X ⊓ Subgroup.centralizer (pCoreOf 2 X₀ : Set G) : Subgroup G) : Set G) := by
    intro hfix
    refine hnotc (A4.thompson_axb (isPGroup_z2Of X) (eq_oTwoUpper_of_eq_oPrimeResidual hX)
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_z2Of X))
      (hQX.trans (normalizer_le_normalizer_z2Of X)) ?_ hAB hfix)
    intro b hb
    obtain ⟨k, hk⟩ := hQ2 ⟨b, hb⟩
    refine ⟨k, ?_⟩
    have h1 : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨x, hxX, hxc⟩ := IsConcreteLE.not_le_iff_exists.mp hnfix
  obtain ⟨z, hz, hzx⟩ : ∃ z ∈ z2Of X ⊓ Subgroup.centralizer (pCoreOf 2 X₀ : Set G),
      z * x ≠ x * z := by
    by_contra hall
    push Not at hall
    exact hxc (Subgroup.mem_centralizer_iff.mpr hall)
  obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.mp hz
  have hQ₂ : pCoreOf 2 X ≤ pCoreOf 2 X₀ :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 X).trans hXX₀)
      (hN.trans (normalizer_le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)
  have hzZ : z ∈ z2Of X₀ :=
    Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hQ₂ (z2Of_le_pCoreOf X hzV), hzC⟩,
      z2Of_sq X z hzV⟩
  have hmem : ⁅z, x⁆ ∈ ⁅z2Of X₀, X₀⁆ := Subgroup.commutator_mem_commutator hzZ (hXX₀ hxX)
  rw [← quasithinV2_eq_commutator, h0, Subgroup.mem_bot, commutatorElement_def] at hmem
  apply hzx
  have h1 : z * x * z⁻¹ = x := mul_inv_eq_one.mp (by simpa [mul_assoc] using hmem)
  calc z * x = z * x * z⁻¹ * z := by group
    _ = x * z := by rw [h1]

end S15223

end CFSG.Quasithin
