module

public import CFSG.RankThree.PartTwo.Sec18.Item187RLemma
public import CFSG.RankThree.PartTwo.Sec18.Item187F2OTwoFiveSup
import CFSG.RankThree.PartTwo.Sec18.SylowPlane

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement Pointwise

section Helpers

variable {G : Type} [Group G]

private theorem f3_mul_mem_of_normalizer {K : Subgroup G} {g k : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K) : g * k * g⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp hg k).mp hk

private theorem f3_inv_mul_mem_of_normalizer {K : Subgroup G} {g k : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hk : k ∈ K) : g⁻¹ * k * g ∈ K :=
  (Subgroup.mem_normalizer_iff''.mp hg k).mp hk

private def f3CommSubgroup (K Q : Subgroup G) (c : G)
    (hK : K ≤ Subgroup.normalizer (Q : Set G)) : Subgroup G where
  carrier := {g | g ∈ K ∧ ⁅g, c⁆ ∈ Q}
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
  mul_mem' := fun {a b} ha hb => by
    refine ⟨mul_mem ha.1 hb.1, ?_⟩
    rw [show ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ by simp only [commutatorElement_def]; group]
    exact mul_mem (f3_mul_mem_of_normalizer (hK ha.1) hb.2) ha.2
  inv_mem' := fun {a} ha => by
    refine ⟨inv_mem ha.1, ?_⟩
    rw [show ⁅a⁻¹, c⁆ = a⁻¹ * (⁅a, c⁆)⁻¹ * a by simp only [commutatorElement_def]; group]
    exact f3_inv_mul_mem_of_normalizer (hK ha.1) (inv_mem ha.2)

private def f3NormCentralizer (K Q : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ Subgroup.normalizer (Q : Set G) ∧ ∀ g ∈ K, ⁅g, z⁆ ∈ Q}
  one_mem' := ⟨one_mem _, fun g _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
  mul_mem' := fun {z w} hz hw => by
    refine ⟨mul_mem hz.1 hw.1, fun g hg => ?_⟩
    rw [show ⁅g, z * w⁆ = ⁅g, z⁆ * (z * ⁅g, w⁆ * z⁻¹) by simp only [commutatorElement_def]; group]
    exact mul_mem (hz.2 g hg) (f3_mul_mem_of_normalizer hz.1 (hw.2 g hg))
  inv_mem' := fun {z} hz => by
    refine ⟨inv_mem hz.1, fun g hg => ?_⟩
    rw [show ⁅g, z⁻¹⁆ = z⁻¹ * (⁅g, z⁆)⁻¹ * z by simp only [commutatorElement_def]; group]
    exact f3_inv_mul_mem_of_normalizer hz.1 (inv_mem (hz.2 g hg))

end Helpers

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

section Certified


theorem MinCex.not_commutator_oTwoFive_le (h1812 : Item181_2) (h184 : Item184_1) (h186 : Item186H)
    (hX : MinCex A M H c X) (hsol : Group.IsSolvable ↥X) (h5 : 5 ∣ Nat.card X) :
    ¬ ⁅oTwoFive X, Subgroup.zpowers c⁆ ≤ CFSG.Open.pCoreOf 2 X := by
  intro hP
  have hcA : c ∈ A := (mem_and_commutator_mem_of_sec18H hX.sec18H).1
  have hcX : c ∈ Subgroup.normalizer (X : Set G) := hX.le_normalizer (Subgroup.mem_sup_left hcA)
  have hcS : c ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ M) : Set G) :=
    le_normalizer_pCoreOf hX.sec18H (Subgroup.mem_sup_left hcA)
  have hcQ : c ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hcX
  have hXQ : X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hXP : X ≤ Subgroup.normalizer (oTwoFive X : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_oTwoFive X)
  have hcP : c ∈ Subgroup.normalizer (oTwoFive X : Set G) :=
    normalizer_le_normalizer_oTwoFive X hcX
  have hPX : oTwoFive X ≤ X := oTwoFive_le X
  have hSX : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤ X := hX.pCoreOf_le
  have hsup : oTwoFive X ⊔ CFSG.Open.pCoreOf 2 (H ⊓ M) = X :=
    MinCex.sup_oTwoFive_eq h186 hX hsol h5
  have hπ : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = 5 :=
    MinCex.card_primeFactors_subset h186 hX hsol h5
  have hF1 : ∀ p ∈ oTwoFive X, ⁅p, c⁆ ∈ CFSG.Open.pCoreOf 2 X := fun p hp =>
    hP (Subgroup.commutator_mem_commutator hp (Subgroup.mem_zpowers c))
  have hF2 : ∀ p ∈ oTwoFive X, ⁅p, c⁻¹⁆ ∈ CFSG.Open.pCoreOf 2 X := by
    intro p hp
    rw [show ⁅p, c⁻¹⁆ = c⁻¹ * (⁅p, c⁆)⁻¹ * c by simp only [commutatorElement_def]; group]
    exact f3_inv_mul_mem_of_normalizer hcQ (inv_mem (hF1 p hp))
  have hHW : ∀ x ∈ CFSG.Open.pCoreOf 2 (H ⊓ M), ∀ y ∈ oTwoFive X,
      ⁅⁅x, c⁆, y⁆ ∈ CFSG.Open.pCoreOf 2 X := by
    intro x hxS y hyP
    have hxN : x ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := hXQ (hSX hxS)
    have hyN : y ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := hXQ (hPX hyP)
    have hy2 : x⁻¹ * (c⁻¹ * y * c) * x ∈ oTwoFive X :=
      f3_inv_mul_mem_of_normalizer (hXP (hSX hxS)) (f3_inv_mul_mem_of_normalizer hcP hyP)
    have key : ⁅⁅x, c⁆, y⁆ = y * (⁅y⁻¹, c⁻¹⁆ *
        (x * ⁅(x⁻¹ * (c⁻¹ * y * c) * x)⁻¹, c⁆ * x⁻¹)) * y⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [key]
    exact f3_mul_mem_of_normalizer hyN (mul_mem (hF2 y⁻¹ (inv_mem hyP))
      (f3_mul_mem_of_normalizer hxN (hF1 _ (inv_mem hy2))))
  have hSc : ∀ x ∈ CFSG.Open.pCoreOf 2 (H ⊓ M), ⁅x, c⁆ ∈ CFSG.Open.pCoreOf 2 X := by
    intro x hxS
    have hxc : ⁅x, c⁆ ∈ CFSG.Open.pCoreOf 2 (H ⊓ M) := by
      rw [show ⁅x, c⁆ = x * (c * x⁻¹ * c⁻¹) by simp only [commutatorElement_def]; group]
      exact mul_mem hxS (f3_mul_mem_of_normalizer hcS (inv_mem hxS))
    have hxcP : ⁅x, c⁆ ∈ oTwoFive X :=
      mem_oTwoFive_of_commutator_mem hsol hπ (hSX hxc) (fun y hy => hHW x hxS y hy)
    exact MinCex.oTwoFive_inf_S hX (Subgroup.mem_inf.mpr ⟨hxcP, hxc⟩)
  have hXT : X ≤ f3CommSubgroup X (CFSG.Open.pCoreOf 2 X) c hXQ := by
    refine hsup.symm.le.trans (sup_le ?_ ?_)
    · intro p hp
      exact ⟨hPX hp, hF1 p hp⟩
    · intro s hs
      exact ⟨hSX hs, hSc s hs⟩
  have hcC : c ∈ f3NormCentralizer X (CFSG.Open.pCoreOf 2 X) :=
    ⟨hcQ, fun g hg => (hXT hg).2⟩
  have hcomm : ⁅X, Subgroup.zpowers c⁆ ≤ CFSG.Open.pCoreOf 2 X := by
    refine Subgroup.commutator_le.mpr fun g hg z hz => ?_
    exact (Subgroup.zpowers_le.mpr hcC hz).2 g hg
  exact MinCex.not_commutator_le hX (MinCex.orderOf_c h184 hX) (MinCex.pCoreOf_le_S h186 hX)
    (MinCex.normalizer_commutator_le h1812 h184 h186 hX) hcomm

end Certified

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
