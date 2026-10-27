module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCOrbIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCOrbK

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

namespace OrbData

variable {Lb Tb A C F H₁ X₁ : Subgroup X} {p : ℕ} (d : OrbData Lb Tb A C F H₁ X₁ p)
include d

theorem twoPTwoIrred_K :
    TwoPTwoIrred (orbK Tb A C F H₁) (orbK Tb A C F H₁ ⊓ Tb) (orb C X₁) p :=
  ⟨⟨d.irr.prime, d.irr.odd, d.oTwoPTwo_K, d.sylowTwo_K, d.sylowP_K⟩, d.irred_K⟩

theorem not_le_pCore : ¬ A ≤ pCoreOf 2 (orbK Tb A C F H₁) := by
  intro hA
  obtain ⟨⟨c, hc⟩, hc1⟩ := (ne_bot_iff_exists_ne_one).1 d.C_ne
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hX₁ : X₁ ≠ ⊥ := fun h => by
    have := d.irr.irred.1
    rw [h] at this
    exact not_lt_bot this
  obtain ⟨⟨x, hx⟩, hx1⟩ := (ne_bot_iff_exists_ne_one).1 hX₁
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hcO : c ∈ pCoreOf 2 (orbK Tb A C F H₁) := hA (d.C_le hc)
  have hxK : x ∈ orbK Tb A C F H₁ := d.XB_le_K (le_orb C X₁ hx)
  have hz1 : x * c * x⁻¹ * c⁻¹ ∈ pCoreOf 2 (orbK Tb A C F H₁) :=
    mul_mem ((mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hxK) c).1 hcO) (inv_mem hcO)
  have hz2 : x * c * x⁻¹ * c⁻¹ ∈ orb C X₁ := by
    rw [show x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) by group]
    exact mul_mem (le_orb C X₁ hx) (conjSub_le_orb hc (mul_mem_conjSub (inv_mem hx)))
  have hz : x * c * x⁻¹ * c⁻¹ = 1 := by
    have hmem : x * c * x⁻¹ * c⁻¹ ∈ orb C X₁ ⊓ pCoreOf 2 (orbK Tb A C F H₁) := ⟨hz2, hz1⟩
    rwa [TwoPTwo.sylowP_inf_pCoreOf d.twoPTwoIrred_K.toTwoPTwo, mem_bot] at hmem
  have hxc : c * x * c⁻¹ = x := by
    calc c * x * c⁻¹ = (x * c * x⁻¹ * c⁻¹)⁻¹ * x := by group
      _ = x := by rw [hz, inv_one, one_mul]
  have hxC : x ∈ centralizer (Lb : Set X) := by
    have := d.mem_centralizer_of_ne hc hc1'
      (mul_mem_conjSub (d.H_le (d.X_le_H hx)) : c * x * c⁻¹ ∈ conjSub c Lb)
    rwa [hxc] at this
  have hmem : x ∈ H₁ ⊓ centralizer (Lb : Set X) := ⟨d.X_le_H hx, hxC⟩
  rw [d.cent, mem_bot] at hmem
  exact hx1' hmem

omit [Finite X] in
theorem conj_mem_F {c : X} (hc : c ∈ Tb) {f : X} (hf : f ∈ F) : c⁻¹ * f * c ∈ F := by
  have := (mem_normalizer_iff.mp (d.F_normal (Tb.inv_mem hc)) f).mp hf
  simpa using this

theorem F_le_pCore : F ≤ pCoreOf 2 (orbK Tb A C F H₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRK : orb C (pCoreOf 2 H₁) ≤ pCoreOf 2 (orbK Tb A C F H₁) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((orb_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 H₁)).trans orb_le_orbK)
      d.K_le_normalizer_R (d.T2.to_le d.R_le_T)
  intro f hf
  have hc : ∀ x ∈ orb C X₁, ⁅f, x⁆ ∈ pCoreOf 2 (orbK Tb A C F H₁) := by
    intro x hx
    refine (iSup_induction (fun c : C => conjSub (c : X) X₁)
      (C := fun y => y ∈ orbK Tb A C F H₁ ∧ ⁅f, y⁆ ∈ pCoreOf 2 (orbK Tb A C F H₁)) hx
      ?_ ?_ ?_).2
    · intro c y hy
      refine ⟨d.XB_le_K (conjSub_le_orb c.2 hy), hRK (conjSub_le_orb c.2 ?_)⟩
      rw [mem_conjSub]
      have e : (c : X)⁻¹ * ⁅f, y⁆ * c = ((c : X)⁻¹ * f * c) * ((c : X)⁻¹ * y * c) *
          ((c : X)⁻¹ * f * c)⁻¹ * ((c : X)⁻¹ * y * c)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact d.F_comm _ (d.conj_mem_F (d.C_le_T c.2) hf) _ (mem_conjSub.1 hy)
    · exact ⟨one_mem _, by simp⟩
    · rintro y z ⟨hyK, hy⟩ ⟨hzK, hz⟩
      refine ⟨mul_mem hyK hzK, ?_⟩
      have e : ⁅f, y * z⁆ = ⁅f, y⁆ * (y * ⁅f, z⁆ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hy ((mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hyK) _).1 hz)
  have h1 := TwoPTwo.mem_sup_of_commutator_mem d.twoPTwoIrred_K.toTwoPTwo (F_le_orbK hf) hc
  obtain ⟨n, hn⟩ := d.T2 ⟨f, d.F_le hf⟩
  exact TwoPTwo.mem_pCoreOf_of_mem_sup d.twoPTwoIrred_K.toTwoPTwo h1 (n := n)
    (by simpa using congrArg Subtype.val hn)

theorem exists_K : ∃ K Y : Subgroup X, TwoPTwoIrred K (K ⊓ Tb) Y p ∧ A ≤ K ∧
    ¬ A ≤ pCoreOf 2 K ∧ F ≤ pCoreOf 2 K ∧ X₁ ≤ Y :=
  ⟨_, _, d.twoPTwoIrred_K, A_le_orbK, d.not_le_pCore, d.F_le_pCore, le_orb C X₁⟩

end OrbData

end CFSG.LocalAnalysis.WeakClosure81.TC914
