module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieG2

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin

set_option linter.unusedSectionVars false

section G2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem G2_normalizer_le (j : Fin 2) :
    Subgroup.normalizer
        (((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) :
          Subgroup ↥(adjointGroup Tag.G2 K)) : Set ↥(adjointGroup Tag.G2 K)) ≤
      (parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf (adjointGroup Tag.G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  intro c hc
  have hc' : (c : ModGL Tag.G2 K) ∈
      Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) := by
    have key : ∀ v : ↥(adjointGroup Tag.G2 K), (v : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K ↔
        ((c * v * c⁻¹ : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) ∈ posUnipotent Tag.G2 K :=
      fun v => Subgroup.mem_normalizer_iff.1 hc v
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact (key ⟨u, hUC hu⟩).1 hu
    · intro hcu
      have huC : u ∈ adjointGroup Tag.G2 K := by
        have : u = (c : ModGL Tag.G2 K)⁻¹ * ((c : ModGL Tag.G2 K) * u * (c : ModGL Tag.G2 K)⁻¹) *
            (c : ModGL Tag.G2 K) := by group
        rw [this]
        exact mul_mem (mul_mem (inv_mem c.2) (hUC hcu)) c.2
      exact (key ⟨u, huC⟩).2 hcu
  have hB : (c : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := by
    rw [← (borel_self_normalizers Tag.G2 K).1]
    exact ⟨c.2, hc'⟩
  exact borelGroup_le_parabolicSubgroup _ hB

theorem rank2Pkg_g2 {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    Rank2Pkg ↥(adjointGroup Tag.G2 K)
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K))
      (fun j : Fin 2 => (parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf
        (adjointGroup Tag.G2 K)) where
  res := G2_residualOvergroupsAt
  norm j := G2_normalizer_le j
  levi j := by
    obtain ⟨g, hg, hker⟩ := exists_levi_hom_adjoint (τ := Tag.G2) (K := K) hK hf (g2Index j)
    exact ⟨K, inferInstance, inferInstance, inferInstance, f, hK, hf, g, hg, hker⟩
  charTwo j := by
    refine charTwo_perfectCore ?_
    have h := (B113Lie.G2.parabolicData (K := K) hK hf).charTwo
    have hi : ∀ x : Fin Tag.G2.rank, x = Vol2Native.L239.Lie.G2.i0 ∨
        x = Vol2Native.L239.Lie.G2.i1 := by
      rintro ⟨v, hv⟩
      have hv' : v < 2 := hv
      interval_cases v
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hi (g2Index j) with h0 | h1
    · rw [h0]
      exact h _ (Or.inl rfl)
    · rw [h1]
      exact h _ (Or.inr rfl)

end G2

end CFSG.Quasithin.Rk2
