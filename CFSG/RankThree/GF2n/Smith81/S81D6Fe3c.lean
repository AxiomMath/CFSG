module

public import CFSG.RankThree.GF2n.Smith81.S81D6Fe3a

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule
  CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]

@[expose] def IsRootEltL (K : Type) [Field K] (g : ↥(e7Data_valid.minGroup K)) : Prop :=
  ∃ (h : ↥(e7Data_valid.minGroup K)) (β : Fin (Tag.rank .E7) → ℤ) (c : K),
    (h : (Module.End K (V K))ˣ) ∈ Lam K ∧ β ∈ Perp ∧ c ≠ 0 ∧
      g = h * e7Data_valid.xm K β c * h⁻¹

theorem IsRootEltL.exists_conj_theta4 [CharP K 2] {x : ↥(e7Data_valid.minGroup K)}
    (hx : IsRootEltL K x) :
    ∃ p : ↥(e7Data_valid.minGroup K), (p : (Module.End K (V K))ˣ) ∈ Lam K ∧ ∃ c : K, c ≠ 0 ∧
      x = p * e7Data_valid.xm K theta4 c * p⁻¹ := by
  obtain ⟨h, β, c, hh, hβ, hc, rfl⟩ := hx
  obtain ⟨g, hgL, -, hg⟩ := exists_conj_to_theta4_Lam (K := K) hβ
  refine ⟨h * g⁻¹, ?_, c, hc, ?_⟩
  · have : (((h * g⁻¹ : ↥(e7Data_valid.minGroup K))) : (Module.End K (V K))ˣ) =
        (h : (Module.End K (V K))ˣ) * (g : (Module.End K (V K))ˣ)⁻¹ := rfl
    rw [this]
    exact mul_mem hh (inv_mem hgL)
  · rw [← (hg c).1]
    group

end CFSG.RankThree.GF2n.Smith81.D6Spin
