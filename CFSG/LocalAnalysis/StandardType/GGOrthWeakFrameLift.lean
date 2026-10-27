module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType

namespace OrthTorus

theorem mem_normalizer_of_conj_mem_range {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} {H : Type} [Group H] (ψ : H →* G) (β : ↥Bs →* H)
    (hBs : CFSG.Assembly.IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hcompat : ∀ (b : ↥Bs) (y : H), ψ (β b * y * (β b)⁻¹) = (b : G) * ψ y * (b : G)⁻¹)
    (hcomm : ∀ b b' : ↥Bs, β b * β b' = β b' * β b)
    {w : H} (hw : ∀ b : ↥Bs, ∃ b' : ↥Bs, w * β b * w⁻¹ = β b') :
    ψ w ∈ Subgroup.normalizer (Bs : Set G) := by
  let c : ↥Bs → G := fun b => (ψ (β b))⁻¹ * (b : G)
  have hc_comm : ∀ (b : ↥Bs) (y : H), c b * ψ y = ψ y * c b := by
    intro b y
    have h1 : ψ (β b) * ψ y * (ψ (β b))⁻¹ = (b : G) * ψ y * (b : G)⁻¹ := by
      rw [← hcompat b y, map_mul, map_mul, map_inv]
    have h2 : (b : G) * ψ y = ψ (β b) * ψ y * (ψ (β b))⁻¹ * (b : G) := by
      rw [h1]
      group
    calc
      c b * ψ y = (ψ (β b))⁻¹ * ((b : G) * ψ y) := by simp only [c]; group
      _ = (ψ (β b))⁻¹ * (ψ (β b) * ψ y * (ψ (β b))⁻¹ * (b : G)) := by rw [h2]
      _ = ψ y * c b := by simp only [c]; group
  have hmem : ∀ b : ↥Bs, ψ (β b) ∈ Bs := by
    intro b
    refine hSC (ψ (β b)) ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      let b' : ↥Bs := ⟨x, hx⟩
      have hx_eq : x = ψ (β b') * c b' := by
        simp [c]
        rfl
      have h1 : Commute (ψ (β b)) (ψ (β b')) := by
        show ψ (β b) * ψ (β b') = ψ (β b') * ψ (β b)
        rw [← map_mul ψ (β b) (β b'), ← map_mul ψ (β b') (β b), hcomm b b']
      have h2 : Commute (ψ (β b)) (c b') := (hc_comm b' (β b)).symm
      rw [hx_eq]
      exact (h1.mul_right h2).symm
    · have hbp : b ^ p = 1 := by
        apply Subtype.ext
        simpa using hBs.2 (b : G) b.2
      rw [← map_pow, ← map_pow, hbp]
      simp
  have hc_mem : ∀ b : ↥Bs, c b ∈ Bs := by
    intro b
    simpa [c] using Bs.mul_mem (Bs.inv_mem (hmem b)) b.2
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  let b : ↥Bs := ⟨n, hn⟩
  obtain ⟨b', hb'⟩ := hw b
  have hn_eq : n = ψ (β b) * c b := by
    simp [c]
    rfl
  have hconj : ψ w * ψ (β b) * (ψ w)⁻¹ = ψ (β b') := by
    rw [← hb']
    simp only [map_mul, map_inv]
  have hkey : ψ w * n * (ψ w)⁻¹ = c b * ψ (β b') := by
    calc
      ψ w * n * (ψ w)⁻¹ = ψ w * (ψ (β b) * c b) * (ψ w)⁻¹ := by rw [hn_eq]
      _ = ψ w * (c b * ψ (β b)) * (ψ w)⁻¹ := by rw [← hc_comm b (β b)]
      _ = (ψ w * c b) * ψ (β b) * (ψ w)⁻¹ := by group
      _ = (c b * ψ w) * ψ (β b) * (ψ w)⁻¹ := by rw [← hc_comm b w]
      _ = c b * (ψ w * ψ (β b) * (ψ w)⁻¹) := by group
      _ = c b * ψ (β b') := by rw [hconj]
  rw [hkey]
  exact Bs.mul_mem (hc_mem b) (hmem b')

end OrthTorus

end CFSG.StandardType

end
