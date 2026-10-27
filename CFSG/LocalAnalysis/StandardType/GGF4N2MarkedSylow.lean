module

public import CFSG.LocalAnalysis.StandardType.GGF4N2Rank
public import CFSG.LocalAnalysis.StandardType.GGF4N2JModelExclusions
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.RankThree.PartOne.S11d.FinalSylow

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem ggF4N2_exists_marking_conj {G₀ X₀ K Bs : Subgroup G} (hX₀ : X₀ ≤ G₀) (hKX₀ : K ≤ X₀)
    {a y : G} (haX₀ : a ∈ X₀) (haK : a ∈ Subgroup.centralizer (K : Set G)) (ha : orderOf a = 5)
    (hyG₀ : y ∈ G₀) (hyK : y ∈ Subgroup.centralizer (K : Set G)) (hy : orderOf y = 5)
    (hcyc : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (K : Set G) → IsPGroup 5 P → IsCyclic P)
    (hBs : Bs = Subgroup.zpowers y ⊔ (Bs ⊓ K)) :
    ∃ c ∈ G₀ ⊓ Subgroup.centralizer (K : Set G),
      Subgroup.zpowers (c * a * c⁻¹) = Subgroup.zpowers y ∧
      (∀ k ∈ K, c * k * c⁻¹ = k) ∧
      X₀.map (MulAut.conj c).toMonoidHom ≤ G₀ ∧
      K ≤ X₀.map (MulAut.conj c).toMonoidHom ∧
      Bs ≤ X₀.map (MulAut.conj c).toMonoidHom ∧
      (G₀ ≤ X₀.map (MulAut.conj c).toMonoidHom → G₀ ≤ X₀) := by
  obtain ⟨c, hc, hca⟩ := CFSG.RankThree.PartOne.exists_conj_zpowers_eq Nat.prime_five
    (H := G₀ ⊓ Subgroup.centralizer (K : Set G))
    (fun P hP hPp => hcyc P (hP.trans inf_le_right) hPp)
    ⟨hyG₀, hyK⟩ ⟨hX₀ haX₀, haK⟩ ⟨1, by rw [hy, pow_one]⟩ ⟨1, by rw [ha, pow_one]⟩
    (hy.trans ha.symm)
  have hfix : ∀ k ∈ K, c * k * c⁻¹ = k := fun k hk => by
    rw [← (Subgroup.mem_centralizer_iff.mp hc.2) k hk, mul_inv_cancel_right]
  have hXK : K ≤ X₀.map (MulAut.conj c).toMonoidHom := fun k hk =>
    ⟨k, hKX₀ hk, hfix k hk⟩
  refine ⟨c, hc, hca, hfix, ?_, hXK, ?_, fun h g hg => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact G₀.mul_mem (G₀.mul_mem hc.1 (hX₀ hz)) (G₀.inv_mem hc.1)
  · rw [hBs]
    refine sup_le ?_ (inf_le_right.trans hXK)
    rw [← hca, Subgroup.zpowers_le]
    exact ⟨a, haX₀, rfl⟩
  · obtain ⟨z, hz, hzg⟩ := h (G₀.mul_mem (G₀.mul_mem hc.1 hg) (G₀.inv_mem hc.1))
    have hzg' : c * z * c⁻¹ = c * g * c⁻¹ := hzg
    rw [mul_left_inj, mul_right_inj] at hzg'
    exact hzg' ▸ hz

section Original

theorem ggF4N2_mixed_exists_marking_conj {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) {X₀ : Subgroup G} (hX₀ : X₀ ≤ ggG0 5 B x L D J)
    (hKX₀ : K ≤ X₀) {g : G} (hgL : g ∈ L) (hyg : y ∈ K.map (MulAut.conj g).toMonoidHom)
    {a : G} (haX₀ : a ∈ X₀) (haK : a ∈ Subgroup.centralizer (K : Set G)) (ha : orderOf a = 5) :
    ∃ c ∈ ggG0 5 B x L D J ⊓ Subgroup.centralizer (K : Set G),
      Subgroup.zpowers (c * a * c⁻¹) = Subgroup.zpowers y ∧
      (∀ k ∈ K, c * k * c⁻¹ = k) ∧
      X₀.map (MulAut.conj c).toMonoidHom ≤ ggG0 5 B x L D J ∧
      K ≤ X₀.map (MulAut.conj c).toMonoidHom ∧
      Bs ≤ X₀.map (MulAut.conj c).toMonoidHom ∧
      (ggG0 5 B x L D J ≤ X₀.map (MulAut.conj c).toMonoidHom → ggG0 5 B x L D J ≤ X₀) := by
  obtain ⟨-, -, -, hcomp, hcyc⟩ := ggF4N2_sStar_K hR hNbr hL hK
  obtain ⟨-, -, hy, -⟩ := ggF4N2_x_data hR hNbr
  obtain ⟨hBs, -⟩ := ggF4N2_exists_actual_torus_data hR hNbr hL hK
  have hgG₀ : g ∈ ggG0 5 B x L D J := le_ggG0_left 5 B x L D J hgL
  have hKG₀ : K ≤ ggG0 5 B x L D J := le_ggG0_of_ggNbr hNbr
  have hyG₀ : y ∈ ggG0 5 B x L D J := by
    obtain ⟨k, hk, rfl⟩ := hyg
    exact (ggG0 5 B x L D J).mul_mem ((ggG0 5 B x L D J).mul_mem hgG₀ (hKG₀ hk))
      ((ggG0 5 B x L D J).inv_mem hgG₀)
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := Subgroup.mem_centralizer_iff.mpr fun k hk =>
    ((Subgroup.mem_centralizer_iff.mp (hcomp.1 hk)) y rfl).symm
  exact ggF4N2_exists_marking_conj hX₀ hKX₀ haX₀ haK ha hyG₀ hyK hy hcyc hBs

end Original

end CFSG.StandardType

end
