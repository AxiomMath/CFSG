module

import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4A
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4Cent
import CFSG.RankThree.PartTwo.Sec21.Item219LieProofLayer
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.LayerCentralizer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item219LieProof

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Subgroup

theorem commutator_mem_layer_of_model {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (x : X)
    {N : Subgroup Y} (hNC : N ≤ centralizer ({e x} : Set Y))
    (hcomm : ∀ a ∈ centralizer ({e x} : Set Y), ∀ b ∈ centralizer ({e x} : Set Y),
      a * b * a⁻¹ * b⁻¹ ∈ N)
    (hN : CFSG.IsQuasisimple N) :
    ∀ a ∈ centralizer ({x} : Set X), ∀ b ∈ centralizer ({x} : Set X),
      a * b * a⁻¹ * b⁻¹ ∈ CFSG.inSubgroup CFSG.layer (centralizer ({x} : Set X)) := by
  have hK := inSubgroup_layer_eq_of_commutator_mem hNC hcomm hN
  have hmap := CFSG.AGLEmbeddingD2.Wilson.Proving.map_inSubgroup_layer_centralizer e x
  rw [hK] at hmap
  have he : ∀ a ∈ centralizer ({x} : Set X), e a ∈ centralizer ({e x} : Set Y) := by
    intro a ha
    rw [mem_centralizer_singleton_iff] at ha ⊢
    rw [← map_mul, ← map_mul, ha]
  intro a ha b hb
  have h1 : e (a * b * a⁻¹ * b⁻¹) ∈ N := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hcomm _ (he a ha) _ (he b hb)
  rw [← hmap] at h1
  obtain ⟨y, hy, hye⟩ := h1
  have hy' : y = a * b * a⁻¹ * b⁻¹ := e.injective hye
  rw [← hy']
  exact hy


theorem ks219D4_commutator_mem (X : Type) [Group X] [Finite X] (n : ℕ) (hn : 0 < n)
    (hev : Even n) (hX : ChevalleyExceptionalModel X .trialityD4 2 n) (x : X) (hx1 : x ≠ 1)
    (hxc : IsCentral218 (⊤ : Subgroup X) x) :
    ∀ a ∈ centralizer ({x} : Set X), ∀ b ∈ centralizer ({x} : Set X),
      a * b * a⁻¹ * b⁻¹ ∈ CFSG.inSubgroup CFSG.layer (centralizer ({x} : Set X)) := by
  obtain ⟨K, _, _, _, σ, hK, hσ, -, hf1, -, ⟨φ⟩⟩ :=
    Sec4.Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hX
  have hz1 : φ x ≠ 1 := fun h' => hx1 (φ.injective (h'.trans (map_one φ).symm))
  have hzc := (CFSG.AGLEmbeddingD2.Wilson.Proving.isCentral218_top_map_iff φ x).mp hxc
  obtain ⟨hz3, g, hgS⟩ := ks219D4ThreeCentral_holds K n σ hn hev hK hσ (φ x) hz1 hzc
  have hq1 : 2 ^ n % 3 = 1 := by
    obtain ⟨r, hr⟩ := hev
    rw [hr, ← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hs3 : (g * φ x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
  have hs1 : g * φ x * g⁻¹ ≠ 1 := by
    intro h1
    apply hz1
    calc φ x = g⁻¹ * (g * φ x * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨c, R, -, hR2, hR3, hRq, -⟩ :=
    d4_threeA_model Nat.prime_two hf1 (by decide) hq1 hK hσ hgS hs3 hs1
  let e' : X ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := φ.trans (MulAut.conj (c * g))
  have he' : e' x = c * (g * φ x * g⁻¹) * c⁻¹ := by
    simp only [e', MulEquiv.trans_apply, MulAut.conj_apply]
    group
  rw [← he'] at hR2 hR3
  exact commutator_mem_layer_of_model e' x hR2 hR3 hRq

end CFSG.RankThree.PartTwo.Sec21.Item219LieProof
