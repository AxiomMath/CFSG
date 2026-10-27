module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTransfer
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Basic
public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian)

section Inputs

@[expose] def GGFieldRankTransfer (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K 2]
    (p : ℕ) : Prop :=
  ∀ (σ : K ≃+* K), σ ^ p = 1 → σ ≠ 1 →
    ∀ B : Subgroup (adjointGroup τ K), IsElemAbelian p B →
      ∃ E : Subgroup (adjointGroup τ K), IsElemAbelian p E ∧
        (∀ x ∈ E, entrywiseAdjointAut τ σ x = x) ∧ Nat.card B ≤ p * Nat.card E

theorem ggFieldRankTransfer_of_bounds {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {p a : ℕ} (hp : p.Prime)
    (hRank : GGElemAbelianRankLE (adjointGroup τ K) p a)
    (hExists : ∀ σ : K ≃+* K, σ ^ p = 1 → σ ≠ 1 →
      GGExcElemAbelianExists (adjointGroup τ (fixSubfield σ)) p (a - 1)) :
    GGFieldRankTransfer τ K p := by
  rintro σ hσp hσ1 B hB
  by_cases h0 : a = 0
  · have hB1 : Nat.card B ≤ 1 := by simpa [h0] using hRank B hB
    have hBpos : 0 < Nat.card B := Nat.card_pos
    have hBone : Nat.card B = 1 := by omega
    refine ⟨⊥, CFSG.Open.isElemAbelian_bot p, by simp, ?_⟩
    rw [hBone, Subgroup.card_bot, mul_one]
    exact hp.one_lt.le
  · have hm : 1 ≤ a := Nat.pos_of_ne_zero h0
    obtain ⟨E, hE, hEfix, hcard⟩ :=
      exists_elemAbelian_fixSubfield (τ := τ) (K := K) hp hm σ hσ1 hσp hB
        (hRank B hB) (hExists σ hσp hσ1)
    exact ⟨E, hE, hEfix, hcard⟩

theorem exists_elemAbelian_centralizing_of_mulAut_field {τ : Tag} {K : Type} [Field K] [Finite K]
    [CharP K 2] {G : Type} [Group G] [Finite G] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {ψ : adjointGroup τ K →* G} (hinj : Function.Injective ψ)
    {G₀ Bs : Subgroup G} (hrange : ψ.range = G₀)
    (hcent : Subgroup.centralizer (G₀ : Set G) = ⊥)
    {B : Subgroup (adjointGroup τ K)} (hB : IsElemAbelian p B)
    (hBcard : Nat.card Bs ≤ Nat.card B)
    {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G)) (hyp : orderOf y = p)
    (hNF : ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 →
      (∀ h : adjointGroup τ K, α ≠ MulAut.conj h) →
      ∃ (x : adjointGroup τ K) (σ : K ≃+* K),
        σ ^ p = 1 ∧ σ ≠ 1 ∧ α = MulAut.conj x * entrywiseAdjointAut τ σ)
    (hTransfer : GGFieldRankTransfer τ K p)
    (α : MulAut (adjointGroup τ K))
    (hα : ∀ u : adjointGroup τ K, ψ (α u) = y * ψ u * y⁻¹)
    (hαp : α ^ p = 1) (hnin : ∀ h : adjointGroup τ K, α ≠ MulAut.conj h) :
    ∃ E₀ : Subgroup G, E₀ ≤ G₀ ∧ IsElemAbelian p E₀ ∧ (∀ x ∈ E₀, y * x = x * y) ∧
      Nat.card Bs ≤ p * Nat.card E₀ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hα_ord : orderOf α = p := by
    refine orderOf_eq_prime hαp ?_
    intro h1
    exact hnin 1 (by rw [h1]; exact (map_one (MulAut.conj :
      adjointGroup τ K →* MulAut (adjointGroup τ K))).symm)
  obtain ⟨x, σ, hσp1, hσ1, hα_eq⟩ := hNF α hαp hnin
  have hσp : orderOf σ = p := orderOf_eq_prime hσp1 hσ1
  have hα_ord' : orderOf (MulAut.conj x * entrywiseAdjointAut τ σ) = p := by
    rw [← hα_eq]
    exact hα_ord
  obtain ⟨-, δ, hδ⟩ :=
    CFSG.RankThree.Chevalley.exists_conj_eq_entrywiseAdjointAut_of_orderOf τ
      Nat.prime_two hf K hK hp x σ hσp hα_ord'
  have hδ' : δ * α * δ⁻¹ = entrywiseAdjointAut τ σ := by
    rw [hα_eq]
    exact hδ
  obtain ⟨E, hE, hEfix, hEcard⟩ := hTransfer σ hσp1 hσ1 B hB
  let E₁ : Subgroup (adjointGroup τ K) := E.map δ⁻¹.toMonoidHom
  have hE₁ : IsElemAbelian p E₁ := hE.map δ⁻¹.toMonoidHom
  have hE₁card : Nat.card E₁ = Nat.card E :=
    Subgroup.card_map_of_injective δ⁻¹.injective
  have hE₁fix : ∀ u ∈ E₁, α u = u := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine δ.injective ?_
    have h3 : (δ * α * δ⁻¹) v = v := by
      rw [hδ']
      exact hEfix v hv
    simpa [MulAut.mul_apply] using h3
  let E₀ : Subgroup G := E₁.map ψ
  have hE₀ : IsElemAbelian p E₀ := hE₁.map ψ
  have hE₀card : Nat.card E₀ = Nat.card E₁ := Subgroup.card_map_of_injective hinj
  have hE₀le : E₀ ≤ G₀ := by
    rw [← hrange]
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  have hE₀comm : ∀ u ∈ E₀, y * u = u * y := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 := hα v
    rw [hE₁fix v hv] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1.symm
  refine ⟨E₀, hE₀le, hE₀, hE₀comm, ?_⟩
  calc Nat.card Bs ≤ Nat.card B := hBcard
    _ ≤ p * Nat.card E := hEcard
    _ = p * Nat.card E₀ := by rw [hE₀card, hE₁card]

end Inputs

end CFSG.StandardType
