module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord
open CFSG.RankThree.Classical2 (orthDerived)

theorem ggTBJ_omPlus_stdModel_nf_ns
    {p m r₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hm : 3 ≤ m) (hmo : Odd m) (hpq : p ∣ Nat.card K + 1)
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* OrthRest.RPlus K (m + 1))
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r₀ (OrthRest.RPlus K (m + 1))
      (Set.range (MulAut.conj : OrthRest.RPlus K (m + 1) →* MulAut (OrthRest.RPlus K (m + 1))))
      L' ψ₀ A) :
    ∃ (r : ℕ) (E : Subgroup ((Fin (m + 1) ⊕ Fin (m + 1) → K) ≃ₗ[K]
        (Fin (m + 1) ⊕ Fin (m + 1) → K)))
      (Δ : OrthTorus.TBJOmData (TableBOrth.qPlusForm K (m + 1)) p E r)
      (hE : E ≤ orthDerived (TableBOrth.qPlusForm K (m + 1)))
      (σ : (Fin r → Multiplicative (ZMod p)) →* L')
      (Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A),
      (∀ f, ψ₀ (σ f) = (OrthTorus.rPlusEquiv K (Nat.le_add_left 1 m)).symm (Δ.τΩ hE f)) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∀ v : Fin (m + 1) ⊕ Fin (m + 1) → K, (∀ a ∈ E, a v = v) → v = 0) := by
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m + 1)
  obtain ⟨r, E, Δ, hE, σ, Θ, hσ, hΘ, hW⟩ :=
    ggTBJ_om_stdModel_of_mulEquiv (V := Fin (m + 1) ⊕ Fin (m + 1) → K)
      (Q := TableBOrth.qPlusForm K (m + 1)) hp hp2
      (TableBOrth.nondegenerate_qPlusForm (m + 1))
      (OrthTorus.exists_totallySingular_qPlusForm (n := m) hm)
      (Or.inr hpq) (OrthTorus.rPlusEquiv K (Nat.le_add_left 1 m)) hZ hcp ψ₀ A hA
  refine ⟨r, E, Δ, hE, σ, Θ, hσ, hΘ, hW, Δ.noFixed ?_⟩
  rw [OrthTorus.charSum_qPlusForm m]
  have h := (OrthTorus.modEq_neg_one_of_dvd hpq).pow (m + 1)
  rw [Even.neg_one_pow hmo.add_one] at h
  exact h

theorem ggTBJ_omPlus_stdModel_ns
    {p m r₀ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hm : 3 ≤ m) (hme : Even m) (hpq : p ∣ Nat.card K + 1)
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* OrthRest.RPlus K (m + 1))
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r₀ (OrthRest.RPlus K (m + 1))
      (Set.range (MulAut.conj : OrthRest.RPlus K (m + 1) →* MulAut (OrthRest.RPlus K (m + 1))))
      L' ψ₀ A) :
    ∃ (r : ℕ) (E : Subgroup ((Fin (m + 1) ⊕ Fin (m + 1) → K) ≃ₗ[K]
        (Fin (m + 1) ⊕ Fin (m + 1) → K)))
      (Δ : OrthTorus.TBJOmData (TableBOrth.qPlusForm K (m + 1)) p E r)
      (hE : E ≤ orthDerived (TableBOrth.qPlusForm K (m + 1)))
      (σ : (Fin r → Multiplicative (ZMod p)) →* L')
      (Θ : (Fin r → Multiplicative (ZMod p)) ≃* ↥A),
      (∀ f, ψ₀ (σ f) = (OrthTorus.rPlusEquiv K (Nat.le_add_left 1 m)).symm (Δ.τΩ hE f)) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∃ v : Fin (m + 1) ⊕ Fin (m + 1) → K, v ≠ 0 ∧ ∀ a ∈ E, a v = v) := by
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ m + 1)
  obtain ⟨r, E, Δ, hE, σ, Θ, hσ, hΘ, hW⟩ :=
    ggTBJ_om_stdModel_of_mulEquiv (V := Fin (m + 1) ⊕ Fin (m + 1) → K)
      (Q := TableBOrth.qPlusForm K (m + 1)) hp hp2
      (TableBOrth.nondegenerate_qPlusForm (m + 1))
      (OrthTorus.exists_totallySingular_qPlusForm (n := m) hm)
      (Or.inr hpq) (OrthTorus.rPlusEquiv K (Nat.le_add_left 1 m)) hZ hcp ψ₀ A hA
  refine ⟨r, E, Δ, hE, σ, Θ, hσ, hΘ, hW, Δ.exFixed ?_⟩
  rw [OrthTorus.charSum_qPlusForm m]
  have h := (OrthTorus.modEq_neg_one_of_dvd hpq).pow (m + 1)
  rw [Odd.neg_one_pow (Even.add_one hme)] at h
  exact h

end CFSG.StandardType

end
