module

public import CFSG.RankThree.GF2n.Smith81.Orth213LemmaQA

public section

open CFSG.ClassicalGroups.Orthogonal (eichler)

namespace CFSG.RankThree.GF2n.Smith81.Orth213

section LemmaQ

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def ClassE (X : ((ι → K) × (ι → K)) → ((ι → K) × (ι → K))) : Prop :=
  ∃ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 ∧ g ≠ 1 ∧ (g - 1) * (g - 1) = 0 ∧
    ∀ p, X p = orthTensor g id p

@[expose] def ClassA (qU : QuadraticForm K (ι → K))
    (X : ((ι → K) × (ι → K)) → ((ι → K) × (ι → K))) : Prop :=
  ∃ u w : ι → K, qU u = 0 ∧ qU w = 0 ∧ QuadraticMap.polar qU u w = 0 ∧
    LinearIndependent K ![u, w] ∧ ∀ p, X p = orthTensor 1 ⇑(eichler qU u w) p

theorem lemmaQ (qU : QuadraticForm K (ι → K))
    (hnd : ∀ u : ι → K, (∀ v : ι → K, QuadraticMap.polar qU u v = 0) → u = 0)
    (hsing : ∃ p : ι → K, p ≠ 0 ∧ qU p = 0)
    (X Y : ((ι → K) × (ι → K)) ≃ₗ[K] ((ι → K) × (ι → K)))
    (hX : ClassE (K := K) (ι := ι) X ∨ ClassA qU X)
    (hY : ClassE (K := K) (ι := ι) Y ∨ ClassA qU Y) :
    (∃ v, v ∈ LinearMap.range ((X : ((ι → K) × (ι → K)) →ₗ[K] ((ι → K) × (ι → K))) - 1) ∧
        Y v = v ∧ PairTypeA qU v) ∨
    (∃ k : ℕ, Odd k ∧ (X * Y) ^ k = 1 ∧
      ∀ v ∈ LinearMap.range ((X : ((ι → K) × (ι → K)) →ₗ[K] ((ι → K) × (ι → K))) - 1),
        (X * Y) v = v → v = 0) := by
  have hE : ∀ {Z : ((ι → K) × (ι → K)) ≃ₗ[K] ((ι → K) × (ι → K))},
      ClassE (K := K) (ι := ι) Z →
      ∃ N : Matrix (Fin 2) (Fin 2) K, N ≠ 0 ∧ N * N = 0 ∧
        ∀ p, Z p = orthTensor (1 + N) id p := by
    rintro Z ⟨g, -, hg1, hg2, hg3⟩
    refine ⟨g - 1, sub_ne_zero.mpr hg1, hg2, fun p => ?_⟩
    rw [hg3, add_sub_cancel]
  have hA : ∀ {Z : ((ι → K) × (ι → K)) ≃ₗ[K] ((ι → K) × (ι → K))}, ClassA qU Z →
      ∃ u w : ι → K, qU u = 0 ∧ qU w = 0 ∧ QuadraticMap.polar qU u w = 0 ∧
        LinearIndependent K ![u, w] ∧
        ∀ p, Z p = (eichler qU u w p.1, eichler qU u w p.2) := by
    rintro Z ⟨u, w, hu, hw, huw, hind, hZ⟩
    exact ⟨u, w, hu, hw, huw, hind, fun p => by rw [hZ, LemmaQ.orthTensor_one_apply']⟩
  rcases hX with hX | hX <;> rcases hY with hY | hY
  ·
    obtain ⟨N, hN0, hNN, hXN⟩ := hE hX
    obtain ⟨N', hN0', hNN', hYN⟩ := hE hY
    by_cases hM : N' * N = 0
    · exact Or.inl (LemmaQ.EE_left hsing hN0 hM X Y hXN hYN)
    · exact Or.inr (LemmaQ.EE_right hNN hNN' hM X Y hXN hYN)
  ·
    obtain ⟨N, hN0, hNN, hXN⟩ := hE hX
    obtain ⟨u, w, hu, hw, huw, hind, hYA⟩ := hA hY
    have hu0 : u ≠ 0 := by simpa using hind.ne_zero 0
    exact Or.inl (LemmaQ.EA_left hN0 hu0 hu (eichler qU u w)
      (CFSG.ClassicalGroups.Orthogonal.eichler_apply_self u w) X Y hXN hYA)
  ·
    obtain ⟨u, w, hu, hw, huw, hind, hXA⟩ := hA hX
    obtain ⟨N, hN0, hNN, hYN⟩ := hE hY
    have hu0 : u ≠ 0 := by simpa using hind.ne_zero 0
    obtain ⟨s, hs1, hs2⟩ := LemmaQ.exists_polar_eq hnd hind 0 1
    have hs : eichler qU u w s - s = u := by
      rw [LemmaQ.eichler_eq_add_eN hu hw huw, add_sub_cancel_left, LemmaQ.eN_apply, hs1, hs2]
      simp
    exact Or.inl (LemmaQ.AE_left hNN hN0 hu0 hu (eichler qU u w) hs X Y hXA hYN)
  ·
    obtain ⟨ux, wx, hux, hwx, huwx, hindx, hXA⟩ := hA hX
    obtain ⟨uy, wy, huy, hwy, huwy, hindy, hYA⟩ := hA hY
    by_cases hcase : ∀ α β : K, QuadraticMap.polar qU (α • ux + β • wx) uy = 0 →
        QuadraticMap.polar qU (α • ux + β • wx) wy = 0 → α = 0 ∧ β = 0
    · exact Or.inr (LemmaQ.AA_right hux hwx huwx huy hwy huwy hindy hcase X Y hXA hYA)
    · have hcase' : ∃ α β : K, (α ≠ 0 ∨ β ≠ 0) ∧
          QuadraticMap.polar qU (α • ux + β • wx) uy = 0 ∧
          QuadraticMap.polar qU (α • ux + β • wx) wy = 0 := by
        by_contra hcon
        apply hcase
        intro α β h1 h2
        by_contra hne
        apply hcon
        refine ⟨α, β, ?_, h1, h2⟩
        by_contra h
        push Not at h
        exact hne ⟨h.1, h.2⟩
      obtain ⟨α, β, hαβ, h1, h2⟩ := hcase'
      exact Or.inl (LemmaQ.AA_left hnd hux hwx huwx hindx huy hwy huwy hαβ h1 h2 X Y hXA hYA)

end LemmaQ

end CFSG.RankThree.GF2n.Smith81.Orth213
