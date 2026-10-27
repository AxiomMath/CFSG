module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsPairs
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LieType.Chevalley.WeylRoots

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Chevalley

private theorem jtag_share {k : ℕ} {γ δ : Fin k → ℤ} (h : ggDDot γ δ ≠ 0) :
    ∃ y, γ y ≠ 0 ∧ δ y ≠ 0 := by
  by_contra hno
  refine h (Finset.sum_eq_zero fun y _ => ?_)
  by_cases hy : γ y = 0
  · rw [hy, zero_mul]
  · rw [show δ y = 0 from by_contra fun hδ => hno ⟨y, hy, hδ⟩, mul_zero]

private theorem jtag_orth_disj {k : ℕ} {Φ : Set (Fin k → ℤ)} (hΦ : GGDSubsys k Φ)
    (hss : ∀ a b : Fin k, a ≠ b →
      ¬ (Pi.single a 1 + Pi.single b 1 ∈ Φ ∧ Pi.single a 1 - Pi.single b 1 ∈ Φ))
    {γ δ : Fin k → ℤ} (hγ : γ ∈ Φ) (hδ : δ ∈ Φ) (h0 : ggDDot γ δ = 0) (x : Fin k) :
    γ x = 0 ∨ δ x = 0 := by
  rcases ggDRootSet_orth (hΦ.1 hγ) (hΦ.1 hδ) h0 with ⟨a, b, s, hab, hs, hγ', hδ'⟩ |
    ⟨a, b, c, d, s, s', u, u', -, -, hac, had, hbc, hbd, -, -, -, -, rfl, rfl⟩
  · exfalso
    have h1 : Pi.single a 1 + Pi.single b s ∈ Φ := by
      rcases hγ' with rfl | rfl
      · exact hγ
      · simpa using hΦ.neg_mem hγ
    have h2 : Pi.single a 1 - Pi.single b s ∈ Φ := by
      rcases hδ' with rfl | rfl
      · exact hδ
      · simpa using hΦ.neg_mem hδ
    rcases hs with rfl | rfl
    · exact hss a b hab ⟨h1, h2⟩
    · rw [Pi.single_neg, ← sub_eq_add_neg] at h1
      rw [Pi.single_neg, sub_neg_eq_add] at h2
      exact hss a b hab ⟨h2, h1⟩
  · by_cases hxa : x = a
    · exact Or.inr (hxa ▸ ggDPair_apply_of_ne hac had u u')
    by_cases hxb : x = b
    · exact Or.inr (hxb ▸ ggDPair_apply_of_ne hbc hbd u u')
    exact Or.inl (ggDPair_apply_of_ne hxa hxb s s')

private theorem jtag_no_branch {k ℓ : ℕ} {Φ : Set (Fin k → ℤ)} (hΦ : GGDSubsys k Φ)
    (hss : ∀ a b : Fin k, a ≠ b →
      ¬ (Pi.single a 1 + Pi.single b 1 ∈ Φ ∧ Pi.single a 1 - Pi.single b 1 ∈ Φ))
    {N : CoxeterMatrix (Fin ℓ)} (η : Fin ℓ → Fin k → ℤ) (hηΦ : ∀ i, η i ∈ Φ)
    (hdot2 : ∀ i j, i ≠ j → N.M i j = 2 → ggDDot (η i) (η j) = 0)
    (hdot3 : ∀ i j, N.M i j = 3 → ggDDot (η i) (η j) ≠ 0) {u v₁ v₂ v₃ : Fin ℓ}
    (h : N.M u v₁ = 3 ∧ N.M u v₂ = 3 ∧ N.M u v₃ = 3 ∧ N.M v₁ v₂ = 2 ∧ N.M v₁ v₃ = 2 ∧
      N.M v₂ v₃ = 2) : False := by
  obtain ⟨h1, h2, h3, h12, h13, h23⟩ := h
  have hd : ∀ {i j : Fin ℓ} {y : Fin k}, N.M i j = 2 → η i y ≠ 0 → η j y = 0 :=
    fun {i j y} h hy => by
      have hij : i ≠ j := fun he => by
        rw [he, N.diagonal] at h
        exact absurd h (by decide)
      exact (jtag_orth_disj hΦ hss (hηΦ _) (hηΦ _) (hdot2 _ _ hij h) y).resolve_left hy
  obtain ⟨y₁, hu₁, h₁⟩ := jtag_share (hdot3 u v₁ h1)
  obtain ⟨y₂, hu₂, h₂⟩ := jtag_share (hdot3 u v₂ h2)
  obtain ⟨y₃, hu₃, h₃⟩ := jtag_share (hdot3 u v₃ h3)
  have d12 : y₁ ≠ y₂ := fun h => h₂ (h ▸ hd h12 h₁)
  have d13 : y₃ ≠ y₁ := fun h => h₃ (h ▸ hd h13 h₁)
  have d23 : y₃ ≠ y₂ := fun h => h₃ (h ▸ hd h23 h₂)
  exact hu₃ (ggDRootSet_eq_zero (hΦ.1 (hηΦ _)) d12 hu₁ hu₂ d13 d23)

theorem ggDk_tag_eq_psl_of_roots
    {k : ℕ} {Φ : Set (Fin k → ℤ)} (hΦ : GGDSubsys k Φ)
    (hss : ∀ a b : Fin k, a ≠ b →
      ¬ (Pi.single a 1 + Pi.single b 1 ∈ Φ ∧ Pi.single a 1 - Pi.single b 1 ∈ Φ))
    {t : StatedLieTag} {n f : ℕ} (htag : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (η : Fin (ggU t n f).D.rank → Fin k → ℤ)
    (hηΦ : ∀ i, η i ∈ Φ)
    (hdot2 : ∀ i j, i ≠ j → (coxeterMatrix (ggU t n f).D.isFiniteType).M i j = 2 →
      ggDDot (η i) (η j) = 0)
    (hdot3 : ∀ i j, (coxeterMatrix (ggU t n f).D.isFiniteType).M i j = 3 →
      ggDDot (η i) (η j) ≠ 0) :
    t = .PSL := by
  rcases htag with rfl | rfl | rfl | rfl | rfl
  · rfl
  ·
    exfalso
    have hn4 : 4 ≤ n := hadm.2.2
    have hn3 : 3 ≤ n := by omega
    have hU : ggU .POmegaPlus n f = ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
        Spin.plusDatum n (GaloisField 2 f) hn3⟩ := by
      simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
    revert η hηΦ hdot2 hdot3
    rw [hU]
    intro η hηΦ hdot2 hdot3
    have hM : coxeterMatrix (Spin.isFiniteType_cartanD n) = ggCoxeterMatrixD n :=
      coxeterMatrix_eq_of_ggIntCartan _ (by rw [Spin.cartanD_eq n]; exact ggIntCartan_D n)
    have h2 : ∀ i j : Fin n, i ≠ j → (coxeterMatrix (Spin.isFiniteType_cartanD n)).M i j = 2 →
        ggDDot (η i) (η j) = 0 := hdot2
    have h3 : ∀ i j : Fin n, (coxeterMatrix (Spin.isFiniteType_cartanD n)).M i j = 3 →
        ggDDot (η i) (η j) ≠ 0 := hdot3
    rw [hM] at h2 h3
    refine jtag_no_branch hΦ hss (N := ggCoxeterMatrixD n) η hηΦ h2 h3 (u := ⟨n - 3, by omega⟩)
      (v₁ := ⟨n - 4, by omega⟩) (v₂ := ⟨n - 2, by omega⟩) (v₃ := ⟨n - 1, by omega⟩) ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [ggCoxeterMatrixD_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> first | omega | contradiction
  ·
    have hM : coxeterMatrix (ggU .E6 n f).D.isFiniteType = CoxeterMatrix.E₆ :=
      coxeterMatrix_eq_of_ggIntCartan _ (by
        rw [show (ggU .E6 n f).D.cartan = CartanMatrix.E 6 from cartanE_eq 6]
        exact ggIntCartan_E₆)
    rw [hM] at hdot2 hdot3
    exact (jtag_no_branch hΦ hss (N := CoxeterMatrix.E₆) η hηΦ hdot2 hdot3 (u := 3) (v₁ := 1)
      (v₂ := 2) (v₃ := 4) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩).elim
  ·
    have hM : coxeterMatrix (ggU .E7 n f).D.isFiniteType = CoxeterMatrix.E₇ :=
      coxeterMatrix_eq_of_ggIntCartan _ (by
        rw [show (ggU .E7 n f).D.cartan = CartanMatrix.E 7 from cartanE_eq 7]
        exact ggIntCartan_E₇)
    rw [hM] at hdot2 hdot3
    exact (jtag_no_branch hΦ hss (N := CoxeterMatrix.E₇) η hηΦ hdot2 hdot3 (u := 3) (v₁ := 1)
      (v₂ := 2) (v₃ := 4) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩).elim
  ·
    have hM : coxeterMatrix (ggU .E8 n f).D.isFiniteType = CoxeterMatrix.E₈ :=
      coxeterMatrix_eq_of_ggIntCartan _ (by
        rw [show (ggU .E8 n f).D.cartan = CartanMatrix.E 8 from cartanE_eq 8]
        exact ggIntCartan_E₈)
    rw [hM] at hdot2 hdot3
    exact (jtag_no_branch hΦ hss (N := CoxeterMatrix.E₈) η hηΦ hdot2 hdot3 (u := 3) (v₁ := 1)
      (v₂ := 2) (v₃ := 4) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩).elim

end CFSG.StandardType

end
