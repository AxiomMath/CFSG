module

public import CFSG.Quasithin.EmptyFaithful.S1421QA12Lin
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bB

public section

namespace CFSG.Quasithin

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L

namespace QA12

section Model

variable {K : Type} [Field K] {X : Type} [Group X]

structure SpData (π : StatedSp 2 K →* X) : Prop where
  inj : Function.Injective π
  coatoms : ∀ A : Subgroup X, (unipotent 2 K).map π ≤ A →
    (A ⋖ (⊤ : Subgroup X) ↔ ∃ j : Fin 2, A = (Q2 K j).map π)
  normalizer_le : Subgroup.normalizer (((unipotent 2 K).map π : Subgroup X) : Set X) ≤
    (borelSubgroup 2 K).map π

theorem SpData.exists_eq_Q {π : StatedSp 2 K →* X} (h : SpData π) {P P' : Subgroup X}
    (hPar : IsTwoParabolicsOver ((unipotent 2 K).map π) P P') :
    ∃ j j' : Fin 2, j ≠ j' ∧ P = (Q2 K j).map π ∧ P' = (Q2 K j').map π := by
  have hP : P ⋖ (⊤ : Subgroup X) := (hPar.2.2.2.2 P hPar.2.1).mpr (Or.inl rfl)
  have hP' : P' ⋖ (⊤ : Subgroup X) := (hPar.2.2.2.2 P' hPar.2.2.1).mpr (Or.inr rfl)
  obtain ⟨j, hj⟩ := (h.coatoms P hPar.2.1).mp hP
  obtain ⟨j', hj'⟩ := (h.coatoms P' hPar.2.2.1).mp hP'
  exact ⟨j, j', fun hjj => hPar.1 (by rw [hj, hj', hjj]), hj, hj'⟩

theorem spMat_spLevi_zero_diag (u : Kˣ) :
    spMat (spLevi 0 (F146Field.Case2b.diagSL u)) (Sum.inl 0) (Sum.inl 0) = 1 ∧
      spMat (spLevi 0 (F146Field.Case2b.diagSL u)) (Sum.inl 1) (Sum.inl 1) = (u : K) ∧
      spMat (spLevi 0 (F146Field.Case2b.diagSL u)) (Sum.inl 0) (Sum.inl 1) = 0 ∧
      spMat (spLevi 0 (F146Field.Case2b.diagSL u)) (Sum.inl 1) (Sum.inl 0) = 0 := by
  rw [spMat_lam]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [pairMat, F146Field.Case2b.diagSL, Matrix.one_apply]

section Finite

variable [Finite K]

theorem det_block_sp_one {m : StatedSp 2 K} (hm : m ∈ perfectCore (Q2 K 1)) :
    spMat m (Sum.inl 0) (Sum.inl 0) * spMat m (Sum.inl 1) (Sum.inl 1) -
      spMat m (Sum.inl 0) (Sum.inl 1) * spMat m (Sum.inl 1) (Sum.inl 0) = 1 := by
  have h := (blkN 1 ⟨m, hm⟩).2
  rw [blkN_coe, Matrix.det_fin_two] at h
  simpa [blkIdx, sigma2] using h

variable [Finite X]

theorem sp_false_01 {π : StatedSp 2 K →* X} (h : SpData π) (hK : 4 ≤ Nat.card K)
    (heq : Subgroup.normalizer (((unipotent 2 K).map π : Subgroup X) : Set X) ⊓
        perfectCore ((Q2 K 0).map π) =
      Subgroup.normalizer (((unipotent 2 K).map π : Subgroup X) : Set X) ⊓
        perfectCore ((Q2 K 1).map π)) : False := by
  obtain ⟨u, hu⟩ := exists_unit_ne_one hK
  have hK4 := exists_finset_card_four hK
  have ht0 : spLevi 0 (F146Field.Case2b.diagSL u) ∈ perfectCore (Q2 K 0) :=
    spLevi_mem_perfectCore hK4 0 _
  have h1 : π (spLevi 0 (F146Field.Case2b.diagSL u)) ∈ perfectCore ((Q2 K 0).map π) := by
    rw [← map_perfectCore π (Q2 K 0)]
    exact Subgroup.mem_map_of_mem π ht0
  have hnorm : π (spLevi 0 (F146Field.Case2b.diagSL u)) ∈
      Subgroup.normalizer (((unipotent 2 K).map π : Subgroup X) : Set X) := by
    refine Subgroup.le_normalizer_map π ⟨spLevi 0 (F146Field.Case2b.diagSL u), ?_, rfl⟩
    rw [normalizer_unipotent]
    rw [← F146Field.Case2b.torusHom_eq_spLevi_zero]
    exact torus_le_borelSubgroup ⟨_, rfl⟩
  have h2 : π (spLevi 0 (F146Field.Case2b.diagSL u)) ∈ perfectCore ((Q2 K 1).map π) := by
    have hm : π (spLevi 0 (F146Field.Case2b.diagSL u)) ∈ Subgroup.normalizer
        (((unipotent 2 K).map π : Subgroup X) : Set X) ⊓ perfectCore ((Q2 K 0).map π) :=
      ⟨hnorm, h1⟩
    rw [heq] at hm
    exact hm.2
  rw [← map_perfectCore π (Q2 K 1)] at h2
  obtain ⟨m, hm, hmπ⟩ := Subgroup.mem_map.mp h2
  have hmt : m = spLevi 0 (F146Field.Case2b.diagSL u) := h.inj hmπ
  rw [hmt] at hm
  have hdet := det_block_sp_one hm
  obtain ⟨e00, e11, e01, e10⟩ := spMat_spLevi_zero_diag u
  rw [e00, e11, e01, e10] at hdet
  apply hu
  exact Units.ext (by simpa using hdet)

end Finite

end Model

section Assemble

variable {X : Type} [Group X] [Finite X]

theorem false_of_isPSp4 {n : ℕ} (hn : 2 ≤ n) (hX : IsPSp4 2 n X) {U P P' : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hPar : IsTwoParabolicsOver U P P')
    (heq : Subgroup.normalizer (U : Set X) ⊓ perfectCore P =
      Subgroup.normalizer (U : Set X) ⊓ perfectCore P') : False := by
  obtain ⟨K, hF, hFin, hCh, φ, hcard, hφU, hres, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_symplectic hX hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set π : StatedSp 2 K →* X := φ.symm.toMonoidHom.comp (proj 2 K) with hπ
  have hπU : (unipotent 2 K).map π = (projUnipotent 2 K).map φ.symm.toMonoidHom := by
    rw [hπ, ← Subgroup.map_map]
    rfl
  have hVπ : (unipotent 2 K).map π = U := by
    rw [hπU, ← hφU]
    exact map_equiv_symm_map φ U
  have hQ : ∀ j : Fin 2, (Q2 K j).map π =
      (projStabilizer 2 K (flag 2 K ((j : ℕ) + 1))).map φ.symm.toMonoidHom := fun j => by
    rw [hπ, ← Subgroup.map_map]
    rfl
  have hinj : Function.Injective π := φ.symm.injective.comp proj_injective_charTwo
  have hN : Subgroup.normalizer (((unipotent 2 K).map π : Subgroup X) : Set X) ≤
      (borelSubgroup 2 K).map π := by
    rw [hπU, normalizer_map_equiv φ.symm, normalizer_projUnipotent 2 (by norm_num)]
    rw [hπ, projBorel, ← Subgroup.map_map]
  have hD : SpData π :=
    ⟨hinj, fun A hA => by
      have hA' : U ≤ A := hVπ ▸ hA
      rw [hres.2.2.1 A hA']
      simp only [hQ], hN⟩
  subst hVπ
  obtain ⟨j, j', hjj, rfl, rfl⟩ := hD.exists_eq_Q hPar
  fin_cases j <;> fin_cases j'
  · exact absurd rfl hjj
  · exact sp_false_01 hD hK4 heq
  · exact sp_false_01 hD hK4 heq.symm
  · exact absurd rfl hjj

end Assemble

end QA12

end CFSG.Quasithin
