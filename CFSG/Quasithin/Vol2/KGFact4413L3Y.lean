module

public import CFSG.Quasithin.Vol2.KGFact4413L3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual

public section

namespace CFSG.Quasithin.H13.KG4413

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
open scoped MatrixGroups

theorem exists_mem_normalizer_of_isPSL3 {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : IsPSL 3 2 n Y) {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) (𝒜 : Set (MulAut Y))
    (h𝒜U : ∀ α ∈ 𝒜, U.map α.toMonoidHom = U)
    (h𝒜P : ∀ P : Subgroup Y, IsCoatom P → Subgroup.normalizer (U : Set Y) ≤ P →
      ∃ α ∈ 𝒜, P.map α.toMonoidHom ≠ P)
    {A : Subgroup Y} (hAN : A ≤ Subgroup.normalizer (U : Set Y)) (hAodd : Odd (Nat.card A))
    (h𝒜A : ∀ α ∈ 𝒜, ∀ a ∈ A, α a ∈ A ⊔ U) :
    ∃ x : Y, x ∉ Subgroup.normalizer (U : Set Y) ∧ x ∈ Subgroup.normalizer (A : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, _, ψ, -, hψU, hRes, -⟩ := even_rank_two_residual_linear hY hU
  obtain ⟨-, hUP, hmax, -⟩ := hRes
  have hNU : (Subgroup.normalizer (U : Set Y)).map ψ.toMonoidHom = projUpperTriangular 3 F := by
    rw [Subgroup.map_equiv_normalizer_eq, hψU, normalizer_projUnitriangular 2]
  have hmm : ∀ X : Subgroup Y, (X.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = X := by
    intro X
    ext x
    simp
  set P₀ := (projStabilizer (flagSpace 3 F ((0 : Fin 2) + 1))).map ψ.symm.toMonoidHom with hP₀
  have hP₀c : IsCoatom P₀ := by
    rw [← covBy_top_iff]
    exact (hmax P₀ (hUP 0)).mpr ⟨0, rfl⟩
  have hNP₀ : Subgroup.normalizer (U : Set Y) ≤ P₀ := by
    intro x hx
    have h1 : ψ x ∈ projUpperTriangular 3 F := hNU ▸ Subgroup.mem_map_of_mem _ hx
    have h2 := projUpperTriangular_le_projStabilizer_flag (F := F) ((0 : Fin 2) + 1) h1
    exact ⟨ψ x, h2, by simp⟩
  obtain ⟨α, hα𝒜, hαP⟩ := h𝒜P P₀ hP₀c hNP₀
  set α'' : MulAut (projectiveSL 3 F) := (ψ.symm.trans α).trans ψ with hα''
  have hα''U : (projUnitriangular 3 F).map α''.toMonoidHom = projUnitriangular 3 F := by
    rw [← hψU]
    ext y
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨α u, ?_, by simp [hα'']⟩
      rw [← h𝒜U α hα𝒜]
      exact ⟨u, hu, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      have hv' : v ∈ U.map α.toMonoidHom := (h𝒜U α hα𝒜).symm ▸ hv
      obtain ⟨u, hu, rfl⟩ := hv'
      exact ⟨ψ u, ⟨u, hu, rfl⟩, by simp [hα'']⟩
  have hα''s : α'' ∉ LinearFlag.semilinearAutGroup 3 F := by
    intro hs
    have h1 := CFSG.QuasithinUnique.Setup.X7Sec.semilinear_flag hs hα''U
      (d := (0 : Fin 2) + 1) (by norm_num)
    apply hαP
    rw [hP₀, Subgroup.map_map]
    conv_rhs => rw [← h1, Subgroup.map_map]
    refine congrArg (fun f => (projStabilizer (flagSpace 3 F ((0 : Fin 2) + 1))).map f) ?_
    ext x
    simp [hα'']
  set A'' := A.map ψ.toMonoidHom with hA''
  have hA''N : A'' ≤ projUpperTriangular 3 F := hNU ▸ Subgroup.map_mono hAN
  have hA''odd : Odd (Nat.card A'') := by
    rw [hA'', Subgroup.card_map_of_injective ψ.injective]
    exact hAodd
  have hα''A : ∀ a ∈ A'', α'' a ∈ A'' ⊔ projUnitriangular 3 F := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := h𝒜A α hα𝒜 a ha
    have h2 := Subgroup.mem_map_of_mem ψ.toMonoidHom h1
    rw [Subgroup.map_sup, hψU] at h2
    have h3 : α'' (ψ.toMonoidHom a) = ψ.toMonoidHom (α a) := by simp [hα'']
    rw [h3]
    exact h2
  obtain ⟨x'', hx''B, hx''N⟩ := exists_mem_normalizer_psl3 hα''U hα''s hA''N hA''odd hα''A
  refine ⟨ψ.symm x'', fun h => hx''B ?_, ?_⟩
  · rw [← hNU]
    exact ⟨ψ.symm x'', h, by simp⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx''N ⊢
    have h1 := congrArg (Subgroup.map ψ.symm.toMonoidHom) hx''N
    rw [hA'', hmm] at h1
    conv_rhs => rw [← h1]
    rw [Subgroup.map_map, Subgroup.map_map]
    refine congrArg (fun f => A.map f) ?_
    ext y
    simp

end CFSG.Quasithin.H13.KG4413
