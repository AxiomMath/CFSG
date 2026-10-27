module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Stab
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Sp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeCovers
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem r899_exists_swap_of_opRes_three {M L : Subgroup G} (hc3 : (conjSetOf M L).ncard = 3)
    (hOp : F10.OpRes 3 M = M) :
    ∃ τ ∈ M, ∃ K ∈ conjSetOf M L, K.map (MulAut.conj τ).toMonoidHom = K ∧
      ∃ K' ∈ conjSetOf M L, K'.map (MulAut.conj τ).toMonoidHom ≠ K' := by
  classical
  letI : MulAction (MulAut G) (Subgroup G) := Subgroup.pointwiseMulAction
  letI : MulAction ↥M (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp M.subtype)
  have hsmul : ∀ (g : ↥M) (N : Subgroup G),
      g • N = N.map (MulAut.conj (g : G)).toMonoidHom := by
    intro g N
    change (MulAut.conj (g : G)) • N = _
    rw [Subgroup.pointwise_smul_def]
    rfl
  have horbit : (MulAction.orbit ↥M L : Set (Subgroup G)) = conjSetOf M L := by
    ext N
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(g : G), g.2, (hsmul g L).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, (hsmul ⟨g, hg⟩ L).symm⟩
  by_contra hno
  set K : Subgroup ↥M := MulAction.stabilizer ↥M L with hKdef
  have hKmem : ∀ g : ↥M, g ∈ K ↔ (g : G) ∈ normalizer (L : Set G) := by
    intro g
    rw [hKdef, MulAction.mem_stabilizer_iff, hsmul,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    rfl
  have hfixall : ∀ g : ↥M, g ∈ K → ∀ N : Subgroup G, N ∈ conjSetOf M L → g • N = N := by
    intro g hg N hN
    by_contra hne
    have hgL : L.map (MulAut.conj (g : G)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp ((hKmem g).1 hg)
    have hLmem : L ∈ conjSetOf M L := by
      refine ⟨1, M.one_mem, ?_⟩
      ext x
      simp
    exact hno ⟨(g : G), g.2, L, hLmem, hgL, N, hN, by rwa [hsmul] at hne⟩
  have hKnormal : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hconj : (g * n * g⁻¹) • L = L := by
      calc
        (g * n * g⁻¹) • L = g • (n • (g⁻¹ • L)) := by rw [mul_smul, mul_smul]
        _ = g • (g⁻¹ • L) := by
          rw [hfixall n hn (g⁻¹ • L) (by
            rw [← horbit]
            exact ⟨g⁻¹, rfl⟩)]
        _ = L := by rw [← mul_smul, mul_inv_cancel, one_smul]
    exact (hKmem (g * n * g⁻¹)).2
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by rwa [hsmul] at hconj))
  have : K.Normal := hKnormal
  have hidx : K.index = 3 := by
    rw [hKdef, MulAction.index_stabilizer, horbit, hc3]
  have hQ : IsPGroup 3 (↥M ⧸ K) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [← Subgroup.index_eq_card, hidx]
    norm_num
  have hKtop : K = ⊤ :=
    UC6.eq_top_of_isPGroup_quotient_of_opRes_eq_uc6 Nat.prime_three hOp K hQ
  rw [hKtop, Subgroup.index_top] at hidx
  omega

theorem r899_exists_swap_pair {M L K₁ K₂ K₃ : Subgroup G} (hc3 : (conjSetOf M L).ncard = 3)
    (hswap : ∃ τ ∈ M, ∃ K ∈ conjSetOf M L, K.map (MulAut.conj τ).toMonoidHom = K ∧
      ∃ K' ∈ conjSetOf M L, K'.map (MulAut.conj τ).toMonoidHom ≠ K')
    (h₁ : K₁ ∈ conjSetOf M L) (h₂ : K₂ ∈ conjSetOf M L) (h₃ : K₃ ∈ conjSetOf M L)
    (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃) :
    ∃ τ ∈ M, K₁.map (MulAut.conj τ).toMonoidHom = K₂ ∧
      K₂.map (MulAut.conj τ).toMonoidHom = K₁ ∧ K₃.map (MulAut.conj τ).toMonoidHom = K₃ := by
  classical
  obtain ⟨τ, hτM, K, hKmem, hfixK, K', hK'mem, hmove⟩ := hswap
  have hS : ∀ N ∈ conjSetOf M L, N = K₁ ∨ N = K₂ ∨ N = K₃ := by
    have hsub : ({K₁, K₂, K₃} : Set (Subgroup G)) ⊆ conjSetOf M L := by
      intro N hN
      rcases hN with rfl | rfl | hN
      · exact h₁
      · exact h₂
      · rw [Set.mem_singleton_iff.1 hN]
        exact h₃
    have heq := Set.eq_of_subset_of_ncard_le hsub
      (by rw [hc3, Set.ncard_eq_three.2 ⟨K₁, K₂, K₃, h12, h13, h23, rfl⟩]) (Set.toFinite _)
    intro N hN
    rw [← heq] at hN
    exact hN
  have htr : ∀ {A B : Subgroup G}, A ∈ conjSetOf M L → B ∈ conjSetOf M L →
      ∃ g ∈ M, A.map (MulAut.conj g).toMonoidHom = B := by
    intro A B hA hB
    have hB' : B ∈ conjSetOf M A := by
      rw [uc22p2214_conjSetOf_eq hA]
      exact hB
    obtain ⟨g, hg, hgB⟩ := hB'
    exact ⟨g, hg, hgB.symm⟩
  obtain ⟨g, hgM, hgK⟩ := htr hKmem h₃
  set τ' : G := g * τ * g⁻¹ with hτ'def
  have hτ'M : τ' ∈ M := M.mul_mem (M.mul_mem hgM hτM) (M.inv_mem hgM)
  have hfix3 : K₃.map (MulAut.conj τ').toMonoidHom = K₃ := by
    rw [← hgK, hτ'def, uc22p22d_map_conj_map_conj,
      show (g * τ * g⁻¹) * g = g * τ by group,
      ← uc22p22d_map_conj_map_conj K τ g, hfixK]
  have hmove' : ∃ N ∈ conjSetOf M L, N.map (MulAut.conj τ').toMonoidHom ≠ N := by
    refine ⟨K'.map (MulAut.conj g).toMonoidHom,
      uc22r899_map_conj_mem hgM hK'mem, ?_⟩
    intro hEq
    have hcalc : (K'.map (MulAut.conj g).toMonoidHom).map (MulAut.conj τ').toMonoidHom =
        (K'.map (MulAut.conj τ).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [hτ'def, uc22p22d_map_conj_map_conj,
        show (g * τ * g⁻¹) * g = g * τ by group,
        ← uc22p22d_map_conj_map_conj K' τ g]
    exact hmove (Subgroup.map_injective (MulAut.conj g).injective (hcalc.symm.trans hEq))
  have h1 : K₁.map (MulAut.conj τ').toMonoidHom = K₂ := by
    have hmem := uc22r899_map_conj_mem hτ'M h₁
    rcases hS _ hmem with h | h | h
    · exfalso
      have h2mem := uc22r899_map_conj_mem hτ'M h₂
      have h2fix : K₂.map (MulAut.conj τ').toMonoidHom = K₂ := by
        rcases hS _ h2mem with h2 | h2 | h2
        · exact absurd (Subgroup.map_injective (MulAut.conj τ').injective
            (h2.trans h.symm)) h12.symm
        · exact h2
        · exact absurd (Subgroup.map_injective (MulAut.conj τ').injective
            (h2.trans hfix3.symm)) h23
      obtain ⟨N, hN, hNne⟩ := hmove'
      rcases hS N hN with rfl | rfl | rfl
      · exact hNne h
      · exact hNne h2fix
      · exact hNne hfix3
    · exact h
    · exact absurd (Subgroup.map_injective (MulAut.conj τ').injective (h.trans hfix3.symm)) h13
  have h2 : K₂.map (MulAut.conj τ').toMonoidHom = K₁ := by
    have hmem := uc22r899_map_conj_mem hτ'M h₂
    rcases hS _ hmem with h | h | h
    · exact h
    · exfalso
      have h1mem := uc22r899_map_conj_mem hτ'M h₁
      have h1fix : K₁.map (MulAut.conj τ').toMonoidHom = K₁ := by
        rcases hS _ h1mem with h1 | h1 | h1
        · exact h1
        · exact absurd (Subgroup.map_injective (MulAut.conj τ').injective (h1.trans h.symm)) h12
        · exact absurd (Subgroup.map_injective (MulAut.conj τ').injective
            (h1.trans hfix3.symm)) h13
      obtain ⟨N, hN, hNne⟩ := hmove'
      rcases hS N hN with rfl | rfl | rfl
      · exact hNne h1fix
      · exact hNne h
      · exact hNne hfix3
    · exact absurd (Subgroup.map_injective (MulAut.conj τ').injective (h.trans hfix3.symm)) h23
  exact ⟨τ', hτ'M, h1, h2, hfix3⟩

theorem r899_sp_three_of_isL2 {D : Data G} (h82 : F08.R82 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ} (hL2 : IsL2 (Bar2 L) n) :
    IsStronglyPEmbedded 3 D.M := by
  obtain ⟨K₁, K₂, K₃, h12, h13, h23, hS⟩ := Set.ncard_eq_three.1 hc3
  have hmem : ∀ K ∈ ({K₁, K₂, K₃} : Set (Subgroup G)), K ∈ calC D.M ∧ CFSG.Open.pRank 3 K = 1 := by
    intro K hK
    rw [← hS] at hK
    exact ⟨uc22p2214_calC_of_mem_conjSetOf hL hK,
      PartTwo.S17.pRank_three_eq_one_of_isL2 (uc22s21r899_isL2_of_mem hK hL2)⟩
  obtain ⟨c₁, e₁⟩ := hmem K₁ (by simp)
  obtain ⟨c₂, e₂⟩ := hmem K₂ (by simp)
  obtain ⟨c₃, e₃⟩ := hmem K₃ (by simp)
  exact PartTwo.s16h_stronglyEmbedded_three_of_three_pRank_one D h82 c₁ c₂ c₃ h12 h13 h23 e₁ e₂ e₃

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
