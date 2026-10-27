module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadLine
import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LinearGroups (stdHermForm)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f ε : ℕ}
  {b : StatedSU (2 * 2 + ε) (2 ^ f) K} {ω : K}

private theorem inf_eig_eq_bot_or_eq (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    (hK₀ : F08.KOf8103 ⊤ (zpowers b) ≠ ⊥)
    {U : Submodule K (Fin (2 * 2 + ε) → K)}
    (hKU : ∀ k ∈ F08.KOf8103 ⊤ (zpowers b), ∀ u ∈ U,
      ((k : GL (Fin (2 * 2 + ε)) K) :
        Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ u ∈ U)
    (hiso : CFSG.AGLEmbedding.IsTotallyIsotropicSU (2 ^ f) U) :
    eigSU b 1 ⊓ U = ⊥ ∧
      (eigSU b ω ⊓ U = ⊥ ∨ eigSU b ω ⊓ U = eigSU b ω) ∧
      (eigSU b ω⁻¹ ⊓ U = ⊥ ∨ eigSU b ω⁻¹ ⊓ U = eigSU b ω⁻¹) := by
  have hiso' := (CFSG.AGLEmbedding.ToralCensus.isTotallyIsotropicSU_iff h U).mp hiso
  have hVbot : eigSU b 1 ⊓ U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    exact hS.eq_zero_of_isotropic_one h hv.1 (hiso' v hv.2 v hv.2)
  have hWdisj : eigSU b ω ⊓ U = ⊥ ∨ eigSU b ω ⊓ U = eigSU b ω := by
    have hUinv : ∀ k ∈ F08.KOf8103 ⊤ (zpowers b), ∀ v ∈ eigSU b ω ⊓ U,
        ((k : GL (Fin (2 * 2 + ε)) K) :
          Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v ∈ eigSU b ω ⊓ U := by
      intro k hk v hv
      rw [Submodule.mem_inf] at hv ⊢
      exact ⟨(mem_stabSU.mp (kOf_le_stabSU_eigSU b ω hk)) v hv.1, hKU k hk v hv.2⟩
    have hnot1 : Module.finrank K ↥(eigSU b ω ⊓ U) ≠ 1 := by
      intro h1
      obtain ⟨k, hk, v, hv, hkv⟩ :=
        hS.kOf_moves_line h hK₀ (inf_le_left : eigSU b ω ⊓ U ≤ eigSU b ω) h1
      exact hkv (hUinv k hk v hv)
    have hle : Module.finrank K ↥(eigSU b ω ⊓ U) ≤ 2 :=
      (Submodule.finrank_mono inf_le_left).trans (le_of_eq hS.finrank_eig)
    rcases Nat.lt_or_ge (Module.finrank K ↥(eigSU b ω ⊓ U)) 1 with h0 | h1
    · exact Or.inl (Submodule.finrank_eq_zero.mp (by omega))
    · refine Or.inr (Submodule.eq_of_le_of_finrank_eq inf_le_left ?_)
      exact (show Module.finrank K ↥(eigSU b ω ⊓ U) = 2 by omega).trans
        hS.finrank_eig.symm
  have hW'disj : eigSU b ω⁻¹ ⊓ U = ⊥ ∨ eigSU b ω⁻¹ ⊓ U = eigSU b ω⁻¹ := by
    have hUinv : ∀ k ∈ F08.KOf8103 ⊤ (zpowers b), ∀ v ∈ eigSU b ω⁻¹ ⊓ U,
        ((k : GL (Fin (2 * 2 + ε)) K) :
          Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v ∈ eigSU b ω⁻¹ ⊓ U := by
      intro k hk v hv
      rw [Submodule.mem_inf] at hv ⊢
      exact ⟨(mem_stabSU.mp (kOf_le_stabSU_eigSU b ω⁻¹ hk)) v hv.1, hKU k hk v hv.2⟩
    have hnot1 : Module.finrank K ↥(eigSU b ω⁻¹ ⊓ U) ≠ 1 := by
      intro h1
      obtain ⟨k, hk, v, hv, hkv⟩ :=
        hS.symm.kOf_moves_line h hK₀
          (inf_le_left : eigSU b ω⁻¹ ⊓ U ≤ eigSU b ω⁻¹) h1
      exact hkv (hUinv k hk v hv)
    have hle : Module.finrank K ↥(eigSU b ω⁻¹ ⊓ U) ≤ 2 :=
      (Submodule.finrank_mono inf_le_left).trans (le_of_eq hS.finrank_eig_inv)
    rcases Nat.lt_or_ge (Module.finrank K ↥(eigSU b ω⁻¹ ⊓ U)) 1 with h0 | h1
    · exact Or.inl (Submodule.finrank_eq_zero.mp (by omega))
    · refine Or.inr (Submodule.eq_of_le_of_finrank_eq inf_le_left ?_)
      exact (show Module.finrank K ↥(eigSU b ω⁻¹ ⊓ U) = 2 by omega).trans
        hS.finrank_eig_inv.symm
  exact ⟨hVbot, hWdisj, hW'disj⟩

omit [Finite K] in
private theorem eq_eig_of_inf (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    {U : Submodule K (Fin (2 * 2 + ε) → K)}
    (hbU : ∀ u ∈ U, ((b : GL (Fin (2 * 2 + ε)) K) :
      Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ u ∈ U)
    (hiso : CFSG.AGLEmbedding.IsTotallyIsotropicSU (2 ^ f) U)
    (hV : eigSU b 1 ⊓ U = ⊥)
    (hW : eigSU b ω ⊓ U = ⊥ ∨ eigSU b ω ⊓ U = eigSU b ω)
    (hW' : eigSU b ω⁻¹ ⊓ U = ⊥ ∨ eigSU b ω⁻¹ ⊓ U = eigSU b ω⁻¹)
    (hpos : 0 < Module.finrank K U) :
    U = eigSU b ω ∨ U = eigSU b ω⁻¹ := by
  have hiso' := (CFSG.AGLEmbedding.ToralCensus.isTotallyIsotropicSU_iff h U).mp hiso
  have hnotboth : ¬ (eigSU b ω ≤ U ∧ eigSU b ω⁻¹ ≤ U) := by
    rintro ⟨hWU, hW'U⟩
    have hW'ne : eigSU b ω⁻¹ ≠ ⊥ := by
      intro hbot
      have h2 := hS.finrank_eig_inv
      rw [hbot, finrank_bot] at h2
      omega
    obtain ⟨w', hw', hw'ne⟩ := (Submodule.ne_bot_iff (eigSU b ω⁻¹)).mp hW'ne
    exact hw'ne (hS.eq_zero_of_orth h hw' fun w hw => hiso' w (hWU hw) w' (hW'U hw'))
  have hnotbot : ¬ (eigSU b ω ⊓ U = ⊥ ∧ eigSU b ω⁻¹ ⊓ U = ⊥) := by
    rintro ⟨h1, h2⟩
    have hUbot : U = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      obtain ⟨v₁, hv₁, w, hw, w', hw', rfl⟩ := hS.decomp hbU v hv
      rw [(Submodule.eq_bot_iff (eigSU b 1 ⊓ U)).mp hV v₁ hv₁,
        (Submodule.eq_bot_iff (eigSU b ω ⊓ U)).mp h1 w hw,
        (Submodule.eq_bot_iff (eigSU b ω⁻¹ ⊓ U)).mp h2 w' hw']
      simp
    have h0 : Module.finrank K U = 0 := by rw [hUbot, finrank_bot]
    omega
  rcases hW with hWbot | hWtop
  · have hW'top : eigSU b ω⁻¹ ⊓ U = eigSU b ω⁻¹ := by
      rcases hW' with h'bot | h'top
      · exact absurd ⟨hWbot, h'bot⟩ hnotbot
      · exact h'top
    right
    refine le_antisymm ?_ ((le_of_eq hW'top.symm).trans inf_le_right)
    intro v hv
    obtain ⟨v₁, hv₁, w, hw, w', hw', rfl⟩ := hS.decomp hbU v hv
    have hv₁0 : v₁ = 0 := (Submodule.eq_bot_iff (eigSU b 1 ⊓ U)).mp hV v₁ hv₁
    have hw0 : w = 0 := (Submodule.eq_bot_iff (eigSU b ω ⊓ U)).mp hWbot w hw
    have hw'mem : w' ∈ eigSU b ω⁻¹ := (Submodule.mem_inf.mp hw').1
    simpa [hv₁0, hw0] using hw'mem
  · have hW'bot : eigSU b ω⁻¹ ⊓ U = ⊥ := by
      rcases hW' with h'bot | h'top
      · exact h'bot
      · exact absurd ⟨(le_of_eq hWtop.symm).trans inf_le_right,
          (le_of_eq h'top.symm).trans inf_le_right⟩ hnotboth
    left
    refine le_antisymm ?_ ((le_of_eq hWtop.symm).trans inf_le_right)
    intro v hv
    obtain ⟨v₁, hv₁, w, hw, w', hw', rfl⟩ := hS.decomp hbU v hv
    have hv₁0 : v₁ = 0 := (Submodule.eq_bot_iff (eigSU b 1 ⊓ U)).mp hV v₁ hv₁
    have hw'0 : w' = 0 := (Submodule.eq_bot_iff (eigSU b ω⁻¹ ⊓ U)).mp hW'bot w' hw'
    have hwmem : w ∈ eigSU b ω := (Submodule.mem_inf.mp hw).1
    simpa [hv₁0, hw'0] using hwmem

omit [Finite K] [CharP K 2] in
private theorem eq_two_of_mem (hS : RadSetup ε b ω) {I : Set ℕ}
    {U : ℕ → Submodule K (Fin (2 * 2 + ε) → K)}
    (hUfr : ∀ i ∈ I, Module.finrank K (U i) = i)
    (hstep : ∀ i ∈ I, U i = eigSU b ω ∨ U i = eigSU b ω⁻¹)
    {i : ℕ} (hi : i ∈ I) : i = 2 := by
  rcases hstep i hi with hWi | hWi
  · have h := hUfr i hi
    rw [hWi, hS.finrank_eig] at h
    omega
  · have h := hUfr i hi
    rw [hWi, hS.finrank_eig_inv] at h
    omega

theorem RadSetup.eq_or_eq_of_le (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    (hK₀ : F08.KOf8103 ⊤ (zpowers b) ≠ ⊥) {Z : Subgroup (StatedSU (2 * 2 + ε) (2 ^ f) K)}
    (hZ : Z ≠ ⊤)
    (hN : ∃ T₀ : Sylow 2 (StatedSU (2 * 2 + ε) (2 ^ f) K),
      normalizer ((T₀ : Subgroup (StatedSU (2 * 2 + ε) (2 ^ f) K)) :
        Set (StatedSU (2 * 2 + ε) (2 ^ f) K)) ≤ Z)
    (hKZ : F08.KOf8103 ⊤ (zpowers b) ⊔ zpowers b ≤ Z) :
    Z = stabSU (2 ^ f) (eigSU b ω) ∨ Z = stabSU (2 ^ f) (eigSU b ω⁻¹) := by
  have hcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨S₀, hS₀⟩ := hN
  obtain ⟨I, -, hIne, hIsub, -, -, U, hUchain, -, hUmem⟩ :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.exists_chain_iso (K := K) (r := 2) (ε := ε)
      (f := f) (by norm_num) hS.le_one hcard h.one_le Z S₀ hS₀ hZ
  have hUfr : ∀ i ∈ I, Module.finrank K (U i) = i := fun i hi => (hUchain i hi).1
  have hUiso : ∀ i ∈ I, CFSG.AGLEmbedding.IsTotallyIsotropicSU (2 ^ f) (U i) :=
    fun i hi => (hUchain i hi).2
  have hbZ : b ∈ Z := hKZ (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hK₀Z : F08.KOf8103 ⊤ (zpowers b) ≤ Z := le_sup_left.trans hKZ
  have hstep : ∀ i ∈ I, U i = eigSU b ω ∨ U i = eigSU b ω⁻¹ := by
    intro i hi
    have hKU : ∀ k ∈ F08.KOf8103 ⊤ (zpowers b), ∀ u ∈ U i,
        ((k : GL (Fin (2 * 2 + ε)) K) :
          Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ u ∈ U i :=
      fun k hk u hu => (hUmem k).mp (hK₀Z hk) i hi u hu
    obtain ⟨hV, hW, hW'⟩ := inf_eig_eq_bot_or_eq hS h hK₀ hKU (hUiso i hi)
    refine eq_eig_of_inf hS h ((hUmem b).mp hbZ i hi) (hUiso i hi) hV hW hW' ?_
    rw [hUfr i hi]
    exact (Set.mem_Icc.mp (hIsub hi)).1
  have h2mem : 2 ∈ I := by
    obtain ⟨i₀, hi₀⟩ := hIne
    rw [eq_two_of_mem hS hUfr hstep hi₀] at hi₀
    exact hi₀
  have hIeq : I = {2} := by
    ext i
    constructor
    · intro hi
      exact Set.mem_singleton_iff.mpr (eq_two_of_mem hS hUfr hstep hi)
    · intro hi
      rw [Set.mem_singleton_iff] at hi
      rw [hi]
      exact h2mem
  have hZstab : Z = stabSU (2 ^ f) (U 2) := by
    ext y
    rw [hUmem y, mem_stabSU]
    constructor
    · intro hy w hw
      exact hy 2 h2mem w hw
    · intro hy i hi w hw
      have hi2 : i = 2 := Set.mem_singleton_iff.mp (hIeq ▸ hi)
      subst i
      exact hy w hw
  rcases hstep 2 h2mem with hW2 | hW2
  · exact Or.inl (by rw [hZstab, hW2])
  · exact Or.inr (by rw [hZstab, hW2])

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
