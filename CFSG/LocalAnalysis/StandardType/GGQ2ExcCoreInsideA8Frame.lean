module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideWit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormFrame

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

private lemma chainSigma_eq_sum_filter {τ : Tag} {m : ℕ} (β : Fin m → Fin τ.rank → ℤ)
    {a a' : ℕ} (ha : a ≤ a') (ha' : a' ≤ m) :
    chainσ β ⟨a, by omega⟩ ⟨a', by omega⟩ =
      ∑ s ∈ Finset.univ.filter (fun s : Fin m => a ≤ (s : ℕ) ∧ (s : ℕ) < a'), β s := by
  have hω : ∀ k : ℕ, chainω β k =
      ∑ s ∈ Finset.univ.filter (fun s : Fin m => (s : ℕ) < k), β s := by
    intro k
    simp only [chainω]
    rw [Finset.sum_filter]
  simp only [chainσ]
  rw [hω a', hω a]
  have hPQ : Finset.univ.filter (fun s : Fin m => (s : ℕ) < a) ⊆
      Finset.univ.filter (fun s : Fin m => (s : ℕ) < a') := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    omega
  have hdiff : (Finset.univ.filter (fun s : Fin m => (s : ℕ) < a')) \
      (Finset.univ.filter (fun s : Fin m => (s : ℕ) < a)) =
      Finset.univ.filter (fun s : Fin m => a ≤ (s : ℕ) ∧ (s : ℕ) < a') := by
    ext s
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [← Finset.sum_sdiff_eq_sub hPQ, hdiff]


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
  {T₀ : Subgroup (ModGL τ L)} {m : Fin 6}

@[expose] def a8Chain (d : ExcCoordDatum S T₀ m) {c : Finset (ExcRaw.Root m)}
    (w : ExcRaw.A8Witness m c) : Fin 8 → Fin τ.rank → ℤ :=
  fun a => d.γ (w.b a)

theorem iform_a8Chain (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (d : ExcCoordDatum S T₀ m)
    {c : Finset (ExcRaw.Root m)} (w : ExcRaw.A8Witness m c) (a a' : Fin 8) :
    iform (a8Chain d w a) (a8Chain d w a') = chainGram a a' := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  simp only [a8Chain]
  rw [iform_comm, ← corootPair_eq_iform_of_simplyLaced hτ' (d.isRoot (w.b a')),
    ← d.pairing_eq (w.b a) (w.b a')]
  exact w.gram a a'

theorem codeRoots_subset_frameRoots_a8Chain (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (d : ExcCoordDatum S T₀ m) {c : Finset (ExcRaw.Root m)} (w : ExcRaw.A8Witness m c) :
    codeRoots d.γ c ⊆ frameRoots (chainσ (a8Chain d w)) := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  intro δ hδ
  simp only [codeRoots, Set.mem_setOf_eq] at hδ
  simp only [frameRoots, Set.mem_setOf_eq]
  obtain ⟨i, hi, hδ⟩ := hδ
  obtain ⟨a, a', haa', ha'8, ε, hε, hspan⟩ := w.span i hi
  have ha9 : a < 8 + 1 := by omega
  have ha'9 : a' < 8 + 1 := by omega
  set A : Fin (8 + 1) := ⟨a, ha9⟩ with hA
  set A' : Fin (8 + 1) := ⟨a', ha'9⟩ with hA'
  have hAA : A ≠ A' := by
    intro h
    have hv := congrArg Fin.val h
    simp only [hA, hA', Fin.val_mk] at hv
    omega
  have hchain : chainσ (a8Chain d w) A A' =
      ∑ s ∈ Finset.univ.filter (fun s : Fin 8 => a ≤ (s : ℕ) ∧ (s : ℕ) < a'),
        a8Chain d w s := by
    have h := chainSigma_eq_sum_filter (β := a8Chain d w) (a := a) (a' := a') (by omega) (by omega)
    simpa only [hA, hA'] using h
  let T : Fin τ.rank → ℤ := chainσ (a8Chain d w) A A'
  have hT : T = ∑ s ∈ Finset.univ.filter (fun s : Fin 8 => a ≤ (s : ℕ) ∧ (s : ℕ) < a'),
      a8Chain d w s := hchain
  let v : Fin τ.rank → ℤ := d.γ i - ε • T
  have hiff : ∀ j, iform (d.γ j) v = 0 := by
    intro j
    have hdiag : iform (d.γ j) (d.γ i) = ExcRaw.pairing m i j := by
      rw [← corootPair_eq_iform_of_simplyLaced hτ' (d.isRoot j)]
      exact (d.pairing_eq i j).symm
    have hterm : ∀ s : Fin 8, iform (d.γ j) (a8Chain d w s) = ExcRaw.pairing m (w.b s) j := by
      intro s
      rw [a8Chain, ← corootPair_eq_iform_of_simplyLaced hτ' (d.isRoot j)]
      exact (d.pairing_eq (w.b s) j).symm
    have hsum : iform (d.γ j)
        (∑ s ∈ Finset.univ.filter (fun s : Fin 8 => a ≤ (s : ℕ) ∧ (s : ℕ) < a'),
          a8Chain d w s) =
        ∑ s ∈ Finset.univ.filter (fun s : Fin 8 => a ≤ (s : ℕ) ∧ (s : ℕ) < a'),
          ExcRaw.pairing m (w.b s) j := by
      rw [iform_finset_sum_right]
      exact Finset.sum_congr rfl fun s _ => hterm s
    change iform (d.γ j) (d.γ i - ε • T) = 0
    rw [hT, iform_sub_right, iform_smul_right, hdiag, hsum]
    exact sub_eq_zero.mpr (hspan j)
  have hsimple : ∀ k : Fin τ.rank, iform (Pi.single k 1) v = 0 := by
    intro k
    obtain ⟨j, hj | hj⟩ := d.exists_eq (Pi.single k 1) (isRoot_single τ k)
    · rw [hj]
      exact hiff j
    · rw [hj, iform_neg_left, hiff j, neg_zero]
  have hvv : iform v v = 0 := by
    nth_rw 1 [pi_eq_sum_univ' v]
    rw [iform_finset_sum_left]
    exact Finset.sum_eq_zero fun k _ => by rw [iform_smul_left, hsimple k, mul_zero]
  have hv0 : v = 0 :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.KacData.eq_zero_of_iform_self hvv
  have hv0' : d.γ i - ε • chainσ (a8Chain d w) A A' = 0 := hv0
  have hmain : d.γ i = ε • chainσ (a8Chain d w) A A' := sub_eq_zero.mp hv0'
  rcases hε with rfl | hε
  · rw [one_smul] at hmain
    rcases hδ with rfl | rfl
    · exact ⟨A, A', hAA, hmain⟩
    · refine ⟨A', A, hAA.symm, ?_⟩
      rw [hmain, chainσ_neg (a8Chain d w) A A']
  · rw [hε, neg_one_smul] at hmain
    rcases hδ with rfl | rfl
    · refine ⟨A', A, hAA.symm, ?_⟩
      rw [hmain, chainσ_neg (a8Chain d w) A A']
    · refine ⟨A, A', hAA, ?_⟩
      rw [hmain]
      exact neg_neg _


theorem exists_a8ChainHom (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (d : ExcCoordDatum S T₀ m)
    {c : Finset (ExcRaw.Root m)} (w : ExcRaw.A8Witness m c) :
    ∃ ψ : SL(8 + 1, L) →* ModGL τ L,
      ∀ a, ψ.comp (blockSL2 L 8 a) = rootSL2 τ L (a8Chain d w a) := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  have hβ : ∀ a, IsRoot τ (a8Chain d w a) := fun a => d.isRoot (w.b a)
  have hG : ∀ a a' : Fin 8, iform (a8Chain d w a) (a8Chain d w a') = chainGram a a' :=
    fun a a' => iform_a8Chain hτ d w a a'
  have hθ : ∀ (a : Fin 8) (h : (a : ℕ) + 1 < 8), ∃ θ : SL(3, L) →* ModGL τ L,
      θ.comp (blockSL L 3 2 0 (by omega)) = rootSL2 τ L (a8Chain d w a) ∧
        θ.comp (blockSL L 3 2 1 (by omega)) =
          rootSL2 τ L (a8Chain d w ⟨(a : ℕ) + 1, h⟩) := by
    intro a h
    have hne : a ≠ (⟨(a : ℕ) + 1, h⟩ : Fin 8) := by
      intro ha
      have hv := congrArg Fin.val ha
      change (a : ℕ) = (a : ℕ) + 1 at hv
      omega
    have h1 : iform (a8Chain d w a) (a8Chain d w ⟨(a : ℕ) + 1, h⟩) = -1 := by
      rw [hG, chainGram, if_neg hne]
      have hcond : ((a : ℕ) + 1 = ((⟨(a : ℕ) + 1, h⟩ : Fin 8) : ℕ) ∨
          (((⟨(a : ℕ) + 1, h⟩ : Fin 8) : ℕ) + 1 = (a : ℕ))) := Or.inl rfl
      rw [if_pos hcond]
    obtain ⟨θ, hθ1, hθ2⟩ :=
      exists_a2Hom_of_iform_eq_neg_one (L := L) hτ (hβ a) (hβ ⟨(a : ℕ) + 1, h⟩) h1
    exact ⟨θ, hθ1, hθ2⟩
  obtain ⟨ψ, hψ⟩ := exists_chainHom (L := L) hτ' (a8Chain d w) hβ hG hθ
  exact ⟨ψ, hψ⟩

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
