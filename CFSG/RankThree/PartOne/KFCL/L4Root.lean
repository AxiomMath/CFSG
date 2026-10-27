module

public import CFSG.RankThree.PartOne.KFCL.L4Derived
public import CFSG.RankThree.PartOne.KFCL.Core
public import CFSG.RankThree.PartOne.KFCL.L4Weyl

public section

namespace CFSG.RankThree.PartOne.KFCL.L4

open Matrix CFSG.RankThree.PartOne.KFCL.BlockSL
open scoped MatrixGroups

theorem exists_perm_pair {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm α, σ a = c ∧ σ b = d := by
  have hbc : Equiv.swap a c b ≠ c := by
    intro h
    have : Equiv.swap a c b = Equiv.swap a c a := by rw [h, Equiv.swap_apply_left]
    exact hab (Equiv.injective _ this).symm
  refine ⟨Equiv.swap (Equiv.swap a c b) d * Equiv.swap a c, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hbc.symm hcd
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem exists_perm_map_eq {s s' : Finset (Fin 4)} (hs : s.card = 2) (hs' : s'.card = 2) :
    ∃ σ : Equiv.Perm (Fin 4), s.map σ.toEmbedding = s' := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hs
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.1 hs'
  obtain ⟨σ, h1, h2⟩ := exists_perm_pair hab hcd
  exact ⟨σ, by simp [Finset.map_insert, h1, h2]⟩

variable {K : Type} [Field K] [CharP K 2] {p : ℕ}

@[expose] noncomputable def stdRoot (p : ℕ) (K : Type) [Field K] [CharP K 2] (h4 : 4 ≤ Nat.card K) {ζ : K}
    (hζp : ζ ^ p = 1) (hζ0 : ζ ≠ 0) (hζ2 : ζ ≠ ζ⁻¹) : RootData p (torus p K) where
  ι := {s : Finset (Fin 4) // s.card = 2}
  block s := pairBlock K s.1
  hyp s := hypSub p K s.1
  W := (permSL K).range
  W_le := by
    rintro _ ⟨σ, rfl⟩
    exact permSL_mem_normalizer_torus σ
  hyp_le s := hypSub_le_torus p s.1
  hyp_ne s := hypSub_ne_torus hζp hζ0 hζ2 s.2
  hyp_inj s s' h := Subtype.ext (hypSub_inj hζp hζ0 hζ2 s.2 s'.2 h)
  block_le s := pairBlock_le_centralizer p s.1
  block_simple s N hN hnorm := by
    have := isSimpleGroup_pairBlock h4 s.2
    exact eq_bot_or_eq_of_normal_subgroupOf _ N hN hnorm
  derived_le S hS _ := derived_le_std S hS
  weyl := by
    rintro _ ⟨σ, rfl⟩ s
    exact ⟨⟨s.1.map σ.toEmbedding, by rw [Finset.card_map]; exact s.2⟩, map_conj_pairBlock σ s.1,
      map_conj_hypSub σ s.1⟩

theorem stdRoot_genBlocks (h4 : 4 ≤ Nat.card K) {ζ : K} (hζp : ζ ^ p = 1) (hζ0 : ζ ≠ 0)
    (hζ2 : ζ ≠ ζ⁻¹) : (stdRoot p K h4 hζp hζ0 hζ2).GenBlocks := by
  intro J hJ hgen
  have hne : J.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    subst hcon
    have h1 : SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) (1 : K) ∈
        (⊤ : Subgroup (SL(4, K))) := trivial
    rw [← hgen] at h1
    simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at h1
    have h2 := congrArg (fun g : SL(4, K) => g.1 0 1) h1
    simp [SpecialLinearGroup.transvection_coe] at h2
  obtain ⟨r₀, hr₀⟩ := hne
  rw [Set.eq_univ_iff_forall]
  intro r'
  obtain ⟨σ, hσ⟩ := exists_perm_map_eq r₀.2 r'.2
  obtain ⟨j, hjJ, -, hjh⟩ := hJ (permSL K σ) ⟨σ, rfl⟩ r₀ hr₀
  have h1 : hypSub p K r'.1 = hypSub p K j.1 := by
    rw [← hσ, ← map_conj_hypSub]
    exact hjh
  have : r' = j := Subtype.ext (hypSub_inj hζp hζ0 hζ2 r'.2 j.2 h1)
  rw [this]
  exact hjJ

theorem exists_stdRoot (h4 : 4 ≤ Nat.card K) {ζ : K} (hζp : ζ ^ p = 1) (hζ0 : ζ ≠ 0) (hζ2 : ζ ≠ ζ⁻¹) :
    ∃ R : RootData p (torus p K), R.GenBlocks :=
  ⟨stdRoot p K h4 hζp hζ0 hζ2, stdRoot_genBlocks h4 hζp hζ0 hζ2⟩

end CFSG.RankThree.PartOne.KFCL.L4
