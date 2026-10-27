module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelSubgroupBorelComplement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore

open CFSG.BenderSuzuki.MatrixGroups

variable {G : Type*} [Group G]

theorem exists_borel_complement_of_injective {J : Subgroup G} {k : Type*} [Field k] [Finite k]
    {f : ℕ} (hk : Nat.card k = 2 ^ f) (F : J →* PSL2MatrixGroup k) (hF : Function.Injective F)
    (hcore : CFSG.pCore 2 J ≠ ⊥) :
    ∃ W : Subgroup G, W ≤ J ∧ IsCyclic W ∧ Odd (Nat.card W) ∧ Nat.card W ∣ Nat.card k - 1 ∧
      (∃ b : ℕ, Nat.card J = 2 ^ b * Nat.card W) ∧
      ∀ W₀ : Subgroup G, W₀ ≤ W → W₀ ≠ ⊥ → J ⊓ Subgroup.normalizer (W₀ : Set G) ≤ W := by
  classical
  set A : Subgroup (PSL2MatrixGroup k) := F.range with hAdef
  let e : J ≃* A := MonoidHom.ofInjective hF
  have hcoreA : CFSG.pCore 2 A ≠ ⊥ := by
    rw [← CFSG.pCore_map_iso 2 e]
    intro h
    exact hcore ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h)
  obtain ⟨-, -, WA, hWAcyc, hWAodd, hWAdvd, hcompl, -, -, hWAN⟩ :=
    LinearModel.linear_subgroup_nontrivial_two_core_borel_complement hk A hcoreA
  set WJ : Subgroup J := WA.map e.symm.toMonoidHom with hWJdef
  set W : Subgroup G := WJ.map J.subtype with hWdef
  have hWcardJ : Nat.card W = Nat.card WJ := Subgroup.card_map_of_injective J.subtype_injective
  have hWJcard : Nat.card WJ = Nat.card WA := Subgroup.card_map_of_injective e.symm.injective
  have hmemW : ∀ x : J, (x : G) ∈ W ↔ e x ∈ WA := by
    intro x
    rw [hWdef, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      rw [hyx', hWJdef, Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hy
      exact hy
    · intro hx
      refine ⟨x, ?_, rfl⟩
      rw [hWJdef, Subgroup.mem_map_equiv, MulEquiv.symm_symm]
      exact hx
  refine ⟨W, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  · have c1 : WA ≃* WJ := WA.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
    have c2 : WJ ≃* W := WJ.equivMapOfInjective J.subtype J.subtype_injective
    exact (c1.trans c2).isCyclic.mp hWAcyc
  · rw [hWcardJ, hWJcard]
    exact hWAodd
  · rw [hWcardJ, hWJcard]
    exact hWAdvd
  · obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := A)).exists_card_eq
    refine ⟨b, ?_⟩
    rw [hWcardJ, hWJcard, ← hb, hcompl.card_mul_card, Nat.card_congr e.toEquiv]
  · intro W₀ hW₀W hW₀ x hx
    obtain ⟨hxJ, hxN⟩ := Subgroup.mem_inf.mp hx
    have hW₀J : W₀ ≤ J := hW₀W.trans (Subgroup.map_subtype_le _)
    set W₀A : Subgroup A := (W₀.subgroupOf J).map e.toMonoidHom with hW₀Adef
    have hW₀A : W₀A ≤ WA := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      exact (hmemW z).mp (hW₀W hz)
    have hW₀Ane : W₀A ≠ ⊥ := by
      obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW₀
      have hw1' : (⟨w, hW₀J hw⟩ : J) ≠ 1 := by
        intro h
        have hw' : w = 1 := congrArg Subtype.val h
        exact hw1 (Subtype.ext hw')
      intro hbot
      have hmem : e ⟨w, hW₀J hw⟩ ∈ W₀A := Subgroup.mem_map_of_mem _ hw
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hw1' (e.injective (hmem.trans e.map_one.symm))
    have hxN' : (⟨x, hxJ⟩ : J) ∈ Subgroup.normalizer ((W₀.subgroupOf J : Subgroup J) : Set J) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp hxN z
    have hexN : e ⟨x, hxJ⟩ ∈ Subgroup.normalizer (W₀A : Set A) :=
      Subgroup.le_normalizer_map e.toMonoidHom (Subgroup.mem_map_of_mem _ hxN')
    rw [(hWAN W₀A hW₀A hW₀Ane).2] at hexN
    exact (hmemW ⟨x, hxJ⟩).mpr hexN

end CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore
