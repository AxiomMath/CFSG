module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xc
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

namespace P22x

open CFSG.Open CFSG.Open.StatedAPI Matrix
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open scoped Matrix

section Shape

theorem sl2_order_ne (n : ℕ) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 168 ∧ 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 120 := by
  by_cases h : n ≤ 2
  · interval_cases n <;> simp
  · push Not at h
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h9 : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      apply Nat.mul_le_mul h8
      have : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    omega

variable {X V : Type} [Group X] [AddCommGroup V] [Module (ZMod 2) V]

theorem card_of_isL2Ev {Y : Type} [Group Y] {n : ℕ} (h : IsL2Ev Y n) :
    Nat.card Y = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_statedSL_two, hF]

theorem natL2_of_shape148 (ρ : Representation (ZMod 2) X V) (Hi : Subgroup X)
    (Ui C : Submodule (ZMod 2) V) {n' : ℕ} (h2 : IsL2Ev ↥Hi n') (hs : Shape148 ρ Hi Ui C) :
    ∃ n : ℕ, 1 ≤ n ∧ NatL2 ρ Hi Ui (Ui ⊓ C) n := by
  have hcard := card_of_isL2Ev h2
  have h168 : ∀ e : ↥Hi ≃* ↥(StatedSL 3 (ZMod 2)), False := by
    intro e
    have : Nat.card ↥Hi = 168 := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three, Nat.card_zmod]
      norm_num
    exact (sl2_order_ne n').1 (hcard.symm.trans this)
  rcases hs with h | h | h | h
  · exact h
  · obtain ⟨-, -, -, φ, -⟩ := h
    exact (h168 φ).elim
  · obtain ⟨Ai, hAi, -⟩ := h
    obtain ⟨-, -, -, φ, -⟩ := (hAi 0).2.2
    exact (h168 φ).elim
  · obtain ⟨-, -, -, φ, -⟩ := h
    have : Nat.card ↥Hi = 120 := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      rfl
    exact absurd (hcard.symm.trans this) (sl2_order_ne n').2

end Shape

section DataLevel

variable {G : Type} [Group G] [Finite G]

theorem natDec_of_data (D : Data G) (Ch : Choice2011 G) (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch)
    (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod] [Finite Umod]
    (e : ↥D.U ≃* Multiplicative Umod) (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod)
    (hc : ConjModule D.M D.U e ρ) : NatDec ρ (mbarImage D.M D.U (proofN D)) Nb := by
  obtain ⟨hsum, hsh⟩ := h3 hH c m Nb hNb Umod e ρ hc
  have hcl := h51 hH c m Nb hNb
  refine ⟨hNb.1, hsum, fun i => ?_⟩
  obtain ⟨n', hn', -⟩ := hcl i
  exact natL2_of_shape148 ρ (Nb i) _ _ hn' (hsh i)

end DataLevel

end P22x

end CFSG.LocalAnalysis.UniquenessCase.UC22
