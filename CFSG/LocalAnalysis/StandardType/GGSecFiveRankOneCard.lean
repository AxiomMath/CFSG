module

public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.StandardType

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

private lemma ggSL2_arith {q : ℕ} (hq : 2 ≤ q) :
    ((q ^ 2 - 1) * (q ^ 2 - q)) / (q - 1) = q * (q ^ 2 - 1) := by
  have hqpos : 0 < q - 1 := by omega
  have hsub : q ^ 2 - q = q * (q - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hsub]
  rw [← mul_assoc]
  rw [mul_comm (q ^ 2 - 1) q]
  exact Nat.mul_div_cancel _ hqpos

private lemma ggSL2_val_eq (q : ℕ) : q * (q ^ 2 - 1) = q ^ 3 - q := by
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  congr 1
  ring

private lemma ggSL2_val_lt {q q' : ℕ} (hq : 1 ≤ q) (h : q < q') :
    q * (q ^ 2 - 1) < q' * (q' ^ 2 - 1) := by
  rw [ggSL2_val_eq, ggSL2_val_eq]
  have hq3 : q ≤ q ^ 3 := by
    have := Nat.pow_le_pow_right (n := q) (by omega) (show 1 ≤ 3 by norm_num)
    simpa using this
  have hq'3 : q' ≤ q' ^ 3 := by
    have := Nat.pow_le_pow_right (n := q') (by omega) (show 1 ≤ 3 by norm_num)
    simpa using this
  have hcast : ((q ^ 3 - q : ℕ) : ℤ) < ((q' ^ 3 - q' : ℕ) : ℤ) := by
    rw [Nat.cast_sub hq3, Nat.cast_sub hq'3]
    push_cast
    have hfac : (q' : ℤ) ^ 3 - q' - ((q : ℤ) ^ 3 - q)
        = ((q' : ℤ) - q) * ((q' : ℤ) ^ 2 + (q' : ℤ) * q + (q : ℤ) ^ 2 - 1) := by
      ring
    have h1 : (0 : ℤ) < (q' : ℤ) - q := by omega
    have h2 : (0 : ℤ) < (q' : ℤ) ^ 2 + (q' : ℤ) * q + (q : ℤ) ^ 2 - 1 := by
      nlinarith [hq, h, sq_nonneg ((q' : ℤ)), sq_nonneg ((q : ℤ))]
    nlinarith [hfac, mul_pos h1 h2]
  exact_mod_cast hcast

theorem ggSL2_card (F : Type) [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  haveI := Fintype.ofFinite F
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field (𝔽 := F) 2, Fin.prod_univ_two, Nat.card_eq_fintype_card]
  norm_num
  exact ggSL2_arith hq

theorem ggSL2_card_inj {F F' : Type} [Field F] [Finite F] [Field F'] [Finite F']
    (h : Nat.card SL(2, F) = Nat.card SL(2, F')) : Nat.card F = Nat.card F' := by
  have hF : 1 ≤ Nat.card F := le_of_lt Finite.one_lt_card
  have hF' : 1 ≤ Nat.card F' := le_of_lt Finite.one_lt_card
  rw [ggSL2_card F, ggSL2_card F'] at h
  rcases lt_trichotomy (Nat.card F) (Nat.card F') with hlt | heq | hgt
  · exact absurd h (ggSL2_val_lt hF hlt).ne
  · exact heq
  · exact absurd h.symm (ggSL2_val_lt hF' hgt).ne

section Helpers

variable {F : Type} [Field F] {X : Type} [Group X]

private lemma ker_comp_conj_le_center {θ : SL(3, F) →* X}
    (hθ : θ.ker ≤ Subgroup.center SL(3, F)) (c : SL(3, F)) :
    (θ.comp (MulAut.conj c⁻¹).toMonoidHom).ker ≤ Subgroup.center SL(3, F) := by
  intro x hx
  have hx1 : θ (c⁻¹ * x * c) = 1 := by
    have h := MonoidHom.mem_ker.mp hx
    change θ ((MulAut.conj c⁻¹) x) = 1 at h
    simpa only [MulAut.conj_apply, inv_inv] using h
  have hzc : c⁻¹ * x * c ∈ Subgroup.center SL(3, F) := hθ hx1
  have hcz : c * (c⁻¹ * x * c) * c⁻¹ = c⁻¹ * x * c := by
    have hcomm := (Subgroup.mem_center_iff.mp hzc) c
    rw [hcomm]
    group
  have hxid : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
  rw [hxid, hcz]
  exact hzc

private lemma card_map_block (θ : SL(3, F) →* X)
    (hθ : θ.ker ≤ Subgroup.center SL(3, F)) (i : ℕ) (h : i + 2 ≤ 3) :
    Nat.card (θ.comp (blockSL F 3 2 i h)).range = Nat.card SL(2, F) := by
  have hinj : Function.Injective (θ.comp (blockSL F 3 2 i h)) :=
    comp_blockSL_injective hθ h (by norm_num)
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private lemma map_conj_map_block_eq_range (θ : SL(3, F) →* X) (c : SL(3, F))
    (i : ℕ) (h : i + 2 ≤ 3) :
    (((blockSL F 3 2 i h).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ) =
      ((θ.comp (MulAut.conj c⁻¹).toMonoidHom).comp (blockSL F 3 2 i h)).range := by
  rw [Subgroup.map_map, ← MonoidHom.range_comp]

private lemma card_map_conj_map_block (θ : SL(3, F) →* X) (c : SL(3, F))
    (hθ : θ.ker ≤ Subgroup.center SL(3, F)) (i : ℕ) (h : i + 2 ≤ 3) :
    Nat.card (((blockSL F 3 2 i h).range.map (MulAut.conj c⁻¹).toMonoidHom).map θ) =
      Nat.card SL(2, F) := by
  rw [map_conj_map_block_eq_range θ c i h]
  exact card_map_block (θ.comp (MulAut.conj c⁻¹).toMonoidHom)
    (ker_comp_conj_le_center hθ c) i h

end Helpers

section Pair

variable {F : Type} [Field F] {X : Type} [Group X] {W U V : Subgroup X}

theorem ggLinearBlockPair_card_left (h : LinearBlockStandardPair F W U V) :
    Nat.card U = Nat.card SL(2, F) := by
  obtain ⟨θ, c, hW, hker, hUV⟩ := h
  rcases hUV with ⟨h12, h23⟩ | ⟨h12, h23⟩
  · rw [← h12]
    rw [show B12 F = (blockSL F 3 2 0 (by omega)).range from rfl]
    exact card_map_conj_map_block θ c hker 0 (by omega)
  · rw [← h23]
    rw [show B23 F = (blockSL F 3 2 1 (by omega)).range from rfl]
    exact card_map_conj_map_block θ c hker 1 (by omega)

theorem ggLinearBlockPair_card_right (h : LinearBlockStandardPair F W U V) :
    Nat.card V = Nat.card SL(2, F) := by
  obtain ⟨θ, c, hW, hker, hUV⟩ := h
  rcases hUV with ⟨h12, h23⟩ | ⟨h12, h23⟩
  · rw [← h23]
    rw [show B23 F = (blockSL F 3 2 1 (by omega)).range from rfl]
    exact card_map_conj_map_block θ c hker 1 (by omega)
  · rw [← h12]
    rw [show B12 F = (blockSL F 3 2 0 (by omega)).range from rfl]
    exact card_map_conj_map_block θ c hker 0 (by omega)

theorem ggLinearBlockPair_map_conj (h : LinearBlockStandardPair F W U V) (g : X) :
    LinearBlockStandardPair F (W.map (MulAut.conj g).toMonoidHom)
      (U.map (MulAut.conj g).toMonoidHom) (V.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨θ, c, hW, hker, hUV⟩ := h
  refine ⟨(MulAut.conj g).toMonoidHom.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hW]
  · rw [MonoidHom.ker_comp_of_injective θ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective]
    exact hker
  · have hmap : ∀ S : Subgroup SL(3, F),
        ((S.map (MulAut.conj c⁻¹).toMonoidHom).map
            ((MulAut.conj g).toMonoidHom.comp θ)) =
          ((S.map (MulAut.conj c⁻¹).toMonoidHom).map θ).map
            (MulAut.conj g).toMonoidHom := by
      intro S
      exact (Subgroup.map_map (S.map (MulAut.conj c⁻¹).toMonoidHom)
        (MulAut.conj g).toMonoidHom θ).symm
    rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [hmap, h1], by rw [hmap, h2]⟩
    · exact Or.inr ⟨by rw [hmap, h1], by rw [hmap, h2]⟩

theorem ggLinearBlockPair_exists_of_card_eq [Finite F] {F' : Type} [Field F'] [Finite F']
    (h : LinearBlockStandardPair F' W U V) (hU : Nat.card U = Nat.card SL(2, F)) :
    ∃ W' : Subgroup X, LinearBlockStandardPair F W' U V := by
  have hleft : Nat.card U = Nat.card SL(2, F') := ggLinearBlockPair_card_left h
  have hcard : Nat.card SL(2, F) = Nat.card SL(2, F') := hU.symm.trans hleft
  have hFF' : Nat.card F = Nat.card F' := ggSL2_card_inj hcard
  haveI := Fintype.ofFinite F
  haveI := Fintype.ofFinite F'
  have hc : Fintype.card F' = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hFF'.symm
  exact ⟨W, h.of_ringEquiv (FiniteField.ringEquivOfCardEq hc)⟩

end Pair

end CFSG.StandardType

end
