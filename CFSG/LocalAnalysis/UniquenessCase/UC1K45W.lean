module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

theorem isMulCommutative_of_mulEquiv {M N : Type*} [Group M] [Group N] (e : M ≃* N)
    (h : IsMulCommutative N) : IsMulCommutative M :=
  IsMulCommutative.of_comm fun x y =>
    e.injective (by rw [map_mul, map_mul]; exact h.is_comm.comm _ _)

theorem eq_two_of_mul_pow_two_eq_four_mul {C Z d : ℕ} (h : C = Z * 2 ^ d) (h4 : C = 4 * Z)
    (hZ : 0 < Z) : d = 2 := by
  have hmain : Z * 2 ^ d = Z * 4 := by rw [← h, h4, mul_comm 4 Z]
  have hpow : 2 ^ d = 4 := Nat.mul_left_cancel hZ hmain
  have h2 : 2 ^ d = 2 ^ 2 := by rw [hpow]; norm_num
  exact Nat.pow_right_injective (le_refl 2) h2

theorem z3E9A5Mod2_of_map {H H' : Type} [Group H] [Group H'] (f : H →* H')
    (hf : Function.Injective f) (Y : Subgroup H) (h : Z3E9A5Mod2 (Y.map f)) :
    Z3E9A5Mod2 Y := by
  intro N hNnorm hN
  haveI : N.Normal := hNnorm
  let e : ↥Y ≃* ↥(Y.map f) := Subgroup.equivMapOfInjective Y f hf
  let N' : Subgroup ↥(Y.map f) := N.map e.toMonoidHom
  haveI : N'.Normal := hNnorm.map e.toMonoidHom e.surjective
  have hN' : N' = (CFSG.Open.pCoreOf 2 (Y.map f)).subgroupOf (Y.map f) := by
    have h1 : N' = CFSG.pCore 2 ↥(Y.map f) := by
      dsimp only [N']
      rw [hN, CFSG.openPCoreOf_subgroupOf]
      exact CFSG.pCore_map_iso 2 e
    rw [h1, CFSG.openPCoreOf_subgroupOf]
  let E : ↥Y ⧸ N ≃* ↥(Y.map f) ⧸ N' := QuotientGroup.congr N N' e rfl
  rcases h N' hN' with ⟨hcyc, hcard3⟩ | ⟨hcard9, hcomm⟩ | halt
  · exact Or.inl ⟨(MulEquiv.isCyclic E.symm).mp hcyc,
      (Nat.card_congr E.toEquiv).trans hcard3⟩
  · exact Or.inr (Or.inl ⟨(Nat.card_congr E.toEquiv).trans hcard9,
      isMulCommutative_of_mulEquiv E hcomm⟩)
  · refine Or.inr (Or.inr ?_)
    rcases halt with ⟨g⟩
    exact ⟨E.trans g⟩

theorem pairX_of_pairSp (hSymp : SympData) (hPair : PairSp) : PairX := by
  intro G _ _ X N _ _ hXp hcomm hsq hcyc hN a b ha hb hcarda hcardb
  obtain ⟨W, _, _, _, B, φ, _, hBnd, hBalt, hφinj, hisom, -, -, -, -, -, hcard⟩ :=
    hSymp G X N hXp hcomm hsq hcyc hN
  let a' : W ≃ₗ[ZMod 2] W := φ (QuotientGroup.mk a)
  let b' : W ≃ₗ[ZMod 2] W := φ (QuotientGroup.mk b)
  let Y : Subgroup (G ⧸ N) := (Subgroup.closure ({a, b} : Set G)).map (QuotientGroup.mk' N)
  have hZpos : 0 < Nat.card ↥((Subgroup.center ↥X).map X.subtype) := by
    haveI : Nonempty ↥((Subgroup.center ↥X).map X.subtype) := ⟨1, by simp⟩
    exact Nat.card_pos
  have ha3 : orderOf a' = 3 := by
    change orderOf (φ (QuotientGroup.mk a)) = 3
    rw [orderOf_injective φ hφinj]
    exact ha
  have hb3 : orderOf b' = 3 := by
    change orderOf (φ (QuotientGroup.mk b)) = 3
    rw [orderOf_injective φ hφinj]
    exact hb
  have hisomA : ∀ x y, B (a' x) (a' y) = B x y := by
    intro x y
    change B (φ (QuotientGroup.mk a) x) (φ (QuotientGroup.mk a) y) = B x y
    exact hisom (QuotientGroup.mk a) x y
  have hisomB : ∀ x y, B (b' x) (b' y) = B x y := by
    intro x y
    change B (φ (QuotientGroup.mk b) x) (φ (QuotientGroup.mk b) y) = B x y
    exact hisom (QuotientGroup.mk b) x y
  have hda : Module.finrank (ZMod 2)
      ↥(LinearMap.range ((a' : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2 :=
    eq_two_of_mul_pow_two_eq_four_mul (hcard a) hcarda hZpos
  have hdb : Module.finrank (ZMod 2)
      ↥(LinearMap.range ((b' : W →ₗ[ZMod 2] W) - LinearMap.id)) = 2 :=
    eq_two_of_mul_pow_two_eq_four_mul (hcard b) hcardb hZpos
  have hpair := hPair W B hBnd hBalt a' b' hisomA hisomB ha3 hb3 hda hdb
  have hYmap : Y.map φ = Subgroup.closure {a', b'} := by
    dsimp only [Y]
    rw [Subgroup.map_map, MonoidHom.map_closure, Set.image_pair]
    rfl
  have hY : Z3E9A5Mod2 (Y.map φ) := by rw [hYmap]; exact hpair
  exact z3E9A5Mod2_of_map φ hφinj Y hY

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
