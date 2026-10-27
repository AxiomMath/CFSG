module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixModelTransport
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  (stabilizer unipotent exists_sylow_unipotent)
open scoped Pointwise

theorem c8_card_stabilizer_lagrangianZero :
    Nat.card (stabilizer 3 (ZMod 2) (lagrangianZero 3)) = 10752 := by
  have hle : (tauSym 3).range ≤ stabilizer 3 (ZMod 2) (lagrangianZero 3) := by
    rw [← normalizer_range_tauSym]
    exact Subgroup.le_normalizer
  have hker : Nat.card (lagrangianLevi 3).ker = 64 := by
    rw [ker_lagrangianLevi]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_range_tauSym]
    norm_num
  have hrange : Nat.card (lagrangianLevi 3).range = 168 := by
    rw [MonoidHom.range_eq_top_of_surjective _ lagrangianLevi_surjective, Subgroup.card_top,
      Matrix.card_GL_field (𝔽 := ZMod 2) 3, ZMod.card, Fin.prod_univ_three]
    norm_num
  have h := Subgroup.card_ker_mul_card_range (lagrangianLevi 3)
  rw [hker, hrange] at h
  rw [← h]

theorem c8_exists_conj_eq_range_tauSym {E : Subgroup (StatedSp 3 (ZMod 2))}
    (hE : IsElemAbelian 2 E) (h64 : Nat.card E = 64) :
    ∃ g : StatedSp 3 (ZMod 2), E.map (MulAut.conj g).toMonoidHom = (tauSym 3).range := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hEQ⟩ := (IsElemAbelian.isPGroup hE).exists_le_sylow
  obtain ⟨U, hU⟩ := exists_sylow_unipotent (K := ZMod 2) 2 3
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 3 (ZMod 2)) Q U
  have hmap : (Q : Subgroup (StatedSp 3 (ZMod 2))).map (MulAut.conj g).toMonoidHom =
      unipotent 3 (ZMod 2) := by
    have h := congrArg (fun P : Sylow 2 (StatedSp 3 (ZMod 2)) =>
      (P : Subgroup (StatedSp 3 (ZMod 2)))) hg
    rw [Sylow.coe_subgroup_smul, hU] at h
    rwa [Subgroup.pointwise_smul_def] at h
  refine ⟨g, ?_⟩
  set E' : Subgroup (StatedSp 3 (ZMod 2)) := E.map (MulAut.conj g).toMonoidHom with hE'
  have hE'e : IsElemAbelian 2 E' := IsElemAbelian.map hE (MulAut.conj g).toMonoidHom
  have hcardE' : Nat.card E' = 64 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective, h64]
  have hE'u : E' ≤ unipotent 3 (ZMod 2) := by
    rw [hE']
    exact (Subgroup.map_mono hEQ).trans (le_of_eq hmap)
  have hcomm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    intro x hx y hy
    haveI : IsMulCommutative E' := hE'e.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E') ⟨y, hy⟩)
  have hsq : ∀ x ∈ E', x * x = 1 := by
    intro x hx
    have h := hE'e.2 x hx
    rwa [pow_two] at h
  rcases le_range_tauSym_or_card_le hE'u hcomm hsq with hsub | hle
  · exact Subgroup.eq_of_le_of_card_ge hsub (by rw [card_range_tauSym, hcardE']; norm_num)
  · rw [hcardE'] at hle
    norm_num at hle

theorem c8_exists_model_radical {H' : Type*} [Group H'] {H : Subgroup H'}
    (φ : ↥H ≃* ↥(StatedSp 3 (ZMod 2))) {N P : Subgroup H'} (hNP : N ≤ P) (hPH : P ≤ H)
    (hN : IsElemAbelian 2 N) (hN64 : Nat.card N = 64) (hNn : (N.subgroupOf P).Normal)
    (hP : Nat.card P = 10752) :
    ∃ ψ : ↥H ≃* ↥(StatedSp 3 (ZMod 2)), N = pullSub ψ (tauSym 3).range ∧
      P = pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) := by
  classical
  have hNH : N ≤ H := hNP.trans hPH
  have hE : IsElemAbelian 2 ((N.subgroupOf H).map φ.toMonoidHom) :=
    IsElemAbelian.map (IsElemAbelian.subgroupOf hN H) φ.toMonoidHom
  have hE64 : Nat.card ((N.subgroupOf H).map φ.toMonoidHom) = 64 := by
    rw [Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, hN64]
  obtain ⟨g, hg⟩ := c8_exists_conj_eq_range_tauSym hE hE64
  set ψ : ↥H ≃* ↥(StatedSp 3 (ZMod 2)) := φ.trans (MulAut.conj g) with hψ
  have hψhom : ψ.toMonoidHom = (MulAut.conj g).toMonoidHom.comp φ.toMonoidHom := by
    rw [hψ]
    rfl
  have hNR : (N.subgroupOf H).map ψ.toMonoidHom = (tauSym 3).range := by
    rw [hψhom, ← Subgroup.map_map]
    exact hg
  have hNpull : N = pullSub ψ (tauSym 3).range := by
    rw [eq_pullSub_of_le ψ hNH, hNR]
  have hPleN : P ≤ Subgroup.normalizer (N : Set H') :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hNn
  have hPpull : P = pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) := by
    have hle : P ≤ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) := by
      have h1 : P ≤ Subgroup.normalizer (N : Set H') ⊓ H := le_inf hPleN hPH
      rw [hNpull, normalizer_pullSub_inf ψ (tauSym 3).range, normalizer_range_tauSym] at h1
      exact h1
    haveI : Finite (pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3))) :=
      Nat.finite_of_card_ne_zero (by
        rw [card_pullSub, c8_card_stabilizer_lagrangianZero]
        norm_num)
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_pullSub, c8_card_stabilizer_lagrangianZero, hP])
  exact ⟨ψ, hNpull, hPpull⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
