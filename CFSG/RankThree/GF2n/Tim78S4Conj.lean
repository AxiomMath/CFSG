module

public import CFSG.RankThree.GF2n.Tim78S4Setting
import CFSG.RankThree.GF2n.Basic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

omit [Finite G] in
theorem conj (x : G) : Hyp4 (conjSubgroup x M) (conjSubgroup x B) (conjSubgroup x Q)
    (conjSubgroup x P) (conjSubgroup x T) := by
  let φ : G ≃* G := MulAut.conj x
  have hφ : ∀ U : Subgroup G, conjSubgroup x U = U.map φ.toMonoidHom := fun U => rfl
  have hinj : Function.Injective (fun U : Subgroup G => U.map φ.toMonoidHom) :=
    Subgroup.map_injective φ.injective
  have hback : ∀ U : Subgroup G, (U.map φ.toMonoidHom).map φ.symm.toMonoidHom = U := by
    intro U
    rw [Subgroup.map_map]
    have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G :=
      MonoidHom.ext φ.symm_apply_apply
    rw [this, Subgroup.map_id]
  have hback' : ∀ U : Subgroup G, (U.map φ.symm.toMonoidHom).map φ.toMonoidHom = U := by
    intro U
    rw [Subgroup.map_map]
    have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G :=
      MonoidHom.ext φ.apply_symm_apply
    rw [this, Subgroup.map_id]
  have hconj_mem : ∀ U : Subgroup G, ∀ y, y ∈ conjSubgroup x U ↔ x⁻¹ * y * x ∈ U := fun U y =>
    mem_conjSubgroup
  refine ⟨H.o2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact PartTwo.Late.isMaximalTwoLocal_map H.maxLocal φ
  ·
    have e : ↥M ≃* ↥(M.map φ.toMonoidHom) := MulEquiv.subgroupMap φ M
    show generalizedFitting ↥(M.map φ.toMonoidHom) = CFSG.Open.pCore 2 ↥(M.map φ.toMonoidHom)
    rw [← CFSG.WholeGroup.generalizedFitting_map_mulEquiv e, ← CFSG.pCore_map_iso 2 e,
      H.fitting]
  ·
    have hcomm : ∀ (f : G ≃* G) (U : Subgroup G), IsMulCommutative U →
        IsMulCommutative (U.map f.toMonoidHom) := by
      intro f U hU
      refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      have : a' * b' = b' * a' := congrArg Subtype.val (hU.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
      show (a : G) * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul, this]
    have hfwd : ∀ U : Subgroup G, (U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
        IsMulCommutative U) → (U.map φ.toMonoidHom ≤ M.map φ.toMonoidHom ∧
        M.map φ.toMonoidHom ≤ Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup G) : Set G) ∧
        IsMulCommutative (U.map φ.toMonoidHom)) := by
      rintro U ⟨h1, h2, h3⟩
      refine ⟨Subgroup.map_mono h1, ?_, hcomm φ U h3⟩
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono h2
    have hbwd : ∀ U : Subgroup G, (U ≤ M.map φ.toMonoidHom ∧
        M.map φ.toMonoidHom ≤ Subgroup.normalizer (U : Set G) ∧ IsMulCommutative U) →
        ((U.map φ.symm.toMonoidHom) ≤ M ∧ M ≤ Subgroup.normalizer
          ((U.map φ.symm.toMonoidHom : Subgroup G) : Set G) ∧
          IsMulCommutative (U.map φ.symm.toMonoidHom)) := by
      rintro U ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, hcomm φ.symm U h3⟩
      · have := Subgroup.map_mono (f := φ.symm.toMonoidHom) h1
        rwa [hback] at this
      · rw [← Subgroup.map_equiv_normalizer_eq]
        have := Subgroup.map_mono (f := φ.symm.toMonoidHom) h2
        rwa [hback] at this
    refine ⟨hfwd B H.maxAb.prop, fun y hy hBy => ?_⟩
    have h1 := H.maxAb.le_of_ge (hbwd y hy) (by
      have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hBy
      rwa [hφ B, hback] at this)
    have h2 := Subgroup.map_mono (f := φ.toMonoidHom) h1
    rwa [hback'] at h2
  ·
    intro y hy
    rw [hφ, Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have := H.sq_eq_one z hz
    simp [φ, ← map_pow, this]
  · exact isTI_conjSubgroup H.ti x
  ·
    have : Nat.card (conjSubgroup x B) = Nat.card B := by
      rw [hφ]
      exact Subgroup.card_map_of_injective φ.injective
    have := H.q4
    omega
  ·
    rw [hφ, hφ, H.hQ]
    exact CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.inSubgroup_pCore_map φ M
  ·
    have key : ∀ g : G, conjSubgroup g (conjSubgroup x B) =
        conjSubgroup x (conjSubgroup (x⁻¹ * g * x) B) := by
      intro g; rw [← conjSubgroup_mul, ← conjSubgroup_mul]; congr 1; group
    apply le_antisymm
    · rw [hφ P, Subgroup.map_le_iff_le_comap, H.hP]
      refine iSup₂_le fun g hg => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      have e : conjSubgroup x (conjSubgroup g B) =
          conjSubgroup (x * g * x⁻¹) (conjSubgroup x B) := by
        rw [← conjSubgroup_mul, ← conjSubgroup_mul]; congr 1; group
      show conjSubgroup x (conjSubgroup g B) ≤ _
      rw [e]
      exact le_iSup₂ (f := fun (g' : G) (_ : conjSubgroup g' (conjSubgroup x B) ≤
        conjSubgroup x Q) => conjSubgroup g' (conjSubgroup x B)) (x * g * x⁻¹)
        (by rw [← e]; exact Subgroup.map_mono hg)
    · refine iSup₂_le fun g' hg' => ?_
      rw [key g']
      have hQ' : conjSubgroup (x⁻¹ * g' * x) B ≤ Q := by
        have := hg'
        rw [key g'] at this
        exact (Subgroup.map_le_map_iff_of_injective φ.injective).mp this
      have hle : conjSubgroup (x⁻¹ * g' * x) B ≤ P := by
        rw [H.hP]
        exact le_iSup₂ (f := fun (g : G) (_ : conjSubgroup g B ≤ Q) => conjSubgroup g B)
          (x⁻¹ * g' * x) hQ'
      exact Subgroup.map_mono hle
  ·
    ext y
    rw [hconj_mem, H.hT, Subgroup.mem_inf, Subgroup.mem_inf, hconj_mem,
      Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    refine and_congr Iff.rfl ?_
    constructor
    · intro h p' hp'
      have hp : x⁻¹ * p' * x ∈ P := (hconj_mem P p').mp hp'
      have h1 := h _ hp
      calc p' * y = x * ((x⁻¹ * p' * x) * (x⁻¹ * y * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * y * x) * (x⁻¹ * p' * x)) * x⁻¹ := by rw [h1]
        _ = y * p' := by group
    · intro h p hp
      have hp' : x * p * x⁻¹ ∈ conjSubgroup x P := by
        rw [hconj_mem]
        simpa [mul_assoc] using hp
      have h1 := h _ hp'
      calc p * (x⁻¹ * y * x) = x⁻¹ * ((x * p * x⁻¹) * y) * x := by group
        _ = x⁻¹ * (y * (x * p * x⁻¹)) * x := by rw [h1]
        _ = (x⁻¹ * y * x) * p := by group
  ·
    obtain ⟨g, hgQ, hgne⟩ := H.notWC
    have e : conjSubgroup (x * g * x⁻¹) (conjSubgroup x B) =
        conjSubgroup x (conjSubgroup g B) := by
      rw [← conjSubgroup_mul, ← conjSubgroup_mul]; congr 1; group
    refine ⟨x * g * x⁻¹, ?_, ?_⟩
    · rw [e]
      exact Subgroup.map_mono hgQ
    · intro h
      apply hgne
      rw [e] at h
      exact hinj h
  · intro h
    exact H.PneQ (hinj h)

end Hyp4

end CFSG.RankThree.GF2n.Tim78
