module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3ETransport
public import CFSG.Quasithin.Vol2.F134LieL3Torus
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieDef

public section

namespace CFSG.Quasithin.H13.NQCore.Psl3Even

open CFSG.Quasithin.F134.LieL3
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped MatrixGroups

variable {A : Type} [Group A] {p : ℕ} {L P T : Subgroup A}

theorem false_of_borel (h : OddCfg p L P T) {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : ↥L ≃* projectiveSL 3 K)
    (hUe : ((T ⊓ L).subgroupOf L).map e.toMonoidHom = projUnitriangular 3 K)
    (hab : ∀ x ∈ (P.subgroupOf L).map e.toMonoidHom, ∀ y ∈ (P.subgroupOf L).map e.toMonoidHom,
      x * y = y * x)
    (hD1 : (P.subgroupOf L).map e.toMonoidHom ⊓ ratioGroup K ≠ ⊥)
    (hD2 : ¬ (P.subgroupOf L).map e.toMonoidHom ≤ ratioGroup K) : False := by
  classical
  have hLn : L.Normal := h.normal
  set P' : Subgroup (projectiveSL 3 K) := (P.subgroupOf L).map e.toMonoidHom with hP'def
  set α : A → MulAut (projectiveSL 3 K) := fun t => (e.symm.trans (MulAut.conjNormal t)).trans e
    with hαdef
  have hα : ∀ t (y : L), α t (e y) = e (MulAut.conjNormal t y) := fun t y => by
    rw [hαdef]
    simp
  have hαU : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A),
      (projUnitriangular 3 K).map (α t).toMonoidHom = projUnitriangular 3 K := by
    intro t ht
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hUe] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨MulAut.conjNormal t y, ?_, (hα t y).symm⟩
      have hy' := Subgroup.mem_subgroupOf.mp hy
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
      exact ⟨T.mul_mem (T.mul_mem ht.1 hy'.1) (T.inv_mem ht.1), hLn.conj_mem _ hy'.2 t⟩
    · rw [Subgroup.card_map_of_injective (α t).injective]
  have hαP : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ x ∈ P', α t x ∈ P' := by
    rintro t ht _ ⟨y, hy, rfl⟩
    refine ⟨MulAut.conjNormal t y, ?_, (hα t y).symm⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.mp ht.2 _).mp (Subgroup.mem_subgroupOf.mp hy)
  set Q : Subgroup (projectiveSL 3 K) := P' ⊓ ratioGroup K with hQdef
  have hαQ : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ x ∈ Q, α t x ∈ Q :=
    fun t ht x hx => ⟨hαP t ht x hx.1, map_mem_ratioGroup (hαU t ht) hx.2⟩
  set QA : Subgroup A := (Q.map e.symm.toMonoidHom).map L.subtype with hQAdef
  have hQAP : QA ≤ P := by
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hq.1
    have hy' : e.symm (e y) = y := e.symm_apply_apply y
    change ((e.symm (e y) : L) : A) ∈ P
    rw [hy']
    exact Subgroup.mem_subgroupOf.mp hy
  have hfwd : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ z ∈ QA, t * z * t⁻¹ ∈ QA := by
    rintro t ht _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨_, ⟨α t q, hαQ t ht q hq, rfl⟩, ?_⟩
    have h1 : e.symm (α t q) = MulAut.conjNormal t (e.symm q) := by
      have h2 := hα t (e.symm q)
      rw [e.apply_symm_apply] at h2
      rw [h2, e.symm_apply_apply]
    change ((e.symm (α t q) : L) : A) = t * ((e.symm q : L) : A) * t⁻¹
    rw [h1, MulAut.conjNormal_apply]
  have hnorm : T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (QA : Set A) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hfwd t ht z, fun hz => ?_⟩
    have h1 := hfwd t⁻¹ (inv_mem ht) _ hz
    rwa [show t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ = z by group] at h1
  have hcomm : ⁅P, P⁆ = ⊥ := commutator_eq_bot_of_map h.le e hab
  rcases h.irred QA (by rw [hcomm]; exact bot_le) hQAP hnorm with h' | h'
  · apply hD1
    rw [hcomm, hQAdef, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at h'
    exact h'
  · apply hD2
    have hP : P = (P.subgroupOf L).map L.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.le]
    rw [hQAdef, hP] at h'
    have h2 := Subgroup.map_injective L.subtype_injective h'
    have h3 : Q = P' := by
      rw [hP'def, ← h2, Subgroup.map_map]
      ext x
      simp
    intro x hx
    rw [← h3] at hx
    exact hx.2

end CFSG.Quasithin.H13.NQCore.Psl3Even
