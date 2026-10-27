module

public import Mathlib.GroupTheory.Commutator.Basic
public import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverBase

set_option autoImplicit false

public section

namespace CFSG

theorem exists_autEquiv_of_lifts {F S : Type*} [Group F] [Group S]
    (hF : commutator F = ⊤) (q : F →* S)
    (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.center F)
    (hlift : ∀ β : MulAut S, ∃ α : MulAut F, ∀ u : F, q (α u) = β (q u)) :
    ∃ Φ : MulAut F ≃* MulAut S,
      (∀ (α : MulAut F) (u : F), q (α u) = Φ α (q u)) ∧
      (∀ (β : MulAut S) (u : F), q (Φ.symm β u) = β (q u)) ∧
      (∀ (β : MulAut S) (α : MulAut F),
        (∀ u : F, q (α u) = β (q u)) → α = Φ.symm β) ∧
      (∀ u : F, Φ (MulAut.conj u) = MulAut.conj (q u)) ∧
      (∀ α : MulAut F,
        Φ α ∈ (MulAut.conj : S →* MulAut S).range ↔
          α ∈ (MulAut.conj : F →* MulAut F).range) ∧
      (∀ Φ' : MulAut F ≃* MulAut S,
        (∀ (α : MulAut F) (u : F), q (α u) = Φ' α (q u)) → Φ' = Φ) := by
  classical
  let b : F ⧸ Subgroup.center F ≃* S :=
    QuotientGroup.liftEquiv (Subgroup.center F) hq hker.symm
  let Φ0 : MulAut F →* MulAut S :=
    (MulAut.congr b).toMonoidHom.comp (MulAut.mapQuotient (Subgroup.center F))
  have hb : ∀ u : F, b (u : F ⧸ Subgroup.center F) = q u := by
    intro u
    exact QuotientGroup.liftEquiv_mk (Subgroup.center F) hq hker.symm u
  have hΦ0 : ∀ (α : MulAut F) (u : F), q (α u) = Φ0 α (q u) := by
    intro α u
    have hb_symm : b.symm (q u) = (u : F ⧸ Subgroup.center F) := by
      rw [← hb u, MulEquiv.symm_apply_apply]
    calc
      q (α u) = b (α u : F ⧸ Subgroup.center F) := (hb (α u)).symm
      _ = b ((MulAut.mapQuotient (Subgroup.center F) α)
            (u : F ⧸ Subgroup.center F)) := by
            rw [MulAut.mapQuotient_mk]
      _ = b ((MulAut.mapQuotient (Subgroup.center F) α) (b.symm (q u))) := by
            rw [hb_symm]
      _ = ((MulAut.congr b) (MulAut.mapQuotient (Subgroup.center F) α)) (q u) := by
            simp [MulAut.congr_apply]
      _ = Φ0 α (q u) := rfl
  have hΦ0_injective : Function.Injective Φ0 := by
    intro α α' h
    have hcomp : q.comp α.toMonoidHom = q.comp α'.toMonoidHom := by
      ext u
      calc
        q (α u) = Φ0 α (q u) := hΦ0 α u
        _ = Φ0 α' (q u) := by rw [h]
        _ = q (α' u) := (hΦ0 α' u).symm
    have hhom : α.toMonoidHom = α'.toMonoidHom :=
      CFSG.ComponentClassification.GrSLit.L34Facts.hom_ext_of_central
        hF q hker.le hcomp
    exact MulEquiv.ext fun u => DFunLike.congr_fun hhom u
  have hΦ0_surjective : Function.Surjective Φ0 := by
    intro β
    obtain ⟨α, hα⟩ := hlift β
    refine ⟨α, ?_⟩
    refine MulEquiv.ext fun y => ?_
    obtain ⟨u, rfl⟩ := hq y
    exact (hΦ0 α u).symm.trans (hα u)
  let Φ : MulAut F ≃* MulAut S :=
    MulEquiv.ofBijective Φ0 ⟨hΦ0_injective, hΦ0_surjective⟩
  have hΦα : ∀ α : MulAut F, Φ α = Φ0 α := by
    intro α
    exact MulEquiv.ofBijective_apply Φ0 ⟨hΦ0_injective, hΦ0_surjective⟩ α
  have hΦ : ∀ (α : MulAut F) (u : F), q (α u) = Φ α (q u) := by
    intro α u
    rw [hΦα α]
    exact hΦ0 α u
  have hconj : ∀ u : F, Φ (MulAut.conj u) = MulAut.conj (q u) := by
    intro u
    refine MulEquiv.ext fun y => ?_
    obtain ⟨v, rfl⟩ := hq y
    calc
      Φ (MulAut.conj u) (q v) = q ((MulAut.conj u) v) :=
        (hΦ (MulAut.conj u) v).symm
      _ = q (u * v * u⁻¹) := by rw [MulAut.conj_apply]
      _ = q u * q v * (q u)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = MulAut.conj (q u) (q v) := by rw [MulAut.conj_apply]
  refine ⟨Φ, hΦ, ?_, ?_, hconj, ?_, ?_⟩
  · intro β u
    calc
      q (Φ.symm β u) = Φ (Φ.symm β) (q u) := hΦ (Φ.symm β) u
      _ = β (q u) := by rw [MulEquiv.apply_symm_apply]
  · intro β α h
    have hβα : Φ α = β := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨u, rfl⟩ := hq y
      exact (hΦ α u).symm.trans (h u)
    rw [← hβα]
    rw [MulEquiv.symm_apply_apply]
  · intro α
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨u, rfl⟩ := hq s
      refine MonoidHom.mem_range.mpr ⟨u, ?_⟩
      apply Φ.injective
      rw [hconj u]
      exact hs
    · rintro ⟨u, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨q u, (hconj u).symm⟩
  · intro Φ' hΦ'
    refine MulEquiv.ext fun α => ?_
    refine MulEquiv.ext fun y => ?_
    obtain ⟨u, rfl⟩ := hq y
    exact (hΦ' α u).symm.trans (hΦ α u)

theorem forall_mulAut_eq_conj_of_forall_mulAut_eq_conj {F S : Type*} [Group F] [Group S]
    (hF : commutator F = ⊤) (q : F →* S) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center F) (hZ : Subgroup.center S = ⊥)
    (hInner : ∀ β : MulAut S, ∃ s : S, β = MulAut.conj s) :
    ∀ α : MulAut F, ∃ f : F, α = MulAut.conj f := by
  have hker' : q.ker = Subgroup.center F := by
    refine le_antisymm hker ?_
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzS : q z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨u, rfl⟩ := hq s
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz u]
    rwa [hZ, Subgroup.mem_bot] at hzS
  have hlift : ∀ β : MulAut S, ∃ α : MulAut F, ∀ u : F, q (α u) = β (q u) := by
    intro β
    obtain ⟨s, rfl⟩ := hInner β
    obtain ⟨f, rfl⟩ := hq s
    refine ⟨MulAut.conj f, fun u => ?_⟩
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  obtain ⟨Φ, -, -, -, -, hInn, -⟩ := exists_autEquiv_of_lifts hF q hq hker' hlift
  intro α
  have hΦα : Φ α ∈ (MulAut.conj : S →* MulAut S).range := by
    obtain ⟨s, hs⟩ := hInner (Φ α)
    exact ⟨s, hs.symm⟩
  obtain ⟨f, hf⟩ := (hInn α).mp hΦα
  exact ⟨f, hf.symm⟩

end CFSG
