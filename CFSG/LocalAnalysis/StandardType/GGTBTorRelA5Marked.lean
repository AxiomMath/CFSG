module

public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt
public import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux

@[expose] public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative

theorem exists_markedB_of_signedModel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')} {k : ℕ} (hk2 : 2 ≤ k)
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (n : Fin k → L') (hn : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (heq : ∀ i, ggConjAut A (hn i) = MulAut.congr Θ (ggSpSigned_spReflAut p k i))
    (hsp : ∀ (m : L') (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hm))) :
    ∃ e : (CoxeterMatrix.B k).Group ≃*
        ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A),
      ∀ i, (e ((CoxeterMatrix.B k).simple i) : MulAut ↥A) = ggConjAut A (hn i) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hk1 : 1 ≤ k := by omega
  obtain ⟨e0, he0⟩ := ggRC_coxeterB_equiv_spSigned (p := p) hp2 hk2
  let gen : Fin k → ↥(SpJoin.spSignedGroup k p) := fun i =>
    ⟨SpJoin.spReflPerm k p i, SpJoin.spReflPerm_mem_spSignedGroup k p i⟩
  let ρc : ↥(SpJoin.spSignedGroup k p) →* MulAut ↥A :=
    (MulAut.congr Θ).toMonoidHom.comp (ggSpSigned_rho p k)
  have hρc_inj : Function.Injective ρc :=
    (MulAut.congr Θ).injective.comp (ggSpSigned_rho_injective p k)
  have hρc_gen : ∀ i, ρc (gen i) = ggConjAut A (hn i) := by
    intro i
    show MulAut.congr Θ (ggSpSigned_rho p k (gen i)) = ggConjAut A (hn i)
    rw [ggSpSigned_rho_spReflPerm p k i]
    exact (heq i).symm
  have htop : Subgroup.closure (Set.range gen) =
      (⊤ : Subgroup ↥(SpJoin.spSignedGroup k p)) :=
    ggSpSigned_closure_range_subtype (fun i => SpJoin.spReflPerm k p i)
      (fun i => SpJoin.spReflPerm_mem_spSignedGroup k p i) rfl
  have hrange_le : ρc.range ≤ ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    rw [MonoidHom.range_eq_map, Subgroup.map_le_iff_le_comap, ← htop]
    intro u hu
    refine Subgroup.closure_induction
      (p := fun u _ => ρc u ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
      ?_ ?_ ?_ ?_ hu
    · rintro u ⟨i, rfl⟩
      rw [hρc_gen i]
      exact ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
        (MonoidHom.mem_range.mpr ⟨n i, rfl⟩) (hn i)
    · rw [map_one]; exact Subgroup.one_mem _
    · intro x y hx hy ihx ihy
      rw [map_mul]; exact Subgroup.mul_mem _ ihx ihy
    · intro x hx ih
      rw [map_inv]; exact Subgroup.inv_mem _ ih
  have hrange_ge : ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤ ρc.range := by
    intro φ hφ
    obtain ⟨g, hgH, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hφ
    obtain ⟨m, rfl⟩ := hgH
    have hφeq : φ = ggConjAut A hgN := by
      apply MulEquiv.ext; intro b
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact hgφ b
    have hspn : IsSignedPerm ⇑((MulAut.congr Θ).symm φ) := by
      rw [hφeq]
      exact hsp m hgN
    obtain ⟨u, hu⟩ := ggSpSigned_isSignedPerm_mem_range (p := p) (k := k) hk1 hspn
    refine ⟨u, ?_⟩
    show MulAut.congr Θ (ggSpSigned_rho p k u) = φ
    rw [hu, MulEquiv.apply_symm_apply]
  have hrange : ρc.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    le_antisymm hrange_le hrange_ge
  let Ψ : ↥(SpJoin.spSignedGroup k p) ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    (MonoidHom.ofInjective hρc_inj).trans (MulEquiv.subgroupCongr hrange)
  let e : (CoxeterMatrix.B k).Group ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) := e0.trans Ψ
  have he : ∀ i, (e ((CoxeterMatrix.B k).simple i) : MulAut ↥A) = ggConjAut A (hn i) := by
    intro i
    have hgen : e0 ((CoxeterMatrix.B k).simple i) = gen i := Subtype.ext (he0 i)
    have hΨ : (Ψ (gen i) : MulAut ↥A) = ggConjAut A (hn i) := by
      change ρc (gen i) = ggConjAut A (hn i)
      exact hρc_gen i
    change (Ψ (e0 ((CoxeterMatrix.B k).simple i)) : MulAut ↥A) = ggConjAut A (hn i)
    rw [hgen]
    exact hΨ
  exact ⟨e, he⟩

theorem exists_rho_of_signedModel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')} {k : ℕ} (hk2 : 2 ≤ k)
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (n : Fin k → L') (hn : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (heq : ∀ i, ggConjAut A (hn i) = MulAut.congr Θ (ggSpSigned_spReflAut p k i))
    (hsp : ∀ (m : L') (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hm))) :
    ∃ ρ : (CoxeterMatrix.B k).Group →* MulAut ↥A, Function.Injective ρ ∧
      ρ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A ∧
      ∀ i (a : ↥A), ((ρ ((CoxeterMatrix.B k).simple i) a : ↥A) : MulAut L') =
        MulAut.conj (n i) * (a : MulAut L') * (MulAut.conj (n i))⁻¹ := by
  obtain ⟨e, he⟩ := exists_markedB_of_signedModel hp hp2 hk2 Θ n hn heq hsp
  refine ⟨(ggAutomizer (MulAut.conj : L' →* MulAut L').range A).subtype.comp e.toMonoidHom,
    (Subgroup.subtype_injective _).comp e.injective, ?_, ?_⟩
  · ext φ
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hφ
      obtain ⟨x, hx⟩ := e.surjective ⟨φ, hφ⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  · intro i a
    have h2 : (((e ((CoxeterMatrix.B k).simple i) : MulAut ↥A) a : ↥A) : MulAut L') =
        ((ggConjAut A (hn i) a : ↥A) : MulAut L') :=
      congrArg (fun φ : MulAut ↥A => ((φ a : ↥A) : MulAut L')) (he i)
    rw [ggConjAut_apply] at h2
    exact h2

end CFSG.StandardType
