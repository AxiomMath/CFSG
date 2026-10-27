module

public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt
public import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative

theorem ggWeylFrame_of_signedModel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')} {k : ℕ} (hk : 3 ≤ k)
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hW : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      GGTorusWeylElt p A n)
    (hsgn : ∀ i : Fin k, ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hsp : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn))) :
    GGWeylFrame p A (CoxeterMatrix.B k) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hk2 : 2 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hdata : ∀ i : Fin k, ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (ggSpSigned_spReflAut p k i) := by
    intro i
    by_cases h : i.val + 1 < k
    · obtain ⟨m, hm, he⟩ := hperm (Equiv.swap i ⟨i.val + 1, h⟩)
      refine ⟨m, hm, ?_⟩
      rw [show ggSpSigned_spReflAut p k i =
          SpCoord.permAut (Equiv.swap i ⟨i.val + 1, h⟩) from by
        simp only [ggSpSigned_spReflAut, dif_pos h]]
      exact he
    · obtain ⟨m, hm, he⟩ := hsgn i
      refine ⟨m, hm, ?_⟩
      rw [show ggSpSigned_spReflAut p k i = SpCoord.sgnAut i from by
        simp only [ggSpSigned_spReflAut, dif_neg h]]
      exact he
  choose n hn heq using hdata
  have hweyl : ∀ i, GGTorusWeylElt p A (n i) := fun i => hW (n i) (hn i)
  have hrefl : ∀ i, GGIsReflection p (ggConjAut A (hn i)) := by
    intro i
    rw [heq i]
    by_cases h : i.val + 1 < k
    · rw [show ggSpSigned_spReflAut p k i =
          SpCoord.permAut (Equiv.swap i ⟨i.val + 1, h⟩) from by
        simp only [ggSpSigned_spReflAut, dif_pos h]]
      have hne : i ≠ (⟨i.val + 1, h⟩ : Fin k) := by
        intro hh
        have : i.val = i.val + 1 := congrArg Fin.val hh
        omega
      exact ggSpSigned_ggIsReflection_congr hp hp2 Θ
        (SpCoord.permAut_swap_sq i ⟨i.val + 1, h⟩)
        (SpCoord.card_fix_permAut_swap hp hp2 hne)
    · rw [show ggSpSigned_spReflAut p k i = SpCoord.sgnAut i from by
        simp only [ggSpSigned_spReflAut, dif_neg h]]
      exact ggSpSigned_ggIsReflection_congr hp hp2 Θ
        (SpCoord.sgnAut_sq i) (SpCoord.card_fix_sgnAut hp hp2 i)
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
  exact ⟨n, hn, hweyl, hrefl, e, he⟩

end CFSG.StandardType

end
