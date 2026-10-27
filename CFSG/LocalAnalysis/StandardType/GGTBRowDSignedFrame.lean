module

public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt
public import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterD
public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux
import CFSG.LocalAnalysis.StandardType.GGTorusDWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative

theorem ggWeylFrame_of_dSignedModel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L' : Type} [Group L'] {A : Subgroup (MulAut L')} {k : ℕ} (hk : 4 ≤ k)
    (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hW : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      GGTorusWeylElt p A n)
    (hd : ∀ i j : Fin k, i ≠ j → ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i * sgnAut j))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hsp : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∏ i, ε i = 1 ∧ ∀ f i,
          toAdd ((MulAut.congr Θ).symm (ggConjAut A hn) f (π i)) = ε i * toAdd (f i)) :
    GGWeylFrame p A (ggCoxeterMatrixD k) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨eS, heS⟩ := DScalarTorus.exists_evenSignedCoxeterEquiv (p := p) (N := k) hp2 hk
  let H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) :=
    (ggAutomizer (MulAut.conj : L' →* MulAut L').range A).comap (MulAut.congr Θ).toMonoidHom
  have hdH : ∀ i j : Fin k, i ≠ j → sgnAut i * sgnAut j ∈ H := by
    intro i j hij
    obtain ⟨n, hn, hconj⟩ := hd i j hij
    change MulAut.congr Θ (sgnAut i * sgnAut j) ∈
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A
    rw [← hconj]
    exact ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
      (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have htH : ∀ σ : Equiv.Perm (Fin k), permAut σ ∈ H := by
    intro σ
    obtain ⟨n, hn, hconj⟩ := hperm σ
    change MulAut.congr Θ (permAut σ) ∈
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A
    rw [← hconj]
    exact ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
      (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have hH : DScalarTorus.evenSignedGroup (p := p) (N := k) ≤ H :=
    DScalarTorus.evenSignedGroup_le (p := p) (N := k) hp2 hdH htH
  have hsimple : ∀ i, MulAut.congr Θ (DScalarTorus.simpleReflection hk i) ∈
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    intro i
    have h := hH (eS ((ggCoxeterMatrixD k).simple i)).2
    rw [heS i] at h
    exact h
  have hdata : ∀ i, ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (DScalarTorus.simpleReflection hk i) := by
    intro i
    obtain ⟨g, hgH, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp (hsimple i)
    obtain ⟨n, rfl⟩ := hgH
    refine ⟨n, hgN, MulEquiv.ext fun b => Subtype.ext ?_⟩
    rw [ggConjAut_apply]
    exact (hgφ b).symm
  choose n hn hconj using hdata
  have hweyl : ∀ i, GGTorusWeylElt p A (n i) := fun i => hW (n i) (hn i)
  have hrefl : ∀ i, GGIsReflection p (ggConjAut A (hn i)) := by
    intro i
    rw [hconj i]
    by_cases hi : i.val + 1 < k
    · rw [show DScalarTorus.simpleReflection hk i =
          SpCoord.permAut (Equiv.swap i ⟨i.val + 1, hi⟩) from by
        simp only [DScalarTorus.simpleReflection, dif_pos hi]]
      have hne : i ≠ (⟨i.val + 1, hi⟩ : Fin k) := by
        intro hh
        have : i.val = i.val + 1 := congrArg Fin.val hh
        omega
      exact ggSpSigned_ggIsReflection_congr hp hp2 Θ
        (SpCoord.permAut_swap_sq i ⟨i.val + 1, hi⟩)
        (SpCoord.card_fix_permAut_swap hp hp2 hne)
    · rw [show DScalarTorus.simpleReflection hk i =
          SpCoord.sgnAut ⟨k - 2, by omega⟩ * SpCoord.sgnAut ⟨k - 1, by omega⟩ *
            SpCoord.permAut (Equiv.swap ⟨k - 2, by omega⟩ ⟨k - 1, by omega⟩) from by
        simp only [DScalarTorus.simpleReflection, dif_neg hi]]
      have hne : (⟨k - 2, by omega⟩ : Fin k) ≠ ⟨k - 1, by omega⟩ := by
        intro hh
        have h' : k - 2 = k - 1 := congrArg Fin.val hh
        omega
      exact ggSpSigned_ggIsReflection_congr hp hp2 Θ
        (OrthExcEven.sgnTransp_sq hne) (OrthExcEven.card_fix_sgnTransp hp hp2 hne)
  let ρ : (ggCoxeterMatrixD k).Group →* MulAut ↥A :=
    (MulAut.congr Θ).toMonoidHom.comp
      ((DScalarTorus.evenSignedGroup (p := p) (N := k)).subtype.comp eS.toMonoidHom)
  have hρ : Function.Injective ρ :=
    (MulAut.congr Θ).injective.comp
      ((DScalarTorus.evenSignedGroup (p := p) (N := k)).subtype_injective.comp eS.injective)
  have hρsimple : ∀ i, ρ ((ggCoxeterMatrixD k).simple i) = ggConjAut A (hn i) := by
    intro i
    rw [show ρ ((ggCoxeterMatrixD k).simple i) =
        MulAut.congr Θ (DScalarTorus.simpleReflection hk i) from
      congrArg (MulAut.congr Θ) (heS i)]
    exact (hconj i).symm
  have hρle : ρ.range ≤ ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    have hgen : Subgroup.closure (Set.range (ggCoxeterMatrixD k).simple) = ⊤ := by
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
        (ggCoxeterMatrixD k).toCoxeterSystem.subgroup_closure_range_simple
    have hle : Subgroup.closure (Set.range (ggCoxeterMatrixD k).simple) ≤
        (ggAutomizer (MulAut.conj : L' →* MulAut L').range A).comap ρ := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      change ρ ((ggCoxeterMatrixD k).simple i) ∈
        ggAutomizer (MulAut.conj : L' →* MulAut L').range A
      rw [hρsimple]
      exact ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
        (MonoidHom.mem_range.mpr ⟨n i, rfl⟩) (hn i)
    rintro _ ⟨w, rfl⟩
    exact hle (by rw [hgen]; trivial)
  have hρrange : ρ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    refine le_antisymm hρle ?_
    intro a ha
    obtain ⟨g, hgH, hgN, hga⟩ := mem_ggAutomizer_iff.mp ha
    obtain ⟨n, rfl⟩ := hgH
    have haeq : a = ggConjAut A hgN := MulEquiv.ext fun b => Subtype.ext (hga b)
    have hu : (MulAut.congr Θ).symm a ∈ DScalarTorus.evenSignedGroup (p := p) (N := k) := by
      have h := hsp n hgN
      rw [← haeq] at h
      exact h
    refine ⟨eS.symm ⟨(MulAut.congr Θ).symm a, hu⟩, ?_⟩
    change MulAut.congr Θ ↑(eS (eS.symm ⟨(MulAut.congr Θ).symm a, hu⟩)) = a
    rw [MulEquiv.apply_symm_apply]
    exact MulEquiv.apply_symm_apply (MulAut.congr Θ) a
  let e : (ggCoxeterMatrixD k).Group ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    (MonoidHom.ofInjective hρ).trans (MulEquiv.subgroupCongr hρrange)
  exact ⟨n, hn, hweyl, hrefl, e, fun i => hρsimple i⟩

end CFSG.StandardType

end
