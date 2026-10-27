module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicLinear
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LieType.Steinberg.Classical.SpinPlus
public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

namespace LayerCyc

theorem ggPSections_of_mulEquiv {p : ℕ} {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    (h : GGPSections p H) : GGPSections p H' := by
  intro E _ _ η hη hker hpk
  set η' : E →* H := e.symm.toMonoidHom.comp η with hη'def
  have hker' : η'.ker = η.ker := by
    ext x
    show e.symm (η x) = 1 ↔ η x = 1
    exact map_eq_one_iff _ e.symm.injective
  obtain ⟨σ, hσ⟩ := h E η' (e.symm.surjective.comp hη) (hker' ▸ hker) (hker' ▸ hpk)
  refine ⟨σ.comp e.symm.toMonoidHom, fun y => ?_⟩
  apply e.symm.injective
  exact hσ (e.symm y)

theorem commutator_largeEvenOmegaPlus {m : ℕ} {K : Type} [Field K] (hm : 3 ≤ m) :
    commutator (LargeEvenOmega (LargeEvenQPlus K m)) = ⊤ :=
  (Spin.isPerfect_statedOmega_quadPlus (K := K) hm).commutator_eq_top

theorem largeEvenOmegaMinus_map_glReindex (m : ℕ) (K : Type) [Field K] (b c : K) :
    (LargeEvenOmega (LargeEvenQMinus m b c)).map
      (CFSG.ComponentClassification.ClassicalModelStatedBridge.glReindex K
        (Equiv.sumAssoc (Fin m) (Fin m) (Fin 2)) :
        GL ((Fin m ⊕ Fin m) ⊕ Fin 2) K →* GL (Fin m ⊕ Fin m ⊕ Fin 2) K) =
      StatedOmega (StatedQuadMinus (m + 1) K b c) :=
  CFSG.ComponentClassification.ClassicalModelStatedBridge.map_glReindex_commutator_orthogonalGroup
    _ fun _ => rfl

@[expose] noncomputable def largeEvenOmegaMinusEquiv (m : ℕ) (K : Type) [Field K] (b c : K) :
    LargeEvenOmega (LargeEvenQMinus m b c) ≃* StatedOmega (StatedQuadMinus (m + 1) K b c) :=
  ((LargeEvenOmega (LargeEvenQMinus m b c)).equivMapOfInjective _
    (CFSG.ComponentClassification.ClassicalModelStatedBridge.glReindex K
      (Equiv.sumAssoc (Fin m) (Fin m) (Fin 2))).injective).trans
    (MulEquiv.subgroupCongr (largeEvenOmegaMinus_map_glReindex m K b c))

theorem commutator_largeEvenOmegaMinus {m : ℕ} {K : Type} [Field K] [Finite K] (hm : 3 ≤ m)
    {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    commutator (LargeEvenOmega (LargeEvenQMinus m b c)) = ⊤ := by
  have := Spin.isPerfect_statedOmega_quadMinus (n := m + 1) (K := K) (by omega) hbc
  have : Group.IsPerfect (LargeEvenOmega (LargeEvenQMinus m b c)) :=
    Group.IsPerfect.ofSurjective (f := (largeEvenOmegaMinusEquiv m K b c).symm.toMonoidHom)
      (largeEvenOmegaMinusEquiv m K b c).symm.surjective
  exact Group.IsPerfect.commutator_eq_top

theorem ggPSections_spinPlus
    {m : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGPSections p (spinGroup (Spin.quadPlus m K)) := by
  intro E _ _ η hη hker hpk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := LayerCC.not_two_dvd_card_of_isPGroup hp hp2 hpk
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (Spin.plusDatum m K hm).isFiniteType (Dv := (Spin.plusDatum m K hm).divisible) rfl
  have hE := CFSG.LieType.Steinberg.SpinPlus.chevalleyExtras (K := K) hm O
    CFSG.LieType.Steinberg.SpinPlus.commC (CFSG.LieType.Steinberg.SpinPlus.commutatorFormula hm O)
  exact (CFSG.LieType.Steinberg.existsUnique_section_of_sl2_lift
    (CFSG.LieType.Steinberg.SpinPlus.isCTGroupDatum (K := K) hm)
    (Spin.plusDatum_steinbergExtras hm) hE.param hE.rankOne hη hker hC fun ρ => by
      obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift hη hker hC ρ
      exact ⟨ρ', fun g => congrArg (· g) hρ'⟩).exists

theorem ggPSections_spinMinus
    {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : GGPSections p (spinGroup (Spin.quadMinus n K b c)) := by
  intro E _ _ η hη hker hpk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_coprime hbc
    hn hη hker ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (LayerCC.not_two_dvd_card_of_isPGroup hp hp2 hpk))

end LayerCyc

open LayerCyc in
theorem ggPSections_largeEvenOmegaPlus
    {m : ℕ} (hm : 3 ≤ m) {K : Type}
    [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGPSections p (LargeEvenOmega (LargeEvenQPlus K m)) := by
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadPlus m K)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadPlus_eq_bot (n := m) (K := K) CharTwo.two_eq_zero)
  have hrange : (Spin.spinMatrix (Spin.quadPlus m K)).range =
      LargeEvenOmega (LargeEvenQPlus K m) :=
    Spin.range_spinMatrix_quadPlus hm
  exact ggPSections_of_mulEquiv ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))
    (ggPSections_spinPlus hm hp hp2)

open LayerCyc in
theorem ggPSections_largeEvenOmegaMinus
    {m : ℕ} (hm : 3 ≤ m) {K : Type}
    [Field K] [Finite K] [CharP K 2] {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : GGPSections p (LargeEvenOmega (LargeEvenQMinus m b c)) := by
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadMinus (m + 1) K b c)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadMinus_eq_bot (n := m + 1) hbc CharTwo.two_eq_zero)
  have hrange := Spin.range_spinMatrix_quadMinus (n := m + 1) (K := K) (by omega) hbc
  exact ggPSections_of_mulEquiv
    (((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans
      (largeEvenOmegaMinusEquiv m K b c).symm)
    (ggPSections_spinMinus (n := m + 1) (by omega) hbc hp hp2)

end CFSG.StandardType

end
