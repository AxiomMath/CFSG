module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNsFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestCore
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_center_specialLinear_dvd {d : ℕ} {K : Type} [Field K] [Finite K] (hd : 0 < d) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K)) ∣ Nat.card K - 1 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := K)
    (n := Fin d) ⟨0, hd⟩).toEquiv, Fintype.card_fin, ← Nat.card_units K]
  exact Subgroup.card_subgroup_dvd_card (rootsOfUnity d K)

private theorem center_eq_bot_of_mulEquiv {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : Subgroup.center R' = ⊥) : Subgroup.center R = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ Subgroup.center R' := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx y]
  rw [h, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.mpr (e.injective (hx'.trans (map_one e).symm))

theorem ggSCWeylIrred_projectiveSL {d p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hpK0 : (p : K) ≠ 0) (hpK : ¬ p ∣ Nat.card K - 1) (hd : 0 < d) :
    GGSCWeylIrred p 0 (projectiveSL d K) := by
  refine ggSCWeylIrred_of_centralQuotient hp (proj d K) (proj_surjective d K) ?_ ?_
    (ggSCWeylIrred_specialLinear hp hpK0 hpK)
  · intro g hg
    rw [← scalars_eq_center]
    exact proj_eq_one_iff.mp hg
  · intro h
    exact hpK (h.trans (card_center_specialLinear_dvd hd))

theorem ggCenterPrime_projectiveSL {d p : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K - 1) (hd : 5 ≤ d) : GGCenterPrime p (projectiveSL d K) := by
  intro L' _ _ ψ hψ hker hperf hpZ
  obtain ⟨φ, hφsurj, hφ⟩ := TypeA.exists_sl_cover
    (TypeA.slHasSections_of_five_le (K := K) hd) ψ hψ hker hperf
  have hZker : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : ψ z ∈ Subgroup.center (projectiveSL d K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := d) (k := K)
      (by omega), Subgroup.mem_bot] at hzc
    exact hzc
  have hkerMap : ψ.ker ≤ (Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K)).map φ := by
    intro l hl
    obtain ⟨g, rfl⟩ := hφsurj l
    rw [MonoidHom.mem_ker, hφ g] at hl
    refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
    rw [← scalars_eq_center d K]
    exact proj_eq_one_iff.mp hl
  have hle : Subgroup.center L' ≤ (Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K)).map φ :=
    hZker.trans hkerMap
  have hdvd : Nat.card (Subgroup.center L') ∣ Nat.card K - 1 :=
    (Subgroup.card_dvd_of_le hle).trans <|
      (Subgroup.card_map_dvd
        (H := Subgroup.center (Matrix.SpecialLinearGroup (Fin d) K)) φ).trans <|
        card_center_specialLinear_dvd (K := K) (by omega)
  exact hpK (dvd_trans hpZ hdvd)

@[expose] def GGTableBNbrInnerLinearNsLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ 4 ≤ lab.rank ∧ p ≠ 2 ∧ ¬ p ∣ 2 ^ lab.n - 1

theorem ggTorusNbrSC_linearNs {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1) (hd : 5 ≤ d) :
    GGTorusNbrSC p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  have hpK0 : (p : K) ≠ 0 := fun h =>
    hp2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      ((CharP.cast_eq_zero_iff K 2 p).mp h)).symm)
  set e := TypeA.recipeEquiv d K with he
  refine ggTorusNbrSC_of_scWeylIrred hp
    (center_eq_bot_of_mulEquiv e (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot
      (by omega)))
    (fun φ hφ hφp => NbrInnerMore.ggOutdiagPrime_linear hp hpK (by omega) φ hφ hφp)
    (ggCenterPrime_of_mulEquiv e (ggCenterPrime_projectiveSL hp hpK hd))
    (ggSCWeylIrred_of_mulEquiv e (ggSCWeylIrred_projectiveSL hp hpK0 hpK (by omega)))

theorem largeEvenLabelAll_torusNbrSC_linearNs {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBNbrInnerLinearNsLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusNbrSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hp2, hq⟩ := h
  dsimp only at ht hl hp2 hq
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := NbrInnerMore.charP_two_of_card_pow hn hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggTorusNbrSC_linearNs (d := l + 1) hp hp2 (by rwa [hK]) (by omega)⟩

theorem ggTableBNbrInnerInputOn_linearNs : GGTableBNbrInnerInputOn GGTableBNbrInnerLinearNsLabel :=
  ggTableBNbrInnerInputOn_of_labelsSC fun _ _ hp hlab h =>
    largeEvenLabelAll_torusNbrSC_linearNs hp hlab h

end CFSG.StandardType

end
