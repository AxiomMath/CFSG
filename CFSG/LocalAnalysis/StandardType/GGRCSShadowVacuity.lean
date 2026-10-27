module

public import CFSG.LocalAnalysis.StandardType.GGRCSShadowBasic
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

private theorem ggShV_component_of_pCore_eq_bot {W : Type} [Group W] [Finite W]
    {H : Subgroup W}
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hU : CFSG.pCore 2 ↥(H ⊓ CFSG.generalizedFitting W) = ⊥) :
    ∃ C : Subgroup W, CFSG.Assembly.IsComponentOf C
      (H ⊓ CFSG.generalizedFitting W) := by
  classical
  let K : Subgroup W := CFSG.generalizedFitting W
  have hKn : K.Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
  let M : Subgroup ↥H := K.subgroupOf H
  let Q : Subgroup ↥H := CFSG.pCore 2 ↥H
  let π : ↥H →* GGHypQuot H := QuotientGroup.mk' Q
  have hπs : Function.Surjective π := by
    change Function.Surjective (QuotientGroup.mk' Q)
    exact QuotientGroup.mk'_surjective Q
  obtain ⟨Cbar, hCbar⟩ := ggExists_component_of_layer_ne_bot hL
  obtain ⟨k, hk⟩ := ggShadow_exists_derivedSeries_le (W := W) (H := H) hperf
  have hkM : derivedSeries ↥H k ≤ M := hk
  have hCbarM : Cbar ≤ M.map π := by
    have h1 : Cbar ≤ derivedSeries (GGHypQuot H) k :=
      ggLe_derivedSeries_of_perfect (ggComponent_perfect hCbar) k
    rw [← map_derivedSeries_eq hπs k] at h1
    exact h1.trans (Subgroup.map_mono hkM)
  have hMX : M.map H.subtype = H ⊓ K := by
    rw [inf_comm]
    exact Subgroup.subgroupOf_map_subtype K H
  let eMX : ↥M ≃* ↥(H ⊓ K) :=
    (Subgroup.equivMapOfInjective M H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hMX)
  have hMp : CFSG.pCore 2 ↥M = ⊥ := by
    have h := CFSG.pCore_map_iso 2 eMX
    change (CFSG.pCore 2 ↥M).map eMX.toMonoidHom =
      CFSG.pCore 2 ↥(H ⊓ CFSG.generalizedFitting W) at h
    rw [hU] at h
    have h' : CFSG.pCore 2 ↥M ≤ (eMX.toMonoidHom).ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact h
    rw [MonoidHom.ker_eq_bot eMX.toMonoidHom eMX.injective] at h'
    exact le_bot_iff.mp h'
  have hQp : IsPGroup 2 Q := CFSG.pCore_isPGroup (p := 2) (G := ↥H)
  have hQn : Q.Normal := CFSG.pCore_normal (p := 2) (G := ↥H)
  have hQMn : (Q.subgroupOf M).Normal := Subgroup.Normal.subgroupOf hQn M
  have hQpM : IsPGroup 2 (Q.subgroupOf M) := by
    rw [← Subgroup.comap_subtype]
    exact hQp.comap_of_injective M.subtype M.subtype_injective
  have hQM : Q.subgroupOf M ≤ CFSG.pCore 2 ↥M := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (Q.subgroupOf M)
      (le_iSup_of_le hQMn (le_iSup_of_le hQpM le_rfl))
  have hQMbot : Q.subgroupOf M = ⊥ := by
    rw [hMp] at hQM
    exact le_bot_iff.mp hQM
  let ρ : ↥M →* GGHypQuot H := π.comp M.subtype
  have hρker : ρ.ker = Q.subgroupOf M := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk' Q) (x : ↥H) = 1 ↔ (x : ↥H) ∈ Q
    exact QuotientGroup.eq_one_iff (N := Q) (x := (x : ↥H))
  have hρ : Function.Injective ρ :=
    (MonoidHom.ker_eq_bot_iff ρ).mp (by rw [hρker, hQMbot])
  let Mbar : Subgroup (GGHypQuot H) := M.map π
  have hCbarMbar : Cbar ≤ Mbar := hCbarM
  have hρr : ρ.range = Mbar := by
    change (π.comp M.subtype).range = M.map π
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eρ : ↥M ≃* ↥Mbar :=
    (MonoidHom.ofInjective hρ).trans (MulEquiv.subgroupCongr hρr)
  have hCbarComp : CFSG.Assembly.IsComponentOf Cbar Mbar :=
    CFSG.Assembly.IsComponentOf.of_le_of_le hCbar hCbarMbar le_top
  have hQtop : CFSG.Assembly.IsComponentOf (Cbar.subgroupOf Mbar) ⊤ := by
    refine (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := Mbar.subtype) Mbar.subtype_injective).mp ?_
    rw [Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hCbarMbar]
    exact hCbarComp
  have hCMtop : CFSG.Assembly.IsComponentOf
      ((Cbar.subgroupOf Mbar).map eρ.symm.toMonoidHom) ⊤ := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := eρ.symm.toMonoidHom) eρ.symm.injective).mpr hQtop
    simpa [Subgroup.map_top_of_surjective eρ.symm.toMonoidHom eρ.symm.surjective] using h
  have hD : CFSG.Assembly.IsComponentOf
      (((Cbar.subgroupOf Mbar).map eρ.symm.toMonoidHom).map M.subtype) M := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := M.subtype) M.subtype_injective).mpr hCMtop
    simpa [Subgroup.map_top, Subgroup.range_subtype] using h
  refine ⟨(((Cbar.subgroupOf Mbar).map eρ.symm.toMonoidHom).map M.subtype).map
    H.subtype, ?_⟩
  have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
    (f := H.subtype) H.subtype_injective).mpr hD
  rw [hMX] at h
  exact h

theorem ggShadow_vacuity {W : Type} [Group W] [Finite W] {p : ℕ} [Fact p.Prime] {H : Subgroup W}
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥)
    (hidx : ¬ p ∣ (H.subgroupOf (CFSG.generalizedFitting W)).index)
    (hnc : ∀ C : Subgroup W,
      ¬ CFSG.Assembly.IsComponentOf C (H ⊓ CFSG.generalizedFitting W)) :
    ∃ (S : Sylow p ↥(CFSG.generalizedFitting W)) (U : Subgroup ↥(CFSG.generalizedFitting W)),
      IsPGroup 2 ↥U ∧ U ≠ ⊥ ∧ (S : Subgroup ↥(CFSG.generalizedFitting W)) ≤
        Subgroup.normalizer (U : Set ↥(CFSG.generalizedFitting W)) := by
  classical
  let K : Subgroup W := CFSG.generalizedFitting W
  let X : Subgroup ↥K := H.subgroupOf K
  have hne : CFSG.pCore 2 ↥X ≠ ⊥ := by
    intro hbot
    have hUX : CFSG.pCore 2 ↥(H ⊓ CFSG.generalizedFitting W) = ⊥ := by
      let e : ↥X ≃* ↥(H ⊓ K) := ggSubgroupOfEquivInf H K
      have h := CFSG.pCore_map_iso 2 e
      rw [hbot, Subgroup.map_bot] at h
      exact h.symm
    obtain ⟨C, hC⟩ := ggShV_component_of_pCore_eq_bot (W := W) (H := H) hperf hL hUX
    exact hnc C hC
  let U0 : Subgroup ↥X := CFSG.pCore 2 ↥X
  let U : Subgroup ↥K := U0.map X.subtype
  have hUp : IsPGroup 2 ↥U := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype
  have hUne : U ≠ ⊥ := by
    intro h
    apply hne
    change U0.map X.subtype = ⊥ at h
    have hle : U0 ≤ X.subtype.ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact h
    rw [MonoidHom.ker_eq_bot X.subtype X.subtype_injective] at hle
    exact le_bot_iff.mp hle
  have hUnorm : X ≤ Subgroup.normalizer (U : Set ↥K) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer
      (show U ≤ X from Subgroup.map_subtype_le U0)]
    have hUsub : U.subgroupOf X = U0 := by
      change (U0.map X.subtype).subgroupOf X = U0
      rw [← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective U0
    rw [hUsub]
    exact CFSG.pCore_normal (p := 2) (G := ↥X)
  obtain ⟨S0 : Sylow p ↥X⟩ := Sylow.nonempty (p := p) (G := ↥X)
  let P : Subgroup ↥K := (S0 : Subgroup ↥X).map X.subtype
  have hPp : IsPGroup p ↥P :=
    IsPGroup.map (H := (S0 : Subgroup ↥X)) (K := ↥K) (Sylow.isPGroup' S0)
      (X.subtype : ↥X →* ↥K)
  have hPidx : ¬ p ∣ P.index := by
    change ¬ p ∣ ((S0 : Subgroup ↥X).map X.subtype).index
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul (Sylow.not_dvd_index S0) hidx
  let S : Sylow p ↥K := hPp.toSylow hPidx
  refine ⟨S, U, hUp, hUne, ?_⟩
  have hSP : (S : Subgroup ↥K) = P := IsPGroup.toSylow_coe hPp hPidx
  rw [hSP]
  exact (Subgroup.map_subtype_le (S0 : Subgroup ↥X)).trans hUnorm

end CFSG.StandardType
