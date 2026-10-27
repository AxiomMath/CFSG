module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitPairGeneration
import CFSG.RankThree.PartOne.KC.OrthogonalPerfectAnchor

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.Timmesfeld.ClassicalOrders
  CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

private theorem pair_eq_sup_singletons_of_range_coherent_split_charts
    {G F : Type} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 4 ≤ Nat.card F)
    (a : ∀ i : Fin 4,
      chartSubgroup (n := 5) (F := F) (b := b) (c := c) (Finset.univ.erase i) →* G)
    (R : Finset (Fin 4) → Subgroup G)
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 4)), S.Nonempty → S.card ≤ 2 →
      S ⊆ Finset.univ.erase i →
      ((chartSubgroup (n := 5) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := 5) (F := F) (b := b) (c := c) (Finset.univ.erase i))).map
          (a i) = R S)
    (i0 i1 j0 j1 : Fin 4) (hjj : j0 ≠ j1)
    (hdisj : Disjoint ({i0, i1} : Finset (Fin 4)) {j0, j1}) :
    R {j0, j1} = R {j0} ⊔ R {j1} := by
  classical
  let Q := quadMinus 5 F b c
  let Ω := orthDerived Q
  have hsub (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∉ S) :
      S ⊆ Finset.univ.erase i := by
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro heq
    subst x
    exact hi hx
  have hPsub : ({j0, j1} : Finset (Fin 4)) ⊆ Finset.univ.erase i0 := by
    apply hsub
    intro h
    exact Finset.disjoint_left.mp hdisj (by simp) h
  have hj0sub : ({j0} : Finset (Fin 4)) ⊆ Finset.univ.erase i0 :=
    (by simp : ({j0} : Finset (Fin 4)) ⊆ {j0, j1}).trans hPsub
  have hj1sub : ({j1} : Finset (Fin 4)) ⊆ Finset.univ.erase i0 :=
    (by simp : ({j1} : Finset (Fin 4)) ⊆ {j0, j1}).trans hPsub
  have hj0le := chartSubgroup_mono (n := 5) (F := F) (b := b) (c := c) hirr hj0sub
  have hj1le := chartSubgroup_mono (n := 5) (F := F) (b := b) (c := c) hirr hj1sub
  have hpgen := chartSubgroup_pair_eq_sup_singletons (r := 3) hcard hirr j0 j1 hjj
  have heq := congrArg
    (fun T : Subgroup Ω => (T.subgroupOf (chartSubgroup (n := 5) (F := F)
      (b := b) (c := c) (Finset.univ.erase i0))).map (a i0)) hpgen
  rw [Subgroup.subgroupOf_sup hj0le hj1le, Subgroup.map_sup,
    hR i0 {j0, j1} (by simp) (by simp [hjj]) hPsub,
    hR i0 {j0} (by simp) (by simp) hj0sub,
    hR i0 {j1} (by simp) (by simp) hj1sub] at heq
  exact heq

theorem pairResidual_commute_of_range_coherent_split_charts
    {G F : Type} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 4 ≤ Nat.card F)
    (a : ∀ i : Fin 4,
      chartSubgroup (n := 5) (F := F) (b := b) (c := c) (Finset.univ.erase i) →* G)
    (ha : ∀ i, Function.Injective (a i)) (R : Finset (Fin 4) → Subgroup G)
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 4)), S.Nonempty → S.card ≤ 2 →
      S ⊆ Finset.univ.erase i →
      ((chartSubgroup (n := 5) (F := F) (b := b) (c := c) S).subgroupOf
        (chartSubgroup (n := 5) (F := F) (b := b) (c := c) (Finset.univ.erase i))).map
          (a i) = R S)
    (i0 i1 j0 j1 : Fin 4) (hij : i0 ≠ i1) (hjj : j0 ≠ j1)
    (hdisj : Disjoint ({i0, i1} : Finset (Fin 4)) {j0, j1}) :
    ∀ g ∈ inSubgroup perfectResidual
        (R {i0, i1} ⊓ Subgroup.centralizer ((R {i0} ⊓ R {i1} : Subgroup G) : Set G)),
      ∀ h ∈ R {j0, j1}, Commute g h := by
  classical
  let Q := quadMinus 5 F b c
  let Ω := orthDerived Q
  let ψ := minusPlaneCoordinates (n := 5) (F := F)
  let W := coordAnchor ψ
  let U : Fin 4 → Submodule F (Vm 5 F) := coordPlane ψ
  let C : Finset (Fin 4) → Subgroup Ω :=
    chartSubgroup (n := 5) (F := F) (b := b) (c := c)
  let X : Subgroup G := R {i0, i1} ⊓ Subgroup.centralizer ((R {i0} ⊓ R {i1} : Subgroup G) : Set G)
  let P := inSubgroup perfectResidual X
  have : Group.IsPerfect (perfectResidual X) :=
    (perfect_residual_characterization (G := ↥X)).2.2.1
  have : Group.IsPerfect P := Group.IsPerfect.map X.subtype
  have hP : P ≤ R {i0, i1} ⊓ Subgroup.centralizer ((R {i0} ⊓ R {i1} : Subgroup G) : Set G) := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hQ : (polarBilin Q).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 5 F hirr
  have hQE : (polarBilin (hypPlane F)).Nondegenerate := hypPlane_polarBilin_nondegenerate
  have hψ : ∀ v : Vm 5 F,
      Q v = binaryForm F b c (ψ v).1 + ∑ i, hypPlane F ((ψ v).2 i) :=
    fun v => quadMinus_eq_binaryForm_add_minusPlaneCoordinates 3 v
  have hW : (polarBilin (Q.comp W.subtype)).Nondegenerate :=
    coordAnchor_nondegenerate ψ hψ hQ hQE
  have hWdim : finrank F W = 2 := by
    have hinj : Function.Injective
        (ψ.symm.toLinearMap.comp (LinearMap.inl F (Fin 2 → F) (Fin 4 → F × F))) :=
      ψ.symm.injective.comp LinearMap.inl_injective
    have hd : finrank F W = finrank F (Fin 2 → F) := LinearMap.finrank_range_of_inj hinj
    rw [hd, Module.finrank_fintype_fun_eq_card]
    simp
  have hU (i : Fin 4) : (polarBilin (Q.comp (U i).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn (coordPlane_polarNondegOn ψ hψ hQE i)
  have hWU (i : Fin 4) : ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0 :=
    fun w hw u hu => polar_coordAnchor_plane ψ hψ hw hu
  have hUU (i j : Fin 4) (hij : i ≠ j) : ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0 :=
    fun u hu v hv => polar_coordPlane_plane ψ hψ hij hu hv
  have hA : (polarBilin (Q.comp (U i0 ⊔ U i1).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup
        (polarNondegOn_of_nondegenerate (hU i0)) (polarNondegOn_of_nondegenerate (hU i1))
        (hUU i0 i1 hij))
  have hWA : ∀ w ∈ W, ∀ x ∈ U i0 ⊔ U i1, polar Q w x = 0 := by
    intro w hw x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    rw [polar_add_right, hWU i0 w hw u hu, hWU i1 w hw v hv, add_zero]
  have hWspace : anchoredSupport F 5 ∅ = W := coordAnchor_minusPlaneCoordinates.symm
  have hAspace : anchoredSupport F 5 {i0, i1} = W ⊔ (U i0 ⊔ U i1) := by
    simpa [coordSupport] using
      (coordSupport_minusPlaneCoordinates_eq_anchoredSupport (n := 5) (F := F) {i0, i1}).symm
  have hBspace (k : Fin 4) : anchoredSupport F 5 {k} = W ⊔ U k := by
    simpa [coordSupport] using
      (coordSupport_minusPlaneCoordinates_eq_anchoredSupport (n := 5) (F := F) {k}).symm
  have hone (d k : Fin 4) (hd : d ∉ ({i0, i1} : Finset (Fin 4)))
      (hk : k ≠ i0 ∧ k ≠ i1) (hkd : k ≠ d) :
      ∀ g ∈ P, ∀ h ∈ R {k}, Commute g h := by
    let D := Finset.univ.erase d
    let ρ : C D →* ((Vm 5 F) ≃ₗ[F] (Vm 5 F)) := Ω.subtype.comp (C D).subtype
    have hρ : Function.Injective ρ := Ω.subtype_injective.comp (C D).subtype_injective
    have hsub (S : Finset (Fin 4)) (hs : d ∉ S) : S ⊆ D := by
      intro x hx
      simp only [D, Finset.mem_erase, Finset.mem_univ, and_true]
      intro heq
      subst x
      exact hs hx
    have hrep (S : Finset (Fin 4)) (hS : S ⊆ D) :
        ((C S).subgroupOf (C D)).map ρ = supportedDerived Q (anchoredSupport F 5 S) := by
      have hle := chartSubgroup_mono (n := 5) (F := F) (b := b) (c := c) hirr hS
      have hsd := supportedDerived_le_orthDerived_of_regular
        (CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
          (polarNondegOn_anchoredSupport (n := 5) (F := F) (b := b) (c := c) hirr S))
      dsimp only [ρ]
      rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hle,
        Subgroup.map_subgroupOf_eq_of_le hsd]
    let CW := (C ∅).subgroupOf (C D)
    let CA := (C {i0, i1}).subgroupOf (C D)
    let CB := (C {k}).subgroupOf (C D)
    have hCW : CW.map ρ = supportedDerived Q W := by
      simpa only [CW, hWspace] using hrep ∅ (Finset.empty_subset _)
    have hCA : CA.map ρ = supportedDerived Q (W ⊔ (U i0 ⊔ U i1)) := by
      simpa only [CA, hAspace] using hrep {i0, i1} (hsub _ hd)
    have hCB : CB.map ρ = supportedDerived Q (W ⊔ U k) := by
      simpa only [CB, hBspace] using hrep {k} (hsub _ (by simpa using hkd.symm))
    have hactualA : CA.map (a d) = R {i0, i1} := hR d _ (by simp) (by simp [hij]) (hsub _ hd)
    have hactualB : CB.map (a d) = R {k} :=
      hR d _ (by simp) (by simp) (hsub _ (by simpa using hkd.symm))
    have hAnchor : CW.map (a d) ≤ R {i0} ⊓ R {i1} := by
      apply le_inf
      · have hmono := chartSubgroup_mono (n := 5) (F := F) (b := b) (c := c)
          hirr (Finset.empty_subset ({i0} : Finset (Fin 4)))
        have hm := Subgroup.map_mono (f := a d)
          (show CW ≤ (C {i0}).subgroupOf (C D) from fun x hx => hmono hx)
        have hd0 : d ∉ ({i0} : Finset (Fin 4)) := by
          intro h
          exact hd (Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h)))
        rw [hR d {i0} (by simp) (by simp) (hsub _ hd0)] at hm
        exact hm
      · have hmono := chartSubgroup_mono (n := 5) (F := F) (b := b) (c := c)
          hirr (Finset.empty_subset ({i1} : Finset (Fin 4)))
        have hm := Subgroup.map_mono (f := a d)
          (show CW ≤ (C {i1}).subgroupOf (C D) from fun x hx => hmono hx)
        have hd1 : d ∉ ({i1} : Finset (Fin 4)) := fun h => hd (Finset.mem_insert.mpr (Or.inr h))
        rw [hR d {i1} (by simp) (by simp) (hsub _ hd1)] at hm
        exact hm
    have hAB : ∀ x ∈ U i0 ⊔ U i1, ∀ y ∈ U k, polar Q x y = 0 := by
      intro x hx y hy
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
      rw [polar_add_left, hUU i0 k hk.1.symm u hu y hy,
        hUU i1 k hk.2.symm v hv y hy, add_zero]
    have hPlocal : P ≤ CA.map (a d) := by
      rw [hactualA]
      exact hP.trans inf_le_left
    have hc : ∀ g ∈ P, ∀ x ∈ CW.map (a d), Commute g x := by
      intro g hg x hx
      exact (Subgroup.mem_centralizer_iff.mp (hP hg).2 x (hAnchor hx)).symm
    have hb := represented_map_commute_of_perfect_centralizer_anchor ρ hρ (a d) (ha d)
      hW hWdim (by omega) hA (hU k) hWA (hWU k) hAB CW CA CB hCW hCA hCB P hPlocal hc
    rw [hactualB] at hb
    exact hb
  have hj0 : j0 ∉ ({i0, i1} : Finset (Fin 4)) := by
    intro h
    exact Finset.disjoint_left.mp hdisj h (by simp)
  have hj1 : j1 ∉ ({i0, i1} : Finset (Fin 4)) := by
    intro h
    exact Finset.disjoint_left.mp hdisj h (by simp)
  have hk0 : j0 ≠ i0 ∧ j0 ≠ i1 := by simpa using hj0
  have hk1 : j1 ≠ i0 ∧ j1 ≠ i1 := by simpa using hj1
  have htwo := hone j1 j0 hj1 hk0 hjj
  have hthree := hone j0 j1 hj0 hk1 hjj.symm
  have hgen := pair_eq_sup_singletons_of_range_coherent_split_charts hirr hcard a R hR
    i0 i1 j0 j1 hjj hdisj
  intro g hg h hh
  have hl2 : R {j0} ≤ Subgroup.centralizer ({g} : Set G) := by
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (htwo g hg x hx).eq
  have hl3 : R {j1} ≤ Subgroup.centralizer ({g} : Set G) := by
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (hthree g hg x hx).eq
  have hl : R {j0, j1} ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [hgen]
    exact sup_le hl2 hl3
  exact Subgroup.mem_centralizer_iff.mp (hl hh) g (Set.mem_singleton g)

end CFSG.RankThree.PartOne.KCOrthogonal

end
