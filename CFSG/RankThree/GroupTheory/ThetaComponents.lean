module

public import CFSG.RankThree.GroupTheory.SubnormalCores
import CFSG.RankThree.PerfectCover.SubnormalSolvableSupplement
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree

open CFSG CFSG.RankThree.LocalRank

@[expose] def thetaComponents (p : ℕ) (H : Type*) [Group H] : Set (Subgroup H) :=
  {L | Group.IsPerfect L ∧ L.IsSubnormal ∧ CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore p L)}

@[expose] def thetaComponentsAt (p : ℕ) {G : Type*} [Group G] (a : G) : Set (Subgroup G) :=
  (fun L => L.map (Subgroup.centralizer ({a} : Set G)).subtype) ''
    thetaComponents p (Subgroup.centralizer ({a} : Set G))

@[expose] def thetaComponentFamily (p : ℕ) {G : Type*} [Group G] (A : Subgroup G) :
    Set (Subgroup G) :=
  ⋃ a ∈ {a : G | a ∈ A ∧ a ≠ 1}, thetaComponentsAt p a

theorem exists_quotient_mulEquiv_map {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (L : Subgroup G) (M : Subgroup L) [M.Normal] (hM : ∀ l : L, l ∈ M ↔ f l = 1) :
    ∃ η : L ⧸ M ≃* L.map f, ∀ l : L, (η (l : L ⧸ M) : Q) = f l := by
  have hker : (f.subgroupMap L).ker = M := by
    ext l
    rw [MonoidHom.mem_ker, hM]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (f.subgroupMap_surjective L)), fun l => rfl⟩

theorem inSubgroup_perfectResidual_of_isPerfect {Q : Type*} [Group Q] [Finite Q]
    {R : Subgroup Q} (hR : Group.IsPerfect R) : inSubgroup perfectResidual R = R := by
  have htop : perfectResidual R = ⊤ := eq_top_iff.mpr
    ((perfect_residual_transport (MonoidHom.id R)).2.2 ⊤ (Group.IsPerfect.top_iff.mpr hR))
  rw [inSubgroup, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

variable {H : Type*} [Group H] [Finite H] {p : ℕ}

theorem aschbacherSolvableCore_eq_subgroupOf (hp : p.Prime) {L : Subgroup H}
    (hL : L.IsSubnormal) :
    aschbacherSolvableCore p L = (aschbacherSolvableCore p H).subgroupOf L := by
  apply Subgroup.map_injective L.subtype_injective
  have h := solvable_prime_complement_core_subnormal_intersection hp hL
  rw [inSubgroup] at h
  rw [h, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem exists_thetaQuotient_mulEquiv_map (hp : p.Prime) {L : Subgroup H} (hL : L.IsSubnormal) :
    ∃ η : (L ⧸ aschbacherSolvableCore p L) ≃*
        L.map (QuotientGroup.mk' (aschbacherSolvableCore p H)),
      ∀ l : L, (η (l : L ⧸ aschbacherSolvableCore p L) : H ⧸ aschbacherSolvableCore p H) =
        QuotientGroup.mk' (aschbacherSolvableCore p H) (l : H) :=
  exists_quotient_mulEquiv_map _ L _ fun l => by
    rw [aschbacherSolvableCore_eq_subgroupOf hp hL, Subgroup.mem_subgroupOf,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem isComponent_map_of_mem_thetaComponents (hp : p.Prime) {L : Subgroup H}
    (hL : L ∈ thetaComponents p H) :
    IsComponent (L.map (QuotientGroup.mk' (aschbacherSolvableCore p H))) := by
  obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map hp hL.2.1
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv η hL.2.2,
    hL.2.1.map (QuotientGroup.mk'_surjective _)⟩

theorem perfectResidual_comap_mem_thetaComponents (hp : p.Prime)
    {J : Subgroup (H ⧸ aschbacherSolvableCore p H)} (hJ : IsComponent J) :
    inSubgroup perfectResidual (J.comap (QuotientGroup.mk' (aschbacherSolvableCore p H))) ∈
        thetaComponents p H ∧
      (inSubgroup perfectResidual (J.comap (QuotientGroup.mk' (aschbacherSolvableCore p H)))).map
        (QuotientGroup.mk' (aschbacherSolvableCore p H)) = J := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore p H)
  set X := J.comap π
  obtain ⟨-, hchar, hperf, -⟩ := perfect_residual_characterization (G := X)
  have hPsn : (inSubgroup perfectResidual X).IsSubnormal :=
    (Subgroup.Normal.isSubnormal inferInstance).trans' (hJ.2.comap π)
  have hPperf : Group.IsPerfect (inSubgroup perfectResidual X) := Group.IsPerfect.map X.subtype
  have hrange : (π.comp X.subtype).range = J := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hPJ : (inSubgroup perfectResidual X).map π = J := by
    have h := (perfect_residual_transport (π.comp X.subtype)).1
    rw [inSubgroup, Subgroup.map_map, h, ← inSubgroup,
      inSubgroup_perfectResidual_of_isPerfect (hrange ▸ hJ.1.1), hrange]
  refine ⟨⟨hPperf, hPsn, ?_⟩, hPJ⟩
  obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map hp hPsn
  have hq : IsQuasisimple ((inSubgroup perfectResidual X).map π) := hPJ ▸ hJ.1
  exact LocalCores.isQuasisimple_of_mulEquiv η.symm hq

theorem perfectResidual_comap_map_of_mem_thetaComponents (hp : p.Prime) {L : Subgroup H}
    (hL : L ∈ thetaComponents p H) :
    inSubgroup perfectResidual ((L.map (QuotientGroup.mk' (aschbacherSolvableCore p H))).comap
      (QuotientGroup.mk' (aschbacherSolvableCore p H))) = L := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  set N := aschbacherSolvableCore p H
  have hLX : L ≤ L ⊔ N := le_sup_left
  have hNX : N ≤ L ⊔ N := le_sup_right
  have hNsol : Group.IsSolvable N := (solvable_prime_complement_core_characterization hp).1
  have hLperf : Group.IsPerfect (L.subgroupOf (L ⊔ N)) := by
    have := hL.1
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLX).symm.surjective
  have hNsol' : Group.IsSolvable (N.subgroupOf (L ⊔ N)) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hNX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNX).injective
  have hsup : L.subgroupOf (L ⊔ N) ⊔ N.subgroupOf (L ⊔ N) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLX hNX, Subgroup.subgroupOf_self]
  obtain ⟨-, hres⟩ := CFSG.RankThree.PerfectCover.perfect_subnormal_solvable_supplement_residual
    hLperf hL.2.1.subgroupOf Subgroup.normal_subgroupOf hNsol' hsup
  rw [inSubgroup, hres, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLX]

theorem theta_component_quotient_correspondence (hp : p.Prime) :
    Set.BijOn (fun L : Subgroup H => L.map (QuotientGroup.mk' (aschbacherSolvableCore p H)))
        (thetaComponents p H) {J | IsComponent J} ∧
      Set.InvOn (fun J : Subgroup (H ⧸ aschbacherSolvableCore p H) =>
          inSubgroup perfectResidual (J.comap (QuotientGroup.mk' (aschbacherSolvableCore p H))))
        (fun L : Subgroup H => L.map (QuotientGroup.mk' (aschbacherSolvableCore p H)))
        (thetaComponents p H) {J | IsComponent J} ∧
      Set.MapsTo (fun J : Subgroup (H ⧸ aschbacherSolvableCore p H) =>
          inSubgroup perfectResidual (J.comap (QuotientGroup.mk' (aschbacherSolvableCore p H))))
        {J | IsComponent J} (thetaComponents p H) := by
  have hinv : Set.InvOn (fun J : Subgroup (H ⧸ aschbacherSolvableCore p H) =>
      inSubgroup perfectResidual (J.comap (QuotientGroup.mk' (aschbacherSolvableCore p H))))
      (fun L : Subgroup H => L.map (QuotientGroup.mk' (aschbacherSolvableCore p H)))
      (thetaComponents p H) {J | IsComponent J} :=
    ⟨fun L hL => perfectResidual_comap_map_of_mem_thetaComponents hp hL,
      fun J hJ => (perfectResidual_comap_mem_thetaComponents hp hJ).2⟩
  have hmaps : Set.MapsTo (fun J : Subgroup (H ⧸ aschbacherSolvableCore p H) =>
      inSubgroup perfectResidual (J.comap (QuotientGroup.mk' (aschbacherSolvableCore p H))))
      {J | IsComponent J} (thetaComponents p H) :=
    fun J hJ => (perfectResidual_comap_mem_thetaComponents hp hJ).1
  exact ⟨hinv.bijOn (fun L hL => isComponent_map_of_mem_thetaComponents hp hL) hmaps, hinv,
    hmaps⟩

theorem map_mulEquiv_mem_thetaComponents {H' : Type*} [Group H'] (hp : p.Prime) (σ : H ≃* H')
    {L : Subgroup H} (hL : L ∈ thetaComponents p H) :
    L.map σ.toMonoidHom ∈ thetaComponents p H' := by
  set e := L.equivMapOfInjective σ.toMonoidHom σ.injective
  refine ⟨?_, hL.2.1.map σ.surjective, ?_⟩
  · have := hL.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · exact LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv hp e)) hL.2.2

theorem theta_component_quotient_correspondence_equivariant (hp : p.Prime) :
    (∀ σ : H ≃* H, ∃ τ : (H ⧸ aschbacherSolvableCore p H) ≃* (H ⧸ aschbacherSolvableCore p H),
      ∀ h : H, τ (QuotientGroup.mk' (aschbacherSolvableCore p H) h) =
        QuotientGroup.mk' (aschbacherSolvableCore p H) (σ h)) ∧
    ∀ (σ : H ≃* H) (τ : (H ⧸ aschbacherSolvableCore p H) ≃* (H ⧸ aschbacherSolvableCore p H)),
      (∀ h : H, τ (QuotientGroup.mk' (aschbacherSolvableCore p H) h) =
        QuotientGroup.mk' (aschbacherSolvableCore p H) (σ h)) →
      (∀ L ∈ thetaComponents p H, L.map σ.toMonoidHom ∈ thetaComponents p H ∧
        (L.map σ.toMonoidHom).map (QuotientGroup.mk' (aschbacherSolvableCore p H)) =
          (L.map (QuotientGroup.mk' (aschbacherSolvableCore p H))).map τ.toMonoidHom) ∧
      (∀ J : Subgroup (H ⧸ aschbacherSolvableCore p H), IsComponent J →
        IsComponent (J.map τ.toMonoidHom) ∧
        inSubgroup perfectResidual
            ((J.map τ.toMonoidHom).comap (QuotientGroup.mk' (aschbacherSolvableCore p H))) =
          (inSubgroup perfectResidual
            (J.comap (QuotientGroup.mk' (aschbacherSolvableCore p H)))).map σ.toMonoidHom) := by
  set N := aschbacherSolvableCore p H
  have hchar : N.Characteristic := (solvable_prime_complement_core_characterization hp).2.1
  refine ⟨fun σ => ⟨QuotientGroup.congr N N σ (Subgroup.characteristic_iff_map_eq.mp hchar σ),
    fun h => QuotientGroup.congr_mk' _ _ _ _ h⟩, fun σ τ hτ => ?_⟩
  have hcomp : (QuotientGroup.mk' N).comp σ.toMonoidHom = τ.toMonoidHom.comp
      (QuotientGroup.mk' N) := MonoidHom.ext fun h => (hτ h).symm
  have hmap : ∀ L ∈ thetaComponents p H, L.map σ.toMonoidHom ∈ thetaComponents p H ∧
      (L.map σ.toMonoidHom).map (QuotientGroup.mk' N) =
        (L.map (QuotientGroup.mk' N)).map τ.toMonoidHom := fun L hL =>
    ⟨map_mulEquiv_mem_thetaComponents hp σ hL, by rw [Subgroup.map_map, Subgroup.map_map, hcomp]⟩
  refine ⟨hmap, fun J hJ => ⟨LocalCores.isComponent_map_mulEquiv τ hJ, ?_⟩⟩
  obtain ⟨hL, hLJ⟩ := perfectResidual_comap_mem_thetaComponents hp hJ
  set L := inSubgroup perfectResidual (J.comap (QuotientGroup.mk' N))
  obtain ⟨hσL, hσLJ⟩ := hmap L hL
  rw [← hLJ, ← hσLJ]
  exact perfectResidual_comap_map_of_mem_thetaComponents hp hσL

theorem theta_component_inter_isSolvable (hp : p.Prime) {L₁ L₂ : Subgroup H}
    (hL₁ : L₁ ∈ thetaComponents p H) (hL₂ : L₂ ∈ thetaComponents p H) (hne : L₁ ≠ L₂) :
    Group.IsSolvable (L₁ ⊓ L₂ : Subgroup H) := by
  set N := aschbacherSolvableCore p H
  set π := QuotientGroup.mk' N
  obtain ⟨hbij, hinv, -⟩ := theta_component_quotient_correspondence (H := H) hp
  have hK₁ := isComponent_map_of_mem_thetaComponents hp hL₁
  have hK₂ := isComponent_map_of_mem_thetaComponents hp hL₂
  have hKne : L₁.map π ≠ L₂.map π := fun h => hne (hbij.injOn hL₁ hL₂ h)
  have hcomm := (LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hKne
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  set W : Subgroup H := L₁ ⊓ L₂
  have himage : ∀ w : W, π w ∈ L₁.map π ⊓ L₂.map π := fun w =>
    ⟨Subgroup.mem_map_of_mem π w.2.1, Subgroup.mem_map_of_mem π w.2.2⟩
  let g : W →* (L₁.map π ⊓ L₂.map π : Subgroup (H ⧸ N)) :=
    (π.comp W.subtype).codRestrict _ himage
  have hNsol : Group.IsSolvable N := (solvable_prime_complement_core_characterization hp).1
  have hcommIm : ∀ a b : (L₁.map π ⊓ L₂.map π : Subgroup (H ⧸ N)), a * b = b * a := by
    intro a b
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hcent a.2.1) b b.2.2).symm
  have : Group.IsSolvable (L₁.map π ⊓ L₂.map π : Subgroup (H ⧸ N)) :=
    Group.isSolvable_of_comm hcommIm
  have : Group.IsSolvable (W ⊓ N : Subgroup H) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_right)
      (Subgroup.inclusion_injective inf_le_right)
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (inf_le_left : W ⊓ N ≤ W)) g ?_
  intro w hw
  have hw' : π w = 1 := congrArg Subtype.val hw
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw'
  exact ⟨⟨w, w.2, hw'⟩, rfl⟩

theorem theta_component_eq_of_perfect_le (hp : p.Prime) {L₁ L₂ : Subgroup H}
    (hL₁ : L₁ ∈ thetaComponents p H) (hL₂ : L₂ ∈ thetaComponents p H) {P : Subgroup H}
    (hP : P ≠ ⊥) (hPperf : Group.IsPerfect P) (hP₁ : P ≤ L₁) (hP₂ : P ≤ L₂) : L₁ = L₂ := by
  by_contra hne
  have hW := theta_component_inter_isSolvable hp hL₁ hL₂ hne
  have hsol : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (le_inf hP₁ hP₂)) (Subgroup.inclusion_injective _)
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  have := hPperf
  exact Group.IsPerfect.not_isSolvable P hsol

end CFSG.RankThree
