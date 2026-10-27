module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
public import CFSG.LocalAnalysis.StandardType.GGKacExcB2
public import CFSG.LocalAnalysis.StandardType.GGK1CoverBij
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.RankThree.PartOne.SLBN.LocalBasic
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFam
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
public import CFSG.LocalAnalysis.StandardType.GGFamLabelIndex
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6TwoThree
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutQuot
public import CFSG.GroupTheory.CentralExtensionS3
public import CFSG.LocalAnalysis.StandardType.GGK0MarkedComponents
public import CFSG.LocalAnalysis.EvenSmallLie.GTwoFour.Outer
public import CFSG.RankThree.PartOne.SRC.RankOneAux

public section

namespace CFSG.StandardType.GGK0MarkedA12

open CFSG CFSG.Assembly CFSG.StandardType
open Subgroup
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem center_eq_bot_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi) : center R = ⊥ := by
  apply le_bot_iff.mp
  intro r hr
  have hrG : M.iota r ∈ M.setup.Γ := by
    rw [← M.iota_range]
    exact ⟨r, rfl⟩
  have hG : M.setup.Γ ≤ M.setup.D.model := Subgroup.commutator_le_self M.setup.D.model
  let g : M.setup.D.model := ⟨M.iota r, hG hrG⟩
  have hact : M.modelAction g = 1 := by
    ext x
    apply M.iota_inj
    rw [M.modelAction_compat]
    change M.iota r * M.iota x * (M.iota r)⁻¹ = M.iota x
    have hc : M.iota x * M.iota r = M.iota r * M.iota x := by
      simpa only [map_mul] using congrArg M.iota ((Subgroup.mem_center_iff.mp hr) x)
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hg : g = 1 := M.modelAction_inj (hact.trans (map_one M.modelAction).symm)
  have hir : M.iota r = 1 := congrArg Subtype.val hg
  exact mem_bot.mpr (M.iota_inj (hir.trans (map_one M.iota).symm))

theorem fullFactor_le_fix_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    (j : Fin M.row.D.orbits.length) :
    fullFactor M.setup M.iota M.a (M.repr j) ≤ ggFixSub phi := by
  let af : PUnit → Fin M.tau.rank → Omegaˣ := fun _ => M.a
  have hker := TableCRes.kernelRoots_famChar_punit_eq M.a
  obtain ⟨i, hi⟩ := TableCRes.exists_componentRoots_eq hker.symm (M.repr j)
  have hroot : TableCRes.famOrbit M.setup.ρ af i =
      rationalRoots M.setup.ρ (rootCharHom M.a) (M.repr j) := by
    unfold TableCRes.famOrbit rationalRoots
    rw [hi]
  have hc := TableCRes.rootSpan_rationalRoots_le_centralizer M.setup af i M.a_torus
    (fun γ hγ => by
      rw [← hi] at hγ
      exact hγ.1.2)
  rw [hroot] at hc
  intro r hr
  have hr' : M.iota r ∈ rationalSpan M.setup.ρ M.setup.Γ
      (rootCharHom M.a) (M.repr j) := hr
  have hcomm := hc hr'.1
  have hact := M.modelAction_compat ⟨CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit M.tau M.a, M.a_model⟩ r
  rw [M.action_eq] at hact
  apply mem_ggFixSub.mpr
  apply M.iota_inj
  rw [hact]
  have he : M.iota r * rootDiagUnit M.tau M.a = rootDiagUnit M.tau M.a * M.iota r :=
    Subgroup.mem_centralizer_singleton_iff.mp hcomm
  rw [← he, mul_assoc, mul_inv_cancel, mul_one]

theorem fullFactors_commute_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    {j k : Fin M.row.D.orbits.length} (hne : j ≠ k) :
    ∀ x ∈ fullFactor M.setup M.iota M.a (M.repr j),
      ∀ y ∈ fullFactor M.setup M.iota M.a (M.repr k), x * y = y * x := by
  have hker : ∀ γ ∈ kernelRoots (rootCharHom M.a), M.setup.ρ γ ∈ kernelRoots (rootCharHom M.a) := by
    intro γ hγ
    refine ⟨(M.setup.frob.isRoot_iff γ).mpr hγ.1, ?_⟩
    change rootChar M.a (M.setup.ρ γ) = 1
    rw [M.setup.frob.rootChar_eq M.a M.a_torus γ hγ.1]
    have he : rootChar M.a γ = 1 := hγ.2
    rw [he, one_pow]
  have hrootne : rationalRoots M.setup.ρ (rootCharHom M.a) (M.repr j) ≠
      rationalRoots M.setup.ρ (rootCharHom M.a) (M.repr k) := by
    intro he
    obtain ⟨γ, hγ⟩ := TableCRes.tc_componentRoots_nonempty (M.repr j)
    have hj : γ ∈ rationalRoots M.setup.ρ (rootCharHom M.a) (M.repr j) := ⟨0, γ, hγ, rfl⟩
    exact Set.disjoint_left.mp (M.orbit_distinct j k hne) hj (he ▸ hj)
  have hc := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.commute_rootSpan_rationalRoots
    hker M.setup.frob.iform_eq hrootne
  intro x hx y hy
  apply M.iota_inj
  simp only [map_mul]
  exact (hc (M.iota x) hx.1 (M.iota y) hy.1).eq

theorem a12_fullFactor_commutes_components
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi) (hp : p.Prime) (hp2 : p ≠ 2)
    (j : Fin M.row.D.orbits.length) (hqs : M.row.D.orbits[j].qs = false) :
    ∀ J : Subgroup R, IsComponentOf J (ggFixSub phi) →
      ∀ s ∈ fullFactor M.setup M.iota M.a (M.repr j), ∀ t ∈ J, s * t = t * s := by
  have htau : M.tau ≠ .G2 := by
    rw [← M.tau_eq]
    cases M.row.T <;> simp [absTag]
  intro J hJ s hs t ht
  obtain ⟨k, hk, hpos⟩ :=
    CFSG.StandardType.GGK0MarkedComponents.exists_component_position_of_realization
      hp hp2 M htau hJ
  have hne : j ≠ k := by
    intro h
    subst k
    rw [hk] at hqs
    contradiction
  have htle : coreFactor M.setup M.iota M.a (M.repr k) ≤
      fullFactor M.setup M.iota M.a (M.repr k) :=
    Subgroup.comap_mono (Subgroup.commutator_le_self _)
  exact fullFactors_commute_of_realization M hne s hs t (htle (hpos ▸ ht))

theorem fixed_preimage_map_eq
    {L R : Type} [Group L] [Group R] (psi : L →* R)
    (e u : MulAut L) (phi v : MulAut R)
    (hu : Commute u e) (hInd : ∀ l, v (psi l) = psi (u l))
    (F : Subgroup R) (hF : F.map v.toMonoidHom = F) :
    ((F.comap psi) ⊓ ggFixSub e).map u.toMonoidHom = (F.comap psi) ⊓ ggFixSub e := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · change psi (u x) ∈ F
      rw [← hInd]
      rw [← hF]
      exact Subgroup.mem_map_of_mem v.toMonoidHom hx.1
    · apply mem_ggFixSub.mpr
      have heq : e (u x) = u (e x) := by
        have h := congrArg (fun f : MulAut L => f x) hu.eq
        exact h.symm
      change e (u x) = u x
      rw [heq, mem_ggFixSub.mp hx.2]
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨u⁻¹ x, ?_, by simp⟩
    refine ⟨?_, ?_⟩
    · have hxF : psi x ∈ F.map v.toMonoidHom := by
        change psi x ∈ F.map v.toMonoidHom
        rw [hF]
        exact hx.1
      obtain ⟨y, hy, hey⟩ := hxF
      have hpre : psi (u⁻¹ x) = y := by
        apply v.injective
        rw [hInd]
        change psi (u (u⁻¹ x)) = v y
        rw [show u (u⁻¹ x) = x from u.apply_symm_apply x]
        exact hey.symm
      change psi (u⁻¹ x) ∈ F
      rw [hpre]
      exact hy
    · apply mem_ggFixSub.mpr
      have heq : e (u⁻¹ x) = u⁻¹ (e x) := by
        have h := congrArg (fun f : MulAut L => f x) (hu.inv_left.eq)
        exact h.symm
      change e (u⁻¹ x) = u⁻¹ x
      rw [heq, mem_ggFixSub.mp hx.2]

theorem a12_fullFactor_commutes_component_images
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R L : Type} [Group R] [Group L]
    {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi) (hp : p.Prime) (hp2 : p ≠ 2)
    (j : Fin M.row.D.orbits.length) (hqs : M.row.D.orbits[j].qs = false)
    (psi : L →* R) (hpsi : Function.Surjective psi) (hker : psi.ker ≤ center L)
    (e : MulAut L) (hInd : ∀ l, phi (psi l) = psi (e l))
    (J : Subgroup L) (hJ : IsComponentOf J (ggFixSub e)) :
    ∀ s ∈ (fullFactor M.setup M.iota M.a (M.repr j)).comap psi,
      ∀ t ∈ J, s * t = t * s := by
  have hJmap : IsComponentOf (J.map psi) (ggFixSub phi) :=
    USixTwo.isComponentOf_map_fix hpsi hker hInd hJ
  have hcomm := a12_fullFactor_commutes_components M hp hp2 j hqs (J.map psi) hJmap
  have hpJ : ⁅J, J⁆ = J := by
    rw [← Subgroup.map_subtype_commutator J, hJ.2.2.1,
      Subgroup.map_top, Subgroup.range_subtype]
  have hc : ⁅J, (fullFactor M.setup M.iota M.a (M.repr j)).comap psi⁆ ≤ center L := by
    rw [Subgroup.commutator_le]
    intro t ht s hs
    apply hker
    change psi (t * s * t⁻¹ * s⁻¹) = 1
    simp only [map_mul, map_inv]
    have he := hcomm (psi s) hs (psi t) (Subgroup.mem_map_of_mem psi ht)
    rw [← he]
    group
  have hbot := CFSG.RankThree.PartOne.SLBN.commute_of_commutator_le_center hpJ hc
  intro s hs t ht
  exact (hbot t ht s hs).symm

theorem a12_fixed_preimage_derived
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R L : Type} [Group R] [Group L] [Finite L]
    {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    (hn : 1 ≤ lab.n) (hp : p.Prime) (hd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
    (j : Fin M.row.D.orbits.length) (hj : M.row.D.orbits[j].lab = ⟨.A, 1, 1⟩)
    (hqs : M.row.D.orbits[j].qs = false)
    (psi : L →* R) (hpsi : Function.Surjective psi) (hker : psi.ker ≤ center L)
    (e : MulAut L) (he : orderOf e = p) (hInd : ∀ l, phi (psi l) = psi (e l)) :
    let F := fullFactor M.setup M.iota M.a (M.repr j);
    let S := F.comap psi ⊓ ggFixSub e;
    Nat.card (commutator S) = 3 ∧ ¬ commutator S ≤ center S := by
  dsimp only
  let F := fullFactor M.setup M.iota M.a (M.repr j)
  let P := F.comap psi
  obtain ⟨theta⟩ := M.a12_model j hj hqs
  have hp3 : p = 3 := (ggKacValid_qs_false_p3 hn hp hd M.row.valid
    (List.getElem_mem j.2) hqs).2
  have hf : ∀ x : P, phi (psi x) = psi x := fun x =>
    mem_ggFixSub.mp (fullFactor_le_fix_of_realization M j x.2)
  have heP : ∀ x : P, e x ∈ P := by
    intro x
    change psi (e x) ∈ F
    rw [← hInd, hf]
    exact x.2
  have hePinv : ∀ x : P, e⁻¹ x ∈ P := by
    intro x
    change psi (e⁻¹ x) ∈ F
    have heq : phi (psi (e⁻¹ x)) = psi x := by
      rw [hInd]
      exact congrArg psi (e.apply_symm_apply x)
    have hback : phi⁻¹ (psi x) = psi x := by
      apply phi.injective
      simp only [MulAut.apply_inv_self]
      exact (hf x).symm
    have hpre : psi (e⁻¹ x) = psi x := by
      apply phi.injective
      rw [heq, hf]
    exact hpre ▸ x.2
  let alpha : MulAut P :=
    (e.subgroupMap P).trans (MulEquiv.subgroupCongr (by
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨x, hx, rfl⟩
        exact heP ⟨x, hx⟩
      · rw [Subgroup.card_map_of_injective e.injective]))
  have ha : ∀ x : P, (alpha x : L) = e x := fun _ => rfl
  have ha3 : alpha ^ 3 = 1 := by
    have he3 : e ^ 3 = 1 := by rw [← hp3, ← he]; exact pow_orderOf_eq_one e
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    have h := congrArg (fun f : MulAut L => f x) he3
    change e (e (e x)) = x at h
    change ((alpha ^ 3) x : L) = (x : L)
    have hh : ((alpha ^ 3) x : L) = e (e (e x)) := by
      change (alpha (alpha (alpha x)) : L) = e (e (e x))
      rw [ha, ha, ha]
    exact hh.trans h
  let f : P →* F :=
    { toFun := fun x => ⟨psi x, x.2⟩
      map_one' := Subtype.ext (map_one psi)
      map_mul' := fun x y => Subtype.ext (map_mul psi (x : L) (y : L)) }
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hpsi y
    exact ⟨⟨x, by change psi x ∈ F; rw [hx]; exact y.2⟩, Subtype.ext hx⟩
  let pi := theta.toMonoidHom.comp f
  have hpi : Function.Surjective pi := theta.surjective.comp hfs
  have hpic : pi.ker ≤ center P := by
    intro x hx
    have hpix : psi x = 1 := by
      have h : theta (f x) = theta 1 := by
        change theta (f x) = 1 at hx
        simpa only [map_one] using hx
      have hf1 := theta.injective h
      exact congrArg Subtype.val hf1
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hker hpix) y)
  have hpifix : ∀ x : P, pi (alpha x) = pi x := by
    intro x
    apply congrArg theta
    apply Subtype.ext
    change psi (alpha x) = psi x
    rw [ha, ← hInd, hf]
  have hC := CFSG.GroupTheory.CentralExtensionS3.fixed_subgroup_card_commutator_and_not_central
    pi hpi hpic alpha ha3 hpifix
  let C := MonoidHom.eqLocus alpha.toMonoidHom (MonoidHom.id P)
  let S := P ⊓ ggFixSub e
  let equiv : C ≃* S :=
    { toFun := fun x => ⟨x, x.1.2, by
        apply mem_ggFixSub.mpr
        exact congrArg Subtype.val x.2⟩
      invFun := fun x => ⟨⟨x, x.2.1⟩, by
        apply Subtype.ext
        exact mem_ggFixSub.mp x.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_mul' := fun x y => rfl }
  have hdEquiv : commutator C ≃* commutator S :=
    (Subgroup.equivMapOfInjective _ equiv.toMonoidHom equiv.injective).trans
      (MulEquiv.subgroupCongr (by rw [map_commutator_eq, MonoidHom.range_eq_top.mpr equiv.surjective]; rfl))
  refine ⟨Nat.card_congr hdEquiv.toEquiv |>.symm.trans hC.1, ?_⟩
  intro hcentral
  apply hC.2
  intro x hx
  have hmap : equiv x ∈ commutator S := by
    have heq : (commutator C).map equiv.toMonoidHom = commutator S := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr equiv.surjective]
      rfl
    rw [← heq]
    exact Subgroup.mem_map_of_mem equiv.toMonoidHom hx
  have hc := mem_center_iff.mp (hcentral hmap)
  rw [mem_center_iff]
  intro y
  apply equiv.injective
  simpa only [map_mul] using hc (equiv y)

theorem a12_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R L : Type} [Group R] [Group L] [Finite L]
    {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    (hn : 1 ≤ lab.n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)
    (psi : L →* R) (hpsi : Function.Surjective psi) (hker : psi.ker ≤ center L)
    (e : MulAut L) (he : orderOf e = p) (hInd : ∀ l, phi (psi l) = psi (e l)) :
    GGKacA12Comp M.row.D L e := by
  intro j hj hqs
  let F := fullFactor M.setup M.iota M.a (M.repr j)
  let S := F.comap psi ⊓ ggFixSub e
  have hZ : psi.ker = center L := by
    apply le_antisymm hker
    intro x hx
    have hmap : psi x ∈ (center L).map psi := Subgroup.mem_map_of_mem psi hx
    have hc := Subgroup.map_center_le_center hpsi hmap
    rw [center_eq_bot_of_realization M] at hc
    exact mem_bot.mp hc
  let descend := CFSG.EvenSporadicStandard.TwoFi22.DS81.AutQuot.inducedAut psi hpsi hZ
  have hde : descend e = phi := by
    apply MulEquiv.ext
    intro r
    obtain ⟨l, rfl⟩ := hpsi r
    exact (CFSG.EvenSporadicStandard.TwoFi22.DS81.AutQuot.inducedAut_apply psi hpsi hZ e l).trans
      (hInd l).symm
  have hind : ∀ u : MulAut L, ∀ l,
      descend u (psi l) = psi (u l) :=
    CFSG.EvenSporadicStandard.TwoFi22.DS81.AutQuot.inducedAut_apply psi hpsi hZ
  obtain ⟨hcard, hnon⟩ := a12_fixed_preimage_derived M hn hp hd j hj hqs
    psi hpsi hker e he hInd
  refine ⟨S, inf_le_right, ?_, ?_, hcard, hnon⟩
  · intro J hJ s hs t ht
    exact a12_fullFactor_commutes_component_images M hp hp2 j hqs psi hpsi hker e hInd J hJ s hs.1 t ht
  · intro u hu
    have hcomm : Commute u e := hu
    have hv : Commute (descend u) phi := by
      have hv := hcomm.map descend
      simpa only [hde] using hv
    have hF : F.map (descend u).toMonoidHom = F := M.a12_invariant j hj hqs (descend u) hv
    exact fixed_preimage_map_eq psi e u phi (descend u) hcomm (hind u) F hF

theorem a12_of_excPair
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R L : Type} [Group R] [Group L] [Finite L]
    {I : Set (MulAut R)} {phi : MulAut R}
    (hl : LargeEvenInLambda2 lab) (hp : GGKacExcPair lab p)
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    (psi : L →* R) (hpsi : Function.Surjective psi) (hker : psi.ker ≤ center L)
    (e : MulAut L) (he : orderOf e = p) (hInd : ∀ l, phi (psi l) = psi (e l)) :
    GGKacA12Comp M.row.D L e :=
  a12_of_realization M hl.1 hp.1 hp.2.1 hp.2.2.1 psi hpsi hker e he hInd

end CFSG.StandardType.GGK0MarkedA12
