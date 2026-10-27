module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutGraphTwE6
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem irgT6_neg_mem_roots {K : Type*} [Group K] (D : UniversalRootDatum K)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) : -γ ∈ D.roots := by
  simp only [UniversalRootDatum.roots, CFSG.LieType.RootSystem.roots, Set.mem_union,
    Set.mem_setOf_eq] at hγ ⊢
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · left
    refine ⟨w * (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i, i, ?_⟩
    rw [weylAction_mul_apply, weylAction_simple_single, map_neg]
  · right
    refine ⟨w * (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i, i, hi, ?_⟩
    rw [weylAction_mul_apply, weylAction_simple_single, map_neg, smul_neg]

private theorem irgT6_ggRootSub_eq {U G : Type*} [Group U] [Group G]
    (Δ : UniversalRootDatum U) (φ : U →* G) (γ : Fin Δ.rank → ℤ) (u : U) :
    ggRootSub Δ φ γ u = (Δ.rootGroup γ |>.map φ).map (MulAut.conj (φ u)).toMonoidHom := by
  have hcomp : φ.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (φ u)).toMonoidHom.comp φ := by
    ext z
    show φ (u * z * u⁻¹) = φ u * φ z * (φ u)⁻¹
    rw [map_mul, map_mul, map_inv]
  rw [ggRootSub]
  conv_lhs => rw [Subgroup.map_map]
  conv_rhs => rw [Subgroup.map_map]
  rw [hcomp]

private theorem irgT6_map_mul {G : Type*} [Group G] (S : Subgroup G) (f g : MulAut G) :
    S.map (f * g).toMonoidHom = (S.map g.toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem irgT6_map_conj_conj {G : Type*} [Group G] (S : Subgroup G) (a w : G) :
    (S.map (MulAut.conj w).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      S.map (MulAut.conj (a * w)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  show a * (w * z * w⁻¹) * a⁻¹ = a * w * z * (a * w)⁻¹
  group

private theorem irgT6_map_conj_map {G : Type*} [Group G] (S : Subgroup G) (w : G) (α : MulAut G) :
    (S.map (MulAut.conj w).toMonoidHom).map α.toMonoidHom =
      (S.map α.toMonoidHom).map (MulAut.conj (α w)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext z
  show α (w * z * w⁻¹) = α w * α z * (α w)⁻¹
  rw [map_mul, map_mul, map_inv]

private theorem irgT6_map_map_eq_of {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (θ : MulAut G) (α : MulAut H) (h : ∀ x, α (e x) = e (θ x)) {R : Subgroup G} :
    (R.map θ.toMonoidHom).map e.toMonoidHom = (R.map e.toMonoidHom).map α.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  exact (h x).symm

private theorem irgT6_map_eq_of_map_le {G : Type*} [Group G] (S : Subgroup G) {f g : MulAut G}
    (hfg : f * g = 1) (hf : S.map f.toMonoidHom ≤ S) (hg : S.map g.toMonoidHom ≤ S) :
    S.map f.toMonoidHom = S := by
  apply le_antisymm hf
  intro s hs
  refine ⟨g s, hg ⟨s, hs, rfl⟩, ?_⟩
  have h := congrArg (fun e : MulAut G => e s) hfg
  simpa using h

private theorem irgT6_bridge {U Q H : Type*} [Group U] [Group Q] [Group H]
    (D : UniversalRootDatum U) (q : U →* Q) (π : U →* H) (e : Q ≃* H)
    (he : ∀ y, e (q y) = π y) (γ : Fin D.rank → ℤ) (u₀ : U) :
    (ggRootSub D q γ u₀).map e.toMonoidHom = ggRootSub D π γ u₀ := by
  have hqc : e.toMonoidHom.comp q = π := MonoidHom.ext fun y => he y
  simp only [ggRootSub]
  rw [Subgroup.map_map, hqc]

private theorem irgT6_one_root {U Q H : Type*} [Group U] [Group Q] [Group H]
    (D : UniversalRootDatum U) (q : U →* Q) (π : U →* H) (e : Q ≃* H)
    (he : ∀ y, e (q y) = π y) (θ : MulAut Q) (α : MulAut H) (hα : ∀ x, α (e x) = e (θ x))
    (ginner : H) (γ : Fin D.rank → ℤ)
    (hpres : ((D.rootGroup γ).map π).map α.toMonoidHom =
      ((D.rootGroup γ).map π).map (MulAut.conj ginner).toMonoidHom)
    (u' u : U) (hu : π u = α (π u') * ginner) :
    (ggRootSub D q γ u').map θ.toMonoidHom = ggRootSub D q γ u := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [irgT6_map_map_eq_of e θ α hα, irgT6_bridge D q π e he γ u', irgT6_bridge D q π e he γ u]
  calc Subgroup.map α.toMonoidHom (ggRootSub D π γ u')
      = Subgroup.map α.toMonoidHom
          (Subgroup.map (MulAut.conj (π u')).toMonoidHom ((D.rootGroup γ).map π)) :=
          congrArg (Subgroup.map α.toMonoidHom) (irgT6_ggRootSub_eq D π γ u')
    _ = Subgroup.map (MulAut.conj (α (π u'))).toMonoidHom
          (Subgroup.map α.toMonoidHom ((D.rootGroup γ).map π)) :=
          irgT6_map_conj_map ((D.rootGroup γ).map π) (π u') α
    _ = Subgroup.map (MulAut.conj (α (π u'))).toMonoidHom
          (Subgroup.map (MulAut.conj ginner).toMonoidHom ((D.rootGroup γ).map π)) :=
          congrArg (Subgroup.map (MulAut.conj (α (π u'))).toMonoidHom) hpres
    _ = Subgroup.map (MulAut.conj (α (π u') * ginner)).toMonoidHom ((D.rootGroup γ).map π) :=
          irgT6_map_conj_conj ((D.rootGroup γ).map π) (α (π u')) ginner
    _ = ggRootSub D π γ u := by
          rw [irgT6_ggRootSub_eq D π γ u, hu]

private theorem irgT6_pair_abstract {U Q H : Type*} [Group U] [Group Q] [Group H]
    (D : UniversalRootDatum U) (q : U →* Q) (π : U →* H) (hπ : Function.Surjective π)
    (e : Q ≃* H) (he : ∀ y, e (q y) = π y) (θ : MulAut Q) (α : MulAut H)
    (hα : ∀ x, α (e x) = e (θ x)) (ginner : H) (γ₁ γ₂ : Fin D.rank → ℤ)
    (h₁ : ((D.rootGroup γ₁).map π).map α.toMonoidHom =
      ((D.rootGroup γ₁).map π).map (MulAut.conj ginner).toMonoidHom)
    (h₂ : ((D.rootGroup γ₂).map π).map α.toMonoidHom =
      ((D.rootGroup γ₂).map π).map (MulAut.conj ginner).toMonoidHom) (u' : U) :
    ∃ u : U, (ggRootSub D q γ₁ u').map θ.toMonoidHom = ggRootSub D q γ₁ u ∧
      (ggRootSub D q γ₂ u').map θ.toMonoidHom = ggRootSub D q γ₂ u := by
  obtain ⟨u, hu⟩ := hπ (α (π u') * ginner)
  exact ⟨u, irgT6_one_root D q π e he θ α hα ginner γ₁ h₁ u' u hu,
    irgT6_one_root D q π e he θ α hα ginner γ₂ h₂ u' u hu⟩

theorem irgRootPairAut_twistedE6
    {g : ℕ} (hadm : StatedLieAdmissible .twistedE6 0 2 g) : IRGRootPairAut .twistedE6 0 g := by
  classical
  intro θ β' hβ' hlong u'
  have hf : 1 ≤ g := hadm.2.1
  let θT : MulAut (twistedE6Group 2 g ⧸ Subgroup.center (twistedE6Group 2 g)) := θ
  let βT : Fin (twistedE6Datum 2 g).rank → ℤ := β'
  let uT : twistedE6Group 2 g := u'
  have hβT : βT ∈ (twistedE6Datum 2 g).roots := hβ'
  have hlongT : GGLongRoot (twistedE6Datum 2 g) βT := hlong
  let βN : Fin (twistedE6Datum 2 g).rank → ℤ := -βT
  have hβN : βN ∈ (twistedE6Datum 2 g).roots := irgT6_neg_mem_roots _ hβT
  show ∃ β : Fin (twistedE6Datum 2 g).rank → ℤ,
    IRGGoodRoot .twistedE6 0 g β ∧ ∃ u : twistedE6Group 2 g,
    (ggRootSub (twistedE6Datum 2 g)
        (QuotientGroup.mk' (Subgroup.center (twistedE6Group 2 g))) βT uT).map θT.toMonoidHom =
      ggRootSub (twistedE6Datum 2 g)
        (QuotientGroup.mk' (Subgroup.center (twistedE6Group 2 g))) β u ∧
    (ggRootSub (twistedE6Datum 2 g)
        (QuotientGroup.mk' (Subgroup.center (twistedE6Group 2 g))) (-βT) uT).map θT.toMonoidHom =
      ggRootSub (twistedE6Datum 2 g)
        (QuotientGroup.mk' (Subgroup.center (twistedE6Group 2 g))) (-β) u
  have hK : Nat.card (GaloisField 2 (2 * g)) = (2 ^ g) ^ 2 := by
    rw [GaloisField.card 2 (2 * g) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g c = c ^ (2 ^ g) := fun c =>
    iterateFrobeniusEquiv_def _ 2 g c
  have hσθ : (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g).toRingHom = frobQ 2 g :=
    RingHom.ext fun c => by
      change iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g c = frobQ 2 g c
      rw [hσ, frobQ_apply]
  obtain ⟨-, -, -, -, -, hcoe, -, hnf, -, -, hder, hZ, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      (GaloisField 2 (2 * g)) hK (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g) hσ
  have hH : ⁅twistedFixedGroup .E6 (GaloisField 2 (2 * g)) (frobQ 2 g),
      twistedFixedGroup .E6 (GaloisField 2 (2 * g)) (frobQ 2 g)⁆ =
      twistedE6RootGroup (GaloisField 2 (2 * g))
        (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g) := by
    rw [← hσθ]
    exact hder
  let C0 := twistedE6RootGroup (GaloisField 2 (2 * g))
    (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g)
  let π : twistedE6Group 2 g →* C0 :=
    (MulEquiv.subgroupCongr hH).toMonoidHom.comp (twistedE6Isogeny 2 g hf)
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hH).surjective.comp (twistedE6Isogeny_surjective 2 g hf)
  have hπval : ∀ z : twistedE6Group 2 g,
      ((π z : C0) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * g))) =
        ((e6Isogeny (GaloisField 2 (2 * g))
            (z : e6Data_valid.minGroup (GaloisField 2 (2 * g))) :
          adjointGroup .E6 (GaloisField 2 (2 * g))) :
            ModGL .E6 (GaloisField 2 (2 * g))) := fun _ => rfl
  have hπvalT : ∀ z : twistedE6Group 2 g,
      ((π z : C0) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * g))) =
        ((e6IsogenyT (GaloisField 2 (2 * g))
            (z : e6Data_valid.minGroup (GaloisField 2 (2 * g))) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * g))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * g))) := fun _ => rfl
  have hkerπ : π.ker = Subgroup.center (twistedE6Group 2 g) := by
    refine le_antisymm (RootDetectTwE6.ker_le_center g π hπvalT) ?_
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : π z ∈ Subgroup.center C0 := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := hπ y
      calc π x * π z = π (x * z) := (map_mul π x z).symm
        _ = π (z * x) := by rw [Subgroup.mem_center_iff.mp hz x]
        _ = π z * π x := map_mul π z x
    rw [hZ] at hzc
    exact Subgroup.mem_bot.mp hzc
  let q : twistedE6Group 2 g →* twistedE6Group 2 g ⧸ Subgroup.center (twistedE6Group 2 g) :=
    QuotientGroup.mk' (Subgroup.center (twistedE6Group 2 g))
  let e : twistedE6Group 2 g ⧸ Subgroup.center (twistedE6Group 2 g) ≃* C0 :=
    (QuotientGroup.quotientMulEquivOfEq hkerπ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have he : ∀ y : twistedE6Group 2 g, e (q y) = π y := fun _ => rfl
  let α : MulAut C0 := (e.symm.trans θT).trans e
  have hα : ∀ x, α (e x) = e (θT x) := fun x => by
    change e (θT (e.symm (e x))) = e (θT x)
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨ginner, diagvec, δ, hα_eq⟩ := hnf α
  have hpres : ∀ γ ∈ (twistedE6Datum 2 g).roots,
      (((twistedE6Datum 2 g).rootGroup γ).map π).map α.toMonoidHom =
        (((twistedE6Datum 2 g).rootGroup γ).map π).map
          (MulAut.conj ginner).toMonoidHom := by
    intro γ hγ
    let S : Subgroup C0 := ((twistedE6Datum 2 g).rootGroup γ).map π
    let Δv : MulAut C0 := compatDiagAutHom TwistTag.E6 (GaloisField 2 (2 * g))
      (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g).toRingHom diagvec
    let δ0 : MulAut C0 :=
      fieldActor (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g) δ
    have hδfwd : ∀ ε : GaloisField 2 (2 * g) ≃+* GaloisField 2 (2 * g),
        S.map (fieldActor (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g) ε).toMonoidHom ≤
          S := by
      intro ε
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hyz⟩ := hz
      obtain ⟨y₁, hy₁, hy₁e⟩ := OrdPGraph.exists_field_twisted g hf ε hγ hy
      refine ⟨y₁, hy₁, ?_⟩
      rw [← hyz]
      refine Subtype.ext ?_
      exact hy₁e
    have hΔfwd : ∀ dv : (a : Fin TwistTag.E6.foldedTag.rank) →
        (orbitField TwistTag.E6 (GaloisField 2 (2 * g))
          (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g).toRingHom a)ˣ,
        S.map (compatDiagAutHom TwistTag.E6 (GaloisField 2 (2 * g))
          (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g).toRingHom dv).toMonoidHom ≤ S := by
      intro dv
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hyz⟩ := hz
      obtain ⟨h, hh, hhz⟩ := RootDetectTwE6.hdiag_twisted (frobQ 2 g) (frobQ_frobQ 2 g hf) _
        (RootDetectTwE6.compatDiag_rho g dv) γ hγ
      have hmem : h * y * h⁻¹ ∈ (twistedE6Datum 2 g).rootGroup γ := by
        have hnorm : h ∈ Subgroup.normalizer ((twistedE6Datum 2 g).rootGroup γ : Set _) := by
          simp only [ggTorus, Subgroup.mem_iInf] at hh
          exact hh γ hγ
        exact (Subgroup.mem_normalizer_iff.mp hnorm y).mp hy
      refine ⟨h * y * h⁻¹, hmem, ?_⟩
      rw [← hyz]
      refine Subtype.ext ?_
      exact hhz y hy
    have hδfix : S.map δ0.toMonoidHom = S :=
      irgT6_map_eq_of_map_le S
        (f := fieldActor (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g) δ)
        (g := fieldActor (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g) δ⁻¹)
        (by rw [← fieldActor_mul, mul_inv_cancel, fieldActor_one])
        (hδfwd δ) (hδfwd δ⁻¹)
    have hΔfix : S.map Δv.toMonoidHom = S :=
      irgT6_map_eq_of_map_le S (f := Δv)
        (g := (compatDiagAutHom TwistTag.E6 (GaloisField 2 (2 * g))
          (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g).toRingHom diagvec)⁻¹)
        (mul_inv_cancel Δv)
        (hΔfwd diagvec)
        (by
          have hg : (compatDiagAutHom TwistTag.E6 (GaloisField 2 (2 * g))
              (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g).toRingHom diagvec)⁻¹ =
              compatDiagAutHom TwistTag.E6 (GaloisField 2 (2 * g))
                (iterateFrobeniusEquiv (GaloisField 2 (2 * g)) 2 g).toRingHom diagvec⁻¹ :=
            (map_inv _ diagvec).symm
          rw [hg]
          exact hΔfwd diagvec⁻¹)
    change S.map α.toMonoidHom = S.map (MulAut.conj ginner).toMonoidHom
    have hα_eq' : α = MulAut.conj ginner * Δv * δ0 := hα_eq
    calc S.map α.toMonoidHom
        = S.map ((MulAut.conj ginner * Δv * δ0).toMonoidHom) := by rw [hα_eq']
      _ = (S.map (Δv * δ0).toMonoidHom).map (MulAut.conj ginner).toMonoidHom :=
            irgT6_map_mul S (MulAut.conj ginner) (Δv * δ0)
      _ = ((S.map δ0.toMonoidHom).map Δv.toMonoidHom).map
            (MulAut.conj ginner).toMonoidHom := by
            rw [irgT6_map_mul S Δv δ0]
      _ = (S.map Δv.toMonoidHom).map (MulAut.conj ginner).toMonoidHom :=
            congrArg (fun T : Subgroup C0 =>
              (T.map Δv.toMonoidHom).map (MulAut.conj ginner).toMonoidHom) hδfix
      _ = S.map (MulAut.conj ginner).toMonoidHom :=
            congrArg (fun T : Subgroup C0 =>
              T.map (MulAut.conj ginner).toMonoidHom) hΔfix
  obtain ⟨u, hu₁, hu₂⟩ := irgT6_pair_abstract (twistedE6Datum 2 g) q π hπ e he θT α hα ginner
    βT (-βT) (hpres βT hβT) (hpres (-βT) hβN) uT
  exact ⟨βT, ⟨hβT, Or.inl hlongT⟩, u, hu₁, hu₂⟩

end CFSG.StandardType.RCKRP
