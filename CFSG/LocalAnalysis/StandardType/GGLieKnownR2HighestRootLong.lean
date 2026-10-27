module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootCores
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.HighestRoot.Gen

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.HighestRoot
  CFSG.LieType.TitsSimplicity CFSG.ClassicalInvolution.ModelFacts
open scoped commutatorElement

theorem coreOne_long_of
    {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅) (hirr : IsIrreducible D.cartan)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r)
    (hmax : ∀ γ₀ ∈ D.roots, (∀ δ ∈ D.roots, ht δ ≤ ht γ₀) → γ₀ = r)
    {β : Fin D.rank → ℤ} (hl : GGLongRoot D β) (u : K)
    {Rr Rm Q : Subgroup K}
    (hRr : Rr = ggRootSub D (MonoidHom.id K) β u)
    (hRm : Rm = ggRootSub D (MonoidHom.id K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  obtain ⟨w, γ₀, hγ₀mem, hγ₀max, hβeq⟩ := hl
  have hγ₀ : γ₀ = r := hmax γ₀ hγ₀mem hγ₀max
  have hβr : β = weylAction D.isFiniteType w r := by rw [hβeq, hγ₀]
  set m : K := nrep hct w with hm
  have ham : ActsAs D m w := by rw [hm]; exact actsAs_nrep hct w
  set e : MulAut K := MulAut.conj (u * m) with he
  have hcomp : (MulAut.conj u).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
      e.toMonoidHom := by
    ext x
    rw [he]
    change u * (m * x * m⁻¹) * u⁻¹ = (u * m) * x * (u * m)⁻¹
    group
  have hβmap : D.rootGroup β = (D.rootGroup r).map (MulAut.conj m).toMonoidHom := by
    rw [hβr, ← ham r hr.mem_roots]
  have hnegmem : -r ∈ D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hr.mem_roots
  have hneg : -β = weylAction D.isFiniteType w (-r) := by rw [map_neg, ← hβr]
  have hnegmap : D.rootGroup (-β) =
      (D.rootGroup (-r)).map (MulAut.conj m).toMonoidHom := by
    rw [hneg, ← ham (-r) hnegmem]
  have hRrX : Rr = (D.rootGroup r).map e.toMonoidHom := by
    rw [hRr, ggRootSub, Subgroup.map_id, hβmap, Subgroup.map_map, hcomp]
  have hRmX : Rm = (D.rootGroup (-r)).map e.toMonoidHom := by
    rw [hRm, ggRootSub, Subgroup.map_id, hnegmap, Subgroup.map_map, hcomp]
  set Qr : Subgroup K := pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)) with hQrdef
  have hQr : Q = Qr.map e.toMonoidHom := by
    rw [hQ, hRrX]
    exact (map_pCoreOf_normalizer_mulEquiv e (D.rootGroup r)).symm
  have htop : Qr ⊔ (D.rootGroup r ⊔ D.rootGroup (-r)) = ⊤ :=
    coreOne_highest_of hct hext hdiv hirr hX hr
  calc Q ⊔ (Rr ⊔ Rm)
      = Qr.map e.toMonoidHom ⊔ ((D.rootGroup r).map e.toMonoidHom ⊔
          (D.rootGroup (-r)).map e.toMonoidHom) := by rw [hQr, hRrX, hRmX]
    _ = (Qr ⊔ (D.rootGroup r ⊔ D.rootGroup (-r))).map e.toMonoidHom := by
        rw [Subgroup.map_sup, Subgroup.map_sup]
    _ = ⊤ := by
        rw [htop, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

theorem coreFour_long_of
    {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hcomm : RootGroupCommutators D) (hdiv : D.divisible = ∅)
    {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r)
    (hmax : ∀ γ₀ ∈ D.roots, (∀ δ ∈ D.roots, ht δ ≤ ht γ₀) → γ₀ = r)
    (hC2 : pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)) ≤ highestRootRadical D r)
    {β : Fin D.rank → ℤ} (hl : GGLongRoot D β) (u : K)
    {Rr Q : Subgroup K}
    (hRr : Rr = ggRootSub D (MonoidHom.id K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set K) := by
  obtain ⟨w, γ₀, hγ₀mem, hγ₀max, hβeq⟩ := hl
  have hγ₀ : γ₀ = r := hmax γ₀ hγ₀mem hγ₀max
  have hβr : β = weylAction D.isFiniteType w r := by rw [hβeq, hγ₀]
  set m : K := nrep hct w with hm
  have ham : ActsAs D m w := by rw [hm]; exact actsAs_nrep hct w
  set e : MulAut K := MulAut.conj (u * m) with he
  have hcomp : (MulAut.conj u).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
      e.toMonoidHom := by
    ext x
    rw [he]
    change u * (m * x * m⁻¹) * u⁻¹ = (u * m) * x * (u * m)⁻¹
    group
  have hβmap : D.rootGroup β = (D.rootGroup r).map (MulAut.conj m).toMonoidHom := by
    rw [hβr, ← ham r hr.mem_roots]
  have hRrX : Rr = (D.rootGroup r).map e.toMonoidHom := by
    rw [hRr, ggRootSub, Subgroup.map_id, hβmap, Subgroup.map_map, hcomp]
  set Qr : Subgroup K := pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)) with hQrdef
  have hQr : Q = Qr.map e.toMonoidHom := by
    rw [hQ, hRrX]
    exact (map_pCoreOf_normalizer_mulEquiv e (D.rootGroup r)).symm
  have hcf : ⁅Qr, Qr⁆ ≤ D.rootGroup r ∧
      Qr ≤ Subgroup.centralizer (D.rootGroup r : Set K) :=
    coreFour_highest_of hext hcomm hdiv hr hC2
  refine ⟨?_, ?_⟩
  · calc ⁅Q, Q⁆ = ⁅Qr.map e.toMonoidHom, Qr.map e.toMonoidHom⁆ := by rw [hQr]
      _ = (⁅Qr, Qr⁆).map e.toMonoidHom :=
          (Subgroup.map_commutator (H₁ := Qr) (H₂ := Qr) e.toMonoidHom).symm
      _ ≤ (D.rootGroup r).map e.toMonoidHom := Subgroup.map_mono (f := e.toMonoidHom) hcf.1
      _ = Rr := hRrX.symm
  · calc Q = Qr.map e.toMonoidHom := hQr
      _ ≤ (Subgroup.centralizer (D.rootGroup r : Set K)).map e.toMonoidHom :=
          Subgroup.map_mono (f := e.toMonoidHom) hcf.2
      _ ≤ Subgroup.centralizer (Rr : Set K) := by
          rw [hRrX]
          exact Subgroup.map_centralizer_le_centralizer_image (D.rootGroup r : Set K)
            e.toMonoidHom

end CFSG.StandardType.LieKnownR2
