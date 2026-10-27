module

public import CFSG.RankThree.PartOne.KE6.Phi3Layer
public import CFSG.RankThree.PartOne.KE.A1Main

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)
open scoped Matrix MatrixGroups Pointwise

structure KernelLayer
    {Ω : Type} [Field Ω] (n : ModGL Tag.E6 Ω) (Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω)
    (S : Set (Fin Tag.E6.rank → ℤ)) (K : Type) [Field K] [Algebra K Ω] (ι' : Type) where
  P : ι' → Subgroup (ModGL Tag.E6 Ω)
  fin : ∀ i, Finite (P i)
  quasi : ∀ i, CFSG.IsQuasisimple (P i)
  le_span : ∀ i, P i ≤ rootSpan Tag.E6 Ω S
  le_fixed : ∀ i, P i ≤ twistedFixedPoints n Φ
  norm : ∀ i, ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S, y ∈ twistedFixedPoints n Φ →
    ∀ u ∈ P i, y * u * y⁻¹ ∈ P i
  cent : ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S, (∀ i, ∀ u ∈ P i, y * u = u * y) →
    y ∈ torusGroup Tag.E6 Ω ∧ y ∈ Subgroup.centralizer (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω))
  comm : ∀ X : Module.End Ω (RootModule Tag.E6 Ω),
    (∀ i, ∀ u ∈ P i, Commute X (u : Module.End Ω (RootModule Tag.E6 Ω))) →
      ∀ g ∈ rootSpan Tag.E6 Ω S, Commute X (g : Module.End Ω (RootModule Tag.E6 Ω))
  sl2 : S.Nonempty → ∃ (i₀ : ι') (m : Fin Tag.E6.rank) (h₀ : ModGL Tag.E6 Ω), ∀ B : SL(2, K),
    h₀ * simpleRootSL2 Tag.E6 Ω m (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * h₀⁻¹ ∈
      P i₀


variable {Ω : Type} [Field Ω]

theorem e6Commutant_eq_of_conj_eq {A B : Set (ModGL Tag.E6 Ω)} (n : ModGL Tag.E6 Ω)
    (h : e6Commutant ((fun g => n * g * n⁻¹) '' A) = e6Commutant ((fun g => n * g * n⁻¹) '' B)) :
    e6Commutant A = e6Commutant B := by
  rw [CFSG.RankThree.Chevalley.e6Commutant_conj, CFSG.RankThree.Chevalley.e6Commutant_conj] at h
  have hinj : Function.Injective (fun X : Module.End Ω (RootModule Tag.E6 Ω) =>
      (n : Module.End Ω (RootModule Tag.E6 Ω)) * X * ↑n⁻¹) := by
    intro X Y hXY
    have h1 := congrArg (fun Z : Module.End Ω (RootModule Tag.E6 Ω) =>
      (↑n⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) * Z * ↑n) hXY
    have hn1 : (↑n⁻¹ : Module.End Ω (RootModule Tag.E6 Ω)) * ↑n = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hn2 : (↑n : Module.End Ω (RootModule Tag.E6 Ω)) * ↑n⁻¹ = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simpa [mul_assoc, hn1, hn2, ← mul_assoc] using h1
  exact Set.image_injective.2 hinj h

def KernelLayer.single {n : ModGL Tag.E6 Ω} {Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω}
    {S : Set (Fin Tag.E6.rank → ℤ)} {K : Type} [Field K] [Algebra K Ω]
    (hS : ∀ α ∈ S, IsRoot Tag.E6 α) {w : WeylGroup Tag.E6} {J : Set (Fin Tag.E6.rank)}
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω J)
    (hfin : Finite ↥(rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ))
    (hq : CFSG.IsQuasisimple ↥(rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ))
    (hcomm : e6Commutant (((rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
          Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)))
    (hsl2 : ∃ (m : Fin Tag.E6.rank) (h₀ : ModGL Tag.E6 Ω), ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω m (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * h₀⁻¹ ∈
        rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ) :
    KernelLayer n Φ S K Unit where
  P := fun _ => rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ
  fin := fun _ => hfin
  quasi := fun _ => hq
  le_span := fun _ => inf_le_left
  le_fixed := fun _ => inf_le_right
  norm := fun _ y hy hyR u hu => by
    refine ⟨(Subgroup.mem_normalizer_iff.1
      (torusGroup_sup_rootSpan_le_normalizer' hS hy) u).1 hu.1, ?_⟩
    have hy' : n * Φ y * n⁻¹ = y := mem_twistedFixedPoints.1 hyR
    have hu' : n * Φ u * n⁻¹ = u := mem_twistedFixedPoints.1 hu.2
    refine mem_twistedFixedPoints.2 ?_
    rw [map_mul, map_mul, map_inv]
    calc n * (Φ y * Φ u * (Φ y)⁻¹) * n⁻¹ =
        (n * Φ y * n⁻¹) * (n * Φ u * n⁻¹) * (n * Φ y * n⁻¹)⁻¹ := by group
      _ = y * u * y⁻¹ := by rw [hy', hu']
  cent := fun y hy hc => hPcent_of_std hS hQ hcomm y hy (fun u hu => hc () u hu)
  comm := fun X hX g hg => by
    have hP : e6Commutant ((rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ : Subgroup (ModGL Tag.E6 Ω)) :
        Set (ModGL Tag.E6 Ω)) = e6Commutant (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω)) := by
      refine e6Commutant_eq_of_conj_eq (canonicalRep (coxeterSystem Tag.E6) Ω w) ?_
      have h1 : (fun g => canonicalRep (coxeterSystem Tag.E6) Ω w * g *
          (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) ''
            (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω)) =
          (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)) := by
        rw [← hQ, Subgroup.coe_map]
        rfl
      have h2 : (fun g => canonicalRep (coxeterSystem Tag.E6) Ω w * g *
          (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) ''
            ((rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ : Subgroup (ModGL Tag.E6 Ω)) :
              Set (ModGL Tag.E6 Ω)) =
          (((rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ).map
            (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
              Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) := by
        rw [Subgroup.coe_map]
        rfl
      rw [h1, h2, hcomm]
    have hX' : X ∈ e6Commutant ((rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints n Φ :
        Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) := fun u hu => hX () u hu
    rw [hP] at hX'
    exact hX' g hg
  sl2 := fun _ => by
    obtain ⟨m, h₀, h⟩ := hsl2
    exact ⟨(), m, h₀, h⟩

def KernelLayer.empty {n : ModGL Tag.E6 Ω} {Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω}
    {K : Type} [Field K] [Algebra K Ω] :
    KernelLayer n Φ (∅ : Set (Fin Tag.E6.rank → ℤ)) K Empty where
  P := fun e => e.elim
  fin := fun e => e.elim
  quasi := fun e => e.elim
  le_span := fun e => e.elim
  le_fixed := fun e => e.elim
  norm := fun e => e.elim
  cent := fun y hy _ => by
    have hspan : rootSpan Tag.E6 Ω (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    rw [hspan, sup_bot_eq] at hy
    refine ⟨hy, ?_⟩
    rw [hspan, Subgroup.mem_centralizer_iff]
    intro g hg
    have : g = 1 := hg
    rw [this, one_mul, mul_one]
  comm := fun X _ g hg => by
    have hspan : rootSpan Tag.E6 Ω (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    rw [hspan] at hg
    have : g = 1 := hg
    rw [this]
    exact (Commute.one_right X).symm.symm
  sl2 := fun h => absurd h Set.not_nonempty_empty


theorem e6Commutant_eq_of_conj_commutant {S : Set (Fin Tag.E6.rank → ℤ)}
    {w : WeylGroup Tag.E6} {J : Set (Fin Tag.E6.rank)}
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω J) {P : Subgroup (ModGL Tag.E6 Ω)}
    (hcomm : e6Commutant ((P.map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom : Subgroup
          (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω))) :
    e6Commutant (P : Set (ModGL Tag.E6 Ω)) = e6Commutant (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω)) := by
  refine e6Commutant_eq_of_conj_eq (canonicalRep (coxeterSystem Tag.E6) Ω w) ?_
  have h1 : (fun g => canonicalRep (coxeterSystem Tag.E6) Ω w * g *
      (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) ''
        (rootSpan Tag.E6 Ω S : Set (ModGL Tag.E6 Ω)) =
      (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)) := by
    rw [← hQ, Subgroup.coe_map]
    rfl
  have h2 : (fun g => canonicalRep (coxeterSystem Tag.E6) Ω w * g *
      (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹) '' (P : Set (ModGL Tag.E6 Ω)) =
      ((P.map (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom :
        Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) := by
    rw [Subgroup.coe_map]
    rfl
  rw [h1, h2, hcomm]

def KernelLayer.ofFamily {n : ModGL Tag.E6 Ω}
    {Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω} {S : Set (Fin Tag.E6.rank → ℤ)} {K : Type} [Field K]
    [Algebra K Ω] {ι' : Type} (P : ι' → Subgroup (ModGL Tag.E6 Ω))
    (hS : ∀ α ∈ S, IsRoot Tag.E6 α) {w : WeylGroup Tag.E6} {J : Set (Fin Tag.E6.rank)}
    (hQ : (rootSpan Tag.E6 Ω S).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom =
      subsystemGroup Tag.E6 Ω J)
    (hfin : ∀ i, Finite (P i)) (hq : ∀ i, CFSG.IsQuasisimple (P i))
    (hspan : ∀ i, P i ≤ rootSpan Tag.E6 Ω S) (hfix : ∀ i, P i ≤ twistedFixedPoints n Φ)
    (hnorm : ∀ i, ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S, y ∈ twistedFixedPoints n Φ →
      ∀ u ∈ P i, y * u * y⁻¹ ∈ P i)
    (hcomm : e6Commutant (((⨆ i, P i).map
        (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω w)).toMonoidHom : Subgroup
          (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (subsystemGroup Tag.E6 Ω J : Set (ModGL Tag.E6 Ω)))
    (hsl2 : S.Nonempty → ∃ (i₀ : ι') (m : Fin Tag.E6.rank) (h₀ : ModGL Tag.E6 Ω), ∀ B : SL(2, K),
      h₀ * simpleRootSL2 Tag.E6 Ω m (Matrix.SpecialLinearGroup.map (algebraMap K Ω) B) * h₀⁻¹ ∈
        P i₀) :
    KernelLayer n Φ S K ι' where
  P := P
  fin := hfin
  quasi := hq
  le_span := hspan
  le_fixed := hfix
  norm := hnorm
  cent := fun y hy hc => hPcent_of_std hS hQ hcomm y hy (fun u hu => by
    have hle : (⨆ i, P i) ≤ Subgroup.centralizer ({y} : Set (ModGL Tag.E6 Ω)) :=
      iSup_le fun i u' hu' => Subgroup.mem_centralizer_singleton_iff.2 (hc i u' hu').symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hu)).symm)
  comm := fun X hX g hg => by
    have hP := e6Commutant_eq_of_conj_commutant hQ hcomm
    have hX' : X ∈ e6Commutant (((⨆ i, P i : Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω))) := by
      rw [CFSG.RankThree.Lattice.e6Commutant_iSup, Set.mem_iInter]
      exact fun i u hu => hX i u hu
    rw [hP] at hX'
    exact hX' g hg
  sl2 := hsl2
end CFSG.RankThree.PartOne.KE6
