module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Defs
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Lang.E6Descent.RankTwistedE6
public import CFSG.LieType.Chevalley.KernelComponentRoots
import CFSG.LocalAnalysis.StandardType.GGTwE6SigmaTorus
import CFSG.LocalAnalysis.StandardType.GGTwE6LangRetype
import all CFSG.LocalAnalysis.StandardType.GGL45NtLattice
import CFSG.LieType.Chevalley.SignKernelStabilizer
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public section

namespace CFSG.StandardType.TwE6LemmaK

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.E6Descent CFSG.Open CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.StandardType.NoOffTwE6Three (IsToralE6)

private theorem lk5_familyReflectionGroup_le_closure
    {τ : Tag} {K : Type} [Field K] {ι : Type} (a : ι → Fin τ.rank → Kˣ) :
    CFSG.HardMathSupport.C14Lattice.familyReflectionGroup a ≤
      Subgroup.closure {s | ∃ α ∈ familyKernel a, s = rootReflection α} := by
  change Subgroup.closure {r | ∃ (w : WeylGroup τ) (i : Fin τ.rank),
      w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ familyKernel a ∧ r = w * simple τ i * w⁻¹} ≤
    Subgroup.closure {s | ∃ α ∈ familyKernel a, s = rootReflection α}
  refine Subgroup.closure_mono ?_
  rintro r ⟨w, i, hα, rfl⟩
  exact ⟨w • (Pi.single i 1 : Fin τ.rank → ℤ), hα, conj_simple_eq_rootReflection w i⟩

private theorem lk5_mem_familyStabilizerSubgroup
    {q : ℕ} (h5 : 5 ∣ q + 1) {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ q)
    {ι : Type} {a : ι → Fin Tag.E6.rank → Ωˣ} (ha5 : ∀ s i, a s i ^ 5 = 1) {v₀ : WeylGroup Tag.E6}
    (hfix : ∀ s, canonicalRep (coxeterSystem Tag.E6) Ω v₀ *
      twistE6 Ω Fr (rootDiagUnit Tag.E6 (a s)) * (canonicalRep (coxeterSystem Tag.E6) Ω v₀)⁻¹ =
        rootDiagUnit Tag.E6 (a s)) :
    twE6W0 * v₀⁻¹ ∈ familyStabilizerSubgroup a := by
  have hinv : (twE6W0 * v₀⁻¹)⁻¹ ∈ familyStabilizerSubgroup a := by
    rw [mem_familyStabilizerSubgroup]
    intro s v
    have htw : twistE6 Ω Fr (rootDiagUnit Tag.E6 (a s)) = rootDiagUnit Tag.E6
        (fun i => Units.map Fr.toMonoidHom (a s (CFSG.RankThree.E6.e6Rho.symm i))) :=
      twistE6_rootDiagUnit (a s)
    have hconj_v0 : ∀ v : Fin Tag.E6.rank → ℤ,
        rootChar (a s) (v₀ • v) = rootChar
          (fun i => Units.map Fr.toMonoidHom (a s (CFSG.RankThree.E6.e6Rho.symm i))) v := by
      refine (rootDiagUnit_eq_conj_canonicalRep_iff (a s)
        (fun i => Units.map Fr.toMonoidHom (a s (CFSG.RankThree.E6.e6Rho.symm i))) v₀).1 ?_
      rw [← htw]
      exact (hfix s).symm
    have hconj_w0 : ∀ v : Fin Tag.E6.rank → ℤ,
        rootChar (a s) (twE6W0 • v) = rootChar
          (fun i => Units.map Fr.toMonoidHom (a s (CFSG.RankThree.E6.e6Rho.symm i))) v := by
      refine (rootDiagUnit_eq_conj_canonicalRep_iff (a s)
        (fun i => Units.map Fr.toMonoidHom (a s (CFSG.RankThree.E6.e6Rho.symm i))) twE6W0).1 ?_
      have h : canonicalRep (coxeterSystem Tag.E6) Ω twE6W0 *
          twistE6 Ω Fr (rootDiagUnit Tag.E6 (a s)) *
          (canonicalRep (coxeterSystem Tag.E6) Ω twE6W0)⁻¹ = rootDiagUnit Tag.E6 (a s) :=
        (TwistedDiag.theta_rootDiagUnit_eq_iff (Fr := Fr) hFr (a s)).2 fun i => by
          obtain ⟨k, hk⟩ := h5
          rw [hk, pow_mul, ha5 s i, one_pow]
      rw [htw] at h
      exact h.symm
    rw [mul_inv_rev, inv_inv, mul_smul, hconj_v0, ← hconj_w0, smul_inv_smul]
  simpa using inv_mem hinv

theorem exists_family_of_toral_data_five
    {q : ℕ} (h5 : 5 ∣ q + 1) {Ω : Type} [Field Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ q)
    {X : Subgroup (ModGL Tag.E6 Ω)} (hX5 : IsElemAbelian 5 X) (hXf : Finite X)
    {g₀ : ModGL Tag.E6 Ω} {v₀ : WeylGroup Tag.E6}
    (hA : ∀ x ∈ X, g₀⁻¹ * x * g₀ ∈ torusGroup Tag.E6 Ω ∧
      canonicalRep (coxeterSystem Tag.E6) Ω v₀ * twistE6 Ω Fr (g₀⁻¹ * x * g₀) *
        (canonicalRep (coxeterSystem Tag.E6) Ω v₀)⁻¹ = g₀⁻¹ * x * g₀) :
    ∃ a : X → Fin Tag.E6.rank → Ωˣ,
      (∀ x : X, rootDiagUnit Tag.E6 (a x) = g₀⁻¹ * (x : ModGL Tag.E6 Ω) * g₀) ∧
      (∀ x : X, ∀ i, a x i ^ 5 = 1) ∧
      twE6W0 * v₀⁻¹ ∈ Subgroup.closure {s | ∃ α ∈ familyKernel a, s = rootReflection α} := by
  classical
  haveI := hXf
  have hconj : ∀ z : ModGL Tag.E6 Ω, g₀⁻¹ * z * g₀ = MulAut.conj g₀⁻¹ z := fun z => by
    rw [MulAut.conj_apply, inv_inv]
  have hex : ∀ x : X, ∃ b : Fin Tag.E6.rank → Ωˣ,
      rootDiagUnit Tag.E6 b = g₀⁻¹ * (x : ModGL Tag.E6 Ω) * g₀ ∧ ∀ i, b i ^ 5 = 1 := by
    intro x
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (K := Ω) (hA x x.2).1
    have hx5 : (x : ModGL Tag.E6 Ω) ^ 5 = 1 := hX5.2 x x.2
    have ht5 : (g₀⁻¹ * (x : ModGL Tag.E6 Ω) * g₀) ^ 5 = 1 := by
      rw [hconj, ← map_pow, hx5, map_one]
    have hb5 : b ^ 5 = 1 := rootDiagUnit_injective (K := Ω)
      (by rw [← rootDiagUnit_pow, ← hb, ht5, rootDiagUnit_one])
    exact ⟨b, hb.symm, fun i => by simpa using congrFun hb5 i⟩
  choose a ha ha5 using hex
  have hfix : ∀ x : X, canonicalRep (coxeterSystem Tag.E6) Ω v₀ *
      twistE6 Ω Fr (rootDiagUnit Tag.E6 (a x)) *
      (canonicalRep (coxeterSystem Tag.E6) Ω v₀)⁻¹ = rootDiagUnit Tag.E6 (a x) := by
    intro x
    have h := (hA x x.2).2
    rw [← ha x] at h
    exact h
  refine ⟨a, ha, ha5, ?_⟩
  refine lk5_familyReflectionGroup_le_closure a
    (CFSG.HardMathSupport.C14Lattice.familyStabilizer_le_reflection
      (τ := Tag.E6) (K := Ω) (ι := X) Nat.prime_five
      (Or.inr CFSG.HardMathSupport.C14Lattice.sylowCert_E6_5) ha5 ?_)
  exact lk5_mem_familyStabilizerSubgroup (q := q) (Ω := Ω) (Fr := Fr) (a := a) (v₀ := v₀)
    h5 hFr ha5 hfix

theorem ggTwE6FiveToralTypeMinusOne
    {f : ℕ} (hf : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) (Ω : Type) [Field Ω]
    [Algebra (GaloisField 2 (2 * f)) Ω] [IsAlgClosure (GaloisField 2 (2 * f)) Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f) {X : Subgroup (ModGL Tag.E6 Ω)}
    (hXR : X ≤ TwistedDiag.Rgrp Ω Fr) (hX5 : IsElemAbelian 5 X) (hXf : Finite X)
    (hXt : IsToralE6 Ω X) :
    ∃ g ∈ adjointGroup Tag.E6 Ω, g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω ∧
      ∀ x ∈ X, g⁻¹ * x * g ∈ torusGroup Tag.E6 Ω := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (GaloisField 2 (2 * f))
  haveI : CharP Ω 2 := charP_of_injective_algebraMap
    (algebraMap (GaloisField 2 (2 * f)) Ω).injective 2
  obtain ⟨v₀, g₀, hg₀, hg₀F, hA⟩ :=
    TwE6SigmaTorus.exists_sigmaTorus_of_toral hf Ω Fr hFr hXR hXt
  obtain ⟨a, ha, -, hw⟩ :=
    exists_family_of_toral_data_five (q := 2 ^ f) h5 Fr hFr hX5 hXf hA
  have hFr' : Fr = iterateFrobenius Ω 2 f := RingHom.ext fun c => by
    rw [hFr, iterateFrobenius_def]
  subst hFr'
  obtain ⟨z, hz, hzF⟩ : ∃ z ∈ familyGroup (K := Ω) a,
      (g₀ * z)⁻¹ * twistE6 Ω (iterateFrobenius Ω 2 f) (g₀ * z) = TwistedDiag.n0 Ω :=
    LangRetype.exists_lang_retype_twisted (L := Ω) 2 TwistTag.E6 f hf a
      (g₀ := g₀) (v := v₀) (w := twE6W0) (inv_mul_eq_iff_eq_mul.1 hg₀F)
      (fun s => by
        have h1 := (hA (s : ModGL Tag.E6 Ω) s.2).2
        rw [← ha s] at h1
        exact h1) hw
  have hzc := mem_familyCentralizer.1 (familyGroup_le_familyCentralizer a hz)
  refine ⟨g₀ * z, mul_mem hg₀ hzc.1, hzF, fun x hx => ?_⟩
  rw [show (g₀ * z)⁻¹ * x * (g₀ * z) = z⁻¹ * (g₀⁻¹ * x * g₀) * z by group,
    ← ha ⟨x, hx⟩]
  have hdz : rootDiagUnit Tag.E6 (a ⟨x, hx⟩) * z = z * rootDiagUnit Tag.E6 (a ⟨x, hx⟩) := by
    calc rootDiagUnit Tag.E6 (a ⟨x, hx⟩) * z
        = (rootDiagUnit Tag.E6 (a ⟨x, hx⟩) * z * (rootDiagUnit Tag.E6 (a ⟨x, hx⟩))⁻¹) *
            rootDiagUnit Tag.E6 (a ⟨x, hx⟩) := by group
      _ = z * rootDiagUnit Tag.E6 (a ⟨x, hx⟩) := by rw [hzc.2 ⟨x, hx⟩]
  have hconjz : z⁻¹ * rootDiagUnit Tag.E6 (a ⟨x, hx⟩) * z =
      rootDiagUnit Tag.E6 (a ⟨x, hx⟩) := by
    calc z⁻¹ * rootDiagUnit Tag.E6 (a ⟨x, hx⟩) * z
        = z⁻¹ * (rootDiagUnit Tag.E6 (a ⟨x, hx⟩) * z) := by group
      _ = z⁻¹ * (z * rootDiagUnit Tag.E6 (a ⟨x, hx⟩)) := by rw [hdz]
      _ = rootDiagUnit Tag.E6 (a ⟨x, hx⟩) := by group
  rw [hconjz]
  exact rootDiagUnit_mem_torusGroup _

end CFSG.StandardType.TwE6LemmaK
