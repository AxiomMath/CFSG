module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcIndexTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTorusIndex
public import CFSG.LieType.Chevalley.OddDiagramFixedAmbientCentralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

theorem nonempty_galoisField_ringHom (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) [Fact p.Prime]
    [CharP L p] (f : ℕ) : Nonempty (GaloisField p f →+* L) := by
  let _ : Algebra (ZMod p) L := ZMod.algebra L p
  exact ⟨(IsAlgClosed.lift : GaloisField p f →ₐ[ZMod p] L).toRingHom⟩

@[expose] def TwistedInnerDataOf (t : TwistTag) (L : Type) [Field L] (p f : ℕ) [Fact p.Prime]
    [CharP L p] (R : ℕ → ℕ → Prop) : Prop :=
  ∀ x ∈ fixedPointsIn (adjointGroup t.tag L) (frobTwistGL t.tag L p f (diagramMap t L)),
    x ^ 2 = 1 → x ≠ 1 → ∃ g₁ ∈ adjointGroup t.tag L, ∃ N : ModGL t.tag L,
      g₁ * (frobTwistGL t.tag L p f (diagramMap t L) g₁)⁻¹ = N ∧
      ∃ u : fixedPointsIn (adjointGroup t.tag L) (frobTwistGL t.tag L p f (N * diagramMap t L)),
        orderOf u = p ∧ (∃ (H : Subgroup _) (e n : ℕ), u ∈ H ∧ IsSpecialType p e n ↥H ∧ R e n) ∧
        g₁ * x * g₁⁻¹ * (u : ModGL t.tag L) * (g₁ * x * g₁⁻¹)⁻¹ = (u : ModGL t.tag L)⁻¹

@[expose] def TwistedInnerData (t : TwistTag) (L : Type) [Field L] (p f : ℕ) [Fact p.Prime]
    [CharP L p] : Prop :=
  TwistedInnerDataOf t L p f fun e n => e ≤ n ∧ 3 < p ^ e

theorem exists_inv_inner_twisted
    (t : TwistTag) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p] {R : ℕ → ℕ → Prop}
    (hdata : TwistedInnerDataOf t L p f R) (g : graphFixedRootGroup t K σ.toRingHom)
    (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    ∃ x : graphFixedRootGroup t K σ.toRingHom, orderOf x = p ∧ g * x * g⁻¹ = x⁻¹ ∧
      ∃ (H : Subgroup (graphFixedRootGroup t K σ.toRingHom)) (e n : ℕ), x ∈ H ∧
        IsSpecialType p e n ↥H ∧ R e n := by
  classical
  have hp : p.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  set ι : K →+* L := algebraMap K L with hιdef
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  obtain ⟨hinj, -, -, -⟩ :=
    odd_diagram_fixed_ambient_centralizer_trivial t hp hf hodd K hK σ.toRingHom hσ L ι
  obtain ⟨-, -, hHR, hHN, -, -, -⟩ :=
    odd_diagram_Frobenius_fixed_derived_root_group t hp hf hodd K hK σ.toRingHom hσ L Fr hFr
  have hcop := coprime_index_twistedFixedGroup t hp hf hodd K hK σ.toRingHom hσ L Fr hFr
  have hRF : fixedPointsIn (adjointGroup t.tag L)
      (frobTwistGL t.tag L p f (diagramMap t L)) = twistedFixedGroup t L Fr := by
    ext y
    refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
    change frobTwistGL t.tag L p f (diagramMap t L) y = y ↔ twistHom t L Fr y = y
    rw [frobTwistGL_apply, twistHom_apply]
  have hRn : twistedFixedGroup t L Fr ≤ Subgroup.normalizer
      ((graphFixedRootGroup t K σ.toRingHom).map (baseChangeGL (algebraMap K L)) :
        Set (ModGL t.tag L)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHR).mp hHN
  set x' : ModGL t.tag L := baseChangeGL ι (g : ModGL t.tag K) with hx'def
  have hx'R : x' ∈ twistedFixedGroup t L Fr := by
    refine hHR ⟨g, g.2, ?_⟩
    rw [hx'def, hιdef]
  have hx'mem : x' ∈ fixedPointsIn (adjointGroup t.tag L)
      (frobTwistGL t.tag L p f (diagramMap t L)) := by
    rw [hRF]
    exact hx'R
  have hgK2 : (g : ModGL t.tag K) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hg2]
    rfl
  have hx'2 : x' ^ 2 = 1 := by
    rw [hx'def, ← map_pow, hgK2, map_one]
  have hx'1 : x' ≠ 1 := by
    intro h1
    apply hg1
    have hgK : (g : ModGL t.tag K) = 1 := hinj (h1.trans (map_one (baseChangeGL ι)).symm)
    exact Subtype.ext (by simpa using hgK)
  obtain ⟨g₁, hg₁, N, hc, u, hu, hgood, hinv⟩ := hdata x' hx'mem hx'2 hx'1
  have hTR : ∀ v ∈ fixedPointsIn (adjointGroup t.tag L)
      (frobTwistGL t.tag L p f (N * diagramMap t L)), g₁⁻¹ * v * g₁ ∈ twistedFixedGroup t L Fr := by
    intro v hv
    have h := conj_mem_fixedPointsIn_of_cocycle (p := p) (D := diagramMap t L) (N := N)
      (g₁ := g₁) hg₁ hc hv
    rwa [hRF] at h
  have hβz : ∀ w : graphFixedRootGroup t K σ.toRingHom,
      baseChangeGL ι ((MulAut.conj g w : graphFixedRootGroup t K σ.toRingHom) : ModGL t.tag K) =
      x' * baseChangeGL ι (w : ModGL t.tag K) * x'⁻¹ := by
    intro w
    simp only [hx'def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  obtain ⟨H, e, n, huH, hH, hR⟩ := hgood
  obtain ⟨w, H₀, hw, hwconj, hwH₀, ⟨φ⟩⟩ :=
    exists_inv_of_conj_index (baseChangeGL ι) hinj
      (C := graphFixedRootGroup t K σ.toRingHom) (MulAut.conj g) x' hβz
      hHR hRn hcop (T := fixedPointsIn (adjointGroup t.tag L)
        (frobTwistGL t.tag L p f (N * diagramMap t L))) (y := g₁) hTR hu huH
      (fun v hv => by simpa using hH.1 ⟨v, hv⟩) hinv
  exact ⟨w, hw, by rw [← hwconj]; exact (MulAut.conj_apply g w).symm,
    H₀, e, n, hwH₀, hH.of_mulEquiv φ, hR⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
