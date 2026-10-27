module

public import CFSG.RankThree.PartOne.KE6.Phi3D4Case

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
open CFSG.RankThree.Lattice (e6T3W toMat lget)
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)
open scoped Matrix MatrixGroups Pointwise

namespace NonsplitLayers

theorem dvd_card_triality_of_dvd_phiThree {q p : ℕ} (hq : 1 ≤ q) (h : p ∣ q ^ 2 + q + 1) :
    p ∣ q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) := by
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have h1 : q ^ 6 - 1 = (q ^ 2 + q + 1) * ((q - 1) * (q ^ 3 + 1)) := by
    zify [hq, h6]
    ring
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
  rw [h1]
  exact Dvd.dvd.mul_right h _


variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem phi3_D4_layer_card {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ twistedTorus (phi3N Ω) Fr) {w : WeylGroup Tag.E6}
    (hw : (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 d4Support) :
    Nat.card ↥(rootSpan Tag.E6 Ω (torusRootKernel x) ⊓
        twistedFixedPoints (phi3N Ω) (Units.map (entrywiseHom Fr))) =
      (ℓ ^ f) ^ 12 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 8 + (ℓ ^ f) ^ 4 + 1) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  set S := torusRootKernel x with hSdef
  set n := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  have hFrb : Function.Bijective Fr := ⟨Fr.injective, hFrs⟩
  have hSroots : ∀ α ∈ S, IsRoot Tag.E6 α := fun α hα => hα.1
  have hQ : (rootSpan Tag.E6 Ω S).map (MulAut.conj n).toMonoidHom =
      subsystemGroup Tag.E6 Ω d4Support := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 w S hSroots, hw, subsystemGroup_eq_rootSpan]
  have hvS := torusRootKernel_smul_stable hFr hx
  have hT : ∀ β ∈ parabolicRoots Tag.E6 d4Support,
      (w * e6T3W * w⁻¹) • β ∈ parabolicRoots Tag.E6 d4Support := by
    intro β hβ
    rw [← hw] at hβ ⊢
    obtain ⟨α, hα, rfl⟩ := hβ
    exact ⟨e6T3W • α, hvS α hα, by simp [mul_smul]⟩
  obtain ⟨L, hL, hLT⟩ := weylMatrix_conj_e6T3W_mem_orbit w
  obtain ⟨e, he, hWe⟩ := d4TrialityWeylType_of_conj hL hLT hT
  have hnwM := canonicalRep_mem_monomialSubgroup (τ := Tag.E6) Ω w
  have hnuM := canonicalRep_mem_monomialSubgroup (τ := Tag.E6) Ω e6T3W
  set m : ModGL Tag.E6 Ω := n * phi3N Ω * n⁻¹ with hmdef
  have hm : m ∈ monomialSubgroup Tag.E6 Ω := mul_mem (mul_mem hnwM hnuM) (inv_mem hnwM)
  have hcan : weylQuotientHom Tag.E6 Ω ⟨n, hnwM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hcanu : weylQuotientHom Tag.E6 Ω ⟨phi3N Ω, hnuM⟩ = e6T3W :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep e6T3W)
  have hwm : weylQuotientHom Tag.E6 Ω ⟨m, hm⟩ = w * e6T3W * w⁻¹ := by
    have e : (⟨m, hm⟩ : monomialSubgroup Tag.E6 Ω) =
        ⟨n, hnwM⟩ * ⟨phi3N Ω, hnuM⟩ * ⟨n, hnwM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hcan, hcanu]
  obtain ⟨g, hg, hgconj⟩ := exists_conj_eq_d4Theta ℓ f hf hFr hm (by rw [hwm]; exact hWe)
  set P := rootSpan Tag.E6 Ω S ⊓ twistedFixedPoints (phi3N Ω) (Units.map (entrywiseHom Fr))
    with hPdef
  have hθ_eq : ∀ z, phi3ThetaConj Ω Fr w z = m * baseChangeGL Fr z * m⁻¹ := fun z => by
    rw [phi3ThetaConj_eq_conj hFrb w z, baseChangeGL_eq_entrywise]
  have hPmap : ∀ z, z ∈ P.map (MulAut.conj n).toMonoidHom ↔
      (z ∈ subsystemGroup Tag.E6 Ω d4Support ∧ m * baseChangeGL Fr z * m⁻¹ = z) := by
    intro z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hz : n * y * n⁻¹ ∈ subsystemGroup Tag.E6 Ω d4Support := by
        rw [← hQ]
        exact ⟨y, hy.1, rfl⟩
      refine ⟨hz, ?_⟩
      have h1 : phi3Theta Ω Fr y = y := mem_twistedFixedPoints.1 hy.2
      have h2 := phi3ThetaConj_conj (L := Ω) (Fr := Fr) w y
      rw [h1, hθ_eq] at h2
      exact h2
    · rintro ⟨hz, hfix⟩
      rw [← hQ] at hz
      obtain ⟨y, hy, hyz⟩ := hz
      change n * y * n⁻¹ = z at hyz
      refine ⟨y, ⟨hy, mem_twistedFixedPoints.2 ?_⟩, hyz⟩
      have h2 := phi3ThetaConj_conj (L := Ω) (Fr := Fr) w y
      rw [hyz, hθ_eq, hfix] at h2
      have h3 : n * y * n⁻¹ = n * phi3Theta Ω Fr y * n⁻¹ := by rw [hyz]; exact h2
      exact (mul_left_cancel (mul_right_cancel h3)).symm
  have hconjL : P.map (MulAut.conj n).toMonoidHom =
      (d4Layer Fr e).map (MulAut.conj g⁻¹).toMonoidHom := by
    ext z
    rw [hPmap z]
    constructor
    · rintro ⟨hz, hfix⟩
      have hiff := fixed_iff_conj_mem_d4ThetaFixed (Fr := Fr) (e := e) (m := m) (g := g) hg hgconj hz
      have hmem : (⟨g * z * g⁻¹, mul_mem (mul_mem hg hz) (inv_mem hg)⟩ :
          subsystemGroup Tag.E6 Ω d4Support) ∈ d4ThetaFixed Ω Fr e := hiff.1 hfix
      refine ⟨g * z * g⁻¹, ⟨_, hmem, rfl⟩, ?_⟩
      change g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z
      group
    · rintro ⟨l, ⟨l', hl', rfl⟩, rfl⟩
      have hz : g⁻¹ * (l' : ModGL Tag.E6 Ω) * g⁻¹⁻¹ ∈ subsystemGroup Tag.E6 Ω d4Support :=
        mul_mem (mul_mem (inv_mem hg) l'.2) (by simpa using hg)
      refine ⟨hz, ?_⟩
      have hiff := fixed_iff_conj_mem_d4ThetaFixed (Fr := Fr) (e := e) (m := m) (g := g) hg hgconj hz
      refine hiff.2 ?_
      have : (⟨g * (g⁻¹ * (l' : ModGL Tag.E6 Ω) * g⁻¹⁻¹) * g⁻¹,
          mul_mem (mul_mem hg hz) (inv_mem hg)⟩ : subsystemGroup Tag.E6 Ω d4Support) = l' :=
        Subtype.ext (by group)
      rw [this]
      exact hl'
  have hk₃ := natCard_cubicSubfield (Ω := Ω) (ℓ := ℓ) hf
  have : IsAlgClosure (cubicSubfield (Ω := Ω) ℓ f) Ω :=
    ⟨inferInstance, isAlgebraic_cubicSubfield hK⟩
  have : CharP (cubicSubfield (Ω := Ω) ℓ f) ℓ := inferInstance
  let σ : cubicSubfield (Ω := Ω) ℓ f →+* cubicSubfield (Ω := Ω) ℓ f :=
    iterateFrobenius (cubicSubfield (Ω := Ω) ℓ f) ℓ (f * e)
  have hσ : ∀ c, σ c = c ^ ((ℓ ^ f) ^ e) := fun c => by
    rw [iterateFrobenius_def, pow_mul]
  obtain ⟨φ, -⟩ := exists_d4ThetaFixed_equiv (K := cubicSubfield (Ω := Ω) ℓ f) hℓ hf hk₃ he hσ hFr
  have hequiv : ↥P ≃* ↥(d4ThetaFixed Ω Fr e) :=
    (((Subgroup.equivMapOfInjective P (MulAut.conj n).toMonoidHom
        (MulAut.conj n).injective).trans (MulEquiv.subgroupCongr hconjL)).trans
      (Subgroup.equivMapOfInjective (d4Layer Fr e) (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).symm).trans
      (Subgroup.equivMapOfInjective (d4ThetaFixed Ω Fr e)
        (subsystemGroup Tag.E6 Ω d4Support).subtype (Subgroup.subtype_injective _)).symm
  have hcard := (triality_both_orientations_exact_finite_order ℓ f hℓ hf
    (cubicSubfield (Ω := Ω) ℓ f) hk₃ e he σ hσ).1
  rw [Nat.card_congr hequiv.toEquiv, Nat.card_congr φ.toEquiv]
  exact hcard

end NonsplitLayers

end CFSG.RankThree.PartOne.KE6
