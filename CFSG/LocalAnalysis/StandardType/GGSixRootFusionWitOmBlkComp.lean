module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkCore
public import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

namespace WitOmBlk

open QuadraticMap Module CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCPrimary Polynomial

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem fixes_of_commute_of_eight {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hQ : (polarBilin Q).Nondegenerate) (h8 : 8 ≤ finrank K (fixedSpace x)) {g : V ≃ₗ[K] V}
    (hg : g ∈ isometryCentralizer Q x)
    (hcomm : ∀ f ∈ supportedFixedDerived Q x, ∀ v, g (f v) = f (g v)) :
    ∀ w ∈ fixedSpace x, g w = w := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hWnd := hx.polarBilin_fixed_nondegenerate
  have h3 : 3 ≤ finrank K (fixedSpace x) := by omega
  obtain ⟨k, hk⟩ := CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry.even_finrank_fixed hx
  obtain ⟨e, he0, hQe⟩ := CFSG.RankThree.PartOne.exists_singular_of_even_regular
    (Q.comp (fixedSpace x).subtype) hWnd (n := k) (by omega) (by omega)
  have hsing : ∃ e ∈ fixedSpace x, e ≠ 0 ∧ Q e = 0 :=
    ⟨e, e.2, fun h => he0 (Subtype.ext h), hQe⟩
  have hM : ElementaryMapsMem Q (fixedSpace x) :=
    elementaryMapsMem_of_regular hWnd h3 (fun _ h => absurd h (by omega))
  have hgQ : ∀ v, Q (g.toAddEquiv v) = (1 : K) * (RingEquiv.refl K) (Q v) := fun v => by
    rw [one_mul]
    exact (mem_isometryCentralizer.mp hg).1 v
  have hcomm' : ∀ g' ∈ supportedDerived Q (fixedSpace x), ∀ v,
      g.toAddEquiv (g' v) = g' (g.toAddEquiv v) := fun g' hg' v =>
    hcomm g' (CFSG.RankThree.PartOne.supportedDerived_le_supportedFixedDerived hx hg') v
  obtain ⟨-, c, hc0, hc⟩ := scalar_restriction_of_commute g.toAddEquiv (RingEquiv.refl K) 1 hgQ
    hcomm' hQ hWnd h3 hsing hM (fun c v => by simp)
  have : Nontrivial (fixedSpace x) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨w₁, hw₁⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hWnd
  have hcc : c * c = 1 := by
    have h1 := (mem_isometryCentralizer.mp hg).1 (w₁ : V)
    have h5 : g (w₁ : V) = c • (w₁ : V) := hc w₁ w₁.2
    rw [h5, QuadraticMap.map_smul, smul_eq_mul] at h1
    have h6 : (Q.comp (fixedSpace x).subtype) w₁ = Q (w₁ : V) := rfl
    rw [h6] at hw₁
    exact mul_right_cancel₀ hw₁ (by rw [one_mul]; exact h1)
  have hc1 : c = 1 := by
    have h8 : (c - 1) ^ 2 = 0 := by
      have : (c - 1) ^ 2 = c * c - 1 - 2 * (c - 1) := by ring
      rw [this, hcc, h2]
      ring
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h8)
  intro w hw
  have h5 : g w = c • w := hc w hw
  rw [h5, hc1, one_smul]

theorem exists_component_block (hQ : Q.polarBilin.Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : V ≃ₗ[K] V} (hx : x ∈ orthDerived Q) (hxp : x ^ p = 1)
    {X : Submodule K V} (hxoff : ∀ y ∈ X.orthogonalBilin (polarBilin Q), x y = y)
    (hdim : finrank K X + 8 ≤ finrank K V) :
    ∃ L : Subgroup (V ≃ₗ[K] V), L ≤ orthDerived Q ∧ CFSG.IsQuasisimple L ∧
      (∀ l ∈ L, l * x = x * l) ∧
      (∀ g ∈ orthDerived Q, g * x = x * g → ∀ l ∈ L, g * l * g⁻¹ ∈ L) ∧
      ∀ c ∈ TauCeti.QuadraticMap.orthogonalGroup Q, c * x = x * c → (∀ l ∈ L, c * l = l * c) →
        ∀ y ∈ X.orthogonalBilin (polarBilin Q), c y = y := by
  have hΩO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _
  have hpK : (p : K) ≠ 0 := by
    rw [CFSG.RankThree.PartOne.OddIso.natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
    exact one_ne_zero
  have hxo : OddOrderIsometry Q p x :=
    ⟨hΩO hx, hxp, hpK, fun v hv => hQ.1 v fun w => by rw [polarBilin_apply_apply]; exact hv w⟩
  have hle : X.orthogonalBilin (polarBilin Q) ≤ fixedSpace x := fun y hy =>
    mem_fixedSpace.mpr (hxoff y hy)
  have h8 : 8 ≤ finrank K (fixedSpace x) := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hQ X
    change finrank K (X.orthogonalBilin (polarBilin Q)) = _ at h1
    have h2 := Submodule.finrank_mono hle
    omega
  obtain ⟨k, hk⟩ := CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry.even_finrank_fixed hxo
  have hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0 :=
    CFSG.RankThree.PartOne.exists_threeSingular_of_dim _ hxo.polarBilin_fixed_nondegenerate
      (m := k) (by omega) (by omega)
  refine ⟨supportedFixedDerived Q x, hxo.supportedFixedDerived_le_orthDerived,
    hxo.isQuasisimple_supportedFixedDerived hT, fun l hl => ?_, fun g hg hgx l hl => ?_,
    fun c hc hcx hcL y hy => ?_⟩
  · have h1 := (mem_isometryCentralizer.mp (supportedFixedDerived_le_isometryCentralizer hl)).2
    exact LinearEquiv.ext fun v => h1 v
  · refine hxo.conj_mem_supportedFixedDerived (mem_isometryCentralizer.mpr ⟨fun v => ?_,
      fun v => ?_⟩) hl
    · exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hΩO hg) v
    · rw [← LinearEquiv.mul_apply, hgx, LinearEquiv.mul_apply]
  · refine fixes_of_commute_of_eight hxo hQ h8 (mem_isometryCentralizer.mpr ⟨fun v => ?_,
      fun v => ?_⟩) (fun f hf v => ?_) y (hle hy)
    · exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hc v
    · rw [← LinearEquiv.mul_apply, hcx, LinearEquiv.mul_apply]
    · rw [← LinearEquiv.mul_apply, hcL f hf, LinearEquiv.mul_apply]

end WitOmBlk

end CFSG.StandardType
