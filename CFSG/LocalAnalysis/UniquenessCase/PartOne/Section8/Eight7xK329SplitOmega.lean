module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329KCThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitTwist
import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeD
import CFSG.RankThree.PartOne.KC.OrthogonalDerivedInLayer
import CFSG.RankThree.PartOne.KF.ClsOmega
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitOrder
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.RankThree.PartOne.S11d.OrthCaseH
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoOBlocks
import CFSG.LargeExtraspecial.PSL10USimple
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
import CFSG.Blueprint.SourceClassicalTransportLinear
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedLieAdmissible StatedOmega StatedQuadOdd StatedQuadPlus StatedQuadMinus)

open Polynomial Module
open CFSG.RankThree.PartOne.KCOrthogonal

open CFSG.RankThree.Classical2
open scoped Classical

section K329O4PPrivate

private theorem k329o4p_fixed_scalar
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) {m : V ≃ₗ[K] V} (hm : m ∈ isometryCentralizer Q x)
    (hcomm : ∀ f ∈ supportedFixedDerived Q x, ∀ v, m (f v) = f (m v))
    (h3 : 3 ≤ finrank K (fixedSpace x)) (hK : 2 < Nat.card K) :
    ∃ c : K, ∀ w : fixedSpace x,
      ((isometryRestrictFixed Q x ⟨m, hm⟩ : fixedSpace x →ₗ[K] fixedSpace x) w : V) =
        c • (w : V) := by
  have hQW := hx.polarBilin_fixed_nondegenerate
  let O := TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)
  let M : fixedSpace x →ₗ[K] fixedSpace x :=
    (isometryRestrictFixed Q x ⟨m, hm⟩ : fixedSpace x →ₗ[K] fixedSpace x)
  have hMcomm : ∀ g ∈ (⁅O, O⁆ : Subgroup (fixedSpace x ≃ₗ[K] fixedSpace x)),
      M ∘ₗ (g : fixedSpace x →ₗ[K] fixedSpace x) =
      (g : fixedSpace x →ₗ[K] fixedSpace x) ∘ₗ M := by
    intro g hg
    have hg' : (g : fixedSpace x ≃ₗ[K] fixedSpace x) ∈
        orthDerived (Q.comp (fixedSpace x).subtype) := hg
    obtain ⟨f, hf⟩ := restrictFixed_surjective hx (g : fixedSpace x ≃ₗ[K] fixedSpace x)
      (orthDerived_le_orthogonalGroup hg')
    have hfSD : f.1 ∈ supportedFixedDerived Q x :=
      mem_supportedFixedDerived.mpr ⟨f.2, by rw [hf]; exact hg'⟩
    ext w
    change ((M ((g : fixedSpace x →ₗ[K] fixedSpace x) w) : fixedSpace x) : V) =
      (((g : fixedSpace x →ₗ[K] fixedSpace x) (M w) : fixedSpace x) : V)
    have hMg : ((M ((g : fixedSpace x →ₗ[K] fixedSpace x) w) : fixedSpace x) : V) =
        m (((g : fixedSpace x →ₗ[K] fixedSpace x) w : fixedSpace x) : V) := by
      simp only [M]
      exact coe_isometryRestrictFixed (Q := Q) (x := x) ⟨m, hm⟩ _
    have hMw : ((M w : fixedSpace x) : V) = m (w : V) := by
      simp only [M]
      exact coe_isometryRestrictFixed (Q := Q) (x := x) ⟨m, hm⟩ _
    have hgw : (((g : fixedSpace x →ₗ[K] fixedSpace x) w : fixedSpace x) : V) =
        f.1 (w : V) := by
      rw [← hf]; exact coe_restrictFixed f w
    have hgMw : (((g : fixedSpace x →ₗ[K] fixedSpace x) (M w) : fixedSpace x) : V) =
        f.1 ((M w : fixedSpace x) : V) := by
      rw [← hf]; exact coe_restrictFixed f (M w)
    rw [hMg, hgw, hgMw, hMw]
    exact hcomm f.1 hfSD (w : V)
  obtain ⟨c, hc⟩ := (CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar
      hK (Q.comp (fixedSpace x).subtype) hQW h3).1 M |>.mp hMcomm
  refine ⟨c, fun w => ?_⟩
  show (M w : V) = c • (w : V)
  rw [hc]
  simp

private theorem k329o4p_isPerfect_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : Group.IsPerfect G) : Group.IsPerfect G' := by
  have : Group.IsPerfect G := h
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

private theorem k329o4p_supportedFixedDerived_perfect
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) (hK : Nat.card K = 8)
    (h3 : 3 ≤ finrank K (fixedSpace x)) :
    ⁅supportedFixedDerived Q x, supportedFixedDerived Q x⁆ = supportedFixedDerived Q x := by
  have hQ := hx.polarBilin_fixed_nondegenerate
  have hns : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype) := by
    rintro (⟨-, h3⟩ | ⟨⟨-, -⟩, h2 | h2⟩)
    · rw [hK] at h3; norm_num at h3
    · rw [hK] at h2; norm_num at h2
    · rw [hK] at h2; norm_num at h2
  have hder : DerivedCoverage (Q.comp (fixedSpace x).subtype) :=
    (orthogonal_regular_space_coverage _ hQ h3).2 hns
  have hODperf : Group.IsPerfect ↥(orthDerived (Q.comp (fixedSpace x).subtype)) := by
    refine k329o4p_isPerfect_of_mulEquiv ?_ hder.1
    exact (Subgroup.equivMapOfInjective
        (_root_.commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))
        (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)).subtype
        (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _))
  have hSDperf : Group.IsPerfect ↥(supportedFixedDerived Q x) :=
    k329o4p_isPerfect_of_mulEquiv (supportedFixedDerivedEquiv hx).symm hODperf
  exact Subgroup.isPerfect_iff.mp hSDperf

private theorem k329o4p_quad_no_root {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    (r : K) : r ^ 2 + r + 1 ≠ 0 := by
  intro h
  have hchar : CharP K 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 3) hK
  have h3 : (3 : K) ≠ 0 := by
    intro h3
    have h' := (CharP.cast_eq_zero_iff K 2 3).mp h3
    omega
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0] at h; norm_num at h
  have hr3 : r ^ 3 = 1 := by linear_combination (r - 1) * h
  let u : Kˣ := Units.mk0 r hr0
  have hu3 : u ^ 3 = 1 := by ext; simpa [u] using hr3
  have hu1 : u ≠ 1 := by
    intro hu
    have hr1 : r = 1 := congrArg Units.val hu
    rw [hr1] at h
    exact h3 (by linear_combination h)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : 3 ∣ Nat.card Kˣ := hord ▸ orderOf_dvd_natCard u
  rw [Nat.card_units, hK] at hdvd
  norm_num at hdvd

private theorem k329o4p_quad_irreducible {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) : Irreducible (X ^ 2 + X + 1 : K[X]) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have hnd : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
    rw [hnd]; norm_num
  · intro r hr
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hr
    exact k329o4p_quad_no_root hK r hr

private theorem k329o4p_primaryFactors_eq {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x : V ≃ₗ[K] V} (hx : x ^ 3 = 1) {b : K[X]}
    (hb : b ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors x.toLinearMap) :
    b = X - 1 ∨ b = X ^ 2 + X + 1 := by
  have hx3 : x.toLinearMap ^ 3 = 1 := by
    rw [← toLinearMap_pow, hx]
    rfl
  have haeval : aeval x.toLinearMap (X ^ 3 - C 1 : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, C_1, map_one, hx3, sub_self]
  have hdvd : b ∣ X ^ 3 - C 1 :=
    (CFSG.RankThree.PartOne.KCPrimary.mem_primaryFactors.mp hb).2.2.trans
      (minpoly.dvd K x.toLinearMap haeval)
  have hfac : (X ^ 3 - C 1 : K[X]) = (X - 1) * (X ^ 2 + X + 1) := by
    simp only [map_one]; ring
  rw [hfac] at hdvd
  have hbirr := CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hb
  have hbmonic := CFSG.RankThree.PartOne.KCPrimary.monic_of_mem_primaryFactors hb
  rcases hbirr.prime.dvd_or_dvd hdvd with h | h
  · left
    exact eq_of_monic_of_associated hbmonic (monic_X_sub_C 1)
      (hbirr.associated_of_dvd (irreducible_X_sub_C 1) h)
  · right
    exact eq_of_monic_of_associated hbmonic (by monicity!)
      (hbirr.associated_of_dvd (k329o4p_quad_irreducible hK) h)

private theorem k329o4p_commute_of_perfect_subgroup
    {n : ℕ} {K : Type} [Field K] [Finite K]
    (hΩ : StatedOmega (StatedQuadPlus n K) =
      (orthDerived (CFSG.LieType.Universal.Spin.quadPlus n K)).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K).toMonoidHom)
    {x : StatedOmega (StatedQuadPlus n K)}
    {S : Subgroup ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))}
    (hSΩ : S ≤ orthDerived (CFSG.LieType.Universal.Spin.quadPlus n K))
    (hSM : S ≤ isometryCentralizer (CFSG.LieType.Universal.Spin.quadPlus n K)
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K x))
    (hSperf : ⁅S, S⁆ = S)
    {R : Subgroup (StatedOmega (StatedQuadPlus n K))}
    (hRcomm : ⁅R, K329Lres x⁆ = ⊥)
    {g : StatedOmega (StatedQuadPlus n K)} (hg : g ∈ R) :
    ∀ f ∈ S, Commute (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K g) f := by
  intro f hf
  let φ := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K
  let H := StatedOmega (StatedQuadPlus n K)
  let Q : Subgroup (GL (Fin n ⊕ Fin n) K) := S.comap φ.toMonoidHom
  have hQH : Q ≤ H := by
    intro u hu
    show u ∈ StatedOmega (StatedQuadPlus n K)
    rw [hΩ]
    exact hSΩ hu
  let C : Subgroup H := Subgroup.centralizer ({x} : Set H)
  let P : Subgroup H := Q.subgroupOf H
  have hPC : P ≤ C := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have huS : φ (u : GL (Fin n ⊕ Fin n) K) ∈ S :=
      Subgroup.mem_comap.mp (Subgroup.mem_subgroupOf.mp hu)
    apply Subgroup.subtype_injective H
    rw [map_mul, map_mul]
    apply φ.injective
    rw [map_mul, map_mul]
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact ((mem_isometryCentralizer.mp (hSM huS)).2 v).symm
  have hPperf : ⁅P, P⁆ = P := by
    have e : ↥Q ≃* ↥P := (Subgroup.subgroupOfEquivOfLe hQH).symm
    have h1 : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.mpr (by
      apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective φ.surjective S,
        hSperf])
    exact Subgroup.isPerfect_iff.mp (k329o4p_isPerfect_of_mulEquiv e h1)
  have hPres : P ≤ K329Lres x := by
    show P ≤ K329Res C
    exact k329_perfect_le_res hPC hPperf
  have hfQ : φ.symm f ∈ Q := by
    show φ (φ.symm f) ∈ S
    rw [φ.apply_symm_apply]
    exact hf
  let u : H := ⟨φ.symm f, hQH hfQ⟩
  have hfP : u ∈ P := Subgroup.mem_subgroupOf.mpr hfQ
  have hcomm' : Commute g u := by
    rw [commute_iff_eq]
    exact (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hRcomm hg) u (hPres hfP)).symm
  have hmap := (hcomm'.map (Subgroup.subtype H)).map φ.toMonoidHom
  simpa [u, φ] using hmap

private theorem k329o4p_coord_commute
    {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {x : Module.End K V} (hsq : Squarefree (minpoly K x))
    {z z' : CFSG.RankThree.PartOne.KCPrimary.commutant x}
    {i : CFSG.RankThree.PartOne.KCPrimary.primaryFactors x}
    (h : ∀ v : CFSG.RankThree.PartOne.KCPrimary.primaryComponent x (i : K[X]),
      z.1 (z'.1 (v : V)) = z'.1 (z.1 (v : V))) :
    Commute ((CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq z) i)
      ((CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq z') i) := by
  rw [Commute]
  ext v
  rw [Module.End.mul_apply, Module.End.mul_apply]
  rw [CFSG.RankThree.PartOne.KCPrimary.coe_commutantEquivPi_apply,
    CFSG.RankThree.PartOne.KCPrimary.coe_commutantEquivPi_apply,
    CFSG.RankThree.PartOne.KCPrimary.coe_commutantEquivPi_apply,
    CFSG.RankThree.PartOne.KCPrimary.coe_commutantEquivPi_apply]
  exact h v

private theorem k329o4p_fixed_coord_commute
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {p : ℕ}
    (hx : OddOrderIsometry Q p x) (hp2 : Odd p) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep)
    (hdim : finrank K (fixedSpace x) ≤ 2)
    {m m' : V ≃ₗ[K] V} (hm : m ∈ isometryCentralizer Q x) (hmΩ : m ∈ orthDerived Q)
    (hm' : m' ∈ isometryCentralizer Q x) (hm'Ω : m' ∈ orthDerived Q)
    (v : CFSG.RankThree.PartOne.KCPrimary.primaryComponent x.toLinearMap (X - 1)) :
    m (m' (v : V)) = m' (m (v : V)) := by
  have hc := hx.restrict_commute_of_mem_orthDerived hp2 hQ hRep hdim hm hmΩ hm' hm'Ω
  have hv : (v : V) ∈ fixedSpace x := by
    rw [fixedSpace_eq_primaryComponent]; exact v.2
  have h1 := congrArg (fun e : fixedSpace x ≃ₗ[K] fixedSpace x => (e ⟨v, hv⟩ : V)) hc.eq
  simp only [LinearEquiv.mul_apply] at h1
  rw [coe_isometryRestrictFixed, coe_isometryRestrictFixed, coe_isometryRestrictFixed,
    coe_isometryRestrictFixed] at h1
  exact h1

private theorem k329o4p_recip_quad {K : Type} [Field K] :
    reciprocalPolynomial (X ^ 2 + X + 1 : K[X]) = X ^ 2 + X + 1 := by
  have hc : (X ^ 2 + X + 1 : K[X]).coeff 0 = 1 := by simp
  have hnd : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hrev : (X ^ 2 + X + 1 : K[X]).reverse = X ^ 2 + X + 1 := by
    ext n
    rw [coeff_reverse, hnd]
    rcases n with _ | _ | _ | n
    · rw [revAt_le (by norm_num)]; try simp [coeff_X, coeff_one]
    · rw [revAt_le (by norm_num)]; try simp [coeff_X, coeff_one]
    · rw [revAt_le (by norm_num)]; try simp [coeff_X, coeff_one]
    · rw [revAt_eq_self_of_lt (by omega)]
  rw [reciprocalPolynomial, hc, hrev]
  simp

end K329O4PPrivate

theorem k329_Z3_of_sq {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Q : (ι → F) → F} (hQ : ∀ (c : F) v, Q (c • v) = c ^ 2 * Q v) {v₀ : ι → F}
    (hv₀ : Q v₀ ≠ 0) : ∀ ω ∈ K329Zh (StatedOmega Q), ω ^ 3 = 1 → ω = 1 := by
  intro ω hω h3
  have h2 : (ω : GL ι F) ^ 2 = 1 :=
    CFSG.HardMathSupport.Malle.E27Lie.sq_eq_one_of_mem_statedScalars hQ hv₀ ω.2 hω
  have h3' : (ω : GL ι F) ^ 3 = 1 := by simpa using congrArg Subtype.val h3
  have h1 : (ω : GL ι F) = 1 := by
    calc (ω : GL ι F) = (ω : GL ι F) ^ 3 * ((ω : GL ι F) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3', h2]; simp
  exact Subtype.ext h1

theorem k329_Z3_POmegaPlus {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] :
    ∀ ω ∈ K329Zh (StatedOmega (StatedQuadPlus n K)), ω ^ 3 = 1 → ω = 1 :=
  k329_Z3_of_sq (CFSG.HardMathSupport.Malle.E27Lie.statedQuadPlus_smul n)
    (CFSG.HardMathSupport.Malle.E27Lie.statedQuadPlus_ne_zero hn K)

theorem k329_Z3_POmegaMinus {n : ℕ} {K : Type} [Field K] (b c : K) :
    ∀ ω ∈ K329Zh (StatedOmega (StatedQuadMinus n K b c)), ω ^ 3 = 1 → ω = 1 := by
  refine k329_Z3_of_sq (v₀ := Pi.single (Sum.inr (Sum.inr 0)) 1) (fun a v => ?_) ?_
  · simp only [StatedQuadMinus, Pi.smul_apply, smul_eq_mul]
    have hs : ∑ x, a * v (Sum.inl x) * (a * v (Sum.inr (Sum.inl x))) =
        a ^ 2 * ∑ i, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hs]
    ring
  · simp [StatedQuadMinus]

section K329O3FPrivate

private theorem k329o3f_fix_conj {X : Type} [Group X] (a : X) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj a) =
      Subgroup.centralizer ({a} : Set X) := by
  ext g
  rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem k329o3f_eight_of_pow {r e j : ℕ} (hr : r.Prime) (he : 1 ≤ e) (hj : 1 ≤ j)
    (h : (r ^ e) ^ j = 8) : r ^ e = 8 ∨ (r = 2 ∧ e = 1) := by
  have hr2 : r = 2 := by
    have h1 : r ∣ 2 ^ 3 := by
      have : r ∣ (r ^ e) ^ j := dvd_pow (dvd_pow_self r (by omega)) (by omega)
      rw [h] at this
      simpa using this
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h1)
  subst hr2
  have h2 : 2 ^ (e * j) = 2 ^ 3 := by rw [pow_mul]; simpa using h
  have h3 : e * j = 3 := Nat.pow_right_injective (le_refl 2) h2
  rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro j h3) with h4 | h4
  · exact Or.inr ⟨rfl, h4⟩
  · left
    rw [h4]
    norm_num

private theorem k329o3f_card_center_quot {G G' : Type} [Group G] [Group G'] (e : G ≃* G') :
    Nat.card (G ⧸ Subgroup.center G) = Nat.card (G' ⧸ Subgroup.center G') :=
  Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

private theorem k329o3f_map_normal {H G : Type} [Group H] [Group G] (f : H →* G)
    {A B : Subgroup H} (hAB : A ≤ B) (hn : (A.subgroupOf B).Normal) :
    ((A.map f).subgroupOf (B.map f)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hAB)]
  rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  exact ⟨b * a * b⁻¹, (Subgroup.normal_subgroupOf_iff hAB).mp hn a b ha hb, by simp⟩

private theorem k329o3f_not_quasisimple_of_comm {Γ : Type} [Group Γ] (h : ∀ a b : Γ, a * b = b * a) :
    ¬ CFSG.Open.IsQuasisimple Γ := by
  intro hq
  have hsimple : IsSimpleGroup (Γ ⧸ Subgroup.center Γ) := hq.2
  obtain ⟨q, hq1⟩ := exists_ne (1 : Γ ⧸ Subgroup.center Γ)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  apply hq1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  exact fun g => h g a

private theorem k329o3f_not_le_ker {H : Type} [Group H] (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (R : Subgroup H) (hRq : CFSG.Open.IsQuasisimple ↥R) :
    ¬ R ≤ (QuotientGroup.mk' Z).ker := by
  intro h
  have hRZ : R ≤ Subgroup.center H := by
    intro r hr
    have := h hr
    rw [QuotientGroup.ker_mk'] at this
    exact hZ this
  exact k329o3f_not_quasisimple_of_comm
    (fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hRZ a.2) b).symm) hRq

private theorem k329o3f_native {Q : Type} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q h⟩

private theorem k329o3f_component_image {H : Type} [Group H] [Finite H] (Z : Subgroup H)
    [Z.Normal] (hZ : Z ≤ Subgroup.center H) (x : H) (R : Subgroup H)
    (hRL : R ≤ K329Lres x) (hRn : (R.subgroupOf (K329Lres x)).Normal)
    (hRq : CFSG.Open.IsQuasisimple ↥R) :
    CFSG.Open.IsComponentOf (R.map (QuotientGroup.mk' Z))
      (Subgroup.centralizer ({(QuotientGroup.mk x : H ⧸ Z)} : Set (H ⧸ Z))) := by
  set π : H →* H ⧸ Z := QuotientGroup.mk' Z with hπ
  set C : Subgroup H := Subgroup.centralizer ({x} : Set H) with hC
  have hLC : K329Lres x ≤ C := Subgroup.map_subtype_le _
  have hLn : ((K329Lres x).subgroupOf C).Normal :=
    k329_res_normal (le_refl C) (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hπC : C.map π ≤ Subgroup.centralizer ({(QuotientGroup.mk x : H ⧸ Z)} : Set (H ⧸ Z)) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    change π c * π x = π x * π c
    rw [← map_mul, ← map_mul, this]
  have hCn : ((C.map π).subgroupOf
      (Subgroup.centralizer ({(QuotientGroup.mk x : H ⧸ Z)} : Set (H ⧸ Z)))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hπC]
    rintro _ g ⟨c, hc, rfl⟩ hg
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hhx : (QuotientGroup.mk (h * x * h⁻¹) : H ⧸ Z) = QuotientGroup.mk x := by
      change (QuotientGroup.mk h : H ⧸ Z) * QuotientGroup.mk x * (QuotientGroup.mk h)⁻¹ = _
      rw [mul_inv_eq_iff_eq_mul]
      exact hg
    obtain ⟨z, hzZ, hz⟩ : ∃ z ∈ Z, h * x * h⁻¹ = z * x := by
      refine ⟨h * x * h⁻¹ * x⁻¹, ?_, by group⟩
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hhx]
      simp
    have hzc : ∀ y : H, y * z = z * y := fun y => (Subgroup.mem_center_iff.mp (hZ hzZ) y)
    have hzc' : ∀ y : H, y * z⁻¹ = z⁻¹ * y := fun y =>
      (Subgroup.mem_center_iff.mp ((Subgroup.center H).inv_mem (hZ hzZ)) y)
    have h1 : h⁻¹ * x * h = z⁻¹ * x := by
      have e1 : h⁻¹ * (h * x * h⁻¹) * h = x := by group
      rw [hz] at e1
      have e2 : h⁻¹ * (z * x) * h = z * (h⁻¹ * x * h) := by
        have := hzc h⁻¹
        calc h⁻¹ * (z * x) * h = (h⁻¹ * z) * x * h := by group
          _ = (z * h⁻¹) * x * h := by rw [this]
          _ = z * (h⁻¹ * x * h) := by group
      rw [e2] at e1
      calc h⁻¹ * x * h = z⁻¹ * (z * (h⁻¹ * x * h)) := by group
        _ = z⁻¹ * x := by rw [e1]
    refine ⟨h * c * h⁻¹, ?_, by simp [π]⟩
    show h * c * h⁻¹ ∈ C
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    calc h * c * h⁻¹ * x = h * c * (h⁻¹ * x * h) * h⁻¹ := by group
      _ = h * c * (z⁻¹ * x) * h⁻¹ := by rw [h1]
      _ = h * (c * z⁻¹) * x * h⁻¹ := by group
      _ = h * (z⁻¹ * c) * x * h⁻¹ := by rw [hzc' c]
      _ = h * z⁻¹ * (c * x) * h⁻¹ := by group
      _ = h * z⁻¹ * (x * c) * h⁻¹ := by rw [hcx]
      _ = h * (z⁻¹ * x) * c * h⁻¹ := by group
      _ = h * (h⁻¹ * x * h) * c * h⁻¹ := by rw [h1]
      _ = x * (h * c * h⁻¹) := by group
  have hRC : R.map π ≤ (K329Lres x).map π := Subgroup.map_mono hRL
  have hRn' := k329o3f_map_normal π hRL hRn
  have hLC' : (K329Lres x).map π ≤ C.map π := Subgroup.map_mono hLC
  have hLn' := k329o3f_map_normal π hLC hLn
  have hnot : ¬ R ≤ π.ker := k329o3f_not_le_ker Z hZ R hRq
  have hq : CFSG.Open.IsQuasisimple ↥(R.map π) := by
    have := CFSG.LocalCores.isQuasisimple_map (k329o3f_native hRq) π hnot
    exact ⟨Group.isPerfect_def.mp this.1, this.2.1⟩
  exact ⟨hRC.trans (hLC'.trans hπC),
    .step hRC hRn' (.step hLC' hLn' (.step hπC hCn (.refl _))), hq⟩

private theorem k329o3forthbig_pow_card_dvd_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (h : ∀ i ∈ s, (3 : ℤ) ∣ f i) : (3 : ℤ) ^ s.card ∣ ∏ i ∈ s, f i := by
  have h' := Finset.prod_dvd_prod_of_dvd (s := s) (f := fun _ => (3 : ℤ)) (g := f) h
  rwa [Finset.prod_const] at h'

private theorem k329o3forthbig_27_dvd_order_formula (q e k : ℕ) (he : 3 ≤ e) (hk : 3 ≤ k)
    (d : ℤ) :
    (27 : ℤ) ∣ 2 * (q : ℤ) ^ e * d * ∏ i ∈ Finset.Icc 1 k, (((q : ℤ) ^ 2) ^ i - 1) := by
  by_cases h3 : (3 : ℤ) ∣ (q : ℤ)
  · obtain ⟨t, ht⟩ := h3
    have h27 : (27 : ℤ) ∣ (q : ℤ) ^ 3 := ⟨t ^ 3, by rw [ht]; ring⟩
    have hpow : (q : ℤ) ^ 3 ∣ (q : ℤ) ^ e := pow_dvd_pow (q : ℤ) he
    have hA : (27 : ℤ) ∣ 2 * (q : ℤ) ^ e * d := by
      have h := dvd_mul_of_dvd_right (h27.trans hpow) (2 * d)
      convert h using 1
      ring
    exact dvd_mul_of_dvd_left hA _
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hne : (q : ZMod 3) ≠ 0 := fun h =>
      h3 ((ZMod.intCast_zmod_eq_zero_iff_dvd (q : ℤ) 3).mp (by simpa using h))
    have hsq : (q : ZMod 3) ^ 2 = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one hne
    have hdvd_sq : (3 : ℤ) ∣ (q : ℤ) ^ 2 - 1 := by
      have hkey : (((q : ℤ) ^ 2 - 1 : ℤ) : ZMod 3) = 0 := by
        push_cast
        rw [hsq]
        ring
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 2 - 1) 3).mp hkey
    have hf : ∀ i ∈ Finset.Icc 1 k, (3 : ℤ) ∣ (((q : ℤ) ^ 2) ^ i - 1) := by
      intro i _
      have hdiv := sub_dvd_pow_sub_pow ((q : ℤ) ^ 2) 1 i
      simp only [one_pow] at hdiv
      exact hdvd_sq.trans hdiv
    have hprod := k329o3forthbig_pow_card_dvd_prod (Finset.Icc 1 k)
      (fun i => (((q : ℤ) ^ 2) ^ i - 1)) hf
    have hcard : 3 ≤ (Finset.Icc 1 k).card := by
      have hsub : ({1, 2, 3} : Finset ℕ) ⊆ Finset.Icc 1 k := by
        intro i hi
        rw [Finset.mem_Icc]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl
        · exact ⟨le_rfl, by omega⟩
        · exact ⟨by norm_num, by omega⟩
        · exact ⟨by norm_num, by omega⟩
      have hcl := Finset.card_le_card hsub
      rwa [show ({1, 2, 3} : Finset ℕ).card = 3 by decide] at hcl
    have h27prod : (27 : ℤ) ∣ ∏ i ∈ Finset.Icc 1 k, (((q : ℤ) ^ 2) ^ i - 1) := by
      have hpow : (3 : ℤ) ^ 3 ∣ (3 : ℤ) ^ (Finset.Icc 1 k).card := pow_dvd_pow (3 : ℤ) hcard
      have htrans := hpow.trans hprod
      norm_num at htrans
      exact htrans
    exact dvd_mul_of_dvd_right h27prod (2 * (q : ℤ) ^ e * d)

private theorem k329o3forthbig_27_dvd_orthogonalGroup
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h7 : 7 ≤ Module.finrank K V) :
    (27 : ℤ) ∣ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) := by
  rcases Nat.even_or_odd (Module.finrank K V) with heven | hodd
  · obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp heven
    have hk4 : 4 ≤ k := by omega
    let m := k - 1
    have hm : k = m + 1 := by omega
    have hm3 : 3 ≤ m := by omega
    have hdim : Module.finrank K V = 2 * (m + 1) := by rw [hk, hm]
    have he : 3 ≤ m * (m + 1) := by
      have h : 3 * 1 ≤ m * (m + 1) := Nat.mul_le_mul hm3 (by omega)
      omega
    by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
    · rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (m := m) (ε := 1) hQ hdim
        (Or.inl ⟨rfl, hplus⟩)]
      exact k329o3forthbig_27_dvd_order_formula (Nat.card K) (m * (m + 1)) m he hm3
        ((Nat.card K : ℤ) ^ (m + 1) - 1)
    · rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (m := m) (ε := -1) hQ hdim
        (Or.inr ⟨rfl, hplus⟩)]
      exact k329o3forthbig_27_dvd_order_formula (Nat.card K) (m * (m + 1)) m he hm3
        ((Nat.card K : ℤ) ^ (m + 1) - (-1))
  · obtain ⟨n, hn⟩ := odd_iff_exists_bit1.mp hodd
    have hn3 : 3 ≤ n := by omega
    have hchar : ringChar K ≠ 2 := by
      intro h
      have : CharP K 2 := h ▸ ringChar.charP K
      have heven := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
      rw [hn] at heven
      obtain ⟨j, hj⟩ := even_iff_exists_two_mul.mp heven
      omega
    have hdim : Module.finrank K V = 2 * n + 1 := hn
    have he : 3 ≤ n ^ 2 := by nlinarith [hn3]
    rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (n := n) (V := V) (Q := Q)
      hchar hQ hdim]
    simpa using k329o3forthbig_27_dvd_order_formula (Nat.card K) (n ^ 2) n he hn3 1

private theorem k329o3forthbig_27_dvd_orthDerived
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h7 : 7 ≤ Module.finrank K V)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    27 ∣ Nat.card ↥(orthDerived Q) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  let O := TauCeti.QuadraticMap.orthogonalGroup Q
  obtain ⟨-, -, -, -, -, -, hodd, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have h27O : (27 : ℤ) ∣ (Nat.card O : ℤ) := k329o3forthbig_27_dvd_orthogonalGroup Q hQ h7
  have h27Onat : 27 ∣ Nat.card O := Int.natCast_dvd_natCast.mp h27O
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ^ 3 ∣ Nat.card ↥O := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num]
    exact h27Onat
  obtain ⟨P, hPcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥O) (p := 3) (n := 3) hdvd
  have hmap_le : P.map O.subtype ≤ orthDerived Q := by
    rintro _ ⟨g, hgP, rfl⟩
    refine hodd (O.subtype g) g.2 ?_
    rw [orderOf_injective O.subtype O.subtype_injective g]
    have hord : orderOf g ∣ 27 := by
      have h := P.orderOf_dvd_natCard hgP
      rw [hPcard] at h
      norm_num at h
      exact h
    exact Odd.of_dvd_nat ⟨13, by norm_num⟩ hord
  have hcardmap : Nat.card (P.map O.subtype) = Nat.card P :=
    Subgroup.card_map_of_injective O.subtype_injective
  have h27P : Nat.card (P.map O.subtype) = 27 := by rw [hcardmap, hPcard]; norm_num
  have hle := Subgroup.card_dvd_of_le hmap_le
  rwa [h27P] at hle

private theorem k329o3f_orth_large_ne_504 {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h7 : 7 ≤ Module.finrank K V)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Nat.card (↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q)) ≠ 504 := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite ↥(orthDerived Q) :=
    Finite.of_injective (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[K] V))
      (fun _ _ h => Subtype.ext h)
  have : Finite ↥(Subgroup.center ↥(orthDerived Q)) :=
    Finite.of_injective (fun x : ↥(Subgroup.center ↥(orthDerived Q)) => (x : V ≃ₗ[K] V))
      (fun _ _ h => Subtype.ext (Subtype.ext h))
  obtain ⟨-, hcenter, hZcard, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have h27Ω : 27 ∣ Nat.card ↥(orthDerived Q) := k329o3forthbig_27_dvd_orthDerived Q hQ h7 hT
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(orthDerived Q))
  have hZle : Nat.card (Subgroup.center ↥(orthDerived Q)) ≤ 2 := by
    rw [hcenter]
    exact hZcard
  have hZpos : 0 < Nat.card (Subgroup.center ↥(orthDerived Q)) := by
    have : Nonempty ↥(Subgroup.center ↥(orthDerived Q)) := ⟨1, Subgroup.one_mem _⟩
    exact Nat.card_pos
  have hZcases : Nat.card (Subgroup.center ↥(orthDerived Q)) = 1 ∨
      Nat.card (Subgroup.center ↥(orthDerived Q)) = 2 := by
    by_cases h1 : Nat.card (Subgroup.center ↥(orthDerived Q)) = 1
    · exact Or.inl h1
    · right
      omega
  have hZcop : Nat.Coprime 27 (Nat.card (Subgroup.center ↥(orthDerived Q))) := by
    rcases hZcases with h | h <;> rw [h] <;> decide
  have hdvd : 27 ∣ Nat.card (↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q)) := by
    have hdiv : 27 ∣ Nat.card (↥(orthDerived Q) ⧸ Subgroup.center ↥(orthDerived Q)) *
        Nat.card (Subgroup.center ↥(orthDerived Q)) := by
      rw [← hcard]
      exact h27Ω
    exact (hZcop.dvd_mul_right).mp hdiv
  intro h504
  exact absurd (h504 ▸ hdvd) (by norm_num)

private theorem k329o3fclassical_card_eq_char_pow (E : Type) [Field E] [Fintype E] :
    ∃ f : ℕ, 1 ≤ f ∧ (ringChar E).Prime ∧ Nat.card E = (ringChar E) ^ f := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card E (ringChar E)
  exact ⟨(n : ℕ), Nat.succ_le_of_lt n.pos, hp, by rw [Nat.card_eq_fintype_card, hcard]⟩

private noncomputable def k329o3fclassical_centerQuotientEquiv {X G : Type} [Group X] [Group G]
    (e : X ≃* G) : X ⧸ Subgroup.center X ≃* G ⧸ Subgroup.center G :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

private theorem k329o3fclassical_sl {q : ℕ} {X : Type} [Group X]
    (m j : ℕ) (E : Type) [Field E] [Fintype E]
    (hm : 2 ≤ m) (hj : 1 ≤ j) (hcardE : Fintype.card E = q ^ j)
    (hm4 : m = 2 → 4 ≤ Fintype.card E)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin m) E)
    (hc : Nat.card (X ⧸ Subgroup.center X) = 504) : ∃ j : ℕ, 1 ≤ j ∧ q ^ j = 8 := by
  obtain ⟨f, hf, hprime, hcard⟩ := k329o3fclassical_card_eq_char_pow E
  have hpow : (ringChar E) ^ f = Fintype.card E := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard.symm
  have hAdm : StatedLieAdmissible .PSL m (ringChar E) f := by
    refine ⟨hprime, hf, hm, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      have h4 := hm4 h.1
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      have h4 := hm4 h.1
      omega
  have e₂ : X ⧸ Subgroup.center X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL m E) :=
    (k329o3fclassical_centerQuotientEquiv e).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)
  have hmodel : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSL m (ringChar E) f :=
    ⟨hAdm, E, inferInstance, inferInstance, hcard, ⟨e₂⟩⟩
  have hLie : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSL m (ringChar E) f :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hmodel⟩
  obtain ⟨-, -, h504⟩ := k329_S2_order504 (by omega : m ≠ 0) hLie hc
  exact ⟨j, hj, by rw [← hcardE, ← hpow, h504]⟩

private theorem k329o3fclassical_su {q : ℕ} {X : Type} [Group X]
    (m j q' : ℕ) (E : Type) [Field E] [Fintype E]
    (hm : 3 ≤ m) (_hj : 1 ≤ j) (hqq : q' = q ^ j)
    (hcardE : Fintype.card E = q' ^ 2) (hne : (m, q') ≠ (3, 2))
    (e : X ≃* ↥(CFSG.Open.StatedSU m q' E))
    (hc : Nat.card (X ⧸ Subgroup.center X) = 504) : ∃ j : ℕ, 1 ≤ j ∧ q ^ j = 8 := by
  obtain ⟨f, hf, hprime, hcard⟩ := k329o3fclassical_card_eq_char_pow E
  have hq2 : q' ^ 2 = (ringChar E) ^ f := by
    rw [← hcardE, ← Nat.card_eq_fintype_card, hcard]
  have hdvd : q' ∣ (ringChar E) ^ f := by
    rw [← hq2]
    exact dvd_pow_self q' (by norm_num)
  obtain ⟨a, -, hqa⟩ := (Nat.dvd_prime_pow hprime).1 hdvd
  have ha : 1 ≤ a := by
    have h2E : 2 ≤ Fintype.card E := by
      have := Fintype.one_lt_card (α := E)
      omega
    by_contra h
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero] at hqa
    rw [hqa] at hcardE
    norm_num at hcardE
    omega
  subst hqa
  have hF : Nat.card E = ((ringChar E) ^ a) ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact hcardE
  have : Fact (ringChar E).Prime := ⟨hprime⟩
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := E) (p := ringChar E) (f := a) (n := m) hF hm hne).2
  have e₂ : X ⧸ Subgroup.center X ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU m ((ringChar E) ^ a) E) :=
    (k329o3fclassical_centerQuotientEquiv e).trans (QuotientGroup.quotientMulEquivOfEq hZ)
  have hAdm : StatedLieAdmissible .PSU m (ringChar E) a := ⟨hprime, ha, hm, hne⟩
  have hmodel : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSU m (ringChar E) a :=
    ⟨hAdm, E, inferInstance, inferInstance, hF, ⟨e₂⟩⟩
  have hLie : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU m (ringChar E) a :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hmodel⟩
  obtain ⟨hcontra, -, -⟩ := k329_S2_order504 (by omega : m ≠ 0) hLie hc
  exact absurd hcontra (by decide)

private theorem k329o3fclassical_sp {q : ℕ} {X : Type} [Group X]
    (K' : Type) [Field K'] [Fintype K'] (_hKcard : Nat.card K' = q)
    (s : ℕ) (hs : 2 ≤ s) (hne : (s, Nat.card K') ≠ (2, 2))
    (e : X ≃* ↥(CFSG.Open.StatedSp s K'))
    (hc : Nat.card (X ⧸ Subgroup.center X) = 504) : ∃ j : ℕ, 1 ≤ j ∧ q ^ j = 8 := by
  obtain ⟨f, hf, hprime, hcard⟩ := k329o3fclassical_card_eq_char_pow K'
  have hne' : (s, (ringChar K') ^ f) ≠ (2, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    exact hne (Prod.ext h.1 (by rw [hcard]; exact h.2))
  have hAdm : StatedLieAdmissible .PSp s (ringChar K') f := ⟨hprime, hf, hs, hne'⟩
  have e₂ : X ⧸ Subgroup.center X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp s K') :=
    (k329o3fclassical_centerQuotientEquiv e).trans
      (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv s K')
  have hmodel : CFSG.Open.StatedClassicalModel (X ⧸ Subgroup.center X) .PSp s (ringChar K') f :=
    ⟨hAdm, K', inferInstance, inferInstance, hcard, ⟨e₂⟩⟩
  have hLie : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSp s (ringChar K') f :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hmodel⟩
  obtain ⟨hcontra, -, -⟩ := k329_S2_order504 (by omega : s ≠ 0) hLie hc
  exact absurd hcontra (by decide)

private theorem k329o3f_classical_504 {ℓ q : ℕ} {X : Type} [Group X] [Finite X]
    (hX : (∃ (m j : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 2 ≤ m ∧ 1 ≤ j ∧
          ringChar E = ℓ ∧ Fintype.card E = q ^ j ∧ (m = 2 → 4 ≤ Fintype.card E) ∧
          Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin m) E))
      ∨ (∃ (m j q' : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 3 ≤ m ∧ 1 ≤ j ∧
          ringChar E = ℓ ∧ q' = q ^ j ∧ Fintype.card E = q' ^ 2 ∧ (m, q') ≠ (3, 2) ∧
          Nonempty (X ≃* ↥(CFSG.Open.StatedSU m q' E)))
      ∨ (∃ (K' : Type) (_ : Field K') (_ : Fintype K'), Nat.card K' = q ∧ ringChar K' = ℓ ∧
          ∃ s : ℕ, 2 ≤ s ∧ (s, Nat.card K') ≠ (2, 2) ∧
            Nonempty (X ≃* ↥(CFSG.Open.StatedSp s K'))))
    (hc : Nat.card (X ⧸ Subgroup.center X) = 504) : ∃ j : ℕ, 1 ≤ j ∧ q ^ j = 8 := by
  rcases hX with h1 | h2 | h3
  · obtain ⟨m, j, E, hField, hFintype, hm, hj, -, hcardE, hm4, ⟨e⟩⟩ := h1
    let : Field E := hField
    let : Fintype E := hFintype
    exact k329o3fclassical_sl m j E hm hj hcardE hm4 e hc
  · obtain ⟨m, j, q', E, hField, hFintype, hm, hj, -, hqq, hcardE, hne, ⟨e⟩⟩ := h2
    let : Field E := hField
    let : Fintype E := hFintype
    exact k329o3fclassical_su m j q' E hm hj hqq hcardE hne e hc
  · obtain ⟨K', hField, hFintype, hKcard, -, s, hs, hne, ⟨e⟩⟩ := h3
    let : Field K' := hField
    let : Fintype K' := hFintype
    exact k329o3fclassical_sp K' hKcard s hs hne e hc

private theorem k329o3f_orthFactor_504 {ℓ q : ℕ} {X : Type} [Group X] [Finite X]
    (hfac : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFactorOver ℓ q X)
    (hc : Nat.card (X ⧸ Subgroup.center X) = 504) : ∃ j : ℕ, 1 ≤ j ∧ q ^ j = 8 := by
  rcases hfac with h1 | h2 | h3 | ⟨K', _, _, V, _, _, _, Q, -, -, hQ, h7, hT, ⟨e⟩⟩
  · exact k329o3f_classical_504 (Or.inl h1) hc
  · exact k329o3f_classical_504 (Or.inr (Or.inl h2)) hc
  · exact k329o3f_classical_504 (Or.inr (Or.inr h3)) hc
  · exact absurd ((k329o3f_card_center_quot e).symm.trans hc)
      (k329o3f_orth_large_ne_504 Q hQ h7 hT)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp in
private theorem k329o3f_reduction {t : CFSG.Open.StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {G : Type} [Group G] {n r e : ℕ}
    (hG : CFSG.Open.StatedClassicalModel G t n r e) (hr : r ≠ 3) (a : G) (ha : a ^ 3 = 1)
    (J : Subgroup G) (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set G)))
    (hJc : Nat.card (↥J ⧸ Subgroup.center ↥J) = 504) : r ^ e = 8 ∨ (r = 2 ∧ e = 1) := by
  have hadm := hG.1
  have hJ' : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj a)) := by
    rw [k329o3f_fix_conj]
    exact hJ
  obtain ⟨X, _, _, hX, hfac, -, g, hg, hk⟩ :=
    exists_lieFactor_of_component_conj_omega_card slFactorFacts_holds suFactorFacts_holds
      omegaFactorField_holds Nat.prime_three (by norm_num) (Or.inr ht) hG
      (Ne.symm hr) a ha J hJ'
  obtain ⟨eq⟩ := nonempty_centralQuotient_mulEquiv hX.perfect g hg hk
  obtain ⟨j, hj, hq⟩ := k329o3f_orthFactor_504 hfac
    ((Nat.card_congr eq.toEquiv).trans hJc)
  exact k329o3f_eight_of_pow hadm.1 hadm.2.1 hj hq

private theorem k329o3f_zh_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) (H : Subgroup (GL ι K)) : K329Zh H = ⊥ := by
  have hunits : Subsingleton Kˣ := by
    have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    exact (Nat.card_eq_one_iff_unique.mp h1).1
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : (x : GL ι K) ∈ CFSG.Open.StatedScalars ι K := hx
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hx'
  rw [Subsingleton.elim c 1, map_one] at hc
  exact Subtype.ext hc.symm

private theorem k329o3f_perfectResidual_map {G G' : Type} [Group G] [Group G'] [Finite G]
    (f : G →* G') (hf : Function.Surjective f) :
    (CFSG.perfectResidual G).map f = CFSG.perfectResidual G' := by
  have hres : ∃ n, CFSG.perfectResidual G = derivedSeries G n :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_derivedSeries
  apply le_antisymm
  · apply le_iInf
    intro n
    exact (Subgroup.map_mono (iInf_le _ n)).trans (map_derivedSeries_le_derivedSeries f n)
  · obtain ⟨n, hn⟩ := hres
    have hbound := derivedSeries_le_map_derivedSeries hf n
    rw [← hn] at hbound
    exact (iInf_le _ n).trans hbound

private theorem k329o3f_image {P Q : Type} [Group P] [Group Q] (f : P →* Q) (R : Subgroup P)
    (hR : CFSG.Open.IsQuasisimple ↥R) (hnot : ¬ R ≤ f.ker) :
    CFSG.Open.IsQuasisimple ↥(R.map f) ∧
      Nat.card (↥(R.map f) ⧸ Subgroup.center ↥(R.map f)) =
        Nat.card (↥R ⧸ Subgroup.center ↥R) := by
  have hRn := k329o3f_native hR
  have hf : Function.Surjective (f.subgroupMap R) := f.subgroupMap_surjective R
  have hker : (f.subgroupMap R).ker ≤ Subgroup.center ↥R := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hRn (f.subgroupMap R).normal_ker with h | h
    · refine absurd (fun x hx => ?_) hnot
      have hx' : (⟨x, hx⟩ : R) ∈ (f.subgroupMap R).ker := by rw [h]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hx' ⊢
      exact congrArg Subtype.val hx'
    · exact h
  have hq := CFSG.LocalCores.isQuasisimple_of_surjective hRn (f.subgroupMap R) hf hker
  refine ⟨⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩, ?_⟩
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hRn.1 (f.subgroupMap R) hf hker
  let g : ↥R ⧸ Subgroup.center ↥R →* ↥(R.map f) ⧸ Subgroup.center ↥(R.map f) :=
    QuotientGroup.map _ _ (f.subgroupMap R) (le_of_eq hcomap.symm)
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro q hq1
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (f.subgroupMap R) a ∈ Subgroup.center ↥(R.map f) :=
      (QuotientGroup.eq_one_iff _).mp hq1
    have h2 : a ∈ (Subgroup.center ↥(R.map f)).comap (f.subgroupMap R) := h1
    rw [hcomap] at h2
    exact (QuotientGroup.eq_one_iff _).mpr h2
  have hsurj : Function.Surjective g := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨QuotientGroup.mk a, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)).symm

private theorem k329o3f_centralizer_map {H H' : Type} [Group H] [Group H'] (f : H →* H')
    (hf : Function.Injective f) (x : H) :
    (Subgroup.centralizer ({x} : Set H)).map f =
      Subgroup.centralizer ({f x} : Set H') ⊓ f.range := by
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => ?_, ⟨c, rfl⟩⟩
    rw [Set.mem_singleton_iff] at hy
    rw [hy, ← map_mul, ← map_mul]
    exact congrArg f (Subgroup.mem_centralizer_iff.mp hc x (Set.mem_singleton x))
  · rintro y ⟨hy, ⟨c, rfl⟩⟩
    refine Subgroup.mem_map.mpr ⟨c, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_, rfl⟩
    rw [Set.mem_singleton_iff] at hz
    have hz' : f z ∈ ({f x} : Set H') := by
      rw [Set.mem_singleton_iff]
      exact congrArg f hz
    have h := Subgroup.mem_centralizer_iff.mp hy (f z) hz'
    rw [← map_mul, ← map_mul] at h
    exact hf h

private theorem k329o3f_bridge {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (Q : QuadraticForm K (ι → K)) (x : ↥(StatedOmega ⇑Q)) :
    (K329Lres x).map ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom.comp
        (StatedOmega ⇑Q).subtype) =
      K329Res (isometryCentralizer Q
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K (x : GL ι K))) := by
  let θ := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K
  let H := StatedOmega ⇑Q
  let xe : (ι → K) ≃ₗ[K] (ι → K) := θ (x : GL ι K)
  let Θ : ↥H →* (ι → K) ≃ₗ[K] (ι → K) := θ.toMonoidHom.comp H.subtype
  have hFinV : Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
    Finite.of_injective (fun e : (ι → K) ≃ₗ[K] (ι → K) => (e : _ → _))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  let M : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) := isometryCentralizer Q xe
  let C0 : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) :=
    Subgroup.centralizer ({xe} : Set ((ι → K) ≃ₗ[K] (ι → K)))
  have hΘinj : Function.Injective Θ := θ.injective.comp (Subgroup.subtype_injective H)
  have hH : H = (orthDerived Q).comap θ.toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Q) (Q₀ := ⇑Q) rfl
  have hrange : Θ.range = orthDerived Q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hH,
      Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr θ.surjective, top_inf_eq]
  have hMO : M ≤ TauCeti.QuadraticMap.orthogonalGroup Q := inf_le_left
  have hMC : M ≤ C0 := inf_le_right
  have hcommM : ⁅M, M⁆ ≤ M := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  have hcommC : ⁅M, M⁆ ≤ C0 := hcommM.trans hMC
  have hcommO : ⁅M, M⁆ ≤ orthDerived Q := by
    rw [orthDerived]
    exact Subgroup.commutator_mono hMO hMO
  have hcomm : ⁅M, M⁆ ≤ C0 ⊓ orthDerived Q := le_inf hcommC hcommO
  have hle : C0 ⊓ orthDerived Q ≤ M :=
    le_inf (fun g hg => orthDerived_le_orthogonalGroup hg.2) (fun g hg => hg.1)
  have hstep : (K329Res (Subgroup.centralizer ({x} : Set ↥H))).map Θ = K329Res M := by
    rw [k329_res_map Θ (Subgroup.centralizer ({x} : Set ↥H)),
      k329o3f_centralizer_map Θ hΘinj x, hrange]
    exact (@k329_res_eq_of_commutator_le _ _ hFinV _ _ hle hcomm).symm
  exact hstep

private theorem k329o3fq2fixend_orth_card_le_120
    {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (QW : QuadraticForm K W)
    (hQW : (QuadraticMap.polarBilin QW).Nondegenerate) (hK : Nat.card K = 2)
    {m : ℕ} (hm : m ≤ 1) (hdim : Module.finrank K W = 2 * (m + 1)) :
    Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup QW) ≤ 120 := by
  by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType QW
  · have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
      (K := K) (V := W) (Q := QW) hQW (m := m) hdim (Or.inl ⟨rfl, hplus⟩)
    have hbound : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup QW) : ℤ) ≤ 120 := by
      rw [hcard, hK]
      interval_cases m <;> simp
    exact_mod_cast hbound
  · have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
      (K := K) (V := W) (Q := QW) hQW (m := m) hdim (Or.inr ⟨rfl, hplus⟩)
    have hbound : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup QW) : ℤ) ≤ 120 := by
      rw [hcard, hK]
      interval_cases m <;> simp
    exact_mod_cast hbound

private theorem k329o3fq2fixend_center_quot_le_orth
    {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (QW : QuadraticForm K W)
    (J : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup QW)) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≤
      Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup QW) := by
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  refine (Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center ↥J))
    (QuotientGroup.mk'_surjective (Subgroup.center ↥J))).trans ?_
  exact Nat.card_le_card_of_injective (fun x : ↥J => x.1) (fun a b h => Subtype.ext h)

private theorem k329o3f_q_two_fixed_ne6 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (QW : QuadraticForm K W) (hQW : (QuadraticMap.polarBilin QW).Nondegenerate)
    (hdim : Module.finrank K W ≠ 6)
    (J : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup QW))
    (hJL : J ≤ CFSG.perfectResidual ↥(TauCeti.QuadraticMap.orthogonalGroup QW))
    (hJn : (J.subgroupOf
      (CFSG.perfectResidual ↥(TauCeti.QuadraticMap.orthogonalGroup QW))).Normal)
    (hJq : CFSG.Open.IsQuasisimple ↥J) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 504 := by
  classical
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 1) (by
    rw [hK]; norm_num)
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  let O := TauCeti.QuadraticMap.orthogonalGroup QW
  have hbound : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥O :=
    k329o3fq2fixend_center_quot_le_orth QW J
  have heven : Even (Module.finrank K W) :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo QW hQW
  obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp heven
  by_cases hk2 : k ≤ 2
  · have hsmall : Nat.card ↥O < 504 := by
      interval_cases k
      · have hdim0 : Module.finrank K W = 0 := by omega
        have hsub : Subsingleton W := Module.finrank_zero_iff.mp hdim0
        have hsubO : Subsingleton ↥O :=
          ⟨fun a b => Subtype.ext (LinearEquiv.ext fun w => Subsingleton.elim _ _)⟩
        have hcard : Nat.card ↥O ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsubO
        omega
      · have h : Nat.card ↥O ≤ 120 :=
          k329o3fq2fixend_orth_card_le_120 QW hQW hK (m := 0) (by omega) (by omega)
        omega
      · have h : Nat.card ↥O ≤ 120 :=
          k329o3fq2fixend_orth_card_le_120 QW hQW hK (m := 1) (by omega) (by omega)
        omega
    intro h504
    omega
  · have hk4 : 4 ≤ k := by
      by_cases h3 : k = 3
      · exact absurd (by omega) hdim
      · omega
    have h7 : 7 ≤ Module.finrank K W := by omega
    have h3s : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, QW u = 0 :=
      CFSG.RankThree.PartOne.exists_threeSingular_of_dim QW hQW (m := k) hk4 hk
    have hΩq_native : CFSG.IsQuasisimple ↥(orthDerived QW) :=
      CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hQW h3s
    have hΩq : CFSG.Open.IsQuasisimple ↥(orthDerived QW) :=
      ⟨Group.isPerfect_def.mp hΩq_native.1, hΩq_native.2.1⟩
    have hperf : ⁅orthDerived QW, orthDerived QW⁆ = orthDerived QW :=
      Subgroup.isPerfect_iff.1 hΩq_native.1
    have hΩle : orthDerived QW ≤ O :=
      CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup
    have hcommO : ⁅O, O⁆ ≤ orthDerived QW := le_rfl
    have hPmap : (CFSG.perfectResidual ↥O).map O.subtype = orthDerived QW :=
      (k329_res_eq_of_commutator_le hΩle hcommO).trans
        (le_antisymm (Subgroup.map_subtype_le _) (k329_perfect_le_res le_rfl hperf))
    let J' : Subgroup (W ≃ₗ[K] W) := J.map O.subtype
    have hJ'le : J' ≤ orthDerived QW := by
      have h := Subgroup.map_mono (f := O.subtype) hJL
      rw [hPmap] at h
      exact h
    have hJ'n : (J'.subgroupOf (orthDerived QW)).Normal := by
      have h := k329o3f_map_normal O.subtype hJL hJn
      rw [hPmap] at h
      exact h
    have hnot : ¬ J ≤ O.subtype.ker := by
      intro hle
      have hker : O.subtype.ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff O.subtype).mpr (Subgroup.subtype_injective O)
      rw [hker] at hle
      exact k329o3f_not_quasisimple_of_comm
        (fun a b => Subtype.ext (by
          have ha1 : (a : ↥O) = 1 := Subgroup.mem_bot.mp (hle a.2)
          have hb1 : (b : ↥O) = 1 := Subgroup.mem_bot.mp (hle b.2)
          show (a : ↥O) * (b : ↥O) = (b : ↥O) * (a : ↥O)
          rw [ha1, hb1])) hJq
    obtain ⟨hJ'q, hJ'c⟩ := k329o3f_image O.subtype J hJq hnot
    obtain ⟨_, hi⟩ := k329_normal_quasisimple_eq_factor (fun _ : Unit => orthDerived QW)
      (fun _ => hΩq) (fun i j hij => absurd (Subsingleton.elim i j) hij) J'
      (by rw [iSup_const]; exact hJ'le) (by rw [iSup_const]; exact hJ'n) hJ'q
    have hJ'eq : J.map O.subtype = orthDerived QW := hi
    have hc : Nat.card (↥J ⧸ Subgroup.center ↥J) =
        Nat.card (↥(orthDerived QW) ⧸ Subgroup.center ↥(orthDerived QW)) := by
      rw [hJ'eq] at hJ'c
      exact hJ'c.symm
    exact fun h504 => k329o3f_orth_large_ne_504 QW hQW h7 h3s (hc ▸ h504)

private theorem k329o3fq2fixsix_open {Q : Type} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨Group.isPerfect_def.mp h.1, h.2.1⟩

private theorem k329o3fq2fixsix_center_quot
    {K : Type} [Field K] [Finite K]
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (QW : QuadraticForm K W)
    (hΩq : CFSG.Open.IsQuasisimple ↥(CFSG.RankThree.Classical2.orthDerived QW))
    (J : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup QW))
    (hJL : J ≤ CFSG.perfectResidual ↥(TauCeti.QuadraticMap.orthogonalGroup QW))
    (hJn : (J.subgroupOf
      (CFSG.perfectResidual ↥(TauCeti.QuadraticMap.orthogonalGroup QW))).Normal)
    (hJq : CFSG.Open.IsQuasisimple ↥J) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) =
      Nat.card (↥(CFSG.RankThree.Classical2.orthDerived QW) ⧸
        Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived QW)) := by
  classical
  let O := TauCeti.QuadraticMap.orthogonalGroup QW
  let Ω := CFSG.RankThree.Classical2.orthDerived QW
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hperf : ⁅Ω, Ω⁆ = Ω :=
    (Subgroup.isPerfect_iff (H := Ω)).mp ((Group.isPerfect_def (G := ↥Ω)).mpr hΩq.1)
  have hResO : K329Res O = Ω := by
    have h1 : K329Res O = K329Res Ω :=
      k329_res_eq_of_commutator_le (C := O) (M := Ω)
        (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := QW)) le_rfl
    exact h1.trans (le_antisymm (Subgroup.map_subtype_le _) (k329_perfect_le_res le_rfl hperf))
  have hJ'Ω : J.map O.subtype ≤ Ω := by
    have h1 : J.map O.subtype ≤ K329Res O := Subgroup.map_mono hJL
    rwa [hResO] at h1
  have hJ'n : ((J.map O.subtype).subgroupOf Ω).Normal := by
    have h1 : ((J.map O.subtype).subgroupOf (K329Res O)).Normal :=
      k329o3f_map_normal O.subtype hJL hJn
    rwa [hResO] at h1
  have hnot : ¬ J ≤ O.subtype.ker := by
    intro hle
    have hker : O.subtype.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff O.subtype).mpr (Subgroup.subtype_injective O)
    rw [hker] at hle
    exact k329o3f_not_quasisimple_of_comm (Γ := ↥J)
      (fun a b => Subtype.ext (by
        have ha1 : (a : ↥O) = 1 := Subgroup.mem_bot.mp (hle a.2)
        have hb1 : (b : ↥O) = 1 := Subgroup.mem_bot.mp (hle b.2)
        show (a : ↥O) * (b : ↥O) = (b : ↥O) * (a : ↥O)
        rw [ha1, hb1])) hJq
  obtain ⟨hJ'q, hJ'c⟩ := k329o3f_image O.subtype J hJq hnot
  let Lf : Unit → Subgroup (W ≃ₗ[K] W) := fun _ => Ω
  have hsup : (⨆ i, Lf i) = Ω := iSup_const
  obtain ⟨i, hi⟩ := k329_normal_quasisimple_eq_factor (C := W ≃ₗ[K] W)
    Lf (fun _ => hΩq) (fun i j hij => absurd (Subsingleton.elim i j) hij)
    (J.map O.subtype) (by rw [hsup]; exact hJ'Ω) (by rw [hsup]; exact hJ'n) hJ'q
  calc Nat.card (↥J ⧸ Subgroup.center ↥J)
      = Nat.card (↥(J.map O.subtype) ⧸ Subgroup.center ↥(J.map O.subtype)) := hJ'c.symm
    _ = Nat.card (↥Ω ⧸ Subgroup.center ↥Ω) :=
        congrArg (fun M : Subgroup (W ≃ₗ[K] W) =>
          Nat.card (↥M ⧸ Subgroup.center ↥M)) hi

private theorem k329o3fq2fixsix_plus
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (QW : QuadraticForm K W) (hQW : (QuadraticMap.polarBilin QW).Nondegenerate)
    (hdim : Module.finrank K W = 6)
    (hT : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, QW u = 0) :
    Nat.card (↥(CFSG.RankThree.Classical2.orthDerived QW) ⧸
      Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived QW)) ≠ 504 := by
  classical
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  let O := TauCeti.QuadraticMap.orthogonalGroup QW
  let Ω := CFSG.RankThree.Classical2.orthDerived QW
  obtain ⟨-, hcenter, hZcard, -, -, -, hodd, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQW hT
  obtain ⟨U, hU3, hUs⟩ := hT
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType QW :=
    ⟨U, by rw [hU3, hdim], hUs⟩
  have h5O : 5 ∣ Nat.card ↥O := by
    have h5Z : (5 : ℤ) ∣ (Nat.card ↥O : ℤ) := by
      have hord := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
        (m := 2) (ε := 1) hQW (by rw [hdim]) (Or.inl ⟨rfl, hplus⟩)
      rw [hord, hK]
      decide +kernel
    exact Int.natCast_dvd_natCast.mp h5Z
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P5, hP5card⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥O) (p := 5) (n := 1)
    (by rw [pow_one]; exact h5O)
  have hmap_le : P5.map O.subtype ≤ Ω := by
    rintro _ ⟨g, hgP, rfl⟩
    refine hodd (O.subtype g) g.2 ?_
    rw [orderOf_injective O.subtype (Subgroup.subtype_injective O) g]
    have hord : orderOf g ∣ 5 := by
      have h := P5.orderOf_dvd_natCard hgP
      rw [hP5card] at h
      simpa using h
    exact Odd.of_dvd_nat (show Odd 5 from ⟨2, by norm_num⟩) hord
  have hcardmap : Nat.card (P5.map O.subtype) = Nat.card P5 :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective O)
  have h5P : Nat.card (P5.map O.subtype) = 5 := by rw [hcardmap, hP5card]; norm_num
  have h5Ω : 5 ∣ Nat.card ↥Ω := by
    have hle := Subgroup.card_dvd_of_le hmap_le
    rwa [h5P] at hle
  have hcardΩ := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Ω)
  have hZle : Nat.card (Subgroup.center ↥Ω) ≤ 2 := by rw [hcenter]; exact hZcard
  have hZpos : 0 < Nat.card (Subgroup.center ↥Ω) := Nat.card_pos
  have hZcases : Nat.card (Subgroup.center ↥Ω) = 1 ∨ Nat.card (Subgroup.center ↥Ω) = 2 := by
    by_cases h1 : Nat.card (Subgroup.center ↥Ω) = 1
    · exact Or.inl h1
    · right; omega
  have hZcop : Nat.Coprime 5 (Nat.card (Subgroup.center ↥Ω)) := by
    rcases hZcases with h | h <;> rw [h] <;> decide
  have h5quot : 5 ∣ Nat.card (↥Ω ⧸ Subgroup.center ↥Ω) := by
    have hdiv : 5 ∣ Nat.card (↥Ω ⧸ Subgroup.center ↥Ω) * Nat.card (Subgroup.center ↥Ω) := by
      rw [← hcardΩ]; exact h5Ω
    exact (hZcop.dvd_mul_right).mp hdiv
  intro h504
  exact absurd (h504 ▸ h5quot) (by norm_num)

private theorem k329o3fq2fixsix_minus
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (QW : QuadraticForm K W) (hQW : (QuadraticMap.polarBilin QW).Nondegenerate)
    (hdim : Module.finrank K W = 6)
    (hts : ∀ U : Submodule K W, Module.finrank K U = 3 → ∃ u ∈ U, QW u ≠ 0) :
    Nat.card (↥(CFSG.RankThree.Classical2.orthDerived QW) ⧸
      Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived QW)) ≠ 504 := by
  classical
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 1) (by
    rw [hK]; norm_num)
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hsimple, hperf, hnonab, hcard, hidx, hnorm,
    hodd⟩ := CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction QW hQW hdim hts
  have hΩeq : CFSG.RankThree.Classical2.orthDerived QW = ρ.range := hcomm
  have hΩcard : Nat.card ↥(CFSG.RankThree.Classical2.orthDerived QW) = 25920 := by
    rw [hΩeq, hcard, hK]
    norm_num
  have hcenter : Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived QW) = ⊥ :=
    (CFSG.SeitzReduction.OmegaPilot.isQuasisimple_orthDerived_of_six hQW hdim hts).2
  have e : (↥(CFSG.RankThree.Classical2.orthDerived QW) ⧸
      Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived QW)) ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived QW) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  have hcardq : Nat.card (↥(CFSG.RankThree.Classical2.orthDerived QW) ⧸
      Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived QW)) =
      Nat.card ↥(CFSG.RankThree.Classical2.orthDerived QW) :=
    Nat.card_congr e.toEquiv
  rw [hcardq, hΩcard]
  norm_num

private theorem k329o3f_q_two_fixed_six {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (QW : QuadraticForm K W) (hQW : (QuadraticMap.polarBilin QW).Nondegenerate)
    (hdim : Module.finrank K W = 6)
    (J : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup QW))
    (hJL : J ≤ CFSG.perfectResidual ↥(TauCeti.QuadraticMap.orthogonalGroup QW))
    (hJn : (J.subgroupOf
      (CFSG.perfectResidual ↥(TauCeti.QuadraticMap.orthogonalGroup QW))).Normal)
    (hJq : CFSG.Open.IsQuasisimple ↥J) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 504 := by
  classical
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 1) (by
    rw [hK]; norm_num)
  by_cases hT : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, QW u = 0
  · have hΩq : CFSG.Open.IsQuasisimple ↥(CFSG.RankThree.Classical2.orthDerived QW) :=
      k329o3fq2fixsix_open
        (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hQW hT)
    have htrans := k329o3fq2fixsix_center_quot QW hΩq J hJL hJn hJq
    rw [htrans]
    exact k329o3fq2fixsix_plus hK QW hQW hdim hT
  · push Not at hT
    have hΩq : CFSG.Open.IsQuasisimple ↥(CFSG.RankThree.Classical2.orthDerived QW) :=
      k329o3fq2fixsix_open
        (CFSG.SeitzReduction.OmegaPilot.isQuasisimple_orthDerived_of_six hQW hdim hT).1
    have htrans := k329o3fq2fixsix_center_quot QW hΩq J hJL hJn hJq
    rw [htrans]
    exact k329o3fq2fixsix_minus hK QW hQW hdim hT

private theorem k329o3f_q_two_fixed {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (QW : QuadraticForm K W) (hQW : (QuadraticMap.polarBilin QW).Nondegenerate)
    (J : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup QW))
    (hJL : J ≤ CFSG.perfectResidual ↥(TauCeti.QuadraticMap.orthogonalGroup QW))
    (hJn : (J.subgroupOf
      (CFSG.perfectResidual ↥(TauCeti.QuadraticMap.orthogonalGroup QW))).Normal)
    (hJq : CFSG.Open.IsQuasisimple ↥J) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ≠ 504 := by
  by_cases h6 : Module.finrank K W = 6
  · exact k329o3f_q_two_fixed_six hK QW hQW h6 J hJL hJn hJq
  · exact k329o3f_q_two_fixed_ne6 hK QW hQW h6 J hJL hJn hJq

private theorem k329o3fq2block_eq_zero_or_one {K : Type} [Field K] (hK : Nat.card K = 2)
    (a : K) : a = 0 ∨ a = 1 := by
  obtain ⟨y, _, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).1 hK
  rcases eq_or_ne a 0 with h | h
  · exact Or.inl h
  · exact Or.inr ((huniq a h).trans (huniq 1 one_ne_zero).symm)

private theorem k329o3fq2block_primaryFactors_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) (h : K[X])
    (hh : h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors x.toLinearMap) :
    h = X - 1 ∨ h = X ^ 2 + X + 1 := by
  obtain ⟨hirr, hmon, hdvd⟩ := CFSG.RankThree.PartOne.KCPrimary.mem_primaryFactors.mp hh
  have hmin : minpoly K x.toLinearMap ∣ (X - 1) * (X ^ 2 + X + 1 : K[X]) := by
    have h3 : (X ^ 3 - 1 : K[X]) = (X - 1) * (X ^ 2 + X + 1) := by ring
    rw [← h3]
    exact minpoly.dvd K x.toLinearMap hx.aeval_X_pow_sub_one
  have hq_irr : Irreducible (X ^ 2 + X + 1 : K[X]) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
    · rw [show (X ^ 2 + X + 1 : K[X]).natDegree = 2 by compute_degree!]
      norm_num
    · intro a ha
      rcases k329o3fq2block_eq_zero_or_one hK a with rfl | rfl
      · simp [IsRoot.def] at ha
      · have h3 : (3 : K) = 1 + 1 + 1 := by norm_num
        have hne : (1 + 1 + 1 : K) ≠ 0 := by
          rw [← h3]
          exact hx.cast_ne_zero
        exact hne (by simpa [IsRoot.def] using ha)
  rcases hirr.prime.dvd_or_dvd (hdvd.trans hmin) with hd | hd
  · left
    exact eq_of_monic_of_associated hmon monic_X_sub_one
      (hirr.associated_of_dvd irreducible_X_sub_one hd)
  · right
    exact eq_of_monic_of_associated hmon (by monicity!)
      (hirr.associated_of_dvd hq_irr hd)

private theorem k329o3fq2block_res_le_specialProduct {K : Type} [Field K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    {R : Subgroup (V ≃ₗ[K] V)} (hRL : R ≤ K329Res (isometryCentralizer Q x))
    (hR0 : ∀ g ∈ R, ∀ w ∈ fixedSpace x, g w = w)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep) :
    R ≤ specialProduct Q x Rep := by
  intro g hg
  have hgM : g ∈ isometryCentralizer Q x := (Subgroup.map_subtype_le _) (hRL hg)
  have hgcomm : g ∈ ⁅isometryCentralizer Q x, isometryCentralizer Q x⁆ :=
    (k329_res_le_commutator _) (hRL hg)
  obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep hgcomm
  have hfM : f ∈ isometryCentralizer Q x := supportedFixedDerived_le_isometryCentralizer hf
  have hjM : j ∈ isometryCentralizer Q x :=
    iSup₂_le (fun h _ => iSup_le fun _ => specialBlock_le_isometryCentralizer h) hj
  have hgFix : isometryRestrictFixed Q x ⟨g, hgM⟩ = 1 := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    show (isometryRestrictFixed Q x ⟨g, hgM⟩ w : V) = (w : V)
    rw [coe_isometryRestrictFixed]
    exact hR0 g hg w w.2
  have hjFix : isometryRestrictFixed Q x ⟨j, hjM⟩ = 1 :=
    hx.restrictFixed_trivial_of_mem_specialProduct hRep hj hjM
  have hfFix : isometryRestrictFixed Q x ⟨f, hfM⟩ = 1 := by
    have h4 : (⟨g, hgM⟩ : ↥(isometryCentralizer Q x)) = ⟨j, hjM⟩ * ⟨f, hfM⟩ :=
      Subtype.ext hgjf
    rw [h4, map_mul, hjFix, one_mul] at hgFix
    exact hgFix
  have hfB : f ∈ supportedBlock Q x (X - 1) := supportedFixedDerived_le_supportedBlock hf
  have h5 : restrictFixed Q x ⟨f, hfB⟩ = 1 := by
    rw [← isometryRestrictFixed_restrictFixed]
    exact hfFix
  have hf1 : f = 1 := hx.eq_one_of_restrictFixed_eq_one hfB h5
  rw [hgjf, hf1, mul_one]
  exact hj

private theorem k329o3fq2block_exists_specialBlock {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    {R : Subgroup (V ≃ₗ[K] V)} (hRL : R ≤ K329Res (isometryCentralizer Q x))
    (hR0 : ∀ g ∈ R, ∀ w ∈ fixedSpace x, g w = w)
    (hRq : CFSG.Open.IsQuasisimple ↥R)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep) :
    ∃ h : K[X], h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors x.toLinearMap ∧
      h ≠ X - 1 ∧ R ≤ specialBlock Q x h := by
  have hRsp := k329o3fq2block_res_le_specialProduct hx hRL hR0 hRep
  have hdich : ∀ h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors x.toLinearMap,
      h = X - 1 ∨ h = X ^ 2 + X + 1 :=
    fun h hh => k329o3fq2block_primaryFactors_two hK hx h hh
  by_cases hex : ∃ h ∈ Rep, h ≠ X - 1
  · obtain ⟨h₀, hh₀, hne₀⟩ := hex
    refine ⟨h₀, hRep.1 hh₀, hne₀, hRsp.trans ?_⟩
    refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    have hh_eq : h = h₀ := by
      rcases hdich h (hRep.1 hh) with h1 | h1
      · exact absurd h1 hne
      · rcases hdich h₀ (hRep.1 hh₀) with h0 | h0
        · exact absurd h0 hne₀
        · rw [h1, h0]
    rw [hh_eq]
  · have hex' : ∀ h, h ∈ Rep → h = X - 1 := by
      intro h hh
      by_contra hne
      exact hex ⟨h, hh, hne⟩
    exfalso
    have hbot : specialProduct Q x Rep = ⊥ := by
      apply le_bot_iff.mp
      refine iSup₂_le fun h hh => iSup_le fun hne => ?_
      exact absurd (hex' h hh) hne
    have hRbot : R = ⊥ := by
      apply le_bot_iff.mp
      rw [← hbot]
      exact hRsp
    exact ne_bot_of_isQuasisimple (k329o3f_native hRq) hRbot

private theorem k329o3fq2block_normal_in_specialBlock {K : Type} [Field K] [Finite K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    {R : Subgroup (V ≃ₗ[K] V)} (hRL : R ≤ K329Res (isometryCentralizer Q x))
    (hRn : (R.subgroupOf (K329Res (isometryCentralizer Q x))).Normal)
    {h : K[X]} (hh : h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hRF : R ≤ specialBlock Q x h)
    (hm : 4 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h) :
    (R.subgroupOf (specialBlock Q x h)).Normal := by
  have hm2 : 2 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h := by
    omega
  have hFq : CFSG.IsQuasisimple ↥(specialBlock Q x h) :=
    k329kc3_quasisimple_specialBlock hx Nat.prime_three (by norm_num) hh hne1 hm2
      ⟨fun h2 => absurd h2 (by omega), fun h3 => absurd h3 (by omega)⟩
  have hFperf : ⁅specialBlock Q x h, specialBlock Q x h⁆ = specialBlock Q x h :=
    Subgroup.isPerfect_iff.mp hFq.1
  have hFL : specialBlock Q x h ≤ K329Res (isometryCentralizer Q x) :=
    k329_perfect_le_res (specialBlock_le_isometryCentralizer h) hFperf
  rw [Subgroup.normal_subgroupOf_iff hRF]
  intro r k hr hk
  exact (Subgroup.normal_subgroupOf_iff hRL).mp hRn r k hr (hFL hk)

private theorem k329o3f_q_two_special_block {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    (R : Subgroup (V ≃ₗ[K] V)) (hRL : R ≤ K329Res (isometryCentralizer Q x))
    (hRn : (R.subgroupOf (K329Res (isometryCentralizer Q x))).Normal)
    (hRq : CFSG.Open.IsQuasisimple ↥R)
    (hR0 : ∀ g ∈ R, ∀ w ∈ fixedSpace x, g w = w) :
    ∃ h : K[X], h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors x.toLinearMap ∧
      h ≠ X - 1 ∧ R ≤ specialBlock Q x h ∧
      (4 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h →
        (R.subgroupOf (specialBlock Q x h)).Normal) := by
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨h, hh, hne1, hRF⟩ :=
    k329o3fq2block_exists_specialBlock hK hx hRL hR0 hRq hRep
  refine ⟨h, hh, hne1, hRF, fun hm => ?_⟩
  exact k329o3fq2block_normal_in_specialBlock hx hRL hRn hh hne1 hRF hm

private theorem k329o3fq2unit_h_eq {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) : h = X ^ 2 + X + 1 := by
  have hdvd : h ∣ (X : K[X]) ^ 3 - 1 :=
    (CFSG.RankThree.PartOne.KCPrimary.mem_primaryFactors.mp hh).2.2.trans
      (minpoly.dvd K x.toLinearMap hx.aeval_X_pow_sub_one)
  have hdvd' : h ∣ X ^ 3 - C (1 : K) := by simpa using hdvd
  exact CFSG.AGLEmbedding.eq_X_sq_add_X_add_one_of_dvd hK
    (CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh)
    (CFSG.RankThree.PartOne.KCPrimary.monic_of_mem_primaryFactors hh) hdvd' hne1

private theorem k329o3fq2unit_card_adjoinRoot {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) : Nat.card (AdjoinRoot h) = 4 := by
  have hirr := CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh
  have hdeg : h.natDegree = 2 := by
    rw [k329o3fq2unit_h_eq hK hx hh hne1]
    compute_degree!
  have hcard : Nat.card (AdjoinRoot h) = Nat.card K ^ h.natDegree := by
    have : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
    rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot h),
      (AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  rw [hcard, hK, hdeg]
  norm_num

private theorem k329o3fq2unit_card_center_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) : Nat.card (Subgroup.center G) = Nat.card (Subgroup.center H) := by
  rw [← Subgroup.map_center_eq e]
  exact (Subgroup.card_map_of_injective (K := Subgroup.center G) (f := e.toMonoidHom)
    e.injective).symm

private theorem k329o3fq2unit_su_card_le {E : Type} [Field E]
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 E)
    {W : Type} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {B : W →ₛₗ[hU.bar] W →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {m : ℕ} (hm : Module.finrank E W = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3) :
    Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) ≤ 216 := by
  have hSU := (CFSG.LinearGroups.unitary_full_group_order hU hB hBl hm hm1).2.1
  have hmc : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hmc with h | h | h
  · rw [h] at hSU
    have h1 : Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) = 1 := by
      apply Nat.cast_injective (R := ℤ)
      rw [hSU, show Finset.Icc 2 1 = (∅ : Finset ℕ) by decide, Finset.prod_empty]
      norm_num
    omega
  · rw [h] at hSU
    have h2 : Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) = 6 := by
      apply Nat.cast_injective (R := ℤ)
      rw [hSU, show Finset.Icc 2 2 = ({2} : Finset ℕ) by decide, Finset.prod_singleton]
      norm_num
    omega
  · rw [h] at hSU
    have h3 : Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) = 216 := by
      apply Nat.cast_injective (R := ℤ)
      rw [hSU, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
        Finset.prod_insert (by decide), Finset.prod_singleton]
      norm_num
    omega

private theorem k329o3f_q_two_unitary {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x) {h : K[X]}
    (hh : h ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (R : Subgroup (V ≃ₗ[K] V)) (hRF : R ≤ specialBlock Q x h)
    (hRn : 4 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h →
      (R.subgroupOf (specialBlock Q x h)).Normal)
    (hRq : CFSG.Open.IsQuasisimple ↥R) :
    Nat.card (↥R ⧸ Subgroup.center ↥R) ≠ 504 := by
  classical
  have : Finite V := Module.finite_of_finite K
  have hFinV : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hFinF : Finite ↥(specialBlock Q x h) :=
    Finite.of_injective (fun g : ↥(specialBlock Q x h) => (g.1 : V ≃ₗ[K] V))
      fun a b h => Subtype.ext h
  by_cases hm1 : CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h = 1
  · have : Fact (Irreducible h) :=
      ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh⟩
    have hbot : specialBlock Q x h = ⊥ := hx.specialBlock_eq_bot_of_finrank_eq_one hh hm1
    have hRbot : R = ⊥ := le_bot_iff.mp (hRF.trans (le_of_eq hbot))
    exact absurd hRbot (ne_bot_of_isQuasisimple (k329o3f_native hRq))
  · have : Fact (Irreducible h) :=
      ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh⟩
    have hmge2 : 2 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h := by
      have hpos := hx.primaryMultiplicity_pos hh
      omega
    have hself : h = reciprocalPolynomial h := by
      rw [k329o3fq2unit_h_eq hK hx hh hne1]
      exact (CFSG.AGLEmbedding.reciprocalPolynomial_X_sq_add_X_add_one).symm
    obtain ⟨ℓ, f, hU, B, hB, hBl, -, hrange⟩ :=
      k329kc3_exists_selfDual_unitary hx (by decide : Odd 3) hh hne1 hself
    have hcard4 : Nat.card (AdjoinRoot h) = 4 := k329o3fq2unit_card_adjoinRoot hK hx hh hne1
    have hℓ2 : ℓ = 2 := by
      by_contra hne
      have hodd : Odd ℓ := hU.prime.odd_of_ne_two hne
      have hpow : Odd (ℓ ^ (2 * f)) := hodd.pow
      rw [← hU.card, hcard4] at hpow
      exact absurd hpow (by decide)
    subst hℓ2
    have hf1 : f = 1 := by
      have h : 2 ^ (2 * f) = 2 ^ 2 := by
        rw [← hU.card, hcard4]
        norm_num
      have := Nat.pow_right_injective (le_refl 2) h
      omega
    subst hf1
    let e₁ : ↥(specialBlock Q x h) ≃*
        ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) :=
      (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
        (MulEquiv.subgroupCongr hrange)
    have hcard_eq : Nat.card ↥(specialBlock Q x h) =
        Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) :=
      Nat.card_congr e₁.toEquiv
    have hfin : Module.finrank (AdjoinRoot h)
        (CFSG.RankThree.PartOne.KCPrimary.primaryComponent x.toLinearMap h) =
        CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h := rfl
    by_cases hm3 : CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h ≤ 3
    · have hSUle :
          Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) ≤ 216 :=
        k329o3fq2unit_su_card_le hU hB hBl hfin (by omega) hm3
      have hRle : Nat.card ↥R ≤ Nat.card ↥(specialBlock Q x h) := Subgroup.card_le_of_le hRF
      have hRle216 : Nat.card ↥R ≤ 216 := (hRle.trans hcard_eq.le).trans hSUle
      intro h504
      have hleR : Nat.card (↥R ⧸ Subgroup.center ↥R) ≤ Nat.card ↥R :=
        Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center ↥R))
          (QuotientGroup.mk'_surjective _)
      omega
    · have hm4 : 4 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h := by
        omega
      have hFq : CFSG.IsQuasisimple ↥(specialBlock Q x h) :=
        k329kc3_quasisimple_specialBlock hx Nat.prime_three (by norm_num) hh hne1 hmge2
          ⟨fun h2 => absurd h2 (by omega), fun h3 => absurd h3 (by omega)⟩
      have hnorm : (R.subgroupOf (specialBlock Q x h)).Normal := hRn hm4
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hFq hnorm with htop | hcen
      · have hFR : specialBlock Q x h ≤ R := Subgroup.subgroupOf_eq_top.mp htop
        have hRF_eq : R = specialBlock Q x h := le_antisymm hRF hFR
        rw [hRF_eq]
        have hSUdvd : 2 ^ (CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h *
            (CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h - 1) / 2) ∣
            Nat.card ↥(CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup B) :=
          CFSG.LargeExtraspecial.S14.PSLPSU10.two_pow_dvd_card_sesqSpecialUnitaryGroup
            hU hB hBl hfin (by omega)
        have h6 : 6 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h *
            (CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h - 1) / 2 := by
          have hmm : 12 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h *
              (CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h - 1) := by
            have := Nat.mul_le_mul hm4 (by omega : 3 ≤
              CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h - 1)
            norm_num at this
            exact this
          rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
          norm_num
          exact hmm
        have hFdvd : 2 ^ 6 ∣ Nat.card ↥(specialBlock Q x h) :=
          (pow_dvd_pow 2 h6).trans (hcard_eq.symm ▸ hSUdvd)
        have hZcard : Nat.card (Subgroup.center ↥(specialBlock Q x h)) =
            Nat.gcd (CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h) 3 := by
          rw [k329o3fq2unit_card_center_mulEquiv e₁]
          have hd3 : 3 ≤ Module.finrank (AdjoinRoot h)
              (CFSG.RankThree.PartOne.KCPrimary.primaryComponent x.toLinearMap h) := by
            rw [hfin]
            omega
          have hc := (CFSG.LocalAnalysis.GorensteinLyons.four_element_special_unitary_binary_scalar_centralizer
            hU hB hBl hd3).2.2.2
          rw [hfin] at hc
          exact hc
        have hcop : Nat.Coprime (2 ^ 6)
            (Nat.gcd (CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h) 3) := by
          have hd : Nat.gcd
              (CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity x.toLinearMap h) 3 ∣ 3 :=
            Nat.gcd_dvd_right _ 3
          rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
          · rw [h]; decide
          · rw [h]; decide
        have hZodd : Nat.Coprime (2 ^ 6)
            (Nat.card (Subgroup.center ↥(specialBlock Q x h))) := by
          rw [hZcard]
          exact hcop
        have hcardF :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(specialBlock Q x h))
        have hquot : 2 ^ 6 ∣ Nat.card (↥(specialBlock Q x h) ⧸
            Subgroup.center ↥(specialBlock Q x h)) := by
          have hdiv : 2 ^ 6 ∣ Nat.card (↥(specialBlock Q x h) ⧸
              Subgroup.center ↥(specialBlock Q x h)) *
              Nat.card (Subgroup.center ↥(specialBlock Q x h)) := by
            rw [← hcardF]
            exact hFdvd
          exact (hZodd.dvd_mul_right).mp hdiv
        intro h504
        exact absurd (h504 ▸ hquot) (by norm_num)
      · exfalso
        refine (k329o3f_not_quasisimple_of_comm (Γ := ↥R) ?_) hRq
        intro a b
        have ha : (⟨a.1, hRF a.2⟩ : ↥(specialBlock Q x h)) ∈
            R.subgroupOf (specialBlock Q x h) := a.2
        have hc := Subgroup.mem_center_iff.mp (hcen ha) (⟨b.1, hRF b.2⟩ : ↥(specialBlock Q x h))
        exact Subtype.ext
          (congrArg (fun z : ↥(specialBlock Q x h) => (z.1 : V ≃ₗ[K] V)) hc.symm)

private theorem k329o3f_q_two_special {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    (R : Subgroup (V ≃ₗ[K] V)) (hRL : R ≤ K329Res (isometryCentralizer Q x))
    (hRn : (R.subgroupOf (K329Res (isometryCentralizer Q x))).Normal)
    (hRq : CFSG.Open.IsQuasisimple ↥R)
    (hR0 : ∀ g ∈ R, ∀ w ∈ fixedSpace x, g w = w) :
    Nat.card (↥R ⧸ Subgroup.center ↥R) ≠ 504 := by
  obtain ⟨h, hh, hne1, hRF, hRN⟩ := k329o3f_q_two_special_block hK hx R hRL hRn hRq hR0
  exact k329o3f_q_two_unitary hK hx hh hne1 R hRF hRN hRq

private theorem k329o3f_q_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    (R : Subgroup (V ≃ₗ[K] V)) (hRL : R ≤ K329Res (isometryCentralizer Q x))
    (hRn : (R.subgroupOf (K329Res (isometryCentralizer Q x))).Normal)
    (hRq : CFSG.Open.IsQuasisimple ↥R) :
    Nat.card (↥R ⧸ Subgroup.center ↥R) ≠ 504 := by
  classical
  have : Finite V := Module.finite_of_finite K
  have hFinV : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  by_cases hker : ∀ g ∈ R, ∀ w ∈ fixedSpace x, g w = w
  · exact k329o3f_q_two_special hK hx R hRL hRn hRq hker
  · obtain ⟨g0, hg0R, w0, hw0, hg0w0⟩ : ∃ g ∈ R, ∃ w ∈ fixedSpace x, g w ≠ w := by
      by_contra hcon
      exact hker fun g hg w hw => by_contra fun hne => hcon ⟨g, hg, w, hw, hne⟩
    set M : Subgroup (V ≃ₗ[K] V) := isometryCentralizer Q x with hM
    let QW : QuadraticForm K ↥(fixedSpace x) := Q.comp (fixedSpace x).subtype
    let O := TauCeti.QuadraticMap.orthogonalGroup QW
    let ρc : ↥M →* ↥O := (isometryRestrictFixed Q x).codRestrict O
      (fun g => isometryRestrictFixed_mem_orthogonalGroup g)
    have hρc_surj : Function.Surjective ρc := by
      intro φ
      obtain ⟨g, hg⟩ := restrictFixed_surjective hx φ.1 φ.2
      refine ⟨⟨g.1, supportedBlock_le_isometryCentralizer _ g.2⟩, ?_⟩
      apply Subtype.ext
      show isometryRestrictFixed Q x ⟨g.1, supportedBlock_le_isometryCentralizer _ g.2⟩ = φ.1
      rw [isometryRestrictFixed_restrictFixed]
      exact hg
    have hRM : R ≤ M := hRL.trans (Subgroup.map_subtype_le _)
    set RM : Subgroup ↥M := R.subgroupOf M with hRMdef
    have hPM : (K329Res M).subgroupOf M = CFSG.perfectResidual ↥M :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    have hRMP : RM ≤ CFSG.perfectResidual ↥M := by
      intro g hg
      rw [← hPM]
      exact hRL hg
    have hRMn : (RM.subgroupOf (CFSG.perfectResidual ↥M)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hRMP]
      intro h g hh hg
      rw [← hPM] at hg
      have hh' : (h : V ≃ₗ[K] V) ∈ R := hh
      have hg' : (g : V ≃ₗ[K] V) ∈ K329Res M := hg
      exact (Subgroup.normal_subgroupOf_iff hRL).mp hRn _ _ hh' hg'
    let eR : ↥RM ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRM
    have hRMq : CFSG.Open.IsQuasisimple ↥RM := k329_isQuasisimple_of_mulEquiv eR.symm hRq
    have hnot : ¬ RM ≤ ρc.ker := by
      intro hle
      have hmem : (⟨g0, hRM hg0R⟩ : ↥M) ∈ RM := hg0R
      have h1 := MonoidHom.mem_ker.mp (hle hmem)
      have h2 : isometryRestrictFixed Q x ⟨g0, hRM hg0R⟩ = 1 := congrArg Subtype.val h1
      have h3 := congrArg (fun φ : ↥(fixedSpace x) ≃ₗ[K] ↥(fixedSpace x) =>
        ((φ ⟨w0, hw0⟩ : ↥(fixedSpace x)) : V)) h2
      simp only [coe_isometryRestrictFixed] at h3
      exact hg0w0 h3
    obtain ⟨hJq, hJc⟩ := k329o3f_image ρc RM hRMq hnot
    have hres : (CFSG.perfectResidual ↥M).map ρc = CFSG.perfectResidual ↥O :=
      k329o3f_perfectResidual_map ρc hρc_surj
    have hJL : RM.map ρc ≤ CFSG.perfectResidual ↥O :=
      (Subgroup.map_mono hRMP).trans (le_of_eq hres)
    have hJn : ((RM.map ρc).subgroupOf (CFSG.perfectResidual ↥O)).Normal := by
      have := k329o3f_map_normal ρc hRMP hRMn
      rwa [hres] at this
    have hB := k329o3f_q_two_fixed hK QW hx.polarBilin_fixed_nondegenerate (RM.map ρc) hJL hJn hJq
    intro hcard
    apply hB
    rw [hJc, k329o3f_card_center_quot eR]
    exact hcard

private theorem k329o3f_core {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (Q : QuadraticForm K (ι → K)) (hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    {t : CFSG.Open.StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {n r e : ℕ}
    {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hG : CFSG.Open.StatedClassicalModel (CFSG.Open.StatedProj (StatedOmega Q₀)) t n r e)
    (hr : r ≠ 3) (hK : Nat.card K = r ^ e) : K329YMatrix (StatedOmega Q₀) (r ^ e) := by
  classical
  subst hQ
  intro x hxZ hx3 hex
  obtain ⟨R, hRL, hRn, hRq, hRc⟩ := hex
  have hZc : K329Zh (StatedOmega ⇑Q) ≤ Subgroup.center (StatedOmega ⇑Q) := k329_Zh_le_center _
  have hcomp := k329o3f_component_image (K329Zh (StatedOmega ⇑Q)) hZc x R hRL hRn hRq
  obtain ⟨hJq, hJc⟩ := k329o3f_image (QuotientGroup.mk' (K329Zh (StatedOmega ⇑Q))) R hRq
    (k329o3f_not_le_ker _ hZc R hRq)
  have ha : (QuotientGroup.mk x : ↥(StatedOmega ⇑Q) ⧸ K329Zh (StatedOmega ⇑Q)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hx3
  rcases k329o3f_reduction ht hG hr (QuotientGroup.mk x) ha _ hcomp (hJc.trans hRc) with h8 | ⟨rfl, rfl⟩
  · exact h8
  · exfalso
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hZbot := k329o3f_zh_eq_bot (ι := ι) hK2 (StatedOmega ⇑Q)
    have hx3one : x ^ 3 = 1 := by
      have : x ^ 3 ∈ (⊥ : Subgroup ↥(StatedOmega ⇑Q)) := by rw [← hZbot]; exact hx3
      simpa using this
    have hxne : x ≠ 1 := by
      intro h
      apply hxZ
      rw [h, hZbot]
      exact Subgroup.one_mem _
    have horderx : orderOf x = 3 := by
      have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3one
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.mp h1) hxne
      · exact h3
    let θ : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K
    let H : Subgroup (GL ι K) := StatedOmega ⇑Q
    let Θ : ↥H →* ((ι → K) ≃ₗ[K] (ι → K)) := θ.toMonoidHom.comp H.subtype
    have hΘinj : Function.Injective Θ := θ.injective.comp (Subgroup.subtype_injective H)
    have hH : H = (orthDerived Q).comap θ.toMonoidHom :=
      CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Q) (Q₀ := ⇑Q) rfl
    have hmem : θ.toMonoidHom (x : GL ι K) ∈ orthDerived Q := by
      have hx' : (x : GL ι K) ∈ (orthDerived Q).comap θ.toMonoidHom := by
        rw [← hH]
        exact x.2
      exact Subgroup.mem_comap.mp hx'
    let xL : orthDerived Q := ⟨θ.toMonoidHom (x : GL ι K), hmem⟩
    have horderL : orderOf xL = 3 := by
      rw [Subgroup.orderOf_mk]
      exact (MulEquiv.orderOf_eq θ (x : GL ι K)).trans ((Subgroup.orderOf_coe x).trans horderx)
    have hchar : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 1) (by
      rw [hK2]; norm_num)
    have hpl : 3 ≠ ringChar K := by
      rw [ringChar.eq K 2]
      norm_num
    have hx : OddOrderIsometry Q 3 (xL : (ι → K) ≃ₗ[K] (ι → K)) :=
      oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQnd xL horderL
    have hbridge := k329o3f_bridge Q x
    have hRL' : R.map Θ ≤ K329Res (isometryCentralizer Q (xL : (ι → K) ≃ₗ[K] (ι → K))) := by
      have h1 : R.map Θ ≤ (K329Lres x).map Θ := Subgroup.map_mono hRL
      exact hbridge ▸ h1
    have hRn' : ((R.map Θ).subgroupOf
        (K329Res (isometryCentralizer Q (xL : (ι → K) ≃ₗ[K] (ι → K))))).Normal := by
      have h1 := k329o3f_map_normal Θ hRL hRn
      have h2 : (K329Lres x).map Θ =
          K329Res (isometryCentralizer Q (xL : (ι → K) ≃ₗ[K] (ι → K))) := hbridge
      rwa [h2] at h1
    have hnotΘ : ¬ R ≤ Θ.ker := by
      intro hle
      have hker : Θ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff Θ).mpr hΘinj
      rw [hker] at hle
      exact k329o3f_not_quasisimple_of_comm
        (fun a b => Subtype.ext (by
          have ha1 : (a : ↥H) = 1 := Subgroup.mem_bot.mp (hle a.2)
          have hb1 : (b : ↥H) = 1 := Subgroup.mem_bot.mp (hle b.2)
          show (a : ↥H) * (b : ↥H) = (b : ↥H) * (a : ↥H)
          rw [ha1, hb1])) hRq
    obtain ⟨hRq', hRc'⟩ := k329o3f_image Θ R hRq hnotΘ
    exact k329o3f_q_two hK2 hx (R.map Θ) hRL' hRn' hRq' (hRc'.trans hRc)

end K329O3FPrivate

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp in
private theorem k329poodd_reduction {G : Type} [Group G] {n r e : ℕ}
    (hG : CFSG.Open.StatedClassicalModel G .POmegaOdd n r e) (hr : r ≠ 3) (a : G) (ha : a ^ 3 = 1)
    (J : Subgroup G) (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer ({a} : Set G)))
    (hJc : Nat.card (↥J ⧸ Subgroup.center ↥J) = 504) : r ^ e = 8 ∨ (r = 2 ∧ e = 1) := by
  have hadm := hG.1
  have hJ' : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj a)) := by
    rw [k329o3f_fix_conj]
    exact hJ
  obtain ⟨X, _, _, hX, hfac, -, g, hg, hk⟩ :=
    exists_lieFactor_of_component_conj_omega_card slFactorFacts_holds suFactorFacts_holds
      omegaFactorField_holds Nat.prime_three (by norm_num) (Or.inl rfl) hG
      (Ne.symm hr) a ha J hJ'
  obtain ⟨eq⟩ := nonempty_centralQuotient_mulEquiv hX.perfect g hg hk
  obtain ⟨j, hj, hq⟩ := k329o3f_orthFactor_504 hfac
    ((Nat.card_congr eq.toEquiv).trans hJc)
  exact k329o3f_eight_of_pow hadm.1 hadm.2.1 hj hq

private theorem k329poodd_core {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (Q : QuadraticForm K (ι → K)) (_hQnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    {n r e : ℕ} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hG : CFSG.Open.StatedClassicalModel (CFSG.Open.StatedProj (StatedOmega Q₀)) .POmegaOdd n r e)
    (hr : r ≠ 3) (hK : Nat.card K = r ^ e) (hne : r ≠ 2) :
    K329YMatrix (StatedOmega Q₀) (r ^ e) := by
  classical
  subst hQ
  intro x hxZ hx3 hex
  obtain ⟨R, hRL, hRn, hRq, hRc⟩ := hex
  have hZc : K329Zh (StatedOmega ⇑Q) ≤ Subgroup.center (StatedOmega ⇑Q) := k329_Zh_le_center _
  have hcomp := k329o3f_component_image (K329Zh (StatedOmega ⇑Q)) hZc x R hRL hRn hRq
  obtain ⟨hJq, hJc⟩ := k329o3f_image (QuotientGroup.mk' (K329Zh (StatedOmega ⇑Q))) R hRq
    (k329o3f_not_le_ker _ hZc R hRq)
  have ha : (QuotientGroup.mk x : ↥(StatedOmega ⇑Q) ⧸ K329Zh (StatedOmega ⇑Q)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hx3
  rcases k329poodd_reduction hG hr (QuotientGroup.mk x) ha _ hcomp (hJc.trans hRc) with
    h8 | ⟨rfl, rfl⟩
  · exact h8
  · exact absurd rfl hne

theorem k329_S3f_POmegaOdd (n r e : ℕ) (hadm : StatedLieAdmissible .POmegaOdd n r e)
    (hr : r ≠ 3) (K : Type) [Field K] [Finite K] (hK : Nat.card K = r ^ e) :
    K329YMatrix (StatedOmega (StatedQuadOdd n K)) (r ^ e) := by
  have hring : ringChar K = r :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
  have h2 : (2 : K) ≠ 0 := by
    rw [Ne, CFSG.ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two
      (by rw [hring]; exact hadm.1), hring]
    exact hadm.2.2.2
  refine k329poodd_core (n := n) (r := r) (e := e)
    (CFSG.LieType.Universal.Spin.quadOdd n K)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd n K h2)
    (CFSG.LieType.Universal.Spin.coe_quadOdd n K)
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩ hr hK hadm.2.2.2

theorem k329_S3f_POmegaPlus (n r e : ℕ) (hadm : StatedLieAdmissible .POmegaPlus n r e)
    (hr : r ≠ 3) (K : Type) [Field K] [Finite K] (hK : Nat.card K = r ^ e) :
    K329YMatrix (StatedOmega (StatedQuadPlus n K)) (r ^ e) :=
  k329o3f_core (n := n) (r := r) (e := e) (CFSG.LieType.Universal.Spin.quadPlus n K)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K) (Or.inl rfl)
    (CFSG.LieType.Universal.Spin.coe_quadPlus n K)
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩ hr hK

private theorem k329o3fm_statedQuadMinus_smul (n : ℕ) (K : Type) [Field K] (b c : K) :
    ∀ (a : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      StatedQuadMinus n K b c (a • v) = a ^ 2 * StatedQuadMinus n K b c v := by
  intro a v
  simp only [StatedQuadMinus, Pi.smul_apply, smul_eq_mul]
  have hs : ∑ x, a * v (Sum.inl x) * (a * v (Sum.inr (Sum.inl x))) =
      a ^ 2 * ∑ i, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs]
  ring

private theorem k329o3fm_statedQuadMinus_ne_zero (n : ℕ) (K : Type) [Field K] (b c : K) :
    StatedQuadMinus n K b c (Pi.single (Sum.inr (Sum.inr 0)) 1) ≠ 0 := by
  simp [StatedQuadMinus]

private theorem k329o3fm_YMatrix_of_unit_cube
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Q : (ι → K) → K} (hQ : ∀ (c : K) v, Q (c • v) = c ^ 2 * Q v) {v₀ : ι → K}
    (hv₀ : Q v₀ ≠ 0) (q : ℕ)
    (hmain : ∀ x : StatedOmega Q, x ∉ K329Zh (StatedOmega Q) → x ^ 3 = 1 →
       (∃ R : Subgroup (StatedOmega Q), R ≤ K329Lres x ∧
         (R.subgroupOf (K329Lres x)).Normal ∧ CFSG.Open.IsQuasisimple ↥R ∧
         Nat.card (↥R ⧸ Subgroup.center ↥R) = 504) → q = 8) :
    K329YMatrix (StatedOmega Q) q := by
  intro x hxZ hx3 hQex
  let H := StatedOmega Q
  let ε : H := x ^ 3
  have hεZh : ε ∈ K329Zh H := hx3
  have hε2 : ε ^ 2 = 1 := by
    apply Subtype.ext
    have hεGLmem : (ε : GL ι K) ∈ StatedOmega Q := ε.2
    have hεGLscal : (ε : GL ι K) ∈ CFSG.Open.StatedScalars ι K :=
      Subgroup.mem_subgroupOf.mp hεZh
    have h := CFSG.HardMathSupport.Malle.E27Lie.sq_eq_one_of_mem_statedScalars
      (F := K) (Q := Q) hQ hv₀ hεGLmem hεGLscal
    simpa [map_pow] using h
  have hεc : ε ∈ Subgroup.center H := k329_Zh_le_center H hεZh
  have hcen : ∀ g : H, g * ε = ε * g := Subgroup.mem_center_iff.mp hεc
  have hceninv : ∀ g : H, g * (ε : H)⁻¹ = (ε : H)⁻¹ * g :=
    Subgroup.mem_center_iff.mp ((Subgroup.center H).inv_mem hεc)
  let x' : H := ε * x
  have hx'rep : x' = ε * x := rfl
  have hx'3 : x' ^ 3 = 1 := by
    show (ε * x) ^ 3 = 1
    rw [show ε * x = x * ε from (hcen x).symm, Commute.mul_pow (hcen x) 3]
    show ε * ε ^ 3 = 1
    have h4 : ε * ε ^ 3 = ε ^ 4 := by
      rw [show (4 : ℕ) = 1 + 3 from rfl, pow_add, pow_one]
    rw [h4, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hε2, one_pow]
  have hx'Z : x' ∉ K329Zh H := by
    intro h
    apply hxZ
    have hεinv : (ε : H)⁻¹ ∈ K329Zh H := inv_mem hεZh
    have : (ε : H)⁻¹ * x' ∈ K329Zh H := mul_mem hεinv h
    have heq : (ε : H)⁻¹ * x' = x := by
      rw [hx'rep]
      group
    rwa [heq] at this
  have hcent : Subgroup.centralizer ({x'} : Set H) = Subgroup.centralizer ({x} : Set H) := by
    ext h
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hh
      have h1 : (ε : H)⁻¹ * x' = x := by rw [hx'rep]; group
      calc h * x = h * ((ε : H)⁻¹ * x') := by rw [h1]
        _ = (ε : H)⁻¹ * (h * x') := by
          rw [show h * ((ε : H)⁻¹ * x') = (h * (ε : H)⁻¹) * x' from by group, hceninv h]
          group
        _ = (ε : H)⁻¹ * (x' * h) := by rw [hh]
        _ = ((ε : H)⁻¹ * x') * h := by group
        _ = x * h := by rw [h1]
    · intro hh
      calc h * x' = h * (ε * x) := by rw [hx'rep]
        _ = ε * (h * x) := by
          have hc : h * ε = ε * h := hcen h
          calc h * (ε * x) = (h * ε) * x := by group
            _ = (ε * h) * x := by rw [hc]
            _ = ε * (h * x) := by group
        _ = ε * (x * h) := by rw [hh]
        _ = (ε * x) * h := by group
        _ = x' * h := by rw [hx'rep]
  have hres : K329Lres x' = K329Lres x := by
    unfold K329Lres K329Res
    rw [hcent]
  obtain ⟨R, hRle, hRn, hRq, hRc⟩ := hQex
  exact hmain x' hx'Z hx'3 ⟨R, hres.symm ▸ hRle, by rw [hres]; exact hRn, hRq, hRc⟩

theorem k329_S3f_POmegaMinus (n r e : ℕ) (hadm : StatedLieAdmissible .POmegaMinus n r e)
    (hr : r ≠ 3) (K : Type) [Field K] [Finite K] (hK : Nat.card K = r ^ e) (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    K329YMatrix (StatedOmega (StatedQuadMinus n K b c)) (r ^ e) := by
  refine k329o3fm_YMatrix_of_unit_cube (k329o3fm_statedQuadMinus_smul n K b c)
    (k329o3fm_statedQuadMinus_ne_zero n K b c) (r ^ e) ?_
  intro x hxZ hx3 hQ
  have hx3' : x ^ 3 ∈ K329Zh (StatedOmega (StatedQuadMinus n K b c)) := by
    rw [hx3]
    exact Subgroup.one_mem _
  exact k329o3f_core (n := n) (r := r) (e := e) (CFSG.LieType.Universal.Spin.quadMinus n K b c)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
    (Or.inr rfl) (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c)
    ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hbc, ⟨MulEquiv.refl _⟩⟩ hr hK
    x hxZ hx3' hQ

section K329O3CPPrivate

open CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.PartOne.KCPrimary
open Polynomial Module
open scoped commutatorElement

private theorem k329o3cp_open_of_native {G : Type*} [Group G] (h : CFSG.IsQuasisimple G) :
    CFSG.Open.IsQuasisimple G :=
  ⟨Group.isPerfect_def.mp h.1, h.2.1⟩

private theorem k329o3cp_zh_eq_bot (n : ℕ) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) :
    K329Zh (StatedOmega (StatedQuadPlus n K)) = ⊥ := by
  have hchar : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  have : CharP K 2 := hchar
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : (x : GL (Fin n ⊕ Fin n) K) ∈ StatedScalars (Fin n ⊕ Fin n) K :=
    Subgroup.mem_subgroupOf.mp hx
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hx'
  have h2 : (x : GL (Fin n ⊕ Fin n) K) ^ 2 = 1 :=
    CFSG.HardMathSupport.Malle.E27Lie.sq_eq_one_of_mem_statedScalars
      (CFSG.HardMathSupport.Malle.E27Lie.statedQuadPlus_smul n)
      (CFSG.HardMathSupport.Malle.E27Lie.statedQuadPlus_ne_zero hn K) x.2 hx'
  have h3 : (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c) ^ 2 = 1 := by
    rw [hc]; exact h2
  have hsq : (c : K) ^ 2 = 1 := by
    have hne : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, hn⟩⟩
    have h4 := congrArg (fun g : GL (Fin n ⊕ Fin n) K =>
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Classical.choice hne)
        (Classical.choice hne)) h3
    simpa [← map_pow, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] using h4
  have hc1 : c = 1 := by
    apply Units.ext
    exact CharTwo.sq_inj.mp (by rw [hsq]; simp)
  have hx1 : (x : GL (Fin n ⊕ Fin n) K) = 1 := by
    rw [← hc, hc1, map_one]
  exact Subtype.ext (by simpa using hx1)

private theorem k329o3cp_transport {H G : Type} [Group H] [Group G] [Finite H]
    (φ : H →* G) (hφ : Function.Injective φ) {C : Subgroup H} {D' : Subgroup G}
    (hD : C.map φ = D') (h : K329CentralProduct (K329Res D')) :
    K329CentralProduct (K329Res C) := by
  obtain ⟨ι, hι, Lf, hq, hc, hsup⟩ := h
  have hDrange : K329Res D' ≤ φ.range :=
    (Subgroup.map_subtype_le (CFSG.perfectResidual ↥D')).trans
      (hD.symm ▸ Subgroup.map_le_range φ C)
  have hle : ∀ i, Lf i ≤ φ.range := fun i =>
    (le_iSup Lf i).trans (hsup.le.trans hDrange)
  have hmapi : ∀ i, ((Lf i).comap φ).map φ = Lf i := fun i => by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr (hle i)]
  refine ⟨ι, hι, fun i => (Lf i).comap φ, ?_, ?_, ?_⟩
  · intro i
    let e : ↥((Lf i).comap φ) ≃* ↥(Lf i) :=
      (Subgroup.equivMapOfInjective ((Lf i).comap φ) φ hφ).trans
        (MulEquiv.subgroupCongr (hmapi i))
    exact k329_isQuasisimple_of_mulEquiv e.symm (hq i)
  · intro i j hij
    apply Subgroup.map_injective hφ
    rw [Subgroup.map_commutator, Subgroup.map_bot, hmapi i, hmapi j]
    exact hc i j hij
  · apply Subgroup.map_injective hφ
    rw [Subgroup.map_iSup]
    have h1 : (K329Res C).map φ = K329Res D' := by
      rw [k329_res_map, hD]
    exact (iSup_congr hmapi).trans (hsup.trans h1.symm)

private theorem k329o3cp_perfect_sup {G : Type*} [Group G] {A B : Subgroup G}
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) ?_
  refine sup_le ?_ ?_
  · calc A = ⁅A, A⁆ := hA.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc B = ⁅B, B⁆ := hB.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

private theorem k329o3cp_perfect_iSup {G : Type*} [Group G] {ι : Type*} (F : ι → Subgroup G)
    (hF : ∀ i, ⁅F i, F i⁆ = F i) : ⁅⨆ i, F i, ⨆ i, F i⁆ = ⨆ i, F i := by
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) ?_
  refine iSup_le fun i => ?_
  calc F i = ⁅F i, F i⁆ := (hF i).symm
    _ ≤ ⁅⨆ i, F i, ⨆ i, F i⁆ :=
        Subgroup.commutator_mono (le_iSup F i) (le_iSup F i)

private theorem k329o3cp_linear
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hcard : Nat.card K = 8) :
    K329CentralProduct
      (K329Res (isometryCentralizer Q x ⊓ CFSG.RankThree.Classical2.orthDerived Q)) := by
  classical
  have hp2 : Odd 3 := by decide
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  let C : Subgroup (V ≃ₗ[K] V) :=
    isometryCentralizer Q x ⊓ CFSG.RankThree.Classical2.orthDerived Q
  let ιS : Type := {h : ↥Rep // (h : K[X]) ≠ X - 1 ∧
    2 ≤ primaryMultiplicity x.toLinearMap (h : K[X])}
  have hιS : Fintype ιS := inferInstance
  let S : ιS → Subgroup (V ≃ₗ[K] V) := fun h => specialBlock Q x (h.1 : K[X])
  have hS_q : ∀ i, CFSG.Open.IsQuasisimple ↥(S i) := by
    intro i
    exact k329o3cp_open_of_native
      (k329kc3_quasisimple_specialBlock hx Nat.prime_three (by norm_num)
        (hRep.1 i.1.2) i.2.1 i.2.2
        ⟨fun _ => by rw [hcard]; norm_num, fun _ => by rw [hcard]; norm_num⟩)
  have hS_perf : ∀ i, Group.IsPerfect ↥(S i) := fun i => Group.isPerfect_def.mpr (hS_q i).1
  have hS_c : ∀ i j, i ≠ j → ⁅S i, S j⁆ = ⊥ := by
    intro i j hij
    apply le_bot_iff.mp
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    have h1 : a ∈ supportedBlock Q x (i.1 : K[X]) := specialBlock_le_supportedBlock _ ha
    have h2 : b ∈ supportedBlock Q x (j.1 : K[X]) := specialBlock_le_supportedBlock _ hb
    have hij1 : (i.1 : K[X]) ≠ (j.1 : K[X]) := fun e => hij (Subtype.ext (Subtype.ext e))
    have hij2 : (j.1 : K[X]) ≠ (i.1 : K[X]) := fun e => hij (Subtype.ext (Subtype.ext e.symm))
    exact hx.commute_supportedBlock (hRep.1 i.1.2) (hRep.1 j.1.2) hij2
      (hRep.ne_reciprocal i.1.2 j.1.2 hij1) h1 h2
  have hS_le_C : ∀ i, S i ≤ C := by
    intro i
    exact le_inf (specialBlock_le_isometryCentralizer _)
      (k329kc3_specialBlock_le_orthDerived hx Nat.prime_three (by norm_num)
        (hRep.1 i.1.2) i.2.1 i.2.2
        ⟨fun _ => by rw [hcard]; norm_num, fun _ => by rw [hcard]; norm_num⟩)
  let sfp : Subgroup (V ≃ₗ[K] V) := ⨆ i, S i
  have hsfp_perf : ⁅sfp, sfp⁆ = sfp :=
    k329o3cp_perfect_iSup S (fun i => Subgroup.isPerfect_iff.mp (hS_perf i))
  have hsp_le_sfp : specialProduct Q x Rep ≤ sfp := by
    refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap h
    · exact le_iSup S ⟨⟨h, hh⟩, hne, hm⟩
    · have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors (hRep.1 hh)⟩
      have hpos := hx.primaryMultiplicity_pos (hRep.1 hh)
      have hm1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
      rw [hx.specialBlock_eq_bot_of_finrank_eq_one (hRep.1 hh) hm1]
      exact bot_le
  have hspM : specialProduct Q x Rep ≤ isometryCentralizer Q x :=
    iSup₂_le fun h _ => iSup_le fun _ => specialBlock_le_isometryCentralizer h
  by_cases hW : 3 ≤ finrank K (fixedSpace x)
  ·
    have hX1mem : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
      by_contra hmem
      have hbot := fixedSpace_eq_bot_of_not_mem hmem
      have : finrank K (fixedSpace x) = 0 := by rw [hbot, finrank_bot]
      omega
    have hnexc : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype) := by
      intro hexc
      rcases hexc with ⟨-, h3⟩ | ⟨-, h23⟩
      · rw [hcard] at h3; omega
      · rcases h23 with h2 | h3
        · rw [hcard] at h2; omega
        · rw [hcard] at h3; omega
    have hcov : DerivedCoverage (Q.comp (fixedSpace x).subtype) :=
      ((orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype)
        hx.polarBilin_fixed_nondegenerate hW).2 hnexc)
    obtain ⟨nF, F, hnF1, hnF2, hFsup, hFq, hFc, -⟩ := hx.exists_supported_factors hcov
    let ι : Type := Fin nF ⊕ ιS
    have hι : Fintype ι := inferInstance
    let Lf : ι → Subgroup (V ≃ₗ[K] V) := Sum.elim F S
    have hLf_q : ∀ i, CFSG.Open.IsQuasisimple ↥(Lf i) := by
      intro i
      rcases i with j | j
      · exact k329o3cp_open_of_native (hFq j).1
      · exact hS_q j
    have hF_perf : ∀ i, Group.IsPerfect ↥(F i) := fun i => (hFq i).1.1
    have hLf_c : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥ := by
      intro i j hij
      rcases i with a | a <;> rcases j with b | b
      · change ⁅F a, F b⁆ = ⊥
        apply le_bot_iff.mp
        rw [Subgroup.commutator_le]
        intro u hu v hv
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
        exact hFc a b (fun e => hij (by rw [e])) u hu v hv
      · change ⁅F a, S b⁆ = ⊥
        apply le_bot_iff.mp
        rw [Subgroup.commutator_le]
        intro u hu v hv
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
        have hu' : u ∈ supportedBlock Q x (X - 1) :=
          (hFq a).2.1.trans supportedFixedDerived_le_supportedBlock hu
        have hv' : v ∈ supportedBlock Q x (b.1 : K[X]) := specialBlock_le_supportedBlock _ hv
        exact hx.commute_supportedBlock hX1mem (hRep.1 b.1.2) b.2.1
          (by rw [reciprocalPolynomial_X_sub_one]; exact b.2.1) hu' hv'
      · change ⁅S a, F b⁆ = ⊥
        apply le_bot_iff.mp
        rw [Subgroup.commutator_le]
        intro u hu v hv
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
        have hu' : u ∈ supportedBlock Q x (a.1 : K[X]) := specialBlock_le_supportedBlock _ hu
        have hv' : v ∈ supportedBlock Q x (X - 1) :=
          (hFq b).2.1.trans supportedFixedDerived_le_supportedBlock hv
        exact (hx.commute_supportedBlock hX1mem (hRep.1 a.1.2) a.2.1
          (by rw [reciprocalPolynomial_X_sub_one]; exact a.2.1) hv' hu').symm
      · change ⁅S a, S b⁆ = ⊥
        exact hS_c a b (fun e => hij (by rw [e]))
    have hsfd_perf : ⁅supportedFixedDerived Q x, supportedFixedDerived Q x⁆ =
        supportedFixedDerived Q x := by
      rw [← hFsup]
      exact k329o3cp_perfect_iSup F fun i => Subgroup.isPerfect_iff.mp (hF_perf i)
    let D : Subgroup (V ≃ₗ[K] V) := supportedFixedDerived Q x ⊔ sfp
    have hD_C : D ≤ C := by
      refine sup_le ?_ ?_
      · exact le_inf supportedFixedDerived_le_isometryCentralizer
          hx.supportedFixedDerived_le_orthDerived
      · exact iSup_le hS_le_C
    have hcomm_le_D : ⁅C, C⁆ ≤ D := by
      rw [Subgroup.commutator_le]
      intro m hm m' hm'
      have hg : ⁅m, m'⁆ ∈ ⁅isometryCentralizer Q x, isometryCentralizer Q x⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp hm).1 (Subgroup.mem_inf.mp hm').1
      obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep hg
      rw [hgjf]
      have hBD : sfp ≤ D := le_sup_right
      have hAD : supportedFixedDerived Q x ≤ D := le_sup_left
      exact D.mul_mem (hBD (hsp_le_sfp hj)) (hAD hf)
    have hDperf : ⁅D, D⁆ = D := k329o3cp_perfect_sup hsfd_perf hsfp_perf
    have hres : K329Res C = D :=
      le_antisymm ((k329_res_le_commutator C).trans hcomm_le_D)
        (k329_perfect_le_res hD_C hDperf)
    have hjoin : (⨆ i : ι, Lf i) = D := by
      rw [iSup_sum]
      change (⨆ i : Fin nF, F i) ⊔ (⨆ i : ιS, S i) = supportedFixedDerived Q x ⊔ sfp
      rw [hFsup]
    exact ⟨ι, hι, Lf, hLf_q, hLf_c, hjoin.trans hres.symm⟩
  ·
    have hdim : finrank K (fixedSpace x) ≤ 2 := by omega
    have hsfp_le_C : sfp ≤ C := iSup_le hS_le_C
    have hres : K329Res C = sfp := by
      refine le_antisymm ?_ (k329_perfect_le_res hsfp_le_C hsfp_perf)
      have hkey : ⁅K329Res C, K329Res C⁆ ≤ sfp := by
        rw [Subgroup.commutator_le]
        intro m hm m' hm'
        have hmC : m ∈ C := (Subgroup.map_subtype_le (CFSG.perfectResidual ↥C)) hm
        have hm'C : m' ∈ C := (Subgroup.map_subtype_le (CFSG.perfectResidual ↥C)) hm'
        have hmM : m ∈ isometryCentralizer Q x := (Subgroup.mem_inf.mp hmC).1
        have hm'M : m' ∈ isometryCentralizer Q x := (Subgroup.mem_inf.mp hm'C).1
        have hmΩ : m ∈ CFSG.RankThree.Classical2.orthDerived Q := (Subgroup.mem_inf.mp hmC).2
        have hm'Ω : m' ∈ CFSG.RankThree.Classical2.orthDerived Q := (Subgroup.mem_inf.mp hm'C).2
        have hgM : ⁅m, m'⁆ ∈ isometryCentralizer Q x := by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem hmM hm'M) (inv_mem hmM)) (inv_mem hm'M)
        have hg : ⁅m, m'⁆ ∈ ⁅isometryCentralizer Q x, isometryCentralizer Q x⁆ :=
          Subgroup.commutator_mem_commutator hmM hm'M
        obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep hg
        have hfM : f ∈ isometryCentralizer Q x := supportedFixedDerived_le_isometryCentralizer hf
        have hjM : j ∈ isometryCentralizer Q x := hspM hj
        have h1 : isometryRestrictFixed Q x ⟨⁅m, m'⁆, hgM⟩ = 1 := by
          have h2 : (⟨⁅m, m'⁆, hgM⟩ : ↥(isometryCentralizer Q x)) =
              ⁅(⟨m, hmM⟩ : ↥(isometryCentralizer Q x)),
                (⟨m', hm'M⟩ : ↥(isometryCentralizer Q x))⁆ := Subtype.ext rfl
          rw [h2, map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr
            (hx.restrict_commute_of_mem_orthDerived hp2 hQ hRep hdim hmM hmΩ hm'M hm'Ω).eq
        have h3 : isometryRestrictFixed Q x ⟨f, hfM⟩ = 1 := by
          have h4 : (⟨⁅m, m'⁆, hgM⟩ : ↥(isometryCentralizer Q x)) = ⟨j, hjM⟩ * ⟨f, hfM⟩ :=
            Subtype.ext hgjf
          rw [h4, map_mul, hx.restrictFixed_trivial_of_mem_specialProduct hRep hj hjM,
            one_mul] at h1
          exact h1
        have hfB : f ∈ supportedBlock Q x (X - 1) := supportedFixedDerived_le_supportedBlock hf
        have h5 : restrictFixed Q x ⟨f, hfB⟩ = 1 := by
          rw [← isometryRestrictFixed_restrictFixed]
          exact h3
        have hf1 : f = 1 := hx.eq_one_of_restrictFixed_eq_one hfB h5
        rw [hgjf, hf1, mul_one]
        exact hsp_le_sfp hj
      rw [← k329_res_perfect C]
      exact hkey
    exact ⟨ιS, hιS, S, hS_q, hS_c, hres.symm⟩

private theorem k329o3cp_main (n : ℕ) (hadm : StatedLieAdmissible .POmegaPlus n 2 3)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3) :
    K329CentralProductMatrix (StatedOmega (StatedQuadPlus n K)) := by
  classical
  intro x hxZ hx3
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  let ι : Type := Fin n ⊕ Fin n
  let Qf : QuadraticForm K (ι → K) := CFSG.LieType.Universal.Spin.quadPlus n K
  let θ : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K
  let H : Subgroup (GL ι K) := StatedOmega (StatedQuadPlus n K)
  let C : Subgroup H := Subgroup.centralizer ({x} : Set H)
  let φ : H →* ((ι → K) ≃ₗ[K] (ι → K)) := θ.toMonoidHom.comp H.subtype
  have hφ : Function.Injective φ := by
    intro a b h
    apply Subtype.ext
    exact θ.injective h
  have hQ : (QuadraticMap.polarBilin Qf).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K
  have hSQ0 : H = (CFSG.RankThree.Classical2.orthDerived Qf).comap θ.toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (CFSG.LieType.Universal.Spin.coe_quadPlus n K)
  have hmem : θ.toMonoidHom x ∈ CFSG.RankThree.Classical2.orthDerived Qf := by
    have hx' : (x : GL ι K) ∈ (CFSG.RankThree.Classical2.orthDerived Qf).comap θ.toMonoidHom := by
      rw [← hSQ0]; exact x.2
    exact (Subgroup.mem_comap.mp hx')
  let xL : CFSG.RankThree.Classical2.orthDerived Qf := ⟨θ.toMonoidHom x, hmem⟩
  have hZhbot : K329Zh H = ⊥ := k329o3cp_zh_eq_bot n hn hK
  have hx3one : x ^ 3 = 1 := by
    have : x ^ 3 ∈ (⊥ : Subgroup H) := by rw [← hZhbot]; exact hx3
    simpa using this
  have hxne : x ≠ 1 := by
    intro h
    apply hxZ
    rw [h, hZhbot]
    simp
  have horderx : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3one
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hxne
    · exact h3
  have horderL : orderOf xL = 3 := by
    rw [Subgroup.orderOf_mk]
    exact (MulEquiv.orderOf_eq θ (↑x)).trans ((Subgroup.orderOf_coe x).trans horderx)
  have hchar : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  have hpl : 3 ≠ ringChar K := by
    have : CharP K 2 := hchar
    rw [ringChar.eq K 2]; norm_num
  have hx : OddOrderIsometry Qf 3 ↑xL :=
    oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ xL horderL
  have hHmap : H.map θ.toMonoidHom = CFSG.RankThree.Classical2.orthDerived Qf := by
    rw [hSQ0, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr θ.surjective, top_inf_eq]
  have hcentral : (Subgroup.centralizer ({↑x} : Set (GL ι K))).map θ.toMonoidHom =
      Subgroup.centralizer ({θ.toMonoidHom x} : Set ((ι → K) ≃ₗ[K] (ι → K))) := by
    apply le_antisymm
    · simpa [Set.image_singleton] using
        Subgroup.map_centralizer_le_centralizer_image ({↑x} : Set (GL ι K)) θ.toMonoidHom
    · intro g hg
      refine Subgroup.mem_map.mpr ⟨θ.symm g, ?_, θ.apply_symm_apply g⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      apply θ.injective
      rw [map_mul, map_mul, θ.apply_symm_apply]
      exact hg
  have hCeq : C = (Subgroup.centralizer ({↑x} : Set (GL ι K))).subgroupOf H := by
    ext c
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h; simpa using congrArg Subtype.val h
    · intro h; exact Subtype.ext (by simpa using h)
  have h1 : C.map H.subtype = Subgroup.centralizer ({↑x} : Set (GL ι K)) ⊓ H := by
    rw [hCeq, Subgroup.subgroupOf_map_subtype]
  have hCmap : C.map φ = isometryCentralizer Qf ↑xL ⊓
      CFSG.RankThree.Classical2.orthDerived Qf := by
    rw [show φ = θ.toMonoidHom.comp H.subtype from rfl, ← Subgroup.map_map, h1,
      Subgroup.map_inf _ _ θ.toMonoidHom θ.injective, hcentral, hHmap]
    rw [isometryCentralizer, inf_assoc,
      inf_eq_right.mpr (inf_le_right.trans (orthDerived_le_orthogonalGroup (Q := Qf)))]
  have hlin : K329CentralProduct (K329Res (isometryCentralizer Qf ↑xL ⊓
      CFSG.RankThree.Classical2.orthDerived Qf)) :=
    k329o3cp_linear hx hQ (by rw [hK]; norm_num)
  exact k329o3cp_transport φ hφ hCmap hlin

end K329O3CPPrivate

theorem k329_S3c_POmegaPlus (n : ℕ) (hadm : StatedLieAdmissible .POmegaPlus n 2 3) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3) :
    K329CentralProductMatrix (StatedOmega (StatedQuadPlus n K)) :=
  k329o3cp_main n hadm K hK

section K329O3CMPrivate

open Polynomial Module CFSG.Open CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open scoped commutatorElement

private theorem k329o3cm_open_of_native {G : Type*} [Group G] (h : CFSG.IsQuasisimple G) :
    CFSG.Open.IsQuasisimple G :=
  ⟨Group.isPerfect_def.mp h.1, h.2.1⟩

private theorem k329o3cm_perfect_iSup {G : Type*} [Group G] {ι : Type*} (F : ι → Subgroup G)
    (hF : ∀ i, ⁅F i, F i⁆ = F i) : ⁅⨆ i, F i, ⨆ i, F i⁆ = ⨆ i, F i := by
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) ?_
  refine iSup_le fun i => ?_
  calc F i = ⁅F i, F i⁆ := (hF i).symm
    _ ≤ ⁅⨆ i, F i, ⨆ i, F i⁆ :=
        Subgroup.commutator_mono (le_iSup F i) (le_iSup F i)

private theorem k329o3cm_zh_eq_bot (n : ℕ) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) (b c : K) :
    K329Zh (StatedOmega (StatedQuadMinus n K b c)) = ⊥ := by
  have hchar : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  have : CharP K 2 := hchar
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : (x : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) ∈
      StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K := Subgroup.mem_subgroupOf.mp hx
  obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hx'
  have h2 : (x : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) ^ 2 = 1 :=
    CFSG.HardMathSupport.Malle.E27Lie.sq_eq_one_of_mem_statedScalars
      (fun a v => by
        simp only [StatedQuadMinus, Pi.smul_apply, smul_eq_mul]
        have hs : ∑ x, a * v (Sum.inl x) * (a * v (Sum.inr (Sum.inl x))) =
            a ^ 2 * ∑ i, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hs]
        ring)
      (v₀ := Pi.single (Sum.inr (Sum.inr 0)) 1) (by simp [StatedQuadMinus])
      x.2 hx'
  have h3 : (Matrix.GeneralLinearGroup.scalar
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) d) ^ 2 = 1 := by
    rw [hd]; exact h2
  have hsq : (d : K) ^ 2 = 1 := by
    have hne : Nonempty (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    have h4 := congrArg (fun g : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K =>
      (g : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K)
        (Classical.choice hne) (Classical.choice hne)) h3
    simpa [← map_pow, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] using h4
  have hd1 : d = 1 := by
    apply Units.ext
    exact CharTwo.sq_inj.mp (by rw [hsq]; simp)
  have hx1 : (x : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) = 1 := by
    rw [← hd, hd1, map_one]
  exact Subtype.ext (by simpa using hx1)

private theorem k329o3cm_transport {H G : Type} [Group H] [Group G] [Finite H]
    (φ : H →* G) (hφ : Function.Injective φ) {C : Subgroup H} {D' : Subgroup G}
    (hD : C.map φ = D') (h : K329CentralProduct (K329Res D')) :
    K329CentralProduct (K329Res C) := by
  obtain ⟨ι, hι, Lf, hq, hc, hsup⟩ := h
  have hDrange : K329Res D' ≤ φ.range :=
    (Subgroup.map_subtype_le (CFSG.perfectResidual ↥D')).trans
      (hD.symm ▸ Subgroup.map_le_range φ C)
  have hle : ∀ i, Lf i ≤ φ.range := fun i =>
    (le_iSup Lf i).trans (hsup.le.trans hDrange)
  have hmapi : ∀ i, ((Lf i).comap φ).map φ = Lf i := fun i => by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr (hle i)]
  refine ⟨ι, hι, fun i => (Lf i).comap φ, ?_, ?_, ?_⟩
  · intro i
    let e : ↥((Lf i).comap φ) ≃* ↥(Lf i) :=
      (Subgroup.equivMapOfInjective ((Lf i).comap φ) φ hφ).trans
        (MulEquiv.subgroupCongr (hmapi i))
    exact k329_isQuasisimple_of_mulEquiv e.symm (hq i)
  · intro i j hij
    apply Subgroup.map_injective hφ
    rw [Subgroup.map_commutator, Subgroup.map_bot, hmapi i, hmapi j]
    exact hc i j hij
  · apply Subgroup.map_injective hφ
    rw [Subgroup.map_iSup]
    have h1 : (K329Res C).map φ = K329Res D' := by
      rw [k329_res_map, hD]
    exact (iSup_congr hmapi).trans (hsup.trans h1.symm)

end K329O3CMPrivate

section K329O3CMLinearPrivate

open Polynomial Module CFSG.Open CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open scoped commutatorElement

private theorem k329o3cm_linear
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hcard : Nat.card K = 8) :
    K329CentralProduct
      (K329Res (isometryCentralizer Q x ⊓ CFSG.RankThree.Classical2.orthDerived Q)) := by
  classical
  have hp2 : Odd 3 := by decide
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  let C : Subgroup (V ≃ₗ[K] V) :=
    isometryCentralizer Q x ⊓ CFSG.RankThree.Classical2.orthDerived Q
  let ιS : Type := {h : ↥Rep // (h : K[X]) ≠ X - 1 ∧
    2 ≤ primaryMultiplicity x.toLinearMap (h : K[X])}
  have hιS : Fintype ιS := inferInstance
  let S : ιS → Subgroup (V ≃ₗ[K] V) := fun h => specialBlock Q x (h.1 : K[X])
  have hS_q : ∀ i, CFSG.Open.IsQuasisimple ↥(S i) := by
    intro i
    exact k329o3cm_open_of_native
      (k329kc3_quasisimple_specialBlock hx Nat.prime_three (by norm_num)
        (hRep.1 i.1.2) i.2.1 i.2.2
        ⟨fun _ => by rw [hcard]; norm_num, fun _ => by rw [hcard]; norm_num⟩)
  have hS_perf : ∀ i, Group.IsPerfect ↥(S i) := fun i => Group.isPerfect_def.mpr (hS_q i).1
  have hS_c : ∀ i j, i ≠ j → ⁅S i, S j⁆ = ⊥ := by
    intro i j hij
    apply le_bot_iff.mp
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    have h1 : a ∈ supportedBlock Q x (i.1 : K[X]) := specialBlock_le_supportedBlock _ ha
    have h2 : b ∈ supportedBlock Q x (j.1 : K[X]) := specialBlock_le_supportedBlock _ hb
    have hij1 : (i.1 : K[X]) ≠ (j.1 : K[X]) := fun e => hij (Subtype.ext (Subtype.ext e))
    have hij2 : (j.1 : K[X]) ≠ (i.1 : K[X]) := fun e => hij (Subtype.ext (Subtype.ext e.symm))
    exact hx.commute_supportedBlock (hRep.1 i.1.2) (hRep.1 j.1.2) hij2
      (hRep.ne_reciprocal i.1.2 j.1.2 hij1) h1 h2
  have hS_le_C : ∀ i, S i ≤ C := by
    intro i
    exact le_inf (specialBlock_le_isometryCentralizer _)
      (k329kc3_specialBlock_le_orthDerived hx Nat.prime_three (by norm_num)
        (hRep.1 i.1.2) i.2.1 i.2.2
        ⟨fun _ => by rw [hcard]; norm_num, fun _ => by rw [hcard]; norm_num⟩)
  let sfp : Subgroup (V ≃ₗ[K] V) := ⨆ i, S i
  have hsfp_perf : ⁅sfp, sfp⁆ = sfp :=
    k329o3cm_perfect_iSup S (fun i => Subgroup.isPerfect_iff.mp (hS_perf i))
  have hsp_le_sfp : specialProduct Q x Rep ≤ sfp := by
    refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    by_cases hm : 2 ≤ primaryMultiplicity x.toLinearMap h
    · exact le_iSup S ⟨⟨h, hh⟩, hne, hm⟩
    · have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors (hRep.1 hh)⟩
      have hpos := hx.primaryMultiplicity_pos (hRep.1 hh)
      have hm1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
      rw [hx.specialBlock_eq_bot_of_finrank_eq_one (hRep.1 hh) hm1]
      exact bot_le
  have hspM : specialProduct Q x Rep ≤ isometryCentralizer Q x :=
    iSup₂_le fun h _ => iSup_le fun _ => specialBlock_le_isometryCentralizer h
  by_cases hW : 3 ≤ finrank K (fixedSpace x)
  ·
    have hX1mem : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
      by_contra hmem
      have hbot := fixedSpace_eq_bot_of_not_mem hmem
      have : finrank K (fixedSpace x) = 0 := by rw [hbot, finrank_bot]
      omega
    have hnexc : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype) := by
      intro hexc
      rcases hexc with ⟨-, h3⟩ | ⟨-, h23⟩
      · rw [hcard] at h3; omega
      · rcases h23 with h2 | h3
        · rw [hcard] at h2; omega
        · rw [hcard] at h3; omega
    have hcov : DerivedCoverage (Q.comp (fixedSpace x).subtype) :=
      ((orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype)
        hx.polarBilin_fixed_nondegenerate hW).2 hnexc)
    obtain ⟨nF, F, hnF1, hnF2, hFsup, hFq, hFc, -⟩ := hx.exists_supported_factors hcov
    let ι : Type := Fin nF ⊕ ιS
    have hι : Fintype ι := inferInstance
    let Lf : ι → Subgroup (V ≃ₗ[K] V) := Sum.elim F S
    have hLf_q : ∀ i, CFSG.Open.IsQuasisimple ↥(Lf i) := by
      intro i
      rcases i with j | j
      · exact k329o3cm_open_of_native (hFq j).1
      · exact hS_q j
    have hF_perf : ∀ i, Group.IsPerfect ↥(F i) := fun i => (hFq i).1.1
    have hLf_c : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥ := by
      intro i j hij
      rcases i with a | a <;> rcases j with b | b
      · change ⁅F a, F b⁆ = ⊥
        apply le_bot_iff.mp
        rw [Subgroup.commutator_le]
        intro u hu v hv
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
        exact hFc a b (fun e => hij (by rw [e])) u hu v hv
      · change ⁅F a, S b⁆ = ⊥
        apply le_bot_iff.mp
        rw [Subgroup.commutator_le]
        intro u hu v hv
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
        have hu' : u ∈ supportedBlock Q x (X - 1) :=
          (hFq a).2.1.trans supportedFixedDerived_le_supportedBlock hu
        have hv' : v ∈ supportedBlock Q x (b.1 : K[X]) := specialBlock_le_supportedBlock _ hv
        exact hx.commute_supportedBlock hX1mem (hRep.1 b.1.2) b.2.1
          (by rw [reciprocalPolynomial_X_sub_one]; exact b.2.1) hu' hv'
      · change ⁅S a, F b⁆ = ⊥
        apply le_bot_iff.mp
        rw [Subgroup.commutator_le]
        intro u hu v hv
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
        have hu' : u ∈ supportedBlock Q x (a.1 : K[X]) := specialBlock_le_supportedBlock _ hu
        have hv' : v ∈ supportedBlock Q x (X - 1) :=
          (hFq b).2.1.trans supportedFixedDerived_le_supportedBlock hv
        exact (hx.commute_supportedBlock hX1mem (hRep.1 a.1.2) a.2.1
          (by rw [reciprocalPolynomial_X_sub_one]; exact a.2.1) hv' hu').symm
      · change ⁅S a, S b⁆ = ⊥
        exact hS_c a b (fun e => hij (by rw [e]))
    have hsfd_perf : ⁅supportedFixedDerived Q x, supportedFixedDerived Q x⁆ =
        supportedFixedDerived Q x := by
      rw [← hFsup]
      exact k329o3cm_perfect_iSup F fun i => Subgroup.isPerfect_iff.mp (hF_perf i)
    let D : Subgroup (V ≃ₗ[K] V) := supportedFixedDerived Q x ⊔ sfp
    have hD_C : D ≤ C := by
      refine sup_le ?_ ?_
      · exact le_inf supportedFixedDerived_le_isometryCentralizer
          hx.supportedFixedDerived_le_orthDerived
      · exact iSup_le hS_le_C
    have hcomm_le_D : ⁅C, C⁆ ≤ D := by
      rw [Subgroup.commutator_le]
      intro m hm m' hm'
      have hg : ⁅m, m'⁆ ∈ ⁅isometryCentralizer Q x, isometryCentralizer Q x⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp hm).1 (Subgroup.mem_inf.mp hm').1
      obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep hg
      rw [hgjf]
      have hBD : sfp ≤ D := le_sup_right
      have hAD : supportedFixedDerived Q x ≤ D := le_sup_left
      exact D.mul_mem (hBD (hsp_le_sfp hj)) (hAD hf)
    have hDperf : ⁅D, D⁆ = D := by
      refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) ?_
      refine sup_le ?_ ?_
      · calc supportedFixedDerived Q x = ⁅supportedFixedDerived Q x, supportedFixedDerived Q x⁆ :=
            hsfd_perf.symm
          _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
      · calc sfp = ⁅sfp, sfp⁆ := hsfp_perf.symm
          _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
    have hres : K329Res C = D :=
      le_antisymm ((k329_res_le_commutator C).trans hcomm_le_D)
        (k329_perfect_le_res hD_C hDperf)
    have hjoin : (⨆ i : ι, Lf i) = D := by
      rw [iSup_sum]
      change (⨆ i : Fin nF, F i) ⊔ (⨆ i : ιS, S i) = supportedFixedDerived Q x ⊔ sfp
      rw [hFsup]
    exact ⟨ι, hι, Lf, hLf_q, hLf_c, hjoin.trans hres.symm⟩
  ·
    have hdim : finrank K (fixedSpace x) ≤ 2 := by omega
    have hsfp_le_C : sfp ≤ C := iSup_le hS_le_C
    have hres : K329Res C = sfp := by
      refine le_antisymm ?_ (k329_perfect_le_res hsfp_le_C hsfp_perf)
      have hkey : ⁅K329Res C, K329Res C⁆ ≤ sfp := by
        rw [Subgroup.commutator_le]
        intro m hm m' hm'
        have hmC : m ∈ C := (Subgroup.map_subtype_le (CFSG.perfectResidual ↥C)) hm
        have hm'C : m' ∈ C := (Subgroup.map_subtype_le (CFSG.perfectResidual ↥C)) hm'
        have hmM : m ∈ isometryCentralizer Q x := (Subgroup.mem_inf.mp hmC).1
        have hm'M : m' ∈ isometryCentralizer Q x := (Subgroup.mem_inf.mp hm'C).1
        have hmΩ : m ∈ CFSG.RankThree.Classical2.orthDerived Q := (Subgroup.mem_inf.mp hmC).2
        have hm'Ω : m' ∈ CFSG.RankThree.Classical2.orthDerived Q := (Subgroup.mem_inf.mp hm'C).2
        have hgM : ⁅m, m'⁆ ∈ isometryCentralizer Q x := by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem hmM hm'M) (inv_mem hmM)) (inv_mem hm'M)
        have hg : ⁅m, m'⁆ ∈ ⁅isometryCentralizer Q x, isometryCentralizer Q x⁆ :=
          Subgroup.commutator_mem_commutator hmM hm'M
        obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep hg
        have hfM : f ∈ isometryCentralizer Q x := supportedFixedDerived_le_isometryCentralizer hf
        have hjM : j ∈ isometryCentralizer Q x := hspM hj
        have h1 : isometryRestrictFixed Q x ⟨⁅m, m'⁆, hgM⟩ = 1 := by
          have h2 : (⟨⁅m, m'⁆, hgM⟩ : ↥(isometryCentralizer Q x)) =
              ⁅(⟨m, hmM⟩ : ↥(isometryCentralizer Q x)),
                (⟨m', hm'M⟩ : ↥(isometryCentralizer Q x))⁆ := Subtype.ext rfl
          rw [h2, map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr
            (hx.restrict_commute_of_mem_orthDerived hp2 hQ hRep hdim hmM hmΩ hm'M hm'Ω).eq
        have h3 : isometryRestrictFixed Q x ⟨f, hfM⟩ = 1 := by
          have h4 : (⟨⁅m, m'⁆, hgM⟩ : ↥(isometryCentralizer Q x)) = ⟨j, hjM⟩ * ⟨f, hfM⟩ :=
            Subtype.ext hgjf
          rw [h4, map_mul, hx.restrictFixed_trivial_of_mem_specialProduct hRep hj hjM,
            one_mul] at h1
          exact h1
        have hfB : f ∈ supportedBlock Q x (X - 1) := supportedFixedDerived_le_supportedBlock hf
        have h5 : restrictFixed Q x ⟨f, hfB⟩ = 1 := by
          rw [← isometryRestrictFixed_restrictFixed]
          exact h3
        have hf1 : f = 1 := hx.eq_one_of_restrictFixed_eq_one hfB h5
        rw [hgjf, hf1, mul_one]
        exact hsp_le_sfp hj
      rw [← k329_res_perfect C]
      exact hkey
    exact ⟨ιS, hιS, S, hS_q, hS_c, hres.symm⟩

end K329O3CMLinearPrivate

section K329O3CMMainPrivate

open CFSG.Open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2

private theorem k329o3cm_main (n : ℕ) (_hadm : StatedLieAdmissible .POmegaMinus n 2 3)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3) (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    K329CentralProductMatrix (StatedOmega (StatedQuadMinus n K b c)) := by
  classical
  intro x hxZ hx3
  let ι : Type := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2
  let Qf : QuadraticForm K (ι → K) := CFSG.LieType.Universal.Spin.quadMinus n K b c
  let θ : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K
  let H : Subgroup (GL ι K) := StatedOmega (StatedQuadMinus n K b c)
  let C : Subgroup H := Subgroup.centralizer ({x} : Set H)
  let φ : H →* ((ι → K) ≃ₗ[K] (ι → K)) := θ.toMonoidHom.comp H.subtype
  have hφ : Function.Injective φ := by
    intro a b h
    apply Subtype.ext
    exact θ.injective h
  have hQ : (QuadraticMap.polarBilin Qf).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hbc
  have hSQ0 : H = (CFSG.RankThree.Classical2.orthDerived Qf).comap θ.toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c)
  have hmem : θ.toMonoidHom x ∈ CFSG.RankThree.Classical2.orthDerived Qf := by
    have hx' : (x : GL ι K) ∈ (CFSG.RankThree.Classical2.orthDerived Qf).comap θ.toMonoidHom := by
      rw [← hSQ0]; exact x.2
    exact (Subgroup.mem_comap.mp hx')
  let xL : CFSG.RankThree.Classical2.orthDerived Qf := ⟨θ.toMonoidHom x, hmem⟩
  have hZhbot : K329Zh H = ⊥ := k329o3cm_zh_eq_bot n hK b c
  have hx3one : x ^ 3 = 1 := by
    have : x ^ 3 ∈ (⊥ : Subgroup H) := by rw [← hZhbot]; exact hx3
    simpa using this
  have hxne : x ≠ 1 := by
    intro h
    apply hxZ
    rw [h, hZhbot]
    simp
  have horderx : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3one
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hxne
    · exact h3
  have horderL : orderOf xL = 3 := by
    rw [Subgroup.orderOf_mk]
    exact (MulEquiv.orderOf_eq θ (↑x)).trans ((Subgroup.orderOf_coe x).trans horderx)
  have hchar : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  have hpl : 3 ≠ ringChar K := by
    have : CharP K 2 := hchar
    rw [ringChar.eq K 2]; norm_num
  have hx : OddOrderIsometry Qf 3 ↑xL :=
    oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ xL horderL
  have hHmap : H.map θ.toMonoidHom = CFSG.RankThree.Classical2.orthDerived Qf := by
    rw [hSQ0, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr θ.surjective, top_inf_eq]
  have hcentral : (Subgroup.centralizer ({↑x} : Set (GL ι K))).map θ.toMonoidHom =
      Subgroup.centralizer ({θ.toMonoidHom x} : Set ((ι → K) ≃ₗ[K] (ι → K))) := by
    apply le_antisymm
    · simpa [Set.image_singleton] using
        Subgroup.map_centralizer_le_centralizer_image ({↑x} : Set (GL ι K)) θ.toMonoidHom
    · intro g hg
      refine Subgroup.mem_map.mpr ⟨θ.symm g, ?_, θ.apply_symm_apply g⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      apply θ.injective
      rw [map_mul, map_mul, θ.apply_symm_apply]
      exact hg
  have hCeq : C = (Subgroup.centralizer ({↑x} : Set (GL ι K))).subgroupOf H := by
    ext c
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h; simpa using congrArg Subtype.val h
    · intro h; exact Subtype.ext (by simpa using h)
  have h1 : C.map H.subtype = Subgroup.centralizer ({↑x} : Set (GL ι K)) ⊓ H := by
    rw [hCeq, Subgroup.subgroupOf_map_subtype]
  have hCmap : C.map φ = isometryCentralizer Qf ↑xL ⊓
      CFSG.RankThree.Classical2.orthDerived Qf := by
    rw [show φ = θ.toMonoidHom.comp H.subtype from rfl, ← Subgroup.map_map, h1,
      Subgroup.map_inf _ _ θ.toMonoidHom θ.injective, hcentral, hHmap]
    rw [isometryCentralizer, inf_assoc,
      inf_eq_right.mpr (inf_le_right.trans (orthDerived_le_orthogonalGroup (Q := Qf)))]
  have hlin : K329CentralProduct (K329Res (isometryCentralizer Qf ↑xL ⊓
      CFSG.RankThree.Classical2.orthDerived Qf)) :=
    k329o3cm_linear hx hQ (by rw [hK]; norm_num)
  exact k329o3cm_transport φ hφ hCmap hlin

end K329O3CMMainPrivate

theorem k329_S3c_POmegaMinus (n : ℕ) (hadm : StatedLieAdmissible .POmegaMinus n 2 3) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3) (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    K329CentralProductMatrix (StatedOmega (StatedQuadMinus n K b c)) :=
  k329o3cm_main n hadm K hK b c hbc

theorem k329_S4_POmegaPlus (n : ℕ) (hadm : StatedLieAdmissible .POmegaPlus n 2 3) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3) :
    K329SchurMatrix (StatedOmega (StatedQuadPlus n K)) := by
  intro x hxZh hx3Zh R hRC _hR3 hRcomm a ha b hb
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  have hchar : CharP K 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 3) hK
  have : CharP K 2 := hchar
  let φ := CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n ⊕ Fin n) K
  let H := StatedOmega (StatedQuadPlus n K)
  let Qf := CFSG.LieType.Universal.Spin.quadPlus n K
  have hΩ : H = (orthDerived Qf).comap φ.toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (CFSG.LieType.Universal.Spin.coe_quadPlus n K)
  have hZh : K329Zh H = ⊥ :=
    CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot (K := K) hn
  have hx1 : x ≠ 1 := by
    intro h1
    exact hxZh (by rw [hZh, h1]; exact Subgroup.mem_bot.mpr rfl)
  have hx3 : x ^ 3 = 1 := by
    have := hx3Zh
    rw [hZh, Subgroup.mem_bot] at this
    exact this
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxLmem : φ x ∈ orthDerived Qf := by
    have hxH : (x : GL (Fin n ⊕ Fin n) K) ∈ H := x.2
    rw [hΩ] at hxH
    exact hxH
  let xL : orthDerived Qf := ⟨φ x, hxLmem⟩
  have hxLcoe : (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) = φ x := rfl
  have hxLord : orderOf xL = 3 := by
    have h1 : orderOf (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) = orderOf x := by
      rw [hxLcoe]
      exact (orderOf_injective φ.toMonoidHom φ.injective x).trans (Subgroup.orderOf_coe x)
    rw [← Subgroup.orderOf_coe xL, h1, hxord]
  have hxo : OddOrderIsometry Qf 3 (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
    oddOrderIsometry_of_orthDerived Nat.prime_three
      (by rw [ringChar.eq K 2]; norm_num)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K) xL hxLord
  have hsq : Squarefree (minpoly K (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K]
      (Fin n ⊕ Fin n → K)).toLinearMap) := hxo.squarefree_minpoly
  obtain ⟨Rep, hRep⟩ := hxo.exists_orbitRepresentatives
  have hQnd : (QuadraticMap.polarBilin Qf).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K
  have haΩ : φ a ∈ orthDerived Qf := by
    have haH : (a : GL (Fin n ⊕ Fin n) K) ∈ H := a.2
    rw [hΩ] at haH
    exact haH
  have hbΩ : φ b ∈ orthDerived Qf := by
    have hbH : (b : GL (Fin n ⊕ Fin n) K) ∈ H := b.2
    rw [hΩ] at hbH
    exact hbH
  have haMc : φ a ∈ Subgroup.centralizer ({(xL : (Fin n ⊕ Fin n → K) ≃ₗ[K]
      (Fin n ⊕ Fin n → K))} : Set _) := by
    have hac : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.mp (hRC ha)
    have h2 := congrArg (fun g : H => φ ((g : H) : GL (Fin n ⊕ Fin n) K)) hac
    rw [Subgroup.mem_centralizer_singleton_iff, hxLcoe]
    simpa only [Subgroup.coe_mul, map_mul] using h2
  have hbMc : φ b ∈ Subgroup.centralizer ({(xL : (Fin n ⊕ Fin n → K) ≃ₗ[K]
      (Fin n ⊕ Fin n → K))} : Set _) := by
    have hbc : b * x = x * b := Subgroup.mem_centralizer_singleton_iff.mp (hRC hb)
    have h2 := congrArg (fun g : H => φ ((g : H) : GL (Fin n ⊕ Fin n) K)) hbc
    rw [Subgroup.mem_centralizer_singleton_iff, hxLcoe]
    simpa only [Subgroup.coe_mul, map_mul] using h2
  have haM : φ a ∈ isometryCentralizer Qf (xL :
      (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
    Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup haΩ, haMc⟩
  have hbM : φ b ∈ isometryCentralizer Qf (xL :
      (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
    Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup hbΩ, hbMc⟩
  let za : CFSG.RankThree.PartOne.KCPrimary.commutant
      (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)).toLinearMap :=
    ⟨(φ a).toLinearMap,
      (CFSG.RankThree.PartOne.KCPrimary.mem_commutant
        (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)).toLinearMap).mpr
        (commute_toLinearMap_of_mem_centralizer (x := (xL :
          (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))) (g := φ a) haMc)⟩
  let zb : CFSG.RankThree.PartOne.KCPrimary.commutant
      (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)).toLinearMap :=
    ⟨(φ b).toLinearMap,
      (CFSG.RankThree.PartOne.KCPrimary.mem_commutant
        (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)).toLinearMap).mpr
        (commute_toLinearMap_of_mem_centralizer (x := (xL :
          (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))) (g := φ b) hbMc)⟩
  have hcoord : ∀ i : CFSG.RankThree.PartOne.KCPrimary.primaryFactors
      (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)).toLinearMap,
      (CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq za) i *
        (CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq zb) i =
      (CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq zb) i *
        (CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq za) i := by
    intro i
    by_cases hi : (i : K[X]) = X - 1
    · have hiv : ∀ v : CFSG.RankThree.PartOne.KCPrimary.primaryComponent
          (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)).toLinearMap (i : K[X]),
          (v : (Fin n ⊕ Fin n → K)) ∈ fixedSpace (xL :
            (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) := by
        intro v
        rw [fixedSpace_eq_primaryComponent, ← hi]
        exact v.2
      by_cases hdim : finrank K (fixedSpace (xL :
          (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))) ≤ 2
      · refine k329o4p_coord_commute hsq (fun v => ?_)
        exact k329o4p_fixed_coord_commute hxo (by decide : Odd 3) hQnd hRep hdim haM haΩ hbM
          hbΩ ⟨(v : (Fin n ⊕ Fin n → K)),
            by rw [← fixedSpace_eq_primaryComponent]; exact hiv v⟩
      · have h3 : 3 ≤ finrank K (fixedSpace (xL :
            (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))) := by omega
        have hcomm_fixed_a : ∀ f ∈ supportedFixedDerived Qf (xL :
            (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)), ∀ v,
            (φ a) (f v) = f ((φ a) v) := by
          have hperf : ⁅supportedFixedDerived Qf (xL :
              (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)),
              supportedFixedDerived Qf (xL :
              (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))⁆ =
              supportedFixedDerived Qf (xL :
              (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
            k329o4p_supportedFixedDerived_perfect hxo hK h3
          have hcomm := k329o4p_commute_of_perfect_subgroup hΩ
            hxo.supportedFixedDerived_le_orthDerived
            supportedFixedDerived_le_isometryCentralizer hperf hRcomm ha
          intro f hf v
          have h4 := congrArg (fun e : (Fin n ⊕ Fin n → K) ≃ₗ[K]
            (Fin n ⊕ Fin n → K) => e v) (hcomm f hf).eq
          simpa only [LinearEquiv.mul_apply] using h4
        obtain ⟨c, hc⟩ := k329o4p_fixed_scalar hxo haM hcomm_fixed_a h3 (by rw [hK]; norm_num)
        refine k329o4p_coord_commute hsq (fun v => ?_)
        show (φ a) ((φ b) (v : (Fin n ⊕ Fin n → K))) =
          (φ b) ((φ a) (v : (Fin n ⊕ Fin n → K)))
        have hv := hiv v
        have hvb : (φ b) (v : (Fin n ⊕ Fin n → K)) ∈ fixedSpace (xL :
            (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
          mem_fixedSpace_of_apply hbMc hv
        have h1 : (φ a) ((φ b) (v : (Fin n ⊕ Fin n → K))) =
            c • ((φ b) (v : (Fin n ⊕ Fin n → K))) := by
          rw [← coe_isometryRestrictFixed (g := ⟨φ a, haM⟩)
            (w := ⟨(φ b) (v : (Fin n ⊕ Fin n → K)), hvb⟩)]
          exact hc ⟨(φ b) (v : (Fin n ⊕ Fin n → K)), hvb⟩
        have h2 : (φ a) (v : (Fin n ⊕ Fin n → K)) = c • (v : (Fin n ⊕ Fin n → K)) := by
          rw [← coe_isometryRestrictFixed (g := ⟨φ a, haM⟩)
            (w := ⟨(v : (Fin n ⊕ Fin n → K)), hv⟩)]
          exact hc ⟨(v : (Fin n ⊕ Fin n → K)), hv⟩
        rw [h1, h2, map_smul]
    · have hi_eq : (i : K[X]) = X ^ 2 + X + 1 := by
        rcases k329o4p_primaryFactors_eq hK hxo.pow_eq_one i.2 with h | h
        · exact absurd h hi
        · exact h
      have hself : (i : K[X]) = reciprocalPolynomial (i : K[X]) := by
        rw [hi_eq, k329o4p_recip_quad]
      by_cases hm : 2 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
          (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)).toLinearMap (i : K[X])
      · have hq : (CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
              (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)).toLinearMap
              (i : K[X]) = 2 → 4 ≤ Nat.card K) ∧
            (CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
              (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)).toLinearMap
              (i : K[X]) = 3 → 3 ≤ Nat.card K) :=
          ⟨fun _ => by rw [hK]; norm_num, fun _ => by rw [hK]; norm_num⟩
        have hcomm_spec_a : ∀ f ∈ specialBlock Qf (xL :
            (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) (i : K[X]), ∀ v,
            (φ a) (f v) = f ((φ a) v) := by
          have hperf : ⁅specialBlock Qf (xL :
              (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) (i : K[X]),
              specialBlock Qf (xL :
              (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) (i : K[X])⁆ =
              specialBlock Qf (xL :
              (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) (i : K[X]) :=
            Subgroup.isPerfect_iff.mp (k329kc3_quasisimple_specialBlock hxo Nat.prime_three
              (by norm_num) i.2 hi hm hq).1
          have hcomm := k329o4p_commute_of_perfect_subgroup hΩ
            (k329kc3_specialBlock_le_orthDerived hxo Nat.prime_three (by norm_num) i.2 hi hm hq)
            (specialBlock_le_isometryCentralizer (i : K[X])) hperf hRcomm ha
          intro f hf v
          have h4 := congrArg (fun e : (Fin n ⊕ Fin n → K) ≃ₗ[K]
            (Fin n ⊕ Fin n → K) => e v) (hcomm f hf).eq
          simpa only [LinearEquiv.mul_apply] using h4
        obtain ⟨c, hc⟩ := k329kc3_exists_smul_of_commute_selfDual hxo (by decide : Odd 3) i.2 hi
          hself hm haMc hcomm_spec_a
        have hfa : (CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq za) i =
            c • (1 : Module.End (AdjoinRoot (i : K[X]))
              (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
                (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K]
                  (Fin n ⊕ Fin n → K)).toLinearMap (i : K[X]))) := by
          apply LinearMap.ext
          intro w
          apply Subtype.ext
          rw [CFSG.RankThree.PartOne.KCPrimary.coe_commutantEquivPi_apply]
          simp only [LinearMap.smul_apply, Module.End.one_apply]
          exact hc w
        rw [hfa, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_mul, mul_one]
      · have hle : Module.finrank (AdjoinRoot (i : K[X]))
            (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
              (xL : (Fin n ⊕ Fin n → K) ≃ₗ[K]
                (Fin n ⊕ Fin n → K)).toLinearMap (i : K[X])) ≤ 1 := by
          have hlt := Nat.lt_of_not_le hm
          simpa [CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity] using hlt
        exact CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one hle
          ((CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq za) i)
          ((CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq zb) i)
  have hprod : (CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq za) *
      (CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq zb) =
      (CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq zb) *
      (CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq za) := funext hcoord
  have hzz : za * zb = zb * za := (CFSG.RankThree.PartOne.KCPrimary.commutantEquivPi hsq).injective (by
    rw [map_mul, map_mul, hprod])
  have hlm : (φ a).toLinearMap * (φ b).toLinearMap =
      (φ b).toLinearMap * (φ a).toLinearMap := congrArg Subtype.val hzz
  have hφ : φ a * φ b = φ b * φ a := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact congrArg (fun f : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) => f v) hlm
  apply Subgroup.subtype_injective H
  rw [map_mul, map_mul]
  apply φ.injective
  rw [map_mul, map_mul]
  exact hφ

open CFSG.Open (StatedLieAdmissible StatedOmega StatedQuadMinus StatedScalars)

private theorem k329o4m_minus_smul (n : ℕ) {K : Type} [Field K] (b c : K) :
    ∀ (a : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      StatedQuadMinus n K b c (a • v) = a ^ 2 * StatedQuadMinus n K b c v := by
  intro a v
  simp only [StatedQuadMinus, Pi.smul_apply, smul_eq_mul]
  have hs : ∑ x, a * v (Sum.inl x) * (a * v (Sum.inr (Sum.inl x))) =
      a ^ 2 * ∑ i, v (Sum.inl i) * v (Sum.inr (Sum.inl i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs]
  ring

private theorem k329o4m_minus_ne_zero (n : ℕ) {K : Type} [Field K] (b c : K) :
    StatedQuadMinus n K b c (Pi.single (Sum.inr (Sum.inr 0)) 1) ≠ 0 := by
  simp [StatedQuadMinus]

private theorem k329o4m_eq_one_of_mem_zh {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [CharP K 2] {Q : (ι → K) → K}
    (hQ : ∀ (c : K) v, Q (c • v) = c ^ 2 * Q v) {v₀ : ι → K} (hv₀ : Q v₀ ≠ 0) :
    ∀ ω ∈ K329Zh (StatedOmega Q), ω = 1 := by
  intro ω hω
  have hωS : (ω : GL ι K) ∈ StatedScalars ι K := hω
  have hωH : (ω : GL ι K) ∈ StatedOmega Q := ω.2
  have hsq : (ω : GL ι K) ^ 2 = 1 :=
    CFSG.HardMathSupport.Malle.E27Lie.sq_eq_one_of_mem_statedScalars hQ hv₀ hωH hωS
  obtain ⟨c, hc⟩ := hωS
  rcases isEmpty_or_nonempty ι with hι | hne
  · have := hι
    exact Subtype.ext (Matrix.GeneralLinearGroup.ext fun i => isEmptyElim i)
  · have := hne
    let i₀ : ι := Classical.choice hne
    have h2' : (Matrix.GeneralLinearGroup.scalar ι c) ^ 2 = 1 := by
      rw [hc]
      exact hsq
    have hsqK : (c : K) ^ 2 = 1 := by
      have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) i₀ i₀) h2'
      simpa [← map_pow, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] using this
    have hc1 : c = 1 := by
      apply Units.ext
      have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have h2c : (2 : K) * (c : K) = 0 := by rw [h2K, zero_mul]
      have hsq0 : ((c : K) - 1) * ((c : K) - 1) = 0 := by
        calc ((c : K) - 1) * ((c : K) - 1) = (c : K) ^ 2 - 2 * (c : K) + 1 := by ring
          _ = 1 - 0 + 1 := by rw [hsqK, h2c]
          _ = 0 := by rw [show (1 : K) - 0 + 1 = 2 by ring, h2K]
      have hzero : (c : K) - 1 = 0 := mul_self_eq_zero.mp hsq0
      have hval : (c : K) = 1 := sub_eq_zero.mp hzero
      simpa using hval
    exact Subtype.ext (by rw [← hc, hc1]; simp)

private theorem k329o4m_zh_eq_bot (n : ℕ) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) (b c : K) :
    K329Zh (StatedOmega (StatedQuadMinus n K b c)) = ⊥ := by
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  rw [Subgroup.eq_bot_iff_forall]
  exact k329o4m_eq_one_of_mem_zh (k329o4m_minus_smul n b c) (k329o4m_minus_ne_zero n b c)

private theorem k329o4m_orderOf_eq_three {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) (hZ : K329Zh H = ⊥) {x : ↥H} (hxZ : x ∉ K329Zh H)
    (hx3 : x ^ 3 ∈ K329Zh H) : orderOf x = 3 := by
  have hx3' : x ^ 3 = 1 := by
    have := hx3
    rw [hZ] at this
    simpa using this
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ Subgroup.one_mem _)
  exact orderOf_eq_prime hx3' hx1

theorem k329_S4_POmegaMinus (n : ℕ) (hadm : StatedLieAdmissible .POmegaMinus n 2 3) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3) (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    K329SchurMatrix (StatedOmega (StatedQuadMinus n K b c)) := by
  classical
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  have hn : 4 ≤ n := hadm.2.2
  let ι : Type := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2
  let Qf : QuadraticForm K (ι → K) := CFSG.LieType.Universal.Spin.quadMinus n K b c
  let θ : GL ι K ≃* (ι → K) ≃ₗ[K] (ι → K) := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K
  intro x hxZ hx3 R hRC hR3 hcomm g₁ hg₁ g₂ hg₂
  let θx : (ι → K) ≃ₗ[K] (ι → K) := θ (x : GL ι K)
  let W : Submodule K (ι → K) := fixedSpace θx
  let g₁θ : (ι → K) ≃ₗ[K] (ι → K) := θ (g₁ : GL ι K)
  let g₂θ : (ι → K) ≃ₗ[K] (ι → K) := θ (g₂ : GL ι K)
  let T : Module.End K (ι → K) := θx.toLinearMap
  have hZ : K329Zh (StatedOmega (StatedQuadMinus n K b c)) = ⊥ := k329o4m_zh_eq_bot n hK b c
  have hxord3 : orderOf x = 3 :=
    k329o4m_orderOf_eq_three _ hZ hxZ hx3
  have hH : StatedOmega (StatedQuadMinus n K b c) =
      (CFSG.RankThree.Classical2.orthDerived Qf).comap θ.toMonoidHom := by
    simpa [Qf, θ, CFSG.RankThree.Classical2.orthDerived] using
      CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
        (Q := Qf) (Q₀ := StatedQuadMinus n K b c)
        (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c)
  have hθx : θx ∈ CFSG.RankThree.Classical2.orthDerived Qf := by
    have hxH : (x : GL ι K) ∈
        (CFSG.RankThree.Classical2.orthDerived Qf).comap θ.toMonoidHom := hH ▸ x.2
    simpa using hxH
  let xL : ↥(CFSG.RankThree.Classical2.orthDerived Qf) := ⟨θx, hθx⟩
  have hxordL : orderOf xL = 3 := by
    have h2 : orderOf xL = orderOf (θx) := (Subgroup.orderOf_coe xL).symm
    have h3 : orderOf (θx) = orderOf (x : GL ι K) := θ.orderOf_eq (x : GL ι K)
    have h4 : orderOf (x : GL ι K) = orderOf x := Subgroup.orderOf_coe x
    rw [h2, h3, h4, hxord3]
  have hQnd : (QuadraticMap.polarBilin Qf).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hbc
  have hpl : (3 : ℕ) ≠ ringChar K := by
    rw [ringChar.eq K 2]
    norm_num
  have hx : OddOrderIsometry Qf 3 (θx) :=
    oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQnd xL hxordL
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  have hθaΩ : g₁θ ∈ CFSG.RankThree.Classical2.orthDerived Qf := by
    have hxH : (g₁ : GL ι K) ∈
        (CFSG.RankThree.Classical2.orthDerived Qf).comap θ.toMonoidHom := hH ▸ g₁.2
    simpa using hxH
  have hθbΩ : g₂θ ∈ CFSG.RankThree.Classical2.orthDerived Qf := by
    have hxH : (g₂ : GL ι K) ∈
        (CFSG.RankThree.Classical2.orthDerived Qf).comap θ.toMonoidHom := hH ▸ g₂.2
    simpa using hxH
  have haxH : (g₁ : GL ι K) * (x : GL ι K) = (x : GL ι K) * (g₁ : GL ι K) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hRC hg₁))
  have hbxH : (g₂ : GL ι K) * (x : GL ι K) = (x : GL ι K) * (g₂ : GL ι K) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hRC hg₂))
  have hMa : g₁θ ∈ isometryCentralizer Qf (θx) := by
    refine mem_isometryCentralizer.mpr ⟨fun v => ?_, fun v => ?_⟩
    · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup hθaΩ) v
    · have hcθ : g₁θ * θx = θx * g₁θ := by
        rw [← map_mul, ← map_mul, haxH]
      exact congrArg (fun f : (ι → K) ≃ₗ[K] (ι → K) => f v) hcθ
  have hMb : g₂θ ∈ isometryCentralizer Qf (θx) := by
    refine mem_isometryCentralizer.mpr ⟨fun v => ?_, fun v => ?_⟩
    · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup hθbΩ) v
    · have hcθ : g₂θ * θx = θx * g₂θ := by
        rw [← map_mul, ← map_mul, hbxH]
      exact congrArg (fun f : (ι → K) ≃ₗ[K] (ι → K) => f v) hcθ
  have hHmap : (StatedOmega (StatedQuadMinus n K b c)).map θ.toMonoidHom =
      CFSG.RankThree.Classical2.orthDerived Qf := by
    rw [hH, Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr θ.surjective, top_inf_eq]
  have key_comm : ∀ {S : Subgroup ((ι → K) ≃ₗ[K] (ι → K))},
      S ≤ CFSG.RankThree.Classical2.orthDerived Qf → ⁅S, S⁆ = S →
      S ≤ isometryCentralizer Qf (θx) →
      ∀ g : ↥(StatedOmega (StatedQuadMinus n K b c)), g ∈ R →
      ∀ s ∈ S, Commute (θ (g : GL ι K)) s := by
    intro S hSorth hSperf hSc g hg s hs
    let H := StatedOmega (StatedQuadMinus n K b c)
    let e : ↥H →* (ι → K) ≃ₗ[K] (ι → K) := θ.toMonoidHom.comp H.subtype
    let P : Subgroup ↥H := (S.comap θ.toMonoidHom).subgroupOf H
    have he : Function.Injective e := fun a b h => Subtype.ext (θ.injective h)
    have hPe : P.map e = S := by
      ext s
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact Subgroup.mem_subgroupOf.mp hp
      · intro hsS
        have hsmap : s ∈ H.map θ.toMonoidHom := by
          rw [hHmap]; exact hSorth hsS
        obtain ⟨A, hA, hAeq⟩ := Subgroup.mem_map.mp hsmap
        refine ⟨⟨A, hA⟩, ?_, hAeq⟩
        exact Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_comap.mpr (by change θ.toMonoidHom A ∈ S; rw [hAeq]; exact hsS))
    have hPperf : ⁅P, P⁆ = P := by
      refine le_antisymm (Subgroup.commutator_le_self P) ?_
      have hmap : P.map e ≤ (⁅P, P⁆).map e := by
        rw [Subgroup.map_commutator, hPe, hSperf]
      exact (Subgroup.map_le_map_iff_of_injective (f := e) he).mp hmap
    have hPc : P ≤ Subgroup.centralizer ({x} : Set ↥H) := by
      intro p hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      apply θ.injective
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      have hpS : θ (p : GL ι K) ∈ S := Subgroup.mem_subgroupOf.mp hp
      exact LinearEquiv.ext (fun v => (mem_isometryCentralizer.mp (hSc hpS)).2 v)
    have hPle : P ≤ K329Lres x := k329_perfect_le_res hPc hPperf
    have hRcent : R ≤ Subgroup.centralizer (K329Lres x : Set ↥H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hs' : s ∈ P.map e := by rw [hPe]; exact hs
    obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp hs'
    have hgp : g * p = p * g := (Subgroup.mem_centralizer_iff.mp (hRcent hg) p (hPle hp)).symm
    have hgpGL : (g : GL ι K) * (p : GL ι K) = (p : GL ι K) * (g : GL ι K) :=
      congrArg Subtype.val hgp
    have hgpθ : θ (g : GL ι K) * θ (p : GL ι K) = θ (p : GL ι K) * θ (g : GL ι K) := by
      rw [← map_mul, ← map_mul, hgpGL]
    rw [← hpe]
    exact hgpθ
  have key_fixed_scalar : ∀ (g : ↥(StatedOmega (StatedQuadMinus n K b c))),
      g ∈ R → ∀ (hMg : θ (g : GL ι K) ∈ isometryCentralizer Qf (θx)),
      3 ≤ Module.finrank K (W) →
      ∃ c : K, (isometryRestrictFixed Qf (θx) ⟨θ (g : GL ι K), hMg⟩).toLinearMap =
        c • LinearMap.id := by
    intro g hg hMg hW3
    have hPFperf : Group.IsPerfect ↥(supportedFixedDerived Qf (θx)) :=
      CFSG.RankThree.PartOne.KCOrthComm.isPerfect_supportedFixedDerived hx
        (by rw [hK]; norm_num) hW3
    have hScomm := key_comm
      (OddOrderIsometry.supportedFixedDerived_le_orthDerived hx)
      (Subgroup.isPerfect_iff.mp hPFperf)
      (supportedFixedDerived_le_isometryCentralizer (Q := Qf) (x := θx))
      g hg
    have hcomm_orth : ∀ p ∈ CFSG.RankThree.Classical2.orthDerived
          (Qf.comp (W).subtype),
        (isometryRestrictFixed Qf (θx) ⟨θ (g : GL ι K), hMg⟩).toLinearMap ∘ₗ
            p.toLinearMap =
          p.toLinearMap ∘ₗ
            (isometryRestrictFixed Qf (θx) ⟨θ (g : GL ι K), hMg⟩).toLinearMap := by
      intro p hp
      obtain ⟨gF, hgF⟩ := restrictFixed_surjective hx p (orthDerived_le_orthogonalGroup hp)
      have hgFPF : gF.1 ∈ supportedFixedDerived Qf (θx) := by
        refine mem_supportedFixedDerived.mpr ⟨gF.2, ?_⟩
        rwa [hgF]
      have hcommPF : Commute (θ (g : GL ι K)) gF.1 := hScomm gF.1 hgFPF
      have hcomm_sub : Commute
          (⟨θ (g : GL ι K), hMg⟩ : ↥(isometryCentralizer Qf (θx)))
          ⟨gF.1, supportedFixedDerived_le_isometryCentralizer hgFPF⟩ :=
        Subtype.ext hcommPF.eq
      have hcommγ := congrArg (isometryRestrictFixed Qf (θx)) hcomm_sub.eq
      rw [map_mul, map_mul] at hcommγ
      have hδ : isometryRestrictFixed Qf (θx)
          ⟨gF.1, supportedFixedDerived_le_isometryCentralizer hgFPF⟩ = p := by
        rw [isometryRestrictFixed_restrictFixed]
        exact hgF
      rw [hδ] at hcommγ
      refine LinearMap.ext fun w => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      have hw := congrArg
        (fun f : W ≃ₗ[K] W => f w) hcommγ
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hw
      exact hw
    obtain ⟨c, hc⟩ := ((CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar
      (K := K) (W := W) (by rw [hK]; norm_num)
      (Qf.comp (W).subtype)
      hx.polarBilin_fixed_nondegenerate hW3).1
      (isometryRestrictFixed Qf (θx) ⟨θ (g : GL ι K), hMg⟩).toLinearMap).mp hcomm_orth
    exact ⟨c, hc⟩
  have hcommθ : g₁θ * g₂θ = g₂θ * g₁θ := by
    have hlin : (g₁θ * g₂θ).toLinearMap =
        (g₂θ * g₁θ).toLinearMap := by
      refine CFSG.RankThree.PartOne.KCPrimary.ext_primaryComponent hx.squarefree_minpoly
        fun h0 hh0 v hv => ?_
      by_cases h0X : h0 = X - 1
      · subst h0
        show g₁θ (g₂θ v) = g₂θ (g₁θ v)
        have hvW : v ∈ W := by
          change v ∈ fixedSpace θx
          rw [fixedSpace_eq_primaryComponent]
          exact hv
        have hγ : Commute
            (isometryRestrictFixed Qf (θx) ⟨g₁θ, hMa⟩)
            (isometryRestrictFixed Qf (θx) ⟨g₂θ, hMb⟩) := by
          by_cases hdim : Module.finrank K (W) ≤ 2
          · exact hx.restrict_commute_of_mem_orthDerived (by decide : Odd 3) hQnd hRep hdim
              hMa hθaΩ hMb hθbΩ
          · have hW3 : 3 ≤ Module.finrank K (W) := by omega
            obtain ⟨c, hc⟩ := key_fixed_scalar g₁ hg₁ hMa hW3
            have h1 : ∀ w : W,
                (isometryRestrictFixed Qf (θx) ⟨g₁θ, hMa⟩) w = c • w :=
              fun w => congrArg (fun f : W →ₗ[K] W => f w) hc
            refine LinearEquiv.ext fun w => ?_
            simp only [LinearEquiv.mul_apply]
            rw [h1 ((isometryRestrictFixed Qf (θx) ⟨g₂θ, hMb⟩) w), h1 w, map_smul]
        have hwW : (isometryRestrictFixed Qf (θx) ⟨g₁θ, hMa⟩)
            ((isometryRestrictFixed Qf (θx) ⟨g₂θ, hMb⟩) ⟨v, hvW⟩) =
            (isometryRestrictFixed Qf (θx) ⟨g₂θ, hMb⟩)
              ((isometryRestrictFixed Qf (θx) ⟨g₁θ, hMa⟩) ⟨v, hvW⟩) := by
          have := congrArg (fun f : W ≃ₗ[K] W => f ⟨v, hvW⟩) hγ.eq
          rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
        have hw := congrArg (fun w : W => (w : ι → K)) hwW
        rw [coe_isometryRestrictFixed, coe_isometryRestrictFixed] at hw
        rw [coe_isometryRestrictFixed, coe_isometryRestrictFixed] at hw
        simpa only [g₁θ, g₂θ] using hw
      · have : Fact (Irreducible h0) :=
          ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh0⟩
        have hq : (CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
              T h0 = 2 → 4 ≤ Nat.card K) ∧
            (CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
              T h0 = 3 → 3 ≤ Nat.card K) :=
          ⟨fun _ => by rw [hK]; norm_num, fun _ => by rw [hK]; norm_num⟩
        have hpos : 1 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
            T h0 := by
          have hne : CFSG.RankThree.PartOne.KCPrimary.primaryComponent
              T h0 ≠ ⊥ :=
            CFSG.RankThree.PartOne.KCPrimary.primaryComponent_ne_bot hx.squarefree_minpoly hh0
          have : Nontrivial (CFSG.RankThree.PartOne.KCPrimary.primaryComponent
              T h0) := Submodule.nontrivial_iff_ne_bot.mpr hne
          exact Module.finrank_pos
        have hScomm₁ : ∀ s ∈ specialBlock Qf (θx) h0,
            Commute (g₁θ) s := by
          by_cases hm : 2 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
              T h0
          · have hSperf : ⁅specialBlock Qf (θx) h0,
                specialBlock Qf (θx) h0⁆ = specialBlock Qf (θx) h0 :=
              Subgroup.isPerfect_iff.mp
                (k329kc3_quasisimple_specialBlock hx Nat.prime_three (by norm_num) hh0 h0X hm hq).1
            exact key_comm
              (k329kc3_specialBlock_le_orthDerived hx Nat.prime_three (by norm_num) hh0 h0X hm hq)
              hSperf (specialBlock_le_isometryCentralizer h0) g₁ hg₁
          · have hm1 : CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
                T h0 = 1 := by omega
            have hbot : specialBlock Qf (θx) h0 = ⊥ :=
              hx.specialBlock_eq_bot_of_finrank_eq_one hh0 hm1
            intro s hs
            rw [hbot, Subgroup.mem_bot] at hs
            subst hs
            exact Commute.one_right _
        have hScomm₂ : ∀ s ∈ specialBlock Qf (θx) h0,
            Commute (g₂θ) s := by
          by_cases hm : 2 ≤ CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
              T h0
          · have hSperf : ⁅specialBlock Qf (θx) h0,
                specialBlock Qf (θx) h0⁆ = specialBlock Qf (θx) h0 :=
              Subgroup.isPerfect_iff.mp
                (k329kc3_quasisimple_specialBlock hx Nat.prime_three (by norm_num) hh0 h0X hm hq).1
            exact key_comm
              (k329kc3_specialBlock_le_orthDerived hx Nat.prime_three (by norm_num) hh0 h0X hm hq)
              hSperf (specialBlock_le_isometryCentralizer h0) g₂ hg₂
          · have hm1 : CFSG.RankThree.PartOne.KCPrimary.primaryMultiplicity
                T h0 = 1 := by omega
            have hbot : specialBlock Qf (θx) h0 = ⊥ :=
              hx.specialBlock_eq_bot_of_finrank_eq_one hh0 hm1
            intro s hs
            rw [hbot, Subgroup.mem_bot] at hs
            subst hs
            exact Commute.one_right _
        have hMF₁ : ∀ f ∈ specialBlock Qf (θx) h0, ∀ v,
            g₁θ (f v) = f (g₁θ v) :=
          fun f hf v => congrArg (fun h : (ι → K) ≃ₗ[K] (ι → K) => h v) (hScomm₁ f hf).eq
        have hMF₂ : ∀ f ∈ specialBlock Qf (θx) h0, ∀ v,
            g₂θ (f v) = f (g₂θ v) :=
          fun f hf v => congrArg (fun h : (ι → K) ≃ₗ[K] (ι → K) => h v) (hScomm₂ f hf).eq
        obtain ⟨f₁, hf₁⟩ := k329kc3_exists_blockScalar hx (by decide : Odd 3) hh0 h0X
          (fun v => (mem_isometryCentralizer.mp hMa).2 v) hMF₁
        obtain ⟨f₂, hf₂⟩ := k329kc3_exists_blockScalar hx (by decide : Odd 3) hh0 h0X
          (fun v => (mem_isometryCentralizer.mp hMb).2 v) hMF₂
        have hmem₂ : g₂θ v ∈
            CFSG.RankThree.PartOne.KCPrimary.primaryComponent T h0 :=
          apply_mem_primaryComponent_of_mem_centralizer (Subgroup.mem_inf.mp hMb).2 hv
        have hmem₁ : g₁θ v ∈
            CFSG.RankThree.PartOne.KCPrimary.primaryComponent T h0 :=
          apply_mem_primaryComponent_of_mem_centralizer (Subgroup.mem_inf.mp hMa).2 hv
        have hmem₂' : aeval T f₂ v ∈
            CFSG.RankThree.PartOne.KCPrimary.primaryComponent T h0 := by
          rw [← hf₂ v hv]; exact hmem₂
        show g₁θ (g₂θ v) = g₂θ (g₁θ v)
        calc g₁θ (g₂θ v)
            = g₁θ (aeval T f₂ v) := by rw [hf₂ v hv]
          _ = aeval T f₁
                (aeval T f₂ v) := hf₁ _ hmem₂'
          _ = aeval T (f₁ * f₂) v := by
                rw [map_mul, Module.End.mul_apply]
          _ = aeval T (f₂ * f₁) v := by rw [mul_comm]
          _ = aeval T f₂
                (aeval T f₁ v) := by
                rw [map_mul, Module.End.mul_apply]
          _ = g₂θ (g₁θ v) := by rw [hf₂ _ hmem₁, ← hf₁ v hv]
    exact LinearEquiv.ext fun v => congrArg (fun f : (ι → K) →ₗ[K] (ι → K) => f v) hlin
  apply Subtype.ext
  apply θ.injective
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  exact hcommθ

theorem k329_S5_POmegaPlus (n : ℕ) (hadm : StatedLieAdmissible .POmegaPlus n 2 3) (K : Type)
    [Field K] : K329TwistMatrix (StatedOmega (StatedQuadPlus n K)) False := by
  intro x _ hx3 g hg _ hgx
  exact hgx (k329_S5_of_no_order_three (K329Zh _) (k329_Zh_le_center _)
    (k329_Z3_POmegaPlus (by have := hadm.2.2; omega)) hx3 hg)

theorem k329_S5_POmegaMinus (n : ℕ) (K : Type) [Field K] (b c : K) :
    K329TwistMatrix (StatedOmega (StatedQuadMinus n K b c)) False := by
  intro x _ hx3 g hg _ hgx
  exact hgx (k329_S5_of_no_order_three (K329Zh _) (k329_Zh_le_center _)
    (k329_Z3_POmegaMinus b c) hx3 hg)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
