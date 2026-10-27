module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalar
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarFixed

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module QuadraticMap CFSG CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCPrimary CFSG.ClassicalGroups.Orthogonal

section Conj

variable {T : Type*} [Group T]

theorem fix_of_commute_conj (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    (κ : MulAut T) (t : T) (h : κ * MulAut.conj t = MulAut.conj t * κ) : κ t = t := by
  apply hinj
  ext s
  have h1 := DFunLike.congr_fun h (κ⁻¹ s)
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self] at h1
  simp only [MulAut.conj_apply]
  rw [← h1]

theorem fix_of_isComponent (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    (D : Subgroup (MulAut T)) (hD : (MulAut.conj : T →* MulAut T).range ≤ D) (a : T)
    (κ : MulAut T)
    (hcent : ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T))),
      κ * (d : MulAut T) = (d : MulAut T) * κ)
    {C : Subgroup T} (hCa : C ≤ Subgroup.centralizer ({a} : Set T))
    (hC : CFSG.IsComponent ((C.map (MulAut.conj : T →* MulAut T)).subgroupOf
      (D ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T))))) :
    ∀ j ∈ C, κ j = j := by
  intro j hj
  have hjc : j ∈ Subgroup.centralizer ({a} : Set T) := hCa hj
  have hmem : MulAut.conj j ∈ D ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T)) := by
    refine Subgroup.mem_inf.mpr ⟨hD ⟨j, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_singleton_iff.mp hjc).symm]
  have hlayer := CFSG.LocalCores.component_le_layer hC
    (show (⟨MulAut.conj j, hmem⟩ : ↥(D ⊓ Subgroup.centralizer ({MulAut.conj a} :
      Set (MulAut T)))) ∈ (C.map (MulAut.conj : T →* MulAut T)).subgroupOf
        (D ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T))) from
      Subgroup.mem_subgroupOf.mpr ⟨j, hj, rfl⟩)
  exact fix_of_commute_conj hinj κ j (hcent _ hlayer)

end Conj

section Reps

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.exists_orbitRepresentatives_mem (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) :
    ∃ Rep : Finset K[X], IsOrbitRepresentatives x Rep ∧ h ∈ Rep := by
  classical
  obtain ⟨Rep0, hRep0⟩ := hx.exists_orbitRepresentatives
  obtain ⟨r, ⟨hr0, hhr⟩, -⟩ := hRep0.2 h hh
  rcases hhr with rfl | rfl
  · exact ⟨Rep0, hRep0, hr0⟩
  · refine ⟨insert (reciprocalPolynomial r) (Rep0.erase r), ⟨?_, ?_⟩,
      Finset.mem_insert_self _ _⟩
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hh
      · exact hRep0.1 (Finset.mem_of_mem_erase hs)
    · intro k hk
      obtain ⟨s₀, ⟨hs₀, hks₀⟩, huniq⟩ := hRep0.2 k hk
      have hrr : reciprocalPolynomial (reciprocalPolynomial r) = r :=
        hx.reciprocal_reciprocal_eq (hRep0.1 hr0)
      by_cases hs₀r : s₀ = r
      · refine ⟨reciprocalPolynomial r, ⟨Finset.mem_insert_self _ _, ?_⟩, ?_⟩
        · rw [hs₀r] at hks₀
          rcases hks₀ with h1 | h1
          · exact Or.inr (by rw [hrr]; exact h1)
          · exact Or.inl h1
        · rintro s ⟨hs, hks⟩
          rcases Finset.mem_insert.mp hs with h1 | hs'
          · exact h1
          · obtain ⟨hsr, hs'0⟩ := Finset.mem_erase.mp hs'
            exact absurd ((huniq s ⟨hs'0, hks⟩).trans hs₀r) hsr
      · refine ⟨s₀, ⟨Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hs₀r, hs₀⟩), hks₀⟩, ?_⟩
        rintro s ⟨hs, hks⟩
        rcases Finset.mem_insert.mp hs with h1 | hs'
        · exfalso
          rw [h1] at hks
          refine hs₀r (huniq r ⟨hr0, ?_⟩).symm
          rcases hks with h2 | h2
          · exact Or.inr h2
          · exact Or.inl (by rw [h2, hrr])
        · exact huniq s ⟨(Finset.mem_erase.mp hs').2, hks⟩

end Reps

section Centralizer

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem centralizerImage_le_centralizer (x : orthDerived Q) :
    centralizerImage Q (x : V ≃ₗ[K] V) ≤
      Subgroup.centralizer ({(QuotientGroup.mk x : ProjOrthDerived Q)} :
        Set (ProjOrthDerived Q)) := by
  rw [← map_centralizer_eq_centralizerImage]
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.mp hh]
  have h1 : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  exact (congrArg (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) h1).symm

end Centralizer

section Layers

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem conj_injective_projOrthDerived (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) := by
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenterT : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (ProjOrthDerived Q)) with h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  exact conj_injective_of_center_eq_bot hcenterT

variable {p : ℕ}

theorem natural_fixed_component_fixed (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (x : orthDerived Q) (hxp : orderOf x = p)
    (hxA : (QuotientGroup.mk x : ProjOrthDerived Q) ∈ A)
    (hx1 : (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1) (κ : MulAut (ProjOrthDerived Q))
    (hcent : ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ)
    (hlist : FixedLayerListed Q (x : V ≃ₗ[K] V)) :
    ∀ j ∈ fixedComponentImage Q (x : V ≃ₗ[K] V), κ j = j := by
  have hinj := conj_injective_projOrthDerived hQ hT
  obtain ⟨-, n, Cs, -, -, hC, hcomp, -⟩ :=
    (orthogonal_inner_plane_local_core_centralization hQ hT hp hp3 hpl D hD A hA hAc _ hxA hx1 x
      rfl hxp).1 hlist
  intro j hj
  rw [← hC] at hj
  refine Subgroup.iSup_induction Cs (C := fun j => κ j = j) hj (fun i y hy => ?_) (map_one κ)
    (fun a b ha hb => ?_)
  · exact fix_of_isComponent hinj D hD _ κ hcent (hcomp i).2.2.1 (hcomp i).2.2.2.2 y hy
  · rw [map_mul, ha, hb]

theorem natural_primary_component_fixed (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (x : orthDerived Q) (hxp : orderOf x = p)
    (hxA : (QuotientGroup.mk x : ProjOrthDerived Q) ∈ A)
    (hx1 : (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1) (κ : MulAut (ProjOrthDerived Q))
    (hcent : ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj (QuotientGroup.mk x : ProjOrthDerived Q)} :
          Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ) :
    ∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
      2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
      ∀ j ∈ componentImage Q (x : V ≃ₗ[K] V) h, κ j = j := by
  intro h hh hne hm j hj
  have hinj := conj_injective_projOrthDerived hQ hT
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  obtain ⟨Rep, hRep, hhR⟩ := hx.exists_orbitRepresentatives_mem hh
  have hK := (orthogonal_inner_plane_local_core_centralization hQ hT hp hp3 hpl D hD A hA hAc _ hxA
    hx1 x rfl hxp).2.2.1 Rep hRep
  obtain ⟨-, -, -, hcomp⟩ := hK.1 h hhR hne hm
  exact fix_of_isComponent hinj D hD _ κ hcent
    (componentImage_le_centralizerImage.trans (centralizerImage_le_centralizer x)) hcomp j hj

end Layers

section Scalar

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.isPerfect_supportedDerived_fixedSpace (hx : OddOrderIsometry Q p x)
    (hlist : FixedLayerListed Q x) : Group.IsPerfect ↥(supportedDerived Q (fixedSpace x)) := by
  have hcov := (orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype)
    hx.polarBilin_fixed_nondegenerate hlist.1).2 hlist.2
  have h1 : Group.IsPerfect ↥(orthDerived (Q.comp (fixedSpace x).subtype)) := by
    set O := TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) with hO
    have := hcov.1
    have h2 := Group.IsPerfect.map O.subtype (H := commutator ↥O)
    rwa [Subgroup.map_subtype_commutator] at h2
  rw [hx.supportedDerived_fixedSpace]
  exact Group.IsPerfect.ofSurjective (f := (supportedFixedDerivedEquiv hx).symm.toMonoidHom)
    (supportedFixedDerivedEquiv hx).symm.surjective

theorem OddOrderIsometry.fixedSpace_scalar (hx : OddOrderIsometry Q p x)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hlist : FixedLayerListed Q x) (σ : K ≃+* K) (F : V ≃+ V)
    (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K) (hμ : μ ≠ 0)
    (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (κ : MulAut (ProjOrthDerived Q))
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hfix : ∀ j ∈ fixedComponentImage Q x, κ j = j) :
    σ = RingEquiv.refl K ∧ ∃ c : Kˣ, ∀ w ∈ fixedSpace x, F w = (c : K) • w := by
  have hperf := hx.isPerfect_supportedDerived_fixedSpace hlist
  have hW4 : Nat.card K = 2 → finrank K (fixedSpace x) = 4 →
      ∀ U : Submodule K (fixedSpace x), finrank K U = 2 →
        ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
    intro h2 h4 U hU
    by_contra hcon
    push Not at hcon
    exact hlist.2 (Or.inr ⟨⟨h4, U, hU, hcon⟩, Or.inl h2⟩)
  have hκ : ∀ g : ↥(orthDerived Q), (g : V ≃ₗ[K] V) ∈ supportedDerived Q (fixedSpace x) →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g := by
    intro g hg
    rw [hx.supportedDerived_fixedSpace] at hg
    exact hfix _ ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  obtain ⟨-, -, hσ, hc, -⟩ :=
    supported_orthogonal_derived_semilinear_centralizer_scalar_restriction_of_automorphism Q hQ hT
      (fixedSpace x) hx.polarBilin_fixed_nondegenerate hlist.1 hperf hW4 σ F hFσ μ hμ hFQ κ hκF hκ
  exact ⟨hσ, hc⟩

end Scalar

section Lift

open CFSG.RankThree.Classical

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Nontrivial V] {Q : QuadraticForm K V} {p : ℕ}

theorem natural_lift_facts (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime) (hp3 : 3 < p)
    (hpl : p ≠ ringChar K) (A : Subgroup (ProjOrthDerived Q))
    (hA : Assembly.IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) (Ã : Subgroup (orthDerived Q))
    (hÃ : Ã ≤ A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) ∧
      ∀ P : Sylow p (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))),
        (P : Subgroup (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))).map
          (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).subtype =
            Ã) :
    (∀ x ∈ Ã, x ^ p = 1) ∧
      (∀ x ∈ Ã, (QuotientGroup.mk x : ProjOrthDerived Q) = 1 → x = 1) ∧
      ∀ M : Subgroup Ã, Nat.card M = p → ∀ a ∈ M, a ≠ 1 →
        LinearMap.ker (((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap - LinearMap.id) =
          lineFixSpace M := by
  classical
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  obtain ⟨Ã', hle', hsyl', e, he, -, -, -, -, hker', -⟩ :=
    orthogonal_inner_plane_kernel_line_quadratic_decomposition (K := K) (V := V) hℓ hp
      (by omega) hpl Q hQ A hA hAc
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun e₁ e₂ h =>
      LinearEquiv.ext (congrFun h)
  obtain ⟨P⟩ : Nonempty (Sylow p (A.comap
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))) := inferInstance
  have hÃeq : Ã = Ã' := (hÃ.2 P).symm.trans (hsyl' P)
  subst hÃeq
  refine ⟨fun x hx => ?_, fun x hx h1 => ?_, fun M hM a ha ha1 => (hker' M hM a ha ha1).1⟩
  · have h1 : ((e ⟨x, hx⟩ : A) : ProjOrthDerived Q) ^ p = 1 := hA.2 _ (e ⟨x, hx⟩).2
    have h2 : e ((⟨x, hx⟩ : Ã) ^ p) = 1 := Subtype.ext (by rw [map_pow]; exact h1)
    have h3 : (⟨x, hx⟩ : Ã) ^ p = 1 := e.injective (h2.trans (map_one e).symm)
    exact congrArg Subtype.val h3
  · have h2 : e ⟨x, hx⟩ = 1 := Subtype.ext ((he ⟨x, hx⟩).trans h1)
    exact congrArg Subtype.val (e.injective (h2.trans (map_one e).symm))

end Lift

section Line

open CFSG.RankThree.Classical

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem natural_line_scalar (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (Ã : Subgroup (orthDerived Q))
    (hÃA : ∀ x ∈ Ã, (QuotientGroup.mk x : ProjOrthDerived Q) ∈ A)
    (hpow : ∀ x ∈ Ã, x ^ p = 1)
    (hinj1 : ∀ x ∈ Ã, (QuotientGroup.mk x : ProjOrthDerived Q) = 1 → x = 1)
    (σ : K ≃+* K) (F : V ≃+ V) (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K)
    (hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (κ : MulAut (ProjOrthDerived Q))
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hcent : ∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ)
    (M : Subgroup Ã) (hM : Nat.card M = p)
    (hker : ∀ a ∈ M, a ≠ 1 →
      LinearMap.ker (((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap - LinearMap.id) =
        lineFixSpace M)
    (h3 : 3 ≤ finrank K (lineFixSpace M))
    (hq3 : Nat.card K = 3 → finrank K (lineFixSpace M) ≠ 3)
    (hsplit : (Nat.card K = 2 ∨ Nat.card K = 3) →
      ¬ (finrank K (lineFixSpace M) = 4 ∧ ∃ S : Submodule K (lineFixSpace M),
        finrank K S = 2 ∧ ∀ s ∈ S, (Q.comp (lineFixSpace M).subtype) s = 0)) :
    ∃ c : Kˣ, ∀ v ∈ lineFixSpace M, F v = (c : K) • v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hMne : M ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hM
    exact hp.one_lt.ne hM
  obtain ⟨x0, hx0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hMne
  have hxtM : (x0 : Ã) ∈ M := x0.2
  have hxt1 : (x0 : Ã) ≠ 1 := fun h => hx0 (Subtype.ext h)
  have hxÃ : ((x0 : Ã) : orthDerived Q) ∈ Ã := (x0 : Ã).2
  have hx1 : ((x0 : Ã) : orthDerived Q) ≠ 1 := fun h => hxt1 (Subtype.ext h)
  have hxord : orderOf ((x0 : Ã) : orthDerived Q) = p := orderOf_eq_prime (hpow _ hxÃ) hx1
  have hxA := hÃA _ hxÃ
  have hxne : (QuotientGroup.mk ((x0 : Ã) : orthDerived Q) : ProjOrthDerived Q) ≠ 1 :=
    fun h => hx1 (hinj1 _ hxÃ h)
  have hxO := oddOrderIsometry_of_orthDerived hp hpl hQ ((x0 : Ã) : orthDerived Q) hxord
  have hW : fixedSpace (((x0 : Ã) : orthDerived Q) : V ≃ₗ[K] V) = lineFixSpace M :=
    hker (x0 : Ã) hxtM hxt1
  rw [← hW] at h3 hq3 hsplit ⊢
  have hlist : FixedLayerListed Q (((x0 : Ã) : orthDerived Q) : V ≃ₗ[K] V) := by
    refine ⟨h3, ?_⟩
    rintro (⟨h3', h3''⟩ | ⟨⟨h4, S, hS2, hSQ⟩, hq⟩)
    · exact hq3 h3'' h3'
    · exact hsplit hq ⟨h4, S, hS2, hSQ⟩
  have hfix := natural_fixed_component_fixed hQ hT hp hp3 hpl D hD A hA hAc _ hxord hxA hxne κ
    (hcent _ hxA hxne) hlist
  obtain ⟨-, c, hc⟩ := hxO.fixedSpace_scalar hQ hT hlist σ F hFσ μ hμ hFQ κ hκF hfix
  exact ⟨c, hc⟩

end Line

end CFSG.RankThree.PartOne.KCOrthogonal
