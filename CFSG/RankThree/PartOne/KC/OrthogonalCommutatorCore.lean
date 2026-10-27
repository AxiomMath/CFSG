module

public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorUnit
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorEnd
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents
public import CFSG.RankThree.PartOne.KC.CentralizerOfInnerTrivial
public import CFSG.RankThree.PartOne.KC.ThetaCoreSimpleFixedGroup

public section

namespace CFSG.RankThree.PartOne.KCOrthComm

open Polynomial Module CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Finite

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem finite_coordinateSemilinearGroup : Finite (coordinateSemilinearGroup d K) := by
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) (fun _ _ h => RingEquiv.ext (congrFun h))
  exact Finite.of_injective (fun g : coordinateSemilinearGroup d K => (g.left, g.right))
    (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

theorem finite_similarityPairs : Finite (similarityPairs Q) := by
  have := finite_coordinateSemilinearGroup (K := K) (d := d)
  infer_instance

theorem finite_linearEquiv : Finite ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  Finite.of_injective (fun e : (Fin d → K) ≃ₗ[K] (Fin d → K) => (e : (Fin d → K) → (Fin d → K)))
    fun _ _ h => LinearEquiv.ext (congrFun h)

end Finite

section Good

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) {p : ℕ}

@[expose] def GoodPair (xe : (Fin d → K) ≃ₗ[K] (Fin d → K)) (p : ℕ)
    (g : similarityPairs Q) : Prop :=
  (∀ v, pairMap Q g (xe v) = xe (pairMap Q g v)) ∧
    (∃ j : ℕ, g.val.right ^ p ^ j = 1 ∧ ∃ c : K, ∀ v, (pairMap Q g)^[p ^ j] v = c • v) ∧
    ∀ k ∈ primaryFactors xe.toLinearMap, k.map (g.val.right : K →+* K) = k

structure PlusData (xe : (Fin d → K) ≃ₗ[K] (Fin d → K)) (p : ℕ) where
  Uplus : Subgroup (similarityPairs Q)
  le : Uplus ≤ UP Q xe
  index : (Uplus.subgroupOf (UP Q xe)).index < p
  comm : ∀ u ∈ Uplus, ∀ u' ∈ Uplus, kappa Q u * kappa Q u' = kappa Q u' * kappa Q u
  conj : ∀ g : similarityPairs Q, GoodPair Q xe p g → ∀ u ∈ Uplus, g * u * g⁻¹ ∈ Uplus
  fix2 : ∀ g : similarityPairs Q, GoodPair Q xe p g → ∀ u ∈ Uplus,
    (∃ s : ℕ, u ^ 2 ^ s = 1) → kappa Q (g * u * g⁻¹) = kappa Q u

noncomputable def plusDataOfNeTwo {xe : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hx : OddOrderIsometry Q p xe) (hp : p.Prime) (hp3 : 3 < p)
    (hW2 : finrank K (fixedSpace xe) ≠ 2) : PlusData Q xe p where
  Uplus := UP Q xe
  le := le_rfl
  index := by
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    exact hp.one_lt
  comm := fun u hu u' hu' => by
    rw [← map_mul, ← map_mul]
    refine kappa_congr Q fun v => ?_
    have h := mul_comm_of_blockScalar hx.squarefree_minpoly
      (blockScalar_of_mem_UP Q hx hp hp3 hW2 hu) (blockScalar_of_mem_UP Q hx hp hp3 hW2 hu')
    rw [pairMap_mul, pairMap_mul]
    exact LinearEquiv.congr_fun h v
  conj := fun g hg u hu => conj_mem_UP Q hx hp hp3 g hg.1 hg.2.2 hu
  fix2 := fun g hg u hu ⟨s, hs⟩ => by
    obtain ⟨j, hj, -⟩ := hg.2.1
    exact kappa_conj_eq_of_pow_two_pow Q hx hp hp3 hW2 hg.1 (N := p ^ j)
      ((hp.odd_of_ne_two (by omega)).pow) hj hg.2.2 hu hs

end Good


section Reps

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {xe : V ≃ₗ[K] V}

theorem exists_orbitRepresentatives_mem (hx : OddOrderIsometry Q p xe) {h₀ : K[X]}
    (hh₀ : h₀ ∈ primaryFactors xe.toLinearMap) :
    ∃ Rep : Finset K[X], IsOrbitRepresentatives xe Rep ∧ h₀ ∈ Rep := by
  classical
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  by_cases hmem : h₀ ∈ Rep
  · exact ⟨Rep, hRep, hmem⟩
  set h₁ := reciprocalPolynomial h₀ with hh₁
  have hh₁pf : h₁ ∈ primaryFactors xe.toLinearMap := hx.reciprocalPolynomial_mem hh₀
  have hrr : reciprocalPolynomial h₁ = h₀ := hx.reciprocal_reciprocal_eq hh₀
  obtain ⟨r₀, ⟨hr₀R, hr₀⟩, -⟩ := hRep.2 h₀ hh₀
  have hr₀h₁ : r₀ = h₁ := by
    rcases hr₀ with h | h
    · exact absurd (h ▸ hr₀R) hmem
    · rw [hh₁, h, hx.reciprocal_reciprocal_eq (hRep.1 hr₀R)]
  have hh₁R : h₁ ∈ Rep := hr₀h₁ ▸ hr₀R
  have hne : h₁ ≠ h₀ := fun h => hmem (h ▸ hh₁R)
  let τ : K[X] → K[X] := fun a => if a = h₁ then h₀ else if a = h₀ then h₁ else a
  have hτh₁ : τ h₁ = h₀ := by simp [τ]
  have hτh₀ : τ h₀ = h₁ := by simp [τ, hne.symm]
  have hτother : ∀ a, a ≠ h₁ → a ≠ h₀ → τ a = a := fun a h1 h2 => by simp [τ, h1, h2]
  have hττ : ∀ a, τ (τ a) = a := by
    intro a
    by_cases h1 : a = h₁
    · rw [h1, hτh₁, hτh₀]
    by_cases h2 : a = h₀
    · rw [h2, hτh₀, hτh₁]
    rw [hτother a h1 h2, hτother a h1 h2]
  have hτpf : ∀ a ∈ primaryFactors xe.toLinearMap, τ a ∈ primaryFactors xe.toLinearMap := by
    intro a ha
    by_cases h1 : a = h₁
    · rw [h1, hτh₁]; exact hh₀
    by_cases h2 : a = h₀
    · rw [h2, hτh₀]; exact hh₁pf
    rw [hτother a h1 h2]; exact ha
  have hτrec : ∀ a ∈ primaryFactors xe.toLinearMap,
      τ (reciprocalPolynomial a) = reciprocalPolynomial (τ a) := by
    intro a ha
    by_cases h1 : a = h₁
    · rw [h1, hτh₁, hrr, hτh₀]
    by_cases h2 : a = h₀
    · rw [h2, hτh₀, ← hh₁, hτh₁, hrr]
    have h3 : reciprocalPolynomial a ≠ h₁ := fun h => h2 (by
      rw [← hx.reciprocal_reciprocal_eq ha, h, hrr])
    have h4 : reciprocalPolynomial a ≠ h₀ := fun h => h1 (by
      rw [← hx.reciprocal_reciprocal_eq ha, h])
    rw [hτother _ h3 h4, hτother a h1 h2]
  refine ⟨Rep.image τ, ⟨fun r hr => ?_, fun k hk => ?_⟩, Finset.mem_image.mpr ⟨h₁, hh₁R, hτh₁⟩⟩
  · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hr
    exact hτpf ρ (hRep.1 hρ)
  · obtain ⟨ρ, ⟨hρR, hρ⟩, huniq⟩ := hRep.2 (τ k) (hτpf k hk)
    refine ⟨τ ρ, ⟨Finset.mem_image_of_mem τ hρR, ?_⟩, ?_⟩
    · rcases hρ with h | h
      · left
        rw [← h, hττ]
      · right
        rw [← hτrec ρ (hRep.1 hρR), ← h, hττ]
    · rintro r ⟨hr, hkr⟩
      obtain ⟨ρ', hρ'R, rfl⟩ := Finset.mem_image.mp hr
      have := huniq ρ' ⟨hρ'R, by
        rcases hkr with h | h
        · left
          rw [h, hττ]
        · right
          rw [h, hτrec (τ ρ') (hτpf ρ' (hRep.1 hρ'R)), hττ]⟩
      rw [this]

end Reps


section Centralize

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem finite_linearEquiv_self : Finite (V ≃ₗ[K] V) :=
  have : Finite V := Module.finite_of_finite K
  Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)

theorem apply_eq_of_commute_conj {T : Type*} [Group T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {s : MulAut T} {y : T}
    (h : s * MulAut.conj y = MulAut.conj y * s) : s y = y := by
  have h1 := mulAut_conj_apply_eq_conj_apply s y
  rw [h, mul_inv_cancel_right] at h1
  exact (hinj h1).symm

theorem conj_injective_projOrthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) := by
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenterT : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  exact conj_injective_of_center_eq_bot hcenterT

variable {p : ℕ}

theorem centralize_special (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hp : p.Prime) (hp3 : 3 < p)
    (hpl : p ≠ ringChar K) (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (a : ProjOrthDerived Q) (ha : orderOf a = p) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p)
    {h : K[X]} (hh : h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap) (hne1 : h ≠ X - 1)
    (g : orthDerived Q) (hg : (g : V ≃ₗ[K] V) ∈ specialBlock Q (x : V ≃ₗ[K] V) h)
    {s : MulAut (ProjOrthDerived Q)}
    (hs : s ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))) :
    s (QuotientGroup.mk g : ProjOrthDerived Q) = QuotientGroup.mk g := by
  classical
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have hinj := conj_injective_projOrthDerived hQ hT
  by_cases hm : 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h
  · obtain ⟨Rep, hRep, hhR⟩ := exists_orbitRepresentatives_mem hx hh
    obtain ⟨-, hmain⟩ :=
      orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl B hB a ha x hxa hxp
    obtain ⟨-, -, -, -, -, -, hSD, -⟩ := hmain Rep hRep
    have hmem : (QuotientGroup.mk g : ProjOrthDerived Q) ∈
        componentProduct Q (x : V ≃ₗ[K] V) Rep := by
      refine Subgroup.mem_iSup_of_mem h (Subgroup.mem_iSup_of_mem hhR
        (Subgroup.mem_iSup_of_mem ⟨hne1, hm⟩ ?_))
      exact Subgroup.mem_map.mpr ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have h1 := hSD
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
    have h2 := Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_map_of_mem _ hmem)) s hs
    exact apply_eq_of_commute_conj hinj h2
  · have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hpos : 1 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h := by
      have hne : primaryComponent (x : V ≃ₗ[K] V).toLinearMap h ≠ ⊥ :=
        primaryComponent_ne_bot hx.squarefree_minpoly hh
      have : Nontrivial (primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) :=
        Submodule.nontrivial_iff_ne_bot.mpr hne
      exact Module.finrank_pos
    have h1 : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h = 1 := by omega
    have hbot := hx.specialBlock_eq_bot_of_finrank_eq_one hh h1
    rw [hbot, Subgroup.mem_bot] at hg
    have hg1 : g = 1 := Subtype.ext hg
    rw [hg1, QuotientGroup.mk_one, map_one]

theorem centralize_fixed_layer (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hq : 3 < Nat.card K)
    (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (a : ProjOrthDerived Q) (ha : orderOf a = p) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p)
    (h3 : 3 ≤ finrank K (fixedSpace (x : V ≃ₗ[K] V))) (g : orthDerived Q)
    (hg : (g : V ≃ₗ[K] V) ∈ supportedFixedDerived Q (x : V ≃ₗ[K] V))
    {s : MulAut (ProjOrthDerived Q)}
    (hs : s ∈ inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))) :
    s (QuotientGroup.mk g : ProjOrthDerived Q) = QuotientGroup.mk g := by
  classical
  have := finite_linearEquiv_self (K := K) (V := V)
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have hinj := conj_injective_projOrthDerived hQ hT
  have hlist : FixedLayerListed Q (x : V ≃ₗ[K] V) := by
    refine ⟨h3, ?_⟩
    rintro (⟨-, h⟩ | ⟨-, h | h⟩) <;> omega
  obtain ⟨⟨Rep₀, hRep₀⟩, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl B hB a ha x hxa hxp
  have hNeq : Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
      centralizerImage Q (x : V ≃ₗ[K] V) := (hmain Rep₀ hRep₀).1
  obtain ⟨n, C, -, -, hsup, hC, -, -⟩ := hx.fixedLayer_data hlist
  have hcent : (fixedComponentImage Q (x : V ≃ₗ[K] V)).map
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
      Subgroup.centralizer (inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))) :
        Set (MulAut (ProjOrthDerived Q))) := by
    rw [← hsup, Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    have h0 := commutator_core_map_conj_eq_bot_of_subnormal hp hB a hinj
      (by rw [hNeq]; exact (hC i).2.1) (by rw [hNeq]; exact (hC i).2.2) (hC i).1
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
    exact h0
  have hmem : (QuotientGroup.mk g : ProjOrthDerived Q) ∈
      fixedComponentImage Q (x : V ≃ₗ[K] V) :=
    Subgroup.mem_map.mpr ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have h2 := Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem _ hmem)) s hs
  exact apply_eq_of_commute_conj hinj h2

theorem isPerfect_supportedFixedDerived {xe : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p xe)
    (hq : 3 < Nat.card K) (h3 : 3 ≤ finrank K (fixedSpace xe)) :
    Group.IsPerfect ↥(supportedFixedDerived Q xe) := by
  obtain ⟨-, h2⟩ := orthogonal_regular_space_coverage (Q.comp (fixedSpace xe).subtype)
    hx.polarBilin_fixed_nondegenerate h3
  have hcov := h2 (by rintro (⟨-, h⟩ | ⟨-, h | h⟩) <;> omega)
  obtain ⟨n, F, -, -, hsup, hF, -, -⟩ := hx.exists_supported_factors hcov
  refine Subgroup.isPerfect_iff.mpr (le_antisymm ?_ ?_)
  · exact Subgroup.commutator_le.mpr fun g hg g' hg' => by
      exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')
  · rw [← hsup]
    refine iSup_le fun i => ?_
    have h1 : ⁅F i, F i⁆ = F i := Subgroup.isPerfect_iff.mp (hF i).1.1
    calc F i = ⁅F i, F i⁆ := h1.symm
      _ ≤ ⁅⨆ j, F j, ⨆ j, F j⁆ := Subgroup.commutator_mono (le_iSup F i) (le_iSup F i)


theorem apply_eq_of_mem_centralizer {T : Type*} [Group T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {s : MulAut T} {y : T}
    (h : s ∈ Subgroup.centralizer ({MulAut.conj y} : Set (MulAut T))) : s y = y :=
  apply_eq_of_commute_conj hinj (Subgroup.mem_centralizer_singleton_iff.mp h)

omit [Finite K] [FiniteDimensional K V] in
theorem exists_ne_zero_of_nondegenerate (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) : ∃ v, Q v ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨U, hU3, -⟩ := hT
  have hpol : ∀ v w, QuadraticMap.polarBilin Q v w = 0 := fun v w => by
    simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h]
  have hV : ∀ v : V, v = 0 := fun v => hQ.1 v (hpol v)
  have : Subsingleton U := ⟨fun a b => Subtype.ext ((hV a).trans (hV b).symm)⟩
  have h0 : finrank K U = 0 := Module.finrank_zero_of_subsingleton
  omega

end Centralize

section Assembly

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) {p : ℕ}

theorem index_subgroupOf_map_le {G H : Type*} [Group G] [Group H] [Finite G] (κ : G →* H)
    {U₁ U₂ : Subgroup G} :
    ((U₂.map κ).subgroupOf (U₁.map κ)).index ≤ (U₂.subgroupOf U₁).index := by
  have hsurj : Function.Surjective (κ.subgroupMap U₁) := κ.subgroupMap_surjective U₁
  have hle : U₂.subgroupOf U₁ ≤ ((U₂.map κ).subgroupOf (U₁.map κ)).comap (κ.subgroupMap U₁) := by
    intro u hu
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ⟨u.1, Subgroup.mem_subgroupOf.mp hu, rfl⟩
  rw [← Subgroup.index_comap_of_surjective _ hsurj]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hle)

theorem exists_good_pair {xe : (Fin d → K) ≃ₗ[K] (Fin d → K)} {x : orthDerived Q}
    (hxe : (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) = xe) (hx : OddOrderIsometry Q p xe)
    (hp : p.Prime) (hp3 : 3 < p) (hQ0 : ∃ v, Q v ≠ 0) (hG : GateData Q p)
    {A : Subgroup (MulAut (ProjOrthDerived Q))} (hA : IsPGroup p A)
    (hfixA : ∀ α ∈ A, α (QuotientGroup.mk x) = QuotientGroup.mk x)
    {α : MulAut (ProjOrthDerived Q)} (hα : α ∈ A) :
    ∃ g : similarityPairs Q, kappa Q g = α ∧ GoodPair Q xe p g := by
  obtain ⟨g, hg⟩ := hG.elem A hA hα
  obtain ⟨j, hj⟩ := hA ⟨α, hα⟩
  have hαj : α ^ p ^ j = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  have hfixa : kappa Q g (QuotientGroup.mk x) = QuotientGroup.mk x := by
    rw [hg]
    exact hfixA α hα
  have hj' : kappa Q g ^ p ^ j = 1 := by
    rw [hg]
    exact hαj
  obtain ⟨hFx, hσ, hc, hfix⟩ := pair_good Q hxe hx hp (hp.odd_of_ne_two (by omega)) hQ0 hG hfixa hj'
  exact ⟨g, hg, hFx, ⟨j, hσ, hc⟩, hfix⟩

theorem orthogonal_inner_actor_commutators_odd_of_gates
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hq : 3 < Nat.card K) (hG : GateData Q p) (hp : p.Prime) (hp3 : 3 < p)
    (hpl : p ≠ ringChar K)
    (hplus : ∀ x : orthDerived Q, orderOf x = p →
      Nonempty (PlusData Q (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) p))
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (a : ProjOrthDerived Q) (ha : orderOf a = p)
    {A : Subgroup (MulAut (ProjOrthDerived Q))} (hA : IsPGroup p A)
    (hAC : A ≤ B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))) :
    Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))), A⁆ :
        Subgroup (MulAut (ProjOrthDerived Q)))) := by
  classical
  have := finite_linearEquiv_self (K := K) (V := Fin d → K)
  have := finite_similarityPairs Q
  have hinj := conj_injective_projOrthDerived hQ hT
  have hQ0 := exists_ne_zero_of_nondegenerate hQ hT
  obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  obtain ⟨x, ⟨hxa, hxp⟩, -, -⟩ := hlift p hp (by omega) a ha
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  set xe : (Fin d → K) ≃ₗ[K] (Fin d → K) := (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) with hxe
  set C : Subgroup (MulAut (ProjOrthDerived Q)) :=
    B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))) with hC
  set S := inSubgroup (aschbacherSolvableCore p) C with hS
  obtain ⟨hSC, hSn, hSp, hSs⟩ := inSubgroup_theta_solvable_normal_prime_complement hp C
  have hSnorm : ∀ y ∈ C, ∀ s ∈ S, y * s * y⁻¹ ∈ S := by
    intro y hy s hs
    have := hSn.conj_mem ⟨s, hSC hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hAS : A ≤ Subgroup.normalizer (S : Set (MulAut (ProjOrthDerived Q))) := by
    intro α hα
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hSnorm α (hAC hα) s hs, fun hs => ?_⟩
    have := hSnorm α⁻¹ (C.inv_mem (hAC hα)) _ hs
    simpa [mul_assoc] using this
  have hfixA : ∀ α ∈ A, α (QuotientGroup.mk x) = QuotientGroup.mk x := fun α hα => by
    rw [hxa]
    exact apply_eq_of_mem_centralizer hinj (Subgroup.mem_inf.mp (hAC hα)).2
  have hRS : ⁅S, A⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro s hs α hα
    have h1 := hSnorm α (hAC hα) s⁻¹ (S.inv_mem hs)
    have h2 : ⁅s, α⁆ = s * (α * s⁻¹ * α⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact S.mul_mem hs h1
  obtain ⟨PD⟩ := hplus x hxp
  have hlin := hG.lin A S hA hSs hSp hAS
  have hSAΓ : ⁅S, A⁆ ≤ (UP Q xe).map (kappa Q) := by
    intro r hr
    obtain ⟨u, hu, hur⟩ := hlin hr
    have hrS : r ∈ S := hRS hr
    have hu1 : u.val.right = 1 := (mem_linearSimilarityPairs_iff Q u).mp hu
    have hfix : r (QuotientGroup.mk x) = QuotientGroup.mk x := by
      rw [hxa]
      exact apply_eq_of_mem_centralizer hinj (Subgroup.mem_inf.mp (hSC hrS)).2
    refine ⟨u, mem_UP_of_fixes Q hQ hT hq hx hp hp3 rfl hQ0 hu1 ?_ ?_ ?_ ?_, hur⟩
    · rw [hur]
      exact hfix
    · intro h hh hne1 g hg
      rw [hur]
      exact centralize_special hQ hT hp hp3 hpl B hB a ha x hxa hxp hh hne1 g hg hrS
    · intro h3 g hg
      rw [hur]
      exact centralize_fixed_layer hQ hT hq hp hp3 hpl B hB a ha x hxa hxp h3 g hg hrS
    · intro h3
      exact isPerfect_supportedFixedDerived hx hq h3
  have hidx : (((PD.Uplus).map (kappa Q)).subgroupOf ((UP Q xe).map (kappa Q))).index < p :=
    lt_of_le_of_lt (index_subgroupOf_map_le (kappa Q)) PD.index
  refine odd_card_commutator_of_small_index hp hA hSp hAS hSAΓ hidx ?_ ?_ ?_ ?_
  · rintro α hα _ ⟨u, hu, rfl⟩
    obtain ⟨g, hgα, hgood⟩ := exists_good_pair Q rfl hx hp hp3 hQ0 hG hA hfixA hα
    refine ⟨g * u * g⁻¹, conj_mem_UP Q hx hp hp3 g hgood.1 hgood.2.2 hu, ?_⟩
    rw [map_mul, map_mul, map_inv, hgα]
  · rintro α hα _ ⟨u, hu, rfl⟩
    obtain ⟨g, hgα, hgood⟩ := exists_good_pair Q rfl hx hp hp3 hQ0 hG hA hfixA hα
    refine ⟨g * u * g⁻¹, PD.conj g hgood u hu, ?_⟩
    rw [map_mul, map_mul, map_inv, hgα]
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    exact PD.comm u hu u' hu'
  · rintro α hα z ⟨u₀, hu₀, rfl⟩ ⟨k, hk⟩
    obtain ⟨g, hgα, hgood⟩ := exists_good_pair Q rfl hx hp hp3 hQ0 hG hA hfixA hα
    obtain ⟨u, n, hu, hun⟩ := exists_two_pow_lift ((kappa Q).comp PD.Uplus.subtype)
      (z := kappa Q u₀) ⟨⟨u₀, hu₀⟩, rfl⟩ hk
    have hun' : (u : similarityPairs Q) ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hun
      simpa using this
    have h1 := PD.fix2 g hgood u u.2 ⟨n, hun'⟩
    have hu' : kappa Q u = kappa Q u₀ := hu
    rw [← hu', ← hgα, ← map_inv, ← map_mul, ← map_mul]
    exact h1

end Assembly

end CFSG.RankThree.PartOne.KCOrthComm
