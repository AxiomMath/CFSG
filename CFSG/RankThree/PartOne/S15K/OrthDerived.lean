module

public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedInLayer

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem commutator_centralizer_le_layerProduct
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hq : 3 < Nat.card K)
    (a : ProjOrthDerived Q) (ha : orderOf a = p) (x : orthDerived Q)
    (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a) (hxp : orderOf x = p)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep) :
    ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
        Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆ ≤
      componentProduct Q (x : V ≃ₗ[K] V) Rep ⊔ fixedLayerImage Q (x : V ≃ₗ[K] V) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  obtain ⟨-, hmain⟩ := orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl
    (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range le_rfl a ha x hxa hxp
  obtain ⟨hNeq, -, -, -, -, hspec, -, -⟩ := hmain Rep hRep
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))
    with hN
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q))
    with hρ
  set Mo : Subgroup ↥(orthDerived Q) := (isometryCentralizer Q xe).subgroupOf (orthDerived Q)
    with hMo
  set D : Subgroup (ProjOrthDerived Q) := componentProduct Q xe Rep ⊔ fixedLayerImage Q xe
    with hD
  have hbot : ∀ h ∈ Rep, ¬ 2 ≤ primaryMultiplicity xe.toLinearMap h → specialBlock Q xe h = ⊥ := by
    intro h hh hm
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors (hRep.1 hh)⟩
    have hpos := hx.primaryMultiplicity_pos (hRep.1 hh)
    have h1 : primaryMultiplicity xe.toLinearMap h = 1 := by omega
    exact hx.specialBlock_eq_bot_of_finrank_eq_one (hRep.1 hh) h1
  have hspecΩ : ∀ h ∈ Rep, h ≠ X - 1 → specialBlock Q xe h ≤ orthDerived Q := by
    intro h hh hne
    by_cases hm : 2 ≤ primaryMultiplicity xe.toLinearMap h
    · exact (hspec h hh hne hm).1
    · rw [hbot h hh hm]
      exact bot_le
  have hspecD : ∀ h ∈ Rep, h ≠ X - 1 → componentImage Q xe h ≤ D := by
    intro h hh hne
    by_cases hm : 2 ≤ primaryMultiplicity xe.toLinearMap h
    · exact le_sup_of_le_left (le_iSup₂_of_le h hh (le_iSup_of_le ⟨hne, hm⟩ le_rfl))
    · have : componentImage Q xe h = ⊥ := by
        unfold componentImage
        rw [hbot h hh hm, Subgroup.bot_subgroupOf, Subgroup.map_bot]
      rw [this]
      exact bot_le
  set K₀ : Subgroup (V ≃ₗ[K] V) := (D.comap ρ).map (orthDerived Q).subtype with hK₀
  have hmemK₀ : ∀ b : ↥(orthDerived Q), ρ b ∈ D → (b : V ≃ₗ[K] V) ∈ K₀ :=
    fun b hb => ⟨b, hb, rfl⟩
  have hspK₀ : specialProduct Q xe Rep ≤ K₀ := by
    refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    intro j hj
    have hjΩ := hspecΩ h hh hne hj
    refine hmemK₀ ⟨j, hjΩ⟩ (hspecD h hh hne ?_)
    exact Subgroup.mem_map.mpr ⟨⟨j, hjΩ⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  have hlayerD : FixedLayerListed Q xe → fixedComponentImage Q xe ≤ D := by
    intro hlist
    rw [← fixedLayerImage_of_listed hlist]
    exact le_sup_right
  have hsfdK₀ : FixedLayerListed Q xe → supportedFixedDerived Q xe ≤ K₀ := by
    intro hlist f hf
    have hfΩ := hx.supportedFixedDerived_le_orthDerived hf
    refine hmemK₀ ⟨f, hfΩ⟩ (hlayerD hlist ?_)
    exact Subgroup.mem_map.mpr ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
  have hspM : specialProduct Q xe Rep ≤ isometryCentralizer Q xe :=
    iSup₂_le fun h _ => iSup_le fun _ => specialBlock_le_isometryCentralizer h
  have hkey : ⁅Mo, Mo⁆ ≤ D.comap ρ := by
    rw [Subgroup.commutator_le]
    intro m hm m' hm'
    have hmM : (m : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := Subgroup.mem_subgroupOf.mp hm
    have hm'M : (m' : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := Subgroup.mem_subgroupOf.mp hm'
    have hg : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈
        ⁅isometryCentralizer Q xe, isometryCentralizer Q xe⁆ :=
      Subgroup.commutator_mem_commutator hmM hm'M
    obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep hg
    have hgK : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈ K₀ := by
      by_cases hdim : 3 ≤ finrank K (fixedSpace xe)
      · have hlist : FixedLayerListed Q xe := ⟨hdim, by
          rintro (⟨-, h3⟩ | ⟨-, h23⟩) <;> omega⟩
        rw [hgjf]
        exact K₀.mul_mem (hspK₀ hj) (hsfdK₀ hlist hf)
      · have hdim2 : finrank K (fixedSpace xe) ≤ 2 := by omega
        have hfM : f ∈ isometryCentralizer Q xe := supportedFixedDerived_le_isometryCentralizer hf
        have hjM : j ∈ isometryCentralizer Q xe := hspM hj
        have hgM : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := by
          rw [hgjf]
          exact mul_mem hjM hfM
        have h1 : isometryRestrictFixed Q xe ⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V),
            hgM⟩ = 1 := by
          have h2 : (⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V), hgM⟩ :
              ↥(isometryCentralizer Q xe)) =
              ⁅(⟨(m : V ≃ₗ[K] V), hmM⟩ : ↥(isometryCentralizer Q xe)),
                (⟨(m' : V ≃ₗ[K] V), hm'M⟩ : ↥(isometryCentralizer Q xe))⁆ :=
            Subtype.ext rfl
          rw [h2, map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr
            (hx.restrict_commute_of_mem_orthDerived hp2 hQ hRep hdim2 hmM m.2 hm'M m'.2).eq
        have h3 : isometryRestrictFixed Q xe ⟨f, hfM⟩ = 1 := by
          have h4 : (⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V), hgM⟩ :
              ↥(isometryCentralizer Q xe)) = ⟨j, hjM⟩ * ⟨f, hfM⟩ := Subtype.ext hgjf
          rw [h4, map_mul, hx.restrictFixed_trivial_of_mem_specialProduct hRep hj hjM,
            one_mul] at h1
          exact h1
        have hfB := supportedFixedDerived_le_supportedBlock hf
        have h5 : restrictFixed Q xe ⟨f, hfB⟩ = 1 := by
          rw [← isometryRestrictFixed_restrictFixed]
          exact h3
        have hf1 : f = 1 := hx.eq_one_of_restrictFixed_eq_one hfB h5
        rw [hgjf, hf1, mul_one]
        exact hspK₀ hj
    obtain ⟨b, hb, hbg⟩ := hgK
    have hb' : b = ⁅m, m'⁆ := Subtype.ext hbg
    rw [hb'] at hb
    exact hb
  have hNN : ⁅N, N⁆ = ⁅Mo, Mo⁆.map ρ := by
    rw [hNeq]
    exact (Subgroup.map_commutator Mo Mo ρ).symm
  rw [hNN]
  exact Subgroup.map_le_iff_le_comap.mpr hkey

theorem exists_fixedLayer_family {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) :
    ∃ (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)), (⨆ i, C i) = fixedLayerImage Q x ∧
      (∀ i, CFSG.IsQuasisimple ↥(C i) ∧ C i ≤ centralizerImage Q x ∧
        ((C i).subgroupOf (centralizerImage Q x)).IsSubnormal) ∧
      ∀ i j, i ≠ j → ∀ u ∈ C i, ∀ v ∈ C j, u * v = v * u := by
  classical
  by_cases hlist : FixedLayerListed Q x
  · obtain ⟨n, C, -, -, hsup, hC, hcomm, -⟩ := hx.fixedLayer_data hlist
    exact ⟨n, C, by rw [hsup, fixedLayerImage_of_listed hlist], hC, hcomm⟩
  · exact ⟨0, fun i => i.elim0, by
      have : fixedLayerImage Q x = ⊥ := by simp [fixedLayerImage, hlist]
      rw [this]
      exact iSup_of_empty _, fun i => i.elim0, fun i => i.elim0⟩

end

end CFSG.RankThree.PartOne.S15K
