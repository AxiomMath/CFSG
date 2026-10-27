module

public import CFSG.RankThree.PartOne.FOC.ComponentFact
public import CFSG.RankThree.PartOne.FOC.PlaneOfPair
public import CFSG.RankThree.PartOne.FOC.InnerCase
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitFourClause
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryMultiplicity

public section

namespace CFSG.RankThree.PartOne.FOC

open Polynomial Module Subgroup CFSG
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

section Family

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

abbrev OrthIdx (x : V ≃ₗ[K] V) (Rep : Finset K[X]) (n : ℕ) : Type :=
  {h : K[X] // h ∈ Rep ∧ h ≠ X - 1 ∧ 2 ≤ primaryMultiplicity x.toLinearMap h} ⊕ Fin n

@[expose] noncomputable def orthFam (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (Rep : Finset K[X])
    {n : ℕ} (C : Fin n → Subgroup (ProjOrthDerived Q)) :
    OrthIdx x Rep n → Subgroup (ProjOrthDerived Q) :=
  Sum.elim (fun h => componentImage Q x h.1) C

omit [Finite K] [FiniteDimensional K V] in
theorem iSup_orthFam (x : V ≃ₗ[K] V) (Rep : Finset K[X]) {n : ℕ}
    (C : Fin n → Subgroup (ProjOrthDerived Q)) :
    (⨆ i, orthFam Q x Rep C i) = componentProduct Q x Rep ⊔ ⨆ i, C i := by
  rw [orthFam, iSup_sum]
  congr 1
  apply le_antisymm
  · exact iSup_le fun h => le_iSup₂_of_le h.1 h.2.1 (le_iSup_of_le ⟨h.2.2.1, h.2.2.2⟩ le_rfl)
  · refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    exact le_iSup (fun h : {h : K[X] // h ∈ Rep ∧ h ≠ X - 1 ∧
      2 ≤ primaryMultiplicity x.toLinearMap h} => componentImage Q x h.1) ⟨h, hh, hne.1, hne.2⟩

theorem exists_fixedLayer_fam {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) :
    ∃ (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)), (⨆ i, C i) = fixedLayerImage Q x ∧
      ∀ i, CFSG.IsQuasisimple ↥(C i) ∧ C i ≤ centralizerImage Q x ∧
        ((C i).subgroupOf (centralizerImage Q x)).IsSubnormal := by
  classical
  by_cases hlist : FixedLayerListed Q x
  · obtain ⟨n, C, -, -, hsup, hC, -, -⟩ := hx.fixedLayer_data hlist
    exact ⟨n, C, by rw [hsup, fixedLayerImage_of_listed hlist], hC⟩
  · exact ⟨0, fun i => i.elim0, by
      have : fixedLayerImage Q x = ⊥ := by simp [fixedLayerImage, hlist]
      rw [this]
      exact iSup_of_empty _, fun i => i.elim0⟩

end Family

section Main

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem mem_sup_centralizer_of_component_orth (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (hmult : OrthogonalLiftMultiplicity p Q (MulEquiv.refl (ProjOrthDerived Q)))
    {b y : ProjOrthDerived Q} (hbp : b ^ p = 1) (hyp : y ^ p = 1) (hby : b * y = y * b)
    {E : Subgroup (ProjOrthDerived Q)}
    (hE : IsComponentOf (Subgroup.centralizer ({b} : Set (ProjOrthDerived Q))) E) :
    y ∈ E ⊔ Subgroup.centralizer (E : Set (ProjOrthDerived Q)) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hxlift := CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  by_cases hy1 : y = 1
  · rw [hy1]
    exact Subgroup.one_mem _
  by_cases hb1 : b = 1
  · subst hb1
    have hcent : Subgroup.centralizer ({1} : Set (ProjOrthDerived Q)) = ⊤ := by
      ext g
      simp [Subgroup.mem_centralizer_singleton_iff]
    rw [hcent] at hE
    have : IsSimpleGroup (ProjOrthDerived Q) := hxlift.2.2.2.1
    have : IsSimpleGroup ↥(⊤ : Subgroup (ProjOrthDerived Q)) :=
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (ProjOrthDerived Q)) ≃* _).isSimpleGroup
    have hEtop : E = ⊤ := eq_of_isComponentOf_simple hE
    rw [hEtop]
    exact Subgroup.mem_sup_left (Subgroup.mem_top _)
  by_cases hyb : y ∈ Subgroup.zpowers b
  · refine Subgroup.mem_sup_right ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have : e * b = b * e := Subgroup.mem_centralizer_singleton_iff.mp (hE.1 he)
    exact (Commute.zpow_right (show Commute e b from this) k).eq
  obtain ⟨A, hA, hAcard, hbA, hyA⟩ := exists_plane hp hbp hyp hb1 hby hyb
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  obtain ⟨⟨x, ⟨hxb, hxp⟩, -⟩, hmx⟩ := hmult b hbord
  have hxO : (x : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup x.2
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have hsq := hx.squarefree_minpoly
  have hpm : ∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
      ¬ p ∣ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h := by
    intro h hh hne hdvd
    have hpos : 0 < primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h := by
      have hne' := primaryComponent_ne_bot hsq hh
      have : Nontrivial ↥(primaryComponent (x : V ≃ₗ[K] V).toLinearMap h) :=
        Submodule.nontrivial_iff_ne_bot.mpr hne'
      have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
      exact Module.finrank_pos
    have hlt := (hmx x hxb hxp h hh hne).2.2.1
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  set B : Subgroup (MulAut (ProjOrthDerived Q)) :=
    (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range with hBdef
  obtain ⟨⟨Rep, hRep⟩, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl B le_rfl b hbord x hxb
      hxp
  obtain ⟨hNeq, -, -, -, -, -, -, -⟩ := hmain Rep hRep
  have hNeq' : Subgroup.centralizer ({b} : Set (ProjOrthDerived Q)) =
      centralizerImage Q (x : V ≃ₗ[K] V) := hNeq
  obtain ⟨n, C, hCsup, hC⟩ := exists_fixedLayer_fam hx
  obtain ⟨-, -, -, hfull, -⟩ := orthogonal_inner_plane_local_core_centralization_full hQ hT hp hp3
    hpl B le_rfl A hA hAcard b hbA hb1 x hxb hxp
  obtain ⟨hfspec, -, -, -, hffac⟩ := hfull Rep hRep
  have hyN : y ∈ Subgroup.centralizer ({b} : Set (ProjOrthDerived Q)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hby.symm
  obtain ⟨z, k, hyzk, -, -, hzc, -, hkD, -⟩ := hffac hpm y hyN hyord
  have hjoin : (⨆ i, orthFam Q (x : V ≃ₗ[K] V) Rep C i) =
      componentProduct Q (x : V ≃ₗ[K] V) Rep ⊔ fixedLayerImage Q (x : V ≃ₗ[K] V) := by
    rw [iSup_orthFam, hCsup]
  have hJ : ∀ i, orthFam Q (x : V ≃ₗ[K] V) Rep C i = ⊥ ∨
      IsComponentOf (Subgroup.centralizer ({b} : Set (ProjOrthDerived Q)))
        (orthFam Q (x : V ≃ₗ[K] V) Rep C i) := by
    rintro (⟨h, hmem, hne, hm⟩ | j)
    · obtain ⟨-, -, h3, h4, h5, -⟩ := hfspec h hmem hne hm
      exact Or.inr ⟨h4, h3, h5⟩
    · obtain ⟨h1, h2, h3⟩ := hC j
      refine Or.inr ⟨by rw [hNeq']; exact h2, h1, ?_⟩
      rw [hNeq']
      exact h3
  exact mem_sup_centralizer_of_factorization (orthFam Q (x : V ≃ₗ[K] V) Rep C) hJ hyzk
    (fun n hn => (hzc n hn).eq) (by rw [hjoin]; exact hkD) hE

end Main

end CFSG.RankThree.PartOne.FOC
