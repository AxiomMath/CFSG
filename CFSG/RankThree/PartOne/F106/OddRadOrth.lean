module

public import CFSG.RankThree.PartOne.F106.OddRadOrthOuter
public import CFSG.RankThree.PartOne.F106.OddRadOrthInner
public import CFSG.RankThree.PartOne.S15K.OrthModel

public section

namespace CFSG.RankThree.PartOne.F106.OddRadOrth

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LieType.Universal.Spin CFSG.LocalCores
open scoped commutatorElement

section Final

open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.Sec66T

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem nsub_eq (x : V ≃ₗ[K] V) : nsub Q x = orthDerived Q ⊓ Subgroup.centralizer {x} := by
  ext g
  constructor
  · rintro ⟨⟨_, hgc⟩, hgΩ⟩
    exact ⟨hgΩ, hgc⟩
  · rintro ⟨hgΩ, hgc⟩
    exact ⟨⟨orthDerived_le_orthogonalGroup hgΩ, hgc⟩, hgΩ⟩

theorem oddRadConcl_inner_of_equiv (hQ : (polarBilin Q).Nondegenerate) {T : Type} [Group T]
    (e : T ≃* orthDerived Q) (hZ : Subgroup.center T = ⊥) (t : T)
    (hβ : orderOf (MulAut.conj t : MulAut T) = 5) : OddRadConcl T (MulAut.conj t) := by
  have ht : orderOf t = 5 := by rw [← orderOf_conj_eq hZ t]; exact hβ
  have hy : orderOf (e t) = 5 := by rw [MulEquiv.orderOf_eq]; exact ht
  unfold OddRadConcl
  rw [eqLocus_conj_eq_centralizer t]
  let ι : T →* (V ≃ₗ[K] V) := (orthDerived Q).subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := (orthDerived Q).subtype_injective.comp e.injective
  have h1 := card_radical_residual_of_embedding ι hι t
  have hrange : ι.range = orthDerived Q := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  rw [h1, hrange]
  have hιt : ι t = ((e t : orthDerived Q) : V ≃ₗ[K] V) := rfl
  rw [hιt, ← nsub_eq]
  exact oddRad_nsub hQ (e t) hy

end Final

section Tags

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.RankThree.PartOne.S15K
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.Blueprint

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem oddRadConcl_inner_of_projEquiv (hQ : (polarBilin Q).Nondegenerate)
    (hT3 : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) [Nontrivial V]
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T) (ψ : T ≃* ProjOrthDerived Q) (t : T)
    (hβ : orderOf (MulAut.conj t : MulAut T) = 5) : OddRadConcl T (MulAut.conj t) := by
  have hinj := mk_injective_orth hQ
  let π : orthDerived Q ≃* ProjOrthDerived Q :=
    MulEquiv.ofBijective (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  let e' : T ≃* orthDerived Q := ψ.trans π.symm
  obtain ⟨-, -, -, -, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT3
  have hnc : ∃ a b : T, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨ψ.symm a, ψ.symm b, fun h => hab (by simpa using congrArg ψ h)⟩
  have hZ : Subgroup.center T = ⊥ := center_eq_bot_of_simple_nonabelian hnc
  exact oddRadConcl_inner_of_equiv hQ e' hZ t hβ

theorem oddRadConcl_POmegaMinus_inner {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    {f : ℕ} (hM : LieModel T .POmegaMinus 4 2 f) (t : T)
    (hβ : orderOf (MulAut.conj t : MulAut T) = 5) : OddRadConcl T (MulAut.conj t) := by
  obtain ⟨hadm, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ :=
    statedClassicalModel_of_lieModel_classical (by decide) hM
  have : CharP K 2 := charP_two_of_card_eq_pow hcard
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirr
  have hT3 := exists_three_totSing_quadMinus K b c
  have : Nontrivial (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) := inferInstance
  exact oddRadConcl_inner_of_projEquiv hnd hT3 hs
    (e.trans (statedProjOrthEquiv (coe_quadMinus 4 K b c))) t hβ

theorem oddRadConcl_POmegaPlus_inner {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    {f : ℕ} (hM : LieModel T .POmegaPlus 4 2 f) (t : T)
    (hβ : orderOf (MulAut.conj t : MulAut T) = 5) : OddRadConcl T (MulAut.conj t) := by
  obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ :=
    statedClassicalModel_of_lieModel_classical (by decide) hM
  have : CharP K 2 := charP_two_of_card_eq_pow hcard
  have hnd := nondegenerate_polarBilin_quadPlus 4 K
  have hT3 : ∃ U : Submodule K (Fin 4 ⊕ Fin 4 → K), finrank K U = 3 ∧
      ∀ u ∈ U, quadPlus 4 K u = 0 :=
    ⟨flag 4 K 3, finrank_flag (by norm_num), fun _ hx => quadPlus_eq_zero_of_mem_flag hx⟩
  have : Nontrivial (Fin 4 ⊕ Fin 4 → K) := inferInstance
  exact oddRadConcl_inner_of_projEquiv hnd hT3 hs
    (e.trans (statedProjOrthEquiv (coe_quadPlus 4 K))) t hβ

end Tags

end CFSG.RankThree.PartOne.F106.OddRadOrth

namespace CFSG.RankThree.PartOne.F106

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.N143

theorem oddRadAt_smallModel_pOmegaMinus : OddRadAt (SmallModel .POmegaMinus) := by
  intro T _ _ hs hS β hβ
  obtain ⟨n, f, hadm, hM, hsmall⟩ := hS
  have hn4 : n = 4 := by
    have h1 : 4 ≤ n := hadm.2.2
    have h2 : n ≤ 4 := hsmall
    omega
  subst hn4
  by_cases hinn : β ∈ innerAut T
  · obtain ⟨t, rfl⟩ := hinn
    exact OddRadOrth.oddRadConcl_POmegaMinus_inner hs hM t hβ
  · exact OddRadOrth.oddRadConcl_POmegaMinus_outer hM β hβ hinn

theorem oddRadAt_smallModel_pOmegaPlus : OddRadAt (SmallModel .POmegaPlus) := by
  intro T _ _ hs hS β hβ
  obtain ⟨n, f, hadm, hM, hsmall⟩ := hS
  have hn4 : n = 4 := by
    have h1 : 4 ≤ n := hadm.2.2
    have h2 : n ≤ 4 := hsmall
    omega
  subst hn4
  by_cases hinn : β ∈ innerAut T
  · obtain ⟨t, rfl⟩ := hinn
    exact OddRadOrth.oddRadConcl_POmegaPlus_inner hs hM t hβ
  · exact OddRadOrth.oddRadConcl_POmegaPlus_outer hM β hβ hinn

end CFSG.RankThree.PartOne.F106
