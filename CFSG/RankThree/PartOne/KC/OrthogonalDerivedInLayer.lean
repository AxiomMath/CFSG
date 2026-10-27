module

public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneDefs

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2
  CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem exists_noncommProd_of_mem_commutator [Fintype ι] (B : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ B i → y ∈ B j → Commute x y) {g : G}
    (hg : g ∈ ⁅⨆ i, B i, ⨆ i, B i⁆) :
    ∃ w : ∀ i, ↥(B i), (∀ i, ((w i : ↥(B i)) : G) ∈ ⁅B i, B i⁆) ∧
      g = Subgroup.noncommPiCoprod hcomm w := by
  set Φ := Subgroup.noncommPiCoprod hcomm with hΦ
  have hrange : Φ.range = ⨆ i, B i := Subgroup.noncommPiCoprod_range
  rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  have htop : (⊤ : Subgroup (∀ i, ↥(B i))) = Subgroup.pi Set.univ (fun i => ⊤) :=
    (Subgroup.pi_top Set.univ).symm
  rw [htop, Subgroup.commutator_pi_pi_of_finite] at hw
  refine ⟨w, fun i => ?_, rfl⟩
  have h1 := hw i (Set.mem_univ i)
  have h2 : (⁅(⊤ : Subgroup ↥(B i)), (⊤ : Subgroup ↥(B i))⁆).map (B i).subtype = ⁅B i, B i⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [← h2]
  exact ⟨w i, h1, rfl⟩

end Abstract

section Blocks

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {p : ℕ} {x : V ≃ₗ[K] V}

theorem commutator_supportedBlock_le_specialBlock (h : K[X]) :
    ⁅supportedBlock Q x h, supportedBlock Q x h⁆ ≤ specialBlock Q x h := by
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  have hmem : ⁅g, g'⁆ ∈ supportedBlock Q x h := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')
  refine mem_specialBlock.mpr ⟨hmem, ?_⟩
  have key : ∀ a b : ↥(supportedBlock Q x h), blockDet Q x h (a * b * a⁻¹ * b⁻¹) = 1 := by
    intro a b
    have h1 : blockDet Q x h a * blockDet Q x h a⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : blockDet Q x h b * blockDet Q x h b⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    rw [map_mul, map_mul, map_mul]
    calc blockDet Q x h a * blockDet Q x h b * blockDet Q x h a⁻¹ * blockDet Q x h b⁻¹
        = (blockDet Q x h a * blockDet Q x h a⁻¹) * (blockDet Q x h b * blockDet Q x h b⁻¹) := by
          ring
      _ = 1 := by rw [h1, h2, one_mul]
  exact key ⟨g, hg⟩ ⟨g', hg'⟩

@[expose] noncomputable def specialProduct (Q : QuadraticForm K V) (x : V ≃ₗ[K] V)
    (Rep : Finset K[X]) : Subgroup (V ≃ₗ[K] V) :=
  ⨆ h ∈ Rep, ⨆ (_ : h ≠ X - 1), specialBlock Q x h

theorem specialBlock_le_specialProduct {Rep : Finset K[X]} {h : K[X]} (hh : h ∈ Rep)
    (hne : h ≠ X - 1) : specialBlock Q x h ≤ specialProduct Q x Rep :=
  le_iSup₂_of_le h hh (le_iSup_of_le hne le_rfl)

end Blocks

section Decomposition

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.exists_decomposition_of_mem_commutator (hx : OddOrderIsometry Q p x)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep) {g : V ≃ₗ[K] V}
    (hg : g ∈ ⁅isometryCentralizer Q x, isometryCentralizer Q x⁆) :
    ∃ f ∈ supportedFixedDerived Q x, ∃ j ∈ specialProduct Q x Rep, g = j * f := by
  classical
  have hcomm := hx.blocks_commute hRep
  rw [← hx.blocks_iSup_eq hRep] at hg
  obtain ⟨w, hw, hgw⟩ := exists_noncommProd_of_mem_commutator
    (fun i : ↥Rep => supportedBlock Q x i) hcomm hg
  rw [Subgroup.noncommPiCoprod_apply] at hgw
  have hspec : ∀ i : ↥Rep, (i : K[X]) ≠ X - 1 → ((w i : ↥(supportedBlock Q x i)) : V ≃ₗ[K] V) ∈
      specialProduct Q x Rep := by
    intro i hi
    have h1 : ((w i : ↥(supportedBlock Q x i)) : V ≃ₗ[K] V) ∈
        ⁅supportedBlock Q x (i : K[X]), supportedBlock Q x (i : K[X])⁆ := hw i
    have h2 := commutator_supportedBlock_le_specialBlock (Q := Q) (x := x) (i : K[X]) h1
    exact specialBlock_le_specialProduct (Q := Q) (x := x) i.2 hi h2
  set f' : ↥Rep → V ≃ₗ[K] V := fun i => ((w i : ↥(supportedBlock Q x i)) : V ≃ₗ[K] V) with hf'
  have hcomm' : ((Finset.univ : Finset ↥Rep) : Set ↥Rep).Pairwise fun a b =>
      Commute (f' a) (f' b) := fun a _ b _ hab => hcomm hab _ _ (w a).2 (w b).2
  by_cases hex : (X - 1 : K[X]) ∈ Rep
  · set i₀ : ↥Rep := ⟨X - 1, hex⟩ with hi₀
    have hsplit := Finset.noncommProd_erase_mul (Finset.univ : Finset ↥Rep) (Finset.mem_univ i₀)
      f' hcomm'
    refine ⟨f' i₀, ?_, _, ?_, by rw [hgw, ← hsplit]⟩
    · rw [hx.supportedFixedDerived_eq]
      exact hw i₀
    · refine Subgroup.noncommProd_mem _ _ (fun c hc => ?_)
      have hne : (c : K[X]) ≠ X - 1 := fun heq =>
        (Finset.mem_erase.mp hc).1 (Subtype.ext heq)
      exact hspec c hne
  · refine ⟨1, one_mem _, _, ?_, by rw [mul_one, hgw]⟩
    refine Subgroup.noncommProd_mem _ _ (fun c _ => ?_)
    exact hspec c (fun heq => hex (heq ▸ c.2))

end Decomposition

section Fixed

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.block_fixes_fixedSpace (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1) {g : V ≃ₗ[K] V}
    (hg : g ∈ supportedBlock Q x h) {w : V} (hw : w ∈ fixedSpace x) : g w = w := by
  by_cases hX : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
  · have hne1' : reciprocalPolynomial h ≠ X - 1 := fun heq => hne (by
      rw [← hx.reciprocal_reciprocal_eq hh, heq, reciprocalPolynomial_X_sub_one])
    have := fixes_othersSpace_iff.mp (mem_supportedBlock.mp hg).2 (X - 1) hX (Ne.symm hne)
      (Ne.symm hne1')
    exact this w (by rw [fixedSpace_eq_primaryComponent] at hw; exact hw)
  · rw [fixedSpace_eq_bot_of_not_mem hX, Submodule.mem_bot] at hw
    rw [hw, map_zero]

theorem OddOrderIsometry.restrictFixed_trivial_of_mem_specialProduct (hx : OddOrderIsometry Q p x)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep) {j : V ≃ₗ[K] V}
    (hj : j ∈ specialProduct Q x Rep) (hjM : j ∈ isometryCentralizer Q x) :
    isometryRestrictFixed Q x ⟨j, hjM⟩ = 1 := by
  have hker : specialProduct Q x Rep ≤ (isometryRestrictFixed Q x).ker.map
      (isometryCentralizer Q x).subtype := by
    refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    intro g hg
    have hgB := specialBlock_le_supportedBlock h hg
    refine ⟨⟨g, supportedBlock_le_isometryCentralizer h hgB⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [coe_isometryRestrictFixed]
    exact hx.block_fixes_fixedSpace (hRep.1 hh) hne hgB w.2
  obtain ⟨y, hy, hyj⟩ := hker hj
  have : y = ⟨j, hjM⟩ := Subtype.ext hyj
  rw [← this]
  exact hy

end Fixed

section Dickson

variable {K : Type*} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem eq_one_of_dicksonHom_eq_one_of_finrank_le_one {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {R : QuadraticForm K W} (hR : R.polarBilin.Nondegenerate)
    (hW : finrank K W ≤ 1) {g : TauCeti.QuadraticMap.orthogonalGroup R}
    (hg : dicksonHom R hR g = 1) : (g : W ≃ₗ[K] W) = 1 := by
  have hev := even_finrank_commSpace_of_dicksonHom_eq_one hR hg
  have hle : finrank K (commSpace (g : W ≃ₗ[K] W)) ≤ 1 := (Submodule.finrank_le _).trans hW
  have h0 : finrank K (commSpace (g : W ≃ₗ[K] W)) = 0 := by
    obtain ⟨m, hm⟩ := hev
    omega
  have hbot : commSpace (g : W ≃ₗ[K] W) = ⊥ := Submodule.finrank_eq_zero.mp h0
  ext v
  have hv : (g : W ≃ₗ[K] W) v - v ∈ commSpace (g : W ≃ₗ[K] W) := sub_mem_commSpace _ v
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hv
  rw [hv, LinearEquiv.coe_one, id]

theorem OddOrderIsometry.dickson_restrict_eq_one (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    (hQ : Q.polarBilin.Nondegenerate) {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep)
    {m : V ≃ₗ[K] V} (hm : m ∈ isometryCentralizer Q x) (hmΩ : m ∈ orthDerived Q) :
    dicksonHom (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate
      ⟨isometryRestrictFixed Q x ⟨m, hm⟩, isometryRestrictFixed_mem_orthogonalGroup _⟩ = 1 := by
  have h1 : dicksonCentralizer Q x hQ ⟨m, hm⟩ = 1 :=
    dicksonHom_eq_one_of_mem_orthDerived hQ hmΩ
  have h2 := DFunLike.congr_fun (hx.dicksonCentralizer_eq_dicksonFixed hp2 hQ hRep) ⟨m, hm⟩
  rw [h1] at h2
  exact h2.symm

theorem OddOrderIsometry.restrict_commute_of_mem_orthDerived (hx : OddOrderIsometry Q p x)
    (hp2 : Odd p) (hQ : Q.polarBilin.Nondegenerate) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) (hdim : finrank K (fixedSpace x) ≤ 2)
    {m m' : V ≃ₗ[K] V} (hm : m ∈ isometryCentralizer Q x) (hmΩ : m ∈ orthDerived Q)
    (hm' : m' ∈ isometryCentralizer Q x) (hm'Ω : m' ∈ orthDerived Q) :
    Commute (isometryRestrictFixed Q x ⟨m, hm⟩) (isometryRestrictFixed Q x ⟨m', hm'⟩) := by
  have hQW := hx.polarBilin_fixed_nondegenerate
  have hδ := hx.dickson_restrict_eq_one hp2 hQ hRep hm hmΩ
  have hδ' := hx.dickson_restrict_eq_one hp2 hQ hRep hm' hm'Ω
  by_cases h2 : finrank K (fixedSpace x) = 2
  · exact commute_of_dicksonHom_eq_one hQW h2 (isometryRestrictFixed_mem_orthogonalGroup ⟨m, hm⟩)
      (isometryRestrictFixed_mem_orthogonalGroup ⟨m', hm'⟩) hδ hδ'
  · have hle : finrank K (fixedSpace x) ≤ 1 := by omega
    have e1 : isometryRestrictFixed Q x ⟨m, hm⟩ = 1 :=
      eq_one_of_dicksonHom_eq_one_of_finrank_le_one hQW hle hδ
    rw [e1]
    exact Commute.one_left _

end Dickson

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open scoped commutatorElement

theorem orthogonal_local_derived_centralizer_contained_in_layer
    {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hq : 3 < Nat.card K)
    (B : Subgroup (MulAut (ProjOrthDerived Q)))
    (hB : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (_hAcard : Nat.card A = p ^ 2) (a : ProjOrthDerived Q) (haA : a ∈ A) (ha1 : a ≠ 1)
    (x : orthDerived Q) (hxa : (QuotientGroup.mk x : ProjOrthDerived Q) = a)
    (hxp : orderOf x = p) :
    Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) =
        ((isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf (orthDerived Q)).map
          (QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
            (orthDerived Q))) ∧
      ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
          Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆ =
        (⁅(isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf (orthDerived Q),
            (isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf (orthDerived Q)⁆).map
          (QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
            (orthDerived Q))) ∧
      ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
          Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆ ≤
        (CFSG.layer ↥(Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).map
          (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))).subtype ∧
      ((CFSG.layer ↥(Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).map
          (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))).subtype).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
        (CFSG.layer ↥(B ⊓ Subgroup.centralizer
          ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
          (B ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype ∧
      ∀ φ : MulAut (ProjOrthDerived Q),
        (∀ e ∈ (CFSG.layer ↥(B ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
          (B ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype,
          φ * e = e * φ) →
        ∀ n ∈ ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
          Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆, φ n = n := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have ha : orderOf a = p := orderOf_eq_prime (hA.2 a haA) ha1
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  obtain ⟨⟨Rep0, hRep0⟩, hmain⟩ :=
    orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl B hB a ha x hxa hxp
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenterT : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj : Function.Injective (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) :=
    conj_injective_of_center_eq_bot hcenterT
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set N : Subgroup (ProjOrthDerived Q) := Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))
    with hN
  set Cba : Subgroup (MulAut (ProjOrthDerived Q)) :=
    B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))) with hCba
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q))
    with hρ
  set Mo : Subgroup ↥(orthDerived Q) := (isometryCentralizer Q xe).subgroupOf (orthDerived Q)
    with hMo
  obtain ⟨hNeq, -, -, -, -, hspec, -, -⟩ := hmain Rep0 hRep0
  have hNeq' : N = centralizerImage Q xe := hNeq
  set EN : Subgroup (ProjOrthDerived Q) := (CFSG.layer ↥N).map N.subtype with hEN
  have hcomp : ∀ C : Subgroup (ProjOrthDerived Q), CFSG.IsQuasisimple ↥C → C ≤ N →
      (C.subgroupOf N).IsSubnormal → C ≤ EN := by
    intro C hq hCN hsub
    have hc : CFSG.IsComponent (C.subgroupOf N) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCN).symm hq, hsub⟩
    have h1 := CFSG.LocalCores.component_le_layer hc
    calc C = (C.subgroupOf N).map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hCN).symm
      _ ≤ EN := Subgroup.map_mono h1
  have hbot : ∀ h ∈ Rep0, ¬ 2 ≤ primaryMultiplicity xe.toLinearMap h → specialBlock Q xe h = ⊥ := by
    intro h hh hm
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors (hRep0.1 hh)⟩
    have hpos := hx.primaryMultiplicity_pos (hRep0.1 hh)
    have h1 : primaryMultiplicity xe.toLinearMap h = 1 := by omega
    exact hx.specialBlock_eq_bot_of_finrank_eq_one (hRep0.1 hh) h1
  have hspecΩ : ∀ h ∈ Rep0, h ≠ X - 1 → specialBlock Q xe h ≤ orthDerived Q := by
    intro h hh hne
    by_cases hm : 2 ≤ primaryMultiplicity xe.toLinearMap h
    · exact (hspec h hh hne hm).1
    · rw [hbot h hh hm]
      exact bot_le
  have hspecEN : ∀ h ∈ Rep0, h ≠ X - 1 → componentImage Q xe h ≤ EN := by
    intro h hh hne
    by_cases hm : 2 ≤ primaryMultiplicity xe.toLinearMap h
    · obtain ⟨-, -, -, hq, hle, hnorm, -⟩ := hspec h hh hne hm
      exact hcomp _ hq hle hnorm.isSubnormal
    · have : componentImage Q xe h = ⊥ := by
        unfold componentImage
        rw [hbot h hh hm, Subgroup.bot_subgroupOf, Subgroup.map_bot]
      rw [this]
      exact bot_le
  set K₀ : Subgroup (V ≃ₗ[K] V) := (EN.comap ρ).map (orthDerived Q).subtype with hK₀
  have hmemK₀ : ∀ b : ↥(orthDerived Q), ρ b ∈ EN → (b : V ≃ₗ[K] V) ∈ K₀ :=
    fun b hb => ⟨b, hb, rfl⟩
  have hspK₀ : specialProduct Q xe Rep0 ≤ K₀ := by
    refine iSup₂_le fun h hh => iSup_le fun hne => ?_
    intro j hj
    have hjΩ := hspecΩ h hh hne hj
    refine hmemK₀ ⟨j, hjΩ⟩ (hspecEN h hh hne ?_)
    exact Subgroup.mem_map.mpr ⟨⟨j, hjΩ⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
  have hlayerEN : FixedLayerListed Q xe → fixedComponentImage Q xe ≤ EN := by
    intro hlist
    obtain ⟨n, C, -, -, hsup, hC, -, -⟩ := hx.fixedLayer_data hlist
    rw [← hsup]
    refine iSup_le fun i => hcomp (C i) (hC i).1 ?_ ?_
    · rw [hNeq']
      exact (hC i).2.1
    · rw [hNeq']
      exact (hC i).2.2
  have hsfdK₀ : FixedLayerListed Q xe → supportedFixedDerived Q xe ≤ K₀ := by
    intro hlist f hf
    have hfΩ := hx.supportedFixedDerived_le_orthDerived hf
    refine hmemK₀ ⟨f, hfΩ⟩ (hlayerEN hlist ?_)
    exact Subgroup.mem_map.mpr ⟨⟨f, hfΩ⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
  have hspM : specialProduct Q xe Rep0 ≤ isometryCentralizer Q xe :=
    iSup₂_le fun h _ => iSup_le fun _ => specialBlock_le_isometryCentralizer h
  have hkey : ⁅Mo, Mo⁆ ≤ EN.comap ρ := by
    rw [Subgroup.commutator_le]
    intro m hm m' hm'
    have hmM : (m : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := Subgroup.mem_subgroupOf.mp hm
    have hm'M : (m' : V ≃ₗ[K] V) ∈ isometryCentralizer Q xe := Subgroup.mem_subgroupOf.mp hm'
    have hg : (((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V) ∈
        ⁅isometryCentralizer Q xe, isometryCentralizer Q xe⁆ :=
      Subgroup.commutator_mem_commutator hmM hm'M
    obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep0 hg
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
            (hx.restrict_commute_of_mem_orthDerived hp2 hQ hRep0 hdim2 hmM m.2 hm'M m'.2).eq
        have h3 : isometryRestrictFixed Q xe ⟨f, hfM⟩ = 1 := by
          have h4 : (⟨(((⁅m, m'⁆ : ↥(orthDerived Q))) : V ≃ₗ[K] V), hgM⟩ :
              ↥(isometryCentralizer Q xe)) = ⟨j, hjM⟩ * ⟨f, hfM⟩ := Subtype.ext hgjf
          rw [h4, map_mul, hx.restrictFixed_trivial_of_mem_specialProduct hRep0 hj hjM,
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
  have hle : ⁅N, N⁆ ≤ EN := by
    rw [hNN]
    exact Subgroup.map_le_iff_le_comap.mpr hkey
  have hlay : (CFSG.layer ↥N).map (conjToCentralizer hB a) ≤ CFSG.layer ↥Cba := by
    rw [Subgroup.map_le_iff_le_comap]
    change sSup {K : Subgroup ↥N | CFSG.IsComponent K} ≤ _
    refine sSup_le fun J hJ => ?_
    have hJ' : CFSG.IsComponent J := hJ
    exact Subgroup.map_le_iff_le_comap.mp (CFSG.LocalCores.component_le_layer
      (isComponent_map_conjToCentralizer_of_subnormal hB a hinj hJ'.2 hJ'.1))
  have hlayers : EN.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
      (CFSG.layer ↥Cba).map Cba.subtype := by
    rw [hEN, Subgroup.map_map]
    have h1 : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).comp N.subtype =
        Cba.subtype.comp (conjToCentralizer hB a) := MonoidHom.ext fun n => rfl
    rw [h1, ← Subgroup.map_map]
    exact Subgroup.map_mono hlay
  refine ⟨hNeq, hNN, hle, hlayers, ?_⟩
  intro φ hφ n hn
  have hconj : MulAut.conj n ∈ (CFSG.layer ↥Cba).map Cba.subtype :=
    hlayers (Subgroup.mem_map_of_mem _ (hle hn))
  have h1 := hφ _ hconj
  apply hinj
  have h2 : MulAut.conj (φ n) = φ * MulAut.conj n * φ⁻¹ := by
    ext t
    simp [MulAut.conj_apply]
  rw [h2, h1, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.RankThree.PartOne
