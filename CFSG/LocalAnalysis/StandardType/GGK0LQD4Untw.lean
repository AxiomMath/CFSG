module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4D4
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
public import CFSG.RankThree.PartOne.KD4L.TranspositionLayer
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgClass
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.E6FourFine
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.LocalAnalysis.GLTheoremA.K155X CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
open scoped Matrix MatrixGroups
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  D4TrialityLayer d4Nodes)


private theorem lk0xlqd4un_swapLayerFine_generic
    {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (hf : 1 ≤ f) (σ : Equiv.Perm (Fin Tag.D4.rank))
    (hE : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ σ ∧ E6Fix (ℓ := ℓ) f n₂ ∧
      OmegaMinus8Fine ℓ f (fixE6 ℓ f n₂))
    (π : Equiv.Perm (Fin τ.rank)) (hπσ : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (σ k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    OmegaMinus8Fine ℓ f P := by
  obtain ⟨n₂, h₂, -, hfine⟩ := hE
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdSwap n₁ π σ := ⟨hπ, hπ', hπσ, hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact fine_layer_swap hstd h₂ hfine hh hlang hP

private theorem lk0xlqd4un_d4SwapLayerFine_of_leafSwap
    {τ : Tag} [E6Sub τ]
    (hleaf : ∀ i j : Fin τ.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
      (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
      ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4))) :
    D4SwapLayerFine τ := by
  intro L _ _ ℓ f _ _ hf i j hij hi hj n hn _ hact P hP
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := hleaf i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact lk0xlqd4un_swapLayerFine_generic hf (Equiv.swap 1 3) (exists_fix_swap13_fine hf)
      (Equiv.swap i j) h1 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact lk0xlqd4un_swapLayerFine_generic hf (Equiv.swap 0 3) (exists_fix_swap03_fine hf)
      (Equiv.swap i j) h2 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP
  · exact lk0xlqd4un_swapLayerFine_generic hf (Equiv.swap 0 1) (exists_fix_swap01_fine hf)
      (Equiv.swap i j) h3 (fun x hx => hπ x hx) (fun x hx => hπ' x hx) n hn hact P hP

theorem lq_d4SwapLayerFine_E7 :
    D4SwapLayerFine Tag.E7 :=
  lk0xlqd4un_d4SwapLayerFine_of_leafSwap leafSwap_E7

theorem lq_d4SwapLayerFine_E8 :
    D4SwapLayerFine Tag.E8 :=
  lk0xlqd4un_d4SwapLayerFine_of_leafSwap leafSwap_E8

private def lk0xlqd4un_RefJ (τ : Tag) : Set (WeylGroup τ) :=
  {s | ∃ γ ∈ parabolicRoots τ (d4Nodes τ), s = rootReflection γ}

private def lk0xlqd4un_D4Ev {τ : Tag} (x : Fin τ.rank → ℤ) : Prop :=
  ∀ j ∈ d4Nodes τ, 2 ∣ iform x (Pi.single j 1)

private theorem lk0xlqd4un_iform_expand
    {τ : Tag} (x γ : Fin τ.rank → ℤ) :
    iform x γ = ∑ k, γ k * iform x (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single γ]
  rw [iform_finset_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : (Pi.single k (γ k) : Fin τ.rank → ℤ) = γ k • (Pi.single k 1) := by
    ext j
    simp [Pi.single_apply]
  rw [h, iform_smul_right]

private theorem lk0xlqd4un_even_iform
    {τ : Tag} {x γ : Fin τ.rank → ℤ} (hx : lk0xlqd4un_D4Ev x)
    (hγ : ∀ k ∉ d4Nodes τ, γ k = 0) : 2 ∣ iform x γ := by
  rw [lk0xlqd4un_iform_expand]
  refine Finset.dvd_sum fun k _ => ?_
  by_cases hk : k ∈ d4Nodes τ
  · exact Dvd.dvd.mul_left (hx k hk) _
  · rw [hγ k hk, zero_mul]
    exact dvd_zero 2

private theorem lk0xlqd4un_rootReflection_smul
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (x : Fin τ.rank → ℤ) :
    rootReflection γ • x = x - iform γ x • γ := by
  rw [rootReflection_smul hγ x]
  have h : corootPair γ x = iform γ x := by
    unfold corootPair
    rw [CFSG.SeitzReduction.EPilot.iform_self_eq_two hτ hγ]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [h]

private theorem lk0xlqd4un_parity_refl
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ parabolicRoots τ (d4Nodes τ)) (x : Fin τ.rank → ℤ) :
    (lk0xlqd4un_D4Ev x → lk0xlqd4un_D4Ev (rootReflection γ • x)) ∧
      (lk0xlqd4un_D4Ev x → ∀ k, 2 ∣ (rootReflection γ • x - x) k) := by
  have hr := lk0xlqd4un_rootReflection_smul hτ hγ.1 x
  have hc : lk0xlqd4un_D4Ev x → 2 ∣ iform γ x := fun hx => by
    rw [iform_comm]
    exact lk0xlqd4un_even_iform hx hγ.2
  refine ⟨fun hx j hj => ?_, fun hx k => ?_⟩
  · rw [hr, iform_sub_left, iform_smul_left]
    exact dvd_sub (hx j hj) (Dvd.dvd.mul_right (hc hx) _)
  · rw [hr]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel_left]
    exact dvd_neg.2 (Dvd.dvd.mul_right (hc hx) _)

private theorem lk0xlqd4un_parity
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {u : WeylGroup τ}
    (hu : u ∈ Subgroup.closure (lk0xlqd4un_RefJ τ)) :
    ∀ x : Fin τ.rank → ℤ, (lk0xlqd4un_D4Ev x ↔ lk0xlqd4un_D4Ev (u • x)) ∧
      (lk0xlqd4un_D4Ev x → ∀ k, 2 ∣ (u • x - x) k) := by
  refine Subgroup.closure_induction
    (p := fun w _ => ∀ x : Fin τ.rank → ℤ, (lk0xlqd4un_D4Ev x ↔ lk0xlqd4un_D4Ev (w • x)) ∧
      (lk0xlqd4un_D4Ev x → ∀ k, 2 ∣ (w • x - x) k)) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨γ, hγ, rfl⟩ x
    refine ⟨⟨(lk0xlqd4un_parity_refl hτ hγ x).1, fun h => ?_⟩,
      (lk0xlqd4un_parity_refl hτ hγ x).2⟩
    have h1 := (lk0xlqd4un_parity_refl hτ hγ (rootReflection γ • x)).1 h
    rwa [smul_smul, rootReflection_mul_self hγ.1, one_smul] at h1
  · intro x
    exact ⟨by simp, fun _ k => by simp⟩
  · intro u v _ _ ihu ihv x
    rw [mul_smul]
    refine ⟨⟨fun hx => (ihu (v • x)).1.mp ((ihv x).1.mp hx),
      fun hx => (ihv x).1.mpr ((ihu (v • x)).1.mpr hx)⟩, fun hx k => ?_⟩
    have h1 : 2 ∣ (u • (v • x) - v • x) k := (ihu (v • x)).2 ((ihv x).1.mp hx) k
    have h2 : 2 ∣ (v • x - x) k := (ihv x).2 hx k
    have hsum : (u • (v • x) - x) k = (u • (v • x) - v • x) k + (v • x - x) k := by
      simp only [Pi.sub_apply]
      ring
    rw [hsum]
    exact dvd_add h1 h2
  · intro u _ ihu x
    have hux : u • (u⁻¹ • x) = x := smul_inv_smul u x
    have hiff : lk0xlqd4un_D4Ev x ↔ lk0xlqd4un_D4Ev (u⁻¹ • x) := by
      have h := (ihu (u⁻¹ • x)).1
      rw [hux] at h
      exact h.symm
    refine ⟨hiff, fun hx k => ?_⟩
    have hd : 2 ∣ (x - u⁻¹ • x) k := by
      have h := (ihu (u⁻¹ • x)).2 (hiff.1 hx) k
      rwa [hux] at h
    have h3 : (u⁻¹ • x - x) k = -((x - u⁻¹ • x) k) := by
      simp only [Pi.sub_apply]
      ring
    rw [h3]
    exact dvd_neg.2 hd

private abbrev lk0xlqd4un_es {τ : Tag} (p : Fin τ.rank) : Fin τ.rank → ℤ := Pi.single p 1

private theorem lk0xlqd4un_leaf_mem {τ : Tag} {p : Fin τ.rank} (hp : p.val ∈ ({1, 2, 4} : Set ℕ)) :
    p ∈ d4Nodes τ := by
  simp only [d4Nodes, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
  omega

private theorem lk0xlqd4un_single_mem {τ : Tag} {i : Fin τ.rank} (hi : i ∈ d4Nodes τ) :
    lk0xlqd4un_es i ∈ parabolicRoots τ (d4Nodes τ) :=
  ⟨isRoot_single τ i, fun j hj => Pi.single_eq_of_ne (fun h => hj (by rw [h]; exact hi)) 1⟩

private theorem lk0xlqd4un_iform_single_single {τ : Tag} (p j : Fin τ.rank) :
    iform (Pi.single p 1 : Fin τ.rank → ℤ) (Pi.single j 1) = τ.symmetrizedCartan p j := by
  simp [iform, Pi.single_apply]

private theorem lk0xlqd4un_cartan_pair_even
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (p q j : Fin τ.rank) (hp : p.val ∈ ({1, 2, 4} : Set ℕ)) (hq : q.val ∈ ({1, 2, 4} : Set ℕ))
    (hj : j ∈ d4Nodes τ) :
    2 ∣ τ.symmetrizedCartan p j + τ.symmetrizedCartan q j := by
  have hp' : p.val = 1 ∨ p.val = 2 ∨ p.val = 4 := by simpa using hp
  have hq' : q.val = 1 ∨ q.val = 2 ∨ q.val = 4 := by simpa using hq
  have hj' : 1 ≤ j.val ∧ j.val ≤ 4 := hj
  clear hp hq hj
  rcases hτ with rfl | rfl | rfl <;>
    (fin_cases p <;> fin_cases q <;> fin_cases j <;>
      first | decide +kernel | (exfalso; revert hp' hq' hj'; decide +kernel))

private theorem lk0xlqd4un_ev_add
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p q : Fin τ.rank} (hp : p.val ∈ ({1, 2, 4} : Set ℕ)) (hq : q.val ∈ ({1, 2, 4} : Set ℕ)) :
    lk0xlqd4un_D4Ev (lk0xlqd4un_es p + lk0xlqd4un_es q) := by
  intro j hj
  rw [iform_add_left, lk0xlqd4un_iform_single_single, lk0xlqd4un_iform_single_single]
  exact lk0xlqd4un_cartan_pair_even hτ p q j hp hq hj

private theorem lk0xlqd4un_not_inner_sq_leafThreeCycle
    {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a b c : Fin τ.rank}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a.val ∈ ({1, 2, 4} : Set ℕ))
    (hb : b.val ∈ ({1, 2, 4} : Set ℕ)) (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    {u u'' : WeylGroup τ} (hu : u ∈ Subgroup.closure (lk0xlqd4un_RefJ τ))
    (hu'' : u'' ∈ Subgroup.closure (lk0xlqd4un_RefJ τ))
    (f : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      f α = u • permLattice (List.formPerm [a, b, c]) α)
    (hsq : ∀ α ∈ parabolicRoots τ (d4Nodes τ), f (f α) = u'' • α) : False := by
  have hroot_a := lk0xlqd4un_single_mem (lk0xlqd4un_leaf_mem ha)
  have hroot_b := lk0xlqd4un_single_mem (lk0xlqd4un_leaf_mem hb)
  have hroot_c := lk0xlqd4un_single_mem (lk0xlqd4un_leaf_mem hc)
  have hπa : List.formPerm [a, b, c] a = b := by
    rw [List.formPerm_cons_cons, List.formPerm_pair, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (a := b) (b := c) (x := a) hab hac, Equiv.swap_apply_left]
  have hπb : List.formPerm [a, b, c] b = c := by
    rw [List.formPerm_cons_cons, List.formPerm_pair, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (a := a) (b := b) (x := c) (Ne.symm hac) (Ne.symm hbc)]
  have hπc : List.formPerm [a, b, c] c = a := by
    rw [List.formPerm_cons_cons, List.formPerm_pair, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_right]
  have hwa : f (lk0xlqd4un_es a) = u • lk0xlqd4un_es b := by
    have h := hact (lk0xlqd4un_es a) hroot_a
    rwa [permLattice_single, hπa] at h
  have hwb : f (lk0xlqd4un_es b) = u • lk0xlqd4un_es c := by
    have h := hact (lk0xlqd4un_es b) hroot_b
    rwa [permLattice_single, hπb] at h
  have hwc : f (lk0xlqd4un_es c) = u • lk0xlqd4un_es a := by
    have h := hact (lk0xlqd4un_es c) hroot_c
    rwa [permLattice_single, hπc] at h
  have hsa : f (u • lk0xlqd4un_es b) = u'' • lk0xlqd4un_es a := by
    have h := hsq (lk0xlqd4un_es a) hroot_a
    rwa [hwa] at h
  have hsb : f (u • lk0xlqd4un_es c) = u'' • lk0xlqd4un_es b := by
    have h := hsq (lk0xlqd4un_es b) hroot_b
    rwa [hwb] at h
  have step1 := lk0xlqd4un_parity hτ hu
  have step3 := lk0xlqd4un_parity hτ hu''
  have hdiv1 := (step1 (lk0xlqd4un_es b + lk0xlqd4un_es c)).2 (lk0xlqd4un_ev_add hτ hb hc)
  have hdiv2 := (step1 (lk0xlqd4un_es c + lk0xlqd4un_es a)).2 (lk0xlqd4un_ev_add hτ hc ha)
  have hdiv3 := (step3 (lk0xlqd4un_es a + lk0xlqd4un_es b)).2 (lk0xlqd4un_ev_add hτ ha hb)
  obtain ⟨t1, ht1⟩ : ∃ t : Fin τ.rank → ℤ,
      u • (lk0xlqd4un_es b + lk0xlqd4un_es c) - (lk0xlqd4un_es b + lk0xlqd4un_es c) =
        (2 : ℤ) • t :=
    ⟨fun k => (u • (lk0xlqd4un_es b + lk0xlqd4un_es c) -
        (lk0xlqd4un_es b + lk0xlqd4un_es c)) k / 2, by
      ext k
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (Int.mul_ediv_cancel' (hdiv1 k)).symm⟩
  obtain ⟨t2, ht2⟩ : ∃ t : Fin τ.rank → ℤ,
      u • (lk0xlqd4un_es c + lk0xlqd4un_es a) - (lk0xlqd4un_es c + lk0xlqd4un_es a) =
        (2 : ℤ) • t :=
    ⟨fun k => (u • (lk0xlqd4un_es c + lk0xlqd4un_es a) -
        (lk0xlqd4un_es c + lk0xlqd4un_es a)) k / 2, by
      ext k
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (Int.mul_ediv_cancel' (hdiv2 k)).symm⟩
  obtain ⟨t3, ht3⟩ : ∃ t : Fin τ.rank → ℤ,
      u'' • (lk0xlqd4un_es a + lk0xlqd4un_es b) - (lk0xlqd4un_es a + lk0xlqd4un_es b) =
        (2 : ℤ) • t :=
    ⟨fun k => (u'' • (lk0xlqd4un_es a + lk0xlqd4un_es b) -
        (lk0xlqd4un_es a + lk0xlqd4un_es b)) k / 2, by
      ext k
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (Int.mul_ediv_cancel' (hdiv3 k)).symm⟩
  have hy1 : u • lk0xlqd4un_es b + u • lk0xlqd4un_es c =
      (lk0xlqd4un_es b + lk0xlqd4un_es c) + (2 : ℤ) • t1 := by
    rw [← smul_add, ← ht1]
    abel
  have hy2 : u • lk0xlqd4un_es c + u • lk0xlqd4un_es a =
      (lk0xlqd4un_es c + lk0xlqd4un_es a) + (2 : ℤ) • t2 := by
    rw [← smul_add, ← ht2]
    abel
  have hy3 : u'' • lk0xlqd4un_es a + u'' • lk0xlqd4un_es b =
      (lk0xlqd4un_es a + lk0xlqd4un_es b) + (2 : ℤ) • t3 := by
    rw [← smul_add, ← ht3]
    abel
  have hL : f (u • lk0xlqd4un_es b + u • lk0xlqd4un_es c) =
      (lk0xlqd4un_es a + lk0xlqd4un_es b) + (2 : ℤ) • t3 := by
    rw [map_add, hsa, hsb, hy3]
  have hR : f ((lk0xlqd4un_es b + lk0xlqd4un_es c) + (2 : ℤ) • t1) =
      (lk0xlqd4un_es c + lk0xlqd4un_es a) + (2 : ℤ) • (t2 + f t1) := by
    rw [map_add, map_add, map_zsmul, hwb, hwc, smul_add, ← add_assoc, hy2]
  have hmain : (lk0xlqd4un_es a + lk0xlqd4un_es b) + (2 : ℤ) • t3 =
      (lk0xlqd4un_es c + lk0xlqd4un_es a) + (2 : ℤ) • (t2 + f t1) := by
    calc (lk0xlqd4un_es a + lk0xlqd4un_es b) + (2 : ℤ) • t3
        = f (u • lk0xlqd4un_es b + u • lk0xlqd4un_es c) := hL.symm
      _ = f ((lk0xlqd4un_es b + lk0xlqd4un_es c) + (2 : ℤ) • t1) := by rw [hy1]
      _ = _ := hR
  have hca : (lk0xlqd4un_es a) c = 0 := Pi.single_eq_of_ne (Ne.symm hac) 1
  have hcb : (lk0xlqd4un_es b) c = 0 := Pi.single_eq_of_ne (Ne.symm hbc) 1
  have hcc : (lk0xlqd4un_es c) c = 1 := Pi.single_eq_same c 1
  have hval := congrFun hmain c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hca, hcb, hcc] at hval
  omega

private theorem lk0xlqd4un_conj_mem
    {τ : Tag} (v : WeylGroup τ) {t : WeylGroup τ}
    (ht : t ∈ Subgroup.closure {s | ∃ β ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ),
      s = rootReflection β}) :
    v⁻¹ * t * v ∈ Subgroup.closure (lk0xlqd4un_RefJ τ) := by
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, ⟨α, hα, rfl⟩, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨α, hα, ?_⟩
    show v⁻¹ * rootReflection (v • α) * v = rootReflection α
    rw [rootReflection_smul_root v hα.1]
    group
  | one => simp
  | mul x y _ _ hx hy =>
    have e : v⁻¹ * (x * y) * v = (v⁻¹ * x * v) * (v⁻¹ * y * v) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : v⁻¹ * x⁻¹ * v = (v⁻¹ * x * v)⁻¹ := by group
    rw [e]
    exact inv_mem hx

private theorem lk0xlqd4un_exists_inner_sq
    {τ : Tag} {v : WeylGroup τ} {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : Ψ = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    {σ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (h : twistInner Ψ σ) :
    ∃ u'' ∈ Subgroup.closure (lk0xlqd4un_RefJ τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      v⁻¹ • σ (v • α) = u'' • α := by
  obtain ⟨w, hw, hσ⟩ := h
  subst hΨ
  exact ⟨v⁻¹ * w * v, lk0xlqd4un_conj_mem v hw, fun α hα => by
    rw [hσ (v • α) ⟨α, hα, rfl⟩, mul_smul, mul_smul]⟩

private theorem lk0xlqd4un_parabolic_le
    {τ : Tag} :
    parabolicWeylGroup τ (d4Nodes τ) ≤ Subgroup.closure (lk0xlqd4un_RefJ τ) := by
  unfold parabolicWeylGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  refine Subgroup.subset_closure ⟨Pi.single j 1, ⟨isRoot_single τ j, fun k hk =>
    Pi.single_eq_of_ne (fun h => hk (by rw [h]; exact hj)) 1⟩, ?_⟩
  have h := rootReflection_eq_conj (τ := τ) (w := 1) (j := j) (by rw [one_smul])
  rw [h]
  group

theorem lq_d4_untw
    {τ : Tag} [E6Sub τ] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (hsearch : D4BaseSearch τ) (hL2 : D4SwapLayer τ) (hR2 : D4SwapLayerFine τ)
    (S : LangSetup τ L p) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (h2 : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) (hq : S.D.q = ℓ ^ f) :
    OmegaMinus8Fine ℓ f (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  have hs := componentOrbitLength_eq_one hfin hρ
  rw [hs, Function.iterate_one] at h1
  rw [hs] at h2
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Nodes τ), w₀ • α = permLattice π α :=
    fun α hα => by
      have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
        (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
      rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  obtain ⟨u'', hu'', hu''act⟩ := lk0xlqd4un_exists_inner_sq hΨ
    (σ := (S.ρ : (Fin τ.rank → ℤ) → _)^[2]) (by simpa using h2)
  have hsq : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • (v⁻¹ * w * v) • α = u'' • α := by
    intro α hα
    have hvα : v • α ∈ Ψ := hΨ ▸ ⟨α, hα, rfl⟩
    have hwvα : w • v • α = S.ρ (v • α) := (hρw (v • α) hvα.1.1).symm
    have hww : w • w • v • α = (S.ρ : (Fin τ.rank → ℤ) → _)^[2] (v • α) := by
      rw [hwvα]
      exact (hρw (S.ρ (v • α)) (hρ (v • α) hvα).1.1).symm
    rw [← hu''act α hα, ← hww]
    calc (v⁻¹ * w * v) • (v⁻¹ * w * v) • α
        = v⁻¹ • w • (v • (v⁻¹ • (w • v • α))) := by simp only [mul_smul]
      _ = v⁻¹ • w • w • v • α := by rw [smul_inv_smul]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ :
      γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  let fw : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) :=
    { toFun := fun x => (v⁻¹ * w * v) • x
      map_zero' := smul_zero _
      map_add' := fun x y => smul_add _ x y }
  have hu' := lk0xlqd4un_parabolic_le hu
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) ∧
      OmegaMinus8Fine ℓ f (rootSpan τ L Ψ ⊓ S.D.model) := by
    rw [hΨ]
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact).2,
        fine_rootSpan_inf_model_d4_swap hR2 S hFr hΦ hn v hu h12 hv1 hv2 hact hf hq⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact).2,
        fine_rootSpan_inf_model_d4_swap hR2 S hFr hΦ hn v hu h14 hv1 hv4 hact hf hq⟩
    · exact ⟨(rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact).2,
        fine_rootSpan_inf_model_d4_swap hR2 S hFr hΦ hn v hu h24 hv2 hv4 hact hf hq⟩
    · exact (lk0xlqd4un_not_inner_sq_leafThreeCycle hτ h12 h24 h14 hv1 hv2 hv4 hu' hu'' fw hact
        hsq).elim
    · exact (lk0xlqd4un_not_inner_sq_leafThreeCycle hτ h14 h24.symm h12 hv1 hv4 hv2 hu' hu'' fw
        hact hsq).elim
  rw [rationalComponent_eq_of_layer S i hρ hlayer.1]
  exact hlayer.2

end CFSG.StandardType.GGK0LQ

end
