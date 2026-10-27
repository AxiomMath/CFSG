module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourKac
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.GGFinModel CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag IsElemAbelian)

@[expose] def rckNb (k : Fin 4) : Fin Tag.E8.rank → ℤ :=
  match k with
  | 0 => ![0, 1, 0, 0, 0, 0, 0, 0]
  | 1 => ![0, 0, 1, 0, 0, 0, 0, 0]
  | 2 => ![0, 0, 0, 0, 1, 0, 0, 0]
  | 3 => ![0, 1, 1, 2, 1, 0, 0, 0]

theorem rckNb_root_list : ∀ k : Fin 4, List.ofFn (rckNb k) ∈ Tag.E8.artifactRoots := by
  decide +kernel

theorem rckNb_orth :
    ∀ k l : Fin 4, k ≠ l → iform (τ := Tag.E8) (rckNb k) (rckNb l) = 0 := by
  decide +kernel

theorem rckNb_self :
    ∀ k : Fin 4, iform (τ := Tag.E8) (rckNb k) (rckNb k) = 2 := by
  decide +kernel

theorem rck_refl_apply
    {τ : Tag} {b x : Fin τ.rank → ℤ} (hb : IsRoot τ b) (h2 : iform b b = 2) :
    rootReflection b • x = x - iform b x • b := by
  rw [rootReflection_smul hb]
  have h : corootPair b x = iform b x := by
    unfold corootPair
    rw [h2]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [h]

theorem rck_iform_sub_smul
    {τ : Tag} (b' x b : Fin τ.rank → ℤ) (c : ℤ) :
    iform b' (x - c • b) = iform b' x - c * iform b' b := by
  rw [iform_comm b' (x - c • b), sub_eq_add_neg, ← neg_smul, iform_add_left, iform_smul_left,
    iform_comm x b', iform_comm b b']
  ring

noncomputable def rckW0 : WeylGroup Tag.E8 :=
  rootReflection (rckNb 0) * rootReflection (rckNb 1) * rootReflection (rckNb 2) *
    rootReflection (rckNb 3)

theorem rckNb_root (k : Fin 4) : IsRoot Tag.E8 (rckNb k) :=
  isRoot_iff_mem_artifactRoots.2 (rckNb_root_list k)

theorem rckW0_apply
    (x : Fin Tag.E8.rank → ℤ) :
    rckW0 • x = x - iform (rckNb 0) x • rckNb 0 - iform (rckNb 1) x • rckNb 1 -
      iform (rckNb 2) x • rckNb 2 - iform (rckNb 3) x • rckNb 3 := by
  have o01 := rckNb_orth 0 1 (by decide)
  have o02 := rckNb_orth 0 2 (by decide)
  have o03 := rckNb_orth 0 3 (by decide)
  have o12 := rckNb_orth 1 2 (by decide)
  have o13 := rckNb_orth 1 3 (by decide)
  have o23 := rckNb_orth 2 3 (by decide)
  unfold rckW0
  simp only [mul_smul]
  rw [rck_refl_apply (rckNb_root 3) (rckNb_self 3), rck_refl_apply (rckNb_root 2) (rckNb_self 2),
    rck_refl_apply (rckNb_root 1) (rckNb_self 1), rck_refl_apply (rckNb_root 0) (rckNb_self 0)]
  simp only [rck_iform_sub_smul, o01, o02, o03, o12, o13, o23, mul_zero, sub_zero]
  abel

theorem rckW0_single :
    ∀ j : Fin Tag.E8.rank, 1 ≤ j.val → j.val ≤ 4 →
      (Pi.single j 1 : Fin Tag.E8.rank → ℤ) -
        iform (τ := Tag.E8) (rckNb 0) (Pi.single j 1) • rckNb 0 -
        iform (τ := Tag.E8) (rckNb 1) (Pi.single j 1) • rckNb 1 -
        iform (τ := Tag.E8) (rckNb 2) (Pi.single j 1) • rckNb 2 -
        iform (τ := Tag.E8) (rckNb 3) (Pi.single j 1) • rckNb 3 = -(Pi.single j 1) := by
  decide +kernel

@[expose] def rckD4Nodes : Set (Fin Tag.E8.rank) := {j | 1 ≤ j.val ∧ j.val ≤ 4}

theorem rckNb_supp : ∀ k : Fin 4, ∀ i : Fin Tag.E8.rank, ¬ (1 ≤ i.val ∧ i.val ≤ 4) →
    rckNb k i = 0 := by
  decide +kernel

theorem rckW0_neg_supported
    {α : Fin Tag.E8.rank → ℤ} (hα : ∀ i : Fin Tag.E8.rank, ¬ (1 ≤ i.val ∧ i.val ≤ 4) → α i = 0) :
    rckW0 • α = -α := by
  have hsum : α = ∑ j, α j • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) := by
    conv_lhs => rw [← Finset.univ_sum_single α]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul]
    simp
  have hbasis : ∀ j : Fin Tag.E8.rank, 1 ≤ j.val → j.val ≤ 4 →
      rckW0 • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) = -(Pi.single j 1) := fun j h1 h2 => by
    rw [rckW0_apply]
    exact rckW0_single j h1 h2
  calc rckW0 • α = rckW0 • ∑ j, α j • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) := by rw [← hsum]
    _ = ∑ j, α j • (rckW0 • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    _ = ∑ j, -(α j • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : 1 ≤ j.val ∧ j.val ≤ 4
        · rw [hbasis j hj.1 hj.2, smul_neg]
        · rw [hα j hj]
          simp
    _ = -α := by
        rw [Finset.sum_neg_distrib, ← hsum]

theorem rck_neg_inner
    (v : WeylGroup Tag.E8) :
    twistInner ((fun α => v • α) '' parabolicRoots Tag.E8 rckD4Nodes) (fun γ => -γ) := by
  have hmem : ∀ k : Fin 4, v • rckNb k ∈
      (fun α => v • α) '' parabolicRoots Tag.E8 rckD4Nodes := fun k =>
    ⟨rckNb k, ⟨rckNb_root k, fun i hi => rckNb_supp k i hi⟩, rfl⟩
  refine ⟨v * rckW0 * v⁻¹, ?_, ?_⟩
  · have h : v * rckW0 * v⁻¹ = rootReflection (v • rckNb 0) * rootReflection (v • rckNb 1) *
        rootReflection (v • rckNb 2) * rootReflection (v • rckNb 3) := by
      rw [rootReflection_smul_root v (rckNb_root 0), rootReflection_smul_root v (rckNb_root 1),
        rootReflection_smul_root v (rckNb_root 2), rootReflection_smul_root v (rckNb_root 3)]
      unfold rckW0
      group
    rw [h]
    have hcl : ∀ k : Fin 4, rootReflection (v • rckNb k) ∈ Subgroup.closure
        {s : WeylGroup Tag.E8 | ∃ γ ∈ (fun α => v • α) '' parabolicRoots Tag.E8 rckD4Nodes,
          s = rootReflection γ} := fun k => Subgroup.subset_closure ⟨_, hmem k, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hcl 0) (hcl 1)) (hcl 2))
      (hcl 3)
  · rintro _ ⟨α, hα, rfl⟩
    show -(v • α) = (v * rckW0 * v⁻¹) • (v • α)
    rw [mul_smul, mul_smul, inv_smul_smul, rckW0_neg_supported hα.2, smul_neg]

theorem rckExc_not_shape_D4_of_neg
    (hneg4 : ∀ v : WeylGroup Tag.E8,
      twistInner ((fun α => v • α) '' parabolicRoots Tag.E8 rckD4Nodes) (fun γ => -γ))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin Tag.E8.rank → GGLˣ}
    (hpa : rootDiagUnit Tag.E8 a ^ p = 1) {ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    (hroot : ∀ γ, IsRoot Tag.E8 (ρ γ) ↔ IsRoot Tag.E8 γ) (hneg : ∀ γ, ρ (-γ) = -ρ γ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ)
    (hsq : ∀ γ, IsRoot Tag.E8 γ → ρ (ρ γ) = -γ)
    (hstab : ∀ γ ∈ kernelRoots (rootCharHom a), ρ γ ∈ kernelRoots (rootCharHom a))
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24 ∧
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((ρ : (Fin Tag.E8.rank → ℤ) → _)^[2 *
          componentOrbitLength ρ (componentRoots (rootCharHom a) i)])) := by
  rintro ⟨hr, hc, hni⟩
  obtain ⟨v, C, hΨ, hrank, hncard⟩ := rckExc_kac_comp hp hp2 hpa i
  have hCeq := kacCount_E8_four C (hrank.symm.trans hr) (hncard.symm.trans hc)
  have hΨ' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E8 rckD4Nodes := by
    rw [hΨ, hCeq, kacE8.rootsOf_eq_parabolicRoots (by decide)]
    congr 2
    ext j
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      Option.some.injEq, Set.mem_setOf_eq, rckD4Nodes]
    revert j
    decide
  have hcomp := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hΨroot : ∀ γ ∈ componentRoots (rootCharHom a) i, IsRoot Tag.E8 γ := fun γ hγ => hγ.1.1
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot Tag.E8).subset hΨroot
  have hρ4 : ∀ γ, IsRoot Tag.E8 γ → ρ (ρ (ρ (ρ γ))) = γ := by
    intro γ hγ
    rw [hsq γ hγ, hneg γ, hneg (ρ γ), hsq γ hγ, neg_neg]
  rcases rck_comp_dichotomy hform hstab i with hst | hdis
  · have hs : componentOrbitLength ρ (componentRoots (rootCharHom a) i) = 1 :=
      rck_orbitLength_eq_one hfin hst
    apply hni
    rw [hs]
    obtain ⟨w, hw, hwγ⟩ := hΨ' ▸ hneg4 v
    refine ⟨w, hΨ' ▸ hw, fun γ hγ => ?_⟩
    have h2 : (ρ : (Fin Tag.E8.rank → ℤ) → _)^[2 * 1] γ = -γ := hsq γ (hΨroot γ hγ)
    rw [h2]
    exact hwγ γ (hΨ' ▸ hγ)
  · have hne : (componentRoots (rootCharHom a) i).Nonempty := by
      rw [← Set.ncard_pos hfin, hc]
      norm_num
    have hset : (ρ : (Fin Tag.E8.rank → ℤ) → _)^[2] '' componentRoots (rootCharHom a) i =
        componentRoots (rootCharHom a) i := by
      ext δ
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        have h2 : (ρ : (Fin Tag.E8.rank → ℤ) → _)^[2] γ = -γ := hsq γ (hΨroot γ hγ)
        rw [h2]
        exact hcomp.neg_mem γ hγ
      · intro hδ
        refine ⟨-δ, hcomp.neg_mem δ hδ, ?_⟩
        have hδr := hΨroot δ hδ
        show ρ (ρ (-δ)) = δ
        rw [hneg δ, hneg (ρ δ), hsq δ hδr, neg_neg]
    have hmem : 2 ∈ {s : ℕ | 0 < s ∧ (ρ : (Fin Tag.E8.rank → ℤ) → _)^[s] ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i} := ⟨two_pos, hset⟩
    have hs2 : componentOrbitLength ρ (componentRoots (rootCharHom a) i) = 2 := by
      have hle : componentOrbitLength ρ (componentRoots (rootCharHom a) i) ≤ 2 := Nat.sInf_le hmem
      have hge : componentOrbitLength ρ (componentRoots (rootCharHom a) i) ∈
          {s : ℕ | 0 < s ∧ (ρ : (Fin Tag.E8.rank → ℤ) → _)^[s] ''
            componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i} :=
        Nat.sInf_mem ⟨2, hmem⟩
      have hpos : 0 < componentOrbitLength ρ (componentRoots (rootCharHom a) i) := hge.1
      have hne1 : componentOrbitLength ρ (componentRoots (rootCharHom a) i) ≠ 1 := by
        intro h1
        have h1' : (ρ : (Fin Tag.E8.rank → ℤ) → _)^[1] '' componentRoots (rootCharHom a) i =
            componentRoots (rootCharHom a) i := by
          have := hge.2
          rwa [h1] at this
        obtain ⟨α, hα⟩ := hne
        have : ρ α ∈ componentRoots (rootCharHom a) i := by
          rw [← h1']
          exact ⟨α, hα, rfl⟩
        exact hdis α hα this
      omega
    apply hni
    rw [hs2]
    refine ⟨1, Subgroup.one_mem _, fun γ hγ => ?_⟩
    have h4 : (ρ : (Fin Tag.E8.rank → ℤ) → _)^[2 * 2] γ = γ := hρ4 γ (hΨroot γ hγ)
    rw [h4, one_smul]

theorem rckExc_not_shape_D4
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin Tag.E8.rank → GGLˣ}
    (hpa : rootDiagUnit Tag.E8 a ^ p = 1) {ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    (hroot : ∀ γ, IsRoot Tag.E8 (ρ γ) ↔ IsRoot Tag.E8 γ) (hneg : ∀ γ, ρ (-γ) = -ρ γ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ)
    (hsq : ∀ γ, IsRoot Tag.E8 γ → ρ (ρ γ) = -γ)
    (hstab : ∀ γ ∈ kernelRoots (rootCharHom a), ρ γ ∈ kernelRoots (rootCharHom a))
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24 ∧
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((ρ : (Fin Tag.E8.rank → ℤ) → _)^[2 *
          componentOrbitLength ρ (componentRoots (rootCharHom a) i)])) :=
  rckExc_not_shape_D4_of_neg rck_neg_inner hp hp2 hpa hroot hneg hform hsq hstab i

end CFSG.StandardType.RCKRP
