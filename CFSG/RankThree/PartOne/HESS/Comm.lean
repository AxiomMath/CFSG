module

public import CFSG.RankThree.PartOne.HESS.Classes
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.RankThree.PartOne.HESS

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne.N143
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor rt permSL IsZeta diagSL tSep)
open scoped commutatorElement

@[expose] def tab (ε : Bool) (x y : Fin 3) : Bool := if y = finRotate 3 x then ε else !ε

theorem tab_pos {ε : Bool} {x y : Fin 3} (h : y = finRotate 3 x) : tab ε x y = ε := by
  unfold tab
  simp [h]

theorem tab_neg {ε : Bool} {x y : Fin 3} (h : y ≠ finRotate 3 x) : tab ε x y = !ε := by
  unfold tab
  simp only [h, ↓reduceIte]

theorem comb_table : ∀ (ε : Bool) (a b c d : Fin 3), a ≠ b → c ≠ d → Equiv.swap a b ≠ Equiv.swap c d →
    ((b ≠ c → d ≠ a → tab ε a b ≠ tab ε c d) ∧
     (b = c → tab ε a b = tab ε c d ∧ a ≠ d ∧ tab ε a d ≠ tab ε a b) ∧
     (d = a → tab ε a b = tab ε c d ∧ b ≠ c ∧ tab ε c b ≠ tab ε a b)) := by
  decide

section Comm

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {L : Subgroup G} {f : ℕ}
  {P : Subgroup (MulAut A)} {z : MulAut A} {K : Type} [Field K] [Finite K] [CharP K 2]
  {ρ : SL3 K →* G}

theorem HessSetup.rootSet_nodeOf (hS : HessSetup p A c L f P z) {J : Subgroup G}
    (hJ : J ∈ thetaCompZeroStarE p A) {c' : G} (hL : LineHyp p A c' J f ρ) {i j : Fin 3}
    (hij : i ≠ j) : RootSet A f p (nodeOf A ρ i j) = {rootG ρ hij, rootG ρ hij.symm} := by
  have hkn := hS.kNode_eq hJ (hL.nodeOf_mem_reflectionSet hij) (hL.nodeOf_mem_torusImage i j)
  have hset : RootSet A f p (nodeOf A ρ i j) = RootSetJ A J f (nodeOf A ρ i j) := by
    ext S
    simp only [RootSet, RootSetJ, hkn]
  rw [hset, hL.rootSetJ_eq hij]

theorem HessSetup.mem_rootPairs (hS : HessSetup p A c L f P z) {J : Subgroup G}
    (hJ : J ∈ thetaCompZeroStarE p A) {c' : G} (hL : LineHyp p A c' J f ρ) {i j : Fin 3}
    (hij : i ≠ j) : (nodeOf A ρ i j, rootG ρ hij) ∈ RootPairs p A f :=
  ⟨hL.nodeOf_mem_reflectionSet hij, by rw [hS.rootSet_nodeOf hJ hL hij]; exact Set.mem_insert _ _⟩

theorem HessSetup.mem_rootPairs' (hS : HessSetup p A c L f P z) {J : Subgroup G}
    (hJ : J ∈ thetaCompZeroStarE p A) {c' : G} (hL : LineHyp p A c' J f ρ) {i j : Fin 3}
    (hij : i ≠ j) : (nodeOf A ρ i j, rootG ρ hij.symm) ∈ RootPairs p A f :=
  ⟨hL.nodeOf_mem_reflectionSet hij, by
    rw [hS.rootSet_nodeOf hJ hL hij]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩

theorem HessSetup.ne_bot_of_mem_rootSet (hS : HessSetup p A c L f P z) {t : MulAut A}
    {S : Subgroup G} (hSr : S ∈ RootSet A f p t) : S ≠ ⊥ := by
  intro h
  have h1 := hSr.2.2.1
  rw [h, Subgroup.card_bot] at h1
  have hf : f ≠ 0 := by
    rintro rfl
    have := hS.f_odd
    simp at this
  have : 1 < 2 ^ f := Nat.one_lt_two_pow hf
  omega

omit [Finite K] in
theorem LineHyp.third_node_1 [Finite K] (hL : LineHyp p A c J f ρ) {a b e : Fin 3} (hbe : b ≠ e)
    (hae : a ≠ e) :
    nodeOf A ρ a b * nodeOf A ρ b e * (nodeOf A ρ a b)⁻¹ = nodeOf A ρ a e := by
  have h := hL.piAut_perm_nodeOf (Equiv.swap a b) b e
  rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hae.symm hbe.symm] at h
  exact h

omit [Finite K] in
theorem LineHyp.third_node_2 [Finite K] (hL : LineHyp p A c J f ρ) {a b d : Fin 3} (hda : d ≠ a)
    (hdb : d ≠ b) :
    nodeOf A ρ a b * nodeOf A ρ d a * (nodeOf A ρ a b)⁻¹ = nodeOf A ρ d b := by
  have h := hL.piAut_perm_nodeOf (Equiv.swap a b) d a
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hda hdb] at h
  exact h

theorem HessSetup.pair_rule (hS : HessSetup p A c L f P z) {cls : MulAut A × Subgroup G → Bool}
    (hcls : ClassFnProps p A f P cls) {J : Subgroup G} (hJ : J ∈ thetaCompZeroStarE p A) {c' : G}
    (hL : LineHyp p A c' J f ρ) {a b d e : Fin 3} (hab : a ≠ b) (hde : d ≠ e)
    (hne : Equiv.swap a b ≠ Equiv.swap d e) :
    (cls (nodeOf A ρ a b, rootG ρ hab) ≠ cls (nodeOf A ρ d e, rootG ρ hde) →
      ∀ u ∈ rootG ρ hab, ∀ v ∈ rootG ρ hde, u * v = v * u) ∧
    (cls (nodeOf A ρ a b, rootG ρ hab) = cls (nodeOf A ρ d e, rootG ρ hde) →
      ∃ U ∈ RootSet A f p (nodeOf A ρ a b * nodeOf A ρ d e * (nodeOf A ρ a b)⁻¹),
        cls (nodeOf A ρ a b * nodeOf A ρ d e * (nodeOf A ρ a b)⁻¹, U) ≠
          cls (nodeOf A ρ a b, rootG ρ hab) ∧ ⁅rootG ρ hab, rootG ρ hde⁆ = U ∧ U ≠ ⊥) := by
  classical
  let cl : Fin 3 → Fin 3 → Bool := fun x y =>
    if h : x ≠ y then cls (nodeOf A ρ x y, rootG ρ h) else false
  have hcl : ∀ x y (h : x ≠ y), cl x y = cls (nodeOf A ρ x y, rootG ρ h) := fun x y h => by
    simp [cl, h]
  have hR1 : ∀ x y (h : x ≠ y), cl y x ≠ cl x y := by
    intro x y h
    rw [hcl y x h.symm, hcl x y h, nodeOf_comm y x]
    have hmem := hS.rootSet_nodeOf hJ hL h
    exact hcls.2.1 _ (hL.nodeOf_mem_reflectionSet h) _
      (by rw [hmem]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)) _
      (by rw [hmem]; exact Set.mem_insert _ _) (hL.rootG_ne h).symm
  have hR2 : ∀ x y (h : x ≠ y), cl (finRotate 3 x) (finRotate 3 y) = cl x y := by
    intro x y h
    have hr := hL.rot_mem_Tbar hS
    have h1 := hcls.1 _ hr.1 hr.2 _ (hS.mem_rootPairs hJ hL h)
    have e1 : actPair A (ρ (permSL (finRotate 3))) (nodeOf A ρ x y, rootG ρ h) =
        (nodeOf A ρ (finRotate 3 x) (finRotate 3 y),
          rootG ρ ((finRotate 3).injective.ne h)) := by
      simp only [actPair]
      rw [hL.piAut_perm_nodeOf, conjBy_rootG]
    rw [e1] at h1
    rw [hcl _ _ ((finRotate 3).injective.ne h), hcl x y h]
    exact h1
  have h12 : cl 1 2 = cl 0 1 := hR2 0 1 (by decide)
  have h20 : cl 2 0 = cl 0 1 := (hR2 1 2 (by decide)).trans h12
  have h10 : cl 1 0 = !cl 0 1 := Bool.eq_not.mpr (hR1 0 1 (by decide))
  have h21 : cl 2 1 = !cl 0 1 := by
    have := Bool.eq_not.mpr (hR1 1 2 (by decide))
    rw [this, h12]
  have h02 : cl 0 2 = !cl 0 1 := by
    have := Bool.eq_not.mpr (hR1 2 0 (by decide))
    rw [this, h20]
  have htab : ∀ x y, x ≠ y → cl x y = tab (cl 0 1) x y := by
    intro x y hxy
    have hcases : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨
        (x = 2 ∧ y = 1) ∨ (x = 0 ∧ y = 2) := by
      revert x y
      decide
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [tab_pos (by decide)]
    · rw [tab_pos (by decide), h12]
    · rw [tab_pos (by decide), h20]
    · rw [tab_neg (by decide), h10]
    · rw [tab_neg (by decide), h21]
    · rw [tab_neg (by decide), h02]
  obtain ⟨hN, hC1, hC2⟩ := comb_table (cl 0 1) a b d e hab hde hne
  have hclab := (hcl a b hab).symm
  have hclde := (hcl d e hde).symm
  refine ⟨?_, ?_⟩
  · intro hne' u hu v hv
    by_cases hch : b = d ∨ e = a
    · exfalso
      apply hne'
      rw [hclab, hclde, htab a b hab, htab d e hde]
      rcases hch with hbd | hea
      · exact (hC1 hbd).1
      · exact (hC2 hea).1
    · obtain ⟨hbd, hea⟩ := not_or.1 hch
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      rw [← map_mul, ← map_mul, rootGrp_commute hab hde hbd hea u' hu' v' hv']
  · intro hceq
    rw [hclab, hclde, htab a b hab, htab d e hde] at hceq
    by_cases hbd : b = d
    · subst hbd
      obtain ⟨-, hae, hcae⟩ := hC1 rfl
      have h3 := hL.third_node_1 hde hae
      have hmem : rootG ρ hae ∈ RootSet A f p (nodeOf A ρ a e) := by
        rw [hS.rootSet_nodeOf hJ hL hae]
        exact Set.mem_insert _ _
      refine ⟨rootG ρ hae, ?_, ?_, ?_, hS.ne_bot_of_mem_rootSet hmem⟩
      · rw [h3]
        exact hmem
      · rw [h3, ← hcl a e hae, ← hcl a b hab, htab a e hae, htab a b hab]
        exact hcae
      · unfold rootG
        rw [← Subgroup.map_commutator, commutator_rootGrp_chain hab hde hae]
    · by_cases hea : e = a
      · subst hea
        obtain ⟨-, hbd', hcdb⟩ := hC2 rfl
        have hdb : d ≠ b := fun h => hbd' h.symm
        have h3 := hL.third_node_2 hde hdb
        have hmem : rootG ρ hdb ∈ RootSet A f p (nodeOf A ρ d b) := by
          rw [hS.rootSet_nodeOf hJ hL hdb]
          exact Set.mem_insert _ _
        refine ⟨rootG ρ hdb, ?_, ?_, ?_, hS.ne_bot_of_mem_rootSet hmem⟩
        · rw [h3]
          exact hmem
        · rw [h3, ← hcl d b hdb, ← hcl e b hab, htab d b hdb, htab e b hab]
          exact hcdb
        · unfold rootG
          rw [← Subgroup.map_commutator, Subgroup.commutator_comm,
            commutator_rootGrp_chain hde hab hdb]
      · exact absurd hceq (hN hbd hea)

theorem HessSetup.comm_rule (hS : HessSetup p A c L f P z) {cls : MulAut A × Subgroup G → Bool}
    (hcls : ClassFnProps p A f P cls) {x y : MulAut A} (hx : x ∈ reflectionSet p A)
    (hy : y ∈ reflectionSet p A) (hxy : x ≠ y) {S S' : Subgroup G} (hSr : S ∈ RootSet A f p x)
    (hS'r : S' ∈ RootSet A f p y) :
    (cls (x, S) ≠ cls (y, S') → ∀ a ∈ S, ∀ b ∈ S', a * b = b * a) ∧
    (cls (x, S) = cls (y, S') → ∃ U ∈ RootSet A f p (x * y * x⁻¹),
      cls (x * y * x⁻¹, U) ≠ cls (x, S) ∧ ⁅S, S'⁆ = U ∧ U ≠ ⊥) := by
  obtain ⟨J, hJ, hxJ, hyJ⟩ := hS.pair x hx y hy (hS.ctx.hess x hx y hy hxy)
  obtain ⟨K, hKf, hKfin, hKc, ρ, c', hL⟩ := hS.exists_line_of_mem hJ
  obtain ⟨hx2, hx1⟩ := isAutReflection_sq hx.1
  obtain ⟨hy2, hy1⟩ := isAutReflection_sq hy.1
  obtain ⟨i, j, hij, rfl⟩ := hL.exists_nodeOf_eq hxJ hx2 hx1
  obtain ⟨k, l, hkl, rfl⟩ := hL.exists_nodeOf_eq hyJ hy2 hy1
  have hne : Equiv.swap i j ≠ Equiv.swap k l := fun h => hxy (by simp only [nodeOf, h])
  rw [hS.rootSet_nodeOf hJ hL hij] at hSr
  rw [hS.rootSet_nodeOf hJ hL hkl] at hS'r
  rcases hSr with rfl | hSr
  · rcases hS'r with rfl | hS'r
    · exact hS.pair_rule hcls hJ hL hij hkl hne
    · rw [Set.mem_singleton_iff] at hS'r
      subst hS'r
      rw [nodeOf_comm k l]
      exact hS.pair_rule hcls hJ hL hij hkl.symm (by rwa [Equiv.swap_comm k l] at hne)
  · rw [Set.mem_singleton_iff] at hSr
    subst hSr
    rcases hS'r with rfl | hS'r
    · rw [nodeOf_comm i j]
      exact hS.pair_rule hcls hJ hL hij.symm hkl (by rwa [Equiv.swap_comm i j] at hne)
    · rw [Set.mem_singleton_iff] at hS'r
      subst hS'r
      rw [nodeOf_comm i j, nodeOf_comm k l]
      exact hS.pair_rule hcls hJ hL hij.symm hkl.symm
        (by rwa [Equiv.swap_comm i j, Equiv.swap_comm k l] at hne)

end Comm

end CFSG.RankThree.PartOne.HESS
