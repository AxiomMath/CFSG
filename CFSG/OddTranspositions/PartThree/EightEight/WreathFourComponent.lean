module

public import CFSG.OddTranspositions.PartThree.EightEight.WreathFourBlocks
public import CFSG.Timmesfeld.Bridge.Asc72Defs
import CFSG.OddTranspositions.PartThree.EightEight.WreathNatural
import CFSG.OddTranspositions.PartThree.EightEight.WreathSwapClass
import CFSG.OddTranspositions.PartThree.EightEight.WreathGen
import CFSG.OddTranspositions.PartThree.EightEight.ComponentPerp

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem mem_swapSet_of_mem_Dalpha_w4c (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f : ℕ} (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f 4)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {x : Halpha D hC.alpha}
    (hx : (x : G) ∈ β) :
    φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x) ∈
      WreathEndgame.swapSet f 4 :=
  mem_swapSet_of_mem_DstarH hC hns hf (Or.inr rfl) φ ((mem_DstarH_iff hC).mpr ⟨β, hβ, hx⟩)

private theorem mem_Dalpha_of_disjoint_right_w4c (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f : ℕ} (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f 4)
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha)
    {β β' : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hβ' : β' ∈ Dalpha D hC.alpha)
    {x y : Halpha D hC.alpha} (hx : (x : G) ∈ β) (hy : (y : G) ∈ β')
    (hdisj : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x)).right.Disjoint
      (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y)).right) :
    β' ∈ Dalpha D β := by
  have hxS := mem_swapSet_of_mem_Dalpha_w4c hC hns hf φ hβ hx
  have hyS := mem_swapSet_of_mem_Dalpha_w4c hC hns hf φ hβ' hy
  have hcomm : Commute
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y) :=
    (commute_map_iff (f := φ) φ.injective).1
      (WreathEndgame.commute_of_disjoint_right hxS hyS hdisj)
  have hne : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y := by
    obtain ⟨r, s, hrs, hxr, -⟩ := hxS
    obtain ⟨u, v, huv, hyr, -⟩ := hyS
    rw [hxr, hyr] at hdisj
    intro heq
    have hEq : Equiv.swap r s = Equiv.swap u v := by
      rw [← hxr, ← hyr]
      exact congrArg SemidirectProduct.right (congrArg φ heq)
    rw [← hEq] at hdisj
    exact hrs (Equiv.swap_eq_one_iff.1 (Equiv.Perm.disjoint_refl_iff.1 hdisj))
  exact (hB.mem_Dalpha_iff_mk hC.setup.normal hC.setup.oddT hC.isBlock_alpha hA
    hβ hβ' hx hy).2 ⟨hne, hcomm⟩

theorem reflTransGen_of_right_eq_swap (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f : ℕ} (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f 4)
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    {δ : Set G} (hδ : δ ∈ Dalpha D hC.alpha) {a : Halpha D hC.alpha} (ha : (a : G) ∈ δ)
    (hat : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right =
      Equiv.swap i j)
    {ρ : Set G} (hρ : ρ ∈ Dalpha D hC.alpha) {p : Halpha D hC.alpha} (hp : (p : G) ∈ ρ)
    (hpt : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p)).right =
        Equiv.swap i j ∨
      (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p)).right =
        Equiv.swap k l) :
    Relation.ReflTransGen (DalphaAdj D hC.alpha) δ ρ := by
  have hdisj : (Equiv.swap i j).Disjoint (Equiv.swap k l) :=
    (WreathEndgame.swapDisjoint_iff hij hkl).2 ⟨hik, hil, hjk, hjl⟩
  have hdisj' : (Equiv.swap k l).Disjoint (Equiv.swap i j) :=
    (WreathEndgame.swapDisjoint_iff hkl hij).2 ⟨hik.symm, hjk.symm, hil.symm, hjl.symm⟩
  rcases hpt with hpt | hpt
  · obtain ⟨d, hd, hdeq⟩ := exists_mem_DstarH_eq_of_mem_swapSet hC hns hf (Or.inr rfl) φ
      (WreathEndgame.inr_swap_mem_swapSet hkl)
    have hzbar_mem : φ.symm (SemidirectProduct.inr (Equiv.swap k l) : L2Wreath f 4) ∈
        imageClass hC :=
      ⟨d, hd, (φ.symm_apply_eq.2 hdeq.symm).symm⟩
    obtain ⟨ζ, hζ, z, hz, hzmk⟩ := exists_mem_Dalpha_mk_eq hC hzbar_mem
    have hzr : (φ (QuotientGroup.mk'
        (CFSG.solvableRadical (Halpha D hC.alpha)) z)).right = Equiv.swap k l := by
      rw [hzmk, MulEquiv.apply_symm_apply, SemidirectProduct.right_inr]
    have hζδ : ζ ∈ Dalpha D δ :=
      mem_Dalpha_of_disjoint_right_w4c hC hns hf φ hB hA hδ hζ ha hz (by
        rw [hat, hzr]
        exact hdisj)
    have hρζ : ρ ∈ Dalpha D ζ :=
      mem_Dalpha_of_disjoint_right_w4c hC hns hf φ hB hA hζ hρ hz hp (by
        rw [hzr, hpt]
        exact hdisj')
    exact (Relation.ReflTransGen.single ⟨hζ, hζδ⟩).tail ⟨hρ, hρζ⟩
  · have hρδ : ρ ∈ Dalpha D δ :=
      mem_Dalpha_of_disjoint_right_w4c hC hns hf φ hB hA hδ hρ ha hp (by
        rw [hat, hpt]
        exact hdisj)
    exact Relation.ReflTransGen.single ⟨hρ, hρδ⟩

private theorem mem_normalizer_gen_w4c (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f : ℕ} (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f 4)
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha) {δ : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) {d : G}
    (hcomm : ∀ ρ, Relation.ReflTransGen (DalphaAdj D hC.alpha) δ ρ → ∀ x ∈ ρ, Commute d x)
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) {a : Halpha D hC.alpha} (ha : (a : G) ∈ δ)
    (hat : (φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) a)).right =
      Equiv.swap i j) :
    d ∈ Subgroup.normalizer ((Subgroup.closure {p : G | ∃ hp : p ∈ Halpha D hC.alpha,
      p ∈ DalphaStar D hC.alpha ∧
        φ (QuotientGroup.mk ⟨p, hp⟩) ∈
          (WreathEndgame.sameSwaps f 4 (Equiv.swap i j) ∪
            WreathEndgame.sameSwaps f 4 (Equiv.swap k l))} : Subgroup G) : Set G) := by
  have hcent : d ∈ Subgroup.centralizer
      (Subgroup.closure {p : G | ∃ hp : p ∈ Halpha D hC.alpha,
        p ∈ DalphaStar D hC.alpha ∧
          φ (QuotientGroup.mk ⟨p, hp⟩) ∈
            (WreathEndgame.sameSwaps f 4 (Equiv.swap i j) ∪
              WreathEndgame.sameSwaps f 4 (Equiv.swap k l))} : Subgroup G) := by
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro p hp
    obtain ⟨hpα, hpD, hpE⟩ := hp
    obtain ⟨ρ, hρ, hpρ⟩ := hpD
    have hpt : (φ (QuotientGroup.mk'
          (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨p, hpα⟩)).right = Equiv.swap i j ∨
        (φ (QuotientGroup.mk'
          (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨p, hpα⟩)).right = Equiv.swap k l := by
      rcases hpE with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    exact (hcomm ρ (reflTransGen_of_right_eq_swap hC hns hf φ hB hA hij hik hil hjk hjl hkl
      hδ ha hat hρ hpρ hpt) p hpρ).symm
  exact Subgroup.centralizer_le_normalizer _ hcent

theorem mem_union_DalphaStar_of_commute_reflTransGen (hC : HypothesisC D)
    (hZ : Subgroup.center G = ⊥) (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f : ℕ}
    (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f 4)
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha) {δ : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) {d : G} (hd : d ∈ D)
    (hcomm : ∀ ρ, Relation.ReflTransGen (DalphaAdj D hC.alpha) δ ρ → ∀ x ∈ ρ, Commute d x) :
    d ∈ hC.alpha ∪ DalphaStar D hC.alpha := by
  obtain ⟨a₀, ha₀⟩ : δ.Nonempty := by
    obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hδ.1
    rw [hg]
    exact hC.isBlock_alpha.nonempty.image _
  let a : Halpha D hC.alpha := ⟨a₀, Subgroup.subset_closure ⟨δ, hδ, ha₀⟩⟩
  have ha : (a : G) ∈ δ := ha₀
  obtain ⟨i, j, hij, har, -⟩ := mem_swapSet_of_mem_Dalpha_w4c hC hns hf φ hδ ha
  obtain ⟨ε, hε⟩ := WreathEndgame.exists_embedding_range (k := 2) (i := i) (j := j) hij
  let k : Fin 4 := ε 0
  let l : Fin 4 := ε 1
  have hk : k ∈ Set.range ε := ⟨0, rfl⟩
  have hl : l ∈ Set.range ε := ⟨1, rfl⟩
  have hkk := (hε k).1 hk
  have hll := (hε l).1 hl
  have hik : i ≠ k := hkk.1.symm
  have hil : i ≠ l := hll.1.symm
  have hjk : j ≠ k := hkk.2.symm
  have hjl : j ≠ l := hll.2.symm
  have hkl : k ≠ l := fun h => absurd (ε.injective h) (by decide)
  have hnormal := mem_normalizer_gen_w4c hC hns hf φ hB hA hδ hcomm
    hij hik hil hjk hjl hkl ha har
  have hEsub : (WreathEndgame.sameSwaps f 4 (Equiv.swap i j) ∪
      WreathEndgame.sameSwaps f 4 (Equiv.swap k l)) ⊆ φ '' imageClass hC := by
    intro e he
    have heS : e ∈ WreathEndgame.swapSet f 4 := by
      rcases he with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact h
    obtain ⟨d, hd, hdeq⟩ := exists_mem_DstarH_eq_of_mem_swapSet hC hns hf (Or.inr rfl) φ heS
    refine ⟨φ.symm e, ⟨d, hd, (φ.symm_apply_eq.2 hdeq.symm).symm⟩, φ.apply_symm_apply e⟩
  have hbase : (SemidirectProduct.inl.range : Subgroup (L2Wreath f 4)) ≤
      Subgroup.closure (WreathEndgame.sameSwaps f 4 (Equiv.swap i j) ∪
        WreathEndgame.sameSwaps f 4 (Equiv.swap k l)) :=
    range_inl_le_closure_sameSwaps_union hf hij hik hil hjk hjl hkl
  exact mem_union_DalphaStar_of_mem_normalizer hC hZ hf (by norm_num) (by norm_num) φ
    hEsub hbase hd hnormal

end CFSG.OddTranspositions.PartThree.EightEight
