module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec55Defs
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec55W
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec52
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42Q
import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Z
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Sec53
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_12_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_13_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_14_d
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_e
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_6_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.theorem_11_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_5_c_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_3_a_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_5_b
import CFSG.LinearAlgebra.LinearGroups.LinearTwo
import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitType
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
import CFSG.Sporadic.Th.F2Spec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open P51 (V e)
open S36 (hypF hypU hypA dot)

namespace S55

def gA : Fin 3 → (Fin 3 → ZMod 3) → (Fin 3 → ZMod 3) :=
  ![fun x => ![-x 0, x 1, x 2], fun x => ![x 1, x 0, x 2],
    fun x => x + (x 0 + x 1 + 2 * x 2) • ![1, 1, 1]]

def actA (w : List (Fin 3)) (x : Fin 3 → ZMod 3) : Fin 3 → ZMod 3 :=
  w.foldr (fun i u => gA i u) x

set_option maxRecDepth 100000 in
theorem gf_emb : ∀ i : Fin 3, ∀ x : Fin 3 → ZMod 3, S52.gf i (S52.emb x) = S52.emb (gA i x) := by
  decide +kernel

theorem act_emb (w : List (Fin 3)) (x : Fin 3 → ZMod 3) :
    S52.act w (S52.emb x) = S52.emb (actA w x) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change S52.gf i (S52.act w (S52.emb x)) = S52.emb (gA i (actA w x))
    rw [ih, gf_emb]

theorem emb_add (x y : Fin 3 → ZMod 3) : S52.emb (x + y) = S52.emb x + S52.emb y := by
  ext j; fin_cases j <;> rfl

theorem emb_inj : Function.Injective S52.emb := fun x y h => by
  ext j; fin_cases j
  exacts [congrFun h 0, congrFun h 1, congrFun h 2]

def rep : Fin 13 → Fin 13 := ![1, 1, 2, 2, 2, 8, 8, 8, 8, 1, 1, 1, 1]

def wd : Fin 13 → List (Fin 3) :=
  ![[1], [], [], [2], [0, 2], [0, 1], [1], [1, 0, 1], [], [0, 2], [0, 2, 1], [2, 1], [2]]

def Carries (w : List (Fin 3)) (r i : Fin 13) : Prop :=
  dot (hypF i) (actA w (hypU r)) = 0 ∧ dot (hypF i) (actA w (hypA r)) = 0

instance (w : List (Fin 3)) (r i : Fin 13) : Decidable (Carries w r i) := by
  unfold Carries; infer_instance

set_option maxRecDepth 100000 in
theorem wd_carries : ∀ i : Fin 13, Carries (wd i) (rep i) i := by decide +kernel

theorem prod_rep (d : Fin 13 → ℕ) : ∏ i, d (rep i) = d 1 ^ 6 * d 2 ^ 3 * d 8 ^ 4 := by
  simp [Fin.prod_univ_succ, rep]
  ring

set_option maxRecDepth 100000 in
theorem span_reps :
    (∀ z, dot (hypF 1) z = 0 → ∃ c d : ZMod 3, z = c • ![1, 0, 0] + d • ![0, 0, 1]) ∧
    (∀ z, dot (hypF 2) z = 0 → ∃ c d : ZMod 3, z = c • ![1, 0, 0] + d • ![0, 1, 0]) ∧
    (∀ z, dot (hypF 7) z = 0 → ∃ c d : ZMod 3, z = c • ![1, 0, 0] + d • ![0, 2, 1]) ∧
    (∀ z, dot (hypF 8) z = 0 → ∃ c d : ZMod 3, z = c • ![1, 0, 0] + d • ![0, 1, 1]) := by
  decide +kernel

end S55

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

section Coord

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

abbrev FF81Sec5.εA (x : Fin 3 → ZMod 3) : G := h5.ε (S52.emb x)

theorem FF81Sec5.coordA : S55.Coord h5.εA (A₁sub b b₁ b₂ b₃) where
  add x y := by simp only [FF81Sec5.εA]; rw [S55.emb_add, h5.ε_add]
  inj x y hxy := S55.emb_inj (h5.ε_inj hxy)
  mem x := h5.mem_A₁_of rfl
  surj y hy := by
    obtain ⟨v, hv, rfl⟩ := h5.coord_of_mem_A₁ hy
    refine ⟨![v 0, v 1, v 2], ?_⟩
    simp only [FF81Sec5.εA]
    congr 1
    ext j; fin_cases j <;> simp [S52.emb, hv]

theorem FF81Sec5.εA_b : h5.εA ![1, 0, 0] = b := by
  rw [FF81Sec5.εA, show S52.emb ![1, 0, 0] = e 0 by decide, h5.ε_e0]

theorem FF81Sec5.εA_b₁ : h5.εA ![0, 1, 0] = b₁ := by
  rw [FF81Sec5.εA, show S52.emb ![0, 1, 0] = e 1 by decide, h5.ε_e1]

theorem FF81Sec5.εA_u₃ : h5.εA ![0, 0, 1] = b₂ * b₃ := by
  rw [FF81Sec5.εA, show S52.emb ![0, 0, 1] = ![0, 0, 1, 1] by decide, h5.ε_u₃]

theorem FF81Sec5.εA_x₂ : h5.εA ![0, 1, 1] = b₁ * (b₂ * b₃) := by
  rw [show (![0, 1, 1] : Fin 3 → ZMod 3) = ![0, 1, 0] + ![0, 0, 1] by decide, h5.coordA.add,
    h5.εA_b₁, h5.εA_u₃]

theorem FF81Sec5.εA_x₃ : h5.εA ![0, 2, 1] = b₁⁻¹ * (b₂ * b₃) := by
  rw [show (![0, 2, 1] : Fin 3 → ZMod 3) = -![0, 1, 0] + ![0, 0, 1] by decide, h5.coordA.add,
    h5.coordA.neg, h5.εA_b₁, h5.εA_u₃]

theorem FF81Sec5.A₁_le_cen_s₀ : A₁sub b b₁ b₂ b₃ ≤ Cen s₀ := fun a ha =>
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h5.hs₀A a ha)

theorem FF81Sec5.A₁_le_nor_S : A₁sub b b₁ b₂ b₃ ≤ Nor (Op 2 (Cen s₀)) := fun a ha =>
  Subgroup.mem_normalizer_fintype fun _ hu => op_two_conj (h5.A₁_le_cen_s₀ ha) hu

end Coord

section Words

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {g : Fin 3 → G}
  (hgH : ∀ i, g i ∈ H₅₂ b b₁ b₂ b₃ s₀) (hg : ∀ i v, g i * h5.ε v * (g i)⁻¹ = h5.ε (S52.gf i v))

def S55.wel (g : Fin 3 → G) (w : List (Fin 3)) : G := (w.map g).prod

include hgH in
theorem S55.wel_mem (w : List (Fin 3)) : S55.wel g w ∈ H₅₂ b b₁ b₂ b₃ s₀ :=
  Subgroup.list_prod_mem _ (l := w.map g) fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; exact hgH i

include hgH in
theorem S55.wel_cen (w : List (Fin 3)) : S55.wel g w ∈ Cen s₀ :=
  Subgroup.mem_centralizer_singleton_iff.mpr (mem_cenS_pair_iff.mp (S55.wel_mem hgH w).1).2

include hg in
theorem FF81Sec5.wel_εA (w : List (Fin 3)) (x : Fin 3 → ZMod 3) :
    S55.wel g w * h5.εA x * (S55.wel g w)⁻¹ = h5.εA (S55.actA w x) := by
  rw [FF81Sec5.εA, S55.wel, h5.word_conj hg, S55.act_emb]

include hg in
theorem FF81Sec5.conjBy_hyp {w : List (Fin 3)} {r i : Fin 13} (hw : S55.Carries w r i) :
    conjBy (S55.wel g w) (S55.hyp h5.εA r) = S55.hyp h5.εA i := by
  have hle : conjBy (S55.wel g w) (S55.hyp h5.εA r) ≤ S55.hyp h5.εA i := by
    rw [S55.hyp, Q42.conjBy_closure_pair, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · rw [h5.wel_εA hg]; exact (h5.coordA.mem_hyp i _).2 hw.1
    · rw [h5.wel_εA hg]; exact (h5.coordA.mem_hyp i _).2 hw.2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_conjBy, h5.coordA.card_hyp, h5.coordA.card_hyp]

abbrev FF81Sec5.W (i : Fin 13) : Subgroup G := Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA i)

include hgH hg in
theorem FF81Sec5.conjBy_W {w : List (Fin 3)} {r i : Fin 13} (hw : S55.Carries w r i) :
    conjBy (S55.wel g w) (h5.W r) = h5.W i := by
  rw [FF81Sec5.W, conjBy, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, ← conjBy, ← conjBy,
    conjBy_op_two (S55.wel_cen hgH w), ← conjBy_cenS, h5.conjBy_hyp hg hw]

include hgH hg in
theorem FF81Sec5.card_W {w : List (Fin 3)} {r i : Fin 13} (hw : S55.Carries w r i) :
    Nat.card (h5.W i) = Nat.card (h5.W r) := by
  rw [← h5.conjBy_W hgH hg hw, card_conjBy]

include hgH hg in
theorem FF81Sec5.W_le_cenS {w : List (Fin 3)} {r₁ r₂ i j : Fin 13} (h₁ : S55.Carries w r₁ i)
    (h₂ : S55.Carries w r₂ j) (hc : h5.W r₁ ≤ CenS (h5.W r₂)) : h5.W i ≤ CenS (h5.W j) := by
  rw [← h5.conjBy_W hgH hg h₁, ← h5.conjBy_W hgH hg h₂, conjBy_cenS]
  exact Subgroup.map_mono hc

end Words

section Reps

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

theorem FF81Sec5.W_eq {i : Fin 13} {p q : Fin 3 → ZMod 3} (hp : dot (hypF i) p = 0)
    (hq : dot (hypF i) q = 0)
    (hspan : ∀ z, dot (hypF i) z = 0 → ∃ c d : ZMod 3, z = c • p + d • q) :
    h5.W i = Op 2 (Cen s₀) ⊓ Cen (h5.εA p) ⊓ Cen (h5.εA q) := by
  ext y
  simp only [FF81Sec5.W, Subgroup.mem_inf, h5.coordA.cenS_hyp hp hq hspan,
    Subgroup.mem_centralizer_singleton_iff, and_assoc]

theorem FF81Sec5.W₁_eq : h5.W 1 = Op 2 (Cen s₀) ⊓ Cen b ⊓ Cen (b₂ * b₃) := by
  rw [h5.W_eq (by decide) (by decide) S55.span_reps.1, h5.εA_b, h5.εA_u₃]

theorem FF81Sec5.W₂_eq : h5.W 2 = Op 2 (Cen s₀) ⊓ Cen b ⊓ Cen b₁ := by
  rw [h5.W_eq (by decide) (by decide) S55.span_reps.2.1, h5.εA_b, h5.εA_b₁]

theorem FF81Sec5.W₇_eq : h5.W 7 = Op 2 (Cen s₀) ⊓ Cen b ⊓ Cen (b₁⁻¹ * (b₂ * b₃)) := by
  rw [h5.W_eq (by decide) (by decide) S55.span_reps.2.2.1, h5.εA_b, h5.εA_x₃]

theorem FF81Sec5.W₈_eq : h5.W 8 = Op 2 (Cen s₀) ⊓ Cen b ⊓ Cen (b₁ * (b₂ * b₃)) := by
  rw [h5.W_eq (by decide) (by decide) S55.span_reps.2.2.2, h5.εA_b, h5.εA_x₂]

theorem FF81Sec5.R_hyp :
    Op 2 (Cen s₀) ⊓ Cen b ≤ L ⊓ Cen s₀ ∧ IsPGroup 2 ↥(Op 2 (Cen s₀) ⊓ Cen b) ∧
      L ⊓ Cen s₀ ≤ Nor (Op 2 (Cen s₀) ⊓ Cen b) ∧ s₀ ∈ Op 2 (Cen s₀) ⊓ Cen b := by
  have hB := h5.basis
  have hp : IsPGroup 2 ↥(Op 2 (Cen s₀) ⊓ Cen b) := (op_two_isPGroup s₀).to_le inf_le_left
  refine ⟨fun y hy => ⟨hB.le_of_isPGroup inf_le_right hp hy, op_two_le s₀ hy.1⟩, hp,
    fun l hl => Subgroup.mem_normalizer_fintype fun y hy => ⟨op_two_conj hl.2 hy.1, ?_⟩,
    ⟨mem_op_two_self h5.hs₀, ?_⟩⟩
  · exact (Cen b).mul_mem ((Cen b).mul_mem (hB.hyp.hLC hl.1) hy.2) ((Cen b).inv_mem (hB.hyp.hLC hl.1))
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp h5.hs₀A b (Subgroup.subset_closure (by simp))).symm

theorem FF81Sec5.s₀_b₁ : s₀ * b₁ = b₁ * s₀ :=
  (Subgroup.mem_centralizer_iff.mp h5.hs₀A b₁ (Subgroup.subset_closure (by simp))).symm

theorem FF81Sec5.s₀_u₃ : s₀ * (b₂ * b₃) = b₂ * b₃ * s₀ :=
  (Subgroup.mem_centralizer_iff.mp h5.hs₀A (b₂ * b₃) (Subgroup.subset_closure (by simp))).symm

end Reps

theorem card_eq_two_of_le {K : Subgroup G} {s : G} (hs : orderOf s = 2) (hsK : s ∈ K)
    (h : ∀ y ∈ K, y = 1 ∨ y = s) : Nat.card K = 2 := by
  have hK : K = Subgroup.zpowers s := by
    refine le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.mpr hsK)
    rcases h y hy with rfl | rfl
    exacts [Subgroup.one_mem _, Subgroup.mem_zpowers _]
  rw [hK, Nat.card_zpowers, hs]

theorem eq_one_or_of_card_two {K : Subgroup G} {s : G} (hs : orderOf s = 2) (hsK : s ∈ K)
    (hK : Nat.card K = 2) {y : G} (hy : y ∈ K) : y = 1 ∨ y = s := by
  have hle : Subgroup.zpowers s ≤ K := Subgroup.zpowers_le.mpr hsK
  have heq : Subgroup.zpowers s = K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hK, Nat.card_zpowers, hs])
  rw [← heq] at hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hs]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [Nat.cast_ofNat, h, zpow_zero]
  · right; rw [Nat.cast_ofNat, h, zpow_one]

section Order

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

theorem FF81Sec5.s₀_mem_S_cenS : s₀ ∈ Op 2 (Cen s₀) ⊓ CenS (A₁sub b b₁ b₂ b₃) :=
  ⟨mem_op_two_self h5.hs₀, h5.hs₀A⟩

theorem FF81Sec5.s₀_mem_W (i : Fin 13) : s₀ ∈ h5.W i :=
  ⟨mem_op_two_self h5.hs₀, Subgroup.centralizer_le (S55.hyp_le h5.coordA i) h5.hs₀A⟩

theorem FF81Sec5.eq_one_of_mem_B_S {z : G} (hzB : z ∈ B) (hzS : z ∈ Op 2 (Cen s₀)) : z = 1 := by
  obtain ⟨k, hk⟩ := op_two_isPGroup s₀ ⟨z, hzS⟩
  have hk' : z ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact eq_one_of_pow_two_of_odd hk' (orderOf_dvd_of_pow_eq_one (h5.basis.B_cube hzB))
    (by decide)

theorem FF81Sec5.mem_S_cenS_A₁ (hKF : KF_Sp6Levi) {y : G}
    (hy : y ∈ Op 2 (Cen s₀) ⊓ CenS (A₁sub b b₁ b₂ b₃)) : y = 1 ∨ y = s₀ := by
  obtain ⟨z, hzB, rfl | rfl⟩ := FF81Sec5.cenS_A₁ hKF h5 hy.2
  · exact Or.inl (h5.eq_one_of_mem_B_S hzB hy.1)
  · have hzS : z ∈ Op 2 (Cen s₀) := by
      have := (Op 2 (Cen s₀)).mul_mem hy.1 ((Op 2 (Cen s₀)).inv_mem (mem_op_two_self h5.hs₀))
      rwa [mul_inv_cancel_right] at this
    rw [h5.eq_one_of_mem_B_S hzB hzS, one_mul]
    exact Or.inr rfl

theorem FF81Sec5.card_S_cenS_A₁ (hKF : KF_Sp6Levi) :
    Nat.card ↥(Op 2 (Cen s₀) ⊓ CenS (A₁sub b b₁ b₂ b₃)) = 2 :=
  card_eq_two_of_le h5.hs₀ h5.s₀_mem_S_cenS fun _ hy => h5.mem_S_cenS_A₁ hKF hy

theorem FF81Sec5.card_S_mul_prod (hKF : KF_Sp6Levi) :
    Nat.card (Op 2 (Cen s₀)) * 2 ^ 12 = ∏ i : Fin 13, Nat.card (h5.W i) := by
  obtain ⟨hc, hs⟩ := S36.coprime_solvable_of_two (op_two_isPGroup s₀)
  have := S55.card_mul_pow_twelve h5.coordA h5.A₁_le_nor_S hc hs
  rwa [h5.card_S_cenS_A₁ hKF] at this


theorem FF81Sec5.card_S_mul (hKF : KF_Sp6Levi) :
    Nat.card (Op 2 (Cen s₀)) * 2 ^ 12 =
      Nat.card (h5.W 1) ^ 6 * Nat.card (h5.W 2) ^ 3 * Nat.card (h5.W 8) ^ 4 := by
  obtain ⟨g, hgH, hg⟩ := h5.gens hKF
  rw [h5.card_S_mul_prod hKF, ← S55.prod_rep fun r => Nat.card (h5.W r)]
  exact Finset.prod_congr rfl fun i _ => h5.card_W hgH hg (S55.wd_carries i)

end Order

end CFSG.RankThree.PartTwo.Sec21.FF81
