module

public import CFSG.Quasithin.Background.F7TwoInvExcBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenWeyl
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenRankOne
public import CFSG.LocalAnalysis.EvenBN.G2.Torus
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.F7TwoDefs
public import CFSG.Quasithin.Background.SmithB42G2FNat
public import CFSG.Quasithin.Background.SmithB42G2FOff
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Certificate8026Base

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F7Two.G2Ev

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.EvenBN.G2.Model

section Roots

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] def rootElt (γ : Fin Tag.G2.rank → ℤ) (x : K) : ↥(adjointGroup .G2 K) :=
  ⟨pinnedX .G2 K γ x, pinnedX_mem_adjointGroup γ x⟩

@[simp] theorem coe_rootElt (γ : Fin Tag.G2.rank → ℤ) (x : K) :
    ((rootElt K γ x : ↥(adjointGroup .G2 K)) : ModGL .G2 K) = pinnedX .G2 K γ x := rfl

theorem rootElt_add (γ : Fin Tag.G2.rank → ℤ) (x y : K) :
    rootElt K γ (x + y) = rootElt K γ x * rootElt K γ y :=
  Subtype.ext (pinnedX_add .G2 K γ x y)

theorem rootElt_zero (γ : Fin Tag.G2.rank → ℤ) : rootElt K γ 0 = 1 :=
  Subtype.ext (pinnedX_zero .G2 K γ)

theorem rootElt_mul_self (γ : Fin Tag.G2.rank → ℤ) (x : K) :
    rootElt K γ x * rootElt K γ x = 1 :=
  Subtype.ext (pinnedX_mul_self γ x)

theorem rootElt_inv (γ : Fin Tag.G2.rank → ℤ) (x : K) : (rootElt K γ x)⁻¹ = rootElt K γ x :=
  inv_eq_of_mul_eq_one_right (rootElt_mul_self γ x)

variable (K) in
@[expose] def n0 : ↥(adjointGroup .G2 K) :=
  ⟨canonicalRep (coxeterSystem .G2) K g2LongestWeyl, canonicalRep_mem_adjointGroup _ K _⟩

@[expose] def IsPos (γ : Fin Tag.G2.rank → ℤ) : Prop :=
  γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c

theorem isPos_g2r : IsPos g2r := Or.inl rfl
theorem isPos_g2a : IsPos g2a := Or.inr (Or.inl rfl)
theorem isPos_g2v : IsPos g2v := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem isPos_g2b : IsPos g2b := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
theorem isPos_g2c : IsPos g2c := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem IsPos.isRoot {γ : Fin Tag.G2.rank → ℤ} (h : IsPos γ) : IsRoot .G2 γ := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [isRoot_g2r, isRoot_g2a, isRoot_g2u, isRoot_g2v, isRoot_g2b, isRoot_g2c]

theorem longest_smul_pos {γ : Fin Tag.G2.rank → ℤ} (h : IsPos γ) : g2LongestWeyl • γ = -γ := by
  have := g2LongestWeyl_smul_neg γ h
  rw [smul_neg] at this
  exact neg_eq_iff_eq_neg.1 this

theorem n0_conj_rootElt {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ) (x : K) :
    n0 K * rootElt K γ x * (n0 K)⁻¹ = rootElt K (g2LongestWeyl • γ) x :=
  Subtype.ext (canonicalRep_conj g2LongestWeyl hγ x)

theorem n0_conj_rootElt_pos {γ : Fin Tag.G2.rank → ℤ} (h : IsPos γ) (x : K) :
    n0 K * rootElt K γ x * (n0 K)⁻¹ = rootElt K (-γ) x := by
  rw [n0_conj_rootElt h.isRoot, longest_smul_pos h]

theorem n0_conj_rootElt_neg {γ : Fin Tag.G2.rank → ℤ} (h : IsPos γ) (x : K) :
    n0 K * rootElt K (-γ) x * (n0 K)⁻¹ = rootElt K γ x := by
  rw [n0_conj_rootElt (IsRoot.neg h.isRoot), g2LongestWeyl_smul_neg γ h]

variable (K) in
@[expose] def HasRoot (H : Subgroup ↥(adjointGroup .G2 K)) (γ : Fin Tag.G2.rank → ℤ) : Prop :=
  ∀ x : K, rootElt K γ x ∈ H

theorem hasRoot_neg {H : Subgroup ↥(adjointGroup .G2 K)} (hn : n0 K ∈ H) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsPos γ) (h : HasRoot K H γ) : HasRoot K H (-γ) := fun x => by
  rw [← n0_conj_rootElt_pos hγ]
  exact H.mul_mem (H.mul_mem hn (h x)) (H.inv_mem hn)

theorem hasRoot_of_neg {H : Subgroup ↥(adjointGroup .G2 K)} (hn : n0 K ∈ H)
    {γ : Fin Tag.G2.rank → ℤ} (hγ : IsPos γ) (h : HasRoot K H (-γ)) : HasRoot K H γ := fun x => by
  rw [← n0_conj_rootElt_neg hγ]
  exact H.mul_mem (H.mul_mem hn (h x)) (H.inv_mem hn)

variable (K) in
@[expose] def wElt (γ : Fin Tag.G2.rank → ℤ) : ↥(adjointGroup .G2 K) :=
  rootElt K γ 1 * rootElt K (-γ) 1 * rootElt K γ 1

theorem wElt_conj_rootElt {γ δ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ) (hδ : IsRoot .G2 δ)
    (x : K) :
    wElt K γ * rootElt K δ x * (wElt K γ)⁻¹ = rootElt K (rootReflection γ • δ) x := by
  refine Subtype.ext ?_
  have h1 := canonicalRep_conj (K := K) (rootReflection γ) hδ x
  rw [canonicalRep_rootReflection hγ] at h1
  exact h1

theorem hasRoot_reflect {H : Subgroup ↥(adjointGroup .G2 K)} {γ δ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot .G2 γ) (hδ : IsRoot .G2 δ) (h1 : HasRoot K H γ) (h2 : HasRoot K H (-γ))
    (h3 : HasRoot K H δ) : HasRoot K H (rootReflection γ • δ) := fun x => by
  rw [← wElt_conj_rootElt hγ hδ]
  have hw : wElt K γ ∈ H := H.mul_mem (H.mul_mem (h1 1) (h2 1)) (h1 1)
  exact H.mul_mem (H.mul_mem hw (h3 x)) (H.inv_mem hw)

theorem eq_top_of_hasRoot {H : Subgroup ↥(adjointGroup .G2 K)} (ha : HasRoot K H g2a)
    (ha' : HasRoot K H (-g2a)) (hr : HasRoot K H g2r) (hr' : HasRoot K H (-g2r)) : H = ⊤ := by
  have hxy : ∀ (i : Fin Tag.G2.rank) (c : K),
      (xUnit .G2 K i c : ModGL .G2 K) ∈ H.map (adjointGroup .G2 K).subtype ∧
        (yUnit .G2 K i c : ModGL .G2 K) ∈ H.map (adjointGroup .G2 K).subtype := by
    intro i c
    have hi : i = g2ia ∨ i = g2ir := by fin_cases i <;> simp [g2ia, g2ir]
    rcases hi with rfl | rfl
    · refine ⟨⟨rootElt K g2a c, ha c, ?_⟩, ⟨rootElt K (-g2a) c, ha' c, ?_⟩⟩
      · rw [Subgroup.coe_subtype, coe_rootElt, g2a_eq_single, pinnedX_single]
      · rw [Subgroup.coe_subtype, coe_rootElt, g2a_eq_single, pinnedX_neg_single]
    · refine ⟨⟨rootElt K g2r c, hr c, ?_⟩, ⟨rootElt K (-g2r) c, hr' c, ?_⟩⟩
      · rw [Subgroup.coe_subtype, coe_rootElt, g2r_eq_single, pinnedX_single]
      · rw [Subgroup.coe_subtype, coe_rootElt, g2r_eq_single, pinnedX_neg_single]
  have hle : adjointGroup .G2 K ≤ H.map (adjointGroup .G2 K).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, c, hg | hg⟩
    · have : g = xUnit .G2 K i c := Units.ext hg
      rw [this]
      exact (hxy i c).1
    · have : g = yUnit .G2 K i c := Units.ext hg
      rw [this]
      exact (hxy i c).2
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨h, hh, hgh⟩ := hle g.2
  have : h = g := Subtype.ext hgh
  rwa [← this]

theorem sl2_mul_pow_three : (uSL (1 : K) * vSL 1) ^ 3 = 1 ∧ uSL (1 : K) * vSL 1 ≠ 1 := by
  have h2 : (1 : K) + 1 = 0 := by
    have := (CharTwo.two_eq_zero (R := K))
    linear_combination this
  have hM : ((uSL (1 : K) * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 1, 1] = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]
  refine ⟨?_, ?_⟩
  · ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hM]
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]
  · intro h
    have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [hM] at this
    simp at this

theorem pinnedX_mul_neg_facts {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β) :
    (pinnedX .G2 K β 1 * pinnedX .G2 K (-β) 1) ^ 3 = 1 ∧
      pinnedX .G2 K β 1 * pinnedX .G2 K (-β) 1 ≠ 1 := by
  obtain ⟨w, j, hwj⟩ := isRoot_iff_exists_smul_single.1 hβ
  obtain ⟨ρ, hu, hv, -, -, -, hinj, -, -⟩ := g2_rank_one (K := K) j
  have h1 := canonicalRep_conj (K := K) w (isRoot_single .G2 j) 1
  have h2 := canonicalRep_conj (K := K) w (IsRoot.neg (isRoot_single .G2 j)) 1
  rw [hwj] at h1
  rw [smul_neg, hwj] at h2
  have e : pinnedX .G2 K β 1 * pinnedX .G2 K (-β) 1 =
      canonicalRep (coxeterSystem .G2) K w * ρ (uSL 1 * vSL 1) *
        (canonicalRep (coxeterSystem .G2) K w)⁻¹ := by
    rw [map_mul, hu, hv, ← pinnedX_single, ← pinnedX_neg_single, ← h1, ← h2]
    group
  obtain ⟨hM3, hM1⟩ := sl2_mul_pow_three (K := K)
  refine ⟨?_, ?_⟩
  · rw [e, conj_pow, ← map_pow, hM3, map_one, mul_one, mul_inv_cancel]
  · rw [e]
    intro h
    apply hM1
    apply hinj
    rw [map_one]
    rwa [mul_inv_eq_one, mul_eq_left] at h

theorem rootElt_mul_neg_facts {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β) :
    (rootElt K β 1 * rootElt K (-β) 1) ^ 3 = 1 ∧ rootElt K β 1 * rootElt K (-β) 1 ≠ 1 := by
  obtain ⟨h3, h1⟩ := pinnedX_mul_neg_facts (K := K) hβ
  refine ⟨Subtype.ext ?_, fun h => h1 (congrArg Subtype.val h)⟩
  simpa using h3

theorem not_isPGroup_two_zpowers_rootElt_mul_neg {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot .G2 β) :
    ¬ IsPGroup 2 ↥(Subgroup.zpowers (rootElt K β 1 * rootElt K (-β) 1)) :=
  not_isPGroup_two_zpowers_of_pow_prime Nat.prime_three (by norm_num)
    (rootElt_mul_neg_facts hβ).1 (rootElt_mul_neg_facts hβ).2

end Roots

end CFSG.Quasithin.F7Two.G2Ev
