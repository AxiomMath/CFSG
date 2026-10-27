module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFrame

public section

namespace CFSG.StandardType

namespace ExcE6Plus

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TwE6CorootCore CFSG.StandardType.TableBExcTwoFusion
  CFSG.RankThree.PartOne.KE

theorem exists_frameElt {K : Type} [Field K] [Finite K] [CharP K 2]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∃ g₀ : SL2 (AlgebraicClosure K),
      Matrix.SpecialLinearGroup.map Fr g₀ = g₀ * nSL (1 : (AlgebraicClosure K)ˣ) := by
  let L := AlgebraicClosure K
  have hcard : 2 ≤ Nat.card K := by
    haveI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Nat.succ_le_of_lt Fintype.one_lt_card
  have hroot : ∃ a : L, a ^ Nat.card K - a + 1 = 0 := by
    let p : Polynomial L := Polynomial.X ^ Nat.card K - Polynomial.X + Polynomial.C (1 : L)
    have hdeg : p.natDegree = Nat.card K := by
      dsimp only [p]
      compute_degree!
      · have hq1 : (1 : ℕ) ≠ Nat.card K := by omega
        have hq0 : Nat.card K ≠ 0 := by omega
        simp [hq1, hq0]
      · omega
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
      rw [Polynomial.degree_eq_natDegree (by intro h; rw [h] at hdeg; simp at hdeg; omega), hdeg]
      exact_mod_cast (by omega : Nat.card K ≠ 0))
    exact ⟨a, by simpa [p] using ha⟩
  obtain ⟨a, ha⟩ := hroot
  have ha' : a ^ Nat.card K = a + 1 := by
    have h : a ^ Nat.card K = -(-a + 1) := eq_neg_of_add_eq_zero_left (by
      simpa [sub_eq_add_neg, add_assoc] using ha)
    rw [h, neg_add, neg_neg, CharTwo.neg_eq]
  have hone : (1 : L) + 1 = 0 := by
    rw [one_add_one_eq_two, CharTwo.two_eq_zero]
  have ha'' : (a ^ Nat.card K) ^ Nat.card K = a := by
    have h1 : (a ^ Nat.card K) ^ Nat.card K = Fr (a ^ Nat.card K) := by rw [hFr]
    have h2 : Fr (a ^ Nat.card K) = Fr (a + 1) := by rw [ha']
    have h3 : Fr (a + 1) = Fr a + Fr 1 := map_add Fr a 1
    have h4 : Fr a + Fr 1 = a ^ Nat.card K + 1 := by rw [hFr, map_one]
    have h5 : a ^ Nat.card K + 1 = (a + 1) + 1 := by rw [ha']
    have h6 : (a + 1) + 1 = a := by rw [add_assoc, hone, add_zero]
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))
  let g : SL2 L := ⟨!![a, a ^ Nat.card K; 1, 1], by
    have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
    rw [Matrix.det_fin_two_of, ha']
    linear_combination -h2⟩
  refine ⟨g, ?_⟩
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_mul, coe_nSL_one]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hFr, ha'', CharTwo.neg_eq, g]

private theorem ggKGE6a_list_map_rootReflection_prod_smul
    (l : List (Fin Tag.E6.rank → ℤ)) (hl : ∀ β ∈ l, IsRoot .E6 β)
    (v : Fin Tag.E6.rank → ℤ) :
    (l.map rootReflection).prod • v = l.foldr (fun β u => u - corootPair β u • β) v := by
  induction l with
  | nil => simp
  | cons β l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul,
      ih fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ),
      rootReflection_smul (hl β List.mem_cons_self), List.foldr_cons]

private theorem ggKGE6a_canonicalRep_list_prod
    (L : Type) [Field L] [CharP L 2] (l : List (WeylGroup .E6)) :
    (l.map (canonicalRep (coxeterSystem .E6) L)).prod =
      canonicalRep (coxeterSystem .E6) L l.prod := by
  induction l with
  | nil => simp [canonicalRep_one]
  | cons a l ih =>
    rw [List.map_cons]
    simp only [List.prod_cons]
    rw [CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo, ih]

private theorem ggKGE6a_frame_foldr_nonpos :
    ∀ α ∈ rootFinset Tag.E6,
      (∀ i, 0 ≤ α i) →
        ∀ i, (List.ofFn fun i : Fin 4 => corootFrameRoot i).foldr
            (fun β u => u - corootPair β u • β) α i ≤ 0 := by
  decide +kernel

theorem exists_longest_canonicalRep
    (L : Type) [Field L] [CharP L 2] :
    ∃ w : WeylGroup .E6, ExcIsLongest .E6 w ∧
      (frameProd L corootFrame (nSL (1 : Lˣ)) : ModGL .E6 L) =
        canonicalRep (coxeterSystem .E6) L w := by
  let f : Fin 4 → (Fin Tag.E6.rank → ℤ) := fun i => corootFrameRoot i
  let w : WeylGroup .E6 := (List.ofFn fun i : Fin 4 => rootReflection (f i)).prod
  refine ⟨w, ?_, ?_⟩
  · intro α hα hpos i
    have hsmul : w • α = (List.ofFn f).foldr (fun β u => u - corootPair β u • β) α := by
      have hw : w = ((List.ofFn f).map rootReflection).prod := by
        dsimp only [w, f]
        rw [List.map_ofFn]
        rfl
      rw [hw]
      exact ggKGE6a_list_map_rootReflection_prod_smul (List.ofFn f)
        (fun β hβ => by
          obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hβ
          exact corootFrame.isRoot j) α
    rw [hsmul]
    exact ggKGE6a_frame_foldr_nonpos α (mem_rootFinset.2 hα) hpos i
  · have hcoe : ((frameProd L corootFrame (nSL 1) : adjointGroup .E6 L) : ModGL .E6 L) =
        (List.ofFn fun i : Fin 4 =>
          canonicalRep (coxeterSystem .E6) L (rootReflection (f i))).prod := by
      rw [coe_frameProd]
      apply congrArg List.prod
      apply congrArg List.ofFn
      funext i
      change rootWeylSL2 .E6 L (corootFrame.root i) 1 =
        canonicalRep (coxeterSystem .E6) L (rootReflection (corootFrame.root i))
      exact CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo
        (corootFrame.isRoot i)
    rw [hcoe]
    have hmap : (List.ofFn fun i : Fin 4 =>
          canonicalRep (coxeterSystem .E6) L (rootReflection (f i))) =
        (List.ofFn fun i : Fin 4 => rootReflection (f i)).map
          (canonicalRep (coxeterSystem .E6) L) := by
      rw [List.map_ofFn]
      rfl
    rw [hmap]
    exact ggKGE6a_canonicalRep_list_prod L (List.ofFn fun i : Fin 4 => rootReflection (f i))

end ExcE6Plus

end CFSG.StandardType

end
