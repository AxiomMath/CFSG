module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedCentre
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Conj

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin CFSG.Quasithin.B45Sz CFSG.Quasithin.B42Sp4
  CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7b
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
variable (k : Type) [Field k] [Algebra K k] [CharP k 2]

theorem natRepS_szIncl_suzukiSElt_zero_col
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : ℕ) (v : K) (j : Fin 4)
    (hj : j = 2 ∨ j = 3) (l : Fin 4) :
    natRepS (F := K) k (2 * c) (szIncl hK (suzukiSElt a K 0 v)) l j = if l = j then 1 else 0 := by
  have hmat : glMat ((szIncl hK (suzukiSElt a K 0 v) : antiSp K) : GL (Fin 4) K) =
      lowU 0 v 0 (suzukiN a 0 v) := by
    rw [szIncl_suzukiSElt, glMat_lowUSp, zero_pow (pow_ne_zero (a + 1) two_ne_zero)]
  have h0 : natRepS (F := K) k 0 (szIncl hK (suzukiSElt a K 0 v)) l j = if l = j then 1 else 0 := by
    rw [natRepS_apply, pow_zero, MulAut.one_apply, Matrix.map_apply, hmat, lowU]
    fin_cases l <;> fin_cases j <;> simp_all [hj]
  have h := natRepS_add_two_mul_pow (F := K) k 0 c (szIncl hK (suzukiSElt a K 0 v))
  rw [zero_add] at h
  rw [h, Matrix.map_apply, h0]
  split_ifs with hlj
  · rw [one_pow]
  · rw [zero_pow (pow_ne_zero c two_ne_zero)]

theorem fixed_Pi_single_suzukiSElt_zero
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {B : Finset ℕ} (hB : B ⊆ szOmega a)
    (f : B → Fin 4) (hf : ∀ i, f i = 2 ∨ f i = 3) (v : K) :
    matRep (szT k hK B) (suzukiSElt a K 0 v) (Pi.single f 1) = Pi.single f 1 := by
  funext x'
  rw [matRep_apply, szT_apply, Matrix.mulVec_single_one, Matrix.col_apply, tensorRepS_apply]
  have hcol : ∀ i : B, natRepS (F := K) k (i : ℕ) (szIncl hK (suzukiSElt a K 0 v)) (x' i) (f i) =
      if x' i = f i then 1 else 0 := by
    intro i
    have hi := hB (Finset.coe_mem i)
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hi
    rw [← hc]
    exact natRepS_szIncl_suzukiSElt_zero_col k hK c v (f i) (hf i) (x' i)
  simp only [hcol]
  by_cases hxf : x' = f
  · subst hxf
    simp
  · have hzero : (Pi.single f (1 : k) : (B → Fin 4) → k) x' = 0 := by
      rw [Pi.single_eq_of_ne hxf]
    rw [hzero]
    obtain ⟨i, hi⟩ : ∃ i, x' i ≠ f i := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hxf (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem fixed_Pi_single_suzukiZ0
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {B : Finset ℕ} (hB : B ⊆ szOmega a)
    (f : B → Fin 4) (hf : ∀ i, f i = 2 ∨ f i = 3) :
    ∀ z ∈ suzukiZ0 a K, matRep (szT k hK B) z (Pi.single f 1) = Pi.single f 1 := by
  intro z hz
  obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).mp hz
  exact fixed_Pi_single_suzukiSElt_zero k hK hB f hf v

private theorem injective_two_three_ite {B : Finset ℕ} :
    Function.Injective (fun g : B → Bool => fun i => if g i then (2 : Fin 4) else 3) := by
  intro g h hgh
  funext i
  have hi := congrFun hgh i
  by_cases hg : g i <;> by_cases hh : h i <;> simp [hg, hh] at hi ⊢

theorem two_pow_card_le_finrank_fixed_suzukiZ0
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {B : Finset ℕ} (hB : B ⊆ szOmega a) :
    2 ^ B.card ≤ Module.finrank k (fixedSub (matRep (szT k hK B)) (suzukiZ0 a K)) := by
  let F : (B → Bool) → (B → Fin 4) := fun g => fun i => if g i then 2 else 3
  let u : (B → Bool) → ((B → Fin 4) → k) := fun g => Pi.single (F g) 1
  have hli : LinearIndependent k u :=
    (Pi.linearIndependent_single_one (B → Fin 4) k).comp F injective_two_three_ite
  have hmem : ∀ g : B → Bool, u g ∈ fixedSub (matRep (szT k hK B)) (suzukiZ0 a K) := by
    intro g
    simp only [mem_fixedSub, SetLike.mem_coe]
    intro z hz
    refine fixed_Pi_single_suzukiZ0 k hK hB (F g) (fun i => ?_) z hz
    by_cases h : g i <;> simp [F, h]
  calc 2 ^ B.card = Fintype.card (B → Bool) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    _ = Module.finrank k (Submodule.span k (Set.range u)) := (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank k (fixedSub (matRep (szT k hK B)) (suzukiZ0 a K)) :=
        Submodule.finrank_mono (Submodule.span_le.mpr (Set.range_subset_iff.mpr hmem))

theorem two_pow_card_le_finrank_fixed_szZ
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {B : Finset ℕ} (hB : B ⊆ szOmega a) :
    2 ^ B.card ≤ Module.finrank k (fixedSub (matRep (szT k hK B)) (szZ a K)) := by
  have hZ := two_pow_card_le_finrank_fixed_suzukiZ0 k hK hB
  let ρ := matRep (szT k hK B)
  have hle : Module.finrank k (fixedSub ρ (suzukiZ0 a K)) ≤
      Module.finrank k (fixedSub ρ (szZ a K)) := by
    rw [show szZ a K = (suzukiZ0 a K).map
      (MulAut.conj (suzukiWElt a K)).toMonoidHom from rfl, fixedSub_map_conj]
    have hinj : Function.Injective
        (ρ (suzukiWElt a K) : ((B → Fin 4) → k) →ₗ[k] ((B → Fin 4) → k)) := by
      intro x y hxy
      have hleft : ∀ z, ρ (suzukiWElt a K)⁻¹ (ρ (suzukiWElt a K) z) = z := by
        intro z
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
      rw [← hleft x, ← hleft y, hxy]
    exact le_of_eq (LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective (ρ (suzukiWElt a K)) hinj
        (fixedSub ρ (suzukiZ0 a K))))
  exact le_trans hZ hle

end CFSG.RankThree.GF2n.Tim81.Sec2
