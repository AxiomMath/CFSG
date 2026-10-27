module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtis
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusRankNode
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQTrivType
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusNat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private noncomputable def w135c2_omfPFamRep_ringEquiv (hF : Nat.card F = 2) : F ≃+* ZMod 2 :=
  have : Fintype F := Fintype.ofFinite F
  (ZMod.ringEquiv (R := F) (n := 2) (by rw [← Nat.card_eq_fintype_card, hF])).symm

omit [Finite F] [CharP F 2] in
open scoped Matrix in
private theorem w135c2_omfPFamRep_map_mulVec {m : Type} [Fintype m] [DecidableEq m]
    (φ : F ≃+* ZMod 2) (M : Matrix m m F) (w : m → ZMod 2) :
    (RingEquiv.piCongrRight fun _ : m => φ.symm).toAddEquiv (M.map (φ : F →+* ZMod 2) *ᵥ w) =
      M *ᵥ (RingEquiv.piCongrRight fun _ : m => φ.symm).toAddEquiv w := by
  funext j
  change (φ.symm : ZMod 2 →+* F) (((M.map (φ : F →+* ZMod 2)) *ᵥ w) j) =
    (M *ᵥ (RingEquiv.piCongrRight fun _ : m => φ.symm).toAddEquiv w) j
  rw [RingHom.map_mulVec]
  have hm : (M.map (φ : F →+* ZMod 2)).map (φ.symm : ZMod 2 →+* F) = M := by
    ext k l
    simp
  have hw : ((φ.symm : ZMod 2 →+* F) ∘ w) =
      (RingEquiv.piCongrRight fun _ : m => φ.symm).toAddEquiv w := by
    funext k
    simp
  rw [hm, hw]

theorem omPlus_two_natural_of_isCurtisType (hF : Nat.card F = 2) {n : ℕ} (hn : 3 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ) {y₀ : V}
    {χ : spinGroup (quadPlus n F) → ZMod 2}
    (ht : (omPlusCurtisDatum n F hn).IsCurtisType ρ y₀ χ (fun s => if s.val = 0 then 1 else 0)) :
    ∃ β : V ≃+ (Fin n ⊕ Fin n → F),
      ∀ (g : spinGroup (quadPlus n F)) (v : V), β (ρ g v) = spinAction (quadPlus n F) g (β v) := by
  have hχ : χ 1 = 1 := ht.chi_one
  let φ : F ≃+* ZMod 2 := w135c2_omfPFamRep_ringEquiv hF
  obtain ⟨β', hβ⟩ := (omPlusCurtisDatum n F hn).iso_of_isCurtisType hρ
    (isSimpleRep_omPlusNatRep hn φ) ht
    (isCurtisType_omPlus_two_natural (F := F) (k := ZMod 2) hF hn (φ : F →+* ZMod 2) hχ)
  let c : (Fin n ⊕ Fin n → ZMod 2) ≃+ (Fin n ⊕ Fin n → F) :=
    (RingEquiv.piCongrRight fun _ : Fin n ⊕ Fin n => φ.symm).toAddEquiv
  refine ⟨β'.toAddEquiv.trans c, ?_⟩
  intro g v
  change c (β' (ρ g v)) = spinAction (quadPlus n F) g (c (β' v))
  dsimp only [c]
  rw [← spinMatrix_mulVec (quadPlus n F) g]
  rw [← w135c2_omfPFamRep_map_mulVec (φ := φ) (M := spinMatrix (quadPlus n F) g) (w := β' v)]
  congr 1
  rw [← omPlusNat_rep_apply (φ := (φ : F →+* ZMod 2)) (g := g) (v := β' v)]
  exact hβ g v

theorem omPlus_two_natural_of_not_separating (hF : Nat.card F = 2) {n : ℕ}
    (hn3 : 3 ≤ n) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    {y : spinGroup (quadPlus n F)} (hρy : ρ y ≠ 1) {y₀ : V}
    {χ : spinGroup (quadPlus n F) → ZMod 2} {μ : Fin n → ZMod 2}
    (ht : (omPlusCurtisDatum n F hn3).IsCurtisType ρ y₀ χ μ)
    (hsep : ¬ ∃ j : Fin n, j.val ≠ 0 ∧ μ j = 1) :
    ∃ β : V ≃+ (Fin n ⊕ Fin n → F),
      ∀ (g : spinGroup (quadPlus n F)) (v : V), β (ρ g v) = spinAction (quadPlus n F) g (β v) := by
  have : NeZero n := ⟨by omega⟩
  let D := omPlusCurtisDatum n F hn3
  have hχ : χ 1 = 1 := ht.chi_one
  have hμ01 : ∀ s : Fin n, μ s = 0 ∨ μ s = 1 := fun s =>
    (ht.mu_eq s).imp id (fun h => by rw [h]; exact omPlusCurtisDatum_two_d'Scalar hF hn3 hχ s)
  have hμz : ∀ s : Fin n, s.val ≠ 0 → μ s = 0 := fun s hs =>
    (hμ01 s).elim id (fun h1 => absurd ⟨s, hs, h1⟩ hsep)
  have hμ0 : μ 0 = 1 := by
    by_contra hne
    have hμ0z : μ 0 = 0 := (hμ01 0).elim id (fun h1 => absurd h1 hne)
    have hμzero : μ = 0 := by
      funext s
      by_cases hs : s.val = 0
      · obtain rfl : s = 0 := Fin.ext hs
        exact hμ0z
      · exact hμz s hs
    have ht0 : D.IsCurtisType ρ y₀ χ 0 := by
      rw [hμzero] at ht
      exact ht
    have hχH : ∀ h ∈ D.H, χ h = 1 := by
      intro h hh
      rw [show D.H = ⊥ from omPlusCurtisDatum_two_H hF hn3, Subgroup.mem_bot] at hh
      rw [hh, hχ]
    exact hρy (omq_rep_eq_one_of_isCurtisType_zero D hρ ht0 hχH y)
  have hμeq : μ = fun s : Fin n => if s.val = 0 then 1 else 0 := by
    funext s
    by_cases hs : s.val = 0
    · obtain rfl : s = 0 := Fin.ext hs
      simp [hμ0]
    · rw [hμz s hs, if_neg hs]
  rw [hμeq] at ht
  exact omPlus_two_natural_of_isCurtisType hF hn3 hρ ht

theorem omPlus_two_natural_or_four_le (hF : Nat.card F = 2) {n : ℕ} (hn5 : 5 ≤ n) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    {y : spinGroup (quadPlus n F)} (hy : y * y = 1) (hρy : ρ y ≠ 1) :
    (∃ β : V ≃+ (Fin n ⊕ Fin n → F),
      ∀ (g : spinGroup (quadPlus n F)) (v : V), β (ρ g v) = spinAction (quadPlus n F) g (β v)) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD n)).Group :=
    CFSG.LieType.RootSystem.finite_group (isFiniteType_cartanD n)
  let D := omPlusCurtisDatum n F hn3
  have hsplit : SplitOver (ZMod 2) D.H := omPlusCurtisDatum_two_splitOver (k := ZMod 2) hF hn3
  obtain ⟨y₀, χ, μ, ht⟩ := D.exists_isCurtisType hsplit hρ
  have hχ : χ 1 = 1 := ht.chi_one
  by_cases hsep : ∃ j : Fin n, j.val ≠ 0 ∧ μ j = 1
  · right
    obtain ⟨j, hj, hj1⟩ := hsep
    have hy1 : y ≠ 1 := fun h => hρy (by rw [h, map_one])
    refine omq_omPlus_four_le_rank_of_node hn5 hρ ht hj ?_ hy hy1
    rw [hj1, omPlusCurtisDatum_two_dScalar hF hn3 hχ j]
  · left
    exact omPlus_two_natural_of_not_separating hF hn3 hρ hρy ht hsep

end CFSG.LocalAnalysis.WeakClosure81
