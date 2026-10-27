module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Smith
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpSmallType
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpNatural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Label
import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Spin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.Quasithin.SmithCurtis
open scoped Matrix

open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar in
private theorem spSR_extend_ne_one {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (StatedSp n K) V} [ρ.IsIrreducible]
    (k : Type) [Field k]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (StatedSp n K)) ρ.asModule) k]
    (hρ1 : ∃ g, ρ g ≠ 1) :
    ∃ g, CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g ≠ 1 := by
  obtain ⟨g, hg⟩ := hρ1
  exact ⟨g, fun h => hg ((extendScalars_endFieldRep_eq_one_iff ρ k g).mp h)⟩

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem spSR_four {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (StatedSp n K) V} [ρ.IsIrreducible]
    (k : Type) [Field k]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (StatedSp n K)) ρ.asModule) k]
    {s : ℕ} (hs1 : 1 ≤ s)
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (StatedSp n K)) ρ.asModule) = 2 ^ s)
    {y : StatedSp n K}
    (hfour : 4 ≤ Module.finrank k (LinearMap.range
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1))) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  rw [finrank_range_sub_one_eq_mul ρ hE k y]
  exact le_trans (by norm_num) (Nat.mul_le_mul hs1 hfour)

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 in
private theorem spSR_cube {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}
    (hf : f = 2 ∨ f = 3) (hK : Nat.card K = 2 ^ f)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (StatedSp n K) V} [ρ.IsIrreducible]
    (k : Type) [Field k] [CharP k 2] [Algebra K k]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (StatedSp n K)) ρ.asModule) k]
    {y₀ : TensorProduct
      (Module.End (MonoidAlgebra (ZMod 2) (StatedSp n K)) ρ.asModule) k ρ.asModule}
    {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y₀ χ μ)
    {y : StatedSp n K}
    (hcube : (∃ (i : Fin n) (c : ℕ), c.Coprime (Nat.card K - 1) ∧
        ∀ u : Kˣ, χ (corootSp i u) = algebraMap K k (u : K) ^ c) ∧
      2 ≤ Module.finrank k (LinearMap.range
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1))) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  obtain ⟨⟨i, c, hc, hχ⟩, h2⟩ := hcube
  obtain ⟨s, hs1, hE⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.exists_card_endField_eq_two_pow ρ
  have : Fintype K := Fintype.ofFinite K
  have hc' : (Nat.card Kˣ).Coprime c := by
    rw [Nat.card_units (α := K)]
    exact hc.symm
  have hpow : ∀ u : Kˣ, algebraMap K k (u : K) ^ 2 ^ s = algebraMap K k (u : K) := by
    intro u
    obtain ⟨a, rfl⟩ :=
      (Nat.Coprime.pow_left_bijective (G := Kˣ) (n := c) hc').surjective u
    have h := CFSG.HardMathSupport.GuralnickMalle.isCurtisType_chi_pow_card ρ
      (spCurtisDatum n K) k ht (corootSp_mem_H i a)
    rw [hχ a, hE] at h
    rw [Units.val_pow_eq_pow_val (a := a) c, map_pow]
    exact h
  have hKf : Fintype.card K = 2 ^ f := Fintype.card_eq_nat_card.trans hK
  have hfs : f ≤ s := le_of_ringHom_pow_eq (algebraMap K k) hKf hs1 hpow
  have h4 : 4 ≤ s * Module.finrank k (LinearMap.range
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1)) := by
    have hle : f * 2 ≤ s * Module.finrank k (LinearMap.range
        (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1)) :=
      Nat.mul_le_mul hfs h2
    exact (by rcases hf with rfl | rfl <;> norm_num : 4 ≤ f * 2).trans hle
  rw [finrank_range_sub_one_eq_mul ρ hE k y]
  exact h4

theorem sp_small_natural_or_four_le {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}
    (hn : 3 ≤ n) (hf : f = 2 ∨ f = 3) (hK : Nat.card K = 2 ^ f) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (StatedSp n K) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1) {y : StatedSp n K} (hy : y * y = 1) (hy1 : y ≠ 1) :
    (∃ β : V ≃+ (Fin n ⊕ Fin n → K), ∀ (g : StatedSp n K) (v : V),
        β (ρ g v) = mat n K g *ᵥ β v) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  have hρirr : ρ.IsIrreducible := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).2 hρ
  have : ρ.IsIrreducible := hρirr
  let D := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.spCurtisDatum n K
  let E := Module.End (MonoidAlgebra (ZMod 2) (StatedSp n K)) ρ.asModule
  have hcharE : CharP E 2 := CFSG.HardMathSupport.GuralnickMalle.endField_charP ρ 2
  let k := AlgebraicClosure E
  let _ : Algebra K k := (CFSG.HardMathSupport.GuralnickMalle.nonempty_ringHom_algebraicClosure
    (K := E) (F₀ := K) (p := 2)).some.toAlgebra
  have hchark : CharP k 2 := charP_of_injective_algebraMap (algebraMap E k).injective 2
  have hfinE : FiniteDimensional E ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  have hsplit : SplitOver k D.H :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.spCurtisDatum_splitOver k
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isSimpleRep_extendScalars_endFieldRep ρ k
  obtain ⟨y₀, χ, μ, ht⟩ := D.exists_isCurtisType hsplit hsimp
  have hρ1' := spSR_extend_ne_one (n := n) k hρ1
  rcases sp_small_type (k := k) hn hf hK hsimp hρ1' ht hy hy1 with
    hnat | hcube | hfour
  · obtain ⟨hμ, φ, hχφ⟩ := hnat
    rw [hμ] at ht
    refine Or.inl (exists_addEquiv_spn_natural (n := n) (by omega)
      (by rcases hf with rfl | rfl <;> rw [hK] <;> norm_num) ρ k ht φ ?_)
    intro t
    exact (hχφ t).trans (congrArg (fun x : Fin n => φ (t x)) (Fin.ext rfl))
  · exact Or.inr (spSR_cube hf hK k ht hcube)
  · obtain ⟨s, hs1, hE⟩ :=
      CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.exists_card_endField_eq_two_pow ρ
    exact Or.inr (spSR_four (s := s) k hs1 hE hfour)

end CFSG.LocalAnalysis.WeakClosure81
