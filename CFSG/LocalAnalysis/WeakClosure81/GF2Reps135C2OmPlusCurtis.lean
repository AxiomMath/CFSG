module

public import CFSG.LieType.Steinberg.CurtisDatum
public import CFSG.LieType.Steinberg.Classical.SpinPlus
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRestSpinPlus
public import CFSG.Quasithin.Background.SmithCurtisMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg CFSG.LieType.RootSystem
open CFSG.Quasithin.SmithCurtis

variable (n : ℕ) (K : Type) [Field K] [Finite K]

instance finite_spinGroup_quadPlus : Finite (spinGroup (quadPlus n K)) := by
  rw [MonoidHom.finite_iff_finite_ker_range (spinMatrix (quadPlus n K))]
  refine ⟨?_, inferInstance⟩
  have hinj : Function.Injective
      (fun x : spinGroup (quadPlus n K) => (x : CliffordAlgebra (quadPlus n K))) :=
    fun _ _ h => Subtype.ext h
  have hpre : ((fun x : spinGroup (quadPlus n K) =>
      (x : CliffordAlgebra (quadPlus n K))) ⁻¹'
        ({1, -1} : Set (CliffordAlgebra (quadPlus n K)))).Finite :=
    Set.Finite.preimage (fun _ _ _ _ h => hinj h)
      ((Set.finite_singleton (-1)).insert 1)
  have hsub : ((spinMatrix (quadPlus n K)).ker : Set (spinGroup (quadPlus n K))) ⊆
      (fun x : spinGroup (quadPlus n K) =>
        (x : CliffordAlgebra (quadPlus n K))) ⁻¹'
        ({1, -1} : Set (CliffordAlgebra (quadPlus n K))) := by
    intro x hx
    rw [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases (mem_ker_spinMatrix_quadPlus_iff x).mp hx with h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr h
  exact (hpre.subset hsub).to_subtype

variable [CharP K 2]

theorem isPGroup_plusRootGroup (hn : 3 ≤ n) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) : IsPGroup 2 (plusRootGroup n K hn γ) := by
  obtain ⟨i, j, hij, s, t, _, hgrp⟩ := exists_plusRootGroup_eq (n := n) (K := K) hn hγ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  have hf : Function.Injective ((plusFrame n K hn).longRoot hij s t) :=
    HypFrame.longRoot_injective _ hij s t
  have hcard : Nat.card ((plusFrame n K hn).longRoot hij s t).range = 2 ^ (k : ℕ) := by
    rw [(Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm]
    rw [show Nat.card (Multiplicative K) = Nat.card K from rfl,
      Nat.card_eq_fintype_card, hk]
  rw [hgrp]
  exact IsPGroup.of_card hcard

@[expose] noncomputable def omPlusCurtisDatum (hn : 3 ≤ n) :
    CurtisDatum (spinGroup (quadPlus n K))
      (coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem 2 :=
  curtisDatumOf (D := plusDatum n K hn) (n := weylD K hn)
    (H := fun k => (torusD K hn k).range) (SpinPlus.isCTGroupDatum hn)
    (plusDatum_steinbergExtras hn) (CFSG.StandardType.GGRootSpinPlus.bruhatExtras hn) 2
    (fun _ hγ => isPGroup_plusRootGroup n K hn hγ)

variable {n K}

theorem omPlusCurtisDatum_U (hn : 3 ≤ n) :
    (omPlusCurtisDatum n K hn).U = posUnipotent (plusDatum n K hn) := rfl

theorem omPlusCurtisDatum_X (hn : 3 ≤ n) (k : Fin n) :
    (omPlusCurtisDatum n K hn).X k = plusRootGroup n K hn (Pi.single k 1) := rfl

theorem omPlusCurtisDatum_n (hn : 3 ≤ n) (k : Fin n) :
    (omPlusCurtisDatum n K hn).n k = weylD K hn k := rfl

theorem omPlusCurtisDatum_H (hn : 3 ≤ n) :
    (omPlusCurtisDatum n K hn).H = ⨆ k, (torusD K hn k).range := rfl

theorem omPlusCurtisDatum_two_H (hK : Nat.card K = 2) (hn : 3 ≤ n) :
    (omPlusCurtisDatum n K hn).H = ⊥ := by
  have : Subsingleton Kˣ := by
    refine Finite.card_le_one_iff_subsingleton.mp ?_
    simp [Nat.card_units K, hK]
  rw [omPlusCurtisDatum_H]
  refine iSup_eq_bot.mpr fun k => ?_
  rw [MonoidHom.range_eq_bot_iff]
  ext τ
  rw [show τ = 1 from Subsingleton.elim _ _]
  simp

theorem omPlusCurtisDatum_two_splitOver (k : Type*) [Field k] (hK : Nat.card K = 2)
    (hn : 3 ≤ n) : SplitOver k (omPlusCurtisDatum n K hn).H := by
  intro h hh
  rw [omPlusCurtisDatum_two_H hK hn, Subgroup.mem_bot] at hh
  rw [hh]
  exact ⟨1, by simp, [1], by simp⟩

private theorem omPlusCurtisDatum_dScalar_eq_one {G : Type*} [Group G] {B : Type*}
    {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ}
    (D : CurtisDatum G cs p) [Finite G] {k : Type*} [Field k] {χ : G → k}
    (hχ : χ 1 = 1) (s : B) (hX : Nat.card (D.X s) = 2) (hH : D.H = ⊥) :
    D.dScalar χ s = 1 := by
  classical
  let : Fintype (D.X s) := Fintype.ofFinite (D.X s)
  rw [CurtisDatum.dScalar.eq_1]
  have hcard : (Finset.univ.erase (1 : D.X s)).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
      show Fintype.card (D.X s) = 2 by rw [← Nat.card_eq_fintype_card, hX]]
  have hterm : ∀ x ∈ (Finset.univ : Finset (D.X s)).erase 1, χ (D.phi s x) = 1 := by
    intro x hx
    have hxne : x ≠ 1 := Finset.ne_of_mem_erase hx
    have hmem : D.phi s x ∈ D.H :=
      D.phi_mem s x x.2 (fun h => hxne (OneMemClass.coe_eq_one.mp h))
    rw [hH] at hmem
    rw [show D.phi s x = 1 from by simpa using hmem, hχ]
  rw [Finset.sum_congr rfl (fun x hx => hterm x hx), Finset.sum_const, hcard, one_smul]

private theorem omPlusCurtisDatum_d'Scalar_eq_one {G : Type*} [Group G] {B : Type*}
    {M : CoxeterMatrix B} {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ}
    (D : CurtisDatum G cs p) [Finite G] {k : Type*} [Field k] {χ : G → k}
    (hχ : χ 1 = 1) (s : B) (hX : Nat.card (D.X s) = 2) (hH : D.H = ⊥) :
    D.d'Scalar χ s = 1 := by
  classical
  let : Fintype (D.X s) := Fintype.ofFinite (D.X s)
  rw [CurtisDatum.d'Scalar.eq_1]
  have hcard : (Finset.univ.erase (1 : D.X s)).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
      show Fintype.card (D.X s) = 2 by rw [← Nat.card_eq_fintype_card, hX]]
  have hterm : ∀ x ∈ (Finset.univ : Finset (D.X s)).erase 1, χ (D.psi s x) = 1 := by
    intro x hx
    have hxne : x ≠ 1 := Finset.ne_of_mem_erase hx
    have hmem : D.psi s x ∈ D.H :=
      D.psi_mem s x x.2 (fun h => hxne (OneMemClass.coe_eq_one.mp h))
    rw [hH] at hmem
    rw [show D.psi s x = 1 from by simpa using hmem, hχ]
  rw [Finset.sum_congr rfl (fun x hx => hterm x hx), Finset.sum_const, hcard, one_smul]

theorem omPlusCurtisDatum_two_dScalar {k : Type*} [Field k] (hK : Nat.card K = 2) (hn : 3 ≤ n)
    {χ : spinGroup (quadPlus n K) → k} (hχ : χ 1 = 1) (s : Fin n) :
    (omPlusCurtisDatum n K hn).dScalar χ s = 1 := by
  refine omPlusCurtisDatum_dScalar_eq_one (omPlusCurtisDatum n K hn) hχ s ?_ ?_
  · rw [omPlusCurtisDatum_X hn s, plusRootGroup_single hn s]
    have hf : Function.Injective (rootD K hn s) :=
      HypFrame.longRoot_injective (plusFrame n K hn) (rootIdxD_ne n (by omega) s) true
        (rootSignD n s)
    rw [(Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm,
      show Nat.card (Multiplicative K) = Nat.card K from rfl, hK]
  · exact omPlusCurtisDatum_two_H hK hn

theorem omPlusCurtisDatum_two_d'Scalar {k : Type*} [Field k] (hK : Nat.card K = 2)
    (hn : 3 ≤ n) {χ : spinGroup (quadPlus n K) → k} (hχ : χ 1 = 1) (s : Fin n) :
    (omPlusCurtisDatum n K hn).d'Scalar χ s = 1 := by
  refine omPlusCurtisDatum_d'Scalar_eq_one (omPlusCurtisDatum n K hn) hχ s ?_ ?_
  · rw [omPlusCurtisDatum_X hn s, plusRootGroup_single hn s]
    have hf : Function.Injective (rootD K hn s) :=
      HypFrame.longRoot_injective (plusFrame n K hn) (rootIdxD_ne n (by omega) s) true
        (rootSignD n s)
    rw [(Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm,
      show Nat.card (Multiplicative K) = Nat.card K from rfl, hK]
  · exact omPlusCurtisDatum_two_H hK hn

end CFSG.LocalAnalysis.WeakClosure81
