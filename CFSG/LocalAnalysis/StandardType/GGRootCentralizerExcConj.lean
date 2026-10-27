module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcRoots
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcModel
public import CFSG.LieType.Ree.ExceptionalAutomorphismData

public section

namespace CFSG.StandardType

namespace RootCentExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section Adjoint


variable {τ : Tag} {K : Type} [Field K]

theorem coe_xPar_eq_pinnedX (h2 : (2 : K) = 0) (F : RootOperatorFamily τ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : K) :
    ((xPar F γ c : adjointGroup τ K) : ModGL τ K) = pinnedX τ K γ c := by
  have hs : (F.pinnedFamilySign γ : K) = 1 := by
    rcases F.pinnedFamilySign_eq γ with h | h <;> rw [h]
    · exact Int.cast_one
    · rw [Int.cast_neg, Int.cast_one]
      linear_combination -h2
  rw [F.pinnedX_eq_eltUnit K hγ, hs, one_mul, xPar_of_isRoot hγ]
  rfl

theorem centTwoGen_xPar_highRoot (h2 : (2 : K) = 0) (F : RootOperatorFamily τ)
    {θ : Fin τ.rank → ℤ} {i₀ : Fin τ.rank} (hd : HighRootData τ θ i₀) :
    CentTwoGen (xPar F θ (1 : K)) := by
  have he : xPar F θ (1 : K) = ⟨pinnedX τ K θ 1, pinnedX_mem_adjointGroup θ 1⟩ :=
    Subtype.ext (coe_xPar_eq_pinnedX h2 F hd.maxHeight.1 1)
  rw [he]
  exact centTwoGen_of_le_closure (hd.centralizer_le_closure h2)

theorem smul_single_of_adj {j k : Fin τ.rank} (h1 : τ.cartan k j = -1)
    (h2 : τ.cartan j k = -1) :
    (simple τ j * simple τ k) • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single k 1 := by
  rw [mul_smul, simple_smul, simple_smul]
  have e1 : reflect τ k (Pi.single j 1) = Pi.single j 1 + Pi.single k 1 := by
    rw [reflect, AutSt.sum_cartan_mul_single, h1, neg_one_smul, sub_neg_eq_add]
  have hs : ∑ l, τ.cartan j l * (Pi.single j 1 + Pi.single k 1 : Fin τ.rank → ℤ) l = 1 := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, AutSt.sum_cartan_mul_single,
      Tag.cartan_self, h2]
    norm_num
  rw [e1, reflect, hs, one_smul, add_sub_cancel_left]

theorem exists_conj_xPar_single_of_adj (h2 : (2 : K) = 0) (F : RootOperatorFamily τ)
    {j k : Fin τ.rank} (h1 : τ.cartan k j = -1) (h1' : τ.cartan j k = -1) :
    ∃ g : adjointGroup τ K,
      g * xPar F (Pi.single j 1) (1 : K) * g⁻¹ = xPar F (Pi.single k 1) 1 := by
  refine ⟨⟨canonicalRep (coxeterSystem τ) K (simple τ j * simple τ k),
    canonicalRep_mem_adjointGroup _ K _⟩, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_xPar_eq_pinnedX h2 F (isRoot_single τ _)]
  rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ (isRoot_single τ j),
    smul_single_of_adj h1 h1']

theorem centTwoGen_iff_of_adj (h2 : (2 : K) = 0) (F : RootOperatorFamily τ)
    {j k : Fin τ.rank} (h1 : τ.cartan k j = -1) (h1' : τ.cartan j k = -1) :
    CentTwoGen (xPar F (Pi.single j 1) (1 : K)) ↔ CentTwoGen (xPar F (Pi.single k 1) (1 : K)) := by
  obtain ⟨g, hg⟩ := exists_conj_xPar_single_of_adj h2 F h1 h1'
  constructor
  · intro h
    rw [← hg]
    exact h.conj g
  · intro h
    rw [← hg] at h
    exact h.of_conj

theorem centTwoGen_of_mem_rootGroup [Finite K] [CharP K 2] (F : RootOperatorFamily τ)
    (hs : ∀ j, CentTwoGen (xPar F (Pi.single j 1) (1 : K))) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {z : adjointGroup τ K} (hz : z ∈ rootGroup F K γ) (hz1 : z ≠ 1) :
    CentTwoGen z := by
  obtain ⟨g, j, hg⟩ := AutSt.exists_conj_xPar_single hγ hz hz1
  have h := hs j
  rw [← hg] at h
  exact h.of_conj

theorem exists_centTwoGen_single [Finite K] [CharP K 2] (F : RootOperatorFamily τ)
    {θ : Fin τ.rank → ℤ} {i₀ : Fin τ.rank} (hd : HighRootData τ θ i₀) :
    ∃ j, CentTwoGen (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hx1 : xPar F θ (1 : K) ≠ 1 := by
    intro h
    rw [← xPar_zero (F := F) θ] at h
    exact one_ne_zero (xPar_injective hd.maxHeight.1 h)
  obtain ⟨g, j, hg⟩ := AutSt.exists_conj_xPar_single hd.maxHeight.1
    (xPar_mem hd.maxHeight.1 (1 : K)) hx1
  refine ⟨j, ?_⟩
  rw [← hg]
  exact (centTwoGen_xPar_highRoot h2 F hd).conj g

theorem xPar_single_eq_xElement (h2 : (2 : K) = 0) (F : RootOperatorFamily τ) (i : Fin τ.rank)
    (c : K) : xPar F (Pi.single i 1) c = xElement i c :=
  Subtype.ext ((coe_xPar_eq_pinnedX h2 F (isRoot_single τ i) c).trans (pinnedX_single τ K i c))

theorem centTwoGen_single_E6 [Finite K] [CharP K 2] (F : RootOperatorFamily .E6)
    (j : Fin Tag.E6.rank) : CentTwoGen (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set P : Fin Tag.E6.rank → Prop := fun j => CentTwoGen (xPar F (Pi.single j 1) (1 : K)) with hP
  have step : ∀ a b : Fin Tag.E6.rank, Tag.cartan .E6 b a = -1 → Tag.cartan .E6 a b = -1 →
      (P b ↔ P ⟨0, by decide⟩) → (P a ↔ P ⟨0, by decide⟩) :=
    fun a b h h' hb => (centTwoGen_iff_of_adj h2 F h h').trans hb
  have h0 : ∀ j, P j ↔ P ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) (step _ ⟨2, by decide⟩ (by decide)
        (by decide) (step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl))
    · exact step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl
    · exact step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩ (by decide)
        (by decide) Iff.rfl)
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) (step _ ⟨2, by decide⟩ (by decide)
        (by decide) (step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl))
    · exact step _ ⟨4, by decide⟩ (by decide) (by decide) (step _ ⟨3, by decide⟩ (by decide)
        (by decide) (step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩
          (by decide) (by decide) Iff.rfl)))
  obtain ⟨j₁, hj₁⟩ := exists_centTwoGen_single (K := K) F highRootData_E6
  exact (h0 j).2 ((h0 j₁).1 hj₁)

theorem centTwoGen_single_E7 [Finite K] [CharP K 2] (F : RootOperatorFamily .E7)
    (j : Fin Tag.E7.rank) : CentTwoGen (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set P : Fin Tag.E7.rank → Prop := fun j => CentTwoGen (xPar F (Pi.single j 1) (1 : K)) with hP
  have step : ∀ a b : Fin Tag.E7.rank, Tag.cartan .E7 b a = -1 → Tag.cartan .E7 a b = -1 →
      (P b ↔ P ⟨0, by decide⟩) → (P a ↔ P ⟨0, by decide⟩) :=
    fun a b h h' hb => (centTwoGen_iff_of_adj h2 F h h').trans hb
  have h3 : P ⟨3, by decide⟩ ↔ P ⟨0, by decide⟩ :=
    step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩ (by decide)
      (by decide) Iff.rfl)
  have h4 : P ⟨4, by decide⟩ ↔ P ⟨0, by decide⟩ := step _ ⟨3, by decide⟩ (by decide) (by decide) h3
  have h5 : P ⟨5, by decide⟩ ↔ P ⟨0, by decide⟩ := step _ ⟨4, by decide⟩ (by decide) (by decide) h4
  have h0 : ∀ j, P j ↔ P ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) h3
    · exact step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl
    · exact h3
    · exact h4
    · exact h5
    · exact step _ ⟨5, by decide⟩ (by decide) (by decide) h5
  obtain ⟨j₁, hj₁⟩ := exists_centTwoGen_single (K := K) F highRootData_E7
  exact (h0 j).2 ((h0 j₁).1 hj₁)

theorem centTwoGen_single_E8 [Finite K] [CharP K 2] (F : RootOperatorFamily .E8)
    (j : Fin Tag.E8.rank) : CentTwoGen (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set P : Fin Tag.E8.rank → Prop := fun j => CentTwoGen (xPar F (Pi.single j 1) (1 : K)) with hP
  have step : ∀ a b : Fin Tag.E8.rank, Tag.cartan .E8 b a = -1 → Tag.cartan .E8 a b = -1 →
      (P b ↔ P ⟨0, by decide⟩) → (P a ↔ P ⟨0, by decide⟩) :=
    fun a b h h' hb => (centTwoGen_iff_of_adj h2 F h h').trans hb
  have h3 : P ⟨3, by decide⟩ ↔ P ⟨0, by decide⟩ :=
    step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩ (by decide)
      (by decide) Iff.rfl)
  have h4 : P ⟨4, by decide⟩ ↔ P ⟨0, by decide⟩ := step _ ⟨3, by decide⟩ (by decide) (by decide) h3
  have h5 : P ⟨5, by decide⟩ ↔ P ⟨0, by decide⟩ := step _ ⟨4, by decide⟩ (by decide) (by decide) h4
  have h6 : P ⟨6, by decide⟩ ↔ P ⟨0, by decide⟩ := step _ ⟨5, by decide⟩ (by decide) (by decide) h5
  have h0 : ∀ j, P j ↔ P ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) h3
    · exact step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact step _ ⟨6, by decide⟩ (by decide) (by decide) h6
  obtain ⟨j₁, hj₁⟩ := exists_centTwoGen_single (K := K) F highRootData_E8
  exact (h0 j).2 ((h0 j₁).1 hj₁)

theorem centTwoGen_single_F4 [Finite K] [CharP K 2] (F : RootOperatorFamily .F4)
    (j : Fin Tag.F4.rank) : CentTwoGen (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := (inferInstance : CharP K 2)
  set P : Fin Tag.F4.rank → Prop := fun j => CentTwoGen (xPar F (Pi.single j 1) (1 : K)) with hP
  let φ : MulAut (adjointGroup Tag.F4 K) := CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut K
  have hφ3 : φ (xElement (τ := Tag.F4) ⟨3, by decide⟩ (1 : K)) =
      xElement (τ := Tag.F4) ⟨0, by decide⟩ 1 := by
    have h := CFSG.LieType.Ree.ReeTag.finiteExceptionalAut_xElement
      (t := CFSG.LieType.Ree.ReeTag.F4) (K := K) ⟨3, by decide⟩ 1
    rw [one_pow, show CFSG.LieType.Ree.ReeTag.F4.perm ⟨3, by decide⟩ = ⟨0, by decide⟩ by
      decide] at h
    exact h
  have h30 : P ⟨3, by decide⟩ ↔ P ⟨0, by decide⟩ := by
    simp only [hP, xPar_single_eq_xElement h2 F]
    constructor
    · intro h
      have h' := h.map φ
      rwa [hφ3] at h'
    · intro h
      have h' := h.map φ.symm
      rwa [← hφ3, MulEquiv.symm_apply_apply] at h'
  have h01 : P ⟨1, by decide⟩ ↔ P ⟨0, by decide⟩ :=
    centTwoGen_iff_of_adj h2 F (by decide) (by decide)
  have h20 : P ⟨2, by decide⟩ ↔ P ⟨0, by decide⟩ :=
    (centTwoGen_iff_of_adj h2 F (k := ⟨3, by decide⟩) (by decide) (by decide)).trans h30
  have h0 : ∀ j, P j ↔ P ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact h01
    · exact h20
    · exact h30
  obtain ⟨j₁, hj₁⟩ := exists_centTwoGen_single (K := K) F highRootData_F4
  exact (h0 j).2 ((h0 j₁).1 hj₁)

end Adjoint

end RootCentExc

end CFSG.StandardType
