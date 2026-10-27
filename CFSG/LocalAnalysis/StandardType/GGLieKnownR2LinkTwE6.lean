module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Link
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization

public section

namespace CFSG.StandardType.LieKnownR2.LinkTwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.StandardType.LieKnownR2.Q2 CFSG.StandardType.LieKnownR2.Link

private theorem gamE6_getD :
    gamE6.getD 0 0 = (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∧
    gamE6.getD 1 0 = -(Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∧
    gamE6.getD 2 0 = (Pi.single 2 1 : Fin Tag.E6.rank → ℤ) ∧
    gamE6.getD 3 0 = -(Pi.single 2 1 : Fin Tag.E6.rank → ℤ) ∧
    gamE6.getD 4 0 = (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) ∧
    gamE6.getD 5 0 = -(Pi.single 3 1 : Fin Tag.E6.rank → ℤ) ∧
    gamE6.getD 6 0 = (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) ∧
    gamE6.getD 7 0 = -(Pi.single 4 1 : Fin Tag.E6.rank → ℤ) ∧
    gamE6.getD 8 0 = (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) ∧
    gamE6.getD 9 0 = -(Pi.single 5 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

private theorem coe_orbitX_card_two
    {t : TwistTag} {K : Type} [Field K] (σ : K →+* K) (a : Fin t.foldedTag.rank)
    (h : (t.orbit a).card = 2) (c : orbitField t K σ a) :
    ((orbitX t K σ a c : adjointGroup t.tag K) : ModGL t.tag K) =
      xUnit t.tag K (t.orbitMin a) (c : K) * xUnit t.tag K (t.perm (t.orbitMin a)) (σ (c : K)) := by
  rw [coe_orbitX, h]
  simp [List.range_succ]

private theorem coe_orbitX_card_one
    {t : TwistTag} {K : Type} [Field K] (σ : K →+* K) (a : Fin t.foldedTag.rank)
    (h : (t.orbit a).card = 1) (c : orbitField t K σ a) :
    ((orbitX t K σ a c : adjointGroup t.tag K) : ModGL t.tag K) =
      xUnit t.tag K (t.orbitMin a) (c : K) := by
  rw [coe_orbitX, h]
  simp [List.range_succ]

private theorem coe_orbitY_card_two
    {t : TwistTag} {K : Type} [Field K] (σ : K →+* K) (a : Fin t.foldedTag.rank)
    (h : (t.orbit a).card = 2) (c : orbitField t K σ a) :
    ((orbitY t K σ a c : adjointGroup t.tag K) : ModGL t.tag K) =
      yUnit t.tag K (t.orbitMin a) (c : K) * yUnit t.tag K (t.perm (t.orbitMin a)) (σ (c : K)) := by
  rw [coe_orbitY, h]
  simp [List.range_succ]

private theorem coe_orbitY_card_one
    {t : TwistTag} {K : Type} [Field K] (σ : K →+* K) (a : Fin t.foldedTag.rank)
    (h : (t.orbit a).card = 1) (c : orbitField t K σ a) :
    ((orbitY t K σ a c : adjointGroup t.tag K) : ModGL t.tag K) =
      yUnit t.tag K (t.orbitMin a) (c : K) := by
  rw [coe_orbitY, h]
  simp [List.range_succ]

private theorem hword_eq
    {K : Type} [Field K] (σ : K →+* K) :
    hword (τ := Tag.E6) (K := K) gamE6 wordTwE6E6 =
      ((orbitX TwistTag.E6 K σ ⟨1, by decide⟩ 1 : adjointGroup TwistTag.E6.tag K) :
          ModGL TwistTag.E6.tag K) *
        ((orbitY TwistTag.E6 K σ ⟨0, by decide⟩ 1 : adjointGroup TwistTag.E6.tag K) :
          ModGL TwistTag.E6.tag K) *
        ((orbitX TwistTag.E6 K σ ⟨0, by decide⟩ 1 : adjointGroup TwistTag.E6.tag K) :
          ModGL TwistTag.E6.tag K) *
        ((orbitY TwistTag.E6 K σ ⟨1, by decide⟩ 1 : adjointGroup TwistTag.E6.tag K) :
          ModGL TwistTag.E6.tag K) *
        ((orbitY TwistTag.E6 K σ ⟨2, by decide⟩ 1 : adjointGroup TwistTag.E6.tag K) :
          ModGL TwistTag.E6.tag K) *
        ((orbitX TwistTag.E6 K σ ⟨2, by decide⟩ 1 : adjointGroup TwistTag.E6.tag K) :
          ModGL TwistTag.E6.tag K) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := gamE6_getD
  have c0 : (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 := by decide +kernel
  have c1 : (TwistTag.E6.orbit ⟨1, by decide⟩).card = 2 := by decide +kernel
  have c2 : (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 := by decide +kernel
  have m0 : TwistTag.E6.orbitMin ⟨0, by decide⟩ = 0 := by decide +kernel
  have m1 : TwistTag.E6.orbitMin ⟨1, by decide⟩ = 2 := by decide +kernel
  have m2 : TwistTag.E6.orbitMin ⟨2, by decide⟩ = 3 := by decide +kernel
  have p0 : TwistTag.E6.perm 0 = 5 := by decide +kernel
  have p2 : TwistTag.E6.perm 2 = 4 := by decide +kernel
  rw [coe_orbitX_card_two σ _ c1, coe_orbitY_card_two σ _ c0, coe_orbitX_card_two σ _ c0,
    coe_orbitY_card_two σ _ c1, coe_orbitY_card_one σ _ c2, coe_orbitX_card_one σ _ c2, m0, m1, m2,
    p0, p2]
  simp only [hword, wordTwE6E6, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, pinnedX_single, pinnedX_neg_single,
    OneMemClass.coe_one, map_one, mul_assoc]
  rfl

private theorem hword_mem_root
    {K : Type} [Field K] (σ : K →+* K) :
    hword (τ := Tag.E6) (K := K) gamE6 wordTwE6E6 ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  rw [hword_eq σ]
  have hX : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ a),
      ((orbitX TwistTag.E6 K σ a c : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) ∈
        graphFixedRootGroup TwistTag.E6 K σ := fun a c =>
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (orbitX_mem_graphFixedPosUnipotent _ σ a c)
  have hY : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ a),
      ((orbitY TwistTag.E6 K σ a c : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) ∈
        graphFixedRootGroup TwistTag.E6 K σ := fun a c =>
    graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (orbitY_mem_graphFixedNegUnipotent _ σ a c)
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hX _ _) (hY _ _)) (hX _ _)) (hY _ _))
    (hY _ _)) (hX _ _)

theorem twE6_exists_odd_fpf
    (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K →+* K) :
    ∃ h ∈ Pθ .E6 K ⊓ graphFixedRootGroup TwistTag.E6 K σ, Odd (orderOf h) ∧
      ∀ q ∈ Qθ .E6 K, h * q * h⁻¹ * q⁻¹ ∈ Uθ .E6 K → q ∈ Uθ .E6 K :=
  exists_odd_fpf_mem (linkE6.core (Or.inr (Or.inl rfl)))
    (fun k hk => by
      rw [← linkE6.glen]
      exact (by decide : ∀ k ∈ wordTwE6E6, k < gensE6.length) k hk)
    certTwE6E6 _ (hword_mem_root σ)

end CFSG.StandardType.LieKnownR2.LinkTwE6
