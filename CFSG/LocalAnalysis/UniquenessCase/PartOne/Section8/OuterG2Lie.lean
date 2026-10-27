module

public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterG2Prime

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel ChevalleyExceptionalModel UntwistedChevalleyModel)
open CFSG.Blueprint.Chevalley (Tag adjointGroup ModGL xUnit yUnit xUnit_mem_adjointGroup
  yUnit_mem_adjointGroup coe_xUnit coe_yUnit)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.LieType.Chevalley (baseChangeGL baseChangeGL_injective baseChangeGL_xUnit
  baseChangeGL_yUnit baseChangeGL_mem_adjointGroup map_baseChangeGL_adjointGroup
  nonempty_mulEquiv_adjointGroup)

theorem card_outer_of_lieModel_G2_prime
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h : CFSG.Blueprint.LieModel X .G2 0 p 1) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hc : ChevalleyExceptionalModel X .G2 p 1 :=
    LieModel.chevalleyExceptionalModel h (by decide)
  have hm : UntwistedChevalleyModel X .G2 (p ^ 1) := hc.2
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eX⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .G2 hm
  haveI : Fintype K := Fintype.ofFinite K
  let eZ : ZMod p ≃+* K :=
    ZMod.ringEquivOfPrime K hp (by
      rw [← Nat.card_eq_fintype_card, hKcard, pow_one])
  let b : adjointGroup .G2 (ZMod p) →* adjointGroup .G2 K :=
    ((baseChangeGL (τ := .G2) eZ.toRingHom).comp
        (adjointGroup .G2 (ZMod p)).subtype).codRestrict (adjointGroup .G2 K)
      fun g => baseChangeGL_mem_adjointGroup (τ := .G2) eZ.toRingHom g.2
  have hb : ∀ g : adjointGroup .G2 (ZMod p),
      (b g : ModGL .G2 K) = baseChangeGL eZ.toRingHom (g : ModGL .G2 (ZMod p)) :=
    fun _ => rfl
  have hcl : adjointGroup .G2 K = Subgroup.closure
      {g : ModGL .G2 K | ∃ (i : Fin Tag.G2.rank) (c : K),
        g = xUnit .G2 K i c ∨ g = yUnit .G2 K i c} := by
    rw [adjointGroup]
    congr 1
    ext g
    constructor
    · rintro ⟨i, c, h | h⟩
      · exact ⟨i, c, Or.inl (Units.ext (by simpa only [coe_xUnit] using h))⟩
      · exact ⟨i, c, Or.inr (Units.ext (by simpa only [coe_yUnit] using h))⟩
    · rintro ⟨i, c, rfl | rfl⟩
      · exact ⟨i, c, Or.inl rfl⟩
      · exact ⟨i, c, Or.inr rfl⟩
  have hmap : (adjointGroup .G2 (ZMod p)).map (baseChangeGL (τ := .G2) eZ.toRingHom) =
      adjointGroup .G2 K := by
    refine le_antisymm ?_ ?_
    · rw [map_baseChangeGL_adjointGroup (τ := .G2) eZ.toRingHom]
      refine (Subgroup.closure_le (adjointGroup .G2 K)).2 ?_
      rintro g ⟨i, c, rfl | rfl⟩
      · exact xUnit_mem_adjointGroup i (eZ c)
      · exact yUnit_mem_adjointGroup i (eZ c)
    · rw [hcl]
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨i, c, rfl | rfl⟩
      · obtain ⟨c', rfl⟩ := eZ.surjective c
        exact ⟨xUnit .G2 (ZMod p) i c', xUnit_mem_adjointGroup i c',
          baseChangeGL_xUnit (τ := .G2) eZ.toRingHom i c'⟩
      · obtain ⟨c', rfl⟩ := eZ.surjective c
        exact ⟨yUnit .G2 (ZMod p) i c', yUnit_mem_adjointGroup i c',
          baseChangeGL_yUnit (τ := .G2) eZ.toRingHom i c'⟩
  have hbinj : Function.Injective b := by
    intro g g' hgg'
    have h1 : baseChangeGL eZ.toRingHom (g : ModGL .G2 (ZMod p)) =
        baseChangeGL eZ.toRingHom (g' : ModGL .G2 (ZMod p)) := by
      simpa only [hb] using congrArg Subtype.val hgg'
    exact Subtype.ext (baseChangeGL_injective eZ.toRingHom h1)
  have hbsurj : Function.Surjective b := by
    intro x
    have hx : (x : ModGL .G2 K) ∈
        (adjointGroup .G2 (ZMod p)).map (baseChangeGL (τ := .G2) eZ.toRingHom) := by
      rw [hmap]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  let adjE : adjointGroup .G2 (ZMod p) ≃* adjointGroup .G2 K :=
    MulEquiv.ofBijective b ⟨hbinj, hbsurj⟩
  have hX : Nat.card (Outer X) = Nat.card (Outer (adjointGroup .G2 K)) :=
    Nat.card_congr (equivalence eX).toEquiv
  have hZ : Nat.card (Outer (adjointGroup .G2 K)) =
      Nat.card (Outer (adjointGroup .G2 (ZMod p))) :=
    Nat.card_congr (equivalence adjE.symm).toEquiv
  exact hX.trans (hZ.trans (card_outer_adjointGroup_G2_zmod_prime p hp hp2 hp3))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
