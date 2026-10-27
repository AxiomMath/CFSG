module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKCoord

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem weyl_elt {Bs X : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    {T : Subgroup ↥X} {w : Fin 6 → ↥X}
    (hcl5 : ∀ a ∈ (ggGamma X hBsN).range, ∀ t ∈ T, a t = t)
    (hcl7 : ∀ i, ∀ a ∈ (ggGamma X hBsN).range,
      w i * (a (w i))⁻¹ ∈ T ∧ (w i * (a (w i))⁻¹) ^ 3 = 1) (i : Fin 6) :
    GGTorusWeylElt 3 (ggGamma X hBsN).range (w i) := by
  intro a ha
  exact ⟨(hcl7 i a ha).2, fun a' ha' =>
    hcl5 a' ha' (w i * (a (w i))⁻¹) (hcl7 i a ha).1⟩

private theorem actsAsK_one {Bs : Subgroup G} (κ : Additive ↥Bs →+ Vec6) :
    ActsAsK κ (1 : MulAut ↥Bs) 1 := by
  intro b
  rw [MulAut.one_apply, Matrix.one_mulVec]

private theorem actsAsK_mul {Bs : Subgroup G} {κ : Additive ↥Bs →+ Vec6}
    {φ ψ : MulAut ↥Bs} {g h : Mat6} (hφ : ActsAsK κ φ g) (hψ : ActsAsK κ ψ h) :
    ActsAsK κ (φ * ψ) (g * h) := by
  intro b
  rw [MulAut.mul_apply, hφ (ψ b), hψ b, Matrix.mulVec_mulVec]

theorem kappaOf_aut {Bs X : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    {Z : Subgroup ↥X} {Φ : ↥(ggGamma X hBsN).range →* Multiplicative (Fin 6 → ZMod 3)}
    {T : Subgroup ↥X} {w : Fin 6 → ↥X}
    (hmodel : GGE6ThreeWeylModelWith Z (ggGamma X hBsN).range Φ T w)
    (hcard : Nat.card (ggGamma X hBsN).range = 3 ^ 5)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    (∀ φ ∈ ggAutomizer X Bs, ∃ g ∈ closureL, ActsAsK (kappaOf hBsN Φ) φ g) ∧
      (∀ g ∈ closureL, ∃ φ ∈ ggAutomizer X Bs, ActsAsK (kappaOf hBsN Φ) φ g) := by
  classical
  have hmodel0 := hmodel
  obtain ⟨-, -, -, -, hcl5, -, hcl7, hcl8, -, hcl10, -, -⟩ := hmodel0
  refine ⟨?_, ?_⟩
  · intro φ hφ
    obtain ⟨n, hnX, hnN, hφb⟩ := mem_ggAutomizer_iff.mp hφ
    have hφeq : φ = ggConjAut Bs hnN := by
      ext b
      rw [ggConjAut_apply]
      exact hφb b
    have hnN' : MulAut.conj (⟨n, hnX⟩ : ↥X) ∈
        Subgroup.normalizer ((ggGamma X hBsN).range : Set (MulAut ↥X)) :=
      conj_mem_normalizer_range_ggGamma hBsN hnX hnN
    obtain ⟨u, hu⟩ := hcl10 ⟨n, hnX⟩ hnN'
    obtain ⟨g, hg, hgv⟩ := exists_closureL_of_weyl u
    refine ⟨g, hg, ?_⟩
    rw [hφeq]
    intro b
    have hrel : (↑((ggGamma X hBsN).rangeRestrict (ggConjAut Bs hnN b)) : MulAut ↥X) =
        MulAut.conj (⟨n, hnX⟩ : ↥X) * (↑((ggGamma X hBsN).rangeRestrict b) : MulAut ↥X) *
          (MulAut.conj (⟨n, hnX⟩ : ↥X))⁻¹ := by
      have h1 : ggConjAut Bs hnN b =
          (⟨n * (b : G) * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnN b).mp b.2⟩ : ↥Bs) :=
        Subtype.ext (ggConjAut_apply Bs hnN b)
      rw [h1]
      simp only [MonoidHom.coe_rangeRestrict]
      exact ggGamma_conj X hBsN ⟨n, hnX⟩ b _
    have hu' := hu ((ggGamma X hBsN).rangeRestrict b)
      ((ggGamma X hBsN).rangeRestrict (ggConjAut Bs hnN b)) hrel
    refine coordE_injOn _ _
      (kappaOf_five hBsN hmodel hcard (ggConjAut Bs hnN b)) ?_ ?_
    · rw [closureL_apply_five hg (kappaOf hBsN Φ (Additive.ofMul b))]
      exact kappaOf_five hBsN hmodel hcard b
    · exact (kappaOf_coordE hBsN hmodel hcard (ggConjAut Bs hnN b)).trans
        (hu'.trans
          ((congrArg (TableBExc.E6Three.adAct .E6 3 u)
            (kappaOf_coordE hBsN hmodel hcard b).symm).trans
            (hgv (kappaOf hBsN Φ (Additive.ofMul b))
              (kappaOf_five hBsN hmodel hcard b)).symm))
  · intro g hg
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      have hnN : ((w (nodeOf j) : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G) :=
        mem_normalizer_of_ggTorusWeylElt hBsN hSC (weyl_elt hBsN hcl5 hcl7 (nodeOf j))
      refine ⟨ggConjAut Bs hnN, ggConjAut_mem_ggAutomizer (w (nodeOf j)).2 hnN, ?_⟩
      intro b
      obtain ⟨b', hb'1, hb'2⟩ := hcl8 (nodeOf j) ((ggGamma X hBsN).rangeRestrict b)
      have hrel : (↑((ggGamma X hBsN).rangeRestrict (ggConjAut Bs hnN b)) : MulAut ↥X) =
          MulAut.conj (w (nodeOf j)) * (↑((ggGamma X hBsN).rangeRestrict b) : MulAut ↥X) *
            (MulAut.conj (w (nodeOf j)))⁻¹ := by
        have h1 : ggConjAut Bs hnN b =
            (⟨((w (nodeOf j) : ↥X) : G) * (b : G) * ((w (nodeOf j) : ↥X) : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp hnN b).mp b.2⟩ : ↥Bs) :=
          Subtype.ext (ggConjAut_apply Bs hnN b)
        rw [h1]
        simp only [MonoidHom.coe_rangeRestrict]
        exact ggGamma_conj X hBsN (w (nodeOf j)) b _
      have hbeq : (ggGamma X hBsN).rangeRestrict (ggConjAut Bs hnN b) = b' :=
        Subtype.ext (hrel.trans hb'1)
      refine coordE_injOn _ _
        (kappaOf_five hBsN hmodel hcard (ggConjAut Bs hnN b)) ?_ ?_
      · rw [gensL_apply_five j (kappaOf hBsN Φ (Additive.ofMul b))]
        exact kappaOf_five hBsN hmodel hcard b
      · exact (kappaOf_coordE hBsN hmodel hcard (ggConjAut Bs hnN b)).trans
          ((congrArg (fun x => Multiplicative.toAdd (Φ x)) hbeq).trans
            (hb'2.trans
              ((congrArg (TableBExc.E6Three.adRefl .E6 3 (nodeOf j))
                (kappaOf_coordE hBsN hmodel hcard b).symm).trans
                (coordE_gensL j (kappaOf hBsN Φ (Additive.ofMul b))
                  (kappaOf_five hBsN hmodel hcard b)).symm)))
    | one => exact ⟨1, one_mem _, actsAsK_one (kappaOf hBsN Φ)⟩
    | mul g h hg hh ihg ihh =>
      obtain ⟨φ, hφ, hφg⟩ := ihg
      obtain ⟨ψ, hψ, hψh⟩ := ihh
      exact ⟨φ * ψ, mul_mem hφ hψ, actsAsK_mul hφg hψh⟩

end E6Dep

end CFSG.StandardType

end
