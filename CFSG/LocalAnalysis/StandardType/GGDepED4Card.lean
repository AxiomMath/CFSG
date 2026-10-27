module

public import CFSG.LocalAnalysis.StandardType.GGDepED4False
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat1
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat2
public import CFSG.LocalAnalysis.StandardType.GGDepEFrame
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4PackDefs
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic
public import CFSG.Holt.H78.Sec4Prop46D
public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
public import CFSG.Holt.General.Basic
public import CFSG.Holt.General.ComponentsImage
public import CFSG.Holt.General.OddOrbitsBasic
public import CFSG.Holt.H78.Sec4AltSylow
public import CFSG.Holt.H78.Sec4Prop46A3
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggDepED4_card_le_oneNode (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3) (hA : GGDepED4Aligned p 1 Bs K J L) :
    Nat.card ↥Bs ≤ 3 ^ 6 := by
  classical
  obtain ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb1, hb2, hcardΛa, hMLeq, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hk2, hform, hrefl, hpairL, hpairK, hKall, hLgen, hJgen⟩ := hA
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨hCfg, hOp, hInner, hNoTr, hNbr, hReflK, hScal⟩ := hH
  have hx : x ∈ Bs := hCfg.tableB_facts.2.2.1
  let Idx := {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa
  let Φ : Idx → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
  have hb12 : b₁ ≠ b₂ := by
    rw [hb1, hb2]
    exact fun hcon => (by decide : (0 : Fin 6) ≠ 5) (e.injective hcon)
  have hcardΛf : Fintype.card Λ = 6 := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hΛaF : Fintype.card Λa = 1 := by
    rw [← Nat.card_eq_fintype_card, hcardΛa]
  have hcardSubF : Fintype.card {j : Λ // j ≠ b₁ ∧ j ≠ b₂} = 4 := by
    rw [CFSG.Holt.H78.CaseAD.card_compl_pair hb12, hcardΛf]
  have hcardIdx : Nat.card Idx = 5 := by
    change Nat.card ({j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa) = 5
    rw [Nat.card_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcardSubF, hΛaF]
  have hLgen' : ggAutomizer L Bs = Subgroup.closure (Set.range Φ) := by
    have hrange : Set.range Φ =
        Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
          Set.range (fun a : Λa => φ (Sum.inr a)) := by
      ext z
      constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | inl j => exact Or.inl ⟨j, rfl⟩
        | inr a => exact Or.inr ⟨a, rfl⟩
      · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
        · exact ⟨Sum.inl j, rfl⟩
        · exact ⟨Sum.inr a, rfl⟩
    rw [hLgen, ← hrange]
  have hxpow : x ^ p = 1 := (hCfg.tableB_facts.2.1).2 x hx
  have hfixb : ∀ b : ↥Bs, (∀ o : Idx, Φ o b = b) → (b : G) ∈ Subgroup.zpowers x := by
    intro b hb
    refine hFix G p B Bs x L D J hCfg hOp hInner hNoTr y K hNbr hReflK hScal b ?_
    intro ψ hψ
    rw [hLgen'] at hψ
    exact ggFixed_of_mem_closure Φ b hb ψ hψ
  have hdimV : Module.finrank (ZMod p) V ≤ 6 := by
    have hfr := ggRC_finrank_le_of_fix (p := p) hxpow (ι := ι) (φ := Φ)
      (h := fun o : Idx => h (o.map Subtype.val id))
      (α := fun o : Idx => α (o.map Subtype.val id))
      (fun o w => hform (o.map Subtype.val id) w) hfixb
    have hc : Fintype.card Idx = 5 := by
      rw [← Nat.card_eq_fintype_card, hcardIdx]
    omega
  have hcardV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rwa [Nat.card_zmod] at h
  calc Nat.card ↥Bs = Nat.card V := card_eq_of_ggLin ι
    _ = p ^ Module.finrank (ZMod p) V := hcardV
    _ ≤ p ^ 6 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hdimV
    _ = 3 ^ 6 := by rw [hp3]

end CFSG.StandardType

end
