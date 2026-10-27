module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWDFalse
public import CFSG.LocalAnalysis.StandardType.GGTWDCells36Orb
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
public import CFSG.LocalAnalysis.StandardType.GGTWCoreDefs
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

theorem ggTW_card_dichotomy (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p N k : ℕ}
    [Fact p.Prime] (hp : 3 ≤ p) (hpN : p ∣ N) (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 9 ∨ N = 10)
    {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hxL : x ∉ L) (hk : k = 1 ∨ k = 2) (hA : GGTWAligned p N k Bs L J K) :
    Nat.card ↥Bs = p ^ (N - 1) ∨ Nat.card ↥Bs = p ^ N := by
  classical
  obtain ⟨pos, Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb12, hcardΛa, hpos, hMLeq, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hk2, hform, hrefl, hpairL, hpairK, hAL, hAK, hAJ⟩ := hA
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hp2 : p ≠ 2 := by
    have hβ : p ∈ LargeEvenBeta 4 G := hH.1.1.2.2.2.2.2.1
    exact hβ.2.1
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hN5 : 5 ≤ N := by rcases hN with h' | h' | h' | h' | h' <;> omega
  have hdep : ¬ LinearIndependent (ZMod p) (fun i : Λ => h (Sum.inl i)) :=
    ggXDatumA_dep hFix hp2 hH hx hxL hN5 hpN e hMLeq hCLcartan
      (ι := ι) (φ := fun i : Λ => φ (Sum.inl i)) (h := fun i : Λ => h (Sum.inl i))
      (α := fun i : Λ => α (Sum.inl i)) (hφ := fun i w => hform (Sum.inl i) w)
      (hpair := fun i j => hpairL i j) (hAL := hAL)
  have hframe : GGDepAFrame p N (fun i : Fin (N - 1) => h (Sum.inl (e i)))
      (fun i : Fin (N - 1) => α (Sum.inl (e i))) (ι (Additive.ofMul ⟨x, hx⟩)) :=
    ggXDatumA_frame hFix hp2 hH hx hN5 hpN e hMLeq hCLcartan
      (ι := ι) (φ := fun i : Λ => φ (Sum.inl i)) (h := fun i : Λ => h (Sum.inl i))
      (α := fun i : Λ => α (Sum.inl i)) (hφ := fun i w => hform (Sum.inl i) w)
      (hpair := fun i j => hpairL i j) (hAL := hAL) (hdep := hdep)
  obtain ⟨hlo, hhi⟩ := ggDepA_finrank_bounds hframe
  have hfin : Module.finrank (ZMod p) V = N - 1 ∨ Module.finrank (ZMod p) V = N := by
    omega
  have hcardV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rwa [Nat.card_zmod] at h
  have hcardBs : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V := by
    have hVB : Nat.card ↥Bs = Nat.card V := card_eq_of_ggLin ι
    rw [hVB, hcardV]
  rcases hfin with hfin | hfin
  · left; rw [hcardBs, hfin]
  · right; rw [hcardBs, hfin]

theorem ggTW_card_le_oneNode (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p N : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x y : G} {L D J K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hA : GGTWAligned p N 1 Bs K J L) :
    Nat.card ↥Bs ≤ p ^ (N - 1) := by
  classical
  obtain ⟨pos, Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb12, hcardΛa, hpos, hMLeq, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hk2, hform, hrefl, hpairL, hpairK, hKall, hLgen, hJgen⟩ := hA
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨hCfg, hOp, hInner, hNoTr, hNbr, hReflK, hScal⟩ := hH
  have hx : x ∈ Bs := hCfg.tableB_facts.2.2.1
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let Idx := {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa
  let Φ : Idx → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
  have hΛaF : Fintype.card Λa = 1 := by
    rw [← Nat.card_eq_fintype_card, hcardΛa]
  have hcardΛf : Fintype.card Λ = N - 1 := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
  have hcardΛ2 : 2 ≤ Fintype.card Λ := by
    calc 2 = ({b₁, b₂} : Finset Λ).card := (Finset.card_pair hb12).symm
      _ ≤ (Finset.univ : Finset Λ).card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card Λ := Finset.card_univ
  have hN3 : 3 ≤ N := by omega
  have hcardSubF : Fintype.card {j : Λ // j ≠ b₁ ∧ j ≠ b₂} = N - 3 := by
    rw [CFSG.Holt.H78.CaseAD.card_compl_pair hb12, hcardΛf]
    omega
  have hcardIdx : Nat.card Idx = N - 2 := by
    change Nat.card ({j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa) = N - 2
    rw [Nat.card_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcardSubF, hΛaF]
    omega
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
  have hdimV : Module.finrank (ZMod p) V ≤ N - 1 := by
    have hfr := ggRC_finrank_le_of_fix (p := p) hxpow (ι := ι) (φ := Φ)
      (h := fun o : Idx => h (o.map Subtype.val id))
      (α := fun o : Idx => α (o.map Subtype.val id))
      (fun o w => hform (o.map Subtype.val id) w) hfixb
    have hc : Fintype.card Idx = N - 2 := by
      rw [← Nat.card_eq_fintype_card, hcardIdx]
    omega
  have hcardV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rwa [Nat.card_zmod] at h
  calc Nat.card ↥Bs = Nat.card V := card_eq_of_ggLin ι
    _ = p ^ Module.finrank (ZMod p) V := hcardV
    _ ≤ p ^ (N - 1) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hdimV

end CFSG.StandardType

end
