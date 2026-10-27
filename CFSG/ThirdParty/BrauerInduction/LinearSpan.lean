module

public import CFSG.ThirdParty.BrauerInduction.Span
public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Character.Span
public import CFSG.ThirdParty.BrauerInduction.Background.LinearChar.Clifford
public import CFSG.ThirdParty.BrauerInduction.Background.LinearChar.InducedCharacter

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Linear-character Brauer span

This file defines the integral span of characters induced from linear
characters of Brauer-elementary subgroups and proves that the Brauer character
span is contained in it.
-/

universe u

open BigOperators CategoryTheory

namespace CFSG.BrauerInduction

section BrauerSpanLin

/--
A generator for the linear-character Brauer span: a Brauer-elementary subgroup
together with a linear character of it.
-/
structure BrauerLinGen (k : Type u) [CommRing k] (G : Type u) [Group G] where
  protected H : Subgroup G
  protected hElem : IsBrauerElementary H
  protected ψ : H →* kˣ

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace BrauerLinGen

/--
The induced linear character attached to a generator of `BrauerSpanLin`.
-/
@[expose] noncomputable def inducedCharacter
  (i : BrauerLinGen k G) : ClassFun k G :=
    ClassFun.character (FDRep.indLin i.H i.ψ)

@[simp] lemma inducedCharacter_apply
    (i : BrauerLinGen k G) (g : G) :
    BrauerLinGen.inducedCharacter i g
      =
    (FDRep.indLin i.H i.ψ).character g := rfl

end BrauerLinGen

/--
The `ℤ`-span of characters induced from linear characters of Brauer-elementary
subgroups.
-/
@[expose] def BrauerSpanLin : Submodule ℤ (ClassFun k G) :=
  Submodule.span ℤ (Set.range (BrauerLinGen.inducedCharacter))

/--
Membership in `BrauerSpanLin` gives an explicit finite `ℤ`-linear combination
of induced linear characters.
-/
theorem BrauerSpanLin.exists_decomposition
    {χ : ClassFun k G}
    (hχ : χ ∈ BrauerSpanLin) :
    ∃ (ι : Type) (_ : Fintype ι)
      (ns : ι → ℤ) (Hs : ι → Subgroup G)
      (ψs : ∀ i, Hs i →* kˣ),
      (∀ i, IsBrauerElementary (Hs i)) ∧
      χ = ∑ i, (ns i) • ClassFun.character (FDRep.indLin (Hs i) (ψs i)) := by
  let P : ClassFun k G → Prop :=
    fun φ =>
      ∃ (ι : Type) (_ : Fintype ι)
        (ns : ι → ℤ) (Hs : ι → Subgroup G)
        (ψs : ∀ i, Hs i →* kˣ),
        (∀ i,  IsBrauerElementary (Hs i)) ∧
        φ = ∑ i, (ns i) • ClassFun.character (FDRep.indLin (Hs i) (ψs i))
  have hP : P χ := by
    refine Submodule.span_induction (p := fun φ _ => P φ) ?gen ?zero ?add ?smul hχ
    · intro φ hφ
      rcases hφ with ⟨i, rfl⟩
      refine ⟨PUnit, inferInstance,
        (fun _ => (1 : ℤ)), (fun _ => i.H), (fun _ => i.ψ), (fun _ => i.hElem), ?_⟩
      ext g
      simp [BrauerLinGen.inducedCharacter]
    · refine
        ⟨Empty, inferInstance, isEmptyElim, isEmptyElim, isEmptyElim, isEmptyElim, ?_⟩
      simp only [Finset.univ_eq_empty, zsmul_eq_mul, Finset.sum_empty]
    · intro x y _ _ hx hy
      rcases hx with ⟨ιx, _, nsx, Hsx, ψsx, hHx, rfl⟩
      rcases hy with ⟨ιy, _, nsy, Hsy, ψsy, hHy, rfl⟩
      refine
        ⟨Sum ιx ιy,
         inferInstance,
         Sum.elim nsx nsy,
         Sum.elim Hsx Hsy,
         (fun i => match i with | Sum.inl j => ψsx j | Sum.inr j => ψsy j),
         (fun i => match i with | Sum.inl j => hHx j | Sum.inr j => hHy j),
         ?_⟩
      simp only [zsmul_eq_mul, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    · intro n x _ hx
      rcases hx with ⟨ιx, _, nsx, Hsx, ψsx, hHx, rfl⟩
      refine ⟨ιx, inferInstance, (fun i => n * nsx i), Hsx, ψsx, hHx, ?_⟩
      rw [Finset.smul_sum]
      simp_rw [mul_smul]
  exact hP

/--
The character span is contained in the linear-character span.

The proof uses the fact that Brauer-elementary groups are nilpotent: every
simple representation of such a group is induced from a linear character of a
subgroup.  After decomposing an arbitrary character into irreducibles, induction
transitivity transports the resulting linear-character induction back to `G`.
-/
theorem BrauerSpanChar.le_BrauerSpanLin [IsAlgClosed k] [CharZero k] :
    BrauerSpanChar (k := k) (G := G) ≤ BrauerSpanLin := by
  rw [BrauerSpanChar, InducedCharacterSpan, Submodule.span_le]
  rintro φ ⟨H, hH_elem, V, rfl⟩
  haveI : Group.IsNilpotent H := hH_elem.isNilpotent
  haveI:  NeZero ↑(Nat.card ↥H) := ⟨One.natCard_ne_zero_of_finite H⟩
  have h_decomp : ClassFun.character V ∈
      Submodule.span ℤ { ψ | ∃ (S : FDRep k H)
    (_ : CategoryTheory.Simple S), ψ = ClassFun.character S } := by
    apply ClassFun.character_mem_span_irreducibles
  let P := fun (χ : ClassFun k H) =>
      ClassFun.ind H χ ∈ BrauerSpanLin
  refine Submodule.span_induction (p := fun χ _ => P χ)
      ?gen ?zero ?add ?smul h_decomp
  · rintro σ ⟨S, hS_simple, rfl⟩
    obtain ⟨K, ψ_lin, ⟨h_iso⟩⟩ :=
      FDRep.exists_indLin_of_nilpotent_simple (ρ := S)
    have h_char_eq :
        ClassFun.character S =
          ClassFun.character (FDRep.indLin K ψ_lin) :=
      ClassFun.char_eq_of_iso h_iso
    rw [h_char_eq]
    letI : DecidablePred fun x : G => x ∈ H := Classical.decPred _
    letI: Fintype G := Fintype.ofFinite G
    letI : Fintype H := H.instFintypeSubtypeMemOfDecidablePred
    rw [ClassFun.character_indLin (G := H) K ψ_lin]
    unfold P
    let K_G : Subgroup G := K.map H.subtype
    let eK : K ≃* K_G :=
      K.equivMapOfInjective H.subtype Subtype.coe_injective
    let ψ_lin_G : K_G →* kˣ :=
      ψ_lin.comp eK.symm.toMonoidHom
    have hK_elem : IsBrauerElementary K :=
      IsBrauerElementary.ofSubgroup hH_elem K
    have hK_G_elem : IsBrauerElementary K_G :=
      IsBrauerElementary.ofMulEquiv hK_elem eK
    have h_trans_direct :
    ClassFun.ind H
      (ClassFun.ind K
        (ClassFun.character (FDRep.ofLinearChar ψ_lin)))
      =
    ClassFun.ind K_G
      ((ClassFun.equivOfMulEquiv eK).symm
        (ClassFun.character (FDRep.ofLinearChar ψ_lin))) := by
      simpa [K_G, eK] using
        (ClassFun.ind_trans (K := H) (H := K)
          (ClassFun.character (FDRep.ofLinearChar ψ_lin)))
    rw [h_trans_direct]
    have h_char_lin_G :
        (ClassFun.equivOfMulEquiv eK).symm
            (ClassFun.character (FDRep.ofLinearChar ψ_lin))
          =
        ClassFun.character (FDRep.ofLinearChar ψ_lin_G) := by
      ext x
      rfl
    have h_indLin_G :
        ClassFun.character (FDRep.indLin K_G ψ_lin_G)
          =
        ClassFun.ind K_G
          ((ClassFun.equivOfMulEquiv eK).symm
            (ClassFun.character (FDRep.ofLinearChar ψ_lin))) := by
      calc
        ClassFun.character (FDRep.indLin K_G ψ_lin_G)
            =
          ClassFun.ind K_G
            (ClassFun.character (FDRep.ofLinearChar ψ_lin_G)) := by
              change
                ClassFun.character
                  (FDRep.ind K_G
                    (FDRep.ofLinearChar ψ_lin_G))
                  =
                ClassFun.ind K_G
                  (ClassFun.character (FDRep.ofLinearChar ψ_lin_G))
              exact
                ClassFun.char_ind K_G (FDRep.ofLinearChar ψ_lin_G)
        _ =
          ClassFun.ind K_G
            ((ClassFun.equivOfMulEquiv eK).symm
              (ClassFun.character (FDRep.ofLinearChar ψ_lin))) := by
                rw [h_char_lin_G]
    rw [← h_indLin_G]
    exact Submodule.subset_span
      ⟨{ H := K_G, hElem := hK_G_elem, ψ := ψ_lin_G }, rfl⟩
  · dsimp [P]
    rw [ClassFun.ind_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    dsimp [P]
    rw [ClassFun.ind_add]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    dsimp [P]
    rw [ClassFun.ind_zsmul n]
    exact Submodule.smul_mem _ n hx

end BrauerSpanLin
end CFSG.BrauerInduction
