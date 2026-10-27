module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.SlotPat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bDiagram

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge

open Representation Module
open CFSG.Semidihedral.Principal CFSG.QuasithinUnique.Setup.X7b
open CFSG.Theory.Representation
open scoped TensorProduct

variable {k G : Type} [Field k] [Group G]
  {V : Type} [AddCommGroup V] [Module k V]

def FactorsFinrankLe (ρ : Representation k G V) (n : ℕ) : Prop :=
  ∀ (S : Type) [AddCommGroup S] [Module k S] [Module.Finite k S]
    (σ : Representation k G S), n < finrank k S → repMultiplicity ρ σ = 0

theorem factorsFinrankLe_of_exact
    {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module k V₁] [Module.Finite k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    [Module.Finite k V₃]
    {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
    {ρ₃ : Representation k G V₃} (f : IntertwiningMap ρ₁ ρ₂)
    (g : IntertwiningMap ρ₂ ρ₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : Function.Exact f g) {n : ℕ}
    (h₁ : FactorsFinrankLe ρ₁ n) (h₃ : FactorsFinrankLe ρ₃ n) :
    FactorsFinrankLe ρ₂ n := by
  intro S _ _ _ σ hS
  rw [repMultiplicity_eq_add_of_exact f g hf hg hex, h₁ S σ hS, h₃ S σ hS, zero_add]

theorem factorsFinrankLe_of_equiv {V' : Type} [AddCommGroup V'] [Module k V']
    {ρ : Representation k G V} {ρ' : Representation k G V'}
    (β : ρ.Equiv ρ') {n : ℕ} (h : FactorsFinrankLe ρ n) :
    FactorsFinrankLe ρ' n := by
  intro S _ _ _ σ hS
  rw [← repMultiplicity_congr_left β]
  exact h S σ hS

theorem factorsFinrankLe_of_finrank_le [Module.Finite k V]
    (ρ : Representation k G V) {n : ℕ} (hdim : finrank k V ≤ n) :
    FactorsFinrankLe ρ n := by
  classical
  intro S _ _ _ σ hS
  unfold repMultiplicity compositionMultiplicity
  split_ifs with hs
  · unfold factorCount
    apply Finset.card_eq_zero.mpr
    rw [Finset.filter_eq_empty_iff]
    intro i _ hfactor
    obtain ⟨β⟩ := hfactor
    let A := hs.choose i.succ
    let B := (hs.choose i.castSucc).comap A.subtype
    have : Module.Finite k ρ.asModule := inferInstanceAs (Module.Finite k V)
    have : Module.Finite k A := Module.Finite.of_injective
      (A.subtype.restrictScalars k) A.injective_subtype
    have hA : finrank k A ≤ finrank k ρ.asModule :=
      LinearMap.finrank_le_finrank_of_injective
        (f := A.subtype.restrictScalars k) A.injective_subtype
    have hB := Submodule.finrank_quotient_add_finrank (B.restrictScalars k)
    have hquot := (Submodule.Quotient.restrictScalarsEquiv k B).finrank_eq
    have hβ := (β.restrictScalars k).finrank_eq
    have hρ := ρ.asModuleEquiv.finrank_eq
    have hσ := σ.asModuleEquiv.finrank_eq
    change finrank k (A ⧸ B) = finrank k σ.asModule at hβ
    omega
  · rfl

theorem factorsFinrankLe_of_surjective [Module.Finite k V]
    {S : Type} [AddCommGroup S] [Module k S]
    {ρ : Representation k G V} {σ : Representation k G S}
    (f : IntertwiningMap ρ σ) (hf : Function.Surjective f) {n : ℕ}
    (h : FactorsFinrankLe ρ n) : FactorsFinrankLe σ n := by
  have : Module.Finite k S := Module.Finite.of_surjective f.toLinearMap hf
  let N : Subrepresentation ρ :=
    { toSubmodule := f.toLinearMap.ker
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        change f v = 0 at hv
        change f (ρ g v) = 0
        rw [f.isIntertwining, hv, map_zero] }
  have hex : Function.Exact (subIncl ρ N) f := by
    apply LinearMap.exact_iff.mpr
    change f.toLinearMap.ker = LinearMap.range N.toSubmodule.subtype
    rw [Submodule.range_subtype]
  intro T _ _ _ τ hT
  have hm := repMultiplicity_eq_add_of_exact (subIncl ρ N) f
    N.toSubmodule.injective_subtype hf hex τ
  rw [h T τ hT] at hm
  omega

theorem factorsFinrankLe_of_injective [Module.Finite k V]
    {S : Type} [AddCommGroup S] [Module k S]
    {ρ : Representation k G V} {σ : Representation k G S}
    (f : IntertwiningMap σ ρ) (hf : Function.Injective f) {n : ℕ}
    (h : FactorsFinrankLe ρ n) : FactorsFinrankLe σ n := by
  have : Module.Finite k S := Module.Finite.of_injective f.toLinearMap hf
  let N : Subrepresentation ρ :=
    { toSubmodule := LinearMap.range f.toLinearMap
      apply_mem_toSubmodule := by
        rintro g v ⟨w, rfl⟩
        exact ⟨σ g w, LinearMap.congr_fun (f.isIntertwining' g) w⟩ }
  have hex : Function.Exact f (quotProj ρ N) := by
    exact LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)
  intro T _ _ _ τ hT
  have hm := repMultiplicity_eq_add_of_exact f (quotProj ρ N) hf
    N.toSubmodule.mkQ_surjective hex τ
  rw [h T τ hT] at hm
  omega

theorem finrank_le_of_factorsFinrankLe [Module.Finite k V]
    (ρ : Representation k G V) (hirr : ρ.IsIrreducible) {n : ℕ}
    (h : FactorsFinrankLe ρ n) : finrank k V ≤ n := by
  by_contra hdim
  have hm := h V ρ (by omega)
  rw [repMultiplicity_of_isIrreducible hirr,
    if_pos ⟨Representation.Equiv.refl ρ⟩] at hm
  norm_num at hm

theorem factorsFinrankLe_pi [Module.Finite k V] {ι : Type} [Fintype ι]
    (ρ : ι → Representation k G V) {n : ℕ} (h : ∀ i, FactorsFinrankLe (ρ i) n) :
    FactorsFinrankLe (CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.piRep ρ) n := by
  intro S _ _ _ σ hS
  rw [CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.repMultiplicity_piRep]
  exact Finset.sum_eq_zero fun i _ => h i S σ hS

theorem factorsFinrankLe_comp [Module.Finite k V] {H : Type} [Group H]
    (ρ : Representation k G V) (φ : H →* G) {n : ℕ} (h : FactorsFinrankLe ρ n) :
    FactorsFinrankLe (ρ.comp φ) n := by
  have key : FactorsFinrankLe ρ n → FactorsFinrankLe (ρ.comp φ) n :=
    rep_induction (k := k) (G := G)
      (fun {V} _ _ _ ρ => FactorsFinrankLe ρ n → FactorsFinrankLe (ρ.comp φ) n)
      (fun {V} _ _ _ ρ hzero _ => by
        have : Subsingleton V := hzero
        apply factorsFinrankLe_of_finrank_le (ρ.comp φ) (n := n)
        rw [Module.finrank_zero_of_subsingleton]
        exact Nat.zero_le _)
      (fun {V} _ _ _ ρ hirr hρ =>
        factorsFinrankLe_of_finrank_le (ρ.comp φ) (finrank_le_of_factorsFinrankLe ρ hirr hρ))
      (fun {V} _ _ _ ρ A hA hQ hρ => by
        have hb : FactorsFinrankLe A.toRepresentation n :=
          factorsFinrankLe_of_injective (subIncl ρ A) A.toSubmodule.injective_subtype hρ
        have hq : FactorsFinrankLe A.quotient n :=
          factorsFinrankLe_of_surjective (quotProj ρ A) A.toSubmodule.mkQ_surjective hρ
        let f : IntertwiningMap (A.toRepresentation.comp φ) (ρ.comp φ) :=
          ⟨A.toSubmodule.subtype, fun _ => rfl⟩
        let g : IntertwiningMap (ρ.comp φ) (A.quotient.comp φ) :=
          ⟨A.toSubmodule.mkQ, fun _ => rfl⟩
        exact factorsFinrankLe_of_exact f g A.toSubmodule.injective_subtype
          A.toSubmodule.mkQ_surjective (LinearMap.exact_subtype_mkQ A.toSubmodule)
          (hA hb) (hQ hq))
      (finrank k V) ρ rfl
  exact key h

theorem factorsFinrankLe_of_comp_surjective [Module.Finite k V] {H : Type} [Group H]
    (ρ : Representation k G V) (π : H →* G) (hπ : Function.Surjective π) {n : ℕ}
    (h : FactorsFinrankLe (ρ.comp π) n) : FactorsFinrankLe ρ n := by
  intro S _ _ _ σ hS
  rw [← repMultiplicity_comp_surjective π hπ ρ σ]
  exact h S (σ.comp π) hS

theorem factorsFinrankLe_comp_conj [Module.Finite k V] {H : Type} [Group H]
    (ρ : Representation k G V) (π : H →* G) (g : G) {n : ℕ}
    (h : FactorsFinrankLe (ρ.comp π) n) :
    FactorsFinrankLe (ρ.comp ((MulAut.conj g).toMonoidHom.comp π)) n := by
  let β : Representation.Equiv (ρ.comp π) (ρ.comp ((MulAut.conj g).toMonoidHom.comp π)) :=
    Representation.Equiv.mk (repLinEquiv ρ g) fun a => by
      apply LinearMap.ext
      intro v
      simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
        LinearMap.comp_apply, LinearEquiv.coe_coe, repLinEquiv_apply]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
  exact factorsFinrankLe_of_equiv β h


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge
