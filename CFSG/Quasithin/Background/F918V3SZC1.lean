module

public import CFSG.Quasithin.Background.A1cModuleSub
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin

open scoped Pointwise commutatorElement

section Abstract

variable {A : Type*} [Group A] {P : Type*} [CommGroup P] [MulDistribMulAction A P]

theorem szc_eqvAut_comm_mod_fixed [Finite P] (hP : ∀ p : P, p ^ 2 = 1)
    (hirr : XMod.IsIrrSec A (XMod.fixed A (⊤ : Subgroup P)) ⊤) (φ ψ : XMod.eqvAut A P) (p : P) :
    (φ : MulAut P) ((ψ : MulAut P) p) * ((ψ : MulAut P) ((φ : MulAut P) p))⁻¹ ∈
      XMod.fixed A (⊤ : Subgroup P) := by
  have hsimple := XMod.isIrrSec_quotient hirr
  have hP' : ∀ q : P ⧸ XMod.fixed A (⊤ : Subgroup P), q ^ 2 = 1 := by
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    rw [← QuotientGroup.mk_pow, hP x, QuotientGroup.mk_one]
  obtain ⟨-, hfield, -⟩ := XMod.eqvEnd_isField_charTwo hP' hsimple
  let f : XMod.eqvAut A P → ↥(XMod.eqvEnd A (P ⧸ XMod.fixed A (⊤ : Subgroup P))) := fun χ =>
    ⟨MonoidHom.toAdditive (XMod.quotAut χ).toMonoidHom, XMod.mem_eqvEnd_iff.2 fun a q => by
      refine QuotientGroup.induction_on q fun x => ?_
      show XMod.quotAut χ (a • QuotientGroup.mk x) = a • XMod.quotAut χ (QuotientGroup.mk x)
      rw [XMod.smul_quotMk, XMod.quotAut_mk, XMod.quotAut_mk, XMod.smul_quotMk, χ.2 a x]⟩
  have h := hfield.mul_comm (f φ) (f ψ)
  have h1 := congrArg (fun e : ↥(XMod.eqvEnd A (P ⧸ XMod.fixed A (⊤ : Subgroup P))) =>
    Additive.toMul ((e : AddMonoid.End (Additive (P ⧸ XMod.fixed A (⊤ : Subgroup P))))
      (Additive.ofMul (QuotientGroup.mk p)))) h
  have h2 : (QuotientGroup.mk ((φ : MulAut P) ((ψ : MulAut P) p)) :
      P ⧸ XMod.fixed A (⊤ : Subgroup P)) =
        QuotientGroup.mk ((ψ : MulAut P) ((φ : MulAut P) p)) := by
    rw [← XMod.quotAut_mk, ← XMod.quotAut_mk, ← XMod.quotAut_mk, ← XMod.quotAut_mk]
    exact h1
  rw [QuotientGroup.eq] at h2
  have h3 := inv_mem h2
  rwa [mul_inv_rev, inv_inv, mul_comm] at h3

end Abstract

variable {W : Type} [CommGroup W] [Finite W]

theorem sz_trivial_mod_fix {D L : Subgroup (MulAut W)} {U : Subgroup W}
    (hV : ∀ w : W, w ^ 2 = 1) (hU : XMod.IsIrrPlus ↥D U) (hperf : ⁅L, L⁆ = L)
    (hDL : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d) (hLU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) :
    ∀ l ∈ L, ∀ u ∈ U, l u * u⁻¹ ∈ fixV D := by
  have hstab : ∀ l ∈ L, l ∈ stabSub U := by
    intro l hl u
    refine ⟨fun h => ?_, fun h => hLU l hl u h⟩
    have := hLU l⁻¹ (L.inv_mem hl) _ h
    simpa using this
  let _ := XMod.subAction hU.1
  have hP : ∀ p : ↥U, p ^ 2 = 1 := fun p => Subtype.ext (hV p)
  have hirr := XMod.isIrrSec_subAction hU.1 hU.2.2
  have haut : ∀ (l : MulAut W) (hl : l ∈ L),
      resHom U ⟨l, hstab l hl⟩ ∈ XMod.eqvAut ↥D ↥U := by
    intro l hl
    rw [XMod.mem_eqvAut_iff]
    intro a p
    refine Subtype.ext ?_
    show l ((a : MulAut W) (p : W)) = (a : MulAut W) (l (p : W))
    exact (congrArg (fun φ : MulAut W => φ (p : W)) (hDL a a.2 l hl)).symm
  have hcomm_mod : ∀ l₁ ∈ L, ∀ l₂ ∈ L, ∀ u ∈ U, l₁ (l₂ u) * (l₂ (l₁ u))⁻¹ ∈ fixV D := by
    intro l₁ hl₁ l₂ hl₂ u hu d hd
    have key := szc_eqvAut_comm_mod_fixed hP hirr ⟨_, haut l₁ hl₁⟩ ⟨_, haut l₂ hl₂⟩ ⟨u, hu⟩
    exact congrArg Subtype.val (key.2 ⟨d, hd⟩)
  let N : Subgroup (MulAut W) :=
    { carrier := {g | g ∈ L ∧ ∀ u ∈ U, g u * u⁻¹ ∈ fixV D}
      one_mem' := ⟨L.one_mem, fun u _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haL, ha⟩ ⟨hbL, hb⟩
        refine ⟨L.mul_mem haL hbL, fun u hu => ?_⟩
        have e : (a * b) u * u⁻¹ = (a (b u) * (b u)⁻¹) * (b u * u⁻¹) := by
          simp [MulAut.mul_apply]
        rw [e]
        exact (fixV D).mul_mem (ha (b u) (hLU b hbL u hu)) (hb u hu)
      inv_mem' := by
        rintro a ⟨haL, ha⟩
        refine ⟨L.inv_mem haL, fun u hu => ?_⟩
        have e : a⁻¹ u * u⁻¹ = (a (a⁻¹ u) * (a⁻¹ u)⁻¹)⁻¹ := by
          simp
        rw [e]
        exact (fixV D).inv_mem (ha (a⁻¹ u) (hLU a⁻¹ (L.inv_mem haL) u hu)) }
  have hN : ⁅L, L⁆ ≤ N := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨g, hg, h, hh, rfl⟩
    refine ⟨L.mul_mem (L.mul_mem (L.mul_mem hg hh) (L.inv_mem hg)) (L.inv_mem hh),
      fun u hu => ?_⟩
    have hu' : g⁻¹ (h⁻¹ u) ∈ U := hLU _ (L.inv_mem hg) _ (hLU _ (L.inv_mem hh) _ hu)
    have key := hcomm_mod g hg h hh _ hu'
    have e : ⁅g, h⁆ u * u⁻¹ = g (h (g⁻¹ (h⁻¹ u))) * (h (g (g⁻¹ (h⁻¹ u))))⁻¹ := by
      simp [commutatorElement_def, MulAut.mul_apply]
    rw [e]
    exact key
  intro l hl u hu
  exact (hN (by rw [hperf]; exact hl)).2 u hu

end CFSG.Quasithin
