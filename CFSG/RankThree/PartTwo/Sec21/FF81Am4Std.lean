module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am4Model
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6RefS
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.Hering214KSp6

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII (zH zCode mat6_zH)
open scoped MatrixGroups

namespace Am4

section Data

variable {G : Type} [Group G] [Finite G]

structure Data (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ : G) : Prop where
  h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀
  h42 : FF81Conc4_2 b₂ b₃
  h43 : FF81Conc4_3 L t₀
  hO3 : Opp 3 (Cen b) = ⊥

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ : G}

theorem Data.exists_cycle (hD : Data b L B b₁ b₂ b₃ t₀) :
    ∃ g : G, g * b₁ * g⁻¹ = b ∧ g * b₂ * g⁻¹ = b₁ ∧ g * b₃ * g⁻¹ = b₂ ∧ g * b * g⁻¹ = b₃ := by
  obtain ⟨-, -, -, -, ⟨c, -, hc0, hc1, hc2, hc3⟩⟩ := hD.h4.caseI.1.1
  refine ⟨c⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [← hc0]; group
  · rw [← hc1]; group
  · rw [← hc2]; group
  · rw [← hc3]; group

end Data

section Zeta


theorem mat6_nsElt (k : Fin 3) :
    mat6 (nsElt (K := ZMod 2) (n := 3) k) = dec6 (zCode k) := by
  rw [mat6_apply]
  change ((mat 3 (ZMod 2) (nsElt k)).submatrix ε6 ε6) = _
  rw [mat_nsElt]
  fin_cases k <;> decide

theorem zH_eq_nsElt (k : Fin 3) : zH k = nsElt (K := ZMod 2) (n := 3) k :=
  mat6_injective ((mat6_zH k).trans (mat6_nsElt k).symm)

end Zeta

section Std

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ : G}

theorem Data.exists_std
    (hD : Data b L B b₁ b₂ b₃ t₀) :
    ∃ f : K3 →* G, Function.Injective f ∧ f.range = L ∧
      f (nsElt 0) = b₃ ∧ f (nsElt 1) = b₂ ∧ f (nsElt 2) = b₁ := by
  have hB := hD.h4.basis
  have hset : ({b₃, b₂, b₁} : Set G) = {b₁, b₂, b₃} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hset' : ({b₃, b₃⁻¹, b₂, b₂⁻¹, b₁, b₁⁻¹} : Set G) = {b₁, b₁⁻¹, b₂, b₂⁻¹, b₃, b₃⁻¹} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hmono : ∀ n ∈ L, n ∈ Nor (Subgroup.closure {b₃, b₂, b₁}) → ∀ x ∈ ({b₃, b₂, b₁} : Set G),
      n * x * n⁻¹ ∈ ({b₃, b₃⁻¹, b₂, b₂⁻¹, b₁, b₁⁻¹} : Set G) := by
    rw [hset, hset']
    exact hB.monoL_stab
  have helem : IsElemAb 3 3 (Subgroup.closure {b₃, b₂, b₁}) := by
    rw [hset]; exact hB.elem
  obtain ⟨f, hf, hfL, e₁, e₂, e₃⟩ := Sp6RefS.exists_hom_std hB.hyp.model hB.hb₃ hB.hb₂ hB.hb₁
    helem hmono
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map]; exact hfL
  · rw [← zH_eq_nsElt]; exact e₁
  · rw [← zH_eq_nsElt]; exact e₂
  · rw [← zH_eq_nsElt]; exact e₃

end Std

structure ThetaData {G : Type} [Group G] (t₀ : G) (fL : K3 →* G) where
  Θ : ↥Pvec →* G
  inj : Function.Injective Θ
  cen : ∀ p, Θ p ∈ Cen t₀
  tvec : Θ ⟨tvec, tvec_mem_Pvec⟩ = t₀
  init : ∀ x : K3, Θ (initHom x) = fL x

theorem exists_thetaData {G : Type} [Group G] {L : Subgroup G} {t₀ : G} (hLC : L ≤ Cen t₀)
    {fL : K3 →* G} (hfinj : Function.Injective fL) (hfL : fL.range = L)
    (Θ : ↥Pvec ≃* ↥(Cen t₀)) (ht : (Θ ⟨tvec, tvec_mem_Pvec⟩ : G) = t₀)
    (hS : ∀ x : ↥Pvec, (x : K4) ∈ Svec ↔ (Θ x : G) ∈ L) : Nonempty (ThetaData t₀ fL) := by
  set Θ₀ : ↥Pvec →* G := (Cen t₀).subtype.comp Θ.toMonoidHom with hΘ₀
  have hΘ₀inj : Function.Injective Θ₀ := Subtype.val_injective.comp Θ.injective
  have hΘ₀cen : ∀ p, Θ₀ p ∈ Cen t₀ := fun p => (Θ p).2
  set θ : K3 →* G := Θ₀.comp initHom with hθ
  have hθinj : Function.Injective θ := hΘ₀inj.comp initHom_injective
  have hθrange : θ.range = L := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (hS (initHom x)).1 (by rw [coe_initHom]; exact initEmb_mem_Svec x)
    · intro l hl
      set p : ↥Pvec := Θ.symm ⟨l, hLC hl⟩ with hp
      have hpl : (Θ p : G) = l := by rw [hp, MulEquiv.apply_symm_apply]
      have hpS : (p : K4) ∈ Svec := (hS p).2 (by rw [hpl]; exact hl)
      obtain ⟨x, hx⟩ : ∃ x, initEmb x = (p : K4) := by
        rw [← range_initEmb] at hpS; exact hpS
      refine ⟨x, ?_⟩
      have hxp : initHom x = p := Subtype.ext hx
      show Θ₀ (initHom x) = l
      rw [hxp]; exact hpl
  have hrange : θ.range = fL.range := hθrange.trans hfL.symm
  let α : MulAut K3 := ((MonoidHom.ofInjective hθinj).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hfinj).symm
  have hα : ∀ x, fL (α x) = θ x := by
    intro x
    have := (MonoidHom.ofInjective hfinj).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hθinj x))
    exact congrArg Subtype.val this
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartTwo.Sec8.Hering611.exists_conj_eq_of_sp62
    CFSG.RankThree.PartTwo.Sec21.Hering214.statedModel_H6 α
  have hαc : ∀ x, α x = c * x * c⁻¹ := fun x => by rw [hc]; rfl
  have hγL : fL c ∈ L := hfL ▸ ⟨c, rfl⟩
  have hγC : fL c ∈ Cen t₀ := hLC hγL
  have hγt : fL c * t₀ = t₀ * fL c := Subgroup.mem_centralizer_singleton_iff.mp hγC
  have hθx : ∀ x, θ x = fL c * fL x * (fL c)⁻¹ := fun x => by
    rw [← hα, hαc, map_mul, map_mul, map_inv]
  refine ⟨{ Θ := (MulAut.conj (fL c)⁻¹).toMonoidHom.comp Θ₀
            inj := (MulAut.conj (fL c)⁻¹).injective.comp hΘ₀inj
            cen := fun p => ?_
            tvec := ?_
            init := fun x => ?_ }⟩
  · show (fL c)⁻¹ * Θ₀ p * (fL c)⁻¹⁻¹ ∈ Cen t₀
    exact (Cen t₀).mul_mem ((Cen t₀).mul_mem ((Cen t₀).inv_mem hγC) (hΘ₀cen p))
      ((Cen t₀).inv_mem ((Cen t₀).inv_mem hγC))
  · show (fL c)⁻¹ * Θ₀ ⟨tvec, tvec_mem_Pvec⟩ * (fL c)⁻¹⁻¹ = t₀
    have : Θ₀ ⟨tvec, tvec_mem_Pvec⟩ = t₀ := ht
    rw [this, inv_inv, mul_assoc, ← hγt, inv_mul_cancel_left]
  · show (fL c)⁻¹ * Θ₀ (initHom x) * (fL c)⁻¹⁻¹ = fL x
    have : Θ₀ (initHom x) = θ x := rfl
    rw [this, hθx, inv_inv]
    group

end Am4

end CFSG.RankThree.PartTwo.Sec21.FF81
