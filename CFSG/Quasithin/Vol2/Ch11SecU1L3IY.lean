module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IX
public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IQ
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IV

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  CFSG.QuasithinUnique.Ch1 CFSG.Quasithin.E2P.Asc80
open scoped MatrixGroups

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

theorem sigmaFacts_L3 (hp : 5 ≤ p) {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) (e : ↥L ≃* PSL3 p) {b : G} (hbL : b ∉ L)
    (hb2 : orderOf b = 2) : SigmaFacts L b := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨A, hA, hβ⟩ := exists_graph_of_outer hp2 hC e hbL hb2
  set ψ := e.trans (psl3EquivP p) with hψ
  set f : projectiveSL 3 (ZMod p) →* G := L.subtype.comp ψ.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := L.subtype_injective.comp ψ.symm.injective
  have hfψ : ∀ (x : G) (hx : x ∈ L), f (ψ ⟨x, hx⟩) = x := fun x hx => by simp [hf]
  set R := ((A⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) with hR
  have hRt : Rᵀ = R := transpose_inv_of_transpose_eq' A hA
  have hRd : R.det ≠ 0 := GeneralLinearGroup.det_ne_zero _
  have hR0 : R ≠ 0 := fun h => hRd (by rw [h]; exact Matrix.det_zero)
  have hfix : ∀ x, b * f x * b⁻¹ = f x ↔
      (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p)) x = x := by
    intro x
    have hβx : (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p)) x =
        ψ (MulAut.conjNormal b (ψ.symm x)) := by
      rw [← hβ]
      rfl
    rw [hβx]
    constructor
    · intro h
      apply ψ.symm.injective
      rw [MulEquiv.symm_apply_apply]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact h
    · intro h
      have h1 := congrArg (fun y => ((ψ.symm y : ↥L) : G)) h
      simp only [MulEquiv.symm_apply_apply, MulAut.conjNormal_apply] at h1
      exact h1
  set F := f.comp (proj 3 (ZMod p)) with hF
  set H := L ⊓ Subgroup.centralizer ({b} : Set G) with hH
  have hLC : H = (soForm R).map F := by
    ext g
    constructor
    · rintro ⟨hgL, hgC⟩
      have hgb := Subgroup.mem_centralizer_singleton_iff.mp hgC
      obtain ⟨x, hx⟩ : ∃ x, f x = g := ⟨ψ ⟨g, hgL⟩, hfψ g hgL⟩
      have hxf : (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p)) x = x := by
        refine (hfix x).mp ?_
        rw [hx]
        calc b * g * b⁻¹ = g * b * b⁻¹ := by rw [hgb]
          _ = g := by group
      obtain ⟨s, hs⟩ := (fixed_iff_mem_range_soProj hA x).mp hxf
      refine ⟨s, s.2, ?_⟩
      have h1 : F s = f (soProj R s) := rfl
      rw [h1, hs, hx]
    · rintro ⟨s, hs, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨(ψ.symm (proj 3 (ZMod p) s)).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx : (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p))
          (proj 3 (ZMod p) s) = proj 3 (ZMod p) s :=
        (fixed_iff_mem_range_soProj hA _).mpr ⟨⟨s, hs⟩, rfl⟩
      have h1 := (hfix _).mpr hx
      have h2 : F s = f (proj 3 (ZMod p) s) := rfl
      rw [h2]
      calc f (proj 3 (ZMod p) s) * b = (b * f (proj 3 (ZMod p) s) * b⁻¹) * b := by rw [h1]
        _ = b * f (proj 3 (ZMod p) s) := by group
  set W : Subgroup SL(3, ZMod p) := ⁅soForm R, soForm R⁆ with hW
  have hL₀ : ⁅H, H⁆ = W.map F := by rw [hLC, ← Subgroup.map_commutator]
  have hFW : Function.Injective (F.comp W.subtype) := by
    intro a a' h
    have h0 : f (proj 3 (ZMod p) a) = f (proj 3 (ZMod p) a') := h
    have h1 : ((proj 3 (ZMod p)).comp W.subtype) a = ((proj 3 (ZMod p)).comp W.subtype) a' :=
      hfinj h0
    exact injective_proj_commutator_soForm hR0 h1
  have hrange : (F.comp W.subtype).range = W.map F := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨eW⟩ := nonempty_commutator_soForm_equiv hp hRt hRd
  let e₀ : ↥⁅H, H⁆ ≃* PSL(2, ZMod p) := (MulEquiv.subgroupCongr (hL₀.trans hrange.symm)).trans
    ((MonoidHom.ofInjective hFW).symm.trans eW)
  have : IsSimpleGroup PSL(2, ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
  have key : ∀ g ∈ Subgroup.centralizer ({b} : Set G), ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
    rintro g hg h ⟨hhL, hhC⟩
    have hgb : Commute g b := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hhb : Commute h b := Subgroup.mem_centralizer_singleton_iff.mp hhC
    exact ⟨‹L.Normal›.conj_mem h hhL g, Subgroup.mem_centralizer_singleton_iff.mpr
      ((hgb.mul_left hhb).mul_left hgb.inv_left).eq⟩
  refine ⟨⁅H, H⁆, ?_, e₀.isSimpleGroup, ?_, fun g hg => ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)
  · obtain ⟨a, a', haa⟩ := exists_ne_comm_psl2_zmod hp
    refine ⟨e₀.symm a, e₀.symm a', fun h => haa ?_⟩
    have h1 := congrArg e₀ h
    simpa using h1
  · apply mem_normalizer_commutator
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key g hg h, fun hh => ?_⟩
    have h1 := key g⁻¹ (Subgroup.inv_mem _ hg) _ hh
    simpa [mul_assoc] using h1
  · rw [eq_bot_iff]
    rintro l ⟨hlL, hlC⟩
    rw [Subgroup.mem_bot]
    obtain ⟨x, hx⟩ : ∃ x, f x = l := ⟨ψ ⟨l, hlL⟩, hfψ l hlL⟩
    have hx1 : x = 1 := by
      refine eq_one_of_commute_commutator_soForm hp hRt hRd fun ω hω => hfinj ?_
      have hω' : f (proj 3 (ZMod p) ω) ∈ ⁅H, H⁆ := by
        rw [hL₀]
        exact ⟨ω, hω, rfl⟩
      rw [map_mul, map_mul, hx]
      exact (Subgroup.mem_centralizer_iff.mp hlC _ hω').symm
    rw [← hx, hx1, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
