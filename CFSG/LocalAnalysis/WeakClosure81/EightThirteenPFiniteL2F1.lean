module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShapes

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open Equiv
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3 IsL3 IsSp4 IsSL3)

private noncomputable def wc813fl2_conjAut {Y : Type} [Group Y] (L : Subgroup Y) (b : Y)
    (hb : b ∈ normalizer (L : Set Y)) : MulAut ↥L :=
  ((MulAut.conj b).subgroupMap L).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp hb))

@[simp] private theorem wc813fl2_conjAut_apply {Y : Type} [Group Y] (L : Subgroup Y) (b : Y)
    (hb : b ∈ normalizer (L : Set Y)) (l : ↥L) :
    (wc813fl2_conjAut L b hb l : Y) = b * (l : Y) * b⁻¹ := by
  simp only [wc813fl2_conjAut, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]

private theorem wc813fl2_exists_perm_of_mulAut {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) (ξ : MulAut X) :
    ∃ ζ : Perm (Fin 5), ∀ q : X,
      (e (ξ q) : Perm (Fin 5)) = ζ * (e q : Perm (Fin 5)) * ζ⁻¹ := by
  have hsurj : Function.Surjective
      (MulAut.conjNormal (H := alternatingGroup (Fin 5)) :
        Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5))) :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
      (by decide) (by decide)).2
  obtain ⟨ζ, hζ⟩ := hsurj (MulAut.congr e ξ)
  refine ⟨ζ, fun q => ?_⟩
  have h := congrArg (fun ψ : MulAut (alternatingGroup (Fin 5)) =>
      ((ψ (e q) : alternatingGroup (Fin 5)) : Perm (Fin 5))) hζ
  simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h
  exact h.symm

private theorem wc813fl2_alt5_outer_involution :
    ∀ σ : Perm (Fin 5), σ * σ = 1 → Perm.sign σ = -1 →
      ∃ x : ↥(alternatingGroup (Fin 5)),
        (x : Perm (Fin 5)) * σ = σ * x ∧ x * x ≠ 1 := by
  decide +kernel

theorem wc813fl2_involutionCentralizerOn_L2 :
    InvolutionCentralizerOn ShapeL2 := by
  intro Y _ _ L b hL hb hb2 hx
  obtain ⟨-, hL2⟩ := hL
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model ↥L
    (show CFSG.Blueprint.LieModel ↥L .PSL 2 2 2 from hL2)
  have hZ5 : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hcenter : Subgroup.center ↥L = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [hZ5] at hmap
    have hker : (e : ↥L →* alternatingGroup (Fin 5)).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr e.injective
    rw [Subgroup.map_eq_bot_iff, hker, le_bot_iff] at hmap
    exact hmap
  set β : MulAut ↥L := wc813fl2_conjAut L b hb with hβdef
  have hβ_apply : ∀ l : ↥L, (β l : Y) = b * (l : Y) * b⁻¹ := by
    intro l
    rw [hβdef]
    exact wc813fl2_conjAut_apply L b hb l
  have hβ2 : β * β = 1 := by
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    simp only [MulAut.mul_apply, MulAut.one_apply, hβdef, wc813fl2_conjAut_apply]
    rw [show b * (b * (l : Y) * b⁻¹) * b⁻¹ = (b * b) * (l : Y) * (b * b)⁻¹ by group, hb2]
    simp
  obtain ⟨ζ, hζ⟩ := wc813fl2_exists_perm_of_mulAut e β
  by_cases hζA : ζ ∈ alternatingGroup (Fin 5)
  ·
    let sL : ↥L := e.symm ⟨ζ, hζA⟩
    have hβs : β = MulAut.conj sL := by
      apply MulEquiv.ext
      intro l
      apply e.injective
      apply Subtype.ext
      rw [hζ l]
      simp [sL, MulAut.conj_apply]
    have hs2center : sL * sL ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hβg : β (β g) = g := by
        have h1 := congrArg (fun φ : MulAut ↥L => φ g) hβ2
        simpa using h1
      rw [hβs] at hβg
      have hval : (sL : Y) * ((sL : Y) * (g : Y) * (sL : Y)⁻¹) * (sL : Y)⁻¹ = (g : Y) := by
        have := congrArg (Subtype.val) hβg
        simpa [MulAut.conj_apply] using this
      have h2 : (sL : Y) * (sL : Y) * (g : Y) * ((sL : Y) * (sL : Y))⁻¹ = (g : Y) := by
        rw [show (sL : Y) * (sL : Y) * (g : Y) * ((sL : Y) * (sL : Y))⁻¹
            = (sL : Y) * ((sL : Y) * (g : Y) * (sL : Y)⁻¹) * (sL : Y)⁻¹ by group]
        exact hval
      have h3 : (sL : Y) * (sL : Y) * (g : Y) = (g : Y) * ((sL : Y) * (sL : Y)) := by
        calc (sL : Y) * (sL : Y) * (g : Y)
            = (sL : Y) * (sL : Y) * (g : Y) * ((sL : Y) * (sL : Y))⁻¹
                * ((sL : Y) * (sL : Y)) := by group
          _ = (g : Y) * ((sL : Y) * (sL : Y)) := by rw [h2]
      exact h3.symm
    have hs2L : sL * sL = 1 := by
      have hmem : sL * sL ∈ (⊥ : Subgroup ↥L) := by
        rw [← hcenter]
        exact hs2center
      simpa using hmem
    have hs2Y : (sL : Y) * (sL : Y) = 1 := by
      have := congrArg (Subtype.val) hs2L
      simpa using this
    have hconj_eq : ∀ xL : ↥L,
        b * (xL : Y) * b⁻¹ = (sL : Y) * (xL : Y) * (sL : Y)⁻¹ := by
      intro xL
      have h1 : β xL = (MulAut.conj sL) xL := by rw [hβs]
      have h2 : ((β xL : ↥L) : Y) = (((MulAut.conj sL) xL : ↥L) : Y) :=
        congrArg Subtype.val h1
      simpa [hβdef, MulAut.conj_apply] using h2
    refine ⟨(sL : Y), sL.2, hs2Y, (sL : Y)⁻¹ * b, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro x hxL
      have h' : (sL : Y)⁻¹ * b * x = x * ((sL : Y)⁻¹ * b) := by
        calc (sL : Y)⁻¹ * b * x
            = (sL : Y)⁻¹ * (b * x * b⁻¹) * b := by group
          _ = (sL : Y)⁻¹ * ((sL : Y) * x * (sL : Y)⁻¹) * b := by
              rw [hconj_eq ⟨x, hxL⟩]
          _ = x * ((sL : Y)⁻¹ * b) := by group
      exact h'.symm
    · show b = (sL : Y) * ((sL : Y)⁻¹ * b)
      group
  ·
    exfalso
    have hζsign : Perm.sign ζ = -1 := by
      rcases Int.units_eq_one_or (Perm.sign ζ) with h | h
      · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) hζA
      · exact h
    have hζ2A : ζ * ζ ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, hζsign]
      decide
    have hζsq : ζ * ζ = 1 := by
      have hcenter5 : (⟨ζ * ζ, hζ2A⟩ : alternatingGroup (Fin 5)) ∈
          Subgroup.center (alternatingGroup (Fin 5)) := by
        rw [Subgroup.mem_center_iff]
        intro a
        apply Subtype.ext
        obtain ⟨q, rfl⟩ := e.surjective a
        have hβg : β (β q) = q := by
          have h1 := congrArg (fun φ : MulAut ↥L => φ q) hβ2
          simpa using h1
        have hqq : (e q : Perm (Fin 5)) = ζ * (ζ * (e q : Perm (Fin 5)) * ζ⁻¹) * ζ⁻¹ := by
          have h2 : e (β (β q)) = e q := by rw [hβg]
          calc (e q : Perm (Fin 5)) = (e (β (β q)) : Perm (Fin 5)) := by rw [h2]
            _ = ζ * (e (β q) : Perm (Fin 5)) * ζ⁻¹ := hζ (β q)
            _ = ζ * (ζ * (e q : Perm (Fin 5)) * ζ⁻¹) * ζ⁻¹ := by rw [hζ q]
        calc (e q : Perm (Fin 5)) * (ζ * ζ)
            = (ζ * (ζ * (e q : Perm (Fin 5)) * ζ⁻¹) * ζ⁻¹) * (ζ * ζ) := by
              nth_rewrite 1 [hqq]
              rfl
          _ = (ζ * ζ) * (e q : Perm (Fin 5)) := by group
      rw [hZ5] at hcenter5
      have h1 : (⟨ζ * ζ, hζ2A⟩ : alternatingGroup (Fin 5)) = 1 := by
        simpa using hcenter5
      have h2 := congrArg (Subtype.val) h1
      simpa using h2
    obtain ⟨x, hxcomm, hxne⟩ := wc813fl2_alt5_outer_involution ζ hζsq hζsign
    let xL : ↥L := e.symm x
    have hxLfix : β xL = xL := by
      apply e.injective
      apply Subtype.ext
      rw [hζ xL]
      have hxe : e xL = x := by simp [xL]
      rw [hxe, ← hxcomm]
      group
    have hbcommL : b * (xL : Y) = (xL : Y) * b := by
      have h := hβ_apply xL
      rw [hxLfix] at h
      calc b * (xL : Y) = (b * (xL : Y) * b⁻¹) * b := by group
        _ = (xL : Y) * b := by rw [h.symm]
    have hxLsq_center : xL * xL ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have hl := hx (xL : Y) xL.2 hbcommL.symm (l : Y) l.2
      exact hl.symm
    have hxLsq1 : xL * xL = 1 := by
      have hmem : xL * xL ∈ (⊥ : Subgroup ↥L) := by
        rw [← hcenter]
        exact hxLsq_center
      simpa using hmem
    have hxx1 : x * x = 1 := by
      have h := congrArg e hxLsq1
      rw [map_mul, map_one] at h
      have hxe : e xL = x := by simp [xL]
      rwa [hxe] at h
    exact hxne hxx1

end CFSG.LocalAnalysis.WeakClosure81

end
