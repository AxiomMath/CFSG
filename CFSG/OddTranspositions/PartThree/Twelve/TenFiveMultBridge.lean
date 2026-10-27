module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModel
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultQuad
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Aut
public import CFSG.Open.StatedDefs
public import CFSG.ClassicalInvolution.Balance.PassTwoConj
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Q3.ClassicalFundamentalModels
public import CFSG.ClassicalInvolution.Q3.Q3PlanParams
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Layer

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def fiveOrthogonal (k : ℕ) (ε : Bool) : Subgroup (GL (Fin (k + 1)) (ZMod 5)) where
  carrier := {g | ∀ x y, fiveForm k ε
    ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
    ((g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y}
  one_mem' := fun x y => by simp
  mul_mem' := fun {g h} hg hh x y => by
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [hg, hh]
  inv_mem' := fun {g} hg x y => by
    have h := hg (((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5))
      *ᵥ x) (((g⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y)
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h
    exact h.symm

@[expose] def fiveOmega (k : ℕ) (ε : Bool) : Subgroup (GL (Fin (k + 1)) (ZMod 5)) :=
  ⁅fiveOrthogonal k ε, fiveOrthogonal k ε⁆

theorem fiveOrthogonal_eq_comap_orthogonalGroup (k : ℕ) (ε : Bool) :
    fiveOrthogonal k ε =
      (TauCeti.QuadraticMap.orthogonalGroup (fiveQuad k ε)).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (k + 1)) (ZMod 5)).toMonoidHom := by
  have hQ : ⇑(fiveQuad k ε) = fun v : Fin (k + 1) → ZMod 5 => fiveForm k ε v v := by
    funext v
    exact fiveQuad_apply k ε v
  have hclosure : Subgroup.closure
      {A : GL (Fin (k + 1)) (ZMod 5) |
        ∀ v, fiveForm k ε ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v)
          ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ v) = fiveForm k ε v v} =
      fiveOrthogonal k ε := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro A hA x y
      have hpolar : QuadraticMap.polar (fiveQuad k ε)
          ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
          ((A : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) =
          QuadraticMap.polar (fiveQuad k ε) x y := by
        unfold QuadraticMap.polar
        simp only [fiveQuad_apply]
        rw [← Matrix.mulVec_add, hA (x + y), hA x, hA y]
      rw [polar_fiveQuad, polar_fiveQuad] at hpolar
      exact mul_left_cancel₀ two_ne_zero_five hpolar
    · intro A hA
      exact Subgroup.subset_closure fun v => hA v v
  rw [← hclosure,
    CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap (Q := fiveQuad k ε) hQ]

theorem fiveOrthogonal_le_closure_fiveReflections (k : ℕ) (ε : Bool) :
    fiveOrthogonal k ε ≤
      Subgroup.closure (fiveReflections k ε true ∪ fiveReflections k ε false) := by
  let S : Set (GL (Fin (k + 1)) (ZMod 5)) :=
    fiveReflections k ε true ∪ fiveReflections k ε false
  let e : GL (Fin (k + 1)) (ZMod 5) ≃*
      ((Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5)) :=
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (k + 1)) (ZMod 5)
  change fiveOrthogonal k ε ≤ Subgroup.closure S
  have hCD := CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_le_closure_reflect
    (Q := fiveQuad k ε) (V := Fin (k + 1) → ZMod 5) two_ne_zero_five
    (polarBilin_fiveQuad_nondegenerate k ε)
  have hgen : TauCeti.QuadraticMap.orthogonalGroup (fiveQuad k ε) ≤
      (Subgroup.closure S).map e.toMonoidHom := by
    rw [MonoidHom.map_closure]
    refine hCD.trans ((Subgroup.closure_le (Subgroup.closure (e '' S))).mpr ?_)
    rintro _ ⟨v, rfl⟩
    by_cases hv : fiveQuad k ε v = 0
    · rw [CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero hv]
      exact Subgroup.one_mem (Subgroup.closure (e '' S))
    · have hv' : fiveForm k ε v v ≠ 0 := by rwa [fiveQuad_apply] at hv
      by_cases hsq : IsSquare (fiveForm k ε v v)
      · have hmem : fiveReflOf k ε v ∈ S :=
          Or.inl (fiveReflOf_mem hv' (by simpa [hsq]))
        rw [reflect_fiveQuad_eq_toLinEquiv_fiveReflOf]
        exact Subgroup.subset_closure ⟨fiveReflOf k ε v, hmem, rfl⟩
      · have hmem : fiveReflOf k ε v ∈ S :=
          Or.inr (fiveReflOf_mem hv' (by simpa [hsq]))
        rw [reflect_fiveQuad_eq_toLinEquiv_fiveReflOf]
        exact Subgroup.subset_closure ⟨fiveReflOf k ε v, hmem, rfl⟩
  intro g hg
  rw [fiveOrthogonal_eq_comap_orthogonalGroup] at hg
  rcases Subgroup.mem_map.mp (hgen hg) with ⟨y, hy, hyeq⟩
  have : y = g := e.injective hyeq
  rwa [this] at hy

@[expose] def FiveSameClass (k : ℕ) (ε π : Bool) : Prop :=
  ∀ g h : GL (Fin (k + 1)) (ZMod 5), g ∈ fiveReflections k ε (!π) → h ∈ fiveReflections k ε (!π) →
    g * h ∈ fiveReflectionGroup k ε π

theorem fiveSameClass {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) : FiveSameClass k ε π :=
  fun _ _ hg hh => mul_mem_fiveReflectionGroup_of_mem_fiveReflections_not hk ε π hg hh

theorem fiveReflectionGroup_le_fiveOrthogonal (k : ℕ) (ε π : Bool) :
    fiveReflectionGroup k ε π ≤ fiveOrthogonal k ε := by
  intro g hg
  exact fiveForm_mulVec_of_mem hg

theorem fiveOmega_le_fiveReflectionGroup {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    (h0 : FiveSameClass k ε π) : fiveOmega k ε ≤ fiveReflectionGroup k ε π := by
  obtain ⟨t0, ht0⟩ := exists_mem_fiveReflections k hk ε (!π)
  have ht0O : t0 ∈ fiveOrthogonal k ε :=
    fiveReflectionGroup_le_fiveOrthogonal k ε (!π) (Subgroup.subset_closure ht0)
  have hconj : ∀ g ∈ fiveOrthogonal k ε, ∀ x ∈ fiveReflectionGroup k ε π,
      g * x * g⁻¹ ∈ fiveReflectionGroup k ε π := by
    intro g hg x hx
    refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ fiveReflectionGroup k ε π)
      ?_ ?_ ?_ ?_ hx
    · intro r hr
      exact Subgroup.subset_closure
        (conj_mem_fiveReflections (n := k) (ε := ε) (π := π) (g := g) hg hr)
    · simp
    · intro a b ha hb iha ihb
      rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
      exact mul_mem iha ihb
    · intro a ha iha
      rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
      exact inv_mem iha
  let G := ↥(fiveOrthogonal k ε)
  let N : Subgroup (GL (Fin (k + 1)) (ZMod 5)) := fiveReflectionGroup k ε π
  let N' : Subgroup G := N.subgroupOf (fiveOrthogonal k ε)
  let t : G := ⟨t0, ht0O⟩
  let H : Subgroup G := Subgroup.zpowers t
  haveI : N'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    change ((g * n * g⁻¹ : G) : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionGroup k ε π
    convert hconj g g.2 n hn using 1⟩
  have hmem_gen : ∀ (b : Bool) (s : GL (Fin (k + 1)) (ZMod 5)),
      s ∈ fiveReflections k ε b → s ∈ (N' ⊔ H).map (Subgroup.subtype (fiveOrthogonal k ε)) := by
    intro b s hs
    have hsO : s ∈ fiveOrthogonal k ε :=
      fiveReflectionGroup_le_fiveOrthogonal k ε b (Subgroup.subset_closure hs)
    refine Subgroup.mem_map.mpr ⟨⟨s, hsO⟩, ?_, rfl⟩
    have hb : b = π ∨ b = !π := by cases b <;> cases π <;> simp
    rcases hb with hb | hb
    · subst hb
      exact Subgroup.mem_sup_left
        (Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure hs))
    · subst hb
      have hst : s * t0 ∈ N := h0 s t0 hs ht0
      have hn : (⟨s * t0, mul_mem hsO ht0O⟩ : G) ∈ N' :=
        Subgroup.mem_subgroupOf.mpr hst
      have htinv : t⁻¹ ∈ H := Subgroup.inv_mem H (Subgroup.mem_zpowers t)
      have hmul : (⟨s * t0, mul_mem hsO ht0O⟩ : G) * t⁻¹ ∈ N' ⊔ H :=
        Subgroup.mul_mem_sup hn htinv
      have heq : (⟨s * t0, mul_mem hsO ht0O⟩ : G) * t⁻¹ = ⟨s, hsO⟩ := by
        apply Subtype.ext
        change (s * t0) * t0⁻¹ = s
        group
      rw [heq] at hmul
      exact hmul
  have hHN : N' ⊔ H = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hgS : (g : GL (Fin (k + 1)) (ZMod 5)) ∈
        Subgroup.closure (fiveReflections k ε true ∪ fiveReflections k ε false) :=
      fiveOrthogonal_le_closure_fiveReflections k ε g.2
    have hcl : Subgroup.closure (fiveReflections k ε true ∪ fiveReflections k ε false) ≤
        (N' ⊔ H).map (Subgroup.subtype (fiveOrthogonal k ε)) :=
      (Subgroup.closure_le _).mpr (fun s hs => by
        rcases hs with hs | hs
        · exact hmem_gen true s hs
        · exact hmem_gen false s hs)
    rcases Subgroup.mem_map.mp (hcl hgS) with ⟨y, hy, hyeq⟩
    have : y = g := Subtype.ext hyeq
    rwa [this] at hy
  have hcomm : _root_.commutator G ≤ N' :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hHN
      (Subgroup.zpowers_isMulCommutative t)
  calc fiveOmega k ε = (commutator G).map (Subgroup.subtype (fiveOrthogonal k ε)) :=
        (Subgroup.map_subtype_commutator (fiveOrthogonal k ε)).symm
    _ ≤ N'.map (Subgroup.subtype (fiveOrthogonal k ε)) := Subgroup.map_mono hcomm
    _ = N := Subgroup.map_subgroupOf_eq_of_le (fiveReflectionGroup_le_fiveOrthogonal k ε π)

theorem commutator_fiveOmega {k : ℕ} (hk : 4 ≤ k) (ε : Bool) :
    ⁅fiveOmega k ε, fiveOmega k ε⁆ = fiveOmega k ε := by
  have hperf := CFSG.LocalAnalysis.GLTheoremA.H81Orth.commutator_orthDerived_eq
    (K := ZMod 5) (U := Fin (k + 1) → ZMod 5)
    (by rw [Nat.card_eq_fintype_card, ZMod.card]; norm_num)
    (fiveQuad k ε) (polarBilin_fiveQuad_nondegenerate k ε)
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; omega)
  let e : GL (Fin (k + 1)) (ZMod 5) ≃*
      ((Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (Fin (k + 1) → ZMod 5)) :=
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin (k + 1)) (ZMod 5)
  have hcomap_comm : ∀ H : Subgroup ((Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5]
        (Fin (k + 1) → ZMod 5)),
      ⁅H.comap e.toMonoidHom, H.comap e.toMonoidHom⁆ = (⁅H, H⁆).comap e.toMonoidHom := by
    intro H
    simp only [Subgroup.comap_equiv_eq_map_symm' e]
    rw [← Subgroup.map_commutator]
  have hfive : fiveOmega k ε =
      (CFSG.RankThree.Classical2.orthDerived (fiveQuad k ε)).comap e.toMonoidHom := by
    simp only [fiveOmega, fiveOrthogonal_eq_comap_orthogonalGroup]
    change ⁅(TauCeti.QuadraticMap.orthogonalGroup (fiveQuad k ε)).comap e.toMonoidHom,
        (TauCeti.QuadraticMap.orthogonalGroup (fiveQuad k ε)).comap e.toMonoidHom⁆ =
      (CFSG.RankThree.Classical2.orthDerived (fiveQuad k ε)).comap e.toMonoidHom
    rw [hcomap_comm (TauCeti.QuadraticMap.orthogonalGroup (fiveQuad k ε))]
  simp only [hfive]
  rw [hcomap_comm (CFSG.RankThree.Classical2.orthDerived (fiveQuad k ε)), hperf]

theorem commutator_fiveReflectionGroup_eq_fiveOmega {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) :
    ⁅fiveReflectionGroup k ε π, fiveReflectionGroup k ε π⁆ = fiveOmega k ε := by
  have hRO := fiveReflectionGroup_le_fiveOrthogonal k ε π
  have hΩR := fiveOmega_le_fiveReflectionGroup hk ε π (fiveSameClass hk ε π)
  apply le_antisymm
  · exact Subgroup.commutator_mono hRO hRO
  · calc fiveOmega k ε = ⁅fiveOmega k ε, fiveOmega k ε⁆ := (commutator_fiveOmega hk ε).symm
      _ ≤ ⁅fiveReflectionGroup k ε π, fiveReflectionGroup k ε π⁆ :=
        Subgroup.commutator_mono hΩR hΩR

end CFSG.OddTranspositions.PartThree
