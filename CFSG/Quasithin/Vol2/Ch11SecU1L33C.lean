module

public import CFSG.Quasithin.Vol2.Ch11SecU1L33B
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IV
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IT

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L33

open CFSG.QuasithinUnique.Vol2Native.L239.L33Insp CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.E2P.Asc80 L3I
open scoped MatrixGroups

theorem proj_injective : Function.Injective (proj 3 (ZMod 3)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨c, hc3, hcx⟩ := proj_eq_one_iff.mp hx
  have hc : c = 1 := by
    have h2 : c ^ 2 = 1 := ZMod.units_pow_card_sub_one_eq_one 3 c
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, h2, inv_one, one_mul]
  apply Subtype.ext
  rw [hcx, hc]
  simp

@[expose] noncomputable def projEquiv : S3 ≃* projectiveSL 3 (ZMod 3) :=
  MulEquiv.ofBijective (proj 3 (ZMod 3)) ⟨proj_injective, proj_surjective 3 (ZMod 3)⟩

theorem projEquiv_apply (x : S3) : projEquiv x = proj 3 (ZMod 3) x := rfl

theorem conjAut_inner (A : GL (Fin 3) (ZMod 3)) :
    ∃ g : projectiveSL 3 (ZMod 3), LinearFlag.conjAut 3 (ZMod 3) A = MulAut.conj g := by
  have hd : (Matrix.GeneralLinearGroup.det A) ^ 2 = 1 :=
    ZMod.units_pow_card_sub_one_eq_one 3 _
  have hdet : ((A : Matrix (Fin 3) (Fin 3) (ZMod 3)) ^ 2).det = 1 := by
    rw [Matrix.det_pow]
    have := congrArg Units.val hd
    simpa using this
  set B : S3 := ⟨(A : Matrix (Fin 3) (Fin 3) (ZMod 3)) ^ 2, hdet⟩ with hB
  have hAB : A ^ 2 = Matrix.SpecialLinearGroup.toGL B := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Matrix.SpecialLinearGroup.coe_GL_coe_matrix])
  refine conjAut_inner_of_pow_inner A (k := 1) (g := proj 3 (ZMod 3) B) ?_
  rw [pow_one, ← map_pow, hAB, conjAut_toGL]

theorem aut_cases (β : MulAut (projectiveSL 3 (ZMod 3))) :
    ∃ g : projectiveSL 3 (ZMod 3), β = MulAut.conj g ∨
      β = MulAut.conj g * LinearFlag.dualAut 3 (ZMod 3) := by
  have := zmod_ringEquiv_subsingleton 3
  obtain ⟨A, σ, ε, hε, hβA⟩ := (automorphism_generation (n := 3) (K := ZMod 3) le_rfl).2 β
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst hσ
  obtain ⟨g, hg⟩ := conjAut_inner A
  refine ⟨g, ?_⟩
  interval_cases ε
  · left
    simpa [hg] using hβA
  · right
    simpa [hg] using hβA

variable {G : Type} [Group G]

theorem exists_model {L : Subgroup G} [L.Normal] (hC : Subgroup.centralizer (L : Set G) = ⊥)
    (e : ↥L ≃* PSL3 3) (hGL : ∃ t : G, t ∉ L) : Nonempty (Model L) := by
  set ψ := e.trans (psl3EquivP 3) with hψ
  set f : S3 →* G := L.subtype.comp (ψ.symm.toMonoidHom.comp projEquiv.toMonoidHom) with hf
  have hfinj : Function.Injective f :=
    L.subtype_injective.comp (ψ.symm.injective.comp projEquiv.injective)
  have hfx : ∀ x : S3, f x = ((ψ.symm (projEquiv x) : ↥L) : G) := fun x => rfl
  set β : G →* MulAut (projectiveSL 3 (ZMod 3)) :=
    (MulAut.congr ψ).toMonoidHom.comp MulAut.conjNormal with hβ
  have hβapp : ∀ g x, β g x = ψ (MulAut.conjNormal g (ψ.symm x)) := fun g x => by
    simp [hβ, MulAut.congr_apply]
  have hβL : ∀ g y, β g = MulAut.conj y → g ∈ L := fun g y hy => mem_of_congr_eq_conj hC ψ hy
  have hβ1 : ∀ g, β g = 1 → g = 1 := by
    intro g hg
    have hg' : g ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := hβapp g (ψ ⟨l, hl⟩)
      rw [hg, MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
      have h2 := congrArg (fun y => ((ψ.symm y : ↥L) : G)) h1
      simp only [MulEquiv.symm_apply_apply, MulAut.conjNormal_apply] at h2
      calc l * g = (g * l * g⁻¹) * g := by rw [← h2]
        _ = g * l := by group
    rw [hC] at hg'
    exact Subgroup.mem_bot.mp hg'
  have hβf : ∀ x : S3, β (f x) = MulAut.conj (projEquiv x) := fun x => by
    have h1 : MulAut.conjNormal (f x) = MulAut.conj (ψ.symm (projEquiv x)) :=
      MulAut.conjNormal_val (h := ψ.symm (projEquiv x))
    show MulAut.congr ψ (MulAut.conjNormal (f x)) = _
    rw [h1, congr_conj, MulEquiv.apply_symm_apply]
  obtain ⟨t₀, ht₀⟩ := hGL
  obtain ⟨g₀, hg₀ | hg₀⟩ := aut_cases (β t₀)
  · exact absurd (hβL t₀ g₀ hg₀) ht₀
  set t := (f (projEquiv.symm g₀))⁻¹ * t₀ with ht
  have hβt : β t = LinearFlag.dualAut 3 (ZMod 3) := by
    rw [ht, map_mul, map_inv, hβf, MulEquiv.apply_symm_apply, hg₀, inv_mul_cancel_left]
  have hδδ : LinearFlag.dualAut 3 (ZMod 3) * LinearFlag.dualAut 3 (ZMod 3) = 1 :=
    (standard_automorphism_transport (n := 3) (K := ZMod 3)).2.2.2.1
  have htt : t * t = 1 := hβ1 _ (by rw [map_mul, hβt, hδδ])
  have hfL : ∀ x, f x ∈ L := fun x => (ψ.symm (projEquiv x)).2
  have htL : t ∉ L := fun h => ht₀ (by
    have h1 := L.mul_mem (hfL (projEquiv.symm g₀)) h
    rwa [ht, mul_inv_cancel_left] at h1)
  have hmem : ∀ g, g ∈ L ↔ ∃ x, f x = g := fun g =>
    ⟨fun hg => ⟨projEquiv.symm (ψ ⟨g, hg⟩), by
      rw [hfx, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]⟩,
     fun ⟨x, hx⟩ => hx ▸ hfL x⟩
  have htf : ∀ x, t * f x = f (delta x) * t := by
    intro x
    have h1 : β t (projEquiv x) = projEquiv (delta x) := by
      rw [hβt, projEquiv_apply, projEquiv_apply, dualAut_proj]
      rfl
    rw [hβapp] at h1
    have h2 := congrArg (fun y => ((ψ.symm y : ↥L) : G)) h1
    simp only [MulEquiv.symm_apply_apply, MulAut.conjNormal_apply] at h2
    rw [hfx, hfx, ← h2]
    group
  have hcover : ∀ g, ∃ x, g = f x ∨ g = f x * t := by
    intro g
    by_cases hg : g ∈ L
    · obtain ⟨x, hx⟩ := (hmem g).mp hg
      exact ⟨x, Or.inl hx.symm⟩
    · obtain ⟨g₁, hg₁ | hg₁⟩ := aut_cases (β g)
      · exact absurd (hβL g g₁ hg₁) hg
      have hgt : g * t ∈ L := hβL _ g₁ (by rw [map_mul, hg₁, hβt, mul_assoc, hδδ, mul_one])
      obtain ⟨x, hx⟩ := (hmem _).mp hgt
      refine ⟨x, Or.inr ?_⟩
      rw [hx, mul_assoc, htt, mul_one]
  exact ⟨⟨f, hfinj, hmem, t, htt, htL, htf, hcover⟩⟩

end CFSG.Quasithin.Vol2.Ch11.SecU1.L33
