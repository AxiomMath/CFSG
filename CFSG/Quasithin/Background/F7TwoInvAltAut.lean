module

public import CFSG.Quasithin.Background.F7TwoInvAltMain
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.F7Two

open Equiv Equiv.Perm

theorem invAutGen_iff_invGen_range {L Γ : Type*} [Group L] [Group Γ] {f : L →* Γ}
    (hf : Function.Injective f) {a : Γ} {φ : MulAut L} (hφ : ∀ x, f (φ x) = a * f x * a⁻¹) :
    InvAutGen L φ ↔ InvGen f.range a := by
  have key : ∀ x : L, IsPGroup 2 ↥(Subgroup.zpowers (a * f x * a⁻¹ * (f x)⁻¹)) ↔
      IsPGroup 2 ↥(Subgroup.zpowers (φ x * x⁻¹)) := fun x => by
    rw [← hφ, ← map_inv, ← map_mul]
    simp only [isPGroup_zpowers_iff, ← map_pow, map_eq_one_iff f hf]
  have hset : f '' {x : L | ¬ IsPGroup 2 ↥(Subgroup.zpowers (φ x * x⁻¹))} =
      invXi f.range a := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, fun h => hx ((key x).1 h)⟩
    · rintro ⟨⟨x, rfl⟩, hy⟩
      exact ⟨x, fun h => hy ((key x).2 h), rfl⟩
  have hmap : (Subgroup.closure {x : L | ¬ IsPGroup 2 ↥(Subgroup.zpowers (φ x * x⁻¹))}).map f =
      Subgroup.closure (invXi f.range a) := by
    rw [MonoidHom.map_closure, hset]
  unfold InvAutGen InvGen
  rw [← hmap, ← Subgroup.map_top, (Subgroup.map_injective hf).eq_iff]

variable {L : Type*} [Group L] {n : ℕ}

theorem invAutGen_of_conj_alternatingGroup (e : L ≃* alternatingGroup (Fin n)) (hn : 5 ≤ n)
    {φ : MulAut L} {σ : Perm (Fin n)}
    (hσ : ∀ x : L, (e (φ x) : Perm (Fin n)) = σ * (e x : Perm (Fin n)) * σ⁻¹)
    (hφ : φ * φ = 1) (hφ1 : φ ≠ 1) : InvAutGen L φ := by
  let f : L →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hσσ : σ * σ = 1 := by
    refine GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
      (a₁ := σ * σ) (a₂ := 1) ?_
    refine MulEquiv.ext fun y => Subtype.ext ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    have h1 := hσ x
    have h2 := hσ (φ x)
    have h3 : e (φ (φ x)) = e x := by rw [← MulAut.mul_apply, hφ]; rfl
    rw [h3, h1] at h2
    simp only [map_mul, MulAut.mul_apply, MulAut.conjNormal_apply, map_one, MulAut.one_apply]
    simpa using h2.symm
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    refine hφ1 (MulEquiv.ext fun x => e.injective (Subtype.ext ?_))
    simpa using hσ x
  refine (invAutGen_iff_invGen_range hf (a := σ) (fun x => hσ x)).2 ?_
  have hrange : f.range = alternatingGroup (Fin n) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [f]⟩
  rw [hrange]
  exact invGen_alternatingGroup_fin hn hσσ hσ1

theorem invAutGen_of_mulEquiv_alternatingGroup (e : L ≃* alternatingGroup (Fin n)) (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (φ : MulAut L) (hφ : φ * φ = 1) (hφ1 : φ ≠ 1) : InvAutGen L φ := by
  obtain ⟨σ, hσ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).2
    (e.symm.trans (φ.trans e))
  refine invAutGen_of_conj_alternatingGroup e hn (σ := σ) (fun x => ?_) hφ hφ1
  have := congrArg (fun ψ : MulAut (alternatingGroup (Fin n)) =>
    ((ψ (e x) : alternatingGroup (Fin n)) : Perm (Fin n))) hσ
  simpa [MulAut.conjNormal_apply] using this.symm

end CFSG.Quasithin.F7Two
