module

public import CFSG.Quasithin.Vol2.Ch10SecQ6L2b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open CFSG.Open

theorem exists_elem_aut {W : Type*} [Group W] {Λ : Subgroup (MulAut W)} {S : Type*} [Group S]
    [Finite S] (πs : S ≃* Λ)
    (hcen : ∀ x : MulAut W, x * x = 1 → (∀ l ∈ Λ, x * l = l * x) → x = 1)
    {E : Subgroup (MulAut W)} (hEN : E ≤ Subgroup.normalizer (Λ : Set (MulAut W)))
    (hEab : IsElemAbelian 2 E) :
    ∃ A : Subgroup (MulAut S), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a * a = 1) ∧
      Nat.card E ≤ Nat.card A := by
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE2 : ∀ a ∈ E, a * a = 1 := fun a ha => by
    rw [← sq]
    exact hEab.2 a ha
  let A : Subgroup (MulAut S) :=
    { carrier := {α | ∃ e ∈ E, ∀ M, (πs (α M) : MulAut W) = e * πs M * e⁻¹}
      one_mem' := ⟨1, E.one_mem, fun M => by simp⟩
      mul_mem' := by
        rintro α β ⟨e, he, hα⟩ ⟨f, hf, hβ⟩
        exact ⟨e * f, E.mul_mem he hf, fun M => by
          rw [MulAut.mul_apply, hα, hβ]
          group⟩
      inv_mem' := by
        rintro α ⟨e, he, hα⟩
        refine ⟨e⁻¹, E.inv_mem he, fun M => ?_⟩
        have h1 := hα (α⁻¹ M)
        rw [MulAut.apply_inv_self] at h1
        rw [h1]
        group }
  refine ⟨A, ?_, ?_, ?_⟩
  · rintro α ⟨e, he, hα⟩ β ⟨f, hf, hβ⟩
    refine MulEquiv.ext fun M => πs.injective (Subtype.ext ?_)
    rw [MulAut.mul_apply, MulAut.mul_apply, hα, hβ, hβ, hα,
      show e * (f * (πs M : MulAut W) * f⁻¹) * e⁻¹ = (e * f) * πs M * (e * f)⁻¹ by group,
      hEc e he f hf]
    group
  · rintro α ⟨e, he, hα⟩
    refine MulEquiv.ext fun M => πs.injective (Subtype.ext ?_)
    rw [MulAut.mul_apply, hα, hα, MulAut.one_apply,
      show e * (e * (πs M : MulAut W) * e⁻¹) * e⁻¹ = (e * e) * πs M * (e * e)⁻¹ by group,
      hE2 e he]
    group
  have hαe : ∀ e ∈ E, ∃ α : MulAut S, ∀ M, (πs (α M) : MulAut W) = e * πs M * e⁻¹ :=
    fun e he => ⟨πs.trans ((conjOn (hEN he)).trans πs.symm), fun M => by
      change (πs (πs.symm (conjOn (hEN he) (πs M))) : MulAut W) = _
      rw [MulEquiv.apply_symm_apply]
      rfl⟩
  choose αf hαf using fun e : E => hαe e e.2
  let f : E → A := fun e => ⟨αf e, e, e.2, hαf e⟩
  have hf : Function.Injective f := by
    intro e e' h
    have h1 : αf e = αf e' := congrArg Subtype.val h
    have hcen' : ∀ l ∈ Λ, ((e' : MulAut W)⁻¹ * e) * l = l * ((e' : MulAut W)⁻¹ * e) := by
      intro l hl
      obtain ⟨M, hM⟩ := πs.surjective ⟨l, hl⟩
      have h2 := hαf e M
      rw [h1, hαf e', hM] at h2
      change (e' : MulAut W) * l * (e' : MulAut W)⁻¹ = e * l * (e : MulAut W)⁻¹ at h2
      calc ((e' : MulAut W)⁻¹ * e) * l = (e' : MulAut W)⁻¹ * (e * l * (e : MulAut W)⁻¹) * e := by
            group
        _ = (e' : MulAut W)⁻¹ * (e' * l * (e' : MulAut W)⁻¹) * e := by rw [h2]
        _ = l * ((e' : MulAut W)⁻¹ * e) := by group
    have he2 : ((e' : MulAut W)⁻¹ * e) * ((e' : MulAut W)⁻¹ * e) = 1 :=
      hE2 _ (E.mul_mem (E.inv_mem e'.2) e.2)
    exact Subtype.ext (inv_mul_eq_one.mp (hcen _ he2 hcen')).symm
  have : Finite (MulAut S) :=
    Finite.of_injective (fun α : MulAut S => (α : S → S)) fun α β h => MulEquiv.ext (congrFun h)
  exact Nat.card_le_card_of_injective f hf

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
