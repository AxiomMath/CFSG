module

public import CFSG.Quasithin.Vol2.Ch10SecQ6A5b
public import CFSG.Quasithin.Vol2.Ch10SecDFacts12

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

variable {W : Type*} [CommGroup W]

@[expose] def permSub (Ψ : W → Fin 5 → ZMod 2) (E : Subgroup (MulAut W)) :
    Subgroup (Perm (Fin 5)) where
  carrier := {σ | ∃ e ∈ E, ∀ w, Ψ (e w) = pv σ (Ψ w)}
  one_mem' := ⟨1, E.one_mem, fun w => rfl⟩
  mul_mem' := by
    rintro σ τ ⟨e, he, hσ⟩ ⟨f, hf, hτ⟩
    exact ⟨e * f, E.mul_mem he hf, fun w => by rw [MulAut.mul_apply, hσ, hτ, pv_mul]⟩
  inv_mem' := by
    rintro σ ⟨e, he, hσ⟩
    refine ⟨e⁻¹, E.inv_mem he, fun w => ?_⟩
    have h1 := hσ (e⁻¹ w)
    rw [MulAut.apply_inv_self] at h1
    rw [h1, ← pv_mul, inv_mul_cancel, pv_one]

theorem perm_unique {Ψ : W → Fin 5 → ZMod 2} (honto : ∀ u, IsO u → ∃ w, Ψ w = u)
    {e : MulAut W} {σ τ : Perm (Fin 5)} (hσ : ∀ w, Ψ (e w) = pv σ (Ψ w))
    (hτ : ∀ w, Ψ (e w) = pv τ (Ψ w)) : σ = τ := by
  have h1 : σ⁻¹ * τ = 1 := eq_one_of_fix_O _ fun u hu => by
    obtain ⟨w, rfl⟩ := honto u hu
    rw [pv_mul, ← hτ, hσ, ← pv_mul, inv_mul_cancel, pv_one]
  rw [← mul_inv_cancel_left σ τ, h1, mul_one]

theorem aut_unique {Ψ : W → Fin 5 → ZMod 2} (hinj : Function.Injective Ψ) {e f : MulAut W}
    {σ : Perm (Fin 5)} (he : ∀ w, Ψ (e w) = pv σ (Ψ w)) (hf : ∀ w, Ψ (f w) = pv σ (Ψ w)) :
    e = f :=
  MulEquiv.ext fun w => hinj (by rw [he, hf])

theorem permSub_comm {Ψ : W → Fin 5 → ZMod 2}
    (honto : ∀ u, IsO u → ∃ w, Ψ w = u) {E : Subgroup (MulAut W)}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ∀ σ ∈ permSub Ψ E, ∀ τ ∈ permSub Ψ E, σ * τ = τ * σ := by
  rintro σ ⟨e, he, hσ⟩ τ ⟨f, hf, hτ⟩
  apply perm_unique honto (e := e * f)
  · intro w
    rw [MulAut.mul_apply, hσ, hτ, pv_mul]
  · intro w
    rw [hEc e he f hf, MulAut.mul_apply, hτ, hσ, pv_mul]

theorem permSub_sq {Ψ : W → Fin 5 → ZMod 2}
    (honto : ∀ u, IsO u → ∃ w, Ψ w = u) {E : Subgroup (MulAut W)}
    (hE2 : ∀ a ∈ E, a * a = 1) : ∀ σ ∈ permSub Ψ E, σ * σ = 1 := by
  rintro σ ⟨e, he, hσ⟩
  apply perm_unique honto (e := e * e)
  · intro w
    rw [MulAut.mul_apply, hσ, hσ, pv_mul]
  · intro w
    rw [hE2 e he, pv_one]
    rfl

end C10P06

theorem fact12A5 : Fact12A5 := by
  intro W _ _ _ Λ _ _ halt
  obtain ⟨π, Ψ, hc⟩ := C10P06.exists_isA5Coord halt
  have hcard := C10P06.card_eq_of_isA5Coord hc
  have hperm : ∀ n ∈ Subgroup.normalizer (Λ : Set (MulAut W)),
      ∃ σ, ∀ w, Ψ (n w) = C10P06.pv σ (Ψ w) := fun n hn =>
    C10P06.exists_perm_of_normalizes hc hn
  obtain ⟨-, -, hinj, -, honto, -⟩ := hc
  have hcomm : ∀ {E : Subgroup (MulAut W)}, CFSG.Open.IsElemAbelian 2 E →
      ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun hE a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ {E : Subgroup (MulAut W)}, CFSG.Open.IsElemAbelian 2 E → ∀ a ∈ E, a * a = 1 :=
    fun hE a ha => by rw [← sq]; exact hE.2 a ha
  refine ⟨hcard, fun E hEN hEab => ?_, fun E hEN hEab hE1 q hq => ?_⟩
  · choose σf hσf using fun e : E => hperm e (hEN e.2)
    let f : E → C10P06.permSub Ψ E := fun e => ⟨σf e, ⟨e, e.2, hσf e⟩⟩
    have hf : Function.Injective f := fun e e' h => Subtype.ext (C10P06.aut_unique hinj (hσf e)
      (by rw [show σf e = σf e' from congrArg Subtype.val h]; exact hσf e'))
    have h1 := Nat.card_le_card_of_injective f hf
    have h2 := C10P06.card_le_four (C10P06.permSub_comm honto (hcomm hEab))
      (C10P06.permSub_sq honto (hsq hEab))
    calc Nat.card E ≤ 4 := h1.trans h2
      _ = 2 ^ 2 := by norm_num
  · by_contra hq1
    push Not at hq1
    have hPE : C10P06.permSub Ψ E ≠ ⊥ := by
      intro h
      apply hE1
      rw [eq_bot_iff]
      intro e he
      obtain ⟨σ, hσ⟩ := hperm e (hEN he)
      have hσ1 : σ ∈ C10P06.permSub Ψ E := ⟨e, he, hσ⟩
      rw [h, Subgroup.mem_bot] at hσ1
      rw [Subgroup.mem_bot]
      exact C10P06.aut_unique hinj hσ (fun w => by rw [hσ1, C10P06.pv_one]; rfl)
    obtain ⟨D', -, ⟨x1, ⟨ex, hexE, hex⟩, hx1D, hcov⟩, u, hu, hufix, d, ⟨ed, hedE, hed⟩, hdu⟩ :=
      C10P06.exists_hyperplane_fix (C10P06.permSub_comm honto (hcomm hEab))
        (C10P06.permSub_sq honto (hsq hEab)) hPE
    let B : Subgroup (MulAut W) :=
      { carrier := {e | e ∈ E ∧ ∃ δ ∈ D', ∀ w, Ψ (e w) = C10P06.pv δ (Ψ w)}
        one_mem' := ⟨E.one_mem, 1, D'.one_mem, fun w => rfl⟩
        mul_mem' := by
          rintro a b ⟨ha, δ1, hδ1, h1⟩ ⟨hb, δ2, hδ2, h2⟩
          exact ⟨E.mul_mem ha hb, δ1 * δ2, D'.mul_mem hδ1 hδ2, fun w => by
            rw [MulAut.mul_apply, h1, h2, C10P06.pv_mul]⟩
        inv_mem' := by
          rintro a ⟨ha, δ, hδ, h⟩
          refine ⟨E.inv_mem ha, δ⁻¹, D'.inv_mem hδ, fun w => ?_⟩
          have h1 := h (a⁻¹ w)
          rw [MulAut.apply_inv_self] at h1
          rw [h1, ← C10P06.pv_mul, inv_mul_cancel, C10P06.pv_one] }
    have hrel : B.relIndex E = 2 := by
      refine C10P06.relIndex_eq_two_of_cover hexE (fun h => hx1D ?_) fun e he => ?_
      · obtain ⟨-, δ, hδ, hδe⟩ := h
        rwa [C10P06.perm_unique honto hex hδe]
      · obtain ⟨σ, hσ⟩ := hperm e (hEN he)
        rcases hcov σ ⟨e, he, hσ⟩ with h | h
        · exact Or.inl ⟨he, σ, h, hσ⟩
        · exact Or.inr ⟨E.mul_mem he hexE, σ * x1, h, fun w => by
            rw [MulAut.mul_apply, hσ, hex, C10P06.pv_mul]⟩
    have hmq : E3.mQuot E B < q := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      unfold E3.mQuot
      rw [hrel, padicValNat_self]
      exact hq1
    have hfixB := hq B (fun _ h => h.1) hmq
    obtain ⟨wu, hwu⟩ := honto u hu
    have hwB : wu ∈ fixV B := by
      rintro b ⟨-, δ, hδ, hbδ⟩
      apply hinj
      rw [hbδ, hwu, hufix δ hδ]
    rw [hfixB] at hwB
    apply hdu
    rw [← hwu, ← hed, hwB ed hedE]

end CFSG.Quasithin.Vol2.Ch10.SecD
