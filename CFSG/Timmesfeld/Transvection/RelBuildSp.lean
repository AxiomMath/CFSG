module

public import CFSG.Timmesfeld.Transvection.RelBuildBasic
public import CFSG.Timmesfeld.Transvection.PresSp

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

structure PreSpRelations (r : ℕ) (K : Type) [Field K] (G : Type*) [Group G] where
  ξ : Fin r ⊕ Fin r → Fin r ⊕ Fin r → K → G
  ξL : Fin r ⊕ Fin r → K → G
  w : Fin r → G
  symm : ∀ a b, idx a ≠ idx b → ∀ c, ξ b a c = ξ a b c
  add : ∀ a b, idx a ≠ idx b → ∀ s t, ξ a b (s + t) = ξ a b s * ξ a b t
  addL : ∀ a s t, ξL a (s + t) = ξL a s * ξL a t
  weyl : ∀ k a b, idx a ≠ idx b → ∀ c,
    w k * ξ a b c * (w k)⁻¹ = ξ (RelBuild.flip k a) (RelBuild.flip k b) c
  weylL : ∀ k a c, w k * ξL a c * (w k)⁻¹ = ξL (RelBuild.flip k a) c
  shortLong : ∀ i j : Fin r, i ≠ j → ∀ s t,
    ⁅ξ (.inl j) (.inr i) s, ξL (.inl i) t⁆ = ξ (.inl j) (.inl i) (s * t) * ξL (.inl j) (s ^ 2 * t)
  commLong : ∀ i j : Fin r, i ≠ j → ∀ s t, ⁅ξ (.inl j) (.inr i) s, ξ (.inl j) (.inl i) t⁆ = 1
  commLL : ∀ i j : Fin r, i ≠ j → ∀ s t, ⁅ξL (.inl i) s, ξL (.inl j) t⁆ = 1
  commLS : ∀ i j : Fin r, i ≠ j → ∀ s t, ⁅ξL (.inl j) s, ξ (.inl j) (.inr i) t⁆ = 1
  commLS₃ : ∀ i j k : Fin r, i ≠ j → i ≠ k → j ≠ k → ∀ s t,
    ⁅ξL (.inl k) s, ξ (.inl j) (.inr i) t⁆ = 1
  commSS₃ : ∀ i j k : Fin r, i ≠ j → i ≠ k → j ≠ k → ∀ s t,
    ⁅ξ (.inl j) (.inr i) s, ξ (.inl k) (.inr i) t⁆ = 1
  commSS₄ : ∀ i j k l : Fin r, i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l → ∀ s t,
    ⁅ξ (.inl j) (.inr i) s, ξ (.inl l) (.inr k) t⁆ = 1
  short : ∀ i j k : Fin r, i ≠ j → j ≠ k → i ≠ k → ∀ s t, ∃ u,
    ⁅ξ (.inl j) (.inr i) s, ξ (.inl k) (.inr j) t⁆ = ξ (.inl k) (.inr i) u ∧
      u ^ 2 = s ^ 2 * t ^ 2

namespace PreSpRelations

variable {r : ℕ} {K : Type} [Field K] {G : Type*} [Group G] (P : PreSpRelations r K G)

theorem mapL_zero (a : Fin r ⊕ Fin r) : P.ξL a 0 = 1 := by
  have h := P.addL a 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

@[expose] def spξ (a b : Fin r ⊕ Fin r) (c : K) : G :=
  if b = a then P.ξL a c else P.ξ a b c

theorem spξ_self (a : Fin r ⊕ Fin r) (c : K) : P.spξ a a c = P.ξL a c :=
  ite_eq_left rfl

theorem spξ_of_ne {a b : Fin r ⊕ Fin r} (h : b ≠ a) (c : K) : P.spξ a b c = P.ξ a b c :=
  ite_eq_right h

variable [CharP K 2]

@[expose] def toPre : PreRelations r (RingEquiv.refl K) G where
  ξ := P.ξ
  ξL := P.ξL
  w := P.w
  swap a b hab c := P.symm a b hab c
  add := P.add
  addL a s t _ _ := P.addL a s t
  weyl := P.weyl
  weylL k a c _ := P.weylL k a c
  shortLong i j hij s t _ := by rw [P.shortLong i j hij s t, RingEquiv.refl_apply, ← sq]
  trace i j hij s t := by
    rw [P.commLong i j hij s t, RingEquiv.refl_apply, RingEquiv.refl_apply,
      CharTwo.add_self_eq_zero, P.mapL_zero]
  commLL i j hij s t _ _ := P.commLL i j hij s t
  commLS i j hij s t _ := P.commLS i j hij s t
  commLS₃ i j k h₁ h₂ h₃ s t _ := P.commLS₃ i j k h₁ h₂ h₃ s t
  commSS₃ := P.commSS₃
  commSS₄ := P.commSS₄

@[simp] theorem toPre_ξ : P.toPre.ξ = P.ξ := rfl

@[simp] theorem toPre_ξL : P.toPre.ξL = P.ξL := rfl

theorem short_exact {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s t : K) :
    ⁅P.ξ (.inl j) (.inr i) s, P.ξ (.inl k) (.inr j) t⁆ = P.ξ (.inl k) (.inr i) (s * t) := by
  obtain ⟨u, hu, hu2⟩ := P.short i j k hij hjk hik s t
  have h : (u + s * t) ^ 2 = 0 := by
    rw [CharTwo.add_sq, hu2, mul_pow, CharTwo.add_self_eq_zero]
  rw [hu, CharTwo.add_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)]

@[expose] def toSpRelations : SpRelations r K G :=
  SpRelations.ofSplit P.spξ
    (fun a b hab c => by
      by_cases h : b = a
      · subst h
        rfl
      · rw [P.spξ_of_ne (Ne.symm h), P.spξ_of_ne h, P.symm a b (idx_ne_of_ne h hab)])
    (fun a b hab s t => by
      by_cases h : b = a
      · subst h
        rw [P.spξ_self, P.spξ_self, P.spξ_self, P.addL]
      · rw [P.spξ_of_ne h, P.spξ_of_ne h, P.spξ_of_ne h, P.add a b (idx_ne_of_ne h hab)])
    (fun a b d hab hbd had s t => by
      rw [P.spξ_of_ne (ne_of_idx_ne hab), P.spξ_of_ne (ne_of_idx_ne (by rwa [idx_swap])),
        P.spξ_of_ne (ne_of_idx_ne had)]
      exact P.toPre.short_of_base hab hbd had (fun s t => P.short_exact hab hbd had s t) rfl rfl
        rfl s t)
    (fun a b hab s t => by
      rw [P.spξ_of_ne (ne_of_idx_ne hab), P.spξ_self, P.spξ_of_ne
        (ne_of_idx_ne (by rwa [idx_swap])), P.spξ_self]
      have h := P.toPre.shortLong' (fun _ => rfl) hab s t rfl
      rwa [RingEquiv.refl_apply, ← sq] at h)
    (fun a b hab s t => by
      rw [P.spξ_of_ne (ne_of_idx_ne hab), P.spξ_of_ne (ne_of_idx_ne (by rwa [idx_swap]))]
      have h := P.toPre.trace' (fun _ => rfl) hab s t
      rwa [RingEquiv.refl_apply, RingEquiv.refl_apply, CharTwo.add_self_eq_zero,
        toPre_ξL, P.mapL_zero] at h)
    (fun a c hca s t => by
      rw [P.spξ_self, P.spξ_self]
      exact P.toPre.commLL' hca rfl rfl)
    (fun a c d hcd hca hda s t => by
      rw [P.spξ_self, P.spξ_of_ne (ne_of_idx_ne hcd)]
      exact P.toPre.commLS' hcd hca hda rfl t)
    (fun a b c d hab hcd hca hcb hda hdb s t => by
      rw [P.spξ_of_ne (ne_of_idx_ne hab), P.spξ_of_ne (ne_of_idx_ne hcd)]
      exact P.toPre.commSS' hab hcd hca hcb hda hdb s t)

@[simp] theorem toSpRelations_ξ_self (a : Fin r ⊕ Fin r) (c : K) :
    P.toSpRelations.ξ a a c = P.ξL a c :=
  P.spξ_self a c

theorem toSpRelations_ξ_of_ne {a b : Fin r ⊕ Fin r} (h : b ≠ a) (c : K) :
    P.toSpRelations.ξ a b c = P.ξ a b c :=
  P.spξ_of_ne h c

end PreSpRelations

end CFSG.Timmesfeld.Transvection
