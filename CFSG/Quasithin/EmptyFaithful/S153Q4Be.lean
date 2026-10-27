module

public import CFSG.Quasithin.EmptyFaithful.S153Q4Bd

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q4B

open Equiv

section Key

variable {W : Type} [CommGroup W] {Ah : Subgroup (MulAut W)} {z : MulAut W}
  {lab : Fin 6 → Subgroup W}

theorem orbit_lemma [Finite W] {X : Subgroup (MulAut W)} {V V₁ V₂ : Subgroup W}
    (hI : V₁ ⊓ V₂ = ⊥) (h1 : Nat.card ↥V₁ = 4) (h2 : Nat.card ↥V₂ = 4)
    (hX' : ∀ x ∈ X, (∀ v ∈ V, x v ∈ V) → (∀ v ∈ V₁, x v ∈ V₁) ∨ (∀ v ∈ V₁, x v ∈ V₂))
    {y : MulAut W} (hy : y ∈ X) (hyV : ∀ v ∈ V, y v ∈ V)
    (hy3 : ∀ v ∈ V₁, (y * y * y) v ∈ V₁) : ∀ v ∈ V₁, y v ∈ V₁ := by
  rcases hX' y hy hyV with h | h
  · exact h
  · exfalso
    have hne : ¬ ∀ v ∈ V₁, v = 1 := by
      intro hall
      have hb : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall V₁).2 hall
      rw [hb, Subgroup.card_bot] at h1
      omega
    apply hne
    have hmeet : ∀ v, v ∈ V₁ → v ∈ V₂ → v = 1 := by
      intro v hv1 hv2
      have hv : v ∈ V₁ ⊓ V₂ := ⟨hv1, hv2⟩
      rw [hI] at hv
      exact Subgroup.mem_bot.1 hv
    have hinj : ∀ (u : MulAut W) (v : W), u v = 1 → v = 1 := fun u v hv =>
      u.injective (hv.trans (map_one u).symm)
    have hyy : ∀ v ∈ V, (y * y) v ∈ V := fun v hv => by
      rw [MulAut.mul_apply]; exact hyV _ (hyV _ hv)
    rcases hX' (y * y) (mul_mem hy hy) hyy with hB1 | hB2
    · intro v hv
      have h3 : (y * y * y) v = y ((y * y) v) := by rw [mul_assoc, MulAut.mul_apply]
      have h4 : (y * y * y) v ∈ V₂ := by rw [h3]; exact h _ (hB1 v hv)
      exact hinj _ v (hmeet _ (hy3 v hv) h4)
    · have hle : V₁.map y.toMonoidHom ≤ V₂ := by
        rintro _ ⟨v, hv, rfl⟩
        exact h v hv
      have hcard : Nat.card ↥(V₁.map y.toMonoidHom) = Nat.card ↥V₂ := by
        rw [Subgroup.card_map_of_injective (f := y.toMonoidHom) y.injective, h1, h2]
      have heq : V₁.map y.toMonoidHom = V₂ :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
      intro v hv
      have h5 : (y * y) v ∈ V₁.map y.toMonoidHom := by rw [heq]; exact hB2 v hv
      obtain ⟨u, hu, hu'⟩ := h5
      have h6 : u = y v := y.injective (by simpa [MulAut.mul_apply] using hu')
      have h7 : y v ∈ V₁ := h6 ▸ hu
      exact hinj y v (hmeet _ h7 (h v hv))

theorem Ctx.cen_conj [Finite W] (C : Ctx W Ah z lab) {P : Fin 3 → MulAut W}
    (hP : ∀ a, P a ∈ Ah ∧ P a * P a = 1 ∧ Ind lab (P a) (S3 a)) {g : MulAut W} (hg : g ∈ Ah)
    (hgτ : Ind lab g tau) (a : Fin 3) : ∀ y ∈ cen (P (a + 1)), ∃ x ∈ cen (P a), y = g x := by
  obtain ⟨hPa, hPaa, hPai⟩ := hP a
  obtain ⟨hPb, hPbb, hPbi⟩ := hP (a + 1)
  have hQA : g * P a * g⁻¹ ∈ Ah := mul_mem (mul_mem hg hPa) (inv_mem hg)
  have hQQ : (g * P a * g⁻¹) * (g * P a * g⁻¹) = 1 := by
    calc (g * P a * g⁻¹) * (g * P a * g⁻¹) = g * (P a * P a) * g⁻¹ := by group
      _ = 1 := by rw [hPaa]; group
  have hQi : Ind lab (g * P a * g⁻¹) (S3 (a + 1)) := by
    have := Ind.mul (Ind.mul hgτ hPai) (C.ind_inv hg hgτ)
    rwa [tau_conj] at this
  have hQ : g * P a * g⁻¹ = P (a + 1) :=
    C.inv_lift_unique (S3_sq _) hQA hPb hQQ hPbb hQi hPbi
  intro y hy
  obtain ⟨u, hu⟩ := mem_cen.1 hy
  refine ⟨P a (g⁻¹ u) * (g⁻¹ u)⁻¹, nHom_mem_cen (P a) (g⁻¹ u), ?_⟩
  rw [← hu, ← hQ]
  simp [MulAut.mul_apply]

theorem Ctx.key [Finite W] (C : Ctx W Ah z lab) {X : Subgroup (MulAut W)} (hAX : Ah ≤ X)
    {V₁ V₂ : Subgroup W} (hV : V₁ ⊔ V₂ = lab 4 ⊔ lab 5) (hI : V₁ ⊓ V₂ = ⊥)
    (h1 : Nat.card ↥V₁ = 4) (h2 : Nat.card ↥V₂ = 4)
    (hX' : ∀ x ∈ X, (∀ v ∈ lab 4 ⊔ lab 5, x v ∈ lab 4 ⊔ lab 5) →
      (∀ v ∈ V₁, x v ∈ V₁) ∨ (∀ v ∈ V₁, x v ∈ V₂)) : V₁ = lab 4 ∨ V₁ = lab 5 := by
  have hV1 : V₁ ≤ lab 4 ⊔ lab 5 := hV ▸ le_sup_left
  have hzind : Ind lab z 1 := C.ind_zpowers (Subgroup.mem_zpowers z)
  have hzV : ∀ v ∈ lab 4 ⊔ lab 5, z v ∈ lab 4 ⊔ lab 5 := fun v hv =>
    Ind.mem_sup_of_fix hzind rfl rfl hv
  have hz3 : z * z * z = 1 := by
    have := C.cube
    simpa [pow_succ] using this
  have hz1 : ∀ v ∈ V₁, z v ∈ V₁ := by
    refine orbit_lemma hI h1 h2 hX' (hAX C.zA) hzV ?_
    intro v hv
    rw [hz3]
    simpa using hv
  have hpt : IsPt z V₁ := ⟨h1, hz1⟩
  obtain ⟨P, hP, hPpt, hPne, hPdist⟩ := C.centres
  obtain ⟨g, hg, hgτ⟩ := C.O.surj tau tau_mem
  have hgV : ∀ v ∈ lab 4 ⊔ lab 5, g v ∈ lab 4 ⊔ lab 5 := fun v hv =>
    Ind.mem_sup_of_fix hgτ tau_four tau_five hv
  have hg3A : g * g * g ∈ Ah := mul_mem (mul_mem hg hg) hg
  have hg3i : Ind lab (g * g * g) 1 := by
    have := Ind.mul (Ind.mul hgτ hgτ) hgτ
    rwa [tau_cube] at this
  have hg3z : g * g * g ∈ Subgroup.zpowers z := C.mem_zpowers_of_ind hg3A hg3i
  have hg3 : ∀ v ∈ V₁, (g * g * g) v ∈ V₁ := by
    rcases ZCtx.mem_zpowers C.toZCtx hg3z with h | h | h
    · rw [h]; intro v hv; simpa using hv
    · rw [h]; exact hz1
    · rw [h]; intro v hv; rw [MulAut.mul_apply]; exact hz1 _ (hz1 _ hv)
  have hg1 : ∀ v ∈ V₁, g v ∈ V₁ := orbit_lemma hI h1 h2 hX' (hAX hg) hgV hg3
  have hcl : V₁ = lab 4 ∨ V₁ = lab 5 ∨ ∃ a, V₁ = cen (P a) := by
    by_contra hcon
    have hn4 : V₁ ≠ lab 4 := fun h => hcon (Or.inl h)
    have hn5 : V₁ ≠ lab 5 := fun h => hcon (Or.inr (Or.inl h))
    have hnc : ∀ a, V₁ ≠ cen (P a) := fun a h => hcon (Or.inr (Or.inr ⟨a, h⟩))
    let o : Fin 6 → Subgroup W := ![lab 4, lab 5, cen (P 0), cen (P 1), cen (P 2), V₁]
    have hpts : ∀ i, IsPt z (o i) := by
      intro i; fin_cases i
      · exact C.pt 4
      · exact C.pt 5
      · exact (hPpt 0).1
      · exact (hPpt 1).1
      · exact (hPpt 2).1
      · exact hpt
    have h45 : lab 4 ≠ lab 5 := fun h => absurd (C.O.inj h) (by decide)
    have h54 : lab 5 ≠ lab 4 := h45.symm
    have hc4 : ∀ a, cen (P a) ≠ lab 4 := fun a => (hPne a).1
    have hc5 : ∀ a, cen (P a) ≠ lab 5 := fun a => (hPne a).2
    have h4c : ∀ a, lab 4 ≠ cen (P a) := fun a => (hPne a).1.symm
    have h5c : ∀ a, lab 5 ≠ cen (P a) := fun a => (hPne a).2.symm
    have hn4' : lab 4 ≠ V₁ := hn4.symm
    have hn5' : lab 5 ≠ V₁ := hn5.symm
    have hnc' : ∀ a, cen (P a) ≠ V₁ := fun a => (hnc a).symm
    have hne : ∀ i j, i ≠ j → o i ≠ o j := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd rfl hij
        | simp [o, h45, h54, hc4, hc5, h4c, h5c, hn4, hn5, hn4', hn5', hnc, hnc', hPdist]
    have hd : ∀ i j, i ≠ j → o i ⊓ o j = ⊥ := fun i j hij =>
      ZCtx.pt_inf_eq_bot C.toZCtx (hpts i) (hpts j) (hne i j hij)
    have hc : ∀ i, Nat.card ↥(o i) = 4 := fun i => (hpts i).1
    have hle : ∀ i, o i ≤ lab 4 ⊔ lab 5 := by
      intro i; fin_cases i
      · exact le_sup_left
      · exact le_sup_right
      · exact (hPpt 0).2
      · exact (hPpt 1).2
      · exact (hPpt 2).2
      · exact hV1
    have hV16 : Nat.card ↥(lab 4 ⊔ lab 5) = 16 :=
      ZCtx.card_sup_pts C.toZCtx (C.pt 4) (C.pt 5) h45
    have h65 := line_pts hV16 o hc hle hd
    omega
  rcases hcl with h | h | ⟨a, ha⟩
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have hsub : cen (P (a + 1)) ≤ cen (P a) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := C.cen_conj hP hg hgτ a y hy
      rw [← ha] at hx ⊢
      exact hg1 x hx
    have heq : cen (P (a + 1)) = cen (P a) :=
      Subgroup.eq_of_le_of_card_ge hsub (by rw [(hPpt a).1.1, (hPpt (a + 1)).1.1])
    exact hPdist (a + 1) a (fin3_add_one_ne a) heq

end Key

end Q4B

end S153Q

end CFSG.Quasithin
