module

public import CFSG.RankThree.GF2n.Smith81.S81VOrth

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary Module

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] def Adj (σ : F ≃+* F) (x y : Submodule F (Fin 6 → F)) : Prop :=
  IsPt σ x ∧ IsPt σ y ∧ finrank F ↥(x ⊓ y) = 2

private theorem gu2a_finrank_sup_span {S : Submodule F (Fin 6 → F)} {v : Fin 6 → F}
    (hv : v ∉ S) : finrank F ↥(S ⊔ Submodule.span F {v}) = finrank F ↥S + 1 := by
  have hv0 : v ≠ 0 := by
    intro h
    apply hv
    rw [h]
    exact S.zero_mem
  have hinf : S ⊓ Submodule.span F {v} = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwS, hwv⟩ := Submodule.mem_inf.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hwv
    rw [Submodule.mem_bot]
    by_cases hc : c = 0
    · rw [hc, zero_smul]
    · exfalso
      apply hv
      have h1 : c⁻¹ • (c • v) ∈ S := S.smul_mem c⁻¹ hwS
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span F {v})
  rw [hinf, finrank_bot, finrank_span_singleton hv0] at h1
  omega

private theorem gu2a_isTotIso_sup {A B : Submodule F (Fin 6 → F)} (hA : IsTotIso σ A)
    (hB : IsTotIso σ B) (hAB : ∀ a ∈ A, ∀ b ∈ B, herm σ a b = 0)
    (hBA : ∀ b ∈ B, ∀ a ∈ A, herm σ b a = 0) : IsTotIso σ (A ⊔ B) := by
  intro a ha b hb
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hb
  simp only [herm_add_left, herm_add_right, hA a₁ ha₁ b₁ hb₁, hAB a₁ ha₁ b₂ hb₂,
    hBA a₂ ha₂ b₁ hb₁, hB a₂ ha₂ b₂ hb₂, add_zero]

private theorem gu2a_isTotIso_span {v : Fin 6 → F} (hv : herm σ v v = 0) :
    IsTotIso σ (Submodule.span F {v}) := by
  intro a ha b hb
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb
  simp [herm_smul_left, herm_smul_right, hv]

private theorem gu2a_exists_between (X : Submodule F (Fin 6 → F)) (m : ℕ) :
    ∀ S : Submodule F (Fin 6 → F), S ≤ X → finrank F ↥S + m ≤ finrank F ↥X →
      ∃ H : Submodule F (Fin 6 → F), S ≤ H ∧ H ≤ X ∧ finrank F ↥H = finrank F ↥S + m := by
  induction m with
  | zero =>
    intro S hSX _
    exact ⟨S, le_rfl, hSX, by omega⟩
  | succ m ih =>
    intro S hSX hdim
    have hlt : S < X := by
      refine lt_of_le_of_ne hSX fun h => ?_
      rw [h] at hdim
      omega
    obtain ⟨v, hvX, hvS⟩ := SetLike.exists_of_lt hlt
    have hS' : S ⊔ Submodule.span F {v} ≤ X :=
      sup_le hSX (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvX))
    have hfin := gu2a_finrank_sup_span hvS
    obtain ⟨H, hH1, hH2, hH3⟩ := ih (S ⊔ Submodule.span F {v}) hS' (by omega)
    exact ⟨H, le_trans le_sup_left hH1, hH2, by omega⟩

theorem exists_adjacent_closer (hσ : IsUnitaryInvolution σ) {x y : Submodule F (Fin 6 → F)}
    (hx : IsPt σ x) (hy : IsPt σ y) (hxy : finrank F ↥(x ⊓ y) ≤ 1) :
    ∃ z, Adj σ x z ∧ finrank F ↥(x ⊓ y) < finrank F ↥(z ⊓ y) := by
  have hinv : ∀ c, σ (σ c) = c := hσ.invol
  obtain ⟨hxti, hx3⟩ : IsTotIso σ x ∧ finrank F ↥x = 3 := hx
  obtain ⟨hyti, hy3⟩ : IsTotIso σ y ∧ finrank F ↥y = 3 := hy
  have hxti' : ∀ a ∈ x, ∀ b ∈ x, herm σ a b = 0 := hxti
  have hyti' : ∀ a ∈ y, ∀ b ∈ y, herm σ a b = 0 := hyti
  obtain ⟨H, hUH, hHx, hH2⟩ : ∃ H : Submodule F (Fin 6 → F),
      x ⊓ y ≤ H ∧ H ≤ x ∧ finrank F ↥H = 2 := by
    obtain ⟨H, h1, h2, h3⟩ :=
      gu2a_exists_between x (2 - finrank F ↥(x ⊓ y)) (x ⊓ y) inf_le_left (by omega)
    exact ⟨H, h1, h2, by omega⟩
  have hHti : IsTotIso σ H := by
    intro a ha b hb
    exact hxti' a (hHx ha) b (hHx hb)
  have horthH : finrank F ↥(orth σ H) = 4 := by
    have h := finrank_orth hinv H
    omega
  have hUd : finrank F ↥(orth σ (x ⊓ y)) + finrank F ↥(x ⊓ y) = 6 :=
    finrank_orth hinv (x ⊓ y)
  have hyorth : y ≤ orth σ (x ⊓ y) := by
    intro v hv
    rw [mem_orth]
    intro w hw
    exact hyti' w (Submodule.mem_inf.mp hw).2 v hv
  have horthmono : orth σ H ≤ orth σ (x ⊓ y) := by
    intro v hv
    rw [mem_orth] at hv ⊢
    intro w hw
    exact hv w (hUH hw)
  have hsup : finrank F ↥(y ⊔ orth σ H) ≤ finrank F ↥(orth σ (x ⊓ y)) :=
    Submodule.finrank_mono (sup_le hyorth horthmono)
  have hsum : finrank F ↥(y ⊔ orth σ H) + finrank F ↥(y ⊓ orth σ H)
      = finrank F ↥y + finrank F ↥(orth σ H) :=
    Submodule.finrank_sup_add_finrank_inf_eq y (orth σ H)
  have hA : finrank F ↥(x ⊓ y) + 1 ≤ finrank F ↥(y ⊓ orth σ H) := by
    omega
  obtain ⟨y₀, hy₀A, hy₀x⟩ : ∃ y₀ ∈ y ⊓ orth σ H, y₀ ∉ x := by
    by_contra hcon
    have hle' : y ⊓ orth σ H ≤ x ⊓ y := by
      intro v hv
      refine Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_inf.mp hv).1⟩
      by_contra hvx
      exact hcon ⟨v, hv, hvx⟩
    have h1 : finrank F ↥(y ⊓ orth σ H) ≤ finrank F ↥(x ⊓ y) :=
      Submodule.finrank_mono hle'
    omega
  have hy₀y : y₀ ∈ y := (Submodule.mem_inf.mp hy₀A).1
  have hy₀H : y₀ ∈ orth σ H := (Submodule.mem_inf.mp hy₀A).2
  have hHy₀ : ∀ a ∈ H, herm σ a y₀ = 0 := by
    intro a ha
    rw [mem_orth] at hy₀H
    exact hy₀H a ha
  have hy₀H' : ∀ a ∈ H, herm σ y₀ a = 0 := fun a ha =>
    herm_eq_zero_comm σ hinv (hHy₀ a ha)
  have hy₀notH : y₀ ∉ H := fun h => hy₀x (hHx h)
  have hy₀sq : herm σ y₀ y₀ = 0 := hyti' y₀ hy₀y y₀ hy₀y
  have hAB : ∀ a ∈ H, ∀ b ∈ Submodule.span F {y₀}, herm σ a b = 0 := by
    intro a ha b hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [herm_smul_right, hHy₀ a ha, mul_zero]
  have hBA : ∀ b ∈ Submodule.span F {y₀}, ∀ a ∈ H, herm σ b a = 0 := by
    intro b hb a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [herm_smul_left, hy₀H' a ha, mul_zero]
  obtain ⟨z, hzdef⟩ : ∃ z : Submodule F (Fin 6 → F), z = H ⊔ Submodule.span F {y₀} :=
    ⟨_, rfl⟩
  have hzmem : y₀ ∈ z := by
    rw [hzdef]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y₀)
  have hHz : H ≤ z := by
    rw [hzdef]
    exact le_sup_left
  have hz_tot : IsTotIso σ z := by
    rw [hzdef]
    exact gu2a_isTotIso_sup hHti (gu2a_isTotIso_span hy₀sq) hAB hBA
  have hz_fin : finrank F ↥z = 3 := by
    have h1 := gu2a_finrank_sup_span hy₀notH
    rw [hzdef]
    omega
  have hz_pt : IsPt σ z := (⟨hz_tot, hz_fin⟩ : IsTotIso σ z ∧ finrank F ↥z = 3)
  have hxz_lo : finrank F ↥H ≤ finrank F ↥(x ⊓ z) :=
    Submodule.finrank_mono (le_inf hHx hHz)
  have hxz_hi : finrank F ↥(x ⊓ z) ≤ 2 := by
    by_contra hcon
    have hle3 : finrank F ↥(x ⊓ z) ≤ finrank F ↥x := Submodule.finrank_mono inf_le_left
    have heq : x ⊓ z = x := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    have hxz : x ≤ z := inf_eq_left.mp heq
    have hxz' : x = z := Submodule.eq_of_le_of_finrank_eq hxz (by omega)
    apply hy₀x
    rw [hxz']
    exact hzmem
  have hxz_eq : finrank F ↥(x ⊓ z) = 2 := by omega
  have hx_pt : IsPt σ x := (⟨hxti, hx3⟩ : IsTotIso σ x ∧ finrank F ↥x = 3)
  have hadj : Adj σ x z :=
    (⟨hx_pt, hz_pt, hxz_eq⟩ : IsPt σ x ∧ IsPt σ z ∧ finrank F ↥(x ⊓ z) = 2)
  have hy₀U : y₀ ∉ x ⊓ y := fun h => hy₀x (Submodule.mem_inf.mp h).1
  have hUy₀ : finrank F ↥((x ⊓ y) ⊔ Submodule.span F {y₀}) = finrank F ↥(x ⊓ y) + 1 :=
    gu2a_finrank_sup_span hy₀U
  have hy₀zy : y₀ ∈ z ⊓ y := Submodule.mem_inf.mpr ⟨hzmem, hy₀y⟩
  have hsub : (x ⊓ y) ⊔ Submodule.span F {y₀} ≤ z ⊓ y := by
    apply sup_le
    · exact le_inf (le_trans hUH hHz) inf_le_right
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hy₀zy)
  have hmono : finrank F ↥((x ⊓ y) ⊔ Submodule.span F {y₀}) ≤ finrank F ↥(z ⊓ y) :=
    Submodule.finrank_mono hsub
  exact ⟨z, hadj, by omega⟩

end CFSG.RankThree.GF2n.Smith81.S81V
