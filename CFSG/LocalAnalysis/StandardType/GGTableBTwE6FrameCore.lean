module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FrameSFDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

namespace TwE6TB

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem frame_conj_fix {p : ℕ} [NeZero p] {R : Type} [Group R] {I : Set (MulAut R)}
    {t : Multiplicative (Fin 6 → ZMod p) →* R} {m : WeylGroup TwistTag.E6.tag →* R}
    (h : GGTwE6FrameAt p R I t m) (γ : MulAut R)
    (hγ : ∀ a b : R, (∀ x ∈ t.range, (MulAut.conj a * γ * MulAut.conj b) x ∈ t.range) →
      ∃ w : WeylGroup TwistTag.E6.tag, ∀ s : Fin 6 → ZMod p,
        (MulAut.conj a * γ * MulAut.conj b) (t (Multiplicative.ofAdd s)) =
          t (Multiplicative.ofAdd (TableBExc.torusAct TwistTag.E6.tag p w s)))
    {E : Subgroup R} (hE : IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    (hSC : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ r : R, ∀ e ∈ E, MulAut.conj r (γ e) = e := by
  obtain ⟨-, hact, hU, -, -⟩ := h
  obtain ⟨c₀, hc₀⟩ := hU E hE h4 hSC
  let E' : Subgroup R := E.map γ.toMonoidHom
  have hE' : IsElemAbelian p E' := IsElemAbelian.map hE γ.toMonoidHom
  have hcardE' : Nat.card E' = Nat.card E := by
    dsimp only [E']
    rw [Subgroup.card_map_of_injective γ.injective]
  have h4' : p ^ 4 ≤ Nat.card E' := by rw [hcardE']; exact h4
  have hSC' : ∀ g : R, (∀ e ∈ E', g * e = e * g) → g ^ p = 1 → g ∈ E' := by
    intro g hg hgp
    have hcomm : ∀ e ∈ E, γ.symm g * e = e * γ.symm g := by
      intro e he
      have hge : g * γ e = γ e * g := hg (γ e) (Subgroup.mem_map_of_mem γ.toMonoidHom he)
      have h' := congrArg γ.symm hge
      simpa only [map_mul, MulEquiv.symm_apply_apply] using h'
    have hpow : (γ.symm g) ^ p = 1 := by
      apply γ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hgp, map_one]
    have hmem : γ.symm g ∈ E := hSC (γ.symm g) hcomm hpow
    have hg_eq : g = γ (γ.symm g) := (MulEquiv.apply_symm_apply γ g).symm
    rw [hg_eq]
    show γ (γ.symm g) ∈ E.map γ.toMonoidHom
    exact Subgroup.mem_map_of_mem γ.toMonoidHom hmem
  obtain ⟨c₁, hc₁⟩ := hU E' hE' h4' hSC'
  let δ : MulAut R := MulAut.conj c₁⁻¹ * γ * MulAut.conj c₀
  have hstab : ∀ x ∈ t.range, δ x ∈ t.range := by
    rintro x ⟨u, rfl⟩
    have hmem0 : MulAut.conj c₀ (t u) ∈ E := by
      rw [hc₀]
      exact Subgroup.mem_map_of_mem (MulAut.conj c₀).toMonoidHom (show t u ∈ t.range from ⟨u, rfl⟩)
    have hmem1 : γ (MulAut.conj c₀ (t u)) ∈ E' :=
      Subgroup.mem_map_of_mem γ.toMonoidHom hmem0
    rw [hc₁] at hmem1
    obtain ⟨y, hy, hyeq⟩ := hmem1
    have hyeq' : MulAut.conj c₁ y = γ (MulAut.conj c₀ (t u)) := by
      simpa only [MulEquiv.coe_toMonoidHom] using hyeq
    have hδy : δ (t u) = y := by
      dsimp only [δ]
      simp only [MulAut.mul_apply]
      rw [← hyeq']
      simp only [MulAut.conj_apply, inv_inv]
      group
    rw [hδy]
    exact hy
  obtain ⟨w, hw⟩ := hγ c₁⁻¹ c₀ hstab
  refine ⟨c₀ * (m w)⁻¹ * c₁⁻¹, ?_⟩
  intro e he
  rw [hc₀] at he
  obtain ⟨x, hx, hxeq⟩ := he
  rw [← hxeq]
  obtain ⟨u, rfl⟩ := hx
  let a : Fin 6 → ZMod p := Multiplicative.toAdd u
  have htu : t u = t (Multiplicative.ofAdd a) := rfl
  have hδ : δ (t (Multiplicative.ofAdd a)) =
      m w * t (Multiplicative.ofAdd a) * (m w)⁻¹ := by
    rw [hw a, ← hact w a]
  have hγe : γ ((MulAut.conj c₀).toMonoidHom (t (Multiplicative.ofAdd a))) =
      c₁ * δ (t (Multiplicative.ofAdd a)) * c₁⁻¹ := by
    dsimp only [δ]
    simp only [MulAut.mul_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rw [htu] at *
  rw [hγe, hδ]
  simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
  group

theorem frame_absorption {p : ℕ} [NeZero p] {R : Type} [Group R]
    {I : Set (MulAut R)} (hinn : ∀ ρ : R, MulAut.conj ρ ∈ I)
    (hmul : ∀ a ∈ I, ∀ b ∈ I, a * b ∈ I) (h : GGTwE6FramePackageSF p R I) {i : MulAut R}
    (hi : i ∈ I) {E : Subgroup R} (hE : IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    (hSC : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ ρ : R, ∀ e ∈ E, (MulAut.conj ρ)⁻¹ (i e) = e := by
  obtain ⟨t, m, h⟩ := h
  obtain ⟨hinj, hact, hU, hAut, hSF⟩ := h
  have h' : GGTwE6FrameAt p R I t m := ⟨hinj, hact, hU, hAut, hSF⟩
  have hγ : ∀ a b : R, (∀ x ∈ t.range, (MulAut.conj a * i * MulAut.conj b) x ∈ t.range) →
      ∃ w : WeylGroup TwistTag.E6.tag, ∀ s : Fin 6 → ZMod p,
        (MulAut.conj a * i * MulAut.conj b) (t (Multiplicative.ofAdd s)) =
          t (Multiplicative.ofAdd (TableBExc.torusAct TwistTag.E6.tag p w s)) := by
    intro a b hstab
    have hmem : MulAut.conj a * i * MulAut.conj b ∈ I := by
      have h1 : MulAut.conj a * i ∈ I := hmul (MulAut.conj a) (hinn a) i hi
      exact hmul (MulAut.conj a * i) h1 (MulAut.conj b) (hinn b)
    exact hSF (MulAut.conj a * i * MulAut.conj b) hmem hstab
  obtain ⟨r, hr⟩ := frame_conj_fix h' i hγ hE h4 hSC
  refine ⟨r⁻¹, ?_⟩
  intro e he
  have hinv : (MulAut.conj r⁻¹)⁻¹ = MulAut.conj r := by
    simp only [map_inv, inv_inv]
  rw [hinv]
  exact hr e he

end TwE6TB

end CFSG.StandardType
