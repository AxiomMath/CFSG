module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModelDefs
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative NbrOrth

private theorem hdRo7DFrTAux_frameSC_of_mulEquiv {p ℓ : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGTorusOrthFrameSC p R' ℓ) : GGTorusOrthFrameSC p R ℓ := by
  intro E hE h3 hsc
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hmem : ∀ x : R, e x ∈ E.map e.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hsc' : ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [hmem]
    refine hsc y (fun x hx => e.injective ?_) ?_
    · rw [map_mul, map_mul]
      exact hg _ ((hmem x).mpr hx)
    · apply e.injective
      rw [map_pow, hgp, map_one]
  obtain ⟨k, τ, hτinj, hτE, hperm, hcases⟩ :=
    h (E.map e.toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hE _) (hcard ▸ h3) hsc'
  have hconj : ∀ (w : R') (f f' : Fin k → Multiplicative (ZMod p)),
      w * τ f * w⁻¹ = τ f' → e.symm w * e.symm (τ f) * (e.symm w)⁻¹ = e.symm (τ f') := by
    intro w f f' hw
    rw [← map_inv, ← map_mul, ← map_mul, hw]
  refine ⟨k, e.symm.toMonoidHom.comp τ, e.symm.injective.comp hτinj, ?_, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      have h1 : τ f ∈ τ.range := ⟨f, rfl⟩
      rw [hτE] at h1
      rw [← hmem]
      simpa using h1
    · intro hx
      have h1 : e x ∈ τ.range := hτE ▸ (hmem x).mpr hx
      obtain ⟨f, hf⟩ := h1
      exact ⟨f, by simp [hf]⟩
  · intro σ
    obtain ⟨w, hw⟩ := hperm σ
    exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩
  · rcases hcases with ⟨hk, hdinv, hnorm⟩ | ⟨hk, hsgn, hnorm⟩
    · left
      refine ⟨hk, ?_, ?_⟩
      · intro i j hij
        obtain ⟨w, hw⟩ := hdinv i j hij
        exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩
      · intro g hg
        have hg' : ∀ x ∈ E.map e.toMonoidHom, e g * x * (e g)⁻¹ ∈ E.map e.toMonoidHom := by
          rintro _ ⟨y, hy, rfl⟩
          exact ⟨g * y * g⁻¹, hg y hy, by simp⟩
        obtain ⟨π, ε, hε, hprod, hrel⟩ := hnorm (e g) hg'
        refine ⟨π, ε, hε, hprod, fun f f' hff' => ?_⟩
        refine hrel f f' ?_
        apply e.symm.injective
        rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
        exact hff'
    · right
      refine ⟨hk, ?_, ?_⟩
      · intro i
        obtain ⟨w, hw⟩ := hsgn i
        exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩
      · intro g hg
        have hg' : ∀ x ∈ E.map e.toMonoidHom, e g * x * (e g)⁻¹ ∈ E.map e.toMonoidHom := by
          rintro _ ⟨y, hy, rfl⟩
          exact ⟨g * y * g⁻¹, hg y hy, by simp⟩
        obtain ⟨π, ε, hε, hrel⟩ := hnorm (e g) hg'
        refine ⟨π, ε, hε, fun f f' hff' => ?_⟩
        refine hrel f f' ?_
        apply e.symm.injective
        rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
        exact hff'

theorem ggTorusOrthFrameSC_of_mulEquiv {p ℓ : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGTorusOrthFrameSC p R ℓ) : GGTorusOrthFrameSC p R' ℓ :=
  hdRo7DFrTAux_frameSC_of_mulEquiv e.symm h

theorem ggTorusOrthFrameSC_of_centralCover {p ℓ : ℕ} (hp : p.Prime) {G R : Type} [Group G]
    [Finite G] [Group R] (q : G →* R) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center G) (hcp : ¬ p ∣ Nat.card (Subgroup.center G))
    (h : GGTorusOrthFrameSC p R ℓ) : GGTorusOrthFrameSC p G ℓ := by
  intro E hE h3 hsc
  have hinj : ∀ x ∈ E, ∀ y ∈ E, q x = q y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have hpow : (x⁻¹ * y) ^ p = 1 := hE.2 _ (E.mul_mem (E.inv_mem hx) hy)
    exact inv_mul_eq_one.mp (eq_one_of_mem_ker_of_pow hp hker hcp hmem hpow)
  let E₁ : Subgroup R := E.map q
  have hE₁ : IsElemAbelian p E₁ := CFSG.SectionRank.isElemAbelian_map hE q
  have hcard : Nat.card E₁ = Nat.card E := by
    have hbij : Function.Bijective
        (fun x : ↥E => (⟨q x, Subgroup.mem_map_of_mem q x.2⟩ : ↥E₁)) := by
      refine ⟨fun x y hxy => Subtype.ext (hinj x x.2 y y.2 (Subtype.ext_iff.mp hxy)), ?_⟩
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  have h3₁ : p ^ 3 ≤ Nat.card E₁ := by rw [hcard]; exact h3
  have hsc₁ : ∀ g : R, (∀ x ∈ E₁, g * x = x * g) → g ^ p = 1 → g ∈ E₁ := by
    intro g hg hgp
    obtain ⟨g', hg'q, hg'p⟩ := exists_lift_pow_eq_one hp hq hker hcp hgp
    have hcent : ∀ e ∈ E, g' * e = e * g' := by
      intro e he
      have hc : q (g' * e * g'⁻¹) = q e := by
        rw [map_mul, map_mul, map_inv, hg'q, hg (q e) (Subgroup.mem_map_of_mem q he)]
        group
      have hp' : (g' * e * g'⁻¹) ^ p = 1 := by
        rw [conj_pow, hE.2 e he, mul_one, mul_inv_cancel]
      have heq : g' * e * g'⁻¹ = e := eq_of_lift_pow_eq_one hp hker hcp hc hp' (hE.2 e he)
      calc g' * e = g' * e * g'⁻¹ * g' := by group
        _ = e * g' := by rw [heq]
    show g ∈ E₁
    rw [← hg'q]
    exact Subgroup.mem_map_of_mem q (hsc g' hcent hg'p)
  obtain ⟨k, τ₁, hτ₁inj, hτ₁range, hperm, hcases⟩ := h E₁ hE₁ h3₁ hsc₁
  have hpowZ : ∀ a : Multiplicative (ZMod p), a ^ p = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    simp
  have hV : ∀ v : Fin k → Multiplicative (ZMod p), v ^ p = 1 := by
    intro v
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    exact hpowZ (v i)
  obtain ⟨s, hs, hsp⟩ := exists_section_of_centerPrime (L' := G) (R := R) (ψ := q) hp hq
    hker hcp (V := Fin k → Multiplicative (ZMod p)) hV τ₁
  have hsinj : Function.Injective s := by
    intro x y hxy
    apply hτ₁inj
    rw [← hs x, ← hs y, hxy]
  have hrange : s.range = E := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hx
      have hmem : q (s v) ∈ E₁ := by
        rw [← hτ₁range]
        exact MonoidHom.mem_range.mpr ⟨v, (hs v).symm⟩
      obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp hmem
      have hsv : s v = e := eq_of_lift_pow_eq_one hp hker hcp heq.symm (hsp v) (hE.2 e he)
      rw [hsv]
      exact he
    · intro x hx
      have hmem : q x ∈ τ₁.range := by
        rw [hτ₁range]
        exact Subgroup.mem_map_of_mem q hx
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hmem
      exact MonoidHom.mem_range.mpr ⟨v,
        eq_of_lift_pow_eq_one hp hker hcp (by rw [hs v]; exact hv) (hsp v) (hE.2 x hx)⟩
  have hmove : ∀ F : (Fin k → Multiplicative (ZMod p)) → Fin k → Multiplicative (ZMod p),
      (∃ w : R, ∀ f, w * τ₁ f * w⁻¹ = τ₁ (F f)) →
      ∃ w : G, ∀ f, w * s f * w⁻¹ = s (F f) := by
    rintro F ⟨w, hw⟩
    obtain ⟨w', rfl⟩ := hq w
    refine ⟨w', fun f => ?_⟩
    have hq' : q (w' * s f * w'⁻¹) = q (s (F f)) := by
      simpa only [map_mul, map_inv, hs] using hw f
    exact eq_of_lift_pow_eq_one hp hker hcp hq'
      (by rw [conj_pow, hsp f, mul_one, mul_inv_cancel]) (hsp (F f))
  refine ⟨k, s, hsinj, hrange, fun σ => hmove (fun f => permAut σ f) (hperm σ), ?_⟩
  rcases hcases with ⟨hk, hdinv, hnorm⟩ | ⟨hk, hsgn, hnorm⟩
  · left
    refine ⟨hk, fun i j hij => hmove (fun f => dinv i j f) (hdinv i j hij), ?_⟩
    intro g hg
    have hg₁ : ∀ x ∈ E₁, q g * x * (q g)⁻¹ ∈ E₁ := by
      rintro _ ⟨e, he, rfl⟩
      exact ⟨g * e * g⁻¹, hg e he, by simp⟩
    obtain ⟨π, ε, hε, hprod, hrel⟩ := hnorm (q g) hg₁
    refine ⟨π, ε, hε, hprod, fun f f' hff' => ?_⟩
    have hqg : q g * τ₁ f * (q g)⁻¹ = τ₁ f' := by
      have := congrArg q hff'
      simpa only [map_mul, map_inv, hs] using this
    exact hrel f f' hqg
  · right
    refine ⟨hk, fun i => hmove (fun f => sgnAut i f) (hsgn i), ?_⟩
    intro g hg
    have hg₁ : ∀ x ∈ E₁, q g * x * (q g)⁻¹ ∈ E₁ := by
      rintro _ ⟨e, he, rfl⟩
      exact ⟨g * e * g⁻¹, hg e he, by simp⟩
    obtain ⟨π, ε, hε, hrel⟩ := hnorm (q g) hg₁
    refine ⟨π, ε, hε, fun f f' hff' => ?_⟩
    have hqg : q g * τ₁ f * (q g)⁻¹ = τ₁ f' := by
      have := congrArg q hff'
      simpa only [map_mul, map_inv, hs] using this
    exact hrel f f' hqg

end CFSG.StandardType
