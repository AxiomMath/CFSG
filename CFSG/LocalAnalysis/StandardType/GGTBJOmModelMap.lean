module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusForms
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB
open CFSG.RankThree.Classical2 (orthDerived)

theorem selfCent_map_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {E : Subgroup R} (hsc : ∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
  intro g hg hgp
  refine ⟨e.symm g, hsc (e.symm g) (fun x hx => ?_) ?_, e.apply_symm_apply g⟩
  · apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hg (e x) ⟨x, hx, rfl⟩
  · apply e.injective
    rw [map_pow, e.apply_symm_apply, hgp, map_one]

theorem natCard_map_mulEquiv {R R' : Type} [Group R] [Group R'] (e : R ≃* R') (E : Subgroup R) :
    Nat.card (E.map e.toMonoidHom) = Nat.card E := by
  exact Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective

theorem exists_ne_one_of_pow_le_card {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {E : Subgroup R} (h3 : p ^ 3 ≤ Nat.card E) : ∃ b ∈ E, b ≠ 1 := by
  by_contra h
  push Not at h
  have hE1 : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h
  rw [hE1, Subgroup.card_bot] at h3
  have := Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt
  omega

theorem map_subtype_hyps {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {p : ℕ} (E : Subgroup ↥(orthDerived Q)) (hE : IsElemAbelian p E)
    (hne : ∃ b ∈ E, b ≠ 1)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    E.map (orthDerived Q).subtype ≤ orthDerived Q ∧
      (∀ a ∈ E.map (orthDerived Q).subtype, a ^ p = 1) ∧
      (∀ a ∈ E.map (orthDerived Q).subtype, ∀ b ∈ E.map (orthDerived Q).subtype,
        a * b = b * a) ∧
      (∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ E.map (orthDerived Q).subtype, g * c = c * g) →
        g ∈ E.map (orthDerived Q).subtype) ∧
      (∃ b ∈ E.map (orthDerived Q).subtype, b ≠ 1) := by
  set A := E.map (orthDerived Q).subtype with hA
  have hAΩ : A ≤ orthDerived Q := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hApow : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE hx hy]
  have hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    refine ⟨⟨g, hg⟩, hsc ⟨g, hg⟩ (fun e he => Subtype.ext (hgc _ ⟨e, he, rfl⟩))
      (Subtype.ext (by rw [Subgroup.coe_pow]; exact hgp)), rfl⟩
  have hneA : ∃ b ∈ A, b ≠ 1 := by
    obtain ⟨b, hb, hb1⟩ := hne
    refine ⟨(b : V ≃ₗ[K] V), ?_, ?_⟩
    · exact ⟨b, hb, rfl⟩
    · intro h
      exact hb1 (Subtype.ext h)
  exact ⟨hAΩ, hApow, hAcomm, hmax, hneA⟩

theorem mem_range_iff_mem_comap_model {T G R : Type} [Group T] [Group G] [Group R]
    {Ω : Subgroup G} (e : R ≃* ↥Ω) (E₀ : Subgroup R) (τ : T →* G) (hτ : ∀ f, τ f ∈ Ω)
    (hrange : τ.range = (E₀.map e.toMonoidHom).map Ω.subtype) (x : R) :
    x ∈ E₀ ↔ x ∈ (e.symm.toMonoidHom.comp (τ.codRestrict Ω hτ)).range := by
  constructor
  · intro hx
    have h1 : (↑(e x) : G) ∈ τ.range := by
      rw [hrange]
      exact Subgroup.mem_map_of_mem Ω.subtype ⟨x, hx, rfl⟩
    obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp h1
    refine MonoidHom.mem_range.mpr ⟨f, ?_⟩
    rw [MonoidHom.comp_apply, show τ.codRestrict Ω hτ f = e x from Subtype.ext hf]
    exact e.symm_apply_apply x
  · rintro ⟨f, hf⟩
    have h2 : e x = τ.codRestrict Ω hτ f := by
      rw [← hf]
      exact e.apply_symm_apply (τ.codRestrict Ω hτ f)
    have h4 : τ f ∈ (E₀.map e.toMonoidHom).map Ω.subtype := by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨f, rfl⟩
    obtain ⟨y, hy, hyf⟩ := Subgroup.mem_map.mp h4
    have h5 : τ.codRestrict Ω hτ f ∈ E₀.map e.toMonoidHom := by
      rw [show τ.codRestrict Ω hτ f = y from Subtype.ext hyf.symm]
      exact hy
    rw [← h2] at h5
    obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp h5
    exact e.injective hze ▸ hz

theorem modEq_neg_one_charSum {K : Type} [Finite K] [Nonempty K] {p m : ℕ}
    (hpq : p ∣ Nat.card K - 1 ∨ (Odd m ∧ p ∣ Nat.card K + 1)) :
    -(Nat.card K : ℤ) ^ (m + 1) ≡ -1 [ZMOD p] := by
  have hq : (Nat.card K : ℤ) ^ (m + 1) ≡ 1 [ZMOD p] := by
    rcases hpq with h1 | ⟨hmo, h1⟩
    · simpa using (OrthTorus.modEq_one_of_dvd Nat.card_pos h1).pow (m + 1)
    · have h2 := (OrthTorus.modEq_neg_one_of_dvd h1).pow (m + 1)
      rwa [Even.neg_one_pow hmo.add_one] at h2
  exact hq.neg

theorem modEq_one_charSum {K : Type} [Finite K] {p m : ℕ} (hm : Even m)
    (hpq : p ∣ Nat.card K + 1) : -(Nat.card K : ℤ) ^ (m + 1) ≡ 1 [ZMOD p] := by
  have h := (OrthTorus.modEq_neg_one_of_dvd hpq).pow (m + 1)
  rw [Odd.neg_one_pow (Even.add_one hm)] at h
  simpa using h.neg

end CFSG.StandardType

end
