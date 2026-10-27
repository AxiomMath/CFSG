module

public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.Sporadic.Schreier

variable {M : Type*} [Group M]

@[expose] def OddWitness (K : Subgroup M) (m : ℕ) : Prop :=
  ∀ x ∈ K, x ≠ 1 → x ^ m = 1 →
    (∃ h ∈ K, (x * (h * x * h⁻¹)) ^ m ≠ 1) ∨
      ∃ h₁ ∈ K, ∃ h₂ ∈ K, (x * (h₁ * x * h₁⁻¹) * (h₂ * x * h₂⁻¹)) ^ m ≠ 1

theorem card_dvd_of_odd {K : Type*} [Group K] {m v : ℕ} (hK : Nat.card K = 2 ^ v * m)
    (N : Subgroup K) (hodd : Odd (Nat.card N)) : Nat.card N ∣ m := by
  have hdvd : Nat.card N ∣ 2 ^ v * m := hK ▸ N.card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card N) (2 ^ v) :=
    Nat.Coprime.pow_right v hodd.coprime_two_right
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem normal_eq_bot_of_oddWitness {K : Subgroup M} {m v : ℕ} (hK : Nat.card K = 2 ^ v * m)
    (hw : OddWitness K m) (N : Subgroup K) [N.Normal] (hodd : Odd (Nat.card N)) : N = ⊥ := by
  by_contra hne
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hNm := card_dvd_of_odd hK N hodd
  have hpow : ∀ z : N, z ^ m = 1 := fun z =>
    (orderOf_dvd_iff_pow_eq_one).1 ((orderOf_dvd_natCard z).trans hNm)
  have hpowK : ∀ z : K, z ∈ N → (z : M) ^ m = 1 := fun z hz => by
    have h := hpow ⟨z, hz⟩
    have h' := congrArg (fun w : N => ((w : K) : M)) h
    simpa using h'
  have hxK : ((x : K) : M) ∈ K := (x : K).2
  have hxne : ((x : K) : M) ≠ 1 := by
    intro h
    apply hx1
    exact Subtype.ext (Subtype.ext h)
  rcases hw _ hxK hxne (hpowK x x.2) with ⟨h, hh, hne'⟩ | ⟨h₁, hh₁, h₂, hh₂, hne'⟩
  · apply hne'
    have hmem : (x : K) * ((⟨h, hh⟩ : K) * x * (⟨h, hh⟩ : K)⁻¹) ∈ N :=
      N.mul_mem x.2 (Subgroup.Normal.conj_mem inferInstance _ x.2 _)
    simpa using hpowK _ hmem
  · apply hne'
    have hmem : (x : K) * ((⟨h₁, hh₁⟩ : K) * x * (⟨h₁, hh₁⟩ : K)⁻¹) *
        ((⟨h₂, hh₂⟩ : K) * x * (⟨h₂, hh₂⟩ : K)⁻¹) ∈ N :=
      N.mul_mem (N.mul_mem x.2 (Subgroup.Normal.conj_mem inferInstance _ x.2 _))
        (Subgroup.Normal.conj_mem inferInstance _ x.2 _)
    simpa using hpowK _ hmem

theorem oddCore_eq_bot_of_oddWitness {K : Subgroup M} {m v : ℕ} (hK : Nat.card K = 2 ^ v * m)
    (hw : OddWitness K m) : CFSG.oddCore K = ⊥ :=
  sSup_eq_bot.2 fun N hN => by
    have := hN.1
    exact normal_eq_bot_of_oddWitness hK hw N hN.2

theorem OddWitness.map_conj {K : Subgroup M} {m : ℕ} (hw : OddWitness K m) (s : M) :
    OddWitness (K.map (MulAut.conj s).toMonoidHom) m := by
  rintro y ⟨x, hx, rfl⟩ hy1 hym
  have hconj : ∀ z : M, (MulAut.conj s).toMonoidHom z = s * z * s⁻¹ := fun z => rfl
  have hx1 : x ≠ 1 := fun h => hy1 (by rw [h, map_one])
  have hxm : x ^ m = 1 := by
    rw [← map_pow] at hym
    exact (MulAut.conj s).injective (by simpa using hym)
  have hmap : ∀ z : M, ((MulAut.conj s).toMonoidHom z) ^ m = 1 → z ^ m = 1 := fun z hz => by
    rw [← map_pow] at hz
    exact (MulAut.conj s).injective (by simpa using hz)
  rcases hw x hx hx1 hxm with ⟨h, hh, hne⟩ | ⟨h₁, hh₁, h₂, hh₂, hne⟩
  · refine Or.inl ⟨s * h * s⁻¹, ⟨h, hh, rfl⟩, fun heq => hne (hmap _ ?_)⟩
    rw [hconj] at heq ⊢
    rw [show s * (x * (h * x * h⁻¹)) * s⁻¹ =
      s * x * s⁻¹ * (s * h * s⁻¹ * (s * x * s⁻¹) * (s * h * s⁻¹)⁻¹) by group]
    exact heq
  · refine Or.inr ⟨s * h₁ * s⁻¹, ⟨h₁, hh₁, rfl⟩, s * h₂ * s⁻¹, ⟨h₂, hh₂, rfl⟩,
      fun heq => hne (hmap _ ?_)⟩
    rw [hconj] at heq ⊢
    rw [show s * (x * (h₁ * x * h₁⁻¹) * (h₂ * x * h₂⁻¹)) * s⁻¹ =
      s * x * s⁻¹ * (s * h₁ * s⁻¹ * (s * x * s⁻¹) * (s * h₁ * s⁻¹)⁻¹) *
        (s * h₂ * s⁻¹ * (s * x * s⁻¹) * (s * h₂ * s⁻¹)⁻¹) by group]
    exact heq

theorem OddWitness.of_map {M' : Type*} [Group M'] {f : M →* M'} (hf : Function.Injective f)
    {K : Subgroup M} {m : ℕ} (hw : OddWitness (K.map f) m) : OddWitness K m := by
  intro x hx hx1 hxm
  have hfx1 : f x ≠ 1 := fun h => hx1 (hf (by rw [h, map_one]))
  have hfxm : f x ^ m = 1 := by rw [← map_pow, hxm, map_one]
  rcases hw (f x) ⟨x, hx, rfl⟩ hfx1 hfxm with ⟨h, ⟨h', hh', rfl⟩, hne⟩ |
      ⟨h₁, ⟨h₁', hh₁', rfl⟩, h₂, ⟨h₂', hh₂', rfl⟩, hne⟩
  · refine Or.inl ⟨h', hh', fun heq => hne ?_⟩
    have := congrArg f heq
    simpa only [map_mul, map_inv, map_pow, map_one] using this
  · refine Or.inr ⟨h₁', hh₁', h₂', hh₂', fun heq => hne ?_⟩
    have := congrArg f heq
    simpa only [map_mul, map_inv, map_pow, map_one] using this

end CFSG.Sporadic.Schreier
