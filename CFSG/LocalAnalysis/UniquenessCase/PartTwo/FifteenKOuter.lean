module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

theorem s15k_out_embed {S H : Type} [Group S] [Group H] (f : S →* H) (hf : Function.Injective f)
    (hn : f.range.Normal) (hc : ∀ h : H, (∀ s : S, h * f s = f s * h) → h = 1) :
    ∃ Ψ : H →* MulAut S, Function.Injective Ψ ∧
      ∀ (h : H) (s : S), f (Ψ h s) = h * f s * h⁻¹ := by
  haveI := hn
  let Ψ : H →* MulAut S :=
    (MulAut.congr (MonoidHom.ofInjective hf).symm).toMonoidHom.comp
      (MulAut.conjNormal (H := f.range))
  have hΨ : ∀ (h : H) (s : S), f (Ψ h s) = h * f s * h⁻¹ := by
    intro h s
    change f ((MonoidHom.ofInjective hf).symm
      (MulAut.conjNormal (H := f.range) h (MonoidHom.ofInjective hf s))) = h * f s * h⁻¹
    rw [MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply]
    rfl
  refine ⟨Ψ, ?_, hΨ⟩
  rw [injective_iff_map_eq_one]
  intro h h1
  apply hc
  intro s
  have h2 := hΨ h s
  rw [h1] at h2
  have h3 : f s = h * f s * h⁻¹ := by simpa using h2
  exact mul_inv_eq_iff_eq_mul.mp h3.symm

theorem s15k_out_index_dvd_outer {S H : Type} [Group S] [Group H] (f : S →* H)
    (hf : Function.Injective f) (hn : f.range.Normal)
    (hc : ∀ h : H, (∀ s : S, h * f s = f s * h) → h = 1) :
    f.range.index ∣ Nat.card (Outer S) := by
  obtain ⟨Ψ, hΨinj, hΨ⟩ := s15k_out_embed f hf hn hc
  have hΨf : ∀ s : S, Ψ (f s) = MulAut.conj s := by
    intro s
    refine MulEquiv.ext fun t => hf ?_
    rw [hΨ, MulAut.conj_apply, map_mul, map_mul, map_inv]
  let ψ : H →* Outer S := (QuotientGroup.mk' (inner S)).comp Ψ
  have hker : ψ.ker = f.range := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : Ψ x ∈ inner S := (QuotientGroup.eq_one_iff _).mp hx
      obtain ⟨s, hs⟩ := hx'
      exact ⟨s, hΨinj ((hΨf s).trans hs)⟩
    · rintro ⟨s, rfl⟩
      rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk' (inner S)) (Ψ (f s)) = 1
      rw [hΨf]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨s, rfl⟩
  rw [← hker, Subgroup.index_eq_card]
  exact Subgroup.card_dvd_of_injective _ (QuotientGroup.kerLift_injective ψ)

theorem s15k_out_card_eq {S H : Type} [Group S] [Group H] (f : S →* H)
    (hf : Function.Injective f) : Nat.card S * f.range.index = Nat.card H := by
  rw [← Subgroup.card_mul_index f.range, Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]

theorem s15k_out_index_pow_of_aut_le {S H : Type} [Group S] [Group H] [Finite S] [Finite H]
    (f : S →* H) (hf : Function.Injective f) (hn : f.range.Normal)
    (hc : ∀ h : H, (∀ s : S, h * f s = f s * h) → h = 1)
    (hA : Nat.card (MulAut S) ≤ 2 * Nat.card S) : ∃ k : ℕ, f.range.index = 2 ^ k := by
  obtain ⟨Ψ, hΨinj, -⟩ := s15k_out_embed f hf hn hc
  have h1 : Nat.card H ≤ Nat.card (MulAut S) := Nat.card_le_card_of_injective _ hΨinj
  have h2 : Nat.card f.range * f.range.index = Nat.card H := Subgroup.card_mul_index f.range
  have h3 : Nat.card f.range = Nat.card S := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm
  have hS : 0 < Nat.card S := Nat.card_pos
  have h4 : f.range.index ≤ 2 := by
    rw [h3] at h2
    have : Nat.card S * f.range.index ≤ Nat.card S * 2 := by omega
    exact Nat.le_of_mul_le_mul_left this hS
  have h5 : 1 ≤ f.range.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  interval_cases hi : f.range.index
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩

theorem s15k_out_odd_mem {S H : Type} [Group S] [Group H] [Finite H] (f : S →* H)
    (hn : f.range.Normal) {k : ℕ} (hk : f.range.index = 2 ^ k) {x : H}
    (hx : Odd (orderOf x)) : x ∈ f.range := by
  haveI := hn
  have h1 : orderOf (QuotientGroup.mk x : H ⧸ f.range) ∣ orderOf x :=
    orderOf_map_dvd (QuotientGroup.mk' f.range) x
  have h2 : orderOf (QuotientGroup.mk x : H ⧸ f.range) ∣ 2 ^ k := by
    rw [← hk, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hx)
  have h3 : orderOf (QuotientGroup.mk x : H ⧸ f.range) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem s15k_out_elem_le_range {S H : Type} [Group S] [Group H] [Finite H] (f : S →* H)
    (hn : f.range.Normal) {k : ℕ} (hk : f.range.index = 2 ^ k) {p : ℕ} (hp : Odd p)
    {E : Subgroup H} (hE : IsElemAbelian p E) : E ≤ f.range := by
  intro x hx
  refine s15k_out_odd_mem f hn hk ?_
  exact Odd.of_dvd_nat hp (orderOf_dvd_of_pow_eq_one (hE.2 x hx))

theorem s15k_out_elem_comap {S H : Type} [Group S] [Group H] (f : S →* H)
    (hf : Function.Injective f) {p : ℕ} {E : Subgroup H} (hE : IsElemAbelian p E)
    (hle : E ≤ f.range) :
    ∃ E' : Subgroup S, IsElemAbelian p E' ∧ E'.map f = E ∧ Nat.card E' = Nat.card E := by
  refine ⟨E.comap f, ⟨?_, ?_⟩, Subgroup.map_comap_eq_self hle, ?_⟩
  · refine isMulCommutative_iff.mpr fun a b => ?_
    have h1 := (isMulCommutative_iff.mp hE.1) ⟨f a, a.2⟩ ⟨f b, b.2⟩
    apply Subtype.ext
    apply hf
    simpa using congrArg Subtype.val h1
  · intro x hx
    apply hf
    rw [map_pow, map_one]
    exact hE.2 _ hx
  · calc Nat.card (E.comap f) = Nat.card ((E.comap f).map f) :=
        (Subgroup.card_map_of_injective hf).symm
      _ = Nat.card E := by rw [Subgroup.map_comap_eq_self hle]

theorem s15k_out_pRank_le {S H : Type} [Group S] [Group H] [Finite H] (f : S →* H)
    (hf : Function.Injective f) (hn : f.range.Normal) {k : ℕ} (hk : f.range.index = 2 ^ k)
    {p : ℕ} (hp : Odd p) (r : ℕ)
    (hr : ∀ E : Subgroup S, IsElemAbelian p E → ∀ j : ℕ, Nat.card E = p ^ j → j ≤ r) :
    pRank p (⊤ : Subgroup H) ≤ r := by
  unfold pRank
  apply csSup_le'
  rintro j ⟨E, -, hE, hj⟩
  obtain ⟨E', hE', -, hcard⟩ :=
    s15k_out_elem_comap f hf hE (s15k_out_elem_le_range f hn hk hp hE)
  exact hr E' hE' j (hcard.trans hj)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
