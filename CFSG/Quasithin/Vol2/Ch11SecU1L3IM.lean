module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

variable {H X : Type} [Group H] [Group X]

theorem exists_lift_odd_prime [Finite H] (φ : H →* X) {Y : Subgroup H}
    (hcen : ∀ k ∈ Y, φ k = 1 → ∀ y ∈ Y, k * y = y * k) (h2 : ∀ k ∈ Y, φ k = 1 → k * k = 1)
    {Pbar : Subgroup X} (hPr : (Nat.card Pbar).Prime) (hP2 : Nat.card Pbar ≠ 2)
    (hPY : Pbar ≤ Y.map φ) :
    ∃ P : Subgroup H, P ≤ Y ∧ Nat.card P = Nat.card Pbar ∧ P.map φ = Pbar ∧
      ∀ q ∈ Subgroup.normalizer (Y : Set H), φ q ∈ Subgroup.normalizer (Pbar : Set X) →
        q ∈ Subgroup.normalizer (P : Set H) := by
  classical
  set r := Nat.card Pbar with hr
  have hrodd : Odd r := hPr.odd_of_ne_two hP2
  have : Finite ↥Pbar := Nat.finite_of_card_ne_zero hPr.ne_zero
  set R : Subgroup H := Pbar.comap φ ⊓ Y with hR
  let φR : ↥R →* ↥Pbar := (φ.comp R.subtype).codRestrict Pbar fun x => x.2.1
  have hcyc : IsCyclic ↥Pbar := isCyclic_of_prime_card (p := r) (hp := ⟨hPr⟩) rfl
  have hker : φR.ker ≤ Subgroup.center ↥R := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro y
    have hk1 : φ (k : H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
    exact Subtype.ext (hcen k k.2.2 hk1 y y.2.2).symm
  have hRcomm : ∀ a b : ↥R, a * b = b * a :=
    (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center φR hker).is_comm.comm
  let P : Subgroup H :=
    { carrier := {x | x ∈ R ∧ x ^ r = 1}
      one_mem' := ⟨R.one_mem, one_pow r⟩
      mul_mem' := by
        rintro x y ⟨hx, hxr⟩ ⟨hy, hyr⟩
        refine ⟨R.mul_mem hx hy, ?_⟩
        have hc : Commute x y := by
          have := hRcomm ⟨x, hx⟩ ⟨y, hy⟩
          exact congrArg Subtype.val this
        rw [hc.mul_pow, hxr, hyr, one_mul]
      inv_mem' := by
        rintro x ⟨hx, hxr⟩
        exact ⟨R.inv_mem hx, by rw [inv_pow, hxr, inv_one]⟩ }
  have hPR : P ≤ R := fun _ hx => hx.1
  have hinj : ∀ x ∈ P, φ x = 1 → x = 1 := by
    rintro x ⟨hxR, hxr⟩ hx1
    have hxx := h2 x hxR.2 hx1
    obtain ⟨k, hk⟩ := hrodd
    calc x = x ^ r * (x * x)⁻¹ ^ k := by rw [hk, pow_succ, pow_mul, pow_two, hxx]; group
      _ = 1 := by rw [hxr, hxx, inv_one, one_pow, one_mul]
  have hle : P.map φ ≤ Pbar := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1.1
  have hmap : P.map φ = Pbar := by
    rcases (Nat.dvd_prime hPr).mp (Subgroup.card_dvd_of_le hle) with h1 | h1
    · exfalso
      obtain ⟨w, hw1⟩ : ∃ w : ↥Pbar, w ≠ 1 := by
        have : Nontrivial ↥Pbar := Finite.one_lt_card_iff_nontrivial.mp hPr.one_lt
        exact exists_ne 1
      obtain ⟨x, hxY, hxw⟩ := hPY w.2
      have hxR : x ∈ R := ⟨by simp [hxw], hxY⟩
      have hx2 : x * x ∈ P := by
        refine ⟨R.mul_mem hxR hxR, ?_⟩
        have hxr : φ (x ^ r) = 1 := by
          rw [map_pow, hxw]
          exact congrArg Subtype.val (pow_card_eq_one' (G := ↥Pbar) (x := w))
        have hxx := h2 (x ^ r) (Y.pow_mem hxY r) hxr
        calc (x * x) ^ r = x ^ r * x ^ r := by
              rw [← pow_two, ← pow_mul, mul_comm, pow_mul, pow_two]
          _ = 1 := hxx
      have hmem : φ (x * x) ∈ P.map φ := ⟨x * x, hx2, rfl⟩
      rw [Subgroup.card_eq_one.mp h1, Subgroup.mem_bot, map_mul, hxw] at hmem
      apply hw1
      have hww : w * w = 1 := Subtype.ext hmem
      have hord : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hww)
      have hordr : orderOf w ∣ r := orderOf_dvd_natCard w
      have h3 : orderOf w ∣ Nat.gcd 2 r := Nat.dvd_gcd hord hordr
      rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hrodd)] at h3
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    · exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq h1.symm)
  have hcardP : Nat.card P = r := by
    have hφinj : Function.Injective (φ.comp P.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact Subtype.ext (hinj x x.2 hx)
    rw [hr, ← hmap, Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, MonoidHom.range_comp,
      Subgroup.range_subtype]
  refine ⟨P, fun _ hx => hx.1.2, hcardP, hmap, fun q hqY hqP => ?_⟩
  have hconj : ∀ g ∈ Subgroup.normalizer (Y : Set H), φ g ∈ Subgroup.normalizer (Pbar : Set X) →
      ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    rintro g hgY hgP x ⟨⟨hxP, hxY⟩, hxr⟩
    refine ⟨⟨?_, (Subgroup.mem_normalizer_iff.mp hgY x).mp hxY⟩, ?_⟩
    · show φ (g * x * g⁻¹) ∈ Pbar
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hgP (φ x)).mp hxP
    · rw [conj_pow, hxr, mul_one, mul_inv_cancel]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hconj q hqY hqP x, fun hx => ?_⟩
  have h1 := hconj q⁻¹ (Subgroup.inv_mem _ hqY) (by rw [map_inv]; exact Subgroup.inv_mem _ hqP)
    _ hx
  simpa [mul_assoc] using h1

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
