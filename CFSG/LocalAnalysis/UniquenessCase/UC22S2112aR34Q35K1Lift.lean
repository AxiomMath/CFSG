module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Prime.Factorial

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open scoped Pointwise

open Subgroup

theorem uc22s2112r34q35_exists_lift_mem_normalizer {X H : Type} [Group X] [Group H] [Finite H]
    {Z : Subgroup H} [Z.Normal] (hZ : IsPGroup 2 Z) (e : X ≃* H ⧸ Z) (S : Sylow 2 H)
    (P : Sylow 2 X) {x : X} (hx : x ∈ normalizer ((P : Subgroup X) : Set X)) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hxs : orderOf x = s) :
    ∃ h : H, h ^ s = 1 ∧ h ≠ 1 ∧ h ∈ normalizer ((S : Subgroup H) : Set H) := by
  have : Finite X := Finite.of_injective (e : X → H ⧸ Z) e.injective
  have hZle : (Z : Subgroup H) ≤ (S : Subgroup H) := IsPGroup.le_sylow_of_normal hZ S
  let Sbar : Sylow 2 (H ⧸ Z) :=
    Sylow.mapSurjective (f := QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) S
  let Pbar : Sylow 2 (H ⧸ Z) :=
    Sylow.mapSurjective (f := (e : X →* H ⧸ Z)) e.surjective P
  have hSbar : (Sbar : Subgroup (H ⧸ Z)) = (S : Subgroup H).map (QuotientGroup.mk' Z) :=
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective Z) S
  have hPbar : (Pbar : Subgroup (H ⧸ Z)) = (P : Subgroup X).map (e : X →* H ⧸ Z) :=
    Sylow.coe_mapSurjective e.surjective P
  have hxbar : e x ∈ normalizer ((Pbar : Subgroup (H ⧸ Z)) : Set (H ⧸ Z)) := by
    have hmem : e x ∈ (normalizer ((P : Subgroup X) : Set X)).map (e : X →* H ⧸ Z) :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have h2 : e x ∈ normalizer ((P : Subgroup X).map (e : X →* H ⧸ Z)) :=
      Subgroup.le_normalizer_map (e : X →* H ⧸ Z) hmem
    rwa [← hPbar] at h2
  have hxbar_order : orderOf (e x) = s := by
    rw [MulEquiv.orderOf_eq, hxs]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (H ⧸ Z) Pbar Sbar
  set x'' : H ⧸ Z := g * e x * g⁻¹ with hx''def
  have hx''ord : orderOf x'' = s := by
    rw [hx''def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hxbar_order]
  have hx''pow : x'' ^ s = 1 := by
    rw [← hx''ord]
    exact pow_orderOf_eq_one x''
  have hx''ne : x'' ≠ 1 := by
    intro h1
    have hord : orderOf x'' = 1 := by rw [h1, orderOf_one]
    rw [hx''ord] at hord
    exact hs.ne_one hord
  have hsub : (Pbar : Subgroup (H ⧸ Z)).map (MulAut.conj g) = (Sbar : Subgroup (H ⧸ Z)) := by
    have hsmul : (MulAut.conj g) • (Pbar : Subgroup (H ⧸ Z)) = (Sbar : Subgroup (H ⧸ Z)) := by
      rw [← hg]
      exact Sylow.coe_subgroup_smul.symm
    rwa [Subgroup.pointwise_smul_def] at hsmul
  have hx''norm : x'' ∈ normalizer ((Sbar : Subgroup (H ⧸ Z)) : Set (H ⧸ Z)) := by
    have h1 : x'' ∈ (normalizer ((Pbar : Subgroup (H ⧸ Z)) : Set (H ⧸ Z))).map
        (MulAut.conj g) :=
      Subgroup.mem_map.mpr ⟨e x, hxbar, rfl⟩
    rw [Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective, hsub] at h1
    exact h1
  obtain ⟨h₀, hh₀⟩ := QuotientGroup.mk'_surjective Z x''
  obtain ⟨a, ha⟩ := IsPGroup.exists_card_eq (p := 2) hZ
  have hsZ : h₀ ^ s ∈ Z := by
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_pow, hh₀, hx''pow]
  have hZpow : (h₀ ^ s) ^ 2 ^ a = 1 := by
    have h := pow_card_eq_one' (x := (⟨h₀ ^ s, hsZ⟩ : Z))
    rw [ha] at h
    simpa using congrArg Subtype.val h
  have hcop : Nat.Coprime (2 ^ a) s :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hs).mpr hs2.symm)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hs.one_lt
  refine ⟨h₀ ^ (2 ^ a * u), ?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm (2 ^ a * u) s, pow_mul, pow_mul, hZpow, one_pow]
  · intro h1
    apply hx''ne
    have hmk : (QuotientGroup.mk' Z) (h₀ ^ (2 ^ a * u)) = x'' := by
      rw [map_pow, hh₀, ← pow_mod_orderOf x'' (2 ^ a * u), hx''ord, hu, pow_one]
    rw [← hmk, h1, map_one]
  ·
    have hmemS : ∀ y : H, (QuotientGroup.mk' Z) y ∈ (Sbar : Subgroup (H ⧸ Z)) ↔
        y ∈ (S : Subgroup H) := by
      intro y
      rw [hSbar, Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, hzy⟩
        have hzy' : (QuotientGroup.mk' Z) (z⁻¹ * y) = 1 := by
          rw [map_mul, map_inv, hzy, inv_mul_cancel]
        have hmem : z⁻¹ * y ∈ Z := by
          rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker]
          exact hzy'
        have hy : y = z * (z⁻¹ * y) := by group
        rw [hy]
        exact (S : Subgroup H).mul_mem hz (hZle hmem)
      · intro hy
        exact ⟨y, hy, rfl⟩
    have hmk : (QuotientGroup.mk' Z) (h₀ ^ (2 ^ a * u)) = x'' := by
      rw [map_pow, hh₀, ← pow_mod_orderOf x'' (2 ^ a * u), hx''ord, hu, pow_one]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← hmemS y, ← hmemS (h₀ ^ (2 ^ a * u) * y * (h₀ ^ (2 ^ a * u))⁻¹)]
    rw [Subgroup.mem_normalizer_iff] at hx''norm
    rw [show (QuotientGroup.mk' Z) (h₀ ^ (2 ^ a * u) * y * (h₀ ^ (2 ^ a * u))⁻¹) =
      x'' * (QuotientGroup.mk' Z) y * x''⁻¹ by rw [map_mul, map_mul, map_inv, hmk]]
    exact hx''norm _

theorem uc22s2112r34q35_commute_of_forall_conj_mem {G : Type} [Group G] {h : G} {s : ℕ}
    (hs : s.Prime) (hh : h ^ s = 1) (A : Finset G) (hA : A.card < s)
    (hmap : ∀ a ∈ A, h * a * h⁻¹ ∈ A) : ∀ a ∈ A, h * a = a * h := by
  intro a ha
  have hinj : Function.Injective (fun x : ↥A => (⟨h * (x : G) * h⁻¹, hmap x.1 x.2⟩ : ↥A)) := by
    intro x y hxy
    have h1 : h * (x : G) * h⁻¹ = h * (y : G) * h⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  let σ : Equiv.Perm ↥A := Equiv.ofBijective _ hinj.bijective_of_finite
  have hσ : ∀ x : ↥A, (σ x : G) = h * (x : G) * h⁻¹ := fun x => rfl
  have hpow : ∀ (k : ℕ) (x : ↥A), ((σ ^ k) x : G) = h ^ k * (x : G) * (h ^ k)⁻¹ := by
    intro k
    induction k with
    | zero =>
      intro x
      rw [pow_zero, pow_zero]
      simp
    | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih (σ x), hσ x, pow_succ]
      group
  have hσs : σ ^ s = 1 := by
    ext x
    have hx := hpow s x
    rw [hh] at hx
    simpa using hx
  have hdvd : orderOf σ ∣ s := orderOf_dvd_iff_pow_eq_one.mpr hσs
  have hfac : orderOf σ ∣ A.card.factorial := by
    have h := orderOf_dvd_natCard σ
    rwa [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe] at h
  have hnot : ¬ s ∣ A.card.factorial := by
    rw [Nat.Prime.dvd_factorial hs]
    omega
  rcases Nat.Prime.eq_one_or_self_of_dvd hs (orderOf σ) hdvd with h1 | h1
  · have hfix : σ ⟨a, ha⟩ = ⟨a, ha⟩ := by rw [orderOf_eq_one_iff.mp h1]; rfl
    have hconj : h * a * h⁻¹ = a := by
      have h2 := congrArg Subtype.val hfix
      simpa [hσ] using h2
    calc h * a = h * a * h⁻¹ * h := by group
      _ = a * h := by rw [hconj]
  · exact absurd (h1 ▸ hfac) hnot

end CFSG.LocalAnalysis.UniquenessCase.UC22
