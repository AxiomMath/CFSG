module

public import CFSG.Quasithin.EmptyFaithful.SzN32Hx

public section

namespace CFSG.Quasithin.SzN32

namespace Step

variable {G : Type*} [Group G]

theorem cube_mul {x y d : G} (hd : d ∈ Subgroup.center G) (hyx : y * x = x * y * d) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 * d ^ 3 := by
  have hc : ∀ g : G, g * d = d * g := Subgroup.mem_center_iff.mp hd
  have hmove : ∀ a b : G, a * d * b = a * b * d := fun a b => by
    rw [mul_assoc, ← hc b, ← mul_assoc]
  have hmove2 : ∀ a b : G, a * (d * d) * b = a * b * (d * d) := fun a b => by
    calc a * (d * d) * b = a * d * (d * b) := by group
      _ = a * d * (b * d) := by rw [← hc b]
      _ = a * (d * b) * d := by group
      _ = a * (b * d) * d := by rw [← hc b]
      _ = a * b * (d * d) := by group
  have hyyx : y * y * x = x * y * y * (d * d) := by
    calc y * y * x = y * (y * x) := by rw [mul_assoc]
      _ = y * (x * y * d) := by rw [hyx]
      _ = y * x * y * d := by group
      _ = x * y * d * y * d := by rw [hyx]
      _ = x * y * (d * y) * d := by group
      _ = x * y * (y * d) * d := by rw [← hc y]
      _ = x * y * y * (d * d) := by group
  calc (x * y) ^ 3 = x * (y * x) * y * x * y := by rw [pow_three']; group
    _ = x * (x * y * d) * y * x * y := by rw [hyx]
    _ = x * x * y * d * (y * x * y) := by group
    _ = x * x * y * (y * x * y) * d := by rw [hmove]
    _ = x * x * (y * y * x) * y * d := by group
    _ = x * x * (x * y * y * (d * d)) * y * d := by rw [hyyx]
    _ = x * x * x * y * y * (d * d) * y * d := by group
    _ = x * x * x * y * y * y * (d * d) * d := by rw [hmove2]
    _ = x ^ 3 * y ^ 3 * d ^ 3 := by simp only [pow_three', mul_assoc]

end Step

theorem step {G : Type*} [Group G] [Finite G] (hG : IsPGroup 3 G) (Z₀ H : Subgroup G) [H.Normal]
    (hZ : Nat.card Z₀ = 3) (hZc : Z₀ ≤ Subgroup.center G) (hZH : Z₀ ≤ H) (hH : H ≤ frattini G)
    (h81 : Nat.card H = 81) (hcube : ∀ x ∈ H, x ^ 3 ∈ Z₀)
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, cm x y ∈ Z₀) :
    ∃ E : Subgroup G, E.Normal ∧ E ≤ H ∧ IsE27 E := by
  suffices h : ∃ E : Subgroup G, E.Normal ∧ E ≤ H ∧ Nat.card E = 27 ∧ ∀ x ∈ E, x ^ 3 = 1 by
    obtain ⟨E, hEn, hEH, hE27, hE3⟩ := h
    refine ⟨E, hEn, hEH, hE27, hE3, ?_⟩
    by_contra hnc
    push Not at hnc
    exact hx hG E hE27 hnc (hEH.trans hH)
  by_cases hall : ∀ x ∈ H, x ^ 3 = 1
  · have : Z₀.Normal := Subgroup.normal_of_le_center hZc
    have hlt : Z₀ < H := lt_of_le_of_ne hZH fun h => by rw [h] at hZ; omega
    obtain ⟨E, hEn, -, hEH, hcard, -⟩ := exists_normal_index_three hG hlt
    exact ⟨E, hEn, hEH, by omega, fun x hx => hall x (hEH hx)⟩
  · push Not at hall
    obtain ⟨x₀, hx₀H, hx₀3⟩ := hall
    have hZ3 : ∀ z ∈ Z₀, z ^ 3 = 1 := fun z hz => by
      have h := pow_card_eq_one' (x := (⟨z, hz⟩ : Z₀))
      rw [hZ] at h
      simpa using congrArg Subtype.val h
    have hcm : ∀ x ∈ H, ∀ y ∈ H, (x * y) ^ 3 = x ^ 3 * y ^ 3 := fun x hx y hy => by
      have hd : (cm x y)⁻¹ ∈ Z₀ := Z₀.inv_mem (hcomm x hx y hy)
      have h := Step.cube_mul (hZc hd) (x := x) (y := y) (by simp only [cm]; group)
      rwa [hZ3 _ hd, mul_one] at h
    obtain ⟨ν, hν⟩ : ∃ ν : H →* G, ∀ x : H, ν x = (x : G) ^ 3 :=
      ⟨MonoidHom.mk' (fun x : H => (x : G) ^ 3) fun x y => hcm x x.2 y y.2, fun _ => rfl⟩
    have hrange_le : ν.range ≤ Z₀ := by
      rintro _ ⟨x, rfl⟩
      rw [hν]
      exact hcube x x.2
    have hrange_ne : ν.range ≠ ⊥ := fun h => by
      have hmem : ν ⟨x₀, hx₀H⟩ ∈ ν.range := ⟨⟨x₀, hx₀H⟩, rfl⟩
      rw [h, Subgroup.mem_bot, hν] at hmem
      exact hx₀3 hmem
    have hrange3 : Nat.card ν.range = 3 := by
      have hdvd : Nat.card ν.range ∣ 3 := hZ ▸ Subgroup.card_dvd_of_le hrange_le
      have hne1 : Nat.card ν.range ≠ 1 := fun h1 => hrange_ne (Subgroup.card_eq_one.mp h1)
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hker : Nat.card ν.ker = 27 := by
      have h := Subgroup.card_ker_mul_card_range ν
      rw [hrange3, h81] at h
      omega
    have hmem : ∀ x : G, x ∈ ν.ker.map H.subtype ↔ x ∈ H ∧ x ^ 3 = 1 := fun x => by
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have h1 : ν y = 1 := hy
        rw [hν] at h1
        exact ⟨y.2, h1⟩
      · rintro ⟨hxH, hx3⟩
        exact ⟨⟨x, hxH⟩, by rw [MonoidHom.mem_ker, hν]; exact hx3, rfl⟩
    refine ⟨ν.ker.map H.subtype, ⟨fun n hn g => (hmem _).2 ⟨?_, ?_⟩⟩,
      fun x hx => ((hmem x).1 hx).1, ?_, fun x hx => ((hmem x).1 hx).2⟩
    · exact Subgroup.Normal.conj_mem inferInstance n ((hmem n).1 hn).1 g
    · rw [conj_pow, ((hmem n).1 hn).2, mul_one, mul_inv_cancel]
    · exact (Subgroup.card_subtype H ν.ker).trans hker

end CFSG.Quasithin.SzN32
