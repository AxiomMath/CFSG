module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup
open scoped Pointwise

theorem simple_order_two_power_three_prime_sylow_product_rigidity {G : Type*} [Group G]
    [Finite G] [IsSimpleGroup G] {a r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hcard : Nat.card G = 2 ^ a * 3 * r) (S : Sylow 2 G) (A : Subgroup G)
    (hA : ¬ 3 ∣ Nat.card A) (hAS : (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G)) :
    A ≤ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B : Subgroup G :=
    { carrier := (A : Set G) * (S : Set G)
      mul_mem' := by
        rintro _ _ ⟨x, hx, s, hs, rfl⟩ ⟨x', hx', s', hs', rfl⟩
        have hsx : s * x' ∈ (S : Set G) * (A : Set G) := ⟨s, hs, x', hx', rfl⟩
        rw [← hAS] at hsx
        obtain ⟨x'', hx'', s'', hs'', he⟩ := hsx
        have he : x'' * s'' = s * x' := he
        refine ⟨x * x'', A.mul_mem hx hx'', s'' * s', S.mul_mem hs'' hs', ?_⟩
        calc x * x'' * (s'' * s') = x * (x'' * s'') * s' := by group
          _ = x * s * (x' * s') := by rw [he]; group
      one_mem' := ⟨1, A.one_mem, 1, S.one_mem, one_mul 1⟩
      inv_mem' := by
        rintro _ ⟨x, hx, s, hs, rfl⟩
        have h : s⁻¹ * x⁻¹ ∈ (S : Set G) * (A : Set G) :=
          ⟨s⁻¹, S.inv_mem hs, x⁻¹, A.inv_mem hx, rfl⟩
        rw [← hAS] at h
        simpa [mul_inv_rev] using h }
  have hSB : (S : Subgroup G) ≤ B := fun s hs => ⟨1, A.one_mem, s, hs, one_mul s⟩
  have hAB : A ≤ B := fun x hx => ⟨x, hx, 1, S.one_mem, mul_one x⟩
  have hr2 : ¬ 2 ∣ 3 * r := by
    rw [Nat.Prime.dvd_mul Nat.prime_two]
    rintro (h | h)
    · omega
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h
      omega
  have hS : Nat.card S = 2 ^ a := by
    rw [Sylow.card_eq_multiplicity, hcard, mul_assoc,
      Nat.factorization_mul (by positivity) (by have := hr.pos; positivity), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hr2, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_two, smul_eq_mul, mul_one, add_zero]
  set d := Nat.card ((QuotientGroup.mk : G → G ⧸ (S : Subgroup G)) '' (A : Set G)) with hd
  have hBcard : Nat.card B = 2 ^ a * d := by
    rw [← hS]
    exact Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (S : Subgroup G) (A : Set G)
  have hdA : d ∣ Nat.card A := by
    have h1 : (QuotientGroup.mk : G → G ⧸ (S : Subgroup G)) '' (A : Set G) =
        MulAction.orbit A ((1 : G) : G ⧸ (S : Subgroup G)) := by
      ext x
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine ⟨⟨g, hg⟩, ?_⟩
        change g • ((1 : G) : G ⧸ (S : Subgroup G)) = (g : G ⧸ (S : Subgroup G))
        rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
      · rintro ⟨⟨g, hg⟩, rfl⟩
        refine ⟨g, hg, ?_⟩
        change (g : G ⧸ (S : Subgroup G)) = g • ((1 : G) : G ⧸ (S : Subgroup G))
        rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
    have h2 := MulAction.index_stabilizer A ((1 : G) : G ⧸ (S : Subgroup G))
    rw [← h1, ← Nat.card_coe_set_eq] at h2
    rw [hd, ← h2]
    exact Subgroup.index_dvd_card _
  have hd3r : d ∣ 3 * r := by
    have h := Subgroup.card_subgroup_dvd_card B
    rw [hBcard, hcard, mul_assoc] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h
  have hd3 : ¬ 3 ∣ d := fun h => hA (h.trans hdA)
  have hdr : d ∣ r :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hd3).symm
      hd3r
  rcases (Nat.dvd_prime hr).mp hdr with hd1 | hdr'
  ·
    have hBS : (S : Subgroup G) = B :=
      Subgroup.eq_of_le_of_card_ge hSB (by rw [hBcard, hd1, mul_one, hS])
    exact hAB.trans hBS.ge
  ·
    exfalso
    have hidx : B.index = 3 := by
      have h := B.card_mul_index
      rw [hBcard, hdr', hcard] at h
      have h' : 2 ^ a * r * B.index = 2 ^ a * r * 3 := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left (by have := hr.pos; positivity) h'
    let φ := MulAction.toPermHom G (G ⧸ B)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp h
      have hdvd := Subgroup.card_dvd_of_injective φ hinj
      rw [Nat.card_perm] at hdvd
      change Nat.card G ∣ (B.index).factorial at hdvd
      rw [hidx, hcard] at hdvd
      have hle : 2 ^ a * 3 * r ≤ 6 := Nat.le_of_dvd (by decide) hdvd
      have h2a : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      nlinarith
    · have hBtop : B = ⊤ := by
        rw [eq_top_iff]
        intro g _
        have hg : g ∈ φ.ker := h ▸ Subgroup.mem_top g
        have h1 := congrArg (fun σ : Equiv.Perm (G ⧸ B) => σ ((1 : G) : G ⧸ B))
          (MonoidHom.mem_ker.mp hg)
        change g • ((1 : G) : G ⧸ B) = ((1 : G) : G ⧸ B) at h1
        rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq] at h1
        simpa using h1
      rw [hBtop, Subgroup.index_top] at hidx
      omega

end CFSG.Quasithin.SteinbergCD
