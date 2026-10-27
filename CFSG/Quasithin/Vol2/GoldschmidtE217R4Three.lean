module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4L27

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace E217R4

theorem centralizer_le_of_L27 {K : Type*} [Group K] (hK : L27 K) {z : K} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) {D : Subgroup K} (hD : IsSylowTwoOf D ⊤) (hDc : ∀ d ∈ D, d * z = z * d) :
    ∀ y : K, y * z = z * y → y ∈ D := by
  intro y hy
  have h8 := hK.cent2 z hz2 hz1
  have hD8 := hK.card2 D hD
  have hle : D ≤ Subgroup.centralizer ({z} : Set K) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (hDc d hd)
  have : Finite ↥(Subgroup.centralizer ({z} : Set K)) :=
    Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h8, hD8])
  have : y ∈ Subgroup.centralizer ({z} : Set K) := Subgroup.mem_centralizer_singleton_iff.2 hy
  rwa [← heq] at this

theorem transitive_three {K : Type*} [Group K] (hK : L27 K) {z : K} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) {D : Subgroup K} (hD : IsSylowTwoOf D ⊤) (hDc : ∀ d ∈ D, d * z = z * d)
    {a a' : K} (ha : a ^ 3 = 1) (ha1 : a ≠ 1) (ha' : a' ^ 3 = 1) (ha'1 : a' ≠ 1)
    (hza : z * a * z⁻¹ = a⁻¹) (hza' : z * a' * z⁻¹ = a'⁻¹) :
    ∃ d ∈ D, ∃ i : ℕ, d * a * d⁻¹ = a' ^ i := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  obtain ⟨g, i₀, hg⟩ := hK.sylow3 a a' ha ha1 ha' ha'1
  set z' := g⁻¹ * z * g with hz'
  have hz'a : z' * a * z'⁻¹ = a⁻¹ := by
    have hb : z * (g * a * g⁻¹) * z⁻¹ = (g * a * g⁻¹)⁻¹ := by
      rw [hg, ← conj_pow, hza', inv_pow]
    calc z' * a * z'⁻¹ = g⁻¹ * (z * (g * a * g⁻¹) * z⁻¹) * g := by rw [hz']; group
      _ = g⁻¹ * (g * a * g⁻¹)⁻¹ * g := by rw [hb]
      _ = a⁻¹ := by group
  set u := z * z' with hu
  have hua : u * a = a * u := by
    have h1 : u * a * u⁻¹ = a := by
      calc u * a * u⁻¹ = z * (z' * a * z'⁻¹) * z⁻¹ := by rw [hu]; group
        _ = z * a⁻¹ * z⁻¹ := by rw [hz'a]
        _ = (z * a * z⁻¹)⁻¹ := by group
        _ = a := by rw [hza, inv_inv]
    calc u * a = (u * a * u⁻¹) * u := by group
      _ = a * u := by rw [h1]
  obtain ⟨j, hj⟩ := hK.cent3 a ha ha1 u hua
  have hzu : z * u * z⁻¹ = u⁻¹ := by rw [hj, ← conj_pow, hza, inv_pow]
  have hu3 : u ^ 3 = 1 := by
    rw [hj, ← pow_mul, mul_comm, pow_mul, ha, one_pow]
  have huz : u * z * u⁻¹ = z' := by
    have h2 : u * u = u⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← pow_three, hu3])
    calc u * z * u⁻¹ = u * (z * u⁻¹ * z⁻¹) * z := by group
      _ = u * (z * u * z⁻¹)⁻¹ * z := by rw [show z * u⁻¹ * z⁻¹ = (z * u * z⁻¹)⁻¹ by group]
      _ = u * u * z := by rw [hzu, inv_inv]
      _ = u⁻¹ * z := by rw [h2]
      _ = z * u * z⁻¹ * z := by rw [hzu]
      _ = z * u := by group
      _ = z' := by rw [hu, ← mul_assoc, hz2, one_mul]
  have hc : (g * u) * z = z * (g * u) := by
    have h3 : g * z' * g⁻¹ = z := by rw [hz']; group
    calc (g * u) * z = g * (u * z * u⁻¹) * u := by group
      _ = g * z' * u := by rw [huz]
      _ = (g * z' * g⁻¹) * (g * u) := by group
      _ = z * (g * u) := by rw [h3]
  refine ⟨g * u, centralizer_le_of_L27 hK hz2 hz1 hD hDc _ hc, i₀, ?_⟩
  calc g * u * a * (g * u)⁻¹ = g * (u * a * u⁻¹) * g⁻¹ := by group
    _ = g * a * g⁻¹ := by rw [show u * a * u⁻¹ = a by rw [hua]; group]
    _ = a' ^ i₀ := hg

end E217R4

end CFSG.Quasithin
