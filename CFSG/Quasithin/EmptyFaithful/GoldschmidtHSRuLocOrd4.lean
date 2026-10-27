module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocCop
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.HSRuLoc.Mod

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem comm_of_sq_eq_one {R : Subgroup H} (h : ∀ x ∈ R, x ^ 2 = 1) {a b : H} (ha : a ∈ R)
    (hb : b ∈ R) : a * b = b * a := by
  have hab : (a * b) * (a * b) = 1 := by simpa [pow_two] using h _ (R.mul_mem ha hb)
  have ha' : a * a = 1 := by simpa [pow_two] using h a ha
  have hb' : b * b = 1 := by simpa [pow_two] using h b hb
  have h1 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha', inv_eq_of_mul_eq_one_right hb'] at h1
  exact h1

omit [Finite H] in
theorem isElemAbelian_of_sq_eq_one {R : Subgroup H} (h : ∀ x ∈ R, x ^ 2 = 1) :
    CFSG.Open.IsElemAbelian 2 R :=
  ⟨⟨⟨fun a b => Subtype.ext (comm_of_sq_eq_one h a.2 b.2)⟩⟩, fun x hx => h x hx⟩

theorem two_pow_mod_seven {e : ℕ} (he : e % 3 = 2) : 2 ^ e % 7 = 4 := by
  obtain ⟨q, hq⟩ : ∃ q, e = 3 * q + 2 := ⟨e / 3, by omega⟩
  have h8 : 8 ^ q % 7 = 1 := by
    rw [Nat.pow_mod]
    simp
  have : 2 ^ e = 8 ^ q * 4 := by
    rw [hq, pow_add, pow_mul]
    norm_num
  rw [this, Nat.mul_mod, h8]

theorem hsru_exists_sq_ne_one {R : Subgroup H} {e : ℕ} (hR : Nat.card R = 2 ^ e) (he : e % 3 = 2)
    {u : H} (hu : orderOf u = 7) (hRu : ∀ x ∈ R, u * x * u⁻¹ ∈ R)
    (hcent : ∀ t : H, orderOf t = 2 → 2 ^ e ∣ Nat.card (Subgroup.centralizer ({t} : Set H)) →
      ¬ 7 ∣ Nat.card (Subgroup.centralizer ({t} : Set H))) :
    ∃ x ∈ R, x ^ 2 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hu7 : u ^ 7 = 1 := hu ▸ pow_orderOf_eq_one u
  have hA : ∀ x ∈ (R : Set H) \ {1}, u * x * u⁻¹ ∈ (R : Set H) \ {1} := by
    rintro x ⟨hxR, hx1⟩
    refine ⟨hRu x hxR, fun h => hx1 ?_⟩
    have : u * x * u⁻¹ = u * 1 * u⁻¹ := by rw [Set.mem_singleton_iff.mp h]; group
    simpa using this
  have hcard : ¬ 7 ∣ ((R : Set H) \ {1}).ncard := by
    have h1 := Set.ncard_sdiff_singleton_add_one (s := (R : Set H)) (a := 1) R.one_mem
    have h2 : (R : Set H).ncard = 2 ^ e := by
      rw [← Nat.card_coe_set_eq]
      exact hR
    rw [h2] at h1
    have h3 := two_pow_mod_seven he
    generalize 2 ^ e = N at h1 h3
    omega
  obtain ⟨x, ⟨hxR, hx1⟩, hxu⟩ := exists_fixed_of_stable hu7 hA hcard
  have hx1' : x ≠ 1 := hx1
  have hx2 : orderOf x = 2 := orderOf_eq_prime (hcon x hxR) hx1'
  have hle : R ≤ Subgroup.centralizer ({x} : Set H) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_sq_eq_one hcon hr hxR)
  have h2e : 2 ^ e ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) :=
    hR ▸ Subgroup.card_dvd_of_le hle
  have hux : u * x = x * u := by
    have : u * x * u⁻¹ * u = x * u := by rw [hxu]
    simpa [mul_assoc] using this
  have hmem : u ∈ Subgroup.centralizer ({x} : Set H) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hux
  have h7 : 7 ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) := by
    have := orderOf_dvd_natCard (⟨u, hmem⟩ : Subgroup.centralizer ({x} : Set H))
    rwa [Subgroup.orderOf_mk, hu] at this
  exact hcent x hx2 h2e h7

end CFSG.Quasithin.HSRuLoc.Mod
