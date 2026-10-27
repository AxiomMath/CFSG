module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKTorus
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKCube

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Assembly.LowTwoRank Matrix CFSG.Open

private theorem mem_of_pow_three_mem_of_pow_eq_one {G : Type*} [Group G] {H : Subgroup G}
    {x : G} {p : ℕ} (hx : x ^ p = 1) (hcop : Nat.Coprime 3 p) (hp1 : 1 < p)
    (h3 : x ^ 3 ∈ H) : x ∈ H := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp1
  have hdm : p * (3 * m / p) + 1 = 3 * m := by
    have h := Nat.div_add_mod (3 * m) p
    rw [hm] at h
    exact h
  have key : (x ^ 3) ^ m = x := by
    rw [← pow_mul, ← hdm, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]
  have hmem := H.pow_mem h3 m
  rwa [key] at hmem

theorem exists_elemAbelian_rank_three {Hb : Type} [Group Hb] [Finite Hb] {F : Type} [Field F]
    [Fintype F] (θ : ↥(StatedSL 3 F) →* Hb) (hθ : Function.Injective θ)
    (Kb' : Subgroup Hb) (hc : ∀ b ∈ Kb', ∀ g : ↥(StatedSL 3 F), b * θ g = θ g * b)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Fintype.card F - 1)
    (hp3 : p = 3 → Fintype.card F = 4) {y : Hb} (hy : y ^ p = 1) (hyK : y ∉ θ.range)
    (hyKK : ∃ (a : ↥(StatedSL 3 F)) (b : Hb), b ∈ Kb' ∧ y = θ a * b) :
    ∃ E : Subgroup Hb, IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  obtain ⟨a, b, hb, rfl⟩ := hyKK
  have hcomm : Commute (θ a) b := (hc b hb a).symm
  have hy' : θ (a ^ p) * b ^ p = 1 := by
    rw [map_pow, ← hcomm.mul_pow]
    exact hy
  have h1 : θ (a ^ p) = (b ^ p)⁻¹ := eq_inv_of_mul_eq_one_left hy'
  have hθap : θ (a ^ p) ∈ Kb' := by
    rw [h1]
    exact Kb'.inv_mem (Kb'.pow_mem hb p)
  have hcen : a ^ p ∈ Subgroup.center ↥(StatedSL 3 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply hθ
    rw [map_mul, map_mul]
    exact (hc _ hθap g).symm
  have hcube : (a ^ p) ^ 3 = 1 := pow_three_eq_one_of_mem_center hcen
  obtain ⟨b₁, hb₁K, hb₁p, hb₁S⟩ : ∃ b₁ ∈ Kb', b₁ ^ p = 1 ∧ b₁ ∉ θ.range := by
    rcases eq_or_ne p 3 with hp3' | hp3'
    · subst hp3'
      have ha3 : a ^ 3 = 1 := pow_three_eq_one_of_pow_three_mem_center (hp3 rfl) hcen
      have hb3 : b ^ 3 = 1 := by
        have h := hy
        rw [hcomm.mul_pow, ← map_pow, ha3, map_one, one_mul] at h
        exact h
      refine ⟨b, hb, hb3, fun hbS => hyK ?_⟩
      obtain ⟨c, hc'⟩ := hbS
      exact MonoidHom.mem_range.mpr ⟨a * c, by rw [map_mul, hc']⟩
    · have hcop : Nat.Coprime 3 p :=
        (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3')
      refine ⟨b ^ 3, Kb'.pow_mem hb 3, ?_, fun hbS => hyK ?_⟩
      · have hbp : b ^ p = (θ (a ^ p))⁻¹ := by rw [h1, inv_inv]
        rw [pow_right_comm, hbp, inv_pow, ← map_pow, hcube, map_one, inv_one]
      · apply mem_of_pow_three_mem_of_pow_eq_one hy hcop hp.one_lt
        rw [hcomm.mul_pow]
        exact θ.range.mul_mem (θ.range.pow_mem (MonoidHom.mem_range.mpr ⟨a, rfl⟩) 3) hbS
  obtain ⟨E₀, hE₀, hE₀card⟩ := exists_torus_elemAbelian hp hpF
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative ↥E₀ := hE₀.1
  have hb₁ne : b₁ ≠ 1 := fun h => hb₁S (by rw [h]; exact θ.range.one_mem)
  have hord : orderOf b₁ = p := orderOf_eq_prime hb₁p hb₁ne
  have hZK : Subgroup.zpowers b₁ ≤ Kb' := Subgroup.zpowers_le.mpr hb₁K
  have hZdvd : ∀ v : ↥(Subgroup.zpowers b₁), orderOf (v : Hb) ∣ p := fun v => by
    have hv := orderOf_dvd_of_mem_zpowers v.2
    rwa [hord] at hv
  have hZpow : ∀ v : ↥(Subgroup.zpowers b₁), (v : Hb) ^ p = 1 := fun v =>
    orderOf_dvd_iff_pow_eq_one.1 (hZdvd v)
  have hZexp : ∀ v : ↥(Subgroup.zpowers b₁), v ^ p = 1 := fun v => Subtype.ext (hZpow v)
  have hcomm2 : ∀ (u : ↥E₀) (v : ↥(Subgroup.zpowers b₁)),
      Commute ((θ.comp E₀.subtype) u) ((Subgroup.zpowers b₁).subtype v) :=
    fun u v => (hc _ (hZK v.2) (u : ↥(StatedSL 3 F))).symm
  obtain ⟨φ, hφapp⟩ : ∃ φ : (↥E₀ × ↥(Subgroup.zpowers b₁)) →* Hb,
      ∀ (u : ↥E₀) (v : ↥(Subgroup.zpowers b₁)), φ (u, v) = θ (u : ↥(StatedSL 3 F)) * (v : Hb) :=
    ⟨(θ.comp E₀.subtype).noncommCoprod (Subgroup.zpowers b₁).subtype hcomm2, fun u v => rfl⟩
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, v⟩ huv
    rw [hφapp] at huv
    have hvS : (v : Hb) ∈ θ.range :=
      MonoidHom.mem_range.mpr ⟨(u : ↥(StatedSL 3 F))⁻¹, by
        rw [map_inv]
        exact (eq_inv_of_mul_eq_one_right huv).symm⟩
    have hv1 : (v : Hb) = 1 := by
      by_contra hne
      have hvord : orderOf (v : Hb) = p := orderOf_eq_prime (hZpow v) hne
      have hle : Subgroup.zpowers (v : Hb) ≤ Subgroup.zpowers b₁ := Subgroup.zpowers_le.mpr v.2
      have hcard : Nat.card (Subgroup.zpowers b₁) ≤ Nat.card (Subgroup.zpowers (v : Hb)) :=
        le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hvord])
      have heq : Subgroup.zpowers (v : Hb) = Subgroup.zpowers b₁ :=
        Subgroup.eq_of_le_of_card_ge hle hcard
      have hb1v : b₁ ∈ Subgroup.zpowers (v : Hb) := by
        rw [heq]
        exact Subgroup.mem_zpowers b₁
      exact hb₁S (Subgroup.zpowers_le.mpr hvS hb1v)
    rw [hv1, mul_one] at huv
    have hu1 : (u : ↥(StatedSL 3 F)) = 1 := hθ (by rw [map_one]; exact huv)
    have hu : u = 1 := Subtype.ext hu1
    have hv : v = 1 := Subtype.ext hv1
    exact Prod.ext hu hv
  refine ⟨φ.range, ⟨inferInstance, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨⟨u, v⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    have hu : u ^ p = 1 := Subtype.ext (hE₀.2 _ u.2)
    have hpow : ((u, v) : ↥E₀ × ↥(Subgroup.zpowers b₁)) ^ p = 1 := Prod.ext hu (hZexp v)
    rw [← map_pow, hpow, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod, hE₀card,
      Nat.card_zpowers, hord]
    ring

end CFSG.Quasithin.H13.Ch4.CentK
