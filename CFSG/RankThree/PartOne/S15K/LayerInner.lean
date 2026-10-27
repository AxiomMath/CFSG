module

public import CFSG.Assembly.Defs
public import CFSG.RankThree.PartOne.S15K.NormAct

public section

namespace CFSG.RankThree.PartOne.S15K

variable {G : Type*} [Group G] {Γ : Type*} [Group Γ]

theorem exists_mul_mem_centralizer_of_decomp {I : Subgroup G} (ψ : ↥I →* Γ)
    (hψ : Function.Injective ψ) {U : Type*} [Group U] (ρ : U →* Γ) {F : Subgroup U} {Q : Subgroup G}
    (hQ : ∀ x : G, x ∈ Q ↔ ∃ hx : x ∈ I, ψ ⟨x, hx⟩ ∈ F.map ρ) (hFB : F.map ρ ≤ ψ.range)
    {e : G} (he : e ∈ Subgroup.normalizer (I : Set G)) {m X y' : U}
    (hcompat : ∀ x : ↥I, ψ (I.normalizerMonoidHom ⟨e, he⟩ x) = ρ m * ψ x * (ρ m)⁻¹)
    (hm : m = X * y') (hX : X ∈ F) (hy' : ∀ f ∈ F, y' * f = f * y') :
    ∃ x ∈ Q, ∃ y ∈ Subgroup.centralizer (Q : Set G), e = x * y := by
  obtain ⟨x₀, hx₀⟩ := hFB ⟨X, hX, rfl⟩
  have hxQ : (x₀ : G) ∈ Q := (hQ _).2 ⟨x₀.2, by
    show ψ x₀ ∈ F.map ρ
    rw [hx₀]
    exact ⟨X, hX, rfl⟩⟩
  refine ⟨x₀, hxQ, (x₀ : G)⁻¹ * e, ?_, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨hzI, f, hf, hfz⟩ := (hQ z).1 hz
  set zz : ↥I := ⟨z, hzI⟩ with hzz
  set w : ↥I := I.normalizerMonoidHom ⟨e, he⟩ zz with hw
  have hcomm : ρ y' * ρ f = ρ f * ρ y' := by rw [← map_mul, ← map_mul, hy' f hf]
  have hu : ψ (x₀⁻¹ * w * x₀) = ψ zz := by
    rw [map_mul, map_mul, map_inv, hx₀, hw, hcompat, ← hfz, hm, map_mul]
    calc (ρ X)⁻¹ * (ρ X * ρ y' * ρ f * (ρ X * ρ y')⁻¹) * ρ X
        = ρ y' * ρ f * (ρ y')⁻¹ := by group
      _ = ρ f := by rw [hcomm]; group
  have hu' : x₀⁻¹ * w * x₀ = zz := hψ hu
  have h2 := congrArg Subtype.val hu'
  have h3 : (x₀ : G)⁻¹ * ((e * z * e⁻¹)) * x₀ = z := by
    have : ((x₀⁻¹ * w * x₀ : ↥I) : G) = (x₀ : G)⁻¹ * (e * z * e⁻¹) * x₀ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [← this]
    exact h2
  calc z * ((x₀ : G)⁻¹ * e) = ((x₀ : G)⁻¹ * (e * z * e⁻¹) * x₀ ) * ((x₀ : G)⁻¹ * e) := by
        rw [h3]
    _ = ((x₀ : G)⁻¹ * e) * z := by
        have : (x₀ : G)⁻¹ * (e * z * e⁻¹) * x₀ * ((x₀ : G)⁻¹ * e) =
            (x₀ : G)⁻¹ * e * z := by group
        rw [this]

theorem exists_mul_mem_centralizer_of_decomp' {I : Subgroup G} (ψ : ↥I →* Γ)
    (hψ : Function.Injective ψ) {J : Subgroup Γ} {Q : Subgroup G}
    (hQ : ∀ x : G, x ∈ Q ↔ ∃ hx : x ∈ I, ψ ⟨x, hx⟩ ∈ J) (hJ : J ≤ ψ.range) {e : G}
    (he : e ∈ Subgroup.normalizer (I : Set G)) {t X y : Γ}
    (hcompat : ∀ x : ↥I, ψ (I.normalizerMonoidHom ⟨e, he⟩ x) = t * ψ x * t⁻¹) (ht : t = X * y)
    (hX : X ∈ J) (hy : ∀ f ∈ J, y * f = f * y) :
    ∃ x ∈ Q, ∃ y ∈ Subgroup.centralizer (Q : Set G), e = x * y := by
  refine exists_mul_mem_centralizer_of_decomp ψ hψ (MonoidHom.id Γ) (F := J) (by simpa using hQ)
    (by simpa using hJ) he (by simpa using hcompat) ht (by simpa using hX) fun f hf => ?_
  exact hy f (by simpa using hf)

theorem eq_one_of_mem_inf_centralizer {I : Subgroup G} (ψ : ↥I →* Γ) (hψ : Function.Injective ψ)
    {U : Type*} [Group U] (ρ : U →* Γ) {F : Subgroup U} {Q : Subgroup G}
    (hQ : ∀ x : G, x ∈ Q ↔ ∃ hx : x ∈ I, ψ ⟨x, hx⟩ ∈ F.map ρ) (hFB : F.map ρ ≤ ψ.range)
    (hρ : ∀ u ∈ F, ρ u = 1 → u = 1) {p : ℕ}
    (hF : ∀ u ∈ F, (∀ f ∈ F, u * f = f * u) → u ^ p = 1 → u = 1) :
    ∀ z ∈ Q ⊓ Subgroup.centralizer (Q : Set G), z ^ p = 1 → z = 1 := by
  intro z hz hzp
  obtain ⟨hzQ, hzC⟩ := hz
  obtain ⟨hzI, u, hu, huz⟩ := (hQ z).1 hzQ
  have hcen : ∀ f ∈ F, u * f = f * u := by
    intro f hf
    obtain ⟨y, hy⟩ := hFB ⟨f, hf, rfl⟩
    have hyQ : (y : G) ∈ Q := (hQ _).2 ⟨y.2, by
      show ψ y ∈ F.map ρ
      rw [hy]
      exact ⟨f, hf, rfl⟩⟩
    have h1 : (y : G) * z = z * (y : G) := Subgroup.mem_centralizer_iff.mp hzC _ hyQ
    have h2 : y * (⟨z, hzI⟩ : ↥I) = (⟨z, hzI⟩ : ↥I) * y := Subtype.ext h1
    have h3 := congrArg ψ h2
    rw [map_mul, map_mul, hy, ← huz] at h3
    have h4 : ρ (f * u) = ρ (u * f) := by rw [map_mul, map_mul]; exact h3
    have h5 : (f * u)⁻¹ * (u * f) = 1 :=
      hρ _ (mul_mem (inv_mem (mul_mem hf hu)) (mul_mem hu hf))
        (by rw [map_mul, map_inv, h4, inv_mul_cancel])
    exact (inv_mul_eq_one.mp h5).symm
  have hzzp : (⟨z, hzI⟩ : ↥I) ^ p = 1 := Subtype.ext hzp
  have hup : u ^ p = 1 :=
    hρ _ (pow_mem hu p) (by rw [map_pow, huz, ← map_pow, hzzp, map_one])
  have hu1 : u = 1 := hF u hu hcen hup
  have : ψ ⟨z, hzI⟩ = ψ 1 := by rw [← huz, hu1, map_one, map_one]
  exact congrArg Subtype.val (hψ this)

theorem not_dvd_card_inf_centralizer [Finite G] {I : Subgroup G} (ψ : ↥I →* Γ)
    (hψ : Function.Injective ψ) {U : Type*} [Group U] (ρ : U →* Γ) {F : Subgroup U}
    {Q : Subgroup G} (hQ : ∀ x : G, x ∈ Q ↔ ∃ hx : x ∈ I, ψ ⟨x, hx⟩ ∈ F.map ρ)
    (hFB : F.map ρ ≤ ψ.range) (hρ : ∀ u ∈ F, ρ u = 1 → u = 1) {p : ℕ} (hp : p.Prime)
    (hF : ∀ u ∈ F, (∀ f ∈ F, u * f = f * u) → u ^ p = 1 → u = 1) :
    ¬ p ∣ Nat.card ↥(Q ⊓ Subgroup.centralizer (Q : Set G)) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hz1 : (z : G) = 1 := eq_one_of_mem_inf_centralizer ψ hψ ρ hQ hFB hρ hF z z.2 (by
    have : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    exact congrArg Subtype.val this)
  have : z = 1 := Subtype.ext hz1
  rw [this, orderOf_one] at hz
  exact hp.one_lt.ne hz

end CFSG.RankThree.PartOne.S15K
