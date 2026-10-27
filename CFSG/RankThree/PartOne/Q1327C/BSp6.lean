module

public import CFSG.RankThree.PartOne.Q1327C.BSp6Matrix
public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  CFSG.RankThree.PartTwo.Census

variable {K : Type} [Field K]
variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def torusPhom (p : ℕ) (K : Type) [Field K] :
    (Fin 3 → rootsOfUnity p K) →* StatedSp 3 K :=
  torusHom.comp ((rootsOfUnity p K).subtype.compLeft (Fin 3))

theorem torusPhom_injective (p : ℕ) : Function.Injective (torusPhom p K) := by
  refine torusHom_injective.comp fun s t hst => funext fun j => Subtype.ext (congrFun hst j)

@[expose] noncomputable def torusP (p : ℕ) (K : Type) [Field K] : Subgroup (StatedSp 3 K) :=
  (torusPhom p K).range

theorem mem_torusP {p : ℕ} {x : StatedSp 3 K} :
    x ∈ torusP p K ↔ ∃ t : Fin 3 → Kˣ, (∀ i, t i ^ p = 1) ∧ torusHom t = x := by
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨fun i => (s i : Kˣ), fun i => ?_, rfl⟩
    have := rootsOfUnity_pow_eq_one (s i)
    exact congrArg Subtype.val this
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => ⟨t i, (mem_rootsOfUnity p _).2 (ht i)⟩, rfl⟩

theorem card_torusP [Finite K] {p : ℕ} (hp : p.Prime) (hrK : p ∣ Nat.card Kˣ) :
    Nat.card (torusP p K) = p ^ 3 := by
  unfold torusP
  rw [← Nat.card_congr (MonoidHom.ofInjective (torusPhom_injective (K := K) p)).toEquiv]
  exact card_fun_rootsOfUnity (card_rootsOfUnity_of_dvd hp hrK)

theorem sp3_signed_perm_data {Y : Type} [Group Y] [Finite Y] {p : ℕ} {ζ : Kˣ}
    (hζ : orderOf ζ = p) (E : Subgroup Y) (χ : Y ≃* StatedSp 3 K)
    (hE : E.map χ.toMonoidHom = torusP p K) :
    ∃ (e w : Fin 3 → Y) (u : Y), (∀ j, e j ∈ E) ∧
      (∀ a b c : ℤ, e 0 ^ a * e 1 ^ b * e 2 ^ c = 1 →
        (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c) ∧
      (∀ i, w i ∈ Subgroup.normalizer (E : Set Y)) ∧ u ∈ Subgroup.normalizer (E : Set Y) ∧
      (∀ i j, w i * e j * (w i)⁻¹ = if i = j then (e j)⁻¹ else e j) ∧
      u * e 0 * u⁻¹ = e 1 ∧ u * e 1 * u⁻¹ = e 0 ∧ u * e 2 * u⁻¹ = e 2 := by
  classical
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  let e' : Fin 3 → StatedSp 3 K := fun j => torusHom (Pi.mulSingle j ζ)
  have he'P : ∀ j, e' j ∈ torusP p K := fun j =>
    mem_torusP.2 ⟨Pi.mulSingle j ζ, fun i => by
      by_cases hij : i = j
      · subst hij; simpa using hζp
      · simp [hij], rfl⟩
  have hmemE : ∀ x : Y, x ∈ E ↔ χ x ∈ torusP p K := by
    intro x
    rw [← hE]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := χ.injective hyx
      rwa [← this]
  refine ⟨fun j => χ.symm (e' j), fun i => χ.symm (lam i sl2W), χ.symm (rho 0 1 h01 sl2W),
    fun j => (hmemE _).2 (by simpa using he'P j), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c habc
    have h1 : χ (χ.symm (e' 0) ^ a * χ.symm (e' 1) ^ b * χ.symm (e' 2) ^ c) = 1 := by
      rw [habc, map_one]
    simp only [map_mul, map_zpow, MulEquiv.apply_symm_apply] at h1
    have h2 : (torusHom (Pi.mulSingle 0 ζ ^ a * Pi.mulSingle 1 ζ ^ b * Pi.mulSingle 2 ζ ^ c) :
        StatedSp 3 K) = torusHom 1 := by
      rw [map_one]
      simpa [e', map_mul, map_zpow] using h1
    have h3 := torusHom_injective h2
    have hk : ∀ k : Fin 3, (Pi.mulSingle 0 ζ ^ a * Pi.mulSingle 1 ζ ^ b *
        Pi.mulSingle 2 ζ ^ c : Fin 3 → Kˣ) k = 1 := fun k => congrFun h3 k
    have h0 := hk 0
    have h1' := hk 1
    have h2' := hk 2
    simp at h0 h1' h2'
    have hdvd : ∀ x : ℤ, ζ ^ x = 1 → (p : ℤ) ∣ x := fun x hx => by
      have := orderOf_dvd_iff_zpow_eq_one.2 hx
      rwa [hζ] at this
    exact ⟨hdvd _ h0, hdvd _ h1', hdvd _ h2'⟩
  · intro i
    apply mem_normalizer_of_conj_le
    intro s hs
    rw [hmemE] at hs ⊢
    obtain ⟨t, ht, hts⟩ := mem_torusP.1 hs
    have h1 : χ (χ.symm (lam i sl2W) * s * (χ.symm (lam i sl2W))⁻¹) =
        torusHom (fun k => if k = i then (t k)⁻¹ else t k) := by
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [← hts]
      exact conj_lam_torus i t
    rw [h1]
    refine mem_torusP.2 ⟨_, fun k => ?_, rfl⟩
    by_cases hk : k = i
    · simp [hk, inv_pow, ht i]
    · simp [hk, ht k]
  · apply mem_normalizer_of_conj_le
    intro s hs
    rw [hmemE] at hs ⊢
    obtain ⟨t, ht, hts⟩ := mem_torusP.1 hs
    have h1 : χ (χ.symm (rho 0 1 h01 sl2W) * s * (χ.symm (rho 0 1 h01 sl2W))⁻¹) =
        torusHom ![t 1, t 0, t 2] := by
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [← hts]
      exact conj_rho01_torus h01 t
    rw [h1]
    refine mem_torusP.2 ⟨_, fun k => ?_, rfl⟩
    fin_cases k <;> simp [ht 0, ht 1, ht 2]
  · intro i j
    apply χ.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, apply_ite χ, map_inv]
    exact conj_lam_e i j ζ
  · apply χ.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact conj_rho01_e0 h01 ζ
  · apply χ.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact conj_rho01_e1 h01 ζ
  · apply χ.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact conj_rho01_e2 h01 ζ

theorem padicValNat_pow_sub_one_eq {p q m : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hq : 2 ≤ q)
    (hd : p ∣ q - 1) (hm1 : 1 ≤ m) (hmp : ¬ p ∣ m) :
    padicValNat p (q ^ m - 1) = padicValNat p (q - 1) := by
  have hpq : ¬ p ∣ q := by
    intro h
    have h2 : p ∣ q - (q - 1) := Nat.dvd_sub h hd
    have : q - (q - 1) = 1 := by omega
    rw [this] at h2
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp h2)
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have := padicValNat.pow_sub_pow (p := p) (x := q) (y := 1) (n := m) hodd (by omega)
    (by simpa using hd) hpq (by omega)
  simp only [one_pow] at this
  rw [this, padicValNat.eq_zero_of_not_dvd hmp, add_zero]

theorem not_dvd_index_of_val {M : Type} [Group M] [Finite M] {T : Subgroup M} {p : ℕ}
    [Fact p.Prime] (h : padicValNat p (Nat.card M) ≤ padicValNat p (Nat.card T)) :
    ¬ p ∣ T.index := by
  have h1 : Nat.card T * T.index = Nat.card M := Subgroup.card_mul_index T
  have hT : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have hI : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : padicValNat p (Nat.card M) = padicValNat p (Nat.card T) + padicValNat p T.index := by
    rw [← h1, padicValNat.mul hT hI]
  have h3 : padicValNat p T.index = 0 := by omega
  intro hd
  have := (dvd_iff_padicValNat_ne_zero hI).1 hd
  exact this h3

theorem gcd_two_two_pow_sub_one {f : ℕ} (hf : 1 ≤ f) : Nat.gcd 2 (2 ^ f - 1) = 1 := by
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hm : (2 ^ f - 1) % 2 = 1 := by omega
  exact Nat.coprime_two_left.2 (Nat.odd_iff.2 hm)

end CFSG.RankThree.PartOne.Q1327C
