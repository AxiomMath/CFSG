module

public import Mathlib.GroupTheory.PGroup
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type} [Group G] {K : Subgroup G} {X : Type} [Group X] (φ : ↥K →* X)

@[expose] def img (H : Subgroup G) : Subgroup X := (H.subgroupOf K).map φ

theorem mem_img {H : Subgroup G} {y : X} :
    y ∈ img φ H ↔ ∃ (h : G) (hK : h ∈ K), h ∈ H ∧ φ ⟨h, hK⟩ = y := by
  unfold img
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, x.2, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨h, hK, hH, rfl⟩
    exact ⟨⟨h, hK⟩, Subgroup.mem_subgroupOf.mpr hH, rfl⟩

theorem mem_img_of_mem {H : Subgroup G} {h : G} (hK : h ∈ K) (hH : h ∈ H) :
    φ ⟨h, hK⟩ ∈ img φ H :=
  (mem_img φ).mpr ⟨h, hK, hH, rfl⟩

theorem img_exp {Y : Subgroup G} {q : ℕ} (h : ∀ y ∈ Y, y ^ q = 1) :
    ∀ y ∈ img φ Y, y ^ q = 1 := by
  intro y hy
  obtain ⟨h₀, hK, hY, rfl⟩ := (mem_img φ).mp hy
  have : (⟨h₀, hK⟩ : ↥K) ^ q = 1 := Subtype.ext (by simpa using h h₀ hY)
  rw [← map_pow, this, map_one]

theorem img_class {Y : Subgroup G} (h : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) :
    ∀ a ∈ img φ Y, ∀ b ∈ img φ Y, ∀ c ∈ img φ Y, ⁅⁅a, b⁆, c⁆ = 1 := by
  intro a ha b hb c hc
  obtain ⟨a₀, hKa, hYa, rfl⟩ := (mem_img φ).mp ha
  obtain ⟨b₀, hKb, hYb, rfl⟩ := (mem_img φ).mp hb
  obtain ⟨c₀, hKc, hYc, rfl⟩ := (mem_img φ).mp hc
  have : ⁅⁅(⟨a₀, hKa⟩ : ↥K), (⟨b₀, hKb⟩ : ↥K)⁆, (⟨c₀, hKc⟩ : ↥K)⁆ = 1 :=
    Subtype.ext (by simpa [commutatorElement_def] using h a₀ hYa b₀ hYb c₀ hYc)
  rw [← map_commutatorElement, ← map_commutatorElement, this, map_one]

theorem img_isPGroup {p : ℕ} {H : Subgroup G} (h : IsPGroup p H) : IsPGroup p (img φ H) := by
  intro x
  obtain ⟨h₀, hK, hH, hx⟩ := (mem_img φ).mp x.2
  obtain ⟨k, hk⟩ := h ⟨h₀, hH⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (⟨h₀, hK⟩ : ↥K) ^ (p ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  show (x : X) ^ (p ^ k) = 1
  rw [← hx, ← map_pow, h1, map_one]

theorem img_le_normalizer {R Y : Subgroup G} (hRN : R ≤ normalizer (Y : Set G)) :
    img φ R ≤ normalizer ((img φ Y : Subgroup X) : Set X) := by
  have hfwd : ∀ g ∈ img φ R, ∀ y ∈ img φ Y, g * y * g⁻¹ ∈ img φ Y := by
    intro g hg y hy
    obtain ⟨r, hKr, hRr, rfl⟩ := (mem_img φ).mp hg
    obtain ⟨y₀, hKy, hYy, rfl⟩ := (mem_img φ).mp hy
    have h1 : r * y₀ * r⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hRN hRr) y₀).mp hYy
    have hK' : r * y₀ * r⁻¹ ∈ K := K.mul_mem (K.mul_mem hKr hKy) (K.inv_mem hKr)
    have h2 := mem_img_of_mem φ hK' h1
    have h3 : (⟨r * y₀ * r⁻¹, hK'⟩ : ↥K) = ⟨r, hKr⟩ * ⟨y₀, hKy⟩ * ⟨r, hKr⟩⁻¹ := Subtype.ext rfl
    rwa [h3, map_mul, map_mul, map_inv] at h2
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hfwd g hg y hy, fun hy => ?_⟩
  have h1 := hfwd g⁻¹ ((img φ R).inv_mem hg) _ hy
  have h2 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  rwa [h2] at h1

theorem centralizes_of_img {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Y R : Subgroup G}
    (hYK : Y ≤ K) (hRK : R ≤ K) (hYexp : ∀ y ∈ Y, y ^ q = 1) (hR2 : IsPGroup 2 R)
    (hRN : R ≤ normalizer (Y : Set G)) (hφk : φ.ker ≤ center ↥K) {r : G} (hr : r ∈ R)
    (hc : φ ⟨r, hRK hr⟩ ∈ centralizer ((img φ Y : Subgroup X) : Set X)) :
    r ∈ centralizer (Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hrK : r ∈ K := hRK hr
  have hyK : y ∈ K := hYK hy
  set n : G := r * y * r⁻¹ * y⁻¹ with hn
  have hnY : n ∈ Y :=
    Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRN hr) y).mp hy) (Y.inv_mem hy)
  have hnK : n ∈ K := hYK hnY
  let ρ : ↥K := ⟨r, hrK⟩
  let η : ↥K := ⟨y, hyK⟩
  let ν : ↥K := ⟨n, hnK⟩
  have hρην : ρ * η * ρ⁻¹ = ν * η := Subtype.ext (by simp [ρ, η, ν, hn])
  have hν1 : φ ν = 1 := by
    have h1 : φ η * φ ρ = φ ρ * φ η :=
      Subgroup.mem_centralizer_iff.mp hc (φ η) (mem_img_of_mem φ hyK hy)
    have h2 : ν = ρ * η * ρ⁻¹ * η⁻¹ := Subtype.ext (by simp [ρ, η, ν, hn])
    rw [h2, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
    simp [mul_assoc]
  have hνc : ν ∈ center ↥K := hφk (MonoidHom.mem_ker.mpr hν1)
  have hpow : ∀ k : ℕ, ρ ^ k * η * (ρ ^ k)⁻¹ = ν ^ k * η := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : ρ ^ (k + 1) * η * (ρ ^ (k + 1))⁻¹ = ρ * (ρ ^ k * η * (ρ ^ k)⁻¹) * ρ⁻¹ := by
        rw [pow_succ']
        group
      have e2 : ρ * (ν ^ k * η) * ρ⁻¹ = (ρ * ν ^ k * ρ⁻¹) * (ρ * η * ρ⁻¹) := by group
      have e3 : ρ * ν ^ k * ρ⁻¹ = ν ^ k := by
        have := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hνc k) ρ
        rw [this]
        group
      rw [e1, ih, e2, e3, hρην, pow_succ]
      simp [mul_assoc]
  obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
  have hρk : ρ ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hν2 : ν ^ (2 ^ k) = 1 := by
    have h1 := hpow (2 ^ k)
    rw [hρk, one_mul, inv_one, mul_one] at h1
    exact (mul_eq_right.mp h1.symm)
  have hνq : ν ^ q = 1 := Subtype.ext (by simpa [ν] using hYexp n hnY)
  have hcop : Nat.Coprime (2 ^ k) q :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
  have hν : ν = 1 := by
    have h3 : orderOf ν ∣ Nat.gcd (2 ^ k) q :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hν2) (orderOf_dvd_of_pow_eq_one hνq)
    rw [hcop.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hn1 : n = 1 := by simpa [ν] using congrArg Subtype.val hν
  have h5 : ⁅r, y⁆ = 1 := by
    rw [commutatorElement_def]
    exact hn1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h5).symm

theorem exists_hom_img {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Y R : Subgroup G}
    (hYK : Y ≤ K) (hRK : R ≤ K) (hYexp : ∀ y ∈ Y, y ^ q = 1) (hR2 : IsPGroup 2 R)
    (hRN : R ≤ normalizer (Y : Set G)) (hφk : φ.ker ≤ center ↥K) (ψ : ↥R →* QD32)
    (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : G) ∈ centralizer (Y : Set G)) :
    ∃ ψ' : ↥(img φ R) →* QD32, Function.Surjective ψ' ∧
      ∀ r : ↥(img φ R), ψ' r = 1 ↔ (r : X) ∈ centralizer ((img φ Y : Subgroup X) : Set X) := by
  let σ : ↥R →* ↥(img φ R) :=
    (φ.subgroupMap (R.subgroupOf K)).comp (Subgroup.subgroupOfEquivOfLe hRK).symm.toMonoidHom
  have hσs : Function.Surjective σ :=
    (MonoidHom.subgroupMap_surjective φ _).comp (Subgroup.subgroupOfEquivOfLe hRK).symm.surjective
  have hσc : ∀ x : ↥R, ((σ x : ↥(img φ R)) : X) = φ ⟨(x : G), hRK x.2⟩ := fun x => rfl
  have hker : σ.ker ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : φ ⟨(x : G), hRK x.2⟩ = 1 := by rw [← hσc, hx]; rfl
    have hxc : (⟨(x : G), hRK x.2⟩ : ↥K) ∈ center ↥K := hφk (MonoidHom.mem_ker.mpr h1)
    refine (hψc x).mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨y, hYK hy⟩)
  let ψ' : ↥(img φ R) →* QD32 :=
    σ.liftOfRightInverse (Function.surjInv hσs) (Function.rightInverse_surjInv hσs) ⟨ψ, hker⟩
  have hψ' : ∀ x, ψ' (σ x) = ψ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply σ _ _ ⟨ψ, hker⟩ x
  refine ⟨ψ', ?_, ?_⟩
  · intro t
    obtain ⟨x, hx⟩ := hψs t
    exact ⟨σ x, by rw [hψ', hx]⟩
  · intro r
    obtain ⟨x, rfl⟩ := hσs r
    rw [hψ', hψc]
    constructor
    · intro hxc
      rw [hσc, Subgroup.mem_centralizer_iff]
      intro y' hy'
      obtain ⟨y, hyK, hyY, rfl⟩ := (mem_img φ).mp hy'
      have hcomm : (⟨y, hyK⟩ : ↥K) * ⟨(x : G), hRK x.2⟩ = ⟨(x : G), hRK x.2⟩ * ⟨y, hyK⟩ :=
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc) y hyY)
      rw [← map_mul, ← map_mul, hcomm]
    · intro hc
      exact centralizes_of_img φ hq hq2 hYK hRK hYexp hR2 hRN hφk x.2 hc

theorem exists_endo_conj (hφs : Function.Surjective φ) (hker : φ.ker = center ↥K) {a : G}
    (ha : a ∈ normalizer (K : Set G)) :
    ∃ β : X →* X, ∀ k k' : ↥K, (k' : G) = a * k * a⁻¹ → β (φ k) = φ k' := by
  have haK : ∀ k : ↥K, a * (k : G) * a⁻¹ ∈ K := fun k =>
    (Subgroup.mem_normalizer_iff.mp ha k).mp k.2
  have haK' : ∀ k : ↥K, a⁻¹ * (k : G) * a ∈ K := fun k => by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (K : Set G)).inv_mem ha) k).mp k.2
    simpa using this
  let c : ↥K →* ↥K :=
    { toFun := fun k => ⟨a * k * a⁻¹, haK k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hcc : ∀ k : ↥K, ((c k : ↥K) : G) = a * k * a⁻¹ := fun k => rfl
  have hcenter : ∀ x : ↥K, x ∈ center ↥K → c x ∈ center ↥K := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro k
    have hk : c ⟨a⁻¹ * (k : G) * a, haK' k⟩ = k := Subtype.ext (by simp [hcc, mul_assoc])
    rw [← hk, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx]
  have hker' : φ.ker ≤ (φ.comp c).ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    have h1 : c x ∈ center ↥K := hcenter x (hker ▸ hx)
    have h2 : c x ∈ φ.ker := hker ▸ h1
    exact h2
  refine ⟨φ.liftOfRightInverse (Function.surjInv hφs) (Function.rightInverse_surjInv hφs)
    ⟨φ.comp c, hker'⟩, fun k k' hk' => ?_⟩
  rw [MonoidHom.liftOfRightInverse_comp_apply φ _ _ ⟨φ.comp c, hker'⟩ k]
  exact congrArg φ (Subtype.ext hk'.symm)

theorem exists_aut_conj (hφs : Function.Surjective φ) (hker : φ.ker = center ↥K) {a : G}
    (ha : a ∈ normalizer (K : Set G)) :
    ∃ α : MulAut X, ∀ k k' : ↥K, (k' : G) = a * k * a⁻¹ → α (φ k) = φ k' := by
  obtain ⟨β, hβ⟩ := exists_endo_conj φ hφs hker ha
  have ha' : a⁻¹ ∈ normalizer (K : Set G) := (normalizer (K : Set G)).inv_mem ha
  obtain ⟨β', hβ'⟩ := exists_endo_conj φ hφs hker ha'
  have haK : ∀ k : ↥K, a * (k : G) * a⁻¹ ∈ K := fun k =>
    (Subgroup.mem_normalizer_iff.mp ha k).mp k.2
  have haK' : ∀ k : ↥K, a⁻¹ * (k : G) * a⁻¹⁻¹ ∈ K := fun k =>
    (Subgroup.mem_normalizer_iff.mp ha' k).mp k.2
  have h1 : ∀ x, β' (β x) = x := by
    intro x
    obtain ⟨k, rfl⟩ := hφs x
    rw [hβ k ⟨a * k * a⁻¹, haK k⟩ rfl]
    exact (hβ' ⟨a * k * a⁻¹, haK k⟩ k (by simp [mul_assoc]))
  have h2 : ∀ x, β (β' x) = x := by
    intro x
    obtain ⟨k, rfl⟩ := hφs x
    rw [hβ' k ⟨a⁻¹ * k * a⁻¹⁻¹, haK' k⟩ rfl]
    exact (hβ ⟨a⁻¹ * k * a⁻¹⁻¹, haK' k⟩ k (by simp [mul_assoc]))
  exact ⟨{ toFun := β, invFun := β', left_inv := h1, right_inv := h2, map_mul' := map_mul β }, hβ⟩

theorem aut_conj_pow_apply {α : MulAut X} {a : G} (ha : a ∈ normalizer (K : Set G))
    (hα : ∀ k k' : ↥K, (k' : G) = a * k * a⁻¹ → α (φ k) = φ k') (n : ℕ) :
    ∀ k k' : ↥K, (k' : G) = a ^ n * k * (a ^ n)⁻¹ → (α ^ n) (φ k) = φ k' := by
  induction n with
  | zero =>
    intro k k' hk
    have : k' = k := Subtype.ext (by simpa using hk)
    subst this
    simp
  | succ n ih =>
    intro k k' hk
    have haK : a * (k : G) * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp ha k).mp k.2
    have h1 := hα k ⟨a * k * a⁻¹, haK⟩ rfl
    have h2 := ih ⟨a * k * a⁻¹, haK⟩ k' (by rw [hk, pow_succ]; simp [mul_assoc])
    rw [pow_succ, MulAut.mul_apply, h1]
    exact h2

theorem aut_conj_pow_eq_one (hφs : Function.Surjective φ) {α : MulAut X} {a : G}
    (ha : a ∈ normalizer (K : Set G))
    (hα : ∀ k k' : ↥K, (k' : G) = a * k * a⁻¹ → α (φ k) = φ k') {n : ℕ} (hn : a ^ n = 1) :
    α ^ n = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨k, rfl⟩ := hφs x
  rw [aut_conj_pow_apply φ ha hα n k k (by rw [hn]; simp)]
  rfl

theorem aut_conj_mem_img {α : MulAut X} {a : G} (ha : a ∈ normalizer (K : Set G))
    (hα : ∀ k k' : ↥K, (k' : G) = a * k * a⁻¹ → α (φ k) = φ k') {H : Subgroup G}
    (haH : a ∈ normalizer (H : Set G)) {y : X} (hy : y ∈ img φ H) : α y ∈ img φ H := by
  obtain ⟨h, hK, hH, rfl⟩ := (mem_img φ).mp hy
  have hK1 : a * h * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp ha h).mp hK
  have hH1 : a * h * a⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp haH h).mp hH
  rw [hα ⟨h, hK⟩ ⟨a * h * a⁻¹, hK1⟩ rfl]
  exact mem_img_of_mem φ hK1 hH1

end CFSG.RankThree.PartOne.F106
