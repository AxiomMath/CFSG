module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Subgroup CFSG CFSG.SectionRank.Ccomm

theorem noncommCoprod_injective_of_disjoint {Q : Type*} [Group Q]
    (hcomm : ∀ x y : Q, Commute x y) {A B : Subgroup Q} (hAB : A ⊓ B = ⊥) :
    Function.Injective (A.subtype.noncommCoprod B.subtype fun _ _ => hcomm _ _) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ h
  simp only [MonoidHom.noncommCoprod_apply, Subgroup.coe_subtype] at h
  have ha : (a : Q) ∈ A ⊓ B := by
    refine mem_inf.2 ⟨a.2, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_mem b.2
  rw [hAB, mem_bot] at ha
  have hb : (b : Q) = 1 := by
    rw [ha, one_mul] at h
    exact h
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

theorem homocyclic_of_power_image {p : ℕ} [hp : Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (hcomm : ∀ x y : Q, x * y = y * x) {a : ℕ} (ha : 1 ≤ a) (hexp : ∀ x : Q, x ^ (p ^ a) = 1)
    (Ω : Subgroup Q) (hΩ : ∀ x, x ∈ Ω ↔ x ^ p = 1) (hΩcard : Nat.card Ω = p ^ 2)
    (himg : ∀ u ∈ Ω, ∃ x : Q, x ^ (p ^ (a - 1)) = u) :
    Nonempty (Q ≃* Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a))) := by
  classical
  have hp1 := hp.out.one_lt
  have : IsMulCommutative Q := ⟨⟨hcomm⟩⟩
  have hcomm' : ∀ x y : Q, Commute x y := hcomm
  have hpa : p ^ (a - 1 + 1) = p ^ a := by rw [Nat.sub_add_cancel ha]
  have hΩnt : Nontrivial Ω :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hΩcard]; exact Nat.one_lt_pow two_ne_zero hp1)
  obtain ⟨⟨u₁, hu₁Ω⟩, hu₁⟩ := exists_ne (1 : Ω)
  have hu₁1 : u₁ ≠ 1 := fun h => hu₁ (Subtype.ext h)
  have hord₁ : orderOf u₁ = p := orderOf_eq_prime ((hΩ u₁).1 hu₁Ω) hu₁1
  have hZ₁card : Nat.card (zpowers u₁) = p := by rw [Nat.card_zpowers, hord₁]
  obtain ⟨u₂, hu₂Ω, hu₂Z⟩ : ∃ u₂ ∈ Ω, u₂ ∉ zpowers u₁ := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show Ω ≤ zpowers u₁ from fun x hx => hcon x hx)
    rw [hΩcard, hZ₁card] at h1
    have h2 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp1 (by norm_num)
    omega
  have hu₂1 : u₂ ≠ 1 := fun h => hu₂Z (h ▸ one_mem _)
  have hord₂ : orderOf u₂ = p := orderOf_eq_prime ((hΩ u₂).1 hu₂Ω) hu₂1
  have hZ₂card : Nat.card (zpowers u₂) = p := by rw [Nat.card_zpowers, hord₂]
  have hZdisj : zpowers u₁ ⊓ zpowers u₂ = ⊥ := by
    have hdvd := Subgroup.card_dvd_of_le (inf_le_right : zpowers u₁ ⊓ zpowers u₂ ≤ zpowers u₂)
    rw [hZ₂card] at hdvd
    rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right : zpowers u₁ ⊓ zpowers u₂ ≤ _)
        (by rw [h1, hZ₂card])
      have hmem : u₂ ∈ zpowers u₁ ⊓ zpowers u₂ := by
        rw [heq]
        exact mem_zpowers u₂
      exact hu₂Z (mem_inf.1 hmem).1
  have hΩform : ∀ z ∈ Ω, ∃ i j : ℕ, u₁ ^ i * u₂ ^ j = z := by
    set φ := (zpowers u₁).subtype.noncommCoprod (zpowers u₂).subtype fun _ _ => hcomm' _ _
      with hφ
    have hφinj := noncommCoprod_injective_of_disjoint hcomm' hZdisj
    have hrange : φ.range ≤ Ω := by
      rintro _ ⟨⟨a₁, a₂⟩, rfl⟩
      rw [hφ, MonoidHom.noncommCoprod_apply]
      exact mul_mem ((zpowers_le.2 hu₁Ω) a₁.2) ((zpowers_le.2 hu₂Ω) a₂.2)
    have hcardφ : Nat.card φ.range = p ^ 2 := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj, card_top, Nat.card_prod,
        hZ₁card, hZ₂card, sq]
    have heq := Subgroup.eq_of_le_of_card_ge hrange (by rw [hcardφ, hΩcard])
    intro z hz
    rw [← heq] at hz
    obtain ⟨⟨a₁, a₂⟩, rfl⟩ := hz
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 a₁.2)
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 a₂.2)
    exact ⟨i, j, by rw [hφ, MonoidHom.noncommCoprod_apply, coe_subtype, coe_subtype, hi, hj]⟩
  obtain ⟨x₁, hx₁⟩ := himg u₁ hu₁Ω
  obtain ⟨x₂, hx₂⟩ := himg u₂ hu₂Ω
  have hordx : ∀ (x u : Q), x ^ (p ^ (a - 1)) = u → u ≠ 1 → orderOf x = p ^ a := by
    intro x u hxu hu1
    rw [← hpa]
    exact orderOf_eq_prime_pow (by rw [hxu]; exact hu1) (by rw [hpa]; exact hexp x)
  have hA : Nat.card (zpowers x₁) = p ^ a := by rw [Nat.card_zpowers, hordx x₁ u₁ hx₁ hu₁1]
  have hB : Nat.card (zpowers x₂) = p ^ a := by rw [Nat.card_zpowers, hordx x₂ u₂ hx₂ hu₂1]
  have hlow : ∀ (x w : Q), orderOf x = p ^ a → w ∈ zpowers x → w ^ p = 1 →
      w ∈ zpowers (x ^ (p ^ (a - 1))) := by
    intro x w hx hw hwp
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hw)
    have hdvd : p ^ (a - 1) * p ∣ m * p := by
      rw [← pow_succ, hpa, ← hx]
      rw [← pow_mul] at hwp
      exact orderOf_dvd_of_pow_eq_one hwp
    obtain ⟨m', hm'⟩ := Nat.dvd_of_mul_dvd_mul_right hp.out.pos hdvd
    rw [hm', pow_mul]
    exact pow_mem (mem_zpowers _) m'
  have hABdisj : zpowers x₁ ⊓ zpowers x₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [mem_bot]
    by_contra hz1
    obtain ⟨hzA, hzB⟩ := mem_inf.1 hz
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one (hexp z))
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hz1 hk
    have hw1 : z ^ (p ^ (k - 1)) ≠ 1 := pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.out.ne_zero)
      (by rw [hk]; exact Nat.pow_lt_pow_right hp1 (by omega))
    have hwp : (z ^ (p ^ (k - 1))) ^ p = 1 := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk0), ← hk,
        pow_orderOf_eq_one]
    have hw₁ : z ^ (p ^ (k - 1)) ∈ zpowers u₁ := by
      rw [← hx₁]
      exact hlow x₁ _ (hordx x₁ u₁ hx₁ hu₁1) (pow_mem hzA _) hwp
    have hw₂ : z ^ (p ^ (k - 1)) ∈ zpowers u₂ := by
      rw [← hx₂]
      exact hlow x₂ _ (hordx x₂ u₂ hx₂ hu₂1) (pow_mem hzB _) hwp
    have hw : z ^ (p ^ (k - 1)) ∈ zpowers u₁ ⊓ zpowers u₂ := mem_inf.2 ⟨hw₁, hw₂⟩
    rw [hZdisj, mem_bot] at hw
    exact hw1 hw
  have hgen : ∀ k, k ≤ a → ∀ y : Q, y ^ (p ^ k) = 1 → y ∈ zpowers x₁ ⊔ zpowers x₂ := by
    intro k
    induction k with
    | zero =>
      intro _ y hy
      rw [pow_zero, pow_one] at hy
      rw [hy]
      exact one_mem _
    | succ k ih =>
      intro hk y hy
      have hzΩ : y ^ (p ^ k) ∈ Ω := by
        rw [hΩ, ← pow_mul, ← pow_succ]
        exact hy
      obtain ⟨i, j, hij⟩ := hΩform _ hzΩ
      have hq : p ^ (a - 1 - k) * p ^ k = p ^ (a - 1) := by
        rw [← pow_add, Nat.sub_add_cancel (by omega : k ≤ a - 1)]
      have hwAB : x₁ ^ (p ^ (a - 1 - k) * i) * x₂ ^ (p ^ (a - 1 - k) * j) ∈
          zpowers x₁ ⊔ zpowers x₂ :=
        mul_mem (mem_sup_left (pow_mem (mem_zpowers x₁) _))
          (mem_sup_right (pow_mem (mem_zpowers x₂) _))
      have hwk : (x₁ ^ (p ^ (a - 1 - k) * i) * x₂ ^ (p ^ (a - 1 - k) * j)) ^ (p ^ k) =
          y ^ (p ^ k) := by
        rw [Commute.mul_pow (hcomm _ _), ← pow_mul, ← pow_mul,
          show p ^ (a - 1 - k) * i * p ^ k = p ^ (a - 1) * i by rw [mul_right_comm, hq],
          show p ^ (a - 1 - k) * j * p ^ k = p ^ (a - 1) * j by rw [mul_right_comm, hq],
          pow_mul, pow_mul, hx₁, hx₂, hij]
      have hy' : (y * (x₁ ^ (p ^ (a - 1 - k) * i) * x₂ ^ (p ^ (a - 1 - k) * j))⁻¹) ^ (p ^ k) =
          1 := by
        rw [Commute.mul_pow (hcomm _ _), inv_pow, hwk, mul_inv_cancel]
      have h1 := ih (by omega) _ hy'
      have e : y = y * (x₁ ^ (p ^ (a - 1 - k) * i) * x₂ ^ (p ^ (a - 1 - k) * j))⁻¹ *
          (x₁ ^ (p ^ (a - 1 - k) * i) * x₂ ^ (p ^ (a - 1 - k) * j)) := by group
      rw [e]
      exact mul_mem h1 hwAB
  have htop : zpowers x₁ ⊔ zpowers x₂ = ⊤ :=
    eq_top_iff.2 fun y _ => hgen a le_rfl y (hexp y)
  set φ := (zpowers x₁).subtype.noncommCoprod (zpowers x₂).subtype fun _ _ => hcomm' _ _ with hφ
  have hφinj := noncommCoprod_injective_of_disjoint hcomm' hABdisj
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ zpowers x₁ ⊔ zpowers x₂ := htop ▸ mem_top y
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_normal_right.1 hy
    exact ⟨(⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩), rfl⟩
  have hCcard : Nat.card (Multiplicative (ZMod (p ^ a))) = p ^ a := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact ⟨(MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm.trans
    (MulEquiv.prodCongr (mulEquivOfCyclicCardEq (hA.trans hCcard.symm))
      (mulEquivOfCyclicCardEq (hB.trans hCcard.symm)))⟩

end CFSG.LocalAnalysis.SteinbergBV
