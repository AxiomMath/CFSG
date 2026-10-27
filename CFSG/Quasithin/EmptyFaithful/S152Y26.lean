module

public import CFSG.Quasithin.EmptyFaithful.S152N2Cases
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType

namespace S152Y

section Dihedral

variable {Q : Type*} [Group Q]

theorem nonempty_sup_zpowers_mulEquiv_dihedral' (C : Subgroup Q) (hC : IsCyclic C) (w : Q)
    (hw : w ∉ C) (hw2 : w * w = 1) (hinv : ∀ c ∈ C, w * c * w⁻¹ = c⁻¹) :
    Nonempty ((C ⊔ Subgroup.zpowers w : Subgroup Q) ≃* DihedralGroup (Nat.card C)) := by
  classical
  let e : Multiplicative (ZMod (Nat.card C)) ≃* C := zmodCyclicMulEquiv hC
  let rot : ZMod (Nat.card C) → Q := fun i => (e (Multiplicative.ofAdd i) : C)
  have hrot_mem (i : ZMod (Nat.card C)) : rot i ∈ C := (e (Multiplicative.ofAdd i)).property
  have hrot_add (i j : ZMod (Nat.card C)) : rot (i + j) = rot i * rot j :=
    congrArg Subtype.val (e.map_mul (Multiplicative.ofAdd i) (Multiplicative.ofAdd j))
  have hrot_neg (i : ZMod (Nat.card C)) : rot (-i) = (rot i)⁻¹ :=
    congrArg Subtype.val (e.map_inv (Multiplicative.ofAdd i))
  have hrot_zero : rot 0 = 1 := congrArg Subtype.val e.map_one
  have hw_inv_eq : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw2).symm
  have hw_mul_rot (i : ZMod (Nat.card C)) : w * rot i = rot (-i) * w := by
    calc w * rot i = (w * rot i * w⁻¹) * w := by rw [hw_inv_eq, mul_assoc, hw2, mul_one]
      _ = (rot i)⁻¹ * w := by rw [hinv (rot i) (hrot_mem i)]
      _ = rot (-i) * w := by rw [hrot_neg]
  have hrot_mul_w (i : ZMod (Nat.card C)) : rot i * w = w * rot (-i) := by
    calc rot i * w = rot (-(-i)) * w := by rw [neg_neg]
      _ = w * rot (-i) := (hw_mul_rot (-i)).symm
  let hom : DihedralGroup (Nat.card C) →* Q :=
    { toFun := fun x => match x with
        | DihedralGroup.r i => rot i
        | DihedralGroup.sr i => w * rot i
      map_one' := hrot_zero
      map_mul' := by
        rintro (i | i) (j | j)
        · change rot (i + j) = rot i * rot j
          exact hrot_add i j
        · change w * rot (j - i) = rot i * (w * rot j)
          calc w * rot (j - i) = w * rot (-i + j) := by rw [sub_eq_add_neg, add_comm]
            _ = w * (rot (-i) * rot j) := by rw [hrot_add]
            _ = (w * rot (-i)) * rot j := by rw [mul_assoc]
            _ = (rot i * w) * rot j := by rw [hrot_mul_w]
            _ = rot i * (w * rot j) := by rw [mul_assoc]
        · change w * rot (i + j) = (w * rot i) * rot j
          rw [hrot_add, mul_assoc]
        · change rot (j - i) = (w * rot i) * (w * rot j)
          calc rot (j - i) = rot (-i + j) := by rw [sub_eq_add_neg, add_comm]
            _ = rot (-i) * rot j := hrot_add (-i) j
            _ = (w * w) * (rot (-i) * rot j) := by rw [hw2, one_mul]
            _ = (w * (w * rot (-i))) * rot j := by simp only [mul_assoc]
            _ = (w * (rot i * w)) * rot j := by rw [hrot_mul_w]
            _ = (w * rot i) * (w * rot j) := by simp only [mul_assoc] }
  have hinj : Function.Injective hom := by
    rintro (i | i) (j | j) hij
    · apply congrArg DihedralGroup.r
      change rot i = rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j :=
        e.injective (Subtype.ext hij)
      exact congrArg Multiplicative.toAdd heq
    · exfalso
      apply hw
      change rot i = w * rot j at hij
      have hwrj : w * rot j ∈ C := hij ▸ hrot_mem i
      exact (C.mul_mem_cancel_right (hrot_mem j)).mp hwrj
    · exfalso
      apply hw
      change w * rot i = rot j at hij
      have hwri : w * rot i ∈ C := hij ▸ hrot_mem j
      exact (C.mul_mem_cancel_right (hrot_mem i)).mp hwri
    · apply congrArg DihedralGroup.sr
      change w * rot i = w * rot j at hij
      have heq : Multiplicative.ofAdd i = Multiplicative.ofAdd j :=
        e.injective (Subtype.ext (mul_left_cancel hij))
      exact congrArg Multiplicative.toAdd heq
  have hrange : hom.range = C ⊔ Subgroup.zpowers w := by
    apply le_antisymm
    · rintro x ⟨(i | i), rfl⟩
      · exact Subgroup.mem_sup_left (hrot_mem i)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w))
          (Subgroup.mem_sup_left (hrot_mem i))
    · apply sup_le
      · intro c hc
        refine ⟨DihedralGroup.r (Multiplicative.toAdd (e.symm ⟨c, hc⟩)), ?_⟩
        change rot (Multiplicative.toAdd (e.symm ⟨c, hc⟩)) = c
        change ((e (Multiplicative.ofAdd (Multiplicative.toAdd (e.symm ⟨c, hc⟩))) : C) : Q) = c
        rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
      · rw [Subgroup.zpowers_le]
        refine ⟨DihedralGroup.sr 0, ?_⟩
        change w * rot 0 = w
        rw [hrot_zero, mul_one]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm⟩

theorem eq_one_or_eq_of_mem_zpowers_of_sq {ρ w : Q} (hρ2 : ρ * ρ = 1)
    (hw : w ∈ Subgroup.zpowers ρ) : w = 1 ∨ w = ρ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    subst hm
    rw [zpow_mul, zpow_two, hρ2, one_zpow]
  · right
    subst hm
    rw [zpow_add_one, zpow_mul, zpow_two, hρ2, one_zpow, one_mul]

theorem mem_zpowers_cases_four {ρ x : Q} (h4 : orderOf ρ = 4) (hx : x ∈ Subgroup.zpowers ρ) :
    x = 1 ∨ x = ρ ∨ x = ρ ^ 2 ∨ x = ρ ^ 3 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h := zpow_mod_orderOf ρ k
  rw [h4] at h
  have hk : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 1 ∨ k % ((4 : ℕ) : ℤ) = 2 ∨
      k % ((4 : ℕ) : ℤ) = 3 := by omega
  rcases hk with hk | hk | hk | hk <;> rw [hk] at h
  · left; simpa using h.symm
  · right; left; simpa using h.symm
  · right; right; left
    rw [← h]
    simp [sq]
  · right; right; right
    rw [← h]
    simp

end Dihedral

section Prime

variable {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime] {A : Subgroup Q}

omit [Finite Q] in
theorem eq_one_of_two_power (hp2 : p ≠ 2) (hA : Nat.card A = p) {c : Q} (hc : c ∈ A)
    (hc2 : ∃ k : ℕ, c ^ 2 ^ k = 1) : c = 1 := by
  obtain ⟨k, hk⟩ := hc2
  have hp : c ^ p = 1 := by
    have : (⟨c, hc⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
    rw [hA] at this
    simpa using congrArg Subtype.val this
  have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hp
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp2))
  have : orderOf c = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h2)
  exact orderOf_eq_one_iff.mp this

theorem mem_zpowers_of_prime_card (hA : Nat.card A = p) {a₁ : Q} (ha₁ : a₁ ∈ A) (h1 : a₁ ≠ 1)
    {a : Q} (ha : a ∈ A) : a ∈ Subgroup.zpowers a₁ := by
  have hz : Subgroup.zpowers a₁ ≤ A := (Subgroup.zpowers_le).mpr ha₁
  have hord : orderOf a₁ = p := by
    have hpow : a₁ ^ p = 1 := by
      have : (⟨a₁, ha₁⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
      rw [hA] at this
      simpa using congrArg Subtype.val this
    have hdvd : orderOf a₁ ∣ p := orderOf_dvd_of_pow_eq_one hpow
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  have hcard : Nat.card (Subgroup.zpowers a₁) = Nat.card A := by rw [Nat.card_zpowers, hord, hA]
  have heq : Subgroup.zpowers a₁ = A := Subgroup.eq_of_le_of_card_ge hz hcard.ge
  rw [heq]
  exact ha

theorem centralizes_or_inverts (hA : Nat.card A = p)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {s : Q}
    (hsA : s ∈ Subgroup.normalizer (A : Set Q)) (hs2 : s * s = 1) :
    (∀ a ∈ A, s * a * s⁻¹ = a) ∨ (∀ a ∈ A, s * a * s⁻¹ = a⁻¹) := by
  by_cases hc : ∀ a ∈ A, s * a * s⁻¹ = a
  · exact Or.inl hc
  · right
    push Not at hc
    obtain ⟨a₁, ha₁, hne⟩ := hc
    have hconjA : ∀ a ∈ A, s * a * s⁻¹ ∈ A := fun a ha =>
      (Subgroup.mem_normalizer_iff.mp hsA a).mp ha
    have ha₁1 : a₁ ≠ 1 := by
      rintro rfl
      simp at hne
    set b := a₁ * (s * a₁ * s⁻¹) with hb
    have hbA : b ∈ A := A.mul_mem ha₁ (hconjA a₁ ha₁)
    have hss : s * (s * a₁ * s⁻¹) * s⁻¹ = a₁ := by
      have : s * (s * a₁ * s⁻¹) * s⁻¹ = (s * s) * a₁ * (s * s)⁻¹ := by group
      rw [this, hs2]
      simp
    have hsb : s * b * s⁻¹ = b := by
      rw [hb]
      calc s * (a₁ * (s * a₁ * s⁻¹)) * s⁻¹
          = (s * a₁ * s⁻¹) * (s * (s * a₁ * s⁻¹) * s⁻¹) := by group
        _ = (s * a₁ * s⁻¹) * a₁ := by rw [hss]
        _ = a₁ * (s * a₁ * s⁻¹) := hAcomm _ (hconjA a₁ ha₁) _ ha₁
    have hb1 : b = 1 := by
      by_contra hb1
      apply hne
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_prime_card hA hbA hb1 ha₁)
      rw [← hk, ← conj_zpow, hsb]
    have hinv1 : s * a₁ * s⁻¹ = a₁⁻¹ := by
      have : a₁ * (s * a₁ * s⁻¹) = 1 := hb1
      exact eq_inv_of_mul_eq_one_right this
    intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_prime_card hA ha₁ ha₁1 ha)
    rw [← hk, ← conj_zpow, hinv1, inv_zpow]

end Prime

section Central

variable {Q : Type*} [Group Q]

theorem mem_pCore_of_central [Finite Q] {z : Q} (hz : ∀ y : Q, y * z = z * y)
    (hz2 : ∃ k : ℕ, z ^ 2 ^ k = 1) : z ∈ CFSG.Open.pCore 2 Q := by
  have hn : (Subgroup.zpowers z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have h1 : g * z ^ m = z ^ m * g := (Commute.zpow_right (hz g) m).eq
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) m
  have hp : IsPGroup 2 (Subgroup.zpowers z) := by
    obtain ⟨k, hk⟩ := hz2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  exact BorelTits.le_pCore 2 hn hp (Subgroup.mem_zpowers z)

end Central

section Recognition

variable {Q : Type*} [Group Q] [Finite Q]

theorem nonempty_oTwoQuot_sup_dihedral {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A S : Subgroup Q} (hA : Nat.card A = p) (hSe : ∀ s ∈ S, s * s = 1)
    (hSA : S ≤ Subgroup.normalizer (A : Set Q))
    (hact : ∃ s ∈ S, ∃ a ∈ A, s * a * s⁻¹ ≠ a) :
    Nonempty (OTwoQuot (A ⊔ S) ≃* DihedralGroup p) := by
  classical
  obtain ⟨ρ, hρS, a₀, ha₀, hρa₀⟩ := hact
  have hAcyc : IsCyclic A := isCyclic_of_prime_card hA
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have := mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hSabel : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    have hst := hSe (s * t) (S.mul_mem hs ht)
    have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hSe s hs)
    have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hSe t ht)
    calc s * t = (s * t)⁻¹ := eq_inv_of_mul_eq_one_left hst
      _ = t * s := by rw [mul_inv_rev, hs', ht']
  have hρ2 : ρ * ρ = 1 := hSe ρ hρS
  have hρN : ρ ∈ Subgroup.normalizer (A : Set Q) := hSA hρS
  have hρ_inv : ∀ a ∈ A, ρ * a * ρ⁻¹ = a⁻¹ := by
    rcases centralizes_or_inverts hA hAcomm hρN hρ2 with h | h
    · exact absurd (h a₀ ha₀) hρa₀
    · exact h
  have hρA : ρ ∉ A := fun h => hρa₀ (by
    have := hAcomm ρ h a₀ ha₀
    calc ρ * a₀ * ρ⁻¹ = a₀ * ρ * ρ⁻¹ := by rw [this]
      _ = a₀ := by simp)
  obtain ⟨eD⟩ := nonempty_sup_zpowers_mulEquiv_dihedral' A hAcyc ρ hρA hρ2 hρ_inv
  have hDP : A ⊔ Subgroup.zpowers ρ ≤ A ⊔ S :=
    sup_le_sup_left ((Subgroup.zpowers_le).mpr hρS) A
  have hPmem : ∀ x ∈ A ⊔ S, ∃ a ∈ A, ∃ s ∈ S, x = a * s := by
    intro x hx
    have h1 := Subgroup.coe_mul_of_right_le_normalizer_left A S hSA
    have hx' : x ∈ ((A ⊔ S : Subgroup Q) : Set Q) := hx
    rw [h1] at hx'
    obtain ⟨a, ha, s, hs, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨a, ha, s, hs, rfl⟩
  have hDmem : ∀ x ∈ A ⊔ Subgroup.zpowers ρ, ∃ a ∈ A, x = a ∨ x = a * ρ := by
    intro x hx
    have hz : Subgroup.zpowers ρ ≤ Subgroup.normalizer (A : Set Q) :=
      (Subgroup.zpowers_le).mpr hρN
    have h1 := Subgroup.coe_mul_of_right_le_normalizer_left A (Subgroup.zpowers ρ) hz
    have hx' : x ∈ ((A ⊔ Subgroup.zpowers ρ : Subgroup Q) : Set Q) := hx
    rw [h1] at hx'
    obtain ⟨a, ha, w, hw, rfl⟩ := Set.mem_mul.mp hx'
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hρ2 hw with rfl | rfl
    · exact ⟨a, ha, Or.inl (mul_one a)⟩
    · exact ⟨a, ha, Or.inr rfl⟩
  have hDnorm : ∀ x ∈ A ⊔ Subgroup.zpowers ρ, ∀ b ∈ A, x * b * x⁻¹ ∈ A := by
    intro x hx b hb
    obtain ⟨a, ha, hxa | hxa⟩ := hDmem x hx
    · rw [hxa]
      exact A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)
    · rw [hxa]
      have h1 : a * ρ * b * (a * ρ)⁻¹ = a * (ρ * b * ρ⁻¹) * a⁻¹ := by group
      rw [h1, hρ_inv b hb]
      exact A.mul_mem (A.mul_mem ha (A.inv_mem hb)) (A.inv_mem ha)
  set P := A ⊔ S with hP
  let φ : ↥(A ⊔ Subgroup.zpowers ρ) →* OTwoQuot P :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥P)).comp (Subgroup.inclusion hDP)
  have hAN : ∀ (a : Q) (ha : a ∈ A),
      ((⟨a, Subgroup.mem_sup_left ha⟩ : ↥P) ∈ CFSG.Open.pCore 2 ↥P) → a = 1 := by
    intro a ha hN
    obtain ⟨k, hk⟩ := (BorelTits.pCore_isPGroup (G := ↥P) 2) ⟨_, hN⟩
    refine eq_one_of_two_power hp2 hA ha ⟨k, ?_⟩
    simpa using congrArg (fun z : CFSG.Open.pCore 2 ↥P => ((z : ↥P) : Q)) hk
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : Subgroup.inclusion hDP x ∈ CFSG.Open.pCore 2 ↥P := (QuotientGroup.eq_one_iff _).mp hx
    have hcomm : ∀ b ∈ A, (x : Q) * b * (x : Q)⁻¹ = b := by
      intro b hb
      have hbP : b ∈ P := Subgroup.mem_sup_left hb
      have hc : Subgroup.inclusion hDP x * ⟨b, hbP⟩ * (Subgroup.inclusion hDP x)⁻¹ * ⟨b, hbP⟩⁻¹ ∈
          CFSG.Open.pCore 2 ↥P := by
        have h1 := (BorelTits.pCore_normal (G := ↥P) 2).conj_mem _
          ((CFSG.Open.pCore 2 ↥P).inv_mem hxN) ⟨b, hbP⟩
        have h2 := (CFSG.Open.pCore 2 ↥P).mul_mem hxN h1
        have : Subgroup.inclusion hDP x * ⟨b, hbP⟩ * (Subgroup.inclusion hDP x)⁻¹ *
            ⟨b, hbP⟩⁻¹ = Subgroup.inclusion hDP x * (⟨b, hbP⟩ * (Subgroup.inclusion hDP x)⁻¹ *
            ⟨b, hbP⟩⁻¹) := by group
        rw [this]
        exact h2
      have hcA : (x : Q) * b * (x : Q)⁻¹ * b⁻¹ ∈ A :=
        A.mul_mem (hDnorm x x.2 b hb) (A.inv_mem hb)
      have h1 : (⟨(x : Q) * b * (x : Q)⁻¹ * b⁻¹, Subgroup.mem_sup_left hcA⟩ : ↥P) ∈
          CFSG.Open.pCore 2 ↥P := hc
      have := hAN _ hcA h1
      calc (x : Q) * b * (x : Q)⁻¹ = (x : Q) * b * (x : Q)⁻¹ * b⁻¹ * b := by group
        _ = b := by rw [this, one_mul]
    obtain ⟨a, ha, hxa | hxa⟩ := hDmem x x.2
    ·
      have h1 : (⟨a, Subgroup.mem_sup_left ha⟩ : ↥P) ∈ CFSG.Open.pCore 2 ↥P := by
        have : Subgroup.inclusion hDP x = ⟨a, Subgroup.mem_sup_left ha⟩ := Subtype.ext hxa
        rw [← this]
        exact hxN
      have := hAN a ha h1
      apply Subtype.ext
      rw [hxa, this]
      rfl
    ·
      exfalso
      have h1 := hcomm a₀ ha₀
      rw [hxa] at h1
      have h2 : a * ρ * a₀ * (a * ρ)⁻¹ = a₀⁻¹ := by
        have : a * ρ * a₀ * (a * ρ)⁻¹ = a * (ρ * a₀ * ρ⁻¹) * a⁻¹ := by group
        rw [this, hρ_inv a₀ ha₀]
        have := hAcomm a ha a₀⁻¹ (A.inv_mem ha₀)
        calc a * a₀⁻¹ * a⁻¹ = a₀⁻¹ * a * a⁻¹ := by rw [this]
          _ = a₀⁻¹ := by simp
      rw [h2] at h1
      apply hρa₀
      rw [hρ_inv a₀ ha₀, h1]
  have hsurj : Function.Surjective φ := by
    intro u
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨a, ha, s, hs, hg⟩ := hPmem g.1 g.2
    have hcentral : ∀ (t : Q) (ht : t ∈ S), (∀ b ∈ A, t * b * t⁻¹ = b) →
        (⟨t, Subgroup.mem_sup_right ht⟩ : ↥P) ∈ CFSG.Open.pCore 2 ↥P := by
      intro t ht htA
      apply mem_pCore_of_central
      · intro y
        obtain ⟨a', ha', s', hs', hy⟩ := hPmem y.1 y.2
        apply Subtype.ext
        show (y : Q) * t = t * (y : Q)
        have hta : t * a' = a' * t := by
          have := htA a' ha'
          calc t * a' = t * a' * t⁻¹ * t := by group
            _ = a' * t := by rw [this]
        rw [hy]
        calc a' * s' * t = a' * (s' * t) := mul_assoc _ _ _
          _ = a' * (t * s') := by rw [hSabel s' hs' t ht]
          _ = (a' * t) * s' := (mul_assoc _ _ _).symm
          _ = (t * a') * s' := by rw [hta]
          _ = t * (a' * s') := mul_assoc _ _ _
      · refine ⟨1, Subtype.ext ?_⟩
        show t ^ 2 ^ 1 = 1
        rw [pow_one, pow_two]
        exact hSe t ht
    have hρinv' : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ2
    rcases centralizes_or_inverts hA hAcomm (hSA hs) (hSe s hs) with hc | hc
    · refine ⟨⟨a, Subgroup.mem_sup_left ha⟩, ?_⟩
      show QuotientGroup.mk (Subgroup.inclusion hDP ⟨a, Subgroup.mem_sup_left ha⟩) = QuotientGroup.mk g
      rw [QuotientGroup.eq]
      have : (Subgroup.inclusion hDP ⟨a, Subgroup.mem_sup_left ha⟩)⁻¹ * g =
          ⟨s, Subgroup.mem_sup_right hs⟩ := by
        apply Subtype.ext
        show a⁻¹ * (g : Q) = s
        rw [hg]
        group
      rw [this]
      exact hcentral s hs hc
    · have hmem : a * ρ ∈ A ⊔ Subgroup.zpowers ρ :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (Subgroup.mem_zpowers ρ))
      refine ⟨⟨a * ρ, hmem⟩, ?_⟩
      show QuotientGroup.mk (Subgroup.inclusion hDP ⟨a * ρ, hmem⟩) = QuotientGroup.mk g
      rw [QuotientGroup.eq]
      have hρsS : ρ * s ∈ S := S.mul_mem hρS hs
      have : (Subgroup.inclusion hDP ⟨a * ρ, hmem⟩)⁻¹ * g = ⟨ρ * s, Subgroup.mem_sup_right hρsS⟩ := by
        apply Subtype.ext
        show (a * ρ)⁻¹ * (g : Q) = ρ * s
        rw [hg, mul_inv_rev, hρinv']
        group
      rw [this]
      refine hcentral (ρ * s) hρsS fun b hb => ?_
      have h1 : ρ * s * b * (ρ * s)⁻¹ = ρ * (s * b * s⁻¹) * ρ⁻¹ := by group
      rw [h1, hc b hb]
      have h2 : ρ * b⁻¹ * ρ⁻¹ = (ρ * b * ρ⁻¹)⁻¹ := by group
      rw [h2, hρ_inv b hb, inv_inv]
  have eD' : ↥(A ⊔ Subgroup.zpowers ρ) ≃* DihedralGroup p := hA ▸ eD
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm.trans eD'⟩

end Recognition

section Sz

variable {Q : Type} [Group Q] [Finite Q]

theorem centralizes_of_mem_pCore {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P A : Subgroup Q}
    (hAP : A ≤ P) (hA : Nat.card A = p) {x : Q} (hxP : x ∈ P)
    (hxN : (⟨x, hxP⟩ : ↥P) ∈ CFSG.Open.pCore 2 ↥P) (hxA : ∀ b ∈ A, x * b * x⁻¹ ∈ A) :
    ∀ b ∈ A, x * b * x⁻¹ = b := by
  intro b hb
  have hbP : b ∈ P := hAP hb
  have h1 := (BorelTits.pCore_normal (G := ↥P) 2).conj_mem _
    ((CFSG.Open.pCore 2 ↥P).inv_mem hxN) ⟨b, hbP⟩
  have h2 := (CFSG.Open.pCore 2 ↥P).mul_mem hxN h1
  have h3 : (⟨x, hxP⟩ : ↥P) * (⟨b, hbP⟩ * (⟨x, hxP⟩ : ↥P)⁻¹ * ⟨b, hbP⟩⁻¹) =
      ⟨x * b * x⁻¹ * b⁻¹, P.mul_mem (P.mul_mem (P.mul_mem hxP hbP) (P.inv_mem hxP))
        (P.inv_mem hbP)⟩ := by
    apply Subtype.ext
    show x * (b * x⁻¹ * b⁻¹) = x * b * x⁻¹ * b⁻¹
    group
  rw [h3] at h2
  have hcA : x * b * x⁻¹ * b⁻¹ ∈ A := A.mul_mem (hxA b hb) (A.inv_mem hb)
  obtain ⟨k, hk⟩ := (BorelTits.pCore_isPGroup (G := ↥P) 2) ⟨_, h2⟩
  have h4 : x * b * x⁻¹ * b⁻¹ = 1 :=
    eq_one_of_two_power hp2 hA hcA ⟨k, by
      simpa using congrArg (fun z : CFSG.Open.pCore 2 ↥P => ((z : ↥P) : Q)) hk⟩
  calc x * b * x⁻¹ = x * b * x⁻¹ * b⁻¹ * b := by group
    _ = b := by rw [h4, one_mul]

theorem nonempty_oTwoQuot_sup_sz (hFr : S152N2.Frobenius20IsSz2) {A S : Subgroup Q} {ρ : Q}
    (hA : Nat.card A = 5) (hS : Nat.card S = 4) (hρS : ρ ∈ S) (hρ4 : orderOf ρ = 4)
    (hSA : S ≤ Subgroup.normalizer (A : Set Q))
    (hinv : ∀ a ∈ A, ρ ^ 2 * a * (ρ ^ 2)⁻¹ = a⁻¹) :
    Nonempty (OTwoQuot (A ⊔ S) ≃* ↥(CFSG.Open.Sz 0)) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hSz : Subgroup.zpowers ρ = S :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hρS)
      (by rw [Nat.card_zpowers, hρ4, hS])
  subst hSz
  have hAcyc : IsCyclic A := isCyclic_of_prime_card hA
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have := mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hA1 : ∀ a ∈ A, a ≠ 1 → a⁻¹ ≠ a := by
    intro a ha ha1 hinvA
    apply ha1
    refine eq_one_of_two_power hp2 hA ha ⟨1, ?_⟩
    rw [pow_one, pow_two]
    calc a * a = a * a⁻¹ := by rw [hinvA]
      _ = 1 := mul_inv_cancel a
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hcon
    rw [this, Subgroup.card_bot] at hA
    omega
  have hρ44 : ρ ^ 4 = 1 := by rw [← hρ4]; exact pow_orderOf_eq_one ρ
  have hkey : ¬ (∀ a ∈ A, ρ ^ 2 * a * (ρ ^ 2)⁻¹ = a) := fun h =>
    hA1 a₀ ha₀ ha₀1 ((hinv a₀ ha₀).symm.trans (h a₀ ha₀))
  have hcent : ∀ x ∈ Subgroup.zpowers ρ, (∀ a ∈ A, x * a * x⁻¹ = a) → x = 1 := by
    intro x hx hxc
    rcases mem_zpowers_cases_four hρ4 hx with h | h | h | h
    · exact h
    · exfalso
      rw [h] at hxc
      apply hkey
      intro a ha
      have h1 := hxc a ha
      calc ρ ^ 2 * a * (ρ ^ 2)⁻¹ = ρ * (ρ * a * ρ⁻¹) * ρ⁻¹ := by
            simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = a := by rw [h1, h1]
    · exfalso
      rw [h] at hxc
      exact hkey hxc
    · exfalso
      rw [h] at hxc
      apply hkey
      intro a ha
      have h1 := hxc a ha
      have h6 : (ρ ^ 3) ^ 2 = ρ ^ 2 := by
        calc (ρ ^ 3) ^ 2 = ρ ^ 4 * ρ ^ 2 := by group
          _ = ρ ^ 2 := by rw [hρ44, one_mul]
      calc ρ ^ 2 * a * (ρ ^ 2)⁻¹ = (ρ ^ 3) ^ 2 * a * ((ρ ^ 3) ^ 2)⁻¹ := by rw [h6]
        _ = ρ ^ 3 * (ρ ^ 3 * a * (ρ ^ 3)⁻¹) * (ρ ^ 3)⁻¹ := by
            simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = a := by rw [h1, h1]
  have hAS : A ⊓ Subgroup.zpowers ρ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxS⟩
    have h5 : x ^ 5 = 1 := by
      have : (⟨x, hxA⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
      rw [hA] at this
      simpa using congrArg Subtype.val this
    have h4 : x ^ 4 = 1 := by
      have : (⟨x, hxS⟩ : Subgroup.zpowers ρ) ^ Nat.card (Subgroup.zpowers ρ) = 1 :=
        pow_card_eq_one'
      rw [Nat.card_zpowers, hρ4] at this
      simpa using congrArg Subtype.val this
    have : x = 1 := by
      calc x = x ^ 5 * (x ^ 4)⁻¹ := by group
        _ = 1 := by rw [h5, h4]; simp
    simpa using this
  have hz : Subgroup.zpowers ρ ≤ Subgroup.normalizer (A : Set Q) := hSA
  have hPnorm : A ⊔ Subgroup.zpowers ρ ≤ Subgroup.normalizer (A : Set Q) :=
    sup_le Subgroup.le_normalizer hz
  have hPmem : ∀ x ∈ A ⊔ Subgroup.zpowers ρ, ∃ a ∈ A, ∃ w ∈ Subgroup.zpowers ρ, x = a * w := by
    intro x hx
    have h1 := Subgroup.coe_mul_of_right_le_normalizer_left A (Subgroup.zpowers ρ) hz
    have hx' : x ∈ ((A ⊔ Subgroup.zpowers ρ : Subgroup Q) : Set Q) := hx
    rw [h1] at hx'
    obtain ⟨a, ha, w, hw, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨a, ha, w, hw, rfl⟩
  have hPconj : ∀ x ∈ A ⊔ Subgroup.zpowers ρ, ∀ b ∈ A, x * b * x⁻¹ ∈ A := fun x hx b hb =>
    (Subgroup.mem_normalizer_iff.mp (hPnorm hx) b).mp hb
  have hcentP : ∀ x ∈ A ⊔ Subgroup.zpowers ρ, (∀ b ∈ A, x * b * x⁻¹ = b) → x ∈ A := by
    intro x hx hxc
    obtain ⟨a, ha, w, hw, rfl⟩ := hPmem x hx
    have hwc : ∀ b ∈ A, w * b * w⁻¹ = b := by
      intro b hb
      have h1 := hxc b hb
      have h2 : a * w * b * (a * w)⁻¹ = a * (w * b * w⁻¹) * a⁻¹ := by group
      rw [h2] at h1
      have h3 : w * b * w⁻¹ = a⁻¹ * b * a := by
        calc w * b * w⁻¹ = a⁻¹ * (a * (w * b * w⁻¹) * a⁻¹) * a := by group
          _ = a⁻¹ * b * a := by rw [h1]
      rw [h3]
      calc a⁻¹ * b * a = a⁻¹ * (b * a) := mul_assoc _ _ _
        _ = a⁻¹ * (a * b) := by rw [hAcomm b hb a ha]
        _ = b := by group
    rw [hcent w hw hwc, mul_one]
    exact ha
  set P := A ⊔ Subgroup.zpowers ρ with hP
  have hAP : A ≤ P := le_sup_left
  have hPcard : Nat.card ↥P = 20 := by
    have hbij : Function.Bijective (fun x : A × Subgroup.zpowers ρ =>
        (⟨(x.1 : Q) * (x.2 : Q), Subgroup.mul_mem_sup x.1.2 x.2.2⟩ : ↥P)) := by
      constructor
      · rintro ⟨⟨a, ha⟩, ⟨w, hw⟩⟩ ⟨⟨a', ha'⟩, ⟨w', hw'⟩⟩ h
        have h1 : a * w = a' * w' := congrArg Subtype.val h
        have h2 : a'⁻¹ * a = w' * w⁻¹ := by
          calc a'⁻¹ * a = a'⁻¹ * (a * w) * w⁻¹ := by group
            _ = a'⁻¹ * (a' * w') * w⁻¹ := by rw [h1]
            _ = w' * w⁻¹ := by group
        have h3 : a'⁻¹ * a ∈ A ⊓ Subgroup.zpowers ρ :=
          ⟨A.mul_mem (A.inv_mem ha') ha, h2 ▸ (Subgroup.zpowers ρ).mul_mem hw' ((Subgroup.zpowers ρ).inv_mem hw)⟩
        rw [hAS, Subgroup.mem_bot] at h3
        have hae : a = a' := by
          calc a = a' * (a'⁻¹ * a) := by group
            _ = a' := by rw [h3, mul_one]
        have hwe : w = w' := by
          have : w' * w⁻¹ = 1 := h2 ▸ h3
          calc w = (w' * w⁻¹)⁻¹ * w' := by group
            _ = w' := by rw [this]; simp
        subst hae
        subst hwe
        rfl
      · rintro ⟨x, hx⟩
        obtain ⟨a, ha, w, hw, rfl⟩ := hPmem x hx
        exact ⟨(⟨a, ha⟩, ⟨w, hw⟩), rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, hA, Nat.card_zpowers, hρ4]
  have hbot : CFSG.Open.pCore 2 ↥P = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨a, ha, w, hw, hnaw⟩ := hPmem n.1 n.2
    have hnN : (⟨n.1, n.2⟩ : ↥P) ∈ CFSG.Open.pCore 2 ↥P := hn
    have hcn := centralizes_of_mem_pCore hp2 hAP hA n.2 hnN (hPconj n.1 n.2)
    have hnA : n.1 ∈ A := hcentP n.1 n.2 hcn
    have h1 : (⟨n.1, hAP hnA⟩ : ↥P) ∈ CFSG.Open.pCore 2 ↥P := hn
    obtain ⟨k, hk⟩ := (BorelTits.pCore_isPGroup (G := ↥P) 2) ⟨_, h1⟩
    have : (n.1 : Q) = 1 := eq_one_of_two_power hp2 hA hnA ⟨k, by
      simpa using congrArg (fun z : CFSG.Open.pCore 2 ↥P => ((z : ↥P) : Q)) hk⟩
    rw [Subgroup.mem_bot]
    exact Subtype.ext this
  obtain ⟨eSz⟩ := hFr ↥P hPcard ⟨A.subgroupOf P,
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mpr hPnorm,
    by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hA], fun x hx => by
      have hxA : (x : Q) ∈ A := hcentP x x.2 fun b hb => by
        have := hx ⟨b, hAP hb⟩ (by simpa [Subgroup.mem_subgroupOf] using hb)
        have h1 : (x : Q) * b = b * x := congrArg Subtype.val this
        calc (x : Q) * b * (x : Q)⁻¹ = b * x * (x : Q)⁻¹ := by rw [h1]
          _ = b := by group
      simpa [Subgroup.mem_subgroupOf] using hxA⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans eSz⟩

end Sz

end S152Y

end CFSG.Quasithin
