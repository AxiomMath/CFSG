module

public import CFSG.Quasithin.Vol2.Ch10SecB5EvPair

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.QuasithinUnique

variable {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F] {n : ℕ}
  {S : Subgroup Q}

omit [Finite Q] in
theorem eq_one_of_pow_three_of_isPGroup {P : Subgroup Q} (hP : IsPGroup 2 P) {x : Q}
    (hx : x ∈ P) (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf x ∣ Nat.gcd (2 ^ k) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h3)
  have h2 : Nat.gcd (2 ^ k) 3 = 1 :=
    Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem card_le_three (hF : Nat.card F = 2 ^ n) (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hS : IsSylowTwoOf S ⊤) {A : Subgroup Q} (hAN : A ≤ Subgroup.normalizer (S : Set Q))
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) : Nat.card A ≤ 3 := by
  by_cases hA : A = ⊥
  · rw [hA, Subgroup.card_bot]
    norm_num
  obtain ⟨⟨a, haA⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  have ha3 : orderOf a = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one (hA3 a haA)) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hle : A ≤ Subgroup.zpowers a := by
    intro b hb
    obtain ⟨i, u, huS, hbu⟩ :=
      exists_pow_mul_of_pow_three hF e hS (hAN haA) ha3 (hAN hb) (hA3 b hb)
    have huA : u ∈ A := by
      have : u = (a ^ i)⁻¹ * b := by rw [hbu]; group
      rw [this]
      exact A.mul_mem (A.inv_mem (A.pow_mem haA i)) hb
    have hu1 : u = 1 := eq_one_of_pow_three_of_isPGroup hS.2.1 huS (hA3 u huA)
    rw [hbu, hu1, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i
  calc Nat.card A ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le hle
    _ = 3 := by rw [Nat.card_zpowers, ha3]

theorem exists_commutator_eq (hF : Nat.card F = 2 ^ n)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hS : IsSylowTwoOf S ⊤) {a : Q}
    (ha : a ∈ Subgroup.normalizer (S : Set Q)) (ha3 : orderOf a = 3) {u : Q} (hu : u ∈ S) :
    ∃ w ∈ S, u = w * a * w⁻¹ * a⁻¹ := by
  have hmem : ∀ w ∈ S, w * a * w⁻¹ * a⁻¹ ∈ S := fun w hw => by
    have h1 : a * w⁻¹ * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp ha _).mp (S.inv_mem hw)
    have := S.mul_mem hw h1
    simpa [mul_assoc] using this
  let f : ↥S → ↥S := fun w => ⟨w * a * (w : Q)⁻¹ * a⁻¹, hmem w w.2⟩
  have hf : Function.Injective f := by
    intro w w' hww'
    have h1 : (w : Q) * a * (w : Q)⁻¹ * a⁻¹ = (w' : Q) * a * (w' : Q)⁻¹ * a⁻¹ :=
      congrArg Subtype.val hww'
    have hv : ((w' : Q)⁻¹ * w) ∈ S := S.mul_mem (S.inv_mem w'.2) w.2
    have h2 : a * ((w' : Q)⁻¹ * w) * a⁻¹ = (w' : Q)⁻¹ * w := by
      have h3 : (w : Q) * a * (w : Q)⁻¹ = (w' : Q) * a * (w' : Q)⁻¹ := by
        simpa using congrArg (· * a) h1
      calc a * ((w' : Q)⁻¹ * w) * a⁻¹
          = (w' : Q)⁻¹ * ((w' : Q) * a * (w' : Q)⁻¹) * w * a⁻¹ := by group
        _ = (w' : Q)⁻¹ * ((w : Q) * a * (w : Q)⁻¹) * w * a⁻¹ := by rw [h3]
        _ = (w' : Q)⁻¹ * w := by group
    have h4 := eq_one_of_conj_eq_of_mulEquiv hF e hS ha ha3 hv h2
    apply Subtype.ext
    have : (w : Q) = (w' : Q) * ((w' : Q)⁻¹ * w) := by group
    rw [this, h4, mul_one]
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hf) ⟨u, hu⟩
  exact ⟨w, w.2, (congrArg Subtype.val hw).symm⟩

omit [Finite Q] in
theorem proj_mem_normalizer [Finite Q] {G : Type} [Group G] {Kc S : Subgroup G} (π : ↥Kc →* Q)
    {k : G} (hkK : k ∈ Kc) (hkN : k ∈ Subgroup.normalizer (S : Set G)) :
    π ⟨k, hkK⟩ ∈ Subgroup.normalizer (((S.subgroupOf Kc).map π : Subgroup Q) : Set Q) := by
  refine mem_normalizer_of_conj_mem fun u hu => ?_
  obtain ⟨s, hs, rfl⟩ := hu
  have hm : k * (s : G) * k⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hkN _).mp hs
  refine ⟨⟨k * s * k⁻¹, Kc.mul_mem (Kc.mul_mem hkK s.2) (Kc.inv_mem hkK)⟩, hm, ?_⟩
  have e : (⟨k * s * k⁻¹, Kc.mul_mem (Kc.mul_mem hkK s.2) (Kc.inv_mem hkK)⟩ : ↥Kc) =
      ⟨k, hkK⟩ * s * (⟨k, hkK⟩ : ↥Kc)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]

end CFSG.Quasithin.Vol2.Ch10.SecB
