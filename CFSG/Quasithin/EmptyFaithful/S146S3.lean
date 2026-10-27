module

public import CFSG.Quasithin.EmptyFaithful.S1421L2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def psiOf {X : Subgroup G} (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    ↥X →* Equiv.Perm (Fin 3) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X))

omit [Finite G] in
theorem psiOf_surjective {X : Subgroup G} (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    Function.Surjective (psiOf e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem psiOf_eq_one_iff {X : Subgroup G} (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) (x : ↥X) :
    psiOf e x = 1 ↔ (x : G) ∈ pCoreOf 2 X := by
  constructor
  · intro h
    have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X) x = 1 := by
      have : e (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X) x) = e 1 := by simpa [psiOf] using h
      exact e.injective this
    exact ⟨x, (QuotientGroup.eq_one_iff x).mp h1, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X) y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    show e (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X) y) = 1
    rw [h1, map_one]

omit [Finite G] in
theorem sign_eq_one_of_odd_orderOf' {g : Equiv.Perm (Fin 3)} (h : Odd (orderOf g)) :
    Equiv.Perm.sign g = 1 := by
  have h1 : (Equiv.Perm.sign g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h2 | h2
  · exact h2
  · rw [h2, Odd.neg_one_pow h] at h1; exact absurd h1 (by decide)

omit [Finite G] in
theorem sign_psiOf_eq_one_of_oTwoUpper {X : Subgroup G} (e : OTwoQuot X ≃* Equiv.Perm (Fin 3))
    {B : Subgroup G} (hBX : B ≤ X) (hB : oTwoUpper B = B) {x : G} (hx : x ∈ B) :
    Equiv.Perm.sign (psiOf e ⟨x, hBX hx⟩) = 1 := by
  have hP : ∀ x ∈ oTwoUpper B, ∃ hx : x ∈ X, Equiv.Perm.sign (psiOf e ⟨x, hx⟩) = 1 := by
    intro x hx'
    induction hx' using Subgroup.closure_induction with
    | mem y hy =>
      refine ⟨hBX hy.1, sign_eq_one_of_odd_orderOf' ?_⟩
      have hdvd : orderOf (psiOf e ⟨y, hBX hy.1⟩) ∣ orderOf (⟨y, hBX hy.1⟩ : ↥X) :=
        orderOf_map_dvd (psiOf e) _
      rw [Subgroup.orderOf_mk] at hdvd
      exact Odd.of_dvd_nat hy.2 hdvd
    | one =>
      refine ⟨X.one_mem, ?_⟩
      have : (⟨1, X.one_mem⟩ : ↥X) = 1 := rfl
      rw [this, map_one, map_one]
    | mul x y _ _ ihx ihy =>
      obtain ⟨hx, sx⟩ := ihx
      obtain ⟨hy, sy⟩ := ihy
      refine ⟨X.mul_mem hx hy, ?_⟩
      have : (⟨x * y, X.mul_mem hx hy⟩ : ↥X) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul, sx, sy, mul_one]
    | inv x _ ihx =>
      obtain ⟨hx, sx⟩ := ihx
      refine ⟨X.inv_mem hx, ?_⟩
      have : (⟨x⁻¹, X.inv_mem hx⟩ : ↥X) = (⟨x, hx⟩ : ↥X)⁻¹ := rfl
      rw [this, map_inv, map_inv, sx, inv_one]
  obtain ⟨hx2, hs⟩ := hP x (by rw [hB]; exact hx)
  exact hs

omit [Finite G] in
theorem perm3_alt_pow' : ∀ g h : Equiv.Perm (Fin 3), Equiv.Perm.sign g = 1 →
    Equiv.Perm.sign h = 1 → h ≠ 1 → ∃ k : Fin 3, h ^ (k : ℕ) = g := by decide

omit [Finite G] in
theorem perm3_three_cycle_not_two_group' :
    ∃ c : Equiv.Perm (Fin 3), ∀ k : ℕ, c ^ 2 ^ k ≠ 1 := by
  refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, fun k hk => ?_⟩
  have h3 : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) ^ 3 = 1 := by decide
  have hne : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) ≠ 1 := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord := orderOf_eq_prime h3 hne
  have hdvd : orderOf (Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hk
  rw [hord] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem nonempty_quot_perm3_of_surjective {X : Type*} [Group X] [Finite X]
    (ψ : X →* Equiv.Perm (Fin 3)) (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) :
    Nonempty (X ⧸ CFSG.Open.pCore 2 X ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : CFSG.Open.pCore 2 X = ψ.ker := by
    apply le_antisymm
    · have hN : ((CFSG.Open.pCore 2 X).map ψ).Normal :=
        Subgroup.Normal.map (CFSG.LieType.BorelTits.pCore_normal 2) ψ hψ
      have hbot : (CFSG.Open.pCore 2 X).map ψ = ⊥ :=
        S1421.perm3_no_normal_two _ ((CFSG.LieType.BorelTits.pCore_isPGroup 2).map ψ)
      exact (Subgroup.map_eq_bot_iff _).mp hbot
    · exact CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker ψ) hker
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hO).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩


omit [Finite G] in
theorem false_of_le_ker_sup {X K Tb : Subgroup G} (e : OTwoQuot X ≃* Equiv.Perm (Fin 3))
    (hKX : K ≤ X) (hTbX : Tb ≤ X) (hTb : IsPGroup 2 Tb)
    (hK : ∀ (k : G) (hk : k ∈ K), psiOf e ⟨k, hKX hk⟩ = 1) (hX : X ≤ K ⊔ Tb) : False := by
  obtain ⟨c, hc⟩ := perm3_three_cycle_not_two_group'
  obtain ⟨x, hx⟩ := psiOf_surjective e c
  let φ : Subgroup (Equiv.Perm (Fin 3)) := (Tb.subgroupOf X).map (psiOf e)
  let R : Subgroup G := (φ.comap (psiOf e)).map X.subtype
  have hKR : K ≤ R := fun a ha => ⟨⟨a, hKX ha⟩, by
    show psiOf e ⟨a, hKX ha⟩ ∈ φ
    rw [hK a ha]; exact φ.one_mem, rfl⟩
  have hTR : Tb ≤ R := fun t ht => ⟨⟨t, hTbX ht⟩, by
    show psiOf e ⟨t, hTbX ht⟩ ∈ φ
    exact ⟨⟨t, hTbX ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩, rfl⟩
  have hXR : X ≤ R := hX.trans (sup_le hKR hTR)
  obtain ⟨x', hx'φ, hx'x⟩ := hXR x.2
  have hx'eq : x' = x := Subtype.ext hx'x
  subst hx'eq
  have hcφ : c ∈ φ := by rw [← hx]; exact hx'φ
  obtain ⟨t, ht, htc⟩ := hcφ
  have hTbp : IsPGroup 2 (Tb.subgroupOf X) :=
    hTb.of_equiv (Subgroup.subgroupOfEquivOfLe hTbX).symm
  obtain ⟨k, hk⟩ := hTbp ⟨t, ht⟩
  apply hc k
  have : psiOf e ((⟨t, ht⟩ : ↥(Tb.subgroupOf X)) ^ 2 ^ k : ↥(Tb.subgroupOf X)) = c ^ 2 ^ k := by
    rw [← htc]; simp [map_pow]
  rw [← this, hk]; simp

theorem nonempty_oTwoQuot_of_exists {X Y : Subgroup G} (e : OTwoQuot X ≃* Equiv.Perm (Fin 3))
    (hYX : Y ≤ X) {a b : G} (ha : a ∈ Y) (hb : b ∈ Y)
    (hsa : Equiv.Perm.sign (psiOf e ⟨a, hYX ha⟩) = 1) (hna : psiOf e ⟨a, hYX ha⟩ ≠ 1)
    (hsb : Equiv.Perm.sign (psiOf e ⟨b, hYX hb⟩) ≠ 1) :
    Nonempty (OTwoQuot Y ≃* Equiv.Perm (Fin 3)) := by
  let ψ : ↥Y →* Equiv.Perm (Fin 3) := (psiOf e).comp (Subgroup.inclusion hYX)
  have hψa : ψ ⟨a, ha⟩ = psiOf e ⟨a, hYX ha⟩ := rfl
  have hψb : ψ ⟨b, hb⟩ = psiOf e ⟨b, hYX hb⟩ := rfl
  have hsurj : Function.Surjective ψ := by
    intro g
    by_cases hg : Equiv.Perm.sign g = 1
    · obtain ⟨k, hk⟩ := perm3_alt_pow' g (psiOf e ⟨a, hYX ha⟩) hg hsa hna
      refine ⟨(⟨a, ha⟩ : ↥Y) ^ (k : ℕ), ?_⟩
      rw [map_pow, hψa, hk]
    · have hsg : Equiv.Perm.sign (g * (psiOf e ⟨b, hYX hb⟩)⁻¹) = 1 := by
        rw [map_mul, map_inv]
        rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h1 | h1
        · exact absurd h1 hg
        rcases Int.units_eq_one_or (Equiv.Perm.sign (psiOf e ⟨b, hYX hb⟩)) with h2 | h2
        · exact absurd h2 hsb
        rw [h1, h2]; decide
      obtain ⟨k, hk⟩ := perm3_alt_pow' (g * (psiOf e ⟨b, hYX hb⟩)⁻¹) (psiOf e ⟨a, hYX ha⟩)
        hsg hsa hna
      refine ⟨(⟨a, ha⟩ : ↥Y) ^ (k : ℕ) * ⟨b, hb⟩, ?_⟩
      rw [map_mul, map_pow, hψa, hψb, hk]
      group
  have hker : IsPGroup 2 ψ.ker := by
    intro y
    have hy : ψ (y : ↥Y) = 1 := y.2
    have hmem : ((y : ↥Y) : G) ∈ pCoreOf 2 X := (psiOf_eq_one_iff e ⟨_, hYX (y : ↥Y).2⟩).mp hy
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨_, hmem⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  exact nonempty_quot_perm3_of_surjective ψ hsurj hker


omit [Finite G] in
theorem eq_or_eq_of_relIndex_prime {A B C : Subgroup G} {p : ℕ} (hp : p.Prime) (hAB : A ≤ B)
    (hBC : B ≤ C) (h : A.relIndex C = p) : B = A ∨ B = C := by
  have hmul := Subgroup.relIndex_mul_relIndex A B C hAB hBC
  rw [h] at hmul
  have hdvd : A.relIndex B ∣ p := ⟨B.relIndex C, hmul.symm⟩
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hAB)
  · rw [h1] at hmul
    have : B.relIndex C = 1 := by
      have hp0 : 0 < p := hp.pos
      exact Nat.eq_of_mul_eq_mul_left hp0 (by rw [hmul, mul_one])
    exact Or.inr (le_antisymm hBC (Subgroup.relIndex_eq_one.mp this))

omit [Finite G] in
theorem isSylowTwoOf_of_le_of_le' {P A C : Subgroup G} (hP : IsSylowTwoOf P A) (hPC : P ≤ C)
    (hCA : C ≤ A) : IsSylowTwoOf P C := by
  refine ⟨hPC, hP.2.1, fun h2 => hP.2.2 ?_⟩
  have hmul := Subgroup.relIndex_mul_relIndex P C A hPC hCA
  show 2 ∣ P.relIndex A
  rw [← hmul]
  exact Dvd.dvd.mul_right h2 _


theorem relIndex_eq_three_of_isSylowTwoOf {X S : Subgroup G}
    (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) (hS : IsSylowTwoOf S X) : S.relIndex X = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) 2).exists_card_eq
  have hcardQ : Nat.card (OTwoQuot X) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hX : Nat.card ↥X = 3 * 2 ^ (k + 1) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥X)
    rw [this]
    change Nat.card (OTwoQuot X) * Nat.card ↥(CFSG.Open.pCore 2 ↥X) = _
    rw [hcardQ, hk]
    ring
  obtain ⟨m, hm⟩ := hS.2.1.exists_card_eq
  have hmul : S.relIndex X * Nat.card ↥S = Nat.card ↥X := by
    have := Subgroup.relIndex_mul_card S X
    rwa [inf_of_le_left hS.1] at this
  have hcop : Nat.Coprime (S.relIndex X) (2 ^ (k + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hS.2.2).symm
  have hdvd : S.relIndex X ∣ 3 * 2 ^ (k + 1) := ⟨Nat.card ↥S, by rw [← hX, ← hmul]⟩
  have h3 : S.relIndex X ∣ 3 := hcop.dvd_of_dvd_mul_right hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
  · exfalso
    rw [h1, hX, hm, one_mul] at hmul
    have : 3 ∣ 2 ^ m := ⟨2 ^ (k + 1), by rw [hmul]⟩
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega
  · exact h1

end CFSG.Quasithin
