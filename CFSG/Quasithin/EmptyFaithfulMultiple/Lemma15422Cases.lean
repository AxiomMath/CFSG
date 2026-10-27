module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15422Config

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6

namespace L15422

section Elementary

variable {D : Type*} [Group D]

theorem exists_ne_of_card_eq_four {E : Subgroup D} (hE : Nat.card E = 4) :
    ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  by_contra h
  push Not at h
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra h'
    push Not at h'
    have hb : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h'
    rw [hb, Subgroup.card_bot] at hE
    omega
  have hsub : (E : Set D) ⊆ {1, a} := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (h x hx a ha hx1 ha1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, a} : Set D).ncard ≤ 2 :=
    (Set.ncard_insert_le 1 {a}).trans (by rw [Set.ncard_singleton])
  have h3 : (E : Set D).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hE
  omega

theorem pow_three_eq_one_of_odd {M : Type*} [Group M] {k : ℕ} (hM : Nat.card M = 2 ^ k * 3)
    {g : M} (hg : Odd (orderOf g)) : g ^ 3 = 1 := by
  have : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; positivity)
  have hdvd : orderOf g ∣ 2 ^ k * 3 := hM ▸ orderOf_dvd_natCard g
  have hcop : Nat.Coprime (orderOf g) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hg)
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hdvd)

theorem eq_one_of_mem_centralizer_of_pCore_eq_bot [Finite D] {H₁ H₂ : Subgroup D}
    (hgen : H₁ ⊔ H₂ = ⊤) (hQ : Open.pCore 2 D = ⊥) {z : D}
    (h₁ : z ∈ Subgroup.centralizer (H₁ : Set D)) (h₂ : z ∈ Subgroup.centralizer (H₂ : Set D))
    (hz : z ^ 2 = 1) : z = 1 := by
  have hc : z ∈ Subgroup.center D := by
    have hle : H₁ ⊔ H₂ ≤ Subgroup.centralizer ({z} : Set D) := by
      refine sup_le (fun h hh => ?_) (fun h hh => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.mp h₁) h hh)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.mp h₂) h hh)
    rw [hgen] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g)))
  have hn : (Subgroup.zpowers z).Normal :=
    ⟨fun x hx g => by
      have hgz : g * x * g⁻¹ = x := by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        have hcz : g * z ^ n * g⁻¹ = z ^ n := by
          have := Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hc n) g
          rw [this, mul_assoc, mul_inv_cancel, mul_one]
        exact hcz
      rw [hgz]
      exact hx⟩
  have hp : IsPGroup 2 (Subgroup.zpowers z) := by
    have hd : orderOf z ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by simpa using hz)
    obtain ⟨m, -, hm2⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm2])
  have hle : Subgroup.zpowers z ≤ Open.pCore 2 D := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.le_pCore 2 hn hp
  rw [hQ, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  exact hle

end Elementary

section Center

variable {D : Type*} [Group D]

theorem false_of_mulEquiv_center {T E : Subgroup D} {M : Type*} [Group M] (e : ↥T ≃* M)
    (hM : ∀ a b : M, (∀ g, a * g = g * a) → (∀ g, b * g = g * b) → a ^ 2 = 1 → b ^ 2 = 1 →
      a = 1 ∨ b = 1 ∨ a = b)
    (hET : E ≤ T) (hEc : E ≤ Subgroup.centralizer (T : Set D)) (hE : Nat.card E = 4)
    (hE2 : ∀ z ∈ E, z ^ 2 = 1) : False := by
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_ne_of_card_eq_four hE
  have hcen : ∀ x (hx : x ∈ E) (g : M), e ⟨x, hET hx⟩ * g = g * e ⟨x, hET hx⟩ := by
    intro x hx g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp (hEc hx)) y y.2).symm
  have hsq : ∀ x (hx : x ∈ E), (e ⟨x, hET hx⟩) ^ 2 = 1 := by
    intro x hx
    rw [← map_pow]
    have : (⟨x, hET hx⟩ : ↥T) ^ 2 = 1 := Subtype.ext (by simpa using hE2 x hx)
    rw [this, map_one]
  rcases hM _ _ (hcen a ha) (hcen b hb) (hsq a ha) (hsq b hb) with h | h | h
  · exact ha1 (by simpa using congrArg Subtype.val (e.injective (h.trans e.map_one.symm)))
  · exact hb1 (by simpa using congrArg Subtype.val (e.injective (h.trans e.map_one.symm)))
  · exact hab (by simpa using congrArg Subtype.val (e.injective h))

theorem dihedral_four_center : ∀ a b : DihedralGroup 4, (∀ g, a * g = g * a) →
    (∀ g, b * g = g * b) → a ^ 2 = 1 → b ^ 2 = 1 → a = 1 ∨ b = 1 ∨ a = b := by
  decide +kernel

private instance instFintypeWreathFourTwo :
    Fintype (Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)) :=
  Fintype.ofEquiv _ (RegularWreathProduct.equivProd _ _).symm

private instance instDecidableEqWreathFourTwo :
    DecidableEq (Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)) :=
  Equiv.decidableEq (RegularWreathProduct.equivProd _ _)

theorem wreath_four_two_center :
    ∀ a b : Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2), (∀ g, a * g = g * a) →
      (∀ g, b * g = g * b) → a ^ 2 = 1 → b ^ 2 = 1 → a = 1 ∨ b = 1 ∨ a = b := by
  decide

end Center

section Odd

variable {D : Type*} [Group D]

theorem eq_one_of_mem_oTwoUpper {H : Subgroup D} {M : Type*} [Group M] (e : ↥H ≃* M) {k : ℕ}
    (hcard : Nat.card M = 2 ^ k * 3) (hM : ∀ g h : M, g ^ 3 = 1 → h ^ 3 = 1 → (g * h) ^ 3 = 1)
    {v : D} (hv : v ∈ oTwoUpper H) (hv2 : v ^ 2 = 1) : v = 1 := by
  let S : Subgroup M :=
    { carrier := {g | g ^ 3 = 1}
      mul_mem' := fun ha hb => hM _ _ ha hb
      one_mem' := one_pow 3
      inv_mem' := fun {g} hg => by
        change g⁻¹ ^ 3 = 1
        change g ^ 3 = 1 at hg
        rw [inv_pow, hg, inv_one] }
  have hle : oTwoUpper H ≤ (S.comap e.toMonoidHom).map H.subtype := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    change (e ⟨x, hx.1⟩) ^ 3 = 1
    refine pow_three_eq_one_of_odd hcard ?_
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hx.2
  obtain ⟨⟨w, hwH⟩, hw, rfl⟩ := hle hv
  change (e ⟨w, hwH⟩) ^ 3 = 1 at hw
  have h2 : (e ⟨w, hwH⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨w, hwH⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by simpa using hv2)
    rw [this, map_one]
  have h1 : e ⟨w, hwH⟩ = 1 := by
    calc e ⟨w, hwH⟩ = (e ⟨w, hwH⟩) ^ 3 * ((e ⟨w, hwH⟩) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hw, h2]; group
  have := congrArg Subtype.val (e.injective (h1.trans e.map_one.symm))
  simpa using this

theorem dihedral_six_cube : ∀ g h : DihedralGroup 6, g ^ 3 = 1 → h ^ 3 = 1 → (g * h) ^ 3 = 1 := by
  decide +kernel

theorem perm_three_dihedral_four_cube : ∀ g h : Equiv.Perm (Fin 3) × DihedralGroup 4,
    g ^ 3 = 1 → h ^ 3 = 1 → (g * h) ^ 3 = 1 := by
  decide +kernel

end Odd

section Quaternion

@[expose] def SmallCenter (X : Type*) [Group X] : Prop :=
  ∀ a b : X, (∀ g, a * g = g * a) → (∀ g, b * g = g * b) → a ≠ 1 → b ≠ 1 → a = b

theorem smallCenter_quaternion : SmallCenter (QuaternionGroup 2) := by
  unfold SmallCenter
  decide +kernel

theorem SmallCenter.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : SmallCenter Y) : SmallCenter X := by
  intro a b ha hb ha1 hb1
  apply e.injective
  refine h _ _ (fun g => ?_) (fun g => ?_) (by simpa using ha1) (by simpa using hb1)
  · obtain ⟨x, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, ha x]
  · obtain ⟨x, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hb x]

theorem smallCenter_of_isCentralProduct₂ {R A B : Type*} [Group R] [Group A] [Group B]
    (hA : SmallCenter A) (hB : SmallCenter B) (h : IsCentralProduct₂ R A B) : SmallCenter R := by
  obtain ⟨A', B', hsup, hcomm, ⟨eA⟩, ⟨eB⟩, hcard⟩ := h
  have hA' : SmallCenter A' := hA.of_mulEquiv eA
  have hB' : SmallCenter B' := hB.of_mulEquiv eB
  have : Finite ↥(A' ⊓ B') := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨⟨ε, hε⟩, hε1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp (by rw [hcard]; norm_num))
  have hε1' : ε ≠ 1 := fun h => hε1 (Subtype.ext h)
  have hε2 : ε * ε = 1 := by
    have h2 := pow_card_eq_one' (G := ↥(A' ⊓ B')) (x := ⟨ε, hε⟩)
    rw [hcard] at h2
    simpa [sq] using congrArg Subtype.val h2
  have hBN : B' ≤ Subgroup.normalizer (A' : Set R) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have e1 : ∀ a ∈ A', b * a * b⁻¹ = a := fun a ha => by
      rw [(hcomm a ha b hb).symm]
      group
    constructor
    · intro ha
      rw [e1 a ha]
      exact ha
    · intro ha
      have hc := hcomm _ ha b hb
      have ha' : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * ((b * a * b⁻¹) * b) := by group
          _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [hc]
          _ = b * a * b⁻¹ := by group
      rw [ha']
      exact ha
  have hmul : ∀ c : R, ∃ a ∈ A', ∃ b ∈ B', c = a * b := by
    intro c
    have hc : c ∈ ((A' ⊔ B' : Subgroup R) : Set R) := by rw [hsup]; trivial
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A' B' hBN] at hc
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hc
    exact ⟨a, ha, b, hb, rfl⟩
  have key : ∀ c : R, (∀ g, c * g = g * c) → c = 1 ∨ c = ε := by
    intro c hc
    obtain ⟨a, ha, b, hb, rfl⟩ := hmul c
    have haz : ∀ x ∈ A', a * x = x * a := by
      intro x hx
      have h1 := hc x
      have h2 := hcomm x hx b hb
      refine mul_right_cancel (b := b) ?_
      calc a * x * b = a * (x * b) := by group
        _ = a * (b * x) := by rw [h2]
        _ = a * b * x := by group
        _ = x * (a * b) := h1
        _ = x * a * b := by group
    have hbz : ∀ y ∈ B', b * y = y * b := by
      intro y hy
      have h1 := hc y
      have h2 := hcomm a ha y hy
      refine mul_left_cancel (a := a) ?_
      calc a * (b * y) = a * b * y := by group
        _ = y * (a * b) := h1
        _ = y * a * b := by group
        _ = a * y * b := by rw [h2]
        _ = a * (y * b) := by group
    have ha' : a = 1 ∨ a = ε := by
      by_cases ha1 : a = 1
      · exact Or.inl ha1
      · right
        have := hA' ⟨a, ha⟩ ⟨ε, hε.1⟩ (fun g => Subtype.ext (haz g g.2))
          (fun g => Subtype.ext (hcomm g g.2 ε hε.2).symm)
          (fun h => ha1 (congrArg Subtype.val h)) (fun h => hε1' (congrArg Subtype.val h))
        exact congrArg Subtype.val this
    have hb' : b = 1 ∨ b = ε := by
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · right
        have := hB' ⟨b, hb⟩ ⟨ε, hε.2⟩ (fun g => Subtype.ext (hbz g g.2))
          (fun g => Subtype.ext (hcomm ε hε.1 g g.2))
          (fun h => hb1 (congrArg Subtype.val h)) (fun h => hε1' (congrArg Subtype.val h))
        exact congrArg Subtype.val this
    rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2 <;> rw [h1, h2]
    · exact Or.inl (mul_one 1)
    · exact Or.inr (one_mul ε)
    · exact Or.inr (mul_one ε)
    · exact Or.inl hε2
  intro c d hc hd hc1 hd1
  rcases key c hc with h | h
  · exact absurd h hc1
  rcases key d hd with h' | h'
  · exact absurd h' hd1
  rw [h, h']

theorem perm_three_commutator : ∀ d : Equiv.Perm (Fin 3), (∃ g, d * g ≠ g * d) →
    ∃ e, (e * d * e⁻¹ * d⁻¹) ^ 3 = 1 ∧ e * d * e⁻¹ * d⁻¹ ≠ 1 := by
  decide +kernel

theorem dihedral_six_commutator : ∀ d : DihedralGroup 6, (∃ g, d * g ≠ g * d) →
    ∃ e, (e * d * e⁻¹ * d⁻¹) ^ 3 = 1 ∧ e * d * e⁻¹ * d⁻¹ ≠ 1 := by
  decide +kernel

theorem perm_three_cube : ∀ s c : Equiv.Perm (Fin 3), s ^ 3 = 1 → c ^ 3 = 1 → c ≠ 1 →
    s = 1 ∨ s = c ∨ s = c * c := by
  decide +kernel

theorem dihedral_six_cube_powers : ∀ s c : DihedralGroup 6, s ^ 3 = 1 → c ^ 3 = 1 → c ≠ 1 →
    s = 1 ∨ s = c ∨ s = c * c := by
  decide +kernel

variable {P : Type*} [Group P] [Finite P]

omit [Finite P] in
private theorem conj_mem_centralizer_of_normal {R : Subgroup P} [R.Normal] {g : P}
    (hg : g ∈ Subgroup.centralizer (R : Set P)) (y : P) :
    y * g * y⁻¹ ∈ Subgroup.centralizer (R : Set P) := by
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro r hr
  have hr' : y⁻¹ * r * y ∈ R := by simpa using (inferInstance : R.Normal).conj_mem r hr y⁻¹
  have h1 := hg _ hr'
  calc r * (y * g * y⁻¹) = y * ((y⁻¹ * r * y) * g) * y⁻¹ := by group
    _ = y * (g * (y⁻¹ * r * y)) * y⁻¹ := by rw [h1]
    _ = y * g * y⁻¹ * r := by group

omit [Finite P] in
private theorem mem_center_of_smallCenter {R : Subgroup P} [hRn : R.Normal] (hRc : SmallCenter R)
    {c : P} (hc : c ∈ R) (hcR : ∀ r ∈ R, r * c = c * r) : c ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro y
  by_cases hc1 : c = 1
  · rw [hc1, mul_one, one_mul]
  have hy : y * c * y⁻¹ ∈ R := hRn.conj_mem c hc y
  have hyR : ∀ r ∈ R, r * (y * c * y⁻¹) = (y * c * y⁻¹) * r := by
    intro r hr
    have hr' : y⁻¹ * r * y ∈ R := by simpa using hRn.conj_mem r hr y⁻¹
    have h1 := hcR _ hr'
    calc r * (y * c * y⁻¹) = y * ((y⁻¹ * r * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * r * y)) * y⁻¹ := by rw [h1]
      _ = y * c * y⁻¹ * r := by group
  have hne : y * c * y⁻¹ ≠ 1 := by
    intro h
    apply hc1
    calc c = y⁻¹ * (y * c * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  have heq := hRc ⟨y * c * y⁻¹, hy⟩ ⟨c, hc⟩
    (fun g => Subtype.ext (hyR g g.2).symm) (fun g => Subtype.ext (hcR g g.2).symm)
    (fun h => hne (congrArg Subtype.val h)) (fun h => hc1 (congrArg Subtype.val h))
  have heq' : y * c * y⁻¹ = c := congrArg Subtype.val heq
  calc y * c = y * c * y⁻¹ * y := by group
    _ = c * y := by rw [heq']

theorem le_center_of_quotient_smallCenter {T R E : Subgroup P} {A : Type*} [Group A]
    {φ : P →* A} (hφ : Function.Surjective φ) (hker : φ.ker = R) (hR2 : IsPGroup 2 R)
    (hRc : SmallCenter R) (hT : IsPGroup 2 T) (hTi : T.index = 3)
    (hA1 : ∀ d : A, (∃ g, d * g ≠ g * d) →
      ∃ e, (e * d * e⁻¹ * d⁻¹) ^ 3 = 1 ∧ e * d * e⁻¹ * d⁻¹ ≠ 1)
    (hA2 : ∀ s c : A, s ^ 3 = 1 → c ^ 3 = 1 → c ≠ 1 → s = 1 ∨ s = c ∨ s = c * c)
    (hE : E ≤ Subgroup.centralizer (T : Set P))
    (hv : ∃ v ∈ E, v ≠ 1 ∧ v ^ 2 = 1 ∧ v ∈ oTwoUpper (⊤ : Subgroup P)) :
    E ≤ Subgroup.center P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRn : R.Normal := hker ▸ φ.normal_ker
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
  have hP : Nat.card P = 2 ^ n * 3 := by rw [← T.card_mul_index, hn, hTi]
  have hodd : ∀ h : P, Odd (orderOf h) → h ^ 3 = 1 := fun h hh => pow_three_eq_one_of_odd hP hh
  have hRT : R ≤ T := by
    have hTs : ¬ 2 ∣ T.index := by rw [hTi]; decide
    exact IsPGroup.le_sylow_of_normal hR2 (hT.toSylow hTs)
  have hER : E ≤ Subgroup.centralizer (R : Set P) :=
    hE.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRT))
  have hR3 : ∀ r ∈ R, r ^ 3 = 1 → r = 1 := by
    intro r hr hr3
    obtain ⟨m, hm⟩ := hR2 ⟨r, hr⟩
    have hm' : r ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h1 : orderOf r ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
    have h2 : orderOf r ∣ 3 := orderOf_dvd_of_pow_eq_one hr3
    have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  intro w hw
  have hwR : w ∈ Subgroup.centralizer (R : Set P) := hER hw
  by_cases hwr : w ∈ R
  · exact mem_center_of_smallCenter hRc hwr fun r hr =>
      (Subgroup.mem_centralizer_iff.mp hwR) r hr
  by_cases hcen : ∀ g : A, φ w * g = g * φ w
  ·
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := P) 3
      (by rw [hP]; exact Dvd.intro_left _ rfl)
    have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
    obtain ⟨c, hcdef⟩ : ∃ c, c = y * w * y⁻¹ * w⁻¹ := ⟨_, rfl⟩
    have hcR : c ∈ R := by
      rw [← hker, MonoidHom.mem_ker, hcdef]
      simp only [map_mul, map_inv]
      rw [← hcen (φ y)]
      group
    have hcC : c ∈ Subgroup.centralizer (R : Set P) := hcdef ▸
      Subgroup.mul_mem _ (conj_mem_centralizer_of_normal hwR y) (Subgroup.inv_mem _ hwR)
    have hcZ : c ∈ Subgroup.center P := mem_center_of_smallCenter hRc hcR fun r hr =>
      (Subgroup.mem_centralizer_iff.mp hcC) r hr
    have hc2 : c ^ 2 = 1 := by
      by_contra hc2
      have hc1 : c ≠ 1 := fun h => hc2 (by rw [h, one_pow])
      have hcZR : ∀ r ∈ R, r * c = c * r := fun r hr => (Subgroup.mem_centralizer_iff.mp hcC) r hr
      have hc2R : ∀ r ∈ R, r * c ^ 2 = c ^ 2 * r := fun r hr => by
        calc r * c ^ 2 = (r * c) * c := by rw [sq, mul_assoc]
          _ = (c * r) * c := by rw [hcZR r hr]
          _ = c * (r * c) := by group
          _ = c * (c * r) := by rw [hcZR r hr]
          _ = c ^ 2 * r := by rw [sq, mul_assoc]
      have := hRc ⟨c ^ 2, R.pow_mem hcR 2⟩ ⟨c, hcR⟩ (fun g => Subtype.ext (hc2R g g.2).symm)
        (fun g => Subtype.ext (hcZR g g.2).symm) (fun h => hc2 (congrArg Subtype.val h))
        (fun h => hc1 (congrArg Subtype.val h))
      have h' : c ^ 2 = c := congrArg Subtype.val this
      apply hc1
      calc c = c ^ 2 * c⁻¹ := by group
        _ = 1 := by rw [h']; group
    have hconj : y * w * y⁻¹ = c * w := by rw [hcdef]; group
    have hcomm : ∀ g : P, c * g = g * c := fun g => (Subgroup.mem_center_iff.mp hcZ g).symm
    have hpow : ∀ k : ℕ, y ^ k * w * (y ^ k)⁻¹ = c ^ k * w := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc y ^ (k + 1) * w * (y ^ (k + 1))⁻¹ = y * (y ^ k * w * (y ^ k)⁻¹) * y⁻¹ := by group
          _ = y * (c ^ k * w) * y⁻¹ := by rw [ih]
          _ = c ^ k * (y * w * y⁻¹) := by
            have : y * c ^ k = c ^ k * y := (Commute.pow_left (hcomm y) k).eq.symm
            calc y * (c ^ k * w) * y⁻¹ = (y * c ^ k) * w * y⁻¹ := by group
              _ = (c ^ k * y) * w * y⁻¹ := by rw [this]
              _ = c ^ k * (y * w * y⁻¹) := by group
          _ = c ^ (k + 1) * w := by rw [hconj, pow_succ]; group
    have h3 := hpow 3
    rw [hy3, show c ^ 3 = c * c ^ 2 by group, hc2] at h3
    have hc1 : c = 1 := by
      have : w = c * w := by simpa using h3
      calc c = c * w * w⁻¹ := by group
        _ = 1 := by rw [← this]; group
    have hyw : y * w = w * y := by
      have : y * w * y⁻¹ = w := by rw [hconj, hc1, one_mul]
      calc y * w = y * w * y⁻¹ * y := by group
        _ = w * y := by rw [this]
    have hyT : y ∉ T := by
      intro hyT
      obtain ⟨m, hm⟩ := hT ⟨y, hyT⟩
      have hm' : y ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have h1 : orderOf y ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
      rw [hy] at h1
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h1)
      omega
    have htop : T ⊔ Subgroup.zpowers y = ⊤ := by
      have hlt : T < T ⊔ Subgroup.zpowers y :=
        lt_of_le_of_ne le_sup_left fun h =>
          hyT (h ▸ (le_sup_right : Subgroup.zpowers y ≤ _) (Subgroup.mem_zpowers y))
      have hmul := Subgroup.relIndex_mul_index (le_sup_left : T ≤ T ⊔ Subgroup.zpowers y)
      rw [hTi] at hmul
      have hne : T.relIndex (T ⊔ Subgroup.zpowers y) ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        exact fun h => (lt_irrefl _ (lt_of_lt_of_le hlt h))
      have h3 : (T ⊔ Subgroup.zpowers y).index ∣ 3 := Dvd.intro_left _ hmul
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
      · exact Subgroup.index_eq_one.mp h
      · rw [h] at hmul
        omega
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : T ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({w} : Set P) := by
      refine sup_le (fun t ht => ?_) ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (hE hw)) t ht
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hyw
    rw [htop] at hle
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  ·
    exfalso
    push Not at hcen
    obtain ⟨e, he3, he1⟩ := hA1 (φ w) hcen
    obtain ⟨e', rfl⟩ := hφ e
    obtain ⟨g, hgdef⟩ : ∃ g, g = e' * w * e'⁻¹ * w⁻¹ := ⟨_, rfl⟩
    have hgC : g ∈ Subgroup.centralizer (R : Set P) := hgdef ▸
      Subgroup.mul_mem _ (conj_mem_centralizer_of_normal hwR e') (Subgroup.inv_mem _ hwR)
    have hφg : φ g = φ e' * φ w * (φ e')⁻¹ * (φ w)⁻¹ := by
      rw [hgdef]
      simp only [map_mul, map_inv]
    obtain ⟨y, hydef⟩ : ∃ y, y = g ^ 2 ^ n := ⟨_, rfl⟩
    have hyC : y ∈ Subgroup.centralizer (R : Set P) := hydef ▸ Subgroup.pow_mem _ hgC _
    have hy3 : y ^ 3 = 1 := by
      rw [hydef, ← pow_mul, ← hP]
      exact pow_card_eq_one'
    have hφy : φ y ≠ 1 := by
      intro h
      rw [hydef, map_pow, hφg] at h
      have h1 : orderOf (φ e' * φ w * (φ e')⁻¹ * (φ w)⁻¹) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
      have h2 : orderOf (φ e' * φ w * (φ e')⁻¹ * (φ w)⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one he3
      have hcop : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
      exact he1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2))
    have hy1 : y ≠ 1 := fun h => hφy (by rw [h, map_one])
    have hφy3 : φ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hzp : ∀ h : P, Odd (orderOf h) → h ∈ Subgroup.zpowers y := by
      intro h hh
      have hh3 := hodd h hh
      have hφh3 : φ h ^ 3 = 1 := by rw [← map_pow, hh3, map_one]
      obtain ⟨i, hi⟩ : ∃ i : ℕ, φ h = φ (y ^ i) := by
        rcases hA2 (φ h) (φ y) hφh3 hφy3 hφy with h1 | h1 | h1
        · exact ⟨0, by rw [h1, pow_zero, map_one]⟩
        · exact ⟨1, by rw [h1, pow_one]⟩
        · exact ⟨2, by rw [h1, map_pow, sq]⟩
      obtain ⟨r, hrdef⟩ : ∃ r, r = h * (y ^ i)⁻¹ := ⟨_, rfl⟩
      have hr : r ∈ R := by
        rw [← hker, MonoidHom.mem_ker, hrdef, map_mul, map_inv, hi, mul_inv_cancel]
      have hry : r * y ^ i = y ^ i * r :=
        (Commute.pow_left ((Subgroup.mem_centralizer_iff.mp hyC) r hr).symm i).eq.symm
      have hh' : h = r * y ^ i := by rw [hrdef]; group
      have hr3 : r ^ 3 = 1 := by
        have : h ^ 3 = r ^ 3 * (y ^ i) ^ 3 := by rw [hh']; exact (Commute.mul_pow hry 3)
        rw [hh3, ← pow_mul, mul_comm i 3, pow_mul, hy3, one_pow, mul_one] at this
        exact this.symm
      rw [hh', hR3 r hr hr3, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) i
    have hle : oTwoUpper (⊤ : Subgroup P) ≤ Subgroup.zpowers y :=
      (Subgroup.closure_le _).mpr fun h hh => hzp h hh.2
    obtain ⟨v, -, hv1, hv2, hvO⟩ := hv
    have hvy := hle hvO
    have h1 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one hv2
    have h2 : orderOf v ∣ 3 := (orderOf_dvd_of_mem_zpowers hvy).trans
      (orderOf_dvd_of_pow_eq_one hy3)
    exact hv1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2))

end Quaternion

end L15422

section Main

open L15422

variable {D : Type} [Group D] [Finite D] {H₁ H₂ Z' : Subgroup D}

theorem Config15422.false_of_quaternion (h : Config15422 H₁ H₂ Z') {A : Type} [Group A]
    [Finite A] {j : ℕ} (hA : Nat.card A = 2 ^ j * 3)
    (hA1 : ∀ d : A, (∃ g, d * g ≠ g * d) →
      ∃ e, (e * d * e⁻¹ * d⁻¹) ^ 3 = 1 ∧ e * d * e⁻¹ * d⁻¹ ≠ 1)
    (hA2 : ∀ s c : A, s ^ 3 = 1 → c ^ 3 = 1 → c ≠ 1 → s = 1 ∨ s = c ∨ s = c * c)
    (hx : IsExtensionWith ↥H₁ A
      (fun N => IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, hcp⟩ := hx
  have htr := h.amalgam.toIsGoldschmidtTriple
  have hRc : SmallCenter φ.ker :=
    smallCenter_of_isCentralProduct₂ smallCenter_quaternion smallCenter_quaternion hcp
  have hT2 : IsPGroup 2 ((H₁ ⊓ H₂).subgroupOf H₁) :=
    htr.isPGroup_inf.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hTi : ((H₁ ⊓ H₂).subgroupOf H₁).index = 3 := htr.relIndex_inf_left
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
  have hH : Nat.card H₁ = 2 ^ n * 3 := by
    rw [← ((H₁ ⊓ H₂).subgroupOf H₁).card_mul_index, hn, hTi]
  have hR2 : IsPGroup 2 φ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hA, hH] at h1
    have h2 : Nat.card φ.ker * 2 ^ j = 2 ^ n := by
      have : 2 ^ n * 3 = (Nat.card φ.ker * 2 ^ j) * 3 := by rw [h1]; ring
      omega
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ h2)
    exact IsPGroup.of_card hm
  have hE : Z'.subgroupOf H₁ ≤ Subgroup.centralizer (((H₁ ⊓ H₂).subgroupOf H₁ : Subgroup H₁) :
      Set H₁) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (h.Z_central hx)) t ht)
  obtain ⟨v, hvZ, hv1, hvO⟩ := h.odd₁
  have hvH : v ∈ H₁ := (h.Z_le hvZ).1
  have hvO' : (⟨v, hvH⟩ : ↥H₁) ∈ oTwoUpper (⊤ : Subgroup H₁) := by
    have hmap := oTwoUpper_map H₁.subtype (⊤ : Subgroup H₁)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    rw [hmap] at hvO
    obtain ⟨x, hx, hxv⟩ := hvO
    have : x = ⟨v, hvH⟩ := Subtype.ext hxv
    rwa [← this]
  have hcen := le_center_of_quotient_smallCenter hφ rfl hR2 hRc hT2 hTi hA1 hA2 hE
    ⟨⟨v, hvH⟩, hvZ, fun h => hv1 (congrArg Subtype.val h),
      Subtype.ext (by simpa using h.sq_Z v hvZ), hvO'⟩
  obtain ⟨z, hz, hz1, hzc⟩ := h.z₂
  have hzH : z ∈ H₁ := (h.Z_le hz).1
  have hzc₁ : z ∈ Subgroup.centralizer (H₁ : Set D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.mem_center_iff.mp (hcen (show (⟨z, hzH⟩ : ↥H₁) ∈ Z'.subgroupOf H₁ from hz))
      ⟨g, hg⟩
    exact (congrArg Subtype.val this)
  exact hz1 (eq_one_of_mem_centralizer_of_pCore_eq_bot htr.gen h.amalgam.pCore_eq_bot hzc₁ hzc
    (h.sq_Z z hz))

theorem Config15422.caseEight_of_oriented (h : Config15422 H₁ H₂ Z')
    (hc : IsF618CaseOriented H₁ H₂) : IsCaseEight15422 D := by
  have hD8 : ¬ Nonempty (↥(H₁ ⊓ H₂) ≃* DihedralGroup 4) := fun ⟨e⟩ =>
    false_of_mulEquiv_center e dihedral_four_center h.Z_le h.Z_central h.card_Z h.sq_Z
  have hW : ¬ Nonempty (↥(H₁ ⊓ H₂) ≃* Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)) :=
    fun ⟨e⟩ => false_of_mulEquiv_center e wreath_four_two_center h.Z_le h.Z_central h.card_Z
      h.sq_Z
  have hS3 : Nat.card (Equiv.Perm (Fin 3)) = 2 ^ 1 * 3 := by
    rw [Nat.card_perm, Nat.card_fin]
    rfl
  have hD12 : Nat.card (DihedralGroup 6) = 2 ^ 2 * 3 := by
    rw [DihedralGroup.nat_card]
    rfl
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exfalso
    have hle := Subgroup.card_le_of_le h.Z_le
    rw [h1.card_inf, h.card_Z] at hle
    omega
  · exfalso
    apply h.nonsolv
    unfold IsF618CaseTwo at h2
    rcases h2 with he | ⟨φ, hφ, hP⟩
    · obtain ⟨e⟩ := he
      have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · have hcard : Nat.card φ.ker = 3 ^ 3 := hP.2.1
      have : Finite φ.ker := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      have : Group.IsNilpotent φ.ker := (IsPGroup.of_card hcard).isNilpotent
      exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by rw [Subgroup.range_subtype])
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, he, -⟩ := h3
    exact absurd he hD8
  · exfalso
    obtain ⟨-, -, ⟨e₁⟩, -⟩ := h4
    obtain ⟨v, hvZ, hv1, hvO⟩ := h.odd₁
    exact hv1 (eq_one_of_mem_oTwoUpper e₁ hD12 dihedral_six_cube hvO (h.sq_Z v hvZ))
  · obtain ⟨-, he, -⟩ := h5
    exact absurd he hD8
  · obtain ⟨-, he, -⟩ := h6
    exact absurd he hD8
  · obtain ⟨-, he, -⟩ := h7
    exact absurd he hD8
  · rcases h8.1 with hS | ⟨p, hp, hp8, hL⟩
    · exact Or.inl hS
    · exact Or.inr ⟨p, hp, by omega, hL⟩
  · exfalso
    obtain ⟨-, -, -, ⟨e₂⟩⟩ := h9
    obtain ⟨v, hvZ, hv1, hvO⟩ := h.odd₂
    have hcard : Nat.card (Equiv.Perm (Fin 3) × DihedralGroup 4) = 2 ^ 4 * 3 := by
      rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, DihedralGroup.nat_card]
      rfl
    exact hv1 (eq_one_of_mem_oTwoUpper e₂ hcard perm_three_dihedral_four_cube hvO
      (h.sq_Z v hvZ))
  · obtain ⟨-, he, -⟩ := h10
    exact absurd he hW
  · obtain ⟨-, -, hx, -⟩ := h11
    exact (h.false_of_quaternion hS3 perm_three_commutator perm_three_cube hx).elim
  · obtain ⟨-, -, hx, -⟩ := h12
    exact (h.false_of_quaternion hS3 perm_three_commutator perm_three_cube hx).elim
  · obtain ⟨-, -, hx, -⟩ := h13
    exact (h.false_of_quaternion hD12 dihedral_six_commutator dihedral_six_cube_powers hx).elim

theorem Config15422.caseEight (h : Config15422 H₁ H₂ Z') (hF : F618Conclusion H₁ H₂) :
    IsCaseEight15422 D := by
  rcases hF with hc | hc
  · exact h.caseEight_of_oriented hc
  · exact h.symm.caseEight_of_oriented hc

end Main

end CFSG.Quasithin.EmptyFaithfulMultiple
