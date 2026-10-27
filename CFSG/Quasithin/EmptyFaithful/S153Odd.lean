module

public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts
public import CFSG.Quasithin.EmptyFaithful.S1417NaturalMore

public section

open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped commutatorElement

namespace CFSG.Quasithin

section Generic

theorem commutator_oTwoUpper_eq_of_inv {G : Type*} [Group G] {X R : Subgroup G} {r : G} (hR : R ≤ X)
    (hrR : r ∈ R) (hinv : ∀ y ∈ X, Odd (orderOf y) → r * y * r⁻¹ = y⁻¹) :
    ⁅oTwoUpper X, R⁆ = oTwoUpper X := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro p hp q hq
    have hqN : q ∈ Subgroup.normalizer (oTwoUpper X : Set G) :=
      le_normalizer_oTwoUpper X (hR hq)
    have hc := (Subgroup.mem_normalizer_iff.mp hqN p).mp hp
    have : ⁅p, q⁆ = p * (q * p⁻¹ * q⁻¹) := by group
    rw [this]
    refine Subgroup.mul_mem _ hp ?_
    have h2 := (Subgroup.mem_normalizer_iff.mp hqN p⁻¹).mp (Subgroup.inv_mem _ hp)
    simpa [mul_assoc] using h2
  · rw [oTwoUpper, Subgroup.closure_le]
    rintro y ⟨hyX, hyodd⟩
    obtain ⟨m, hm⟩ := hyodd
    have hy1 : y ^ orderOf y = 1 := pow_orderOf_eq_one y
    have hy'X : y ^ (m + 1) ∈ X := X.pow_mem hyX _
    have hy'odd : Odd (orderOf (y ^ (m + 1))) :=
      Odd.of_dvd_nat ⟨m, hm⟩ (orderOf_pow_dvd (m + 1))
    have hy'P : y ^ (m + 1) ∈ oTwoUpper X := mem_oTwoUpper_of_odd hy'X hy'odd
    have h1 : r * y ^ (m + 1) * r⁻¹ = (y ^ (m + 1))⁻¹ := hinv _ hy'X hy'odd
    have h2 : r * (y ^ (m + 1))⁻¹ * r⁻¹ = y ^ (m + 1) := by
      have := congrArg (fun a => a⁻¹) h1
      simpa [mul_assoc] using this
    have h3 : ⁅y ^ (m + 1), r⁆ = y := by
      have e : ⁅y ^ (m + 1), r⁆ = y ^ (m + 1) * (r * (y ^ (m + 1))⁻¹ * r⁻¹) := by group
      rw [e, h2, ← pow_add]
      have e2 : m + 1 + (m + 1) = orderOf y + 1 := by omega
      rw [e2, pow_succ, hy1, one_mul]
    show y ∈ ⁅oTwoUpper X, R⁆
    rw [← h3]
    exact Subgroup.commutator_mem_commutator hy'P hrR

theorem exists_ne_one_mem_center_of_normalized {G : Type*} [Group G] [Finite G] {T U : Subgroup G}
    (hT : IsPGroup 2 T) (hUT : U ≤ T) (hU : U ≠ ⊥)
    (hn : T ≤ Subgroup.normalizer (U : Set G)) :
    ∃ z ∈ U, z ≠ 1 ∧ ∀ y ∈ T, y * z = z * y := by
  have hTnil : Group.IsNilpotent T := hT.isNilpotent
  have hUTn : (U.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mpr hn
  have hU' : U.subgroupOf T ≠ ⊥ := by
    intro hbot
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, hbot, Subgroup.map_bot]
  obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hU')
  refine ⟨w, Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1,
    fun h1 => hw1 (Subtype.ext (Subtype.ext h1)), fun y hy => ?_⟩
  have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp hw).2 ⟨y, hy⟩
  exact congrArg Subtype.val this

end Generic

section Odd

variable {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

omit [Finite W] in
theorem cube_mul_of_cube {L : Subgroup (MulAut W)} {U : Subgroup W} (hN : ActsAsNaturalL2 L U)
    {a b : MulAut W} (ha : a ∈ L) (hb : b ∈ L) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) :
    (a * b) ^ 3 = 1 ∧ a * b = b * a := by
  obtain ⟨e⟩ := nonempty_equiv_perm hN
  have key : ∀ x y : Equiv.Perm (Fin 3), x ^ 3 = 1 → y ^ 3 = 1 →
      (x * y) ^ 3 = 1 ∧ x * y = y * x := by decide
  have hA : (⟨a, ha⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hB : (⟨b, hb⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hA' : (e ⟨a, ha⟩) ^ 3 = 1 := by rw [← map_pow, hA, map_one]
  have hB' : (e ⟨b, hb⟩) ^ 3 = 1 := by rw [← map_pow, hB, map_one]
  obtain ⟨k1, k2⟩ := key _ _ hA' hB'
  have e1 : ((⟨a, ha⟩ : L) * ⟨b, hb⟩) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_mul, map_one]
    exact k1
  have e2 : (⟨a, ha⟩ : L) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    apply e.injective
    rw [map_mul, map_mul]
    exact k2
  exact ⟨by simpa using congrArg Subtype.val e1, by simpa using congrArg Subtype.val e2⟩

namespace OfourStruct

@[expose] def cubeSub (h : OfourStruct X L₁ L₂ t) : Subgroup (MulAut W) where
  carrier := {y | y ∈ L₁ ⊔ L₂ ∧ y ^ 3 = 1}
  one_mem' := ⟨Subgroup.one_mem _, one_pow 3⟩
  mul_mem' := by
    rintro a b ⟨haN, ha3⟩ ⟨hbN, hb3⟩
    have hodd : ∀ {y : MulAut W}, y ^ 3 = 1 → Odd (orderOf y) := fun hy =>
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hy)
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl, ha₁3, ha₂3⟩ := h.odd_decomp haN (hodd ha3)
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl, hb₁3, hb₂3⟩ := h.odd_decomp hbN (hodd hb3)
    have hc : a₂ * b₁ = b₁ * a₂ := (h.comm b₁ hb₁ a₂ ha₂).symm
    have e : a₁ * a₂ * (b₁ * b₂) = (a₁ * b₁) * (a₂ * b₂) := by
      calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
        _ = a₁ * (b₁ * a₂) * b₂ := by rw [hc]
        _ = (a₁ * b₁) * (a₂ * b₂) := by group
    have h1 := (cube_mul_of_cube h.nat₁ ha₁ hb₁ ha₁3 hb₁3).1
    have h2 := (cube_mul_of_cube h.nat₂ ha₂ hb₂ ha₂3 hb₂3).1
    have hcomm : Commute (a₁ * b₁) (a₂ * b₂) :=
      h.comm _ (L₁.mul_mem ha₁ hb₁) _ (L₂.mul_mem ha₂ hb₂)
    refine ⟨?_, ?_⟩
    · rw [e]
      exact (Subgroup.mul_mem _ (Subgroup.mem_sup_left (L₁.mul_mem ha₁ hb₁))
        (Subgroup.mem_sup_right (L₂.mul_mem ha₂ hb₂)))
    · rw [e, hcomm.mul_pow, h1, h2, one_mul]
  inv_mem' := by
    rintro a ⟨haN, ha3⟩
    exact ⟨Subgroup.inv_mem _ haN, by rw [inv_pow, ha3, inv_one]⟩

omit [Finite W] in
theorem mem_cubeSub (h : OfourStruct X L₁ L₂ t) {y : MulAut W} :
    y ∈ h.cubeSub ↔ y ∈ L₁ ⊔ L₂ ∧ y ^ 3 = 1 := Iff.rfl

omit [Finite W] in
theorem isPGroup_cubeSub (h : OfourStruct X L₁ L₂ t) : IsPGroup 3 h.cubeSub := by
  intro y
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa using y.2.2

omit [Finite W] in
theorem oTwoUpper_le_cubeSub (h : OfourStruct X L₁ L₂ t) :
    oTwoUpper X ≤ h.cubeSub := by
  rw [oTwoUpper, Subgroup.closure_le]
  rintro y ⟨hyX, hyodd⟩
  have hyN : y ∈ L₁ ⊔ L₂ := h.odd_mem_sup hyX hyodd
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl, h1, h2⟩ := h.odd_decomp hyN hyodd
  refine ⟨hyN, ?_⟩
  have hcomm : Commute l₁ l₂ := h.comm l₁ hl₁ l₂ hl₂
  rw [hcomm.mul_pow, h1, h2, one_mul]

omit [Finite W] in
theorem pow_three_of_mem_oTwoUpper (h : OfourStruct X L₁ L₂ t) {y : MulAut W}
    (hy : y ∈ oTwoUpper X) : y ^ 3 = 1 :=
  (h.oTwoUpper_le_cubeSub hy).2

omit [Finite W] in
theorem odd_orderOf_of_mem_oTwoUpper (h : OfourStruct X L₁ L₂ t) {y : MulAut W}
    (hy : y ∈ oTwoUpper X) : Odd (orderOf y) :=
  Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one (h.pow_three_of_mem_oTwoUpper hy))

omit [Finite W] in
theorem oTwoUpper_le_sup (h : OfourStruct X L₁ L₂ t) : oTwoUpper X ≤ L₁ ⊔ L₂ :=
  fun _ hy => (h.oTwoUpper_le_cubeSub hy).1

theorem odd_card_oTwoUpper (h : OfourStruct X L₁ L₂ t) : Odd (Nat.card (oTwoUpper X)) := by
  obtain ⟨n, hn⟩ := h.isPGroup_cubeSub.exists_card_eq
  have hdvd : Nat.card (oTwoUpper X) ∣ Nat.card h.cubeSub :=
    Subgroup.card_dvd_of_le h.oTwoUpper_le_cubeSub
  rw [hn] at hdvd
  exact Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) hdvd

theorem exists_orderOf_three (h : OfourStruct X L₁ L₂ t) :
    ∃ y ∈ L₁, orderOf y = 3 := by
  have h3 : 3 ∣ Nat.card L₁ := by rw [h.card_L₁]; exact ⟨2, rfl⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem oTwoUpper_ne_bot (h : OfourStruct X L₁ L₂ t) : oTwoUpper X ≠ ⊥ := by
  obtain ⟨y, hy, hy3⟩ := h.exists_orderOf_three
  intro hbot
  have hyX : y ∈ X := h.L₁_le hy
  have hmem : y ∈ oTwoUpper X :=
    mem_oTwoUpper_of_odd hyX (by rw [hy3]; decide)
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hy3
  exact absurd hy3 (by decide)

theorem sup_oTwoUpper_eq (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) : oTwoUpper X ⊔ T' = X := by
  have hle : oTwoUpper X ⊔ T' ≤ X := sup_le (oTwoUpper_le X) hT.1
  rcases h.maximal hT le_sup_right hle with h1 | h1
  · exfalso
    have hP : oTwoUpper X ≤ T' := le_sup_left.trans h1.le
    have hp2 : IsPGroup 2 (oTwoUpper X) := hT.2.1.to_le hP
    obtain ⟨n, hn⟩ := hp2.exists_card_eq
    have hodd := h.odd_card_oTwoUpper
    rw [hn] at hodd
    have hn0 : n = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
    rw [hn0, pow_zero] at hn
    exact h.oTwoUpper_ne_bot (Subgroup.card_eq_one.mp hn)
  · exact h1

theorem eq_bot_of_normal_isPGroup (h : OfourStruct X L₁ L₂ t) {T' K : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) (hKX : K ≤ X)
    (hKn : X ≤ Subgroup.normalizer (K : Set (MulAut W))) (hK2 : IsPGroup 2 K) : K = ⊥ := by
  by_contra hK
  have hKnormal : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hKn
  have hKT : K ≤ T' := A4.le_of_normal_of_isSylowTwoOf hT hKX hKnormal hK2
  obtain ⟨z, hzK, hz1, hzc⟩ :=
    exists_ne_one_mem_center_of_normalized hT.2.1 hKT hK (hT.1.trans hKn)
  obtain ⟨r, hrT, hr1, hrr, hrc, hrz, hrinv⟩ := h.exists_central hT
  have hzr : z = r := (hrz z (hKT hzK) hzc).resolve_left hz1
  have hrK : r ∈ K := hzr ▸ hzK
  obtain ⟨y, hyL, hy3⟩ := h.exists_orderOf_three
  have hyX : y ∈ X := h.L₁_le hyL
  have hyodd : Odd (orderOf y) := by rw [hy3]; decide
  have hconj : r * y * r⁻¹ = y⁻¹ := hrinv y hyX hyodd
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hyr : y * r * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKn hyX) r).mp hrK
  have h1 : r * y⁻¹ * r⁻¹ = y := by
    have := congrArg (fun a => a⁻¹) hconj
    simpa [mul_assoc] using this
  have hform : y * r * y⁻¹ = (y * y) * r := by
    calc y * r * y⁻¹ = y * (r * y⁻¹ * r⁻¹) * r := by group
      _ = y * y * r := by rw [h1]
  have hyy : y * y ∈ T' := by
    have : y * y = (y * r * y⁻¹) * r⁻¹ := by rw [hform]; group
    rw [this]
    exact T'.mul_mem (hKT hyr) (T'.inv_mem hrT)
  have hyT : y ∈ T' := by
    have : y = (y * y) * (y * y) := by
      calc y = y * y ^ 3 := by rw [hy3', mul_one]
        _ = (y * y) * (y * y) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this]
    exact T'.mul_mem hyy hyy
  obtain ⟨k, hk⟩ := hT.2.1 ⟨y, hyT⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : 3 ∣ 2 ^ k := by
    rw [← hy3]
    exact orderOf_dvd_of_pow_eq_one hk'
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

omit [Finite W] in
theorem comm_cubeSub (h : OfourStruct X L₁ L₂ t) {x y : MulAut W} (hx : x ∈ h.cubeSub)
    (hy : y ∈ h.cubeSub) : x * y = y * x := by
  obtain ⟨hxN, hx3⟩ := hx
  obtain ⟨hyN, hy3⟩ := hy
  have hodd : ∀ {y : MulAut W}, y ^ 3 = 1 → Odd (orderOf y) := fun hy =>
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hy)
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl, ha₁3, ha₂3⟩ := h.odd_decomp hxN (hodd hx3)
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl, hb₁3, hb₂3⟩ := h.odd_decomp hyN (hodd hy3)
  have c1 := (cube_mul_of_cube h.nat₁ ha₁ hb₁ ha₁3 hb₁3).2
  have c2 := (cube_mul_of_cube h.nat₂ ha₂ hb₂ ha₂3 hb₂3).2
  have c3 : a₂ * b₁ = b₁ * a₂ := (h.comm b₁ hb₁ a₂ ha₂).symm
  have c4 : b₂ * a₁ = a₁ * b₂ := (h.comm a₁ ha₁ b₂ hb₂).symm
  calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
    _ = a₁ * (b₁ * a₂) * b₂ := by rw [c3]
    _ = (a₁ * b₁) * (a₂ * b₂) := by group
    _ = (b₁ * a₁) * (b₂ * a₂) := by rw [c1, c2]
    _ = b₁ * (a₁ * b₂) * a₂ := by group
    _ = b₁ * (b₂ * a₁) * a₂ := by rw [c4]
    _ = b₁ * b₂ * (a₁ * a₂) := by group

omit [Finite W] in
theorem comm_oTwoUpper (h : OfourStruct X L₁ L₂ t) {x y : MulAut W} (hx : x ∈ oTwoUpper X)
    (hy : y ∈ oTwoUpper X) : x * y = y * x :=
  h.comm_cubeSub (h.oTwoUpper_le_cubeSub hx) (h.oTwoUpper_le_cubeSub hy)

theorem card_oTwoUpper (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) : Nat.card (oTwoUpper X) = 9 := by
  set P := oTwoUpper X with hP
  have hPn : T' ≤ Subgroup.normalizer (P : Set (MulAut W)) :=
    hT.1.trans (le_normalizer_oTwoUpper X)
  have h1 := A4.relIndex_sup_eq_of_le_normalizer' hPn
  rw [sup_comm, h.sup_oTwoUpper_eq hT] at h1
  have hinf : P ⊓ T' = ⊥ := by
    have hp2 : IsPGroup 2 ↥(P ⊓ T') := hT.2.1.to_inf_right
    obtain ⟨n, hn⟩ := hp2.exists_card_eq
    have hdvd : Nat.card ↥(P ⊓ T') ∣ Nat.card P := Subgroup.card_dvd_of_le inf_le_left
    have hodd := h.odd_card_oTwoUpper
    have hodd' : Odd (Nat.card ↥(P ⊓ T')) := Odd.of_dvd_nat hodd hdvd
    rw [hn] at hodd'
    have hn0 : n = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_pow.mpr ⟨even_two, hne⟩)
    rw [hn0, pow_zero] at hn
    exact Subgroup.card_eq_one.mp hn
  have h2 : P.relIndex T' = 8 := by
    have e := Subgroup.relIndex_mul_card P T'
    rw [hinf, Subgroup.card_bot, mul_one, h.card_T hT] at e
    exact e
  have h3 : P.relIndex X = Nat.card X / Nat.card P := by
    have e := Subgroup.relIndex_mul_card P X
    rw [inf_eq_left.2 (oTwoUpper_le X)] at e
    have hpos : 0 < Nat.card P := Nat.card_pos
    exact (Nat.div_eq_of_eq_mul_left hpos e.symm).symm
  rw [h2, h3, h.card_X] at h1
  have hpos : 0 < Nat.card P := Nat.card_pos
  have hdvd : Nat.card P ∣ 72 := by
    have := Subgroup.card_dvd_of_le (oTwoUpper_le X)
    rwa [h.card_X] at this
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at h1
  rw [Nat.mul_div_cancel_left k hpos] at h1
  rw [h1] at hk
  omega

theorem le_commV_of_fixedPointFree {P : Subgroup (MulAut W)} {U : Subgroup W}
    {x : MulAut W} (hxP : x ∈ P) (hst : ∀ u ∈ U, x u ∈ U) (hfpf : ∀ u ∈ U, x u = u → u = 1) :
    U ≤ commV P := by
  let f : ↥U → ↥U := fun u => ⟨x u * (u : W)⁻¹, U.mul_mem (hst u u.2) (U.inv_mem u.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h0 : x (a : W) * (a : W)⁻¹ = x (b : W) * (b : W)⁻¹ := congrArg Subtype.val hab
    have h1 : x a / (a : W) = x b / (b : W) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact h0
    have h3 : x a * (b : W) = x b * (a : W) := div_eq_div_iff_mul_eq_mul.1 h1
    have h2 : x ((a : W) * (b : W)⁻¹) = (a : W) * (b : W)⁻¹ := by
      rw [map_mul, map_inv, ← div_eq_mul_inv, ← div_eq_mul_inv]
      exact div_eq_div_iff_mul_eq_mul.2 (by rw [h3, mul_comm])
    have h3 := hfpf _ (U.mul_mem a.2 (U.inv_mem b.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro w hw
  obtain ⟨u, hu⟩ := hsurj ⟨w, hw⟩
  exact Subgroup.subset_closure ⟨x, hxP, (u : W), congrArg Subtype.val hu⟩

theorem commV_oTwoUpper (h : OfourStruct X L₁ L₂ t) : commV (oTwoUpper X) = ⊤ := by
  have hodd : ∀ {y : MulAut W}, y ^ 3 = 1 → Odd (orderOf y) := fun hy =>
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hy)
  obtain ⟨x₁, hx₁L, hx₁3, hx₁1⟩ := exists_orderThree h.nat₁
  obtain ⟨x₂, hx₂L, hx₂3, hx₂1⟩ := exists_orderThree h.nat₂
  have hx₁P : x₁ ∈ oTwoUpper X := mem_oTwoUpper_of_odd (h.L₁_le hx₁L) (hodd hx₁3)
  have hx₂P : x₂ ∈ oTwoUpper X := mem_oTwoUpper_of_odd (h.L₂_le hx₂L) (hodd hx₂3)
  have hU₁ : commV L₁ ≤ commV (oTwoUpper X) :=
    le_commV_of_fixedPointFree hx₁P (fun u hu => commV_stable L₁ hx₁L hu) fun u hu hxu =>
      by_contra fun hu1 => hx₁1 (eq_one_of_odd_of_fixed h.nat₁
        (fun l hl u hu => commV_stable L₁ hl hu) hx₁L (hodd hx₁3) hu hu1 hxu)
  have hU₂ : commV L₂ ≤ commV (oTwoUpper X) :=
    le_commV_of_fixedPointFree hx₂P (fun u hu => commV_stable L₂ hx₂L hu) fun u hu hxu =>
      by_contra fun hu1 => hx₂1 (eq_one_of_odd_of_fixed h.nat₂
        (fun l hl u hu => commV_stable L₂ hl hu) hx₂L (hodd hx₂3) hu hu1 hxu)
  rw [eq_top_iff, ← h.sup]
  exact sup_le hU₁ hU₂

end OfourStruct

end Odd


end CFSG.Quasithin
