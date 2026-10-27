module

public import CFSG.Quasithin.EmptyFaithful.SzN8Basic
public import CFSG.Quasithin.EmptyFaithful.SzN4Local
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

section Facts

variable {G : Type} [Group G] [Finite G]

theorem szN8_Q_facts {X : Type} [Group X] (hQ : IsElemAbelianOfRank 3 2 X ∨ IsPOnePlusTwo 3 X) :
    (∀ q : X, q ^ 3 = 1) ∧ (Nat.card X = 9 ∨ Nat.card X = 27) := by
  rcases hQ with h | h
  · obtain ⟨e⟩ := h
    refine ⟨fun q => e.injective ?_, Or.inl ?_⟩
    · rw [map_pow, map_one]
      ext i
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      have h3 : (3 : ZMod 3) = 0 := by decide
      simp [h3]
    · rw [Nat.card_congr e.toEquiv]
      simp [Nat.card_eq_fintype_card]
  · exact ⟨h.2.2, Or.inr (by simpa using h.2.1)⟩

theorem szN8_odd_pow_three {Y : Subgroup G} (hQe : ∀ q : OTwoQuot Y, q ^ 3 = 1) {y : G} (hy : y ∈ Y)
    (ho : Odd (orderOf y)) : y ^ 3 = 1 := by
  have h1 : (QuotientGroup.mk (⟨y, hy⟩ : ↥Y) : OTwoQuot Y) ^ 3 = 1 := hQe _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  have hmem : y ^ 3 ∈ pCoreOf 2 Y := ⟨_, h1, rfl⟩
  refine szN4_eq_one_of_mem_pCoreOf_of_pow (L := Y) hmem (m := orderOf y) ho ?_
  rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]

end Facts


section Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem szN8_odd_of_three {P : Subgroup G} (hP3 : IsPGroup 3 P) {x : G} (hx : x ∈ P) :
    Odd (orderOf x) := by
  obtain ⟨n, hn⟩ := hP3 ⟨x, hx⟩
  have h1 : x ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h2 : orderOf x ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  rw [hj]
  exact Odd.pow (by decide)

theorem szN8_eq_one_of_three {P L : Subgroup G} (hP3 : IsPGroup 3 P) {x : G} (hx : x ∈ P)
    (hxL : x ∈ pCoreOf 2 L) : x = 1 :=
  szN4_eq_one_of_mem_pCoreOf_of_pow (L := L) hxL (m := orderOf x) (szN8_odd_of_three hP3 hx)
    (pow_orderOf_eq_one x)

omit [Finite G] in
theorem szN8_mem_of_two_pow_mem {N : Subgroup G} {y : G} (hy : Odd (orderOf y)) {j : ℕ}
    (h : y ^ (2 ^ j) ∈ N) : y ∈ N := by
  obtain ⟨k, hk⟩ := hy
  have e : 2 * (k + 1) = orderOf y + 1 := by omega
  have key : ∀ i : ℕ, y ^ ((orderOf y + 1) ^ i) = y := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e1 : (orderOf y + 1) ^ (i + 1) =
          orderOf y * (orderOf y + 1) ^ i + (orderOf y + 1) ^ i := by ring
      rw [e1, pow_add, pow_mul, pow_orderOf_eq_one, one_pow, one_mul, ih]
  have h1 : (y ^ (2 ^ j)) ^ ((k + 1) ^ j) = y := by
    rw [← pow_mul, ← mul_pow, e, key]
  have h2 := N.pow_mem h ((k + 1) ^ j)
  rwa [h1] at h2

end Helpers

section Main

variable {G : Type} [Group G] [Finite G]

@[expose] def szN8Cs (L : Subgroup G) : Subgroup G :=
  centralizerSection (Subgroup.normalizer (L : Set G)) L (pCoreOf 2 L)

omit [Finite G] in
theorem szN8_mem_Cs {L : Subgroup G} {z : G} :
    z ∈ szN8Cs L ↔
      z ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L, l * z * l⁻¹ * z⁻¹ ∈ pCoreOf 2 L := by
  unfold szN8Cs
  rw [mem_centralizerSection]
  constructor
  · rintro ⟨h1, -, -, h4⟩
    exact ⟨h1, h4⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h1, normalizer_le_normalizer_pCoreOf 2 L h1, h2⟩

omit [Finite G] in
theorem szN8_Cs_conj {L : Subgroup G} {g z : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hz : z ∈ szN8Cs L) : g * z * g⁻¹ ∈ szN8Cs L := by
  obtain ⟨hzN, hzc⟩ := szN8_mem_Cs.mp hz
  refine szN8_mem_Cs.mpr ⟨?_, fun x hx => ?_⟩
  · exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hg hzN)
      ((Subgroup.normalizer _).inv_mem hg)
  · have hx' : g⁻¹ * x * g ∈ L := (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
    have h1 := hzc _ hx'
    have e : x * (g * z * g⁻¹) * x⁻¹ * (g * z * g⁻¹)⁻¹ =
        g * ((g⁻¹ * x * g) * z * (g⁻¹ * x * g)⁻¹ * z⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 L hg) _).mp h1

omit [Finite G] in
theorem szN8_normalizer_le_Cs (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (szN8Cs L : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => szN8_Cs_conj hg hz, fun hz => ?_⟩
  have h1 := szN8_Cs_conj ((Subgroup.normalizer _).inv_mem hg) hz
  have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
  rwa [e] at h1

omit [Finite G] in
theorem szN8_cs_eq {Y L : Subgroup G} (hYN : Y ≤ Subgroup.normalizer (L : Set G)) :
    centralizerSection Y L (pCoreOf 2 L) = Y ⊓ szN8Cs L := by
  ext m
  rw [Subgroup.mem_inf, szN8_mem_Cs, mem_centralizerSection]
  constructor
  · rintro ⟨hmY, -, -, hc⟩
    exact ⟨hmY, hYN hmY, hc⟩
  · rintro ⟨hmY, hmN, hc⟩
    exact ⟨hmY, hmN, normalizer_le_normalizer_pCoreOf 2 L hmN, hc⟩

end Main

section E9

variable {G : Type} [Group G] [Finite G]

theorem szN8_Q_comm_imp_E9 {X : Type} [Group X]
    (hQ : IsElemAbelianOfRank 3 2 X ∨ IsPOnePlusTwo 3 X) (hc : ∀ x y : X, x * y = y * x) :
    IsElemAbelianOfRank 3 2 X := by
  rcases hQ with h | h
  · exact h
  · exfalso
    obtain ⟨hext, -, -⟩ := h
    have := hext
    have hnt : Nontrivial (X ⧸ Subgroup.center X) := CFSG.IsExtraspecial.quotient_nontrivial 3 X
    have hcen : Subgroup.center X = ⊤ := by
      ext x
      simp only [Subgroup.mem_center_iff, Subgroup.mem_top, iff_true]
      exact fun g => hc g x
    have hsub : Subsingleton (X ⧸ Subgroup.center X) := by
      rw [hcen]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_nontrivial_iff_subsingleton.mpr hsub hnt

end E9

section Decomp

variable {G : Type} [Group G] [Finite G]

theorem szN8_decomp {Y L : Subgroup G} (hYN : Y ≤ Subgroup.normalizer (L : Set G))
    (hY2 : oTwoUpper Y = Y)
    (hQ : IsElemAbelianOfRank 3 2 (OTwoQuot Y) ∨ IsPOnePlusTwo 3 (OTwoQuot Y))
    (hA : oTwoUpper (Y ⊓ L) ≠ ⊥)
    (hrank : ∀ E : Subgroup G, E ≤ L → IsPGroup 3 E → (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 3)
    (hZ : ∀ x ∈ L, (∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 L) → x ∈ pCoreOf 2 L)
    (hinner : ∀ y ∈ Y, Odd (orderOf y) →
      ∃ x ∈ L, ∀ l ∈ L, l * (x⁻¹ * y) * l⁻¹ * (x⁻¹ * y)⁻¹ ∈ pCoreOf 2 L) :
    Y = oTwoUpper (Y ⊓ L) ⊔ oTwoUpper (centralizerSection Y L (pCoreOf 2 L)) ∧
      IsElemAbelianOfRank 3 2 (OTwoQuot Y) := by
  classical
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQe, hQcard⟩ := szN8_Q_facts hQ
  rw [szN8_cs_eq hYN]
  obtain ⟨a, haYL, hao, ha1⟩ : ∃ a ∈ Y ⊓ L, Odd (orderOf a) ∧ a ≠ 1 := by
    by_contra hno
    push Not at hno
    apply hA
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, hxo⟩
    exact Subgroup.mem_bot.mpr (hno x hx hxo)
  have ha3 : a ^ 3 = 1 := szN8_odd_pow_three hQe haYL.1 hao
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  let a' : ↥Y := ⟨a, haYL.1⟩
  have ha'ord : orderOf a' = 3 := by
    rw [← haord]
    exact (Subgroup.orderOf_coe a').symm
  have hzp : IsPGroup 3 (Subgroup.zpowers a') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ha'ord, pow_one]
  obtain ⟨S, hS⟩ := hzp.exists_le_sylow
  let P : Subgroup G := (S : Subgroup ↥Y).map Y.subtype
  have hPY : P ≤ Y := Subgroup.map_subtype_le _
  have hP3 : IsPGroup 3 P := S.isPGroup'.map Y.subtype
  have haP : a ∈ P := ⟨a', hS (Subgroup.mem_zpowers a'), rfl⟩
  have hPe : ∀ x ∈ P, x ^ 3 = 1 := fun x hx =>
    szN8_odd_pow_three hQe (hPY hx) (szN8_odd_of_three hP3 hx)
  obtain ⟨u, hu⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥Y) 2)
  obtain ⟨b, hb23, hb⟩ : ∃ b : ℕ, (b = 2 ∨ b = 3) ∧ Nat.card (OTwoQuot Y) = 3 ^ b := by
    rcases hQcard with h | h
    · exact ⟨2, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨3, Or.inr rfl, by rw [h]; norm_num⟩
  have hYcard : Nat.card ↥Y = 3 ^ b * 2 ^ u := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Y)
    rw [h]
    change Nat.card (OTwoQuot Y) * Nat.card (CFSG.Open.pCore 2 ↥Y) = _
    rw [hb, hu]
  have hPcard : Nat.card P = 3 ^ b := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, S.card_eq_multiplicity, hYcard,
      Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      Nat.factorization_pow, Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 2 by norm_num)]
  have hP𝒞N : P ≤ Subgroup.normalizer (szN8Cs L : Set G) := fun x hx =>
    szN8_normalizer_le_Cs L (hYN (hPY hx))
  have hinnerP : ∀ y ∈ P, ∃ x ∈ L, x⁻¹ * y ∈ szN8Cs L := by
    intro y hy
    obtain ⟨x, hxL, hx⟩ := hinner y (hPY hy) (szN8_odd_of_three hP3 hy)
    refine ⟨x, hxL, szN8_mem_Cs.mpr ⟨?_, hx⟩⟩
    exact (Subgroup.normalizer _).mul_mem
      ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer hxL)) (hYN (hPY hy))
  have hL𝒞 : L ⊓ szN8Cs L ≤ pCoreOf 2 L := fun x hx =>
    hZ x hx.1 (fun l hl => (szN8_mem_Cs.mp hx.2).2 l hl)
  have hL𝒞p : IsPGroup 2 ↥(L ⊓ szN8Cs L) := (pCoreOf_isPGroup 2 L).to_le hL𝒞
  have hS6 : Nat.card P ≤ 3 * Nat.card ↥(P ⊓ szN8Cs L) :=
    szN8_index_le_three hP3 hPe hP𝒞N hinnerP hL𝒞p hrank
  have hPAle : P ⊓ L ≤ oTwoUpper (Y ⊓ L) := fun x hx =>
    mem_oTwoUpper_of_odd ⟨hPY hx.1, hx.2⟩ (szN8_odd_of_three hP3 hx.1)
  have hPBle : P ⊓ szN8Cs L ≤ oTwoUpper (Y ⊓ szN8Cs L) := fun x hx =>
    mem_oTwoUpper_of_odd ⟨hPY hx.1, hx.2⟩ (szN8_odd_of_three hP3 hx.1)
  have hcomm : ∀ x ∈ P ⊓ L, ∀ y ∈ P ⊓ szN8Cs L, x * y = y * x := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L := (szN8_mem_Cs.mp hy.2).2 x hx.2
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem hx.1 hy.1) (P.inv_mem hx.1)) (P.inv_mem hy.1)
    have h3 := szN8_eq_one_of_three hP3 h2 h1
    exact commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact h3)
  have hPAB : (P ⊓ L) ⊓ (P ⊓ szN8Cs L) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ pCoreOf 2 L := hL𝒞 ⟨hx.1.2, hx.2.2⟩
    exact Subgroup.mem_bot.mpr (szN8_eq_one_of_three hP3 hx.1.1 h1)
  have hPAN : P ⊓ L ≤ Subgroup.normalizer ((P ⊓ szN8Cs L : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := hcomm x hx h hh
      have e : x * h * x⁻¹ = h := by rw [this]; group
      rwa [e]
    · intro hh
      have h1 := hcomm x⁻¹ ((P ⊓ L).inv_mem hx) _ hh
      have e : x⁻¹ * (x * h * x⁻¹) * x = h := by group
      have e2 : x⁻¹ * (x * h * x⁻¹) = (x * h * x⁻¹) * x⁻¹ := h1
      rw [e2] at e
      have e3 : (x * h * x⁻¹) * x⁻¹ * x = x * h * x⁻¹ := by group
      rw [e3] at e
      rwa [← e]
  have hcardAB := szN8_card_sup_mul_card_inf hPAN
  rw [hPAB, Subgroup.card_bot, mul_one] at hcardAB
  have hPA3 : Nat.card ↥(P ⊓ L) = 3 := by
    have hle := hrank (P ⊓ L) inf_le_right (hP3.to_inf_left) (fun x hx => hPe x hx.1)
    have hdvd : orderOf a ∣ Nat.card ↥(P ⊓ L) := Subgroup.orderOf_dvd_natCard (P ⊓ L) ⟨haP, haYL.2⟩
    rw [haord] at hdvd
    exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
  have hPeq : (P ⊓ L) ⊔ (P ⊓ szN8Cs L) = P := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
    rw [hcardAB, hPA3]
    exact hS6
  have hAY : oTwoUpper (Y ⊓ L) ≤ Y := (oTwoUpper_le _).trans inf_le_left
  have hBY : oTwoUpper (Y ⊓ szN8Cs L) ≤ Y := (oTwoUpper_le _).trans inf_le_left
  have hYA : Y ≤ Subgroup.normalizer (oTwoUpper (Y ⊓ L) : Set G) := fun y hy =>
    normalizer_le_normalizer_oTwoUpper _
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hYN hy⟩)
  have hYB : Y ≤ Subgroup.normalizer (oTwoUpper (Y ⊓ szN8Cs L) : Set G) := fun y hy =>
    normalizer_le_normalizer_oTwoUpper _
      (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy, szN8_normalizer_le_Cs L (hYN hy)⟩)
  have hYN' : Y ≤ Subgroup.normalizer
      ((oTwoUpper (Y ⊓ L) ⊔ oTwoUpper (Y ⊓ szN8Cs L) : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hYA hy, hYB hy⟩
  have hPN : P ≤ oTwoUpper (Y ⊓ L) ⊔ oTwoUpper (Y ⊓ szN8Cs L) :=
    hPeq.ge.trans (sup_le_sup hPAle hPBle)
  have hNY : oTwoUpper (Y ⊓ L) ⊔ oTwoUpper (Y ⊓ szN8Cs L) ≤ Y := sup_le hAY hBY
  have hPd : 3 ^ b ∣ Nat.card ↥(oTwoUpper (Y ⊓ L) ⊔ oTwoUpper (Y ⊓ szN8Cs L)) := by
    rw [← hPcard]
    exact Subgroup.card_dvd_of_le hPN
  obtain ⟨k, hk⟩ := hPd
  let N' : Subgroup ↥Y := (oTwoUpper (Y ⊓ L) ⊔ oTwoUpper (Y ⊓ szN8Cs L)).subgroupOf Y
  have hN'n : N'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYN'
  have hN'card : Nat.card ↥N' = Nat.card ↥(oTwoUpper (Y ⊓ L) ⊔ oTwoUpper (Y ⊓ szN8Cs L)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv
  have hidx : Nat.card ↥N' * N'.index = Nat.card ↥Y := Subgroup.card_mul_index N'
  rw [hN'card, hk, hYcard] at hidx
  have hke : k * N'.index = 2 ^ u := by
    have h3b : 0 < 3 ^ b := by positivity
    apply Nat.eq_of_mul_eq_mul_left h3b
    calc 3 ^ b * (k * N'.index) = 3 ^ b * k * N'.index := by ring
      _ = 3 ^ b * 2 ^ u := hidx
  have he : N'.index ∣ 2 ^ u := Dvd.intro_left k hke
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp he
  have hYle : Y ≤ oTwoUpper (Y ⊓ L) ⊔ oTwoUpper (Y ⊓ szN8Cs L) := by
    have h1 : oTwoUpper Y ≤ oTwoUpper (Y ⊓ L) ⊔ oTwoUpper (Y ⊓ szN8Cs L) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hy, hyo⟩
      have h1 : (⟨y, hy⟩ : ↥Y) ^ N'.index ∈ N' := Subgroup.pow_index_mem N' _
      have h2 : y ^ N'.index ∈ oTwoUpper (Y ⊓ L) ⊔ oTwoUpper (Y ⊓ szN8Cs L) :=
        Subgroup.mem_subgroupOf.mp h1
      rw [hj] at h2
      exact szN8_mem_of_two_pow_mem hyo h2
    calc Y = oTwoUpper Y := hY2.symm
      _ ≤ _ := h1
  refine ⟨le_antisymm hYle hNY, ?_⟩
  have hPB : 3 * Nat.card ↥(P ⊓ szN8Cs L) = 3 ^ b := by
    have h := hcardAB
    rw [hPeq, hPcard, hPA3] at h
    exact h.symm
  have hPAcomm : ∀ x ∈ P ⊓ L, ∀ y ∈ P ⊓ L, x * y = y * x := by
    have hcyc := isCyclic_of_prime_card (p := 3) hPA3
    intro x hx y hy
    exact congrArg Subtype.val (hcyc.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPBcomm : ∀ x ∈ P ⊓ szN8Cs L, ∀ y ∈ P ⊓ szN8Cs L, x * y = y * x := by
    rcases hb23 with rfl | rfl
    · have hc : Nat.card ↥(P ⊓ szN8Cs L) = 3 :=
        Nat.eq_of_mul_eq_mul_left (show 0 < 3 by norm_num) (hPB.trans (by norm_num))
      have hcyc := isCyclic_of_prime_card (p := 3) hc
      intro x hx y hy
      exact congrArg Subtype.val (hcyc.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · have hc : Nat.card ↥(P ⊓ szN8Cs L) = 3 ^ 2 :=
        Nat.eq_of_mul_eq_mul_left (show 0 < 3 by norm_num) (hPB.trans (by norm_num))
      have hcom := IsPGroup.isMulCommutative_of_card_eq_prime_sq hc
      intro x hx y hy
      exact congrArg Subtype.val (hcom.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right (P ⊓ L) (P ⊓ szN8Cs L) hPAN
    rw [hPeq] at hset
    have hx' : x ∈ ((P ⊓ L : Subgroup G) : Set G) * ((P ⊓ szN8Cs L : Subgroup G) : Set G) := by
      rw [← hset]; exact hx
    have hy' : y ∈ ((P ⊓ L : Subgroup G) : Set G) * ((P ⊓ szN8Cs L : Subgroup G) : Set G) := by
      rw [← hset]; exact hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx'
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy'
    have h11 : x₁ * y₁ = y₁ * x₁ := hPAcomm x₁ hx₁ y₁ hy₁
    have h22 : x₂ * y₂ = y₂ * x₂ := hPBcomm x₂ hx₂ y₂ hy₂
    have h12 : x₁ * y₂ = y₂ * x₁ := hcomm x₁ hx₁ y₂ hy₂
    have h21 : x₂ * y₁ = y₁ * x₂ := (hcomm y₁ hy₁ x₂ hx₂).symm
    calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by group
      _ = x₁ * (y₁ * x₂) * y₂ := by rw [h21]
      _ = (x₁ * y₁) * (x₂ * y₂) := by group
      _ = (y₁ * x₁) * (y₂ * x₂) := by rw [h11, h22]
      _ = y₁ * (x₁ * y₂) * x₂ := by group
      _ = y₁ * (y₂ * x₁) * x₂ := by rw [h12]
      _ = y₁ * y₂ * (x₁ * x₂) := by group
  have hQcomm : ∀ q₁ q₂ : OTwoQuot Y, q₁ * q₂ = q₂ * q₁ := by
    let φ : ↥(S : Subgroup ↥Y) →* OTwoQuot Y :=
      (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)).comp (S : Subgroup ↥Y).subtype
    have hφinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have h1 : ((x : ↥Y)) ∈ CFSG.Open.pCore 2 ↥Y := (QuotientGroup.eq_one_iff _).mp hx
      have h2 : ((x : ↥Y) : G) ∈ pCoreOf 2 Y := ⟨_, h1, rfl⟩
      have h3 : ((x : ↥Y) : G) ∈ P := ⟨_, x.2, rfl⟩
      have h4 := szN8_eq_one_of_three hP3 h3 h2
      refine Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext h4))
    have hcardS : Nat.card (OTwoQuot Y) ≤ Nat.card ↥(S : Subgroup ↥Y) := by
      have hmap : Nat.card ↥((S : Subgroup ↥Y).map Y.subtype) = Nat.card ↥(S : Subgroup ↥Y) :=
        Subgroup.card_map_of_injective Y.subtype_injective
      rw [hb, ← hmap]
      exact hPcard.ge
    have hφbij : Function.Bijective φ := hφinj.bijective_of_nat_card_le hcardS
    intro q₁ q₂
    obtain ⟨s₁, rfl⟩ := hφbij.2 q₁
    obtain ⟨s₂, rfl⟩ := hφbij.2 q₂
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact hPcomm _ ⟨_, s₁.2, rfl⟩ _ ⟨_, s₂.2, rfl⟩
  exact szN8_Q_comm_imp_E9 hQ hQcomm

end Decomp

end CFSG.Quasithin
