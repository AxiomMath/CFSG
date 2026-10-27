module

public import CFSG.Quasithin.Background.SmithB42Vacuous
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

@[expose] def B42TypeReeF4Large (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel (X ⧸ Subgroup.center X) .twistedF4 2 f

@[expose] def AsB42ReeF4Large : Prop := AsB42NoOffenderFor B42TypeReeF4Large

theorem AsB42NoOffenderFor.or {P Q : ∀ (X : Type) [Group X], Prop}
    (hP : AsB42NoOffenderFor P) (hQ : AsB42NoOffenderFor Q) :
    AsB42NoOffenderFor (fun (X : Type) [Group X] => P X ∨ Q X) := by
  intro V _ _ hV G L hHyp hPQ A hA
  rcases hPQ with h | h
  · exact hP V hV G L hHyp h A hA
  · exact hQ V hV G L hHyp h A hA

namespace B42Disp

open CFSG.QuasithinUnique.Setup.X5 CFSG.ComponentClassification

theorem exists_prime_orderOf_two_eq (n : ℕ) (hn : 2 ≤ n) (h6 : n ≠ 6) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ orderOf (2 : ZMod ℓ) = n := by
  obtain ⟨ℓ, hℓ, hdvd, hprim⟩ := Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one n hn h6
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h2 : 0 < 2 ^ (n - 1) := by positivity
    omega
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hcast : ∀ k : ℕ, ℓ ∣ 2 ^ k - 1 ↔ (2 : ZMod ℓ) ^ k = 1 := by
    intro k
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow, sub_eq_zero]
    push_cast
    rfl
  have h1 : (2 : ZMod ℓ) ^ n = 1 := (hcast n).1 hdvd
  have hpos : 0 < orderOf (2 : ZMod ℓ) :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, by omega, h1⟩)
  refine ⟨ℓ, hℓ, hℓ2, le_antisymm (Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one h1)) ?_⟩
  by_contra hlt
  push Not at hlt
  exact hprim _ hpos hlt ((hcast _).2 (pow_orderOf_eq_one _))

theorem dvd_orderOf_sq {G : Type*} [Monoid G] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {c : G}
    (h : ℓ ∣ orderOf c) : ℓ ∣ orderOf (c ^ 2) := by
  have h1 : orderOf c ∣ 2 * orderOf (c ^ 2) :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
  rcases (Nat.Prime.dvd_mul hℓ).1 (h.trans h1) with h2 | h2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h2) hℓ2
  · exact h2

theorem commute_of_comm_mem_center {H : Type*} [Group H]
    (hodd : Odd (Nat.card (Subgroup.center H))) {u w : H} (hu : u * u = 1)
    (hc : u * w * u⁻¹ * w⁻¹ ∈ Subgroup.center H) : u * w = w * u := by
  set z := u * w * u⁻¹ * w⁻¹ with hz
  have huw : u * w * u⁻¹ = z * w := by rw [hz]; group
  have hzc : ∀ g : H, g * z = z * g := fun g => (Subgroup.mem_center_iff.1 hc) g
  have hz2 : z * z = 1 := by
    have h1 : u * (u * w * u⁻¹) * u⁻¹ = w := by
      calc u * (u * w * u⁻¹) * u⁻¹ = (u * u) * w * (u * u)⁻¹ := by group
        _ = w := by rw [hu, one_mul, inv_one, mul_one]
    have h2 : u * (z * w) * u⁻¹ = z * (u * w * u⁻¹) := by
      calc u * (z * w) * u⁻¹ = (u * z) * w * u⁻¹ := by group
        _ = (z * u) * w * u⁻¹ := by rw [hzc u]
        _ = z * (u * w * u⁻¹) := by group
    have h3 : z * (z * w) = w := by
      calc z * (z * w) = z * (u * w * u⁻¹) := by rw [huw]
        _ = u * (z * w) * u⁻¹ := h2.symm
        _ = u * (u * w * u⁻¹) * u⁻¹ := by rw [huw]
        _ = w := h1
    have h4 : z * z * w = 1 * w := by rw [mul_assoc, h3, one_mul]
    exact mul_right_cancel h4
  have hz1 : z = 1 := by
    have := eq_one_of_involution_mem_odd hodd (C := Subgroup.center H) hc hz2
    exact this
  have : u * w * u⁻¹ = w := by rw [huw, hz1, one_mul]
  calc u * w = u * w * u⁻¹ * u := by group
    _ = w * u := by rw [this]

theorem sq_eq_one_of_mem_closure {H : Type*} [Group H] {S : Set H}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x * x = 1) :
    (∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x) ∧
      ∀ x ∈ Subgroup.closure S, x * x = 1 := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).2 fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => hcomm y hy x hx
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure S : Set H) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.1 (h1 hy) x hx).symm
  have hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x :=
    fun x hx y hy => (Subgroup.mem_centralizer_iff.1 (h2 hy) x hx)
  refine ⟨hc, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = x * x * (y * y) := by
          rw [mul_assoc, ← mul_assoc y x y, ← hc x hx y hy]; group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

section Space

variable {V : Type*} [CommGroup V]

theorem mem_fixV_closure {S : Set (MulAut V)} {v : V} :
    v ∈ fixV (Subgroup.closure S) ↔ ∀ s ∈ S, s v = v := by
  constructor
  · exact fun h s hs => h s (Subgroup.subset_closure hs)
  · intro h
    have hle : Subgroup.closure S ≤ MulAction.stabilizer (MulAut V) v :=
      (Subgroup.closure_le _).2 fun s hs => by
        rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact h s hs
    intro x hx
    have := hle hx
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

theorem fixV_sup (X Y : Subgroup (MulAut V)) : fixV (X ⊔ Y) = fixV X ⊓ fixV Y :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq X Y

theorem finite_mulAut [Finite V] : Finite (MulAut V) :=
  Finite.of_injective (fun σ : MulAut V => (σ : V → V)) DFunLike.coe_injective

theorem index_fixV_conjAut (k : MulAut V) (X : Subgroup (MulAut V)) :
    (fixV (B1.conjAut k X)).index = (fixV X).index := by
  rw [B1.fixV_conjAut]
  exact Subgroup.index_map_equiv _ k

variable [Finite V]

theorem index_fixV_le_card_of_le {E : Subgroup (MulAut V)}
    (hoff : Nat.card V ≤ Nat.card E * Nat.card (fixV E)) : (fixV E).index ≤ Nat.card E := by
  have h2 := (fixV E).card_mul_index
  have hpos : 0 < Nat.card (fixV E) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  rw [h2, mul_comm]
  exact hoff

theorem index_fixV_le_card {E : Subgroup (MulAut V)}
    (hoff : Nat.card V ≤ Nat.card E * Nat.card (fixV E)) {x : MulAut V} (hx : x ∈ E) :
    (fixV (Subgroup.zpowers x)).index ≤ Nat.card E :=
  (index_fixV_antitone ((Subgroup.zpowers_le).2 hx)).trans (index_fixV_le_card_of_le hoff)

theorem two_pow_le_index_of_dvd_orderOf (hV : ∀ v : V, v * v = 1) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) {g : MulAut V} (hg : ℓ ∣ orderOf g) :
    2 ^ orderOf (2 : ZMod ℓ) ≤ (fixV (Subgroup.zpowers g)).index := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite (MulAut V) := finite_mulAut
  obtain ⟨k, hk⟩ := hg
  have hpos : 0 < orderOf g := orderOf_pos g
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      omega
    · exact h
  have hc : (g ^ k) ^ ℓ = 1 := by
    rw [← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  have hc1 : g ^ k ≠ 1 := by
    intro h
    have h1 := Nat.le_of_dvd hk0 (hk ▸ orderOf_dvd_of_pow_eq_one h)
    have h3 := hℓ.two_le
    nlinarith
  calc 2 ^ orderOf (2 : ZMod ℓ) ≤ (fixV (Subgroup.zpowers (g ^ k))).index :=
        two_pow_orderOf_le_index_fixV hV hℓ2 hc hc1
    _ ≤ (fixV (Subgroup.zpowers g)).index :=
        index_fixV_antitone ((Subgroup.zpowers_le).2
          (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) k))

theorem index_fixV_prod_conj_le (x : MulAut V) (hs : List (MulAut V)) :
    (fixV (Subgroup.zpowers (hs.map fun h => h * x * h⁻¹).prod)).index ≤
      (fixV (Subgroup.zpowers x)).index ^ hs.length := by
  induction hs with
  | nil => simp [B1.fixV_bot]
  | cons h t ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    calc _ ≤ (fixV (Subgroup.zpowers (h * x * h⁻¹))).index *
          (fixV (Subgroup.zpowers (t.map fun h => h * x * h⁻¹).prod)).index :=
          index_fixV_mul_le _ _
      _ ≤ _ := by
          rw [index_fixV_conj]
          exact Nat.mul_le_mul_left _ ih

theorem two_pow_le_index_pow (hV : ∀ v : V, v * v = 1) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (x : MulAut V) (hs : List (MulAut V))
    (hdvd : ℓ ∣ orderOf (hs.map fun h => h * x * h⁻¹).prod) :
    2 ^ orderOf (2 : ZMod ℓ) ≤ (fixV (Subgroup.zpowers x)).index ^ hs.length :=
  (two_pow_le_index_of_dvd_orderOf hV hℓ hℓ2 hdvd).trans (index_fixV_prod_conj_le x hs)

theorem two_pow_le_index_sq_of_inverts (hV : ∀ v : V, v * v = 1) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) {x c : MulAut V} (hx : x * x = 1) (hxc : x * c * x⁻¹ = c⁻¹)
    (hc : ℓ ∣ orderOf c) :
    2 ^ orderOf (2 : ZMod ℓ) ≤ (fixV (Subgroup.zpowers x)).index ^ 2 := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have h1 : x * c⁻¹ * x = c := by
    calc x * c⁻¹ * x = x * c⁻¹ * x⁻¹ := by rw [hxi]
      _ = (x * c * x⁻¹)⁻¹ := by group
      _ = c := by rw [hxc, inv_inv]
  have hprod : ([1, c⁻¹].map fun h => h * x * h⁻¹).prod = c ^ 2 := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, inv_one, one_mul,
      mul_one, inv_inv]
    calc x * (c⁻¹ * x * c) = (x * c⁻¹ * x) * c := by group
      _ = c ^ 2 := by rw [h1, sq]
  have := two_pow_le_index_pow hV hℓ hℓ2 x [1, c⁻¹]
    (by rw [hprod]; exact dvd_orderOf_sq hℓ hℓ2 hc)
  simpa using this

theorem index_fixV_closure_conj_elt_le (x : MulAut V) (hs : List (MulAut V)) :
    (fixV (Subgroup.closure {y | ∃ h ∈ hs, y = h * x * h⁻¹})).index ≤
      (fixV (Subgroup.zpowers x)).index ^ hs.length := by
  set f : Fin hs.length → Subgroup V :=
    fun i => fixV (Subgroup.zpowers (hs.get i * x * (hs.get i)⁻¹)) with hf
  have hle : (⨅ i, f i) ≤ fixV (Subgroup.closure {y | ∃ h ∈ hs, y = h * x * h⁻¹}) := by
    intro v hv
    rw [mem_fixV_closure]
    rintro y ⟨h, hh, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hh
    exact mem_fixV_zpowers.1 ((Subgroup.mem_iInf.1 hv) i)
  calc _ ≤ (⨅ i, f i).index := Subgroup.index_antitone hle
    _ ≤ ∏ i, (f i).index := Subgroup.index_iInf_le f
    _ = (fixV (Subgroup.zpowers x)).index ^ hs.length := by
        simp only [hf, index_fixV_conj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem index_fixV_closure_conj_le (X : Subgroup (MulAut V)) (ks : List (MulAut V)) :
    (fixV (Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ X, y = k * a * k⁻¹})).index ≤
      (fixV X).index ^ ks.length := by
  set f : Fin ks.length → Subgroup V := fun i => fixV (B1.conjAut (ks.get i) X) with hf
  have hle : (⨅ i, f i) ≤ fixV (Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ X, y = k * a * k⁻¹}) := by
    intro v hv
    rw [mem_fixV_closure]
    rintro y ⟨k, hk, a, ha, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hk
    exact (Subgroup.mem_iInf.1 hv i) _ (B1.mem_conjAut.2 (by simpa [mul_assoc] using ha))
  calc _ ≤ (⨅ i, f i).index := Subgroup.index_antitone hle
    _ ≤ ∏ i, (f i).index := Subgroup.index_iInf_le f
    _ = (fixV X).index ^ ks.length := by
        simp only [hf, index_fixV_conjAut, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_le_index_pow_of_fixV_closure_eq_bot (x : MulAut V) (hs : List (MulAut V))
    (hfix : fixV (Subgroup.closure {y | ∃ h ∈ hs, y = h * x * h⁻¹}) = ⊥) :
    Nat.card V ≤ (fixV (Subgroup.zpowers x)).index ^ hs.length := by
  have h := index_fixV_closure_conj_elt_le x hs
  rwa [hfix, Subgroup.index_bot] at h

theorem weight_le_weight_sup {G B Λ : Subgroup (MulAut V)} (hB : IsFFStarOffender G B)
    (hc : ∀ x ∈ Λ, ∀ b ∈ B, x * b = b * x) :
    Nat.card Λ * Nat.card (fixV Λ) ≤ Nat.card (Λ ⊔ B : Subgroup (MulAut V)) *
      Nat.card (fixV (Λ ⊔ B)) := by
  have : Finite (MulAut V) := finite_mulAut
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Λ B hc
  obtain ⟨h2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (fixV Λ) (fixV B)
    (fun x _ y _ => mul_comm x y)
  have hle : fixV Λ ⊔ fixV B ≤ fixV (Λ ⊓ B) :=
    sup_le (fixV_antitone inf_le_left) (fixV_antitone inf_le_right)
  have h3 := Subgroup.card_le_of_le hle
  have h4 := hB.card_le (B := Λ ⊓ B) inf_le_right
  rw [fixV_sup]
  have hpos1 : 0 < Nat.card (Λ ⊓ B : Subgroup (MulAut V)) := Nat.card_pos
  have hpos2 : 0 < Nat.card (fixV Λ ⊔ fixV B : Subgroup V) := Nat.card_pos
  have hbd : Nat.card (Λ ⊓ B : Subgroup (MulAut V)) * Nat.card (fixV Λ ⊔ fixV B : Subgroup V) ≤
      Nat.card B * Nat.card (fixV B) := (Nat.mul_le_mul_left _ h3).trans h4
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos hpos1 hpos2)
  calc Nat.card Λ * Nat.card (fixV Λ) * (Nat.card (Λ ⊓ B : Subgroup (MulAut V)) *
        Nat.card (fixV Λ ⊔ fixV B : Subgroup V))
      ≤ Nat.card Λ * Nat.card (fixV Λ) * (Nat.card B * Nat.card (fixV B)) :=
        Nat.mul_le_mul_left _ hbd
    _ = (Nat.card (Λ ⊔ B : Subgroup (MulAut V)) * Nat.card (Λ ⊓ B : Subgroup (MulAut V))) *
        (Nat.card (fixV Λ ⊔ fixV B : Subgroup V) * Nat.card (fixV Λ ⊓ fixV B : Subgroup V)) := by
        rw [h1, h2]
        ring
    _ = Nat.card (Λ ⊔ B : Subgroup (MulAut V)) * Nat.card (fixV Λ ⊓ fixV B : Subgroup V) *
        (Nat.card (Λ ⊓ B : Subgroup (MulAut V)) * Nat.card (fixV Λ ⊔ fixV B : Subgroup V)) := by
        ring

theorem card_le_weight_closure_conj {G A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A)
    (ks : List (MulAut V)) (hks : ∀ k ∈ ks, k ∈ G)
    (hcomm : ∀ k ∈ ks, ∀ k' ∈ ks, ∀ a ∈ A, ∀ b ∈ A,
      k * a * k⁻¹ * (k' * b * k'⁻¹) = k' * b * k'⁻¹ * (k * a * k⁻¹)) :
    Nat.card V ≤ Nat.card (Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹}) *
      Nat.card (fixV (Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹})) := by
  induction ks with
  | nil =>
    have h : {y : MulAut V | ∃ k ∈ ([] : List (MulAut V)), ∃ a ∈ A, y = k * a * k⁻¹} = ∅ := by
      ext y
      simp
    rw [h, Subgroup.closure_empty, B1.card_bot_mul_card_fixV]
  | cons k ks ih =>
    have ih' := ih (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk'))
      (fun k₁ h₁ k₂ h₂ => hcomm k₁ (List.mem_cons_of_mem _ h₁) k₂ (List.mem_cons_of_mem _ h₂))
    set Λ := Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹} with hΛ
    have hset : {y | ∃ k' ∈ k :: ks, ∃ a ∈ A, y = k' * a * k'⁻¹} =
        {y | ∃ k' ∈ ks, ∃ a ∈ A, y = k' * a * k'⁻¹} ∪ (B1.conjAut k A : Set (MulAut V)) := by
      ext y
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union, SetLike.mem_coe,
        B1.mem_conjAut]
      constructor
      · rintro ⟨k', hk' | hk', a, ha, rfl⟩
        · subst hk'
          right
          simpa [mul_assoc] using ha
        · exact Or.inl ⟨k', hk', a, ha, rfl⟩
      · rintro (⟨k', hk', a, ha, rfl⟩ | h)
        · exact ⟨k', Or.inr hk', a, ha, rfl⟩
        · exact ⟨k, Or.inl rfl, k⁻¹ * y * k, h, by group⟩
    have hcl : Subgroup.closure {y | ∃ k' ∈ k :: ks, ∃ a ∈ A, y = k' * a * k'⁻¹} =
        Λ ⊔ B1.conjAut k A := by
      rw [hset, Subgroup.closure_union, Subgroup.closure_eq]
    rw [hcl]
    have hc : ∀ x ∈ Λ, ∀ b ∈ B1.conjAut k A, x * b = b * x := by
      intro x hx b hb
      have hle : Λ ≤ Subgroup.centralizer (B1.conjAut k A : Set (MulAut V)) := by
        rw [hΛ, Subgroup.closure_le]
        rintro _ ⟨k', hk', a, ha, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro b' hb'
        have hb'' := B1.mem_conjAut.1 hb'
        have := hcomm k (List.mem_cons_self ..) k' (List.mem_cons_of_mem _ hk') _ hb'' a ha
        calc b' * (k' * a * k'⁻¹) = k * (k⁻¹ * b' * k) * k⁻¹ * (k' * a * k'⁻¹) := by group
          _ = k' * a * k'⁻¹ * (k * (k⁻¹ * b' * k) * k⁻¹) := this
          _ = k' * a * k'⁻¹ * b' := by group
      exact ((Subgroup.mem_centralizer_iff.1 (hle hx)) b hb).symm
    exact ih'.trans (weight_le_weight_sup
      (B1.isFFStarOffender_conjAut hA (hks k (List.mem_cons_self ..))) hc)

end Space

section Model

variable {V : Type*} [CommGroup V] (L : Subgroup (MulAut V)) {M : Type*} [Group M]
  (e : L ⧸ Subgroup.center L ≃* M)

@[expose] noncomputable def modelAct : Subgroup.normalizer (L : Set (MulAut V)) →* MulAut M :=
  (MulAut.congr e).toMonoidHom.comp (normalizerAct L)

@[expose] noncomputable def modelProj : L →* M :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))

theorem modelProj_apply (l : L) : modelProj L e l = e (QuotientGroup.mk l) := rfl

theorem modelProj_surjective : Function.Surjective (modelProj L e) := by
  intro m
  obtain ⟨q, rfl⟩ := e.surjective m
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨l, rfl⟩

theorem mem_center_of_modelProj_eq_one {l : L} (hl : modelProj L e l = 1) :
    l ∈ Subgroup.center L := by
  rw [modelProj_apply, ← map_one e] at hl
  exact (QuotientGroup.eq_one_iff l).1 (e.injective hl)

theorem modelAct_apply (a : Subgroup.normalizer (L : Set (MulAut V))) :
    modelAct L e a = MulAut.congr e (normalizerAct L a) := rfl

theorem modelAct_apply_mk (a : Subgroup.normalizer (L : Set (MulAut V))) (x : L) :
    modelAct L e a (e (QuotientGroup.mk x)) = e (QuotientGroup.mk (conjOn L a x)) := by
  rw [modelAct_apply, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [normalizerAct_apply_mk]

theorem modelAct_of_mem {l : MulAut V} (hl : l ∈ L) :
    modelAct L e ⟨l, Subgroup.le_normalizer hl⟩ =
      MulAut.conj (e (QuotientGroup.mk ⟨l, hl⟩)) := by
  rw [modelAct_apply, normalizerAct_of_mem L hl, OuterAutomorphisms.congr_conj]

theorem exists_lift (m : M) : ∃ l : L, e (QuotientGroup.mk l) = m :=
  modelProj_surjective L e m

theorem exists_modelAct_eq_conj (m : M) :
    ∃ h : Subgroup.normalizer (L : Set (MulAut V)), (h : MulAut V) ∈ L ∧
      modelAct L e h = MulAut.conj m := by
  obtain ⟨l, rfl⟩ := exists_lift L e m
  exact ⟨⟨l, Subgroup.le_normalizer l.2⟩, l.2, modelAct_of_mem L e l.2⟩

include e in
theorem center_eq_bot [Group.IsPerfect L] : Subgroup.center M = ⊥ := by
  have h := Group.IsPerfect.center_quotient_center_eq_bot L
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ Subgroup.center (L ⧸ Subgroup.center L) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz (e g)
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot, ← e.apply_symm_apply z, hz', map_one]

theorem eq_one_of_modelAct_eq_one [Group.IsPerfect L]
    (hodd : Odd (Nat.card (Subgroup.centralizer (L : Set (MulAut V)))))
    {a : Subgroup.normalizer (L : Set (MulAut V))} (ha2 : (a : MulAut V) * a = 1)
    (ha : modelAct L e a = 1) : (a : MulAut V) = 1 := by
  refine eq_one_of_normalizerAct_eq_one L hodd ha2 ((MulAut.congr e).injective ?_)
  rw [← modelAct_apply, ha, map_one]

theorem odd_card_center (hodd : Odd (Nat.card (Subgroup.centralizer (L : Set (MulAut V))))) :
    Odd (Nat.card (Subgroup.center L)) := by
  let ι : Subgroup.center L →* Subgroup.centralizer (L : Set (MulAut V)) :=
    (L.subtype.comp (Subgroup.center L).subtype).codRestrict _ (fun z =>
      Subgroup.mem_centralizer_iff.mpr fun g hg => by
        have := (Subgroup.mem_center_iff.mp z.2) ⟨g, hg⟩
        exact congrArg Subtype.val this)
  have hinj : Function.Injective ι := fun x y hxy => by
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective ι hinj)

@[expose] noncomputable def restrictAct {E : Subgroup (MulAut V)}
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) : E →* MulAut M :=
  (modelAct L e).comp (Subgroup.inclusion hEN)

theorem restrictAct_injective [Group.IsPerfect L]
    (hodd : Odd (Nat.card (Subgroup.centralizer (L : Set (MulAut V)))))
    {E : Subgroup (MulAut V)} (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V)))
    (hEa : IsElemAbelian2 E) : Function.Injective (restrictAct L e hEN) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h2 : (a : MulAut V) * a = 1 := by rw [← sq]; exact hEa.2 a a.2
  exact Subtype.ext (eq_one_of_modelAct_eq_one L e hodd (a := Subgroup.inclusion hEN a) h2 ha)

end Model

theorem conj_injective {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : g ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun φ : MulAut M => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  rwa [hZ, Subgroup.mem_bot] at hg'

@[expose] def IsElem2 {X : Type*} [Group X] (F : Subgroup X) : Prop :=
  (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) ∧ ∀ a ∈ F, a ^ 2 = 1

@[expose] def DispAt (M : Type*) [Group M] (α : MulAut M) (n : ℕ) : Prop :=
  ∃ (ℓ : ℕ) (ms : List M), ℓ.Prime ∧ ℓ ≠ 2 ∧
    ℓ ∣ orderOf (ms.map fun m => MulAut.conj m * α * (MulAut.conj m)⁻¹).prod ∧
    n ^ ms.length < 2 ^ orderOf (2 : ZMod ℓ)

@[expose] def GenAt (M : Type*) [Group M] (α : MulAut M) (n : ℕ) : Prop :=
  ∃ (ℓ : ℕ) (ms : List M), ℓ.Prime ∧ ℓ ≠ 2 ∧
    (∃ β ∈ Subgroup.closure {γ | ∃ m ∈ ms, γ = MulAut.conj m * α * (MulAut.conj m)⁻¹},
      ℓ ∣ orderOf β) ∧
    n ^ ms.length < 2 ^ orderOf (2 : ZMod ℓ)

@[expose] def LineGenAt (M : Type*) [Group M] (E : Subgroup M) : Prop :=
  ∃ (ℓ : ℕ) (hs gs : List M), ℓ.Prime ∧ ℓ ≠ 2 ∧
    (∀ h ∈ hs, ∀ h' ∈ hs, ∀ a ∈ E, ∀ b ∈ E,
      h * a * h⁻¹ * (h' * b * h'⁻¹) = h' * b * h'⁻¹ * (h * a * h⁻¹)) ∧
    (∃ c ∈ Subgroup.closure {y | ∃ g ∈ gs, ∃ h ∈ hs, ∃ a ∈ E, y = g * (h * a * h⁻¹) * g⁻¹},
      ℓ ∣ orderOf c) ∧
    Nat.card (Subgroup.closure {y | ∃ h ∈ hs, ∃ a ∈ E, y = h * a * h⁻¹}) ^ gs.length <
      2 ^ orderOf (2 : ZMod ℓ)

@[expose] def DispCriterion (M : Type*) [Group M] : Prop :=
  ∀ F : Subgroup (MulAut M), F ≠ ⊥ → IsElem2 F →
    (∃ α ∈ F, α ≠ 1 ∧ (DispAt M α (Nat.card F) ∨ GenAt M α (Nat.card F))) ∨
      (F ≤ (MulAut.conj : M →* MulAut M).range ∧ LineGenAt M (F.comap MulAut.conj))

theorem DispAt.mono {M : Type*} [Group M] {α : MulAut M} {n n' : ℕ} (h : DispAt M α n)
    (hn : n' ≤ n) : DispAt M α n' := by
  obtain ⟨ℓ, ms, hℓ, hℓ2, hdvd, hlt⟩ := h
  exact ⟨ℓ, ms, hℓ, hℓ2, hdvd, (Nat.pow_le_pow_left hn _).trans_lt hlt⟩

theorem GenAt.mono {M : Type*} [Group M] {α : MulAut M} {n n' : ℕ} (h : GenAt M α n)
    (hn : n' ≤ n) : GenAt M α n' := by
  obtain ⟨ℓ, ms, hℓ, hℓ2, hβ, hlt⟩ := h
  exact ⟨ℓ, ms, hℓ, hℓ2, hβ, (Nat.pow_le_pow_left hn _).trans_lt hlt⟩

theorem DispAt.genAt {M : Type*} [Group M] {α : MulAut M} {n : ℕ} (h : DispAt M α n) :
    GenAt M α n := by
  obtain ⟨ℓ, ms, hℓ, hℓ2, hdvd, hlt⟩ := h
  refine ⟨ℓ, ms, hℓ, hℓ2, ⟨_, Subgroup.list_prod_mem _ ?_, hdvd⟩, hlt⟩
  intro γ hγ
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hγ
  exact Subgroup.subset_closure ⟨m, hm, rfl⟩

theorem dispAt_conj {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥) {ξ : M} {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (ms : List M)
    (hdvd : ℓ ∣ orderOf (ms.map fun m => m * ξ * m⁻¹).prod) {n : ℕ}
    (hlt : n ^ ms.length < 2 ^ orderOf (2 : ZMod ℓ)) : DispAt M (MulAut.conj ξ) n := by
  refine ⟨ℓ, ms, hℓ, hℓ2, ?_, hlt⟩
  have h : (ms.map fun m => MulAut.conj m * MulAut.conj ξ * (MulAut.conj m)⁻¹).prod =
      MulAut.conj (ms.map fun m => m * ξ * m⁻¹).prod := by
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun m _ => ?_
    simp [map_mul, map_inv]
  rw [h, orderOf_injective _ (conj_injective hZ)]
  exact hdvd

theorem dispAt_of_inverts {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥) {α : MulAut M}
    (hα : α * α = 1) {c : M} (hc : α c = c⁻¹) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hdvd : ℓ ∣ orderOf c) {n : ℕ} (hlt : n ^ 2 < 2 ^ orderOf (2 : ZMod ℓ)) :
    DispAt M α n := by
  refine ⟨ℓ, [1, c⁻¹], hℓ, hℓ2, ?_, by simpa using hlt⟩
  have hα' : ∀ y, α (α y) = y := fun y => by
    rw [← MulAut.mul_apply, hα, MulAut.one_apply]
  have hci : α c⁻¹ = c := by rw [map_inv, hc, inv_inv]
  have h : ([1, c⁻¹].map fun m => MulAut.conj m * α * (MulAut.conj m)⁻¹).prod =
      MulAut.conj (c ^ 2) := by
    ext y
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, map_one, one_mul,
      inv_one, mul_one, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul,
      map_inv, inv_inv, hα', hc, hci]
    rw [sq]
    group
  rw [h, orderOf_injective _ (conj_injective hZ)]
  exact dvd_orderOf_sq hℓ hℓ2 hdvd

theorem card_comap_conj {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥)
    {F : Subgroup (MulAut M)} (hF : F ≤ (MulAut.conj : M →* MulAut M).range) :
    Nat.card (F.comap MulAut.conj) = Nat.card F := by
  have h := Subgroup.card_map_of_injective (K := F.comap MulAut.conj) (conj_injective hZ)
  rw [Subgroup.map_comap_eq_self hF] at h
  exact h.symm

theorem isElem2_comap_conj {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥)
    {F : Subgroup (MulAut M)} (hF : IsElem2 F) : IsElem2 (F.comap MulAut.conj) := by
  refine ⟨fun a ha b hb => conj_injective hZ ?_, fun a ha => conj_injective hZ ?_⟩
  · rw [map_mul, map_mul]
    exact hF.1 _ ha _ hb
  · rw [map_pow, map_one]
    exact hF.2 _ ha

theorem dispCriterion_of_classes {M : Type*} [Group M] (hZ : Subgroup.center M = ⊥)
    (B : M → Prop) (r rA s : ℕ)
    (hrank : ∀ E : Subgroup M, IsElem2 E → Nat.card E ≤ 2 ^ r)
    (hpure : ∀ E : Subgroup M, IsElem2 E → (∀ ξ ∈ E, ξ ≠ 1 → ¬ B ξ) → Nat.card E ≤ 2 ^ rA)
    (hindex : ∀ F : Subgroup (MulAut M), IsElem2 F →
      Nat.card F ≤ 2 ^ s * Nat.card (F ⊓ (MulAut.conj : M →* MulAut M).range : Subgroup _))
    (hB : ∀ ξ : M, ξ * ξ = 1 → ξ ≠ 1 → B ξ →
      DispAt M (MulAut.conj ξ) (2 ^ (r + s)) ∨ GenAt M (MulAut.conj ξ) (2 ^ (r + s)))
    (hout : ∀ α : MulAut M, α * α = 1 → α ∉ (MulAut.conj : M →* MulAut M).range →
      DispAt M α (2 ^ (rA + s)) ∨ GenAt M α (2 ^ (rA + s)))
    (hA : ∀ E : Subgroup M, E ≠ ⊥ → IsElem2 E → (∀ ξ ∈ E, ξ ≠ 1 → ¬ B ξ) →
      (∃ ξ ∈ E, ξ ≠ 1 ∧
        (DispAt M (MulAut.conj ξ) (2 ^ rA) ∨ GenAt M (MulAut.conj ξ) (2 ^ rA))) ∨
      LineGenAt M E) :
    DispCriterion M := by
  intro F hF1 hFa
  have hsq : ∀ α ∈ F, α * α = 1 := fun α hα => by rw [← sq]; exact hFa.2 α hα
  set F₀ := F ⊓ (MulAut.conj : M →* MulAut M).range with hF₀
  set E₀ := F₀.comap MulAut.conj with hE₀
  have hF₀le : F₀ ≤ (MulAut.conj : M →* MulAut M).range := inf_le_right
  have hF₀a : IsElem2 F₀ :=
    ⟨fun a ha b hb => hFa.1 a ha.1 b hb.1, fun a ha => hFa.2 a ha.1⟩
  have hE₀a : IsElem2 E₀ := isElem2_comap_conj hZ hF₀a
  have hE₀card : Nat.card E₀ = Nat.card F₀ := card_comap_conj hZ hF₀le
  have hFle := hindex F hFa
  have hmemE₀ : ∀ ξ : M, ξ ∈ E₀ ↔ MulAut.conj ξ ∈ F := fun ξ =>
    ⟨fun h => h.1, fun h => ⟨h, ξ, rfl⟩⟩
  have hconj1 : ∀ ξ : M, ξ ≠ 1 → MulAut.conj ξ ≠ 1 := fun ξ hξ h =>
    hξ (conj_injective hZ (by rw [h, map_one]))
  by_cases hexB : ∃ ξ ∈ E₀, ξ ≠ 1 ∧ B ξ
  ·
    obtain ⟨ξ, hξ, hξ1, hξB⟩ := hexB
    have hξ2 : ξ * ξ = 1 := by rw [← sq]; exact hE₀a.2 ξ hξ
    have hcard : Nat.card F ≤ 2 ^ (r + s) := by
      rw [pow_add, mul_comm]
      exact hFle.trans (Nat.mul_le_mul_left _ (hE₀card ▸ hrank E₀ hE₀a))
    refine Or.inl ⟨MulAut.conj ξ, (hmemE₀ ξ).1 hξ, hconj1 ξ hξ1, ?_⟩
    rcases hB ξ hξ2 hξ1 hξB with h | h
    · exact Or.inl (h.mono hcard)
    · exact Or.inr (h.mono hcard)
  · push Not at hexB
    have hE₀pure : Nat.card E₀ ≤ 2 ^ rA := hpure E₀ hE₀a hexB
    by_cases hexO : ∃ α ∈ F, α ∉ (MulAut.conj : M →* MulAut M).range
    ·
      obtain ⟨α, hαF, hαO⟩ := hexO
      have hα1 : α ≠ 1 := fun h => hαO (h ▸ Subgroup.one_mem _)
      have hcard : Nat.card F ≤ 2 ^ (rA + s) := by
        rw [pow_add, mul_comm]
        exact hFle.trans (Nat.mul_le_mul_left _ (hE₀card ▸ hE₀pure))
      refine Or.inl ⟨α, hαF, hα1, ?_⟩
      rcases hout α (hsq α hαF) hαO with h | h
      · exact Or.inl (h.mono hcard)
      · exact Or.inr (h.mono hcard)
    ·
      push Not at hexO
      have hFinner : F ≤ (MulAut.conj : M →* MulAut M).range := fun α hα => hexO α hα
      have hFF₀ : F₀ = F := le_antisymm inf_le_left (le_inf le_rfl hFinner)
      have hcard : Nat.card F ≤ 2 ^ rA := by rw [← hFF₀, ← hE₀card]; exact hE₀pure
      have hE₀1 : E₀ ≠ ⊥ := by
        intro h
        apply hF1
        rw [eq_bot_iff]
        intro α hα
        obtain ⟨ξ, rfl⟩ := hFinner hα
        have : ξ ∈ E₀ := (hmemE₀ ξ).2 hα
        rw [h, Subgroup.mem_bot] at this
        rw [this, map_one]
        exact Subgroup.one_mem _
      rcases hA E₀ hE₀1 hE₀a hexB with ⟨ξ, hξ, hξ1, h⟩ | h
      · refine Or.inl ⟨MulAut.conj ξ, (hmemE₀ ξ).1 hξ, hconj1 ξ hξ1, ?_⟩
        rcases h with h | h
        · exact Or.inl (h.mono hcard)
        · exact Or.inr (h.mono hcard)
      · right
        refine ⟨hFinner, ?_⟩
        have hE : E₀ = F.comap MulAut.conj := by rw [hE₀, hFF₀]
        rwa [← hE]

section Offender

variable {V : Type*} [CommGroup V] [Finite V]

theorem lt_index_of_genAt (hV : ∀ v : V, v * v = 1) (L : Subgroup (MulAut V)) {M : Type*}
    [Group M] (e : L ⧸ Subgroup.center L ≃* M) (x : Subgroup.normalizer (L : Set (MulAut V)))
    {n : ℕ} (h : GenAt M (modelAct L e x) n) :
    n < (fixV (Subgroup.zpowers (x : MulAut V))).index := by
  obtain ⟨ℓ, ms, hℓ, hℓ2, ⟨β, hβ, hdvd⟩, hlt⟩ := h
  choose lift hliftL hlift using fun m : M => exists_modelAct_eq_conj L e m
  set S : Set (Subgroup.normalizer (L : Set (MulAut V))) :=
    {y | ∃ m ∈ ms, y = lift m * x * (lift m)⁻¹} with hS
  have hmap : (Subgroup.closure S).map (modelAct L e) =
      Subgroup.closure {γ | ∃ m ∈ ms, γ = MulAut.conj m * modelAct L e x *
        (MulAut.conj m)⁻¹} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext γ
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨m, hm, by rw [map_mul, map_mul, map_inv, hlift]⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨_, ⟨m, hm, rfl⟩, by rw [map_mul, map_mul, map_inv, hlift]⟩
  rw [← hmap] at hβ
  obtain ⟨y, hy, rfl⟩ := hβ
  have hdvd' : ℓ ∣ orderOf (y : MulAut V) := by
    rw [Subgroup.orderOf_coe]
    exact hdvd.trans (orderOf_map_dvd _ _)
  have hyY : (y : MulAut V) ∈ Subgroup.closure
      {z | ∃ h ∈ ms.map fun m => (lift m : MulAut V), z = h * (x : MulAut V) * h⁻¹} := by
    have hle : (Subgroup.closure S).map (Subgroup.normalizer (L : Set (MulAut V))).subtype ≤
        Subgroup.closure
          {z | ∃ h ∈ ms.map fun m => (lift m : MulAut V), z = h * (x : MulAut V) * h⁻¹} := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      exact Subgroup.subset_closure ⟨(lift m : MulAut V), List.mem_map_of_mem hm, rfl⟩
    exact hle ⟨y, hy, rfl⟩
  have h1 := two_pow_le_index_of_dvd_orderOf hV hℓ hℓ2 hdvd'
  have h2 := index_fixV_antitone ((Subgroup.zpowers_le).2 hyY)
  have h3 := index_fixV_closure_conj_elt_le (x : MulAut V) (ms.map fun m => (lift m : MulAut V))
  rw [List.length_map] at h3
  by_contra hle
  push Not at hle
  have h4 := Nat.pow_le_pow_left hle ms.length
  omega

theorem false_of_lineGenAt [Nontrivial V] (hV : ∀ v : V, v * v = 1) (L : Subgroup (MulAut V))
    (hirr : ∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {M : Type*} [Group M] (e : L ⧸ Subgroup.center L ≃* M) {G A : Subgroup (MulAut V)}
    (hLG : L ≤ G) (hA : IsFFStarOffender G A) (hAL : A ≤ L)
    (hE : LineGenAt M ((A.subgroupOf L).map (modelProj L e))) : False := by
  obtain ⟨ℓ, hs, gs, hℓ, hℓ2, hcomm, ⟨c, hc, hdvd⟩, hlt⟩ := hE
  have : Finite (MulAut V) := finite_mulAut
  have : Finite M := Finite.of_equiv _ e.toEquiv
  set π := modelProj L e with hπdef
  set E := (A.subgroupOf L).map π with hEdef
  have hZodd := odd_card_center L (centralizer_odd hV L hirr)
  choose lt hlt' using fun m : M => modelProj_surjective L e m
  have hπlt : ∀ m : M, π (lt m) = m := fun m => hlt' m
  have hAsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hA.2.2.1.2 a ha
  set ks : List (MulAut V) := hs.map fun h => (lt h : MulAut V) with hks
  have hksG : ∀ k ∈ ks, k ∈ G := by
    intro k hk
    obtain ⟨h, -, rfl⟩ := List.mem_map.1 hk
    exact hLG (lt h).2
  have hcommL : ∀ h ∈ hs, ∀ h' ∈ hs, ∀ a : L, (a : MulAut V) ∈ A → ∀ b : L,
      (b : MulAut V) ∈ A → lt h * a * (lt h)⁻¹ * (lt h' * b * (lt h')⁻¹) =
        lt h' * b * (lt h')⁻¹ * (lt h * a * (lt h)⁻¹) := by
    intro h hh h' hh' a ha b hb
    apply commute_of_comm_mem_center hZodd
    · have : a * a = 1 := Subtype.ext (by simpa using hAsq a ha)
      calc lt h * a * (lt h)⁻¹ * (lt h * a * (lt h)⁻¹) = lt h * (a * a) * (lt h)⁻¹ := by group
        _ = 1 := by rw [this, mul_one, mul_inv_cancel]
    · apply mem_center_of_modelProj_eq_one L e
      have hcm := hcomm h hh h' hh' (π a) ⟨a, ha, rfl⟩ (π b) ⟨b, hb, rfl⟩
      simp only [map_mul, map_inv, hlt']
      rw [← hπdef, hcm]
      group
  have hcommV : ∀ k ∈ ks, ∀ k' ∈ ks, ∀ a ∈ A, ∀ b ∈ A,
      k * a * k⁻¹ * (k' * b * k'⁻¹) = k' * b * k'⁻¹ * (k * a * k⁻¹) := by
    intro k hk k' hk' a ha b hb
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hk
    obtain ⟨h', hh', rfl⟩ := List.mem_map.1 hk'
    exact congrArg Subtype.val (hcommL h hh h' hh' ⟨a, hAL ha⟩ ha ⟨b, hAL hb⟩ hb)
  set ΛV := Subgroup.closure {y | ∃ k ∈ ks, ∃ a ∈ A, y = k * a * k⁻¹} with hΛV
  have hweight : Nat.card V ≤ Nat.card ΛV * Nat.card (fixV ΛV) :=
    card_le_weight_closure_conj hA ks hksG hcommV
  set Λ := Subgroup.closure {y | ∃ h ∈ hs, ∃ a ∈ E, y = h * a * h⁻¹} with hΛ
  set SL : Set L := {y | ∃ h ∈ hs, ∃ a : L, (a : MulAut V) ∈ A ∧ y = lt h * a * (lt h)⁻¹}
    with hSL
  have hΛVmap : ΛV = (Subgroup.closure SL).map L.subtype := by
    rw [MonoidHom.map_closure, hΛV]
    congr 1
    ext y
    constructor
    · rintro ⟨k, hk, a, ha, rfl⟩
      obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hk
      exact ⟨_, ⟨h, hh, ⟨a, hAL ha⟩, ha, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨h, hh, a, ha, rfl⟩, rfl⟩
      exact ⟨(lt h : MulAut V), List.mem_map_of_mem hh, a, ha, rfl⟩
  have hSLcomm : ∀ x ∈ SL, ∀ y ∈ SL, x * y = y * x := by
    rintro _ ⟨h, hh, a, ha, rfl⟩ _ ⟨h', hh', b, hb, rfl⟩
    exact hcommL h hh h' hh' a ha b hb
  have hSLsq : ∀ x ∈ SL, x * x = 1 := by
    rintro _ ⟨h, hh, a, ha, rfl⟩
    have : a * a = 1 := Subtype.ext (by simpa using hAsq a ha)
    calc lt h * a * (lt h)⁻¹ * (lt h * a * (lt h)⁻¹) = lt h * (a * a) * (lt h)⁻¹ := by group
      _ = 1 := by rw [this, mul_one, mul_inv_cancel]
  have hcardΛ : Nat.card ΛV ≤ Nat.card Λ := by
    have hinj : Set.InjOn π (Subgroup.closure SL : Set L) := by
      intro x hx y hy hxy
      have hxy' : π (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
      have hz := mem_center_of_modelProj_eq_one L e hxy'
      have hmem : x * y⁻¹ ∈ Subgroup.closure SL := mul_mem hx (inv_mem hy)
      have h2 := (sq_eq_one_of_mem_closure hSLcomm hSLsq).2 _ hmem
      have h1 := eq_one_of_involution_mem_odd hZodd (C := Subgroup.center L) hz h2
      exact mul_inv_eq_one.1 h1
    have hle : (Subgroup.closure SL).map π ≤ Λ := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨h, hh, a, ha, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨h, hh, π a, ⟨a, ha, rfl⟩, ?_⟩
      rw [map_mul, map_mul, map_inv, hlt']
    calc Nat.card ΛV = Nat.card (Subgroup.closure SL) := by
          rw [hΛVmap]
          exact Subgroup.card_map_of_injective L.subtype_injective
      _ = Nat.card ((Subgroup.closure SL).map π) := by
          have := Nat.card_image_of_injOn hinj
          rw [← Subgroup.coe_map] at this
          exact this.symm
      _ ≤ Nat.card Λ := Subgroup.card_le_of_le hle
  set gks : List (MulAut V) := gs.map fun g => (lt g : MulAut V) with hgks
  set YV := Subgroup.closure {y | ∃ k ∈ gks, ∃ a ∈ ΛV, y = k * a * k⁻¹} with hYV
  set TL : Set L := {y | ∃ g ∈ gs, ∃ h ∈ hs, ∃ a : L, (a : MulAut V) ∈ A ∧
    y = lt g * (lt h * a * (lt h)⁻¹) * (lt g)⁻¹} with hTL
  have hTLmap : (Subgroup.closure TL).map π =
      Subgroup.closure {y | ∃ g ∈ gs, ∃ h ∈ hs, ∃ a ∈ E, y = g * (h * a * h⁻¹) * g⁻¹} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨g, hg, h, hh, a, ha, rfl⟩, rfl⟩
      exact ⟨g, hg, h, hh, π a, ⟨a, ha, rfl⟩, by simp only [map_mul, map_inv, hπlt]⟩
    · rintro ⟨g, hg, h, hh, _, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨_, ⟨g, hg, h, hh, a, ha, rfl⟩, by simp only [map_mul, map_inv, hπlt]⟩
  rw [← hTLmap] at hc
  obtain ⟨y, hy, rfl⟩ := hc
  have hdvd' : ℓ ∣ orderOf (y : MulAut V) := by
    rw [Subgroup.orderOf_coe]
    exact hdvd.trans (orderOf_map_dvd _ _)
  have hyY : (y : MulAut V) ∈ YV := by
    have hle : (Subgroup.closure TL).map L.subtype ≤ YV := by
      rw [MonoidHom.map_closure, hYV, Subgroup.closure_le]
      rintro _ ⟨_, ⟨g, hg, h, hh, a, ha, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨(lt g : MulAut V), List.mem_map_of_mem hg,
        (lt h : MulAut V) * a * (lt h : MulAut V)⁻¹, ?_, rfl⟩
      exact Subgroup.subset_closure ⟨(lt h : MulAut V), List.mem_map_of_mem hh, a, ha, rfl⟩
    exact hle ⟨y, hy, rfl⟩
  have h1 := two_pow_le_index_of_dvd_orderOf hV hℓ hℓ2 hdvd'
  have h2 := index_fixV_antitone ((Subgroup.zpowers_le).2 hyY)
  have h3 : (fixV YV).index ≤ (fixV ΛV).index ^ gs.length := by
    have := index_fixV_closure_conj_le ΛV gks
    rwa [hgks, List.length_map] at this
  have h4 := index_fixV_le_card_of_le hweight
  have h5 := Nat.pow_le_pow_left (h4.trans hcardΛ) gs.length
  omega

variable [Nontrivial V]

theorem range_restrictAct (hV : ∀ v : V, v * v = 1) (L : Subgroup (MulAut V))
    (hperf : Group.IsPerfect L)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {M : Type*} [Group M] (e : L ⧸ Subgroup.center L ≃* M) {E : Subgroup (MulAut V)}
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE1 : E ≠ ⊥) (hEa : IsElemAbelian2 E) :
    Nat.card (restrictAct L e hEN).range = Nat.card E ∧ (restrictAct L e hEN).range ≠ ⊥ ∧
      IsElem2 (restrictAct L e hEN).range := by
  have := hperf
  have hρ := restrictAct_injective L e (centralizer_odd hV L hirr) hEN hEa
  set ρ := restrictAct L e hEN
  refine ⟨(Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm, ?_, ?_, ?_⟩
  · intro h
    apply hE1
    rw [eq_bot_iff]
    intro a ha
    have h1 : ρ ⟨a, ha⟩ ∈ ρ.range := ⟨⟨a, ha⟩, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one ρ] at h1
    exact Subgroup.mem_bot.2 (congrArg Subtype.val (hρ h1))
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEa.1 a a.2 b b.2)
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hEa.2 a a.2)
    rw [this, map_one]

theorem not_isFFStarOffender_of_dispCriterion (hV : ∀ v : V, v * v = 1)
    (L : Subgroup (MulAut V)) (hperf : Group.IsPerfect L)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {M : Type*} [Group M] (e : L ⧸ Subgroup.center L ≃* M) (hM : DispCriterion M)
    {G A : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V))) : ¬ IsFFStarOffender G A := by
  intro hA
  have := hperf
  have hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have h := hA.card_le (B := ⊥) bot_le
    rwa [B1.card_bot_mul_card_fixV] at h
  have hodd := centralizer_odd hV L hirr
  have hZ := center_eq_bot L e
  obtain ⟨hFcard, hF1, hFa⟩ := range_restrictAct hV L hperf hirr e hAN hA.2.1 hA.2.2.1
  rcases hM _ hF1 hFa with ⟨α, ⟨⟨x, hxA⟩, rfl⟩, -, hα⟩ | ⟨hFin, hline⟩
  · have hG : GenAt M (modelAct L e ⟨x, hAN hxA⟩) (Nat.card (restrictAct L e hAN).range) :=
      hα.elim DispAt.genAt id
    have h1 := lt_index_of_genAt hV L e ⟨x, hAN hxA⟩ hG
    have h2 := index_fixV_le_card hoff hxA
    simp only at h1
    omega
  ·
    have hAL : A ≤ L := by
      intro a ha
      have h2 : a * a = 1 := by rw [← sq]; exact hA.2.2.1.2 a ha
      obtain ⟨m, hm⟩ := hFin ⟨⟨a, ha⟩, rfl⟩
      refine mem_of_involution_inner L hodd (hAN ha) h2 ⟨e.symm m, (MulAut.congr e).injective ?_⟩
      rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ← modelAct_apply, hm]
      rfl
    have hEq : (restrictAct L e hAN).range.comap MulAut.conj =
        (A.subgroupOf L).map (modelProj L e) := by
      ext m
      constructor
      · rintro ⟨⟨a, ha⟩, ham⟩
        refine ⟨⟨a, hAL ha⟩, ha, conj_injective hZ ?_⟩
        rw [← ham, modelProj_apply, ← modelAct_of_mem L e (hAL ha)]
        rfl
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨a, ha⟩, ?_⟩
        rw [modelProj_apply, ← modelAct_of_mem L e a.2]
        rfl
    rw [hEq] at hline
    exact false_of_lineGenAt hV L hirr e hLG hA hAL hline

end Offender

theorem asB42NoOffenderFor_of_dispCriterion {P : ∀ (X : Type) [Group X], Prop}
    (h : ∀ (X : Type) [Group X], P X →
      ∃ (M : Type) (_ : Group M), Nonempty (X ⧸ Subgroup.center X ≃* M) ∧ DispCriterion M) :
    AsB42NoOffenderFor P := by
  intro V _ _ hV G L hHyp hP A hA
  obtain ⟨hnt, hperf, hirr, hAN, -⟩ := B42Vacuous.offender_data hHyp hA
  obtain ⟨M, _, ⟨e⟩, hM⟩ := h L hP
  have := hnt
  have hLG : L ≤ G := by
    rw [hHyp.2.1]
    exact quasithinGenFitting_le G
  exact not_isFFStarOffender_of_dispCriterion (fun v => by rw [← pow_two]; exact hV v) L hperf
    hirr e hM hLG hAN hA

end B42Disp

end CFSG.Quasithin
